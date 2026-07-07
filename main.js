import * as THREE from 'three';
import gsap from 'gsap';
import { ScrollTrigger } from 'gsap/ScrollTrigger';

/* ==========================================================================
   1. HTML UI, Dynamic HUD Telemetry, and Theme Toggling
   ========================================================================== */

document.addEventListener('DOMContentLoaded', () => {
  setupUI();
});

// Cache telemetry DOM nodes for faster access
let hudValX, hudValY, hudValZ, hudScroll, hudFps;

function setupUI() {
  hudValX = document.getElementById('hud-val-x');
  hudValY = document.getElementById('hud-val-y');
  hudValZ = document.getElementById('hud-val-z');
  hudScroll = document.getElementById('hud-scroll');
  hudFps = document.getElementById('hud-fps');

  // Page Loading Progress
  const loader = document.getElementById('loader');
  const progressBar = document.getElementById('load-progress');
  let progress = 0;
  
  const progressInterval = setInterval(() => {
    progress += Math.random() * 25;
    if (progress >= 100) {
      progress = 100;
      clearInterval(progressInterval);
      progressBar.style.width = '100%';
      setTimeout(() => {
        loader.classList.add('loaded');
      }, 150);
    } else {
      progressBar.style.width = `${progress}%`;
    }
  }, 20);

  // Optimized Custom Cursor with GPU Translate3d (Zero Layout Reflow)
  const cursor = document.getElementById('custom-cursor');
  const cursorDot = document.getElementById('custom-cursor-dot');
  let mouseX = 0, mouseY = 0;
  let cursorX = 0, cursorY = 0;
  let dotX = 0, dotY = 0;

  window.addEventListener('mousemove', (e) => {
    mouseX = e.clientX;
    mouseY = e.clientY;
  });

  function animateCursor() {
    // Smoother interpolation coordinates (inertia)
    cursorX += (mouseX - cursorX) * 0.18;
    cursorY += (mouseY - cursorY) * 0.18;
    dotX += (mouseX - dotX) * 0.45;
    dotY += (mouseY - dotY) * 0.45;

    // Apply transform3d for GPU compositor acceleration
    if (cursor && cursorDot) {
      cursor.style.transform = `translate3d(${cursorX}px, ${cursorY}px, 0) translate(-50%, -50%)`;
      cursorDot.style.transform = `translate3d(${dotX}px, ${dotY}px, 0) translate(-50%, -50%)`;
    }

    requestAnimationFrame(animateCursor);
  }
  animateCursor();

  // Hover animations triggers
  const interactables = document.querySelectorAll('a, button, input, textarea, .btn, .timeline-content, .social-links li a');
  interactables.forEach(item => {
    item.addEventListener('mouseenter', () => {
      document.body.classList.add('hovering-link');
    });
    item.addEventListener('mouseleave', () => {
      document.body.classList.remove('hovering-link');
    });
  });

  // Mobile Menu Toggle
  const mobileToggle = document.querySelector('.mobile-nav-toggle');
  const navLinks = document.querySelector('.nav-links');
  
  mobileToggle.addEventListener('click', () => {
    navLinks.classList.toggle('active');
    mobileToggle.classList.toggle('open');
  });

  // Highlight active menu on scroll
  const sections = document.querySelectorAll('section');
  const navItems = document.querySelectorAll('.nav-links a');

  window.addEventListener('scroll', () => {
    let current = '';
    const scrollY = window.scrollY;
    
    sections.forEach(section => {
      const sectionTop = section.offsetTop;
      const sectionHeight = section.clientHeight;
      if (scrollY >= sectionTop - sectionHeight / 3) {
        current = section.getAttribute('id');
      }
    });

    navItems.forEach(item => {
      item.classList.remove('active');
      if (item.getAttribute('href').slice(1) === current) {
        item.classList.add('active');
      }
    });

    // Update Scroll Telemetry Indicator
    const maxScroll = document.documentElement.scrollHeight - window.innerHeight;
    const scrollPct = maxScroll > 0 ? ((scrollY / maxScroll) * 100).toFixed(2) : '0.00';
    if (hudScroll) hudScroll.textContent = `${scrollPct}%`;
  });

  // Theme Toggler Event Setup
  const themeToggle = document.getElementById('theme-toggle');
  if (themeToggle) {
    // Load saved preference
    const savedTheme = localStorage.getItem('theme') || 'dark';
    document.documentElement.dataset.theme = savedTheme;
    
    const icon = themeToggle.querySelector('i');
    if (icon) {
      icon.className = savedTheme === 'dark' ? 'fas fa-moon' : 'fas fa-sun';
    }

    themeToggle.addEventListener('click', () => {
      const currentTheme = document.documentElement.dataset.theme || 'dark';
      const newTheme = currentTheme === 'dark' ? 'light' : 'dark';
      
      // Update DOM dataset
      document.documentElement.dataset.theme = newTheme;
      localStorage.setItem('theme', newTheme);
      
      // Toggle button Icon
      if (icon) {
        icon.className = newTheme === 'dark' ? 'fas fa-moon' : 'fas fa-sun';
      }

      // Update active WebGL scene rendering colors
      updateWebGLTheme(newTheme);
    });
  }

  // Reveal Animations
  const revealElements = document.querySelectorAll('.reveal');
  const revealObserver = new IntersectionObserver((entries) => {
    entries.forEach(entry => {
      if (entry.isIntersecting) {
        entry.target.classList.add('active');
      }
    });
  }, { threshold: 0.1 });

  revealElements.forEach(el => revealObserver.observe(el));
}


/* ==========================================================================
   2. Optimized WebGL 3D Constellation & Telemetry Engine
   ========================================================================== */

// --- Global variables ---
let scene, camera, renderer;
let starfieldParticles;
let constellationGroup, nodePoints, nodeLines;
let coreNucleus;
const numNodes = 140;

// Pre-allocated Vector3 Pools for math optimization (Zero garbage collection)
const nodePositions = [];
const nodeOriginals = [];
const nodeVelocities = [];
const tempDir = new THREE.Vector3();
const localMouse = new THREE.Vector3();
const springDir = new THREE.Vector3();

// Line Segment static buffer parameters (eliminates allocation stutters)
const maxLines = 450;
let linePositions;
let linePositionAttribute;

// Mouse & Touch coordinate tracking
const mouse = new THREE.Vector2(-9999, -9999);
const raycaster = new THREE.Raycaster();
const planeZ = new THREE.Plane(new THREE.Vector3(0, 0, 1), 0);
const mouse3D = new THREE.Vector3();

// Dynamic connection matrix
const maxLineDist = 1.0;
const maxLineDistSq = maxLineDist * maxLineDist;
const maxMouseDist = 2.4;
const maxMouseDistSq = maxMouseDist * maxMouseDist;

// Create circular glowing texture programmatically
function createCircleTexture(colorStr, size = 64) {
  const canvas = document.createElement('canvas');
  canvas.width = size;
  canvas.height = size;
  const ctx = canvas.getContext('2d');

  const grad = ctx.createRadialGradient(size/2, size/2, 0, size/2, size/2, size/2);
  grad.addColorStop(0, colorStr);
  grad.addColorStop(0.25, colorStr);
  grad.addColorStop(0.55, 'rgba(0, 242, 254, 0.25)');
  grad.addColorStop(1, 'rgba(0,0,0,0)');

  ctx.fillStyle = grad;
  ctx.fillRect(0, 0, size, size);

  return new THREE.CanvasTexture(canvas);
}

// Initialize ThreeJS
function initThree() {
  const container = document.getElementById('canvas-container');

  // Scene
  scene = new THREE.Scene();
  
  // Set initial theme values
  const currentTheme = document.documentElement.dataset.theme || 'dark';
  const isLight = currentTheme === 'light';
  const bgColor = isLight ? 0xf2f0f5 : 0x030206;

  scene.fog = new THREE.FogExp2(bgColor, 0.06);

  // Camera
  camera = new THREE.PerspectiveCamera(55, window.innerWidth / window.innerHeight, 0.1, 100);
  camera.position.set(0, 0, 7.5);

  // Renderer
  renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: "high-performance" });
  renderer.setSize(window.innerWidth, window.innerHeight);
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setClearColor(bgColor, 1.0);
  container.appendChild(renderer.domElement);

  // --- Add Lights ---
  const ambientLight = new THREE.AmbientLight(0xffffff, 0.55);
  scene.add(ambientLight);

  const dirLight1 = new THREE.DirectionalLight(0x00f2fe, 1.8);
  dirLight1.position.set(5, 8, 5);
  scene.add(dirLight1);

  const dirLight2 = new THREE.DirectionalLight(0xff007f, 1.2);
  dirLight2.position.set(-5, -8, 5);
  scene.add(dirLight2);

  // --- Particle System 1: Starfield ---
  const starGeo = new THREE.BufferGeometry();
  const starCount = 1000;
  const starPositions = new Float32Array(starCount * 3);

  for (let i = 0; i < starCount * 3; i += 3) {
    const radius = 18 + Math.random() * 25;
    const theta = Math.random() * Math.PI * 2;
    const phi = Math.acos((Math.random() * 2) - 1);
    
    starPositions[i] = radius * Math.sin(phi) * Math.cos(theta);
    starPositions[i + 1] = radius * Math.sin(phi) * Math.sin(theta);
    starPositions[i + 2] = radius * Math.cos(phi);
  }

  starGeo.setAttribute('position', new THREE.BufferAttribute(starPositions, 3));
  
  const starMat = new THREE.PointsMaterial({
    color: isLight ? 0x4f46e5 : 0x00f2fe,
    size: 0.1,
    transparent: true,
    opacity: isLight ? 0.35 : 0.5,
    blending: isLight ? THREE.NormalBlending : THREE.AdditiveBlending,
    depthWrite: false
  });

  starfieldParticles = new THREE.Points(starGeo, starMat);
  scene.add(starfieldParticles);

  // --- Particle System 2: Interactive Central Constellation ---
  constellationGroup = new THREE.Group();
  scene.add(constellationGroup);

  // Futuristic Rotating Holographic Grid Helper
  const gridHelper = new THREE.GridHelper(7, 24, isLight ? 0x8553d9 : 0x00f2fe, isLight ? 0xc084fc : 0x481e85);
  gridHelper.position.y = -3.5;
  gridHelper.material.opacity = isLight ? 0.3 : 0.28;
  gridHelper.material.transparent = true;
  gridHelper.material.blending = isLight ? THREE.NormalBlending : THREE.AdditiveBlending;
  gridHelper.material.depthWrite = false;
  constellationGroup.add(gridHelper);

  // Glowing Core Nucleus (Futuristic Server / Neural node core)
  const coreGeo = new THREE.IcosahedronGeometry(0.48, 1);
  const coreMat = new THREE.MeshBasicMaterial({
    color: isLight ? 0xa21caf : 0xff007f,
    wireframe: true,
    transparent: true,
    opacity: 0.45,
    blending: isLight ? THREE.NormalBlending : THREE.AdditiveBlending
  });
  coreNucleus = new THREE.Mesh(coreGeo, coreMat);
  constellationGroup.add(coreNucleus);

  // Nodes instantiation
  const sphereRadius = 3.2;
  for (let i = 0; i < numNodes; i++) {
    const theta = Math.random() * Math.PI * 2;
    const phi = Math.acos((Math.random() * 2) - 1);
    const r = Math.cbrt(Math.random()) * sphereRadius;

    const x = r * Math.sin(phi) * Math.cos(theta);
    const y = r * Math.sin(phi) * Math.sin(theta);
    const z = r * Math.cos(phi);

    nodePositions.push(new THREE.Vector3(x, y, z));
    nodeOriginals.push(new THREE.Vector3(x, y, z));
    
    // Low drift vectors
    nodeVelocities.push(new THREE.Vector3(
      (Math.random() - 0.5) * 0.006,
      (Math.random() - 0.5) * 0.006,
      (Math.random() - 0.5) * 0.006
    ));
  }

  // Points Geometry
  const nodeGeo = new THREE.BufferGeometry();
  updatePointsGeometry(nodeGeo);

  const nodeMat = new THREE.PointsMaterial({
    size: 0.16,
    map: createCircleTexture(isLight ? '#7c3aed' : '#00f2fe'),
    transparent: true,
    blending: isLight ? THREE.NormalBlending : THREE.AdditiveBlending,
    depthWrite: false
  });

  nodePoints = new THREE.Points(nodeGeo, nodeMat);
  constellationGroup.add(nodePoints);

  // Line segments binding with pre-allocated array (Optimized: Zero memory allocation)
  linePositions = new Float32Array(maxLines * 2 * 3);
  const lineGeo = new THREE.BufferGeometry();
  linePositionAttribute = new THREE.BufferAttribute(linePositions, 3);
  lineGeo.setAttribute('position', linePositionAttribute);

  const lineMat = new THREE.LineBasicMaterial({
    color: isLight ? 0x6d28d9 : 0x00f2fe,
    transparent: true,
    opacity: isLight ? 0.4 : 0.16,
    blending: isLight ? THREE.NormalBlending : THREE.AdditiveBlending,
    depthWrite: false
  });

  nodeLines = new THREE.LineSegments(lineGeo, lineMat);
  constellationGroup.add(nodeLines);

  // Mouse coordinate mappings
  window.addEventListener('mousemove', (e) => {
    mouse.x = (e.clientX / window.innerWidth) * 2 - 1;
    mouse.y = -(e.clientY / window.innerHeight) * 2 + 1;
  });

  // Touch move mapping (Haptic interactions on mobile/tablet)
  window.addEventListener('touchmove', (e) => {
    if (e.touches.length > 0) {
      const touch = e.touches[0];
      mouse.x = (touch.clientX / window.innerWidth) * 2 - 1;
      mouse.y = -(touch.clientY / window.innerHeight) * 2 + 1;
    }
  }, { passive: true });

  window.addEventListener('touchend', () => {
    mouse.x = -9999;
    mouse.y = -9999;
  });

  window.addEventListener('mouseleave', () => {
    mouse.x = -9999;
    mouse.y = -9999;
  });

  window.addEventListener('resize', onWindowResize);

  // Bind scroll trigger animations
  initScrollAnimations();
}

function updatePointsGeometry(geometry) {
  const arr = new Float32Array(numNodes * 3);
  for (let i = 0; i < numNodes; i++) {
    const pos = nodePositions[i];
    arr[i * 3] = pos.x;
    arr[i * 3 + 1] = pos.y;
    arr[i * 3 + 2] = pos.z;
  }
  geometry.setAttribute('position', new THREE.BufferAttribute(arr, 3));
  geometry.attributes.position.needsUpdate = true;
}

// Window resizing
function onWindowResize() {
  camera.aspect = window.innerWidth / window.innerHeight;
  camera.updateProjectionMatrix();
  renderer.setSize(window.innerWidth, window.innerHeight);
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
}

// Dynamically sync WebGL rendering colors with CSS theme selections
function updateWebGLTheme(theme) {
  if (!renderer || !scene) return;

  const isLight = theme === 'light';
  const bgColor = isLight ? 0xf2f0f5 : 0x030206;
  const blendingMode = isLight ? THREE.NormalBlending : THREE.AdditiveBlending;

  // Clear backdrop and fog settings
  renderer.setClearColor(bgColor, 1.0);
  scene.fog.color.setHex(bgColor);

  // Update particles texture colors
  if (nodePoints) {
    nodePoints.material.map = createCircleTexture(isLight ? '#7c3aed' : '#00f2fe');
    nodePoints.material.blending = blendingMode;
    nodePoints.material.needsUpdate = true;
  }

  // Update background starfield colors
  if (starfieldParticles) {
    starfieldParticles.material.color.setHex(isLight ? 0x4f46e5 : 0x00f2fe);
    starfieldParticles.material.opacity = isLight ? 0.35 : 0.5;
    starfieldParticles.material.blending = blendingMode;
    starfieldParticles.material.needsUpdate = true;
  }

  // Update wireframe lines and colors
  if (nodeLines) {
    nodeLines.material.color.setHex(isLight ? 0x6d28d9 : 0x00f2fe);
    nodeLines.material.opacity = isLight ? 0.4 : 0.16;
    nodeLines.material.blending = blendingMode;
    nodeLines.material.needsUpdate = true;
  }

  // Update nucleus center color
  if (coreNucleus) {
    coreNucleus.material.color.setHex(isLight ? 0xa21caf : 0xff007f);
    coreNucleus.material.blending = blendingMode;
    coreNucleus.material.needsUpdate = true;
  }
}


/* ==========================================================================
   3. Scroll Animation Bindings (GSAP ScrollTrigger Rig)
   ========================================================================== */

const cameraRig = {
  posX: 0,
  posY: 0,
  posZ: 7.5,
  lookX: 0,
  lookY: 0,
  lookZ: 0,
  constelX: 0,
  constelY: 0,
  constelZ: 0,
  constelRotY: 0
};

function initScrollAnimations() {
  gsap.registerPlugin(ScrollTrigger);

  const timeline = gsap.timeline({
    scrollTrigger: {
      trigger: "#main-content",
      start: "top top",
      end: "bottom bottom",
      scrub: 1.0, // High responsiveness
    }
  });

  // Interpolation timeline stages
  timeline
    // 1. Hero -> About
    .to(cameraRig, {
      posX: 2.3, posY: 1.0, posZ: 6.0,
      lookX: -0.4, lookY: 0, lookZ: 0,
      constelX: -1.7, constelY: 0, constelZ: 0,
      constelRotY: Math.PI * 0.45,
      duration: 1
    })
    // 2. About -> Experience
    .to(cameraRig, {
      posX: -2.3, posY: -1.6, posZ: 6.2,
      lookX: 0.4, lookY: -2.6, lookZ: 0,
      constelX: 1.7, constelY: -2.6, constelZ: 0,
      constelRotY: Math.PI * 0.95,
      duration: 1
    })
    // 3. Experience -> Skills
    .to(cameraRig, {
      posX: 0, posY: -6.0, posZ: 7.5,
      lookX: 0, lookY: -6.0, lookZ: 0,
      constelX: 0, constelY: -6.0, constelZ: 0,
      constelRotY: Math.PI * 1.55,
      duration: 1
    })
    // 4. Skills -> Projects
    .to(cameraRig, {
      posX: 2.3, posY: -9.5, posZ: 6.2,
      lookX: -0.4, lookY: -9.5, lookZ: 0,
      constelX: -1.7, constelY: -9.5, constelZ: 0,
      constelRotY: Math.PI * 2.2,
      duration: 1
    })
    // 5. Projects -> Contact
    .to(cameraRig, {
      posX: 0, posY: -13.8, posZ: 5.6,
      lookX: 0, lookY: -13.8, lookZ: 0,
      constelX: 0, constelY: -13.8, constelZ: 0,
      constelRotY: Math.PI * 3.0,
      duration: 1
    });
}


/* ==========================================================================
   4. High-Performance Frame Loop
   ========================================================================== */

const clock = new THREE.Clock();
let frames = 0;
let lastFpsTime = 0;

function tick() {
  const elapsedTime = clock.getElapsedTime();

  // --- Real-time FPS Calculation ---
  frames++;
  const now = performance.now();
  if (now >= lastFpsTime + 1000) {
    const fps = Math.round((frames * 1000) / (now - lastFpsTime));
    if (hudFps) hudFps.textContent = `${fps} FPS`;
    frames = 0;
    lastFpsTime = now;
  }

  // --- Dynamic Telemetry Coordinates Mapping ---
  // Raycast Mouse onto Plane Z = 0
  raycaster.setFromCamera(mouse, camera);
  raycaster.ray.intersectPlane(planeZ, mouse3D);

  // Update HUD text
  if (hudValX && mouse.x > -99) {
    hudValX.textContent = mouse3D.x.toFixed(2);
    hudValY.textContent = mouse3D.y.toFixed(2);
    hudValZ.textContent = mouse3D.z.toFixed(2);
  } else if (hudValX) {
    hudValX.textContent = "0.00";
    hudValY.textContent = "0.00";
    hudValZ.textContent = "0.00";
  }

  // --- Optimized Physics Particle Loop ---
  localMouse.copy(mouse3D).sub(constellationGroup.position);

  for (let i = 0; i < numNodes; i++) {
    const pos = nodePositions[i];
    const orig = nodeOriginals[i];
    const vel = nodeVelocities[i];

    // 1. Natural drift
    pos.add(vel);

    // Sphere boundaries check
    const rSq = pos.x*pos.x + pos.y*pos.y + pos.z*pos.z;
    if (rSq > 14.4) { // 3.8^2 = 14.44
      vel.negate();
    }

    // 2. Mouse gravity force: compare squared distance to avoid square root
    const distToMouseSq = pos.distanceToSquared(localMouse);
    if (distToMouseSq < maxMouseDistSq) {
      const dist = Math.sqrt(distToMouseSq);
      const force = (maxMouseDist - dist) * 0.18; // strong responsive reaction
      tempDir.subVectors(pos, localMouse).normalize();
      pos.addScaledVector(tempDir, force);
    }

    // 3. Elastic pull back towards original sphere coordinates
    springDir.subVectors(orig, pos);
    pos.addScaledVector(springDir, 0.015);
  }

  // Update Points Geometry buffer
  updatePointsGeometry(nodePoints.geometry);

  // --- Rebuild Lines Connections segment buffer (GPU static buffer write) ---
  let lineCount = 0;

  for (let i = 0; i < numNodes; i++) {
    const posA = nodePositions[i];
    for (let j = i + 1; j < numNodes; j++) {
      const posB = nodePositions[j];
      
      // Calculate squared distance for fast filter
      const distSq = posA.distanceToSquared(posB);
      if (distSq < maxLineDistSq) {
        if (lineCount < maxLines) {
          const idx = lineCount * 6;
          linePositions[idx] = posA.x;
          linePositions[idx + 1] = posA.y;
          linePositions[idx + 2] = posA.z;
          linePositions[idx + 3] = posB.x;
          linePositions[idx + 4] = posB.y;
          linePositions[idx + 5] = posB.z;
          lineCount++;
        }
      }
    }
  }

  // Limit rendering count & upload to GPU
  nodeLines.geometry.setDrawRange(0, lineCount * 2);
  linePositionAttribute.needsUpdate = true;

  // --- Camera Rig Alignment ---
  camera.position.set(cameraRig.posX, cameraRig.posY, cameraRig.posZ);
  const target = new THREE.Vector3(cameraRig.lookX, cameraRig.lookY, cameraRig.lookZ);
  camera.lookAt(target);

  // Starfield rotation
  starfieldParticles.rotation.y = elapsedTime * 0.012;
  starfieldParticles.rotation.x = elapsedTime * 0.004;

  // Constellation rotation and layout shifts
  constellationGroup.position.set(cameraRig.constelX, cameraRig.constelY, cameraRig.constelZ);
  constellationGroup.rotation.y = elapsedTime * 0.07 + cameraRig.constelRotY;
  constellationGroup.rotation.x = Math.sin(elapsedTime * 0.035) * 0.12;

  // Rotate nucleus core
  if (coreNucleus) {
    coreNucleus.rotation.y = elapsedTime * 0.3;
    coreNucleus.rotation.x = elapsedTime * 0.15;
  }

  // Render Frame
  renderer.render(scene, camera);

  // Next Frame
  requestAnimationFrame(tick);
}

// Start ThreeJS
initThree();
tick();
