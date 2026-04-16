import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
  server: {
    port: 5173,
    open: '/sketch.html',
  },
  build: {
    rollupOptions: {
      input: {
        sketch: 'sketch.html',
      },
    },
  },
});
