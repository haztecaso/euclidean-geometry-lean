# Trabajo de Fin de Grado

Código fuente y memoria del Trabajo de Fin de Grado del grado en Matemáticas de la Universidad Complutense de Madrid. 

Actualmente el trabajo está en desarrollo y en una fase muy inestable; todo está sujeto a cambios radicales.

## Estructura del repositorio

### Código fuente

En la carpeta `/src` puedes encontrar el código fuente en Lean 3, en el que se implementan definiciones y demostraciones de la axiomática de Hilbert para la geometría euclídea plana. Los ficheros están organizados de la siguiente forma:

- En `incidence_geometry.lean` se encuentran los axiomas de incidencia y algún resultado elemental que se puede demostrar con ellos.
- En `order_geometry.lean` se encuentran los axiomas de orden.
- En `examples.lean` hay construidos algunos modelos clásicos de las teorías implementadas en los demás ficheros.

### Memoria

En la carpeta `/memoria` se encuentra la memoria del trabajo.

## Ejecutando el Código


### Instalación local

En [la web de la comunidad de Lean 3](https://leanprover-community.github.io/get_started.html) se encuentran las instrucciones de instalación de Lean 3, mathilb, leanproject y configuración del entorno de desarrollo. Una vez instalado el lenguaje y estas herramientas, puedes ejecutar el comando `https://github.com/haztecaso/euclidean-geometry-lean` para obtener una copia local de este repositorio. Con el editor VS Code y nav

### Entorno en línea

Si has tenido problemas instalando Lean en tu ordenador, o solo quieres navegar por el repositorio con el entorno de desarrollo de Lean sin tener que instalar nada en tu ordenador, puedes utilizar el servicio de *gitpod*.

Para ello haz click en [este enlace](https://gitpod.io/#/https://github.com/haztecaso/euclidean-geometry-lean). Tras el registro en la web tendrás autoconfigurado un entorno con todas las dependencias necesarias para navegar a través de las definiciones y demostraciones del proyecto.

