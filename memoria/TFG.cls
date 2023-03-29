\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{TFG}[2023/03/26 Clase para Trabajo de Fin de Grado]

% Inspiración:
% - https://github.com/guillegran/TFGMates

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{scrartcl}}
\ProcessOptions\relax
\LoadClass[a4paper]{scrartcl}

\RequirePackage[none]{hyphenat}
\RequirePackage[utf8]{inputenc}
\RequirePackage[T1]{fontenc}
\RequirePackage[spanish]{babel}
\RequirePackage{enumitem}
\RequirePackage{array}
\RequirePackage{cite}
\RequirePackage{graphicx}

\RequirePackage[colorlinks=true, linktocpage=true, pagebackref=true, citecolor=red, linkcolor=blue]{hyperref}
\setcounter{tocdepth}{1}

\RequirePackage{enumitem}
\setlist[enumerate]{topsep=0mm}
\setlist[itemize]{topsep=0mm}

% \setlength\parindent{0pt}
\setlength\parskip{1em plus 0.1em minus 0.2em}


\RequirePackage{sectsty}
\RequirePackage{titlesec}

\newcommand{\emptypage}{\newpage\null\thispagestyle{empty}\newpage}

\RequirePackage{xcolor}
\newcommand{\todo}[1]{\noindent\textcolor{red}{\textbf{Pendiente: }#1}}
\newcommand{\redactar}[1]{\noindent\textcolor{blue}{\bfseries #1}}

\renewcommand{\maketitle}{%
    \begin{titlepage}
      \begin{minipage}{.5\textwidth}
        \Large Trabajo de Fin de Grado
      \end{minipage}
      \begin{minipage}{0.5\textwidth}
        \hfill
        \includegraphics[height=1.5cm]{imgs/UCM}
      \end{minipage}
      \vfill
      \begin{center}
        \LARGE\bfseries\sffamily \@title

        \vspace*{.5cm} \LARGE\normalfont \@author

        \vspace*{.3cm} \Large \@date
      \end{center}
      \vfill \Large\noindent \@subtitle
    \end{titlepage}
}

\renewenvironment{abstract}[1][Resumen]{
  \thispagestyle{empty}
  \begin{center}
      \textbf{#1}
  \end{center}
}{\vspace*{1cm}}


% \sectionfont{\centering\Large\underline}
% \titlespacing*{\section}{0pt}{1.2em plus 0.1em minus 0.1em}{0.4em plus 0.1em minus 0.1em}
% \titlespacing*{\subsection}{0pt}{.4em plus 0.1em minus 0.1em}{.2em plus 0.1em minus 0.1em}
% \titlespacing*{\subsubsection}{0pt}{.2em plus 0.1em minus 0.1em}{0em plus 0.1em minus 0.1em}


\bibliographystyle{plain}
