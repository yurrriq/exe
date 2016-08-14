% 
% Copyright (c) 2012-2016 by Mykhailo Makukha <m.makukha@gmail.com>.
% All rights reserved.
% 
% Credits to:
% Anton Varfolomieiev (reporting bugs).
% 

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{saittr16}[2016/01/22 v1.8 SAIT Conference class file]
\def\sa@class{saittr16}

\newif\ifsa@digital
\newif\ifsa@printed
\newif\ifsa@book
\newif\ifsa@prog
\newif\ifsa@editorial
\newif\ifsa@draft
\ifdefined\sa@flag@digital\sa@digitaltrue\fi
\ifdefined\sa@flag@printed\sa@printedtrue\fi
\ifdefined\sa@flag@book\sa@booktrue\fi
\ifdefined\sa@flag@prog\sa@progtrue\fi
\ifdefined\sa@flag@editorial\sa@editorialtrue\fi
\ifsa@digital\else\ifsa@printed\else\sa@digitaltrue\fi\fi
\ifsa@book\else\ifsa@prog\else\sa@booktrue\fi\fi
\def\sa@use#1{\ifdefined#1#1\fi}


% Year-specific things

\newcommand\SaitFooter{%
\href{http://sait.kpi.ua}{\textcolor{\sa@footercolor}{%
18-th International conference on System Analysis and Information Technology SAIT~2016}}\\
\href{http://iasa.kpi.ua}{\textcolor{\sa@footercolor}{Institute for Applied System Analysis}} of
\href{http://kpi.ua}{\textcolor{\sa@footercolor}{National Technical University of Ukraine ``KPI''}},
Kyiv, Ukraine, May 30 -- June 2, 2016}


% Class options

% options are not allowed
\DeclareOption*{\PackageError{\sa@class}{Unknown option <\CurrentOption>.}{}}
\ProcessOptions*\relax


% Document class

\edef\sa@d@twoside{\ifsa@digital false\else true\fi}
\edef\sa@d@fontsize{\ifsa@book 10pt\else 11pt\fi}
\LoadClass[index=totoc,toc=flat,headings=small,captions=tableheading,
  twoside=\sa@d@twoside,fontsize=\sa@d@fontsize]{scrbook}


% Packages and utlilities

\RequirePackage{cmap}
\RequirePackage[T2A]{fontenc}
\AfterPackage{inputenc}{\usepackage[english,russian,ukrainian]{babel}}

\RequirePackage{calc}
\RequirePackage{moredefs}
\RequirePackage{makecmds}
\RequirePackage{multido}

\renewcommand\makelength[2]{%
  \providelength{#1}\setlength{#1}{#2}%
  \@ifundefined{sa@dbg@showlength}{}{\sa@dbg@showlength{#1}}}
\def\sa@dbg@showlength#1{}
% Three-language macros
\newcommand\sa@ThreelangTerm[4]{% english-russian-ukrainian
  \ifnum\pdfstrcmp{#1}{english}=0#2%
  \else\ifnum\pdfstrcmp{#1}{russian}=0#3%
  \else\ifnum\pdfstrcmp{#1}{ukrainian}=0#4%
  \else\PackageWarning{\sa@class}{Unsupported language in threelang: <#1>}{}%
  \fi\fi\fi}
\newcommand\DeclareThreelangTerm[4] % english-russian-ukrainian
  {\providecommand{#1}[1]{}%
  \renewcommand{#1}[1]{\protect\sa@ThreelangTerm{##1}{#2}{#3}{#4}}}
\def\sa@defnempty#1#2#3{\def\sa@deftemp{#2}%
  \ifx\sa@deftemp\@empty#3\else\@namedef{#1}{#2}\fi}
\def\sa@gdefnempty#1#2#3{\def\sa@deftemp{#2}%
  \ifx\sa@deftemp\@empty#3\else\global\@namedef{#1}{#2}\fi}

\def\ShareLaTeX{\href{https://www.sharelatex.com?r=dd85f850&rm=d&rs=b}{ShareLaTeX.com}}


% Page geometry
% NOTE: the scaling factor of this page to A4 is 1:(sqrt(2)/\sa@p@f) = 1:1.1314

% headsep
\ifsa@book \def\sa@p@headsep{0.7\baselineskip} \fi
% footskip
\ifsa@book \def\sa@p@footskip{2\baselineskip} \fi
% margins and binding offset
\def\sa@p@top{8mm}
\def\sa@p@bottom{9mm}
\def\sa@p@bindingoffset{0mm}
\ifsa@book
  \def\sa@p@left{12mm} \def\sa@p@right{12mm}
\fi
% correction: page bleed and scaling factor
\def\sa@p@bleed{2mm}
\def\sa@p@f{1.25}
% correction: digital book&prog header/footer shift
\def\sa@p@topshift{0mm}
\def\sa@p@botshift{0mm}
\ifsa@digital
  \def\sa@p@topshift{4mm}
  \ifsa@book \def\sa@p@botshift{2mm} \fi
\fi
\sa@use\sa@editorial@pagegeometry
% load package
\RequirePackage[
  includeheadfoot,ignoremp,
  papersize={148mm*\real{\sa@p@f},210mm*\real{\sa@p@f}},
  bindingoffset=\sa@p@bindingoffset*\real{\sa@p@f},
  headsep=(\sa@p@headsep+\sa@p@topshift)*\real{\sa@p@f},
  footskip=(\sa@p@footskip+\sa@p@botshift)*\real{\sa@p@f},
  hmargin={(\sa@p@left+\sa@p@bleed)*\real{\sa@p@f},
           (\sa@p@right+\sa@p@bleed)*\real{\sa@p@f}},
  vmargin={(\sa@p@top+\sa@p@bleed-\sa@p@topshift)*\real{\sa@p@f},
           (\sa@p@bottom+\sa@p@bleed-\sa@p@botshift)*\real{\sa@p@f}},
  ]{geometry}


% Colors

\RequirePackage[usenames,x11names]{xcolor}
\colorlet{faded}{gray!70}
\colorlet{notes}{Ivory1!40}
\ifsa@digital
  \def\sa@footercolor{faded}
\else
  \def\sa@footercolor{black}
\fi


% Attaching source files

\ifsa@editorial\else
  \AtEndOfPackage{\RequirePackage[realmainfile]{currfile}}
  \AtEndOfPackage{\RequirePackage{attachfile}}
  \AtEndDocument{\sa@img@attach}
  \AtEndDocument{%
    \let\sa@tempa\@empty
    \def\sa@tempb#1{%
      \IfFileExists{#1}{\Inline\def\sa@tempa{\Super\sa@textattachfile{#1}{}}}{}}%
    \sa@tempb{\currfilepath}%
    \ifx\sa@tempa\@empty
      \ClassError{\sa@class}{Unable to find the source file.}
        {Make sure that source file has a default name: sait2016.tex.}
    \else
      \sa@tempa
    \fi}
  \AfterPackage{hyperref}{\AtBeginDocument{%
    \ifcsname ETE@OrgGin@setfile\endcsname
      \Inline\def\ETE@OrgGin@setfile#1#2#3{\Super\sa@img@reg{#3}}%
    \else
      \Inline\def\Gin@setfile#1#2#3{\Super\sa@img@reg{#3}}%
    \fi}}
  \def\sa@img@max{1000}
  \def\sa@img@reg#1{%
    \edef\sa@tempa{#1}%
    \multido{\i@sa@imgc=0+1}{\sa@img@max}{%
      \ifcsname sa@img@fn@\i@sa@imgc\endcsname
        \edef\sa@tempb{\@nameuse{sa@img@fn@\i@sa@imgc}}%
        \ifx\sa@tempa\sa@tempb\multidostop\fi
      \else
        \Inline\def\sa@tempc{%
          \global\@namedef{sa@img@fn@\Expand\i@sa@imgc}{\Expand\sa@tempa}}%
        \sa@tempc\multidostop
      \fi}}
  \def\sa@img@attach{%
    \PackageInfo{\sa@class}{Attaching image files.}%
    \multido{\i@sa@imgc=0+1}{\sa@img@max}{%
      \ifcsname sa@img@fn@\i@sa@imgc\endcsname
        \PackageInfo{\sa@class}
          {Attaching image file <\@nameuse{sa@img@fn@\i@sa@imgc}>.}
        \sa@textattachfile{\@nameuse{sa@img@fn@\i@sa@imgc}}%
      \fi}}
  \def\sa@textattachfile#1#2{\@firstofone{\textattachfile{#1}}{#2}}
\fi


% Page layout

% headers and footers
\ifsa@printed\ifsa@book
  \PassOptionsToPackage{footsepline}{scrpage2}
\fi\fi
\ifsa@editorial
  \PassOptionsToPackage{headsepline}{scrpage2}
\fi
\RequirePackage{scrpage2}
\pagestyle{scrheadings}
\clearscrheadfoot
\newcommand\SaitLogoHeading{}
\ihead{\small\textcolor{\sa@footercolor}{\headmark}}
\ifsa@editorial
  \ohead{\sa@h@ohb\textbf{\large\pagemark}\sa@h@oha}
\fi
\ifsa@digital
  \def\sa@h@ohb{\sa@h@ohlogobefore}
  \def\sa@h@oha{}
\else
  \def\sa@h@ohb{\ifthenelse{\not\isodd{\value{page}}}{}{\sa@h@ohlogobefore}}
  \def\sa@h@oha{\ifthenelse{\not\isodd{\value{page}}}{\sa@h@ohlogoafter}{}}
\fi
\def\sa@h@ohlogobefore{%
  \raisebox{-0.3ex}{\parbox[b][0pt]{0pt}{%
    \llap{\SaitLogoHeading}}}\hspace{.7em}}
\def\sa@h@ohlogoafter{%
  \hspace{1em}\raisebox{-0.3ex}{\parbox[b][0pt]{0pt}{%
    \rlap{\SaitLogoHeading}}}}
\ifsa@book
  \cfoot{\makebox[0pt][c]{\parbox[b]{\textwidth+6mm}{%
    \vspace{0.45\baselineskip}%
    \begin{spacing}{0.9}%
      \footnotesize\sffamily\upshape\centering
      \textcolor{\sa@footercolor}{\SaitFooter}%
    \end{spacing}}}}
\fi


% Theses environment

\newcounter{sa@@th}
\newcounter{sa@@aut}[sa@@th]
\newcounter{sa@@org}[sa@@th]
\newcounter{sa@@ain}[sa@@th]
\RequirePackage{inlinedef}
\RequirePackage{multido}
% theses environment
\newenvironment{theses}[1]{%
  \stepcounter{sa@@th}%
  \sa@defnempty{sa@lang}{#1}
    {\PackageError{\sa@class}{Theses language required.}{}}%
  \sa@th@startnew
  \ifsa@book
    \let\thanks\sa@thanks
    % make math theorems be usable only inside theses env
    \sa@thm@undeclaretheorems
    \renewcommand\sa@thm@undeclaretheorems{}%
    \sa@thm@declareenvironments
    \sa@thm@resetcounters
  \fi
  % titling command front-ends
  \ifsa@editorial\let\stamp\sa@@@stamp\fi
  \let\title\sa@@@title
  \let\author\sa@@@author
  \let\reviewer\sa@@@reviewer
  \let\organization\sa@@@organization
  \let\maketitle\sa@@@maketitle
  % open environment
  \begin{otherlanguage}{#1}%
  \ifsa@book
    \begin{spacing}{\sa@sp@spacing}%
  \fi
}{%
  \ifsa@book
    \FloatBarrier
    \sa@sp@endthesesspacing
    \end{spacing}%
  \fi
  \ifsa@prog
    \sa@@@maketitle
  \fi
  \end{otherlanguage}%
  \ifsa@book
    \sa@sp@setdefaults
  \fi}
\def\sa@th@startnew@restore{\gdef\sa@th@startnew{\sa@th@startnew@default}}
\sa@th@startnew@restore
\def\sa@th@startnew@default{\clearpage}
% title
\newcommand\sa@@@title[1]{%
  \@namedef{sa@t@title}{#1}}
% author
%  #1: [optional] organization reference number
%  #2: last (family) name and initials
%  #3: author's name for author's index
\newcommand\sa@@@author[3][]{%
  \sa@defnempty{sa@t@aut@orgi@\the\value{sa@@aut}}{#1}{}%
  \sa@defnempty{sa@t@aut@shrt@\the\value{sa@@aut}}{#2}
    {\PackageError{\sa@class}{Author's <short name> required.}{}}%
  \sa@defnempty{sa@t@aut@full@\the\value{sa@@aut}}{#3}
    {\PackageError{\sa@class}{Author's <full name> required.}{}}%
  \stepcounter{sa@@aut}}
% reviewer
% #1,#2,#3: same as author arguments
\newcommand\sa@@@reviewer[3][]{%
  \sa@defnempty{sa@t@rev@orgi}{#1}{}%
  \sa@defnempty{sa@t@rev@shrt}{#2}
    {\PackageError{\sa@class}{Reviewer's <short name> required.}{}}%
  \sa@defnempty{sa@t@rev@full}{#3}
    {\PackageError{\sa@class}{Reviewer's <full name> required.}{}}}
\def\sa@@@reviewer@text{%
  \sa@ThreelangTerm{\sa@lang}
    {reviewer}
    {\cyrr\cyre\cyrc\cyre\cyrn\cyrz\cyre\cyrn\cyrt}
    {\cyrr\cyre\cyrc\cyre\cyrn\cyrz\cyre\cyrn\cyrt}}
% organization
%  #1: [optional] organization reference number
%  #2: organization name
\newcommand\sa@@@organization[2][]{%
  \def\@tempb{#2}%
  \sa@defnempty{sa@t@org@orgi@\the\value{sa@@org}}{#1}{}%
  \sa@defnempty{sa@t@org@name@\the\value{sa@@org}}{#2}
    {\PackageError{\sa@class}{Organization's <name> required.}{}}%
  \stepcounter{sa@@org}}
% make title
\newcommand\sa@@@maketitle{%
  % validate
  \ifcsname sa@t@title\endcsname\else
    \PackageError{\sa@class}
      {Theses require \string\title{} specification.}{}%
  \fi
  \ifnum\value{sa@@aut}>0\else
    \PackageError{\sa@class}
      {Theses require at least one \string\author{} specification.}{}%
  \fi
  % start new "Session" if theses section was changed
  \ifsa@editorial\sa@start@session\fi
  % theses title preparation
  \sa@mk@authors
  \sa@mk@reviewer
  \sa@mk@organizations
  \ifsa@editorial\sa@mk@toc\sa@mk@idx\fi
  % print authors and organizations
  \noindent
  \begin{spacing}{1}%
    \hyphenpenalty=9999\raggedright\itshape
    \sa@mk@authors@t
    \sa@mk@reviewer@t
    \ifnum\value{sa@@org}>0
      \vspace{0.08\baselineskip}\small\par\noindent
      \begin{spacing}{0.95}%
        \sa@mk@organizations@t
      \end{spacing}%
      \vspace{0.1\baselineskip}%
    \fi
  \end{spacing}\par%
  % print title
  \vspace{\sa@sp@titlepreskipamount}%
  \begin{spacing}{0.95}%
    \noindent\raggedright%
    \usekomafont{disposition}\usekomafont{section}%
    %\ifsa@draft\sait@draftsectionmark{\@nameuse{\sa@t@stream}}{\@nameuse{\sa@t@attend}}\fi
    \sa@t@title\par%
  \end{spacing}%
  \vspace{\sa@sp@titlepostskipamount}
  \hypersetup{pdftitle={\sa@t@title},pdfauthor={\sa@mk@authors@tpdf}}}
% theses authors
\def\sa@mk@authors{% returns result in \sa@mk@authors@t, \sa@mk@authors@tpdf
  \def\@@rez{}%
  \def\sa@mk@authors@tpdf{}%
  \Multido{\i=0+1}{\value{sa@@aut}}{%
    \Inline\def\@@rez{\Super
      \sa@mk@authorname{\@nameuse{sa@t@aut@shrt@\Expand\i}}}%
    \Inline\def\sa@mk@authors@tpdf{\Super\@nameuse{sa@t@aut@full@\Expand\i}}%
    \ifcsname sa@t@aut@orgi@\i\endcsname
      \def\sa@tempc{\rlap{,}}%
      \Inline\def\sa@temps{%
        \sa@mk@authororgi{\@nameuse{sa@t@aut@orgi@\Expand\i}}}%
    \else
      \def\sa@tempc{,}%
      \def\sa@temps{}%
    \fi  
    \ifnum\multidocount<\value{sa@@aut}%
      \Inline\def\sa@tempd{\Expand\sa@tempc\Expand\sa@temps{} }%
      \Inline\def\sa@mk@authors@tpdf{\Super; }%
    \else
      \Inline\def\sa@tempd{\Expand\sa@temps}%
    \fi
    \Inline\def\@@rez{\Super\Expand\sa@tempd}}%
  \let\sa@mk@authors@t\@@rez}
\def\sa@mk@authorname#1{\mbox{\textbf{#1}}}
\def\sa@mk@authororgi#1{\textsuperscript{#1}}
% theses reviewer
\def\sa@mk@reviewer{% returns result in \sa@mk@reviewer@t
  \ifx\sa@t@rev@shrt\undefined
    \def\sa@mk@reviewer@t{}%
  \else
    \edef\sa@mk@reviewer@t{\sa@@@reviewer@text}%
    \Inline\def\sa@mk@reviewer@t{%
      \textit{ --- \Expand\sa@mk@reviewer@t~\mbox{\Expand\sa@t@rev@shrt}}}%
  \fi}
% theses organizations
\def\sa@mk@organizations{% returns result in \sa@mk@organizations@t
  \def\@@rez{}%
  \Multido{\i=0+1}{\value{sa@@org}}{%
    \ifcsname sa@t@org@orgi@\i\endcsname
      \Inline\def\@@rez{\Super
        \sa@mk@organizationorgi{\@nameuse{sa@t@org@orgi@\Expand\i}}}%
    \fi
    \Inline\def\@@rez{\Super
      \sa@mk@organizationname{\@nameuse{sa@t@org@name@\Expand\i}}}%
    \ifnum\multidocount<\value{sa@@org}%
      \Inline\def\@@rez{\Super; }%
    \fi}
  \let\sa@mk@organizations@t\@@rez}
\def\sa@mk@organizationname#1{#1}
\def\sa@mk@organizationorgi#1{\textbf{\textsuperscript{#1}}}


% Text general typesetting

\RequirePackage{setspace}
\RequirePackage{textcomp}
% hyphenation
\setlength\emergencystretch{3pt}
\setlength\hfuzz{3pt}
\PassOptionsToPackage{breaklinks}{hyperref}
% indentation
\RequirePackage{indentfirst}
\def\sa@sp@parindent{1.2em}
\setlength\parindent{\sa@sp@parindent}
% micro-typography
\RequirePackage{microtype}


% Text spacing

% font size is base length
\newlength\sa@sp@font
% \AtBeginDocument{\makelength\sa@sp@font{\fontsize}}
% general spaces
\newcommand\sa@sp@setdefaults{%
  \def\sa@sp@spacing{1}%
  \makelength\sa@sp@titlepreskipamount{\smallskipamount}%
  \makelength\sa@sp@titlepostskipamount{1.2\smallskipamount}%
  \makelength\sa@sp@paragraphpreskipamount{2pt*\real{\sa@p@f}}%
  \makelength\sa@sp@listsepskipamount{0.4\sa@sp@titlepostskipamount}%
  \makelength\sa@sp@verbsepskipamount{0.5\sa@sp@titlepostskipamount}%
  \topsep=\sa@sp@paragraphpreskipamount
  \def\sa@sp@bibfont{}%
  \def\sa@sp@bibspacing{\sa@sp@spacing}%
  \makelength\sa@sp@bibitemskipamount{0pt*\real{\sa@p@f}}%
  \makelength\sa@sp@bibheadpreskipamount{1.1\sa@sp@titlepostskipamount}%
  \makelength\sa@sp@bibheadpostskipamount{0.65\sa@sp@bibheadpreskipamount}%
  \def\sa@sp@endthesesspacing{}%
  \sa@sp@setdefaultdisplay%
  \sa@sp@setdefaultfloats}
% spaces around floats
\newcommand\sa@sp@setdefaultfloats{%
  \setlength\intextsep{1.75\sa@sp@titlepostskipamount}%
  \setlength\abovecaptionskip{0.8\intextsep}%
  \setlength\belowcaptionskip{0pt}}
% spaces around display math
\newcommand\sa@sp@setdefaultdisplay{%
  \makelength\sa@sp@displaypreskip{0.9\sa@sp@titlepostskipamount}%
  \makelength\sa@sp@displaypostskip{\sa@sp@displaypreskip}%
  \makelength\sa@sp@displayshortpreskip{0pt plus 0.2ex}%
  \makelength\sa@sp@displayshortpostskip{0.75\sa@sp@displaypostskip}%
  \everydisplay{%
    \setlength\abovedisplayskip{\sa@sp@displaypreskip}%
    \setlength\belowdisplayskip{\sa@sp@displaypostskip}%
    \setlength\abovedisplayshortskip{\sa@sp@displayshortpreskip}%
    \setlength\belowdisplayshortskip{\sa@sp@displayshortpostskip}}}
% set spaces
\AtBeginDocument{\sa@sp@setdefaults}
% spacing coefficient for autors index
\def\sa@sp@autindspacing{1}
% % difference between normalsize and small font baselineskip
% \newlength\sa@sp@baselineskipdiff
% \AtBeginDocument{%
%   \setlength\sa@sp@baselineskipdiff{\baselineskip}%
%   \small\addtolength\sa@sp@baselineskipdiff{-\baselineskip}\normalsize
%   \sa@dbg@showlength\sa@sp@baselineskipdiff}


% Text elements

% thanks and footnotes
\def\sa@thanks#1{%
  \begingroup
  \deffootnote[1em]{0pt}{1em}{}%
  \footnotetext{#1}%
  \endgroup}
\def\ftn@rule@width{.3\columnwidth}
% abstract
\provideenvironment{abstract}
  {\small\leftskip=3\parindent\rightskip=\parindent\noindent\ignorespaces}
  {\par\addvspace{\sa@sp@titlepostskipamount}\par}
% paragraph 
\renewcommand\paragraph[1]{%
  \@startsection{paragraph}{4}{\z@}%
    {\sa@sp@paragraphpreskipamount}{-0.5em}%
    {\raggedsection\sectfont\nobreak}{#1.}}
% list
\RequirePackage{paralist}
\setdefaultitem{\textbullet}{}{}{}
\renewenvironment{enumerate}
  {\setlength\pltopsep{\sa@sp@listsepskipamount}\begin{compactenum}}
  {\end{compactenum}}
\renewenvironment{itemize}
  {\setlength\pltopsep{\sa@sp@listsepskipamount}\begin{compactitem}}
  {\end{compactitem}}
% figures and tables
\RequirePackage{graphicx}
\RequirePackage{wrapfig}
\RequirePackage{subcaption}
\RequirePackage[justification=centering,labelsep=period]{caption}
\RequirePackage{placeins}
\RequirePackage{multirow}
\RequirePackage{makecell}
\RequirePackage{tabularx}
\setcapindent{0em}
\providecommand\tabcaption{\def\@captype{table}\captionabove}
\providecommand\figcaption{\def\@captype{figure}\caption}
\renewcommand\theadfont{\small}
\setlength{\tabcolsep}{3pt}
\setlength{\extrarowheight}{1pt}
\renewcommand\thetable{\arabic{table}}
\renewcommand\thefigure{\arabic{figure}}
\@addtoreset{figure}{sa@@th}
\@addtoreset{table}{sa@@th}
% floats in general
\def\fps@figure{!ht}
\def\fps@table{!ht}
\renewcommand\topfraction{0.9} % max fraction of floats at top
\renewcommand\bottomfraction{0.8} % max fraction of floats at bottom
\setcounter{topnumber}{2}
\setcounter{bottomnumber}{2}
\setcounter{totalnumber}{4}
\setcounter{dbltopnumber}{2} % for 2-column pages
\renewcommand\dbltopfraction{0.9} % fit big float above 2-col. text
\renewcommand\textfraction{0.07} % allow minimal text w. figs
\renewcommand\floatpagefraction{0.89} % require fuller float pages
\renewcommand\dblfloatpagefraction{0.89} % require fuller float pages
% verbatim
\RequirePackage{verbatim}
\addto@hook\every@verbatim{\setlength\topsep{\sa@sp@verbsepskipamount}}


% Bibliography

\RequirePackage{cite}
% redefine bibliography title
\DeclareThreelangTerm\sa@refname
  {References}
  {\cyr\CYRL\cyri\cyrt\cyre\cyrr\cyra\cyrt\cyru\cyrr\cyra}
  {\cyr\CYRL\cyrii\cyrt\cyre\cyrr\cyra\cyrt\cyru\cyrr\cyra}
% customize thebibiography
\renewcommand*\bib@heading{%
  % \vspace{\sa@sp@baselineskipdiff}%
  \FloatBarrier
  \paragraph{\normalsize\sa@refname{\sa@lang}}}
\l@addto@macro\bib@beginhook{%
  \renewcommand\@biblabel[1]{\ \textbf{\textsf{#1.}}~}%
  \def\list#1#2{%
    \inparaenum #2%
    \def\@itemlabel{\@biblabel{\@arabic\c@enumiv}}%
    \def\@item[##1]{\refstepcounter{enumiv}\makelabel{##1}\ignorespaces}}%
  \let\endlist\endinparaenum
  \def\@lbibitem[#1]#2{%
    \@skiphyperreftrue\H@item[%
    \ifx\Hy@raisedlink\@empty
      \hyper@anchorstart{cite.\thesa@@th.#2\@extra@b@citeb}%
      \@BIBLABEL{#1}\hyper@anchorend
    \else\Hy@raisedlink{%
      \hyper@anchorstart{cite.\thesa@@th.#2\@extra@b@citeb}%
      \hyper@anchorend}%
      \@BIBLABEL{#1}\fi]%
    \@skiphyperreffalse
    \if@filesw\begingroup
      \let\protect\noexpand
      \immediate\write\@auxout{\string\bibcite{\thesa@@th.#2}{#1}}%
    \endgroup\fi\ignorespaces}
  \def\@bibitem#1{%
    \@safe@activestrue\org@@bibitem{\thesa@@th.#1}\@safe@activesfalse
    \ignorespaces}
  \normalfont\sa@sp@bibfont
  \begin{spacing}{\sa@sp@bibspacing}%
  \begin{otherlanguage}{ukrainian}}
\renewcommand\bib@endhook{\end{otherlanguage}\end{spacing}}
% customize citations
\prependto@macro\@make@cite@list{\edef\@citeb{\thesa@@th.\@citeb}}


% Hyperlinks

\def\sa@d@hypercolors{citecolor=Blue3,linkcolor=Blue3,urlcolor=Blue3}
\sa@use\sa@editorial@hypercolors
\RequirePackage[
  \sa@d@hypercolors,
  unicode,linktocpage,colorlinks,breaklinks,
  hyperfigures=false,hyperfootnotes=false,hyperindex=true,
  ]{hyperref}
\urlstyle{rm}
\def\UrlSpecials{\do\/{\Url@slash}}
\def\Url@slash{\@ifnextchar/{\kern-.05em\mathchar47\kern-.2em}
  {\kern-.05em\mathchar47\kern-.05em\penalty\UrlBigBreakPenalty}}
\renewcommand\theHequation{\arabic{page}.\arabic{equation}}
\renewcommand\theHtheorem{\arabic{page}.\arabic{theorem}} 
\renewcommand\theHthm{\arabic{page}.\arabic{thm}}
\pdfstringdefDisableCommands{
  \let\kern\@gobble
}


% Math

% general math packages
\RequirePackage{amsmath}
\RequirePackage{mathtools}
% numbering
\@addtoreset{equation}{sa@@th}
\renewcommand\theequation{\arabic{equation}}
% misc commands
\newcommand{\hm}[1]{#1\nobreak\discretionary{}{\hbox{\ensuremath{#1}}}{}}
% symbols and fonts
\RequirePackage{amssymb}
\RequirePackage{maybemath}
\RequirePackage{dsfont}
\RequirePackage{esint}
\RequirePackage[mathcal]{euscript}
\RequirePackage{mathrsfs}
\newcommand\mathbfup[1]{\boldsymbol{\mathrm{#1}}}
\renewcommand\le{\leqslant}
\renewcommand\leq{\leqslant}
\renewcommand\ge{\geqslant}
\renewcommand\geq{\geqslant}
% accents
\makecommand\widebar[1]{\mkern1mu\overline{\mkern-1mu#1}}


% Theorems

\RequirePackage{amsthm}
\newcommand\DeclareTheorem[2]{%
  \sa@thm@newtheorems{#1}{#2}%
  \sa@thm@newenvironments{#1}%
  \g@addto@macro{\sa@thm@undeclaretheorems}{%
    \UndefineName{sa@the@#1}\UndefineName{sa@the@#1*}}}
\newcommand\sa@thm@declare[4]{%
  \sa@thm@declare@{#1}{\sa@ThreelangTerm{\sa@lang}{#2}{#3}{#4}}}
\newcommand\sa@thm@declare@[2]{%
  \sa@thm@newtheorems{#1}{#2}%
  \g@addto@macro{\sa@thm@resetcounters}{\setcounter{sa@thm@counter@#1}{0}}%
  \g@addto@macro{\sa@thm@declareenvironments}{\sa@thm@newenvironments{#1}}}
\newcommand\sa@thm@declareenvironments{}
\newcommand\sa@thm@resetcounters{}
\newcommand\sa@thm@newtheorems[2]{%
  \providecounter{sa@thm@counter@#1}%
  \newtheorem{sa@the@#1}[sa@thm@counter@#1]{#2}%
  \newtheorem*{sa@the@#1*}{#2}}
\newcommand\sa@thm@undeclaretheorems{}
\newcommand\sa@thm@newenvironments[1]{%
  \newenvironment{#1*}[1][]{\begin{sa@the@#1*}[##1]\upshape}{\end{sa@the@#1*}}%
  \newenvironment{#1}[1][]{\begin{sa@the@#1}[##1]\upshape}{\end{sa@the@#1}}}
% predefined theorems
\sa@thm@declare{Corollary}{Corollary}
  {\CYRS\cyrl\cyre\cyrd\cyrs\cyrt\cyrv\cyri\cyre}
  {\CYRN\cyra\cyrs\cyrl\cyrii\cyrd\cyro\cyrk}
\sa@thm@declare{Definition}{Definition}
  {\CYRO\cyrp\cyrr\cyre\cyrd\cyre\cyrl\cyre\cyrn\cyri\cyre}
  {\CYRO\cyrz\cyrn\cyra\cyrch\cyre\cyrn\cyrn\cyrya}
\sa@thm@declare{Lemma}{Lemma}
  {\CYRL\cyre\cyrm\cyrm\cyra}
  {\CYRL\cyre\cyrm\cyra}
\sa@thm@declare{Statement}{Statement}
  {\CYRU\cyrt\cyrv\cyre\cyrr\cyrzh\cyrd\cyre\cyrn\cyri\cyre}
  {\CYRT\cyrv\cyre\cyrr\cyrd\cyrzh\cyre\cyrn\cyrn\cyrya}
\sa@thm@declare{Theorem}{Theorem}
  {\CYRT\cyre\cyro\cyrr\cyre\cyrm\cyra}
  {\CYRT\cyre\cyro\cyrr\cyre\cyrm\cyra}
