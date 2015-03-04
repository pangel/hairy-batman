Utilisation
-----------
Commencer par faire `make`.

Lire le code
------------
Le plus agréable est de faire `make html` puis d'ouvrir `./html/toc.html` dans un navigateur.

Il vaut mieux lire `init` puis `shift_lemmas` puis `reg_nar_lemmas`.

Recompiler
----------
Si une dépendance d'un fichier est modifiée (par exemple `init.v`), fermer le fichier dans CoqIDE, refaire `make` et ré-ouvrir le fichier.

Ajouter un fichier `.v`
------------------------
Si vous ajoutez une dépendance, faire `coq_makefile *.v > Makefile && make`

Description du projet
----------------------
https://wikimpri.dptinfo.ens-cachan.fr/lib/exe/fetch.php?media=cours:upload:2-7-2-projet.pdf

Preuve de normalisation
----------------------
http://homepage.divms.uiowa.edu/~astump/papers/pstt-2010.pdf

Objectif
---------------------
https://www.youtube.com/watch?v=KgxEPBFuofM (merci Joseph)

### TODO : `admits`

1. `lemmas_regularity.v`, simple et moyen je pense
2. `lemmas_narrowing.v`, ?
3. `env_subst.v`, probablement dur

### TODO : rapport

:'(
