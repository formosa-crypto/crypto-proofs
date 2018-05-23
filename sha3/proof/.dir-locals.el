((easycrypt-mode .
  ((eval .
    (flet ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
           (setq easycrypt-load-path `(,(pre "smart_counter"))))))))
