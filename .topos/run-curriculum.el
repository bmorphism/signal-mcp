;;; run-curriculum.el --- Execute org-babel curriculum in batch mode

(require 'org)
(setq org-confirm-babel-evaluate nil)

;; Load ob-jank
(add-to-list 'load-path "/Users/barton/ies/signal-mcp/.topos")
(require 'ob-jank)

;; Enable required languages
(org-babel-do-load-languages
 'org-babel-load-languages
 '((shell . t)
   (sql . t)
   (jank . t)))

;; Open the test curriculum
(find-file "TEST_CURRICULUM.org")

;; Execute all code blocks
(org-babel-execute-buffer)

;; Save results
(write-file "/tmp/curriculum-executed.org")

(message "✅ Curriculum executed successfully!")
(message "✅ Output saved to /tmp/curriculum-executed.org")

;; Exit
(kill-emacs 0)
