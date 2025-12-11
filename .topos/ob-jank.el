;;; ob-jank.el --- Babel Functions for Jank    -*- lexical-binding: t; -*-

;; Copyright (C) 2025 Barton Rhodes

;; Author: Barton Rhodes
;; Keywords: literate programming, reproducible research, jank
;; URL: https://github.com/barton/topos-navigator

;; This file provides org-babel support for the Jank language.
;; Jank is a Clojure-like language with LLVM backend and C++ interop.
;; See: https://jank-lang.org/

;;; Commentary:

;; Support for evaluating Jank code blocks in org-mode.

;; Requirements:
;; - Jank compiler installed (https://jank-lang.org/)
;; - jank binary in PATH

;; Usage:
;; Add to your .emacs or init.el:
;;   (require 'ob-jank)
;;   (org-babel-do-load-languages
;;    'org-babel-load-languages
;;    '((jank . t)))

;;; Code:

(require 'org-macs)
(require 'ob)
(require 'ob-eval)

;; Add jank to the list of supported languages
(defvar org-babel-tangle-lang-exts)
(add-to-list 'org-babel-tangle-lang-exts '("jank" . "jank"))

;; Default header arguments for jank code blocks
(defvar org-babel-default-header-args:jank '())

;; Customization: jank command
(defcustom ob-jank-command (or (executable-find "jank")
                               "/Users/barton/.local/bin/jank")
  "Command to execute jank code.
Default is the jank binary found in PATH or known location."
  :type 'string
  :group 'org-babel)

;; Customization: jank command-line arguments
(defcustom ob-jank-cli-args '("eval")
  "Default command-line arguments for jank.
By default, uses 'eval' to evaluate code directly."
  :type '(repeat string)
  :group 'org-babel)

(defun org-babel-execute:jank (body params)
  "Execute a block of Jank code with org-babel.
This function is called by `org-babel-execute-src-block'.
BODY is the code block content.
PARAMS is a property list of header arguments."
  (let* ((processed-params (org-babel-process-params params))
         ;; Get variables from params
         (vars (org-babel--get-vars processed-params))
         ;; Get result params
         (result-params (cdr (assq :result-params processed-params)))
         ;; Get session (not supported yet)
         (session (cdr (assq :session processed-params)))
         ;; Expand body with variable definitions
         (full-body (org-babel-expand-body:generic
                     body params
                     (org-babel-variable-assignments:jank vars)))
         ;; Build jank command
         (cmd (concat ob-jank-command " "
                     (mapconcat 'identity ob-jank-cli-args " "))))

    ;; Check if jank is available
    (unless (file-executable-p ob-jank-command)
      (error "Jank command not found or not executable: %s" ob-jank-command))

    ;; Session not supported yet
    (when (not (string= session "none"))
      (error "Jank does not support sessions yet"))

    ;; Execute jank code
    (let ((result (org-babel-eval cmd full-body)))
      ;; Process result based on result-params
      (org-babel-result-cond result-params
        result  ; raw output
        (org-babel-jank-table-or-string result)))))  ; parsed output

(defun org-babel-variable-assignments:jank (vars)
  "Return a list of Jank statements assigning the block's variables.
VARS is a list of pairs (NAME . VALUE)."
  (mapcar
   (lambda (pair)
     (format "(def %s %s)"
             (car pair)
             (org-babel-jank-var-to-jank (cdr pair))))
   vars))

(defun org-babel-jank-var-to-jank (var)
  "Convert an elisp value VAR into a Jank representation."
  (cond
   ((null var) "nil")
   ((eq var t) "true")
   ((numberp var) (number-to-string var))
   ((stringp var) (format "\"%s\"" var))
   ((listp var)
    (format "[%s]"
            (mapconcat 'org-babel-jank-var-to-jank var " ")))
   (t (format "%S" var))))

(defun org-babel-jank-table-or-string (result)
  "Convert RESULT into an appropriate elisp value.
If RESULT looks like a table, then convert it into an
Emacs-lisp table, otherwise return it as a string."
  (let ((result (org-babel-string-read result)))
    (if (listp result)
        (mapcar (lambda (el)
                  (if (eq el 'hline)
                      el
                    (if (and (stringp el) (string-match "\\S-" el))
                        (org-babel-read el)
                      el)))
                result)
      result)))

(defun org-babel-prep-session:jank (_session _params)
  "Prepare SESSION according to the header arguments specified in PARAMS.
Jank sessions are not currently supported."
  (error "Jank does not support sessions"))

(provide 'ob-jank)

;;; ob-jank.el ends here
