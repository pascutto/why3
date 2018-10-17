
(* The purpose of this transformation is unify lsymbols with attributes
   immediately associated to them in the term. This is done by replacing those
   lsymbols with new one carrying the attributes. In effect, it allows
   counterexamples to carry those attributes.

   During typing, we add attributes on each generated variable of the form
   (x at label). The return expected counterexamples results will look like:
   x [@at:Old:loc:a.mlw:15:5:6] = 1
   This allows us to give more precise counterexamples as final output (saying
   if the counterexamples is actually at a label or not depending on its
   location).
*)
val attr_to_ls: Task.task Trans.trans
