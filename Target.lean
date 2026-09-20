import TriangleNumerical.Assembly

/-!
Final proof entry point: only the entropy-certificate theorem is requested.
The actual theorem is proved in TriangleNumerical/Assembly.lean.
Do not import Challenge here: it is the separate reference statement for Comparator.
-/

example : TriangleNumerical.EntropyCertificateProposition :=
  TriangleNumerical.entropy_certificate

#check TriangleNumerical.entropy_certificate
#print axioms TriangleNumerical.entropy_certificate
