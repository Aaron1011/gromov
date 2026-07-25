import Mathlib

/-!
# Naming of the multiplicative structure theorem for finitely generated abelian groups

`CommGroup.equiv_free_prod_prod_multiplicative_zmod` in
`Mathlib/GroupTheory/FiniteAbelian/Basic.lean` is the multiplicative counterpart of
`AddCommGroup.equiv_free_prod_directSum_zmod`, but does not share its name. This provides the
matching name, which is what the rest of this project uses.

Upstreaming status: a rename proposal, not new mathematics — the statement is unchanged.
-/

namespace CommGroup

alias equiv_free_prod_directSum_zmod := equiv_free_prod_prod_multiplicative_zmod

end CommGroup
