import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

theorem finrank_quotient_eq_add_finrank_map {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {P Q : Submodule K V} (h : P ≤ Q) :
    Module.finrank K (V ⧸ P) =
      Module.finrank K (V ⧸ Q) + Module.finrank K (Submodule.map P.mkQ Q) := by
  -- Rank-nullity in the ambient space `V ⧸ P`, for the submodule `Q.map P.mkQ`,
  -- combined with the third isomorphism theorem `(V ⧸ P) ⧸ (Q.map P.mkQ) ≃ V ⧸ Q`.
  rw [← Submodule.finrank_quotient_add_finrank (Q.map P.mkQ),
    LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotient P Q h)]

end Work.RB
