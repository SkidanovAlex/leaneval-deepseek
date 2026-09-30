import Mathlib
import Submission.Work.HomologyMV.Concrete
import Submission.Work.HomologyMV.LinAlg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyMV

/-- Surjectivity certificate for the concrete Mayer–Vietoris matrices: `φ_k` is surjective for every `k ≥ 1` (from the explicit inverses of `φ₁`, `φ₂` and a right inverse of `φ₃`; in degrees `≥ 4` both model groups are zero). -/
theorem wConcrete_surj : SurjCert wConcrete := by
  intro k hk
  rcases lt_or_ge k 4 with hk4 | hk4
  · have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl
    · exact range_toLin'_eq_top_of_mul_eq_one phi1Mat inv1Mat phi1Mat_mul_inv1Mat
    · exact range_toLin'_eq_top_of_mul_eq_one phi2Mat inv2Mat phi2Mat_mul_inv2Mat
    · exact range_toLin'_eq_top_of_mul_eq_one phi3Mat psi3Mat phi3Mat_mul_psi3Mat
  · have hS : Subsingleton (Fin (rankN k) → ℤ) := subsingleton_modelN_of_ge k hk4
    exact range_eq_top_of_subsingleton_target (Matrix.toLin' (allPhi k))

end Work.HomologyMV
