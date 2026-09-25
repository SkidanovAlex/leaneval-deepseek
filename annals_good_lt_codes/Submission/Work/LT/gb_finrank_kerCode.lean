import Mathlib
import Submission.Work.LT.good_base_defs

namespace Work.LT

/-- The parity-check code `ker H` for an `r × D` matrix `H` has dimension at least `D - r`: rank-nullity for the map `v ↦ (k ↦ ∑ i, H k i * v i)`. -/
theorem gb_finrank_kerCode {D r : ℕ} (H : Fin r → Fin D → ZMod 2) :
    D ≤ r + GB.frk (GB.kerCode H) := by
  -- The matrix-vector map `v ↦ (k ↦ ∑ i, H k i * v i)`, whose kernel is the code `ker H`.
  let F : (Fin D → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
    LinearMap.pi (fun k => GB.dotLin (H k))
  have hker : F.ker = GB.kerCode H := by
    show (LinearMap.pi (fun k => GB.dotLin (H k))).ker = GB.kerCode H
    rw [LinearMap.ker_pi]
    rfl
  -- Rank-nullity for `F`.
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  have hdom : Module.finrank (ZMod 2) (Fin D → ZMod 2) = D := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have hrange : Module.finrank (ZMod 2) F.range ≤ r := by
    calc Module.finrank (ZMod 2) F.range
        ≤ Module.finrank (ZMod 2) (Fin r → ZMod 2) := Submodule.finrank_le _
      _ = r := by rw [Module.finrank_fintype_fun_eq_card]; simp
  have hkerfin : Module.finrank (ZMod 2) F.ker = GB.frk (GB.kerCode H) := by
    rw [hker]; rfl
  rw [hdom] at hrn
  calc D = Module.finrank (ZMod 2) F.range + Module.finrank (ZMod 2) F.ker := hrn.symm
    _ ≤ r + GB.frk (GB.kerCode H) := Nat.add_le_add hrange (le_of_eq hkerfin)

end Work.LT
