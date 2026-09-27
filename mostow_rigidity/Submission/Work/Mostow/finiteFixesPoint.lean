import Mathlib
import Submission.Work.Mostow.finite_nearStab

/-!
# The pointwise stabiliser of a point is finite

For a discrete subgroup `Λ ≤ PO n 1` and a point `p` of `ℍⁿ`, the set of `c ∈ Λ` fixing `p` is
finite.

This is a small consequence of `finite_nearStab` (the near-stabiliser of the origin is finite):
if `c • p = p` then `c` also fixes `p` under `c⁻¹`, so

`hdist 0 (c • 0) ≤ hdist 0 p + hdist p (c • 0) = hdist 0 p + hdist (c⁻¹ • p) (c⁻¹ • (c • 0))
                = hdist 0 p + hdist p 0 = 2 * hdist 0 p`.

Hence the stabiliser of `p` is contained in the image of `{γ : Λ | hdist 0 (γ • 0) ≤ 2 hdist 0 p}`,
which is finite.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem finiteFixesPoint {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Λ)) (p : Submission.Mostow.E n) :
    {c : LeanEval.Geometry.MostowRigidity.PO n 1 | c ∈ Λ ∧ c • p = p}.Finite := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hIb : HypIsoData n := HypIsoData.ofProp hI
  have hfin : {γ : Λ | Submission.Mostow.hdist (0 : Submission.Mostow.E n)
      ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n))
      ≤ 2 * Submission.Mostow.hdist (0 : Submission.Mostow.E n) p}.Finite :=
    finite_nearStab hAb hIb hdisc (2 * Submission.Mostow.hdist 0 p)
  refine (hfin.image (fun γ : Λ => (γ : LeanEval.Geometry.MostowRigidity.PO n 1))).subset ?_
  intro c hc
  have hcl : c ∈ Λ := hc.1
  have hfix : c • p = p := hc.2
  rw [Set.mem_image]
  refine ⟨⟨c, hcl⟩, ?_, rfl⟩
  have h2 : c⁻¹ • p = p := by
    calc c⁻¹ • p = c⁻¹ • (c • p) := by rw [hfix]
      _ = (c⁻¹ * c) • p := (hAb.mul_smul c⁻¹ c p).symm
      _ = (1 : PO n 1) • p := by rw [inv_mul_cancel]
      _ = p := hAb.one_smul p
  have h3 : c⁻¹ • (c • (0 : Submission.Mostow.E n)) = (0 : Submission.Mostow.E n) := by
    rw [← hAb.mul_smul c⁻¹ c (0 : Submission.Mostow.E n), inv_mul_cancel, hAb.one_smul]
  have h1 := hIb.isom_smul c⁻¹ p (c • (0 : Submission.Mostow.E n))
  rw [h2, h3] at h1
  have hpc0 : hdist p (c • (0 : Submission.Mostow.E n)) =
      hdist (0 : Submission.Mostow.E n) p := by
    rw [← h1, hIb.symm p 0]
  calc hdist (0 : Submission.Mostow.E n) (c • (0 : Submission.Mostow.E n))
      ≤ hdist (0 : Submission.Mostow.E n) p + hdist p (c • (0 : Submission.Mostow.E n)) :=
        hIb.triangle _ _ _
    _ = 2 * hdist (0 : Submission.Mostow.E n) p := by rw [hpc0]; ring

end Work.Mostow
