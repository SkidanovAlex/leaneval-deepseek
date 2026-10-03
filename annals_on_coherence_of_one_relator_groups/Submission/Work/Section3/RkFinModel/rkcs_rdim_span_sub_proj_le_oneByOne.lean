import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.Section3.rdim_span_le_oneByOne

universe u

namespace Work.Section3.RkFinModel

theorem rkcs_rdim_span_sub_proj_le_oneByOne {S : Type u} [Ring S]
    [Work.ORHughesFree.VonNeumannRegularRing S] {n : ℕ}
    (ρ : Work.ORHughesFree.SylvesterRank S)
    (E : Module.End S (Fin n → S)) (hE : E * E = E) (u : Fin n → S) {e : S} (he : e * e = e)
    (hpe : (1 - e) • u ∈ LinearMap.range E) :
    Work.ORHughesFree.NaturalExtension.rdim ρ
        (Submodule.span S ({u - E u} : Set (Fin n → S)))
      ≤ ρ.rk 1 1 (Work.ORHughesFree.oneByOne e) := by
  -- Every `S`-linear endomorphism of `S^n` commutes with left multiplication by `e`: in the
  -- matrix model `E` is `x ↦ x ᵥ* A`, and `e • (x ᵥ* A) = (e • x) ᵥ* A` by associativity.
  have hcomm : ∀ x : Fin n → S, E (e • x) = e • E x := fun x => by
    have hA : Matrix.toLinearMapRight' (Matrix.toLinearMapRight'.symm E) = E :=
      Matrix.toLinearMapRight'.apply_symm_apply E
    conv_lhs => rw [← hA]
    conv_rhs => rw [← hA]
    exact (Matrix.toLinearMapRight' (Matrix.toLinearMapRight'.symm E)).map_smul e x
  -- `(1-e) • u` lies in `range E`, say it equals `E w`; then `(1-E)` kills it.
  obtain ⟨w, hw⟩ := hpe
  have hEE : E (E w) = E w := by rw [← Module.End.mul_apply, hE]
  -- Hence `(1-E)(e • u) = (1-E) u`, because `u = e • u + (1-e) • u`.
  have hstep : (1 - E) (e • u) = (1 - E) u := by
    have h1 : (1 - E) ((1 - e) • u) = 0 := by
      rw [← hw, LinearMap.sub_apply]
      simp [hEE]
    have h2 : (1 - E) u = (1 - E) (e • u) + (1 - E) ((1 - e) • u) := by
      have hsplit : e • u + (1 - e) • u = u := by
        rw [← add_smul, show e + (1 - e) = 1 from by abel, one_smul]
      calc (1 - E) u = (1 - E) (e • u + (1 - e) • u) := by rw [hsplit]
        _ = (1 - E) (e • u) + (1 - E) ((1 - e) • u) := by rw [map_add]
    rw [h1, add_zero] at h2
    exact h2.symm
  -- So `e` fixes `u - E u`, and the conclusion is `rdim_span_le_oneByOne`.
  refine Work.Section3.rdim_span_le_oneByOne ρ e (u - E u) ?_
  calc e • (u - E u) = e • u - e • E u := by rw [smul_sub]
    _ = e • u - E (e • u) := by rw [hcomm u]
    _ = (1 - E) (e • u) := by rw [LinearMap.sub_apply]; simp
    _ = (1 - E) u := hstep
    _ = u - E u := by rw [LinearMap.sub_apply]; simp

end Work.Section3.RkFinModel
