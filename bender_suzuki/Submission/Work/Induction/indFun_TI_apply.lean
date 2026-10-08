import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

/-- Summation over a subgroup of an indicator-type summand: for a subgroup `S ≤ G` and a
function `f` on `S`, the sum over `G` of the summand which is `f x` when `x ∈ S` and `0`
otherwise equals the sum of `f` over `S`.

This is the bookkeeping lemma converting the `∑_{x : G}` in the definition of `indFun` into
a sum over a subgroup (here the normalizer). -/
theorem sum_dite_mem_subgroup {G : Type*} [Group G] [Fintype G] (S : Subgroup G) (f : S → ℂ) :
    (∑ x : G, dite (x ∈ S) (fun hx => f ⟨x, hx⟩) (fun _ => 0)) = ∑ x : S, f x := by
  let F : G → ℂ := fun x => dite (x ∈ S) (fun hx => f ⟨x, hx⟩) (fun _ => 0)
  have hFs : ∀ x : G, (if x ∈ S then F x else 0) = F x := by
    intro x
    by_cases hx : x ∈ S <;> simp [F, hx]
  calc (∑ x : G, dite (x ∈ S) (fun hx => f ⟨x, hx⟩) (fun _ => 0))
      = ∑ x : G, F x := rfl
    _ = ∑ x : G, (if x ∈ S then F x else 0) := by simp only [hFs]
    _ = ∑ x ∈ Finset.univ.filter (fun x => x ∈ S), F x := by rw [Finset.sum_filter]
    _ = ∑ a : Subtype (fun x : G => x ∈ S), F a :=
        Finset.sum_subtype (Finset.univ.filter (fun x => x ∈ S)) (fun x => by simp) F
    _ = ∑ a : S, f a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        simp only [F, dite_eq_left a.2]

-- TI restriction formula.  Multiplying by `|H|` clears the `|H|⁻¹` in `indFun`, leaving
-- `∑_{x : x*h*x⁻¹ ∈ H} φ (x*h*x⁻¹)`.  For `h ≠ 1` the condition `x*h*x⁻¹ ∈ H` forces
-- `x ∈ N_G(H)`: if `x ∉ N_G(H)` then `H ⊓ conj x • H = ⊥` (TI), so `x*h*x⁻¹ ∈ H` implies
-- `x*h*x⁻¹ = 1`, i.e. `h = 1`.  Conversely `x ∈ N_G(H)` gives `x*h*x⁻¹ ∈ H` (`conjMem`).
theorem indFun_TI_apply {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    (hTI : Work.Induction.IsTI H) (h : H) (hh : h ≠ 1) :
    (Nat.card H : ℂ) * Work.Induction.resFun H (Work.Induction.indFun H φ) h
      = ∑ x : Work.Induction.normalizer H, φ (Work.Induction.conjMem H x h) := by
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  rw [resFun_apply, indFun_apply_def, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  -- For `h ≠ 1`, `x * h * x⁻¹ ∈ H` holds exactly for `x` in the normalizer of `H`.
  have hstep : ∀ x : G, dite (x * ↑h * x⁻¹ ∈ H) (fun hx => φ ⟨x * ↑h * x⁻¹, hx⟩) (fun _ => 0)
      = dite (x ∈ normalizer H) (fun hx => φ (conjMem H ⟨x, hx⟩ h)) (fun _ => 0) := by
    intro x
    by_cases hxN : x ∈ normalizer H
    · -- `x ∈ N_G(H)`: both branches are taken and the two arguments of `φ` agree.
      have hxH : x * ↑h * x⁻¹ ∈ H := ((Subgroup.mem_normalizer_iff.mp hxN) ↑h).mp h.2
      rw [dite_eq_left hxH, dite_eq_left hxN]
      exact congrArg φ (Subtype.ext rfl)
    · -- `x ∉ N_G(H)`: TI forces `x * h * x⁻¹ = 1`, so the condition `∈ H` fails (`h ≠ 1`).
      have hxH : ¬ (x * ↑h * x⁻¹ ∈ H) := by
        intro hmem
        have hinf : x * ↑h * x⁻¹ ∈ H ⊓ (MulAut.conj x • H) :=
          ⟨hmem, (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr
            ⟨↑h, h.2, by rw [MulAut.smul_def, MulAut.conj_apply]⟩⟩
        have hbot : x * ↑h * x⁻¹ = 1 := by
          rwa [hTI x hxN, Subgroup.mem_bot] at hinf
        exact hh (Subtype.ext (by
          calc (h : G) = x⁻¹ * (x * ↑h * x⁻¹) * x := by group
            _ = x⁻¹ * 1 * x := by rw [hbot]
            _ = 1 := by group))
      rw [dite_eq_right hxH, dite_eq_right hxN]
  rw [Finset.sum_congr rfl (fun x _ => hstep x)]
  exact sum_dite_mem_subgroup (normalizer H) (fun x => φ (conjMem H x h))

end Work.Induction
