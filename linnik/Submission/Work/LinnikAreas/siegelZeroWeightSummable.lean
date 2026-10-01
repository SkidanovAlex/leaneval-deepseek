import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.norm_Hk_le
import Submission.Work.LinnikAreas.summable_zeroMult_norm_mul
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.LinnikAreas.kernelStripInvSqBound
import Submission.Work.LinnikAreas.xiCZeroInvSqTailBound
import Submission.Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general

/-!
# Summability of the Hecke--Heath-Brown zero weight `ρ ↦ ord(ρ)·‖Hk L K ((1-ρ)𝓛)‖`

For every Dirichlet character `χ` of level `q` (`q ≠ 0`), every `L K : ℝ`, the
multiplicity-weighted sum of the kernel values over the zeros of the completed
`L`-function of the primitive character inducing `χ` converges absolutely:

`Σ_ρ (ord_ρ : ℝ)·‖Hk L K ((1-ρ)·log q)‖ < ∞`.

The zeros are the non-trivial zeros of `L(s,χ)`, which lie in the closed critical
strip `0 ≤ Re ρ ≤ 1`; on that strip the kernel obeys the uniform inverse-square bound
`‖Hk L K ((1-ρ)log q)‖ ≤ A/‖ρ‖²` (`kernelStripInvSqBound`), and the zeros have
counting function `≪ T log T` in `‖ρ‖ ≤ T` (Jensen / Riemann–von Mangoldt), which is
exactly enough to sum the inverse-square weight along dyadic annuli.

* non-principal `χ`: `Σ_u ord_u(Λ(χ*,·))·‖Φ u‖` is summable whenever `Φ` decays like
  `A/‖u‖²` on the critical strip (`summable_zeroMult_norm_mul`, the absolute
  summability of the divisor-weighted zero sum);
* principal `χ`: `zeroMult 1 ρ` is the vanishing order of the completed Riemann zeta
  function `Λ` at `ρ`, which is dominated by the vanishing order of the entire
  completion `Ξ(s) = 1/2 + (1/2)s(s-1)Λ₀(s)` (`zeroMult_one_apply`), whose zeros are
  counted by `xiE_zeroCount`; the corresponding inverse-square tail bound is
  `xiCZeroInvSqTailBound`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- `zeroMult χ ·` is the vanishing order of the completed `L`-function of the primitive
character inducing `χ`. -/
theorem zeroMult_eq_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (ρ : ℂ) :
    Work.LinnikContract.zeroMult χ ρ
      = analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ := by
  rw [Work.LinnikContract.zeroMult]

/-- Zeros of the entire completion `Ξ` lie in the closed critical strip. -/
lemma xiC_zeros_strip {u : ℂ} (hu : Work.LinnikAreas.xiC u = 0) :
    0 ≤ u.re ∧ u.re ≤ 1 :=
  Commons.NumberTheory.Zeta.xiE_LG_zeros_strip hu

/-- **Summability of the inverse-square zero weight of the completed zeta function.**

`Σ_ρ ord_{Ξ}(ρ)·‖Hk L K ((1-ρ)𝓛)‖ < ∞` for `1 < q` and arbitrary real `L K`. -/
theorem summable_xiC_zeroMult_Hk {q : ℕ} [NeZero q] (hq : 1 < q) (L K : ℝ) :
    Summable (fun ρ : ℂ => (analyticOrderNatAt xiC ρ : ℝ)
      * ‖Work.LinnikContract.Hk L K ((1 - ρ) * (Real.log q : ℂ))‖) := by
  have h𝓛 : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨A, hApos, hA⟩ := kernelStripInvSqBound h𝓛 L K
  obtain ⟨C, hCpos, hC⟩ := xiCZeroInvSqTailBound
  set f : ℂ → ℝ := fun ρ => (analyticOrderNatAt xiC ρ : ℝ)
    * ‖Work.LinnikContract.Hk L K ((1 - ρ) * (Real.log q : ℂ))‖ with hfdef
  have hfnn : ∀ u : ℂ, 0 ≤ f u := fun u => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  refine Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound (f := f) (C := A * C) hfnn ?_ ?_
  · -- the zeros in the disk of radius `2` are finite
    have hfin : ({z : ℂ | xiC z = 0} ∩ Metric.closedBall (0 : ℂ) 2).Finite :=
      boxMaxZeroAux.finite_entire_zeros_closedBall boxMaxZeroAux.xiEntire_analytic
        boxMaxZeroAux.xiEntire_zero_ne 0 2
    refine ⟨∑ u ∈ hfin.toFinset, f u, ?_⟩
    intro s hs
    set Z : Finset ℂ := hfin.toFinset with hZdef
    have hZmem : ∀ u : ℂ, u ∈ Z ↔ xiC u = 0 ∧ ‖u‖ ≤ 2 := by
      intro u
      simp only [hZdef, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hzero : ∀ u ∈ s ∪ Z, u ∉ Z → f u = 0 := by
      intro u hu huz
      by_contra hfu
      have hord : analyticOrderNatAt xiC u ≠ 0 := by
        intro h0
        exact hfu (by rw [hfdef]; simp [h0])
      have hzu : xiC u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
      have hus : u ∈ s := by
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · exact absurd h huz
      have hnorm : ‖u‖ ≤ 2 := by
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hs u hus
      exact huz ((hZmem u).mpr ⟨hzu, hnorm⟩)
    calc ∑ u ∈ s, f u ≤ ∑ u ∈ s ∪ Z, f u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            (fun i _ _ => hfnn i)
      _ = ∑ u ∈ Z, f u := (Finset.sum_subset (s₁ := Z) (s₂ := s ∪ Z)
            Finset.subset_union_right hzero).symm
  · -- the tail: the kernel decays like `A/‖u‖²` on the critical strip
    intro s hs
    have hbound : ∀ u ∈ s, f u ≤ (analyticOrderNatAt xiC u : ℝ) * (A / ‖u‖ ^ 2) := by
      intro u hu
      by_cases h0 : analyticOrderNatAt xiC u = 0
      · have hf0 : f u = 0 := by rw [hfdef]; simp [h0]
        simp [hf0, h0]
      · have hzu : xiC u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero h0
        have hstrip := xiC_zeros_strip hzu
        have hle : ‖Work.LinnikContract.Hk L K ((1 - u) * (Real.log q : ℂ))‖ ≤ A / ‖u‖ ^ 2 :=
          hA u hstrip.1 hstrip.2 (le_of_lt (hs u hu))
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
    calc ∑ u ∈ s, f u ≤ ∑ u ∈ s, (analyticOrderNatAt xiC u : ℝ) * (A / ‖u‖ ^ 2) :=
          Finset.sum_le_sum hbound
      _ = A * ∑ u ∈ s, (analyticOrderNatAt xiC u : ℝ) / ‖u‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun u _ => by ring)
      _ ≤ A * C := mul_le_mul_of_nonneg_left (hC s hs) hApos.le

/-- **The principal character.**  Summability of the multiplicity-weighted kernel sum over the
zeros of the completed Riemann zeta function. -/
theorem summable_zeroMult_one_Hk {q : ℕ} [NeZero q] (hq : 1 < q) (L K : ℝ) :
    Summable (fun ρ : ℂ => (Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ : ℝ)
      * ‖Work.LinnikContract.Hk L K ((1 - ρ) * (Real.log q : ℂ))‖) := by
  have hle := summable_xiC_zeroMult_Hk (q := q) hq L K
  refine Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (fun ρ => ?_) hle
  exact mul_le_mul_of_nonneg_right (zeroMult_one_apply q ρ) (norm_nonneg _)

/-- **The non-principal characters.**  The primitive character inducing a non-principal `χ`
is non-principal, so the absolute summability of the divisor-weighted zero sum
(`summable_zeroMult_norm_mul`) applies. -/
theorem summable_zeroMult_Hk_of_ne_one {q : ℕ} [NeZero q] (hq : 1 < q) (L K : ℝ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Summable (fun ρ : ℂ => (Work.LinnikContract.zeroMult χ ρ : ℝ)
      * ‖Work.LinnikContract.Hk L K ((1 - ρ) * (Real.log q : ℂ))‖) := by
  have h𝓛 : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  obtain ⟨A, hApos, hA⟩ := kernelStripInvSqBound h𝓛 L K
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hψne : χ.primitiveCharacter ≠ (1 : DirichletCharacter ℂ χ.conductor) :=
    boxMaxZeroAux.primitiveCharacter_ne_one_of_ne_one χ hχ
  have hΦ : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ →
      ‖Work.LinnikContract.Hk L K ((1 - u) * (Real.log q : ℂ))‖ ≤ A / ‖u‖ ^ 2 :=
    fun u h1 h2 h3 => hA u (le_of_lt h1) (le_of_lt h2) h3
  have hsum := summable_zeroMult_norm_mul (N := χ.conductor) χ.primitiveCharacter hψne
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (Φ := fun u => Work.LinnikContract.Hk L K ((1 - u) * (Real.log q : ℂ))) hApos hΦ
  refine hsum.congr (fun ρ => ?_)
  rw [zeroMult_eq_order χ ρ]

/-- **Summability of the multiplicity-weighted kernel sum over the zeros of `L(s,χ)`.**

For every `L K : ℝ` and every Dirichlet character `χ` of non-zero level `q`,
`Σ_ρ ord_ρ · ‖Hk L K ((1-ρ)·log q)‖` converges; the sum runs over the non-trivial zeros
`ρ` of `L(s,χ)` (counted with multiplicity via the completed `L`-function of the primitive
character inducing `χ`). -/
theorem siegelZeroWeightSummable {q : ℕ} [NeZero q] (L K : ℝ) (χ : DirichletCharacter ℂ q) :
    Summable (fun ρ : ℂ => (Work.LinnikContract.zeroMult χ ρ : ℝ)
      * ‖Work.LinnikContract.Hk L K ((1 - ρ) * (Real.log q : ℂ))‖) := by
  rcases Nat.lt_or_ge 1 q with hq | hq
  · by_cases hχ : χ = 1
    · subst hχ
      exact summable_zeroMult_one_Hk hq L K
    · exact summable_zeroMult_Hk_of_ne_one hq L K χ hχ
  · -- `q = 1`: then `log q = 0`, so the argument of `Hk` is `0` and `Hk L K 0 = 0`
    have hq1 : q = 1 := by
      have hpos : 0 < q := NeZero.pos q
      omega
    have hlog : Real.log (q : ℝ) = 0 := by
      rw [show (q : ℝ) = 1 by exact_mod_cast hq1]; simp
    have hzero : (fun ρ : ℂ => (Work.LinnikContract.zeroMult χ ρ : ℝ)
        * ‖Work.LinnikContract.Hk L K ((1 - ρ) * (Real.log q : ℂ))‖) = fun _ => 0 := by
      funext ρ
      rw [hlog, Complex.ofReal_zero, mul_zero]
      simp [Work.LinnikContract.Hk, Work.LinnikContract.F2]
    rw [hzero]
    exact summable_zero

end

end Work.LinnikAreas
