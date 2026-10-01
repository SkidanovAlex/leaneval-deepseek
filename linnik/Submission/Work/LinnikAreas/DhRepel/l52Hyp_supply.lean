/-
# Supplying Heath-Brown's Lemma 3.1 input `L52Hyp` (Deuring–Heilbronn repulsion)

Heath-Brown (1992), Lemma 3.1, in the window form consumed by §5/§6 of the paper: there are
absolute constants `c > 0` and a threshold `q₀` such that for every non-principal `χ` modulo
`q ≥ q₀` and all `ε, δ ∈ (0,1)`, the logarithmic derivative of `L(·, χ*)` (`χ*` the primitive
character inducing `χ`) is bounded by `(c + ε/4) log q` once the sum over the zeros of the
completed `L`-function lying in the window `‖1 + i·Im s - ρ‖ ≤ δ` is subtracted.

The proof is the *Hadamard partial-fraction* route (no Burgess input):

* `partialFraction_eq` gives `-Λ'/Λ(s) = -Λ'/Λ(s₀) - Σ_ρ (1/(s-ρ) - 1/(s₀-ρ))` for any two points
  with `Λ ≠ 0`; taking `s₀ = 1 - conj s` and using the functional equation
  (`logDeriv Λ(1-s) = -log N - conj (logDeriv Λ s)`) turns this into the *symmetric* identity
  `log N + 2 Re(Λ'/Λ)(s) = Σ_ρ Re (1/(s-ρ) + 1/(conj s + ρ - 1))` (the limit of `kernSum`),
* every summand of that sum is non-negative (zeros of `Λ` lie in `0 < Re ρ < 1`, while
  `Re s > 1`), so the truncated sums are monotone and bounded by their limit,
* the windowed sum `winSum` is dominated twice by the truncated sums: directly by the first half
  (`winSum_le_firstSum`), and by the second half via the reflection `ρ ↦ 1 - conj ρ`, which
  preserves the zero multiplicities (`divisor_refl`) and exchanges the two kernels exactly
  (`winSum_le_secondSum`),
* hence `2 · winSum ≤ log N + 2 Re(Λ'/Λ)(s)`, i.e. `-Re(Λ'/Λ)(s) + winSum ≤ (log N)/2`,
* finally `logDeriv Λ = logDeriv L + logDeriv γ` and the archimedean estimate
  `Re (logDeriv γ)(s) ≤ log π / 2 + (log (2 + |Im s|) + 8)/2` give the statement in the form
  `L52Hyp` with the absolute constants `c = 2`, `q₀ = 10 ^ 6`.
-/
import Mathlib
import Submission.Work.LinnikAreas.DhRepel.Defs
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_defs
import Submission.Work.LinnikAreas.DhRepel.divisor_refl
import Submission.Work.LinnikAreas.DhRepel.tendsto_kernSum

open Complex DirichletCharacter Metric Filter
open scoped Real Topology BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.LinnikAreas.DhRepel

/-! ## Elementary auxiliary facts -/

/-- A monotone real function converging at `atTop` never exceeds its limit. -/
lemma le_of_monotone_tendsto {f : ℝ → ℝ} (hmono : Monotone f) {L : ℝ}
    (ht : Tendsto f atTop (𝓝 L)) (R : ℝ) : f R ≤ L := by
  have hle : ∀ᶠ R' in atTop, f R ≤ f R' :=
    eventually_atTop.mpr ⟨R, fun R' hR' => hmono hR'⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht hle

/-- The divisor of the completed `L`-function of a non-principal character is non-negative. -/
lemma divisor_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (R : ℝ) (u : ℂ) :
    (0:ℝ) ≤ (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) :=
  Commons.Analysis.Complex.divisor_nonneg_on_closedBall
    (fun z _ => (differentiable_completedLFunction hχ).analyticAt z) u

/-- The (integer-valued) divisor of `Λ` in a ball has finite support. -/
lemma divisor_hasFiniteSupport {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (R : ℝ) : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ)) := by
  have h := MeromorphicOn.divisor_support_finite_of_subset
    (f := completedLFunction χ) (U := Metric.closedBall (0:ℂ) R) (V := Metric.closedBall (0:ℂ) R)
    (fun z _ => ((differentiable_completedLFunction hχ).analyticAt z).meromorphicAt)
    (isCompact_closedBall (0:ℂ) R) (subset_refl _)
  simpa [Function.HasFiniteSupport] using h

/-- The support of the divisor is contained in the ball. -/
lemma mem_of_divisor_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (h : MeromorphicOn.divisor f U u ≠ 0) : u ∈ U := by
  by_contra hu
  exact h (by rw [MeromorphicOn.divisor_def]; simp [hu])

/-- At a point where the divisor of `Λ` does not vanish, `Λ` vanishes; hence the point lies in the
critical strip. -/
lemma re_mem_Ioo_of_divisor_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {R : ℝ} {u : ℂ}
    (h : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0) :
    0 < u.re ∧ u.re < 1 := by
  have hz : completedLFunction χ u = 0 :=
    Commons.Analysis.Complex.zero_of_divisor_ne_zero
      (fun z _ => (differentiable_completedLFunction hχ).analyticAt z) h
  exact Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hz

/-- The first kernel is non-negative at every `Λ`-zero. -/
lemma kernel_first_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {R : ℝ} {s u : ℂ} (hs : 1 < s.re)
    (h : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0) :
    0 ≤ (1/(s-u)).re := by
  obtain ⟨h1, h2⟩ := re_mem_Ioo_of_divisor_ne_zero χ hχ hχprim h
  rw [one_div, Complex.inv_re]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simp only [Complex.sub_re]
  linarith

/-- The second (reflected) kernel is non-negative at every `Λ`-zero. -/
lemma kernel_second_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {R : ℝ} {s u : ℂ} (hs : 1 < s.re)
    (h : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u ≠ 0) :
    0 ≤ (1/((starRingEnd ℂ) s + u - 1)).re := by
  obtain ⟨h1, h2⟩ := re_mem_Ioo_of_divisor_ne_zero χ hχ hχprim h
  rw [one_div, Complex.inv_re]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.conj_re]
  linarith

/-- The two kernels are exchanged by the reflection `u ↦ 1 - conj u`. -/
lemma kernel_conj {s u : ℂ} :
    (1/(s-u)).re = (1/((starRingEnd ℂ) s + (1 - (starRingEnd ℂ) u) - 1)).re := by
  have h1 : (starRingEnd ℂ) s + (1 - (starRingEnd ℂ) u) - 1 = (starRingEnd ℂ) (s - u) := by
    simp [map_sub]; ring
  rw [h1, one_div, one_div, ← Complex.conj_inv, Complex.conj_re]

/-! ## Finiteness of the summands -/

lemma finiteSupport_window {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} {δ : ℝ} : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0)) := by
  refine (divisor_hasFiniteSupport χ hχ (|s.im| + 2)).subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  exact hu (by rw [h0]; simp)

lemma finiteSupport_first {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} {R : ℝ} : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) *
        (1/(s-u)).re) := by
  refine (divisor_hasFiniteSupport χ hχ R).subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  exact hu (by rw [h0]; simp)

lemma finiteSupport_second {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} {R : ℝ} : Function.HasFiniteSupport (fun v : ℂ =>
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) v : ℤ) *
        (1/((starRingEnd ℂ) s + v - 1)).re) := by
  refine (divisor_hasFiniteSupport χ hχ R).subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  exact hu (by rw [h0]; simp)

/-! ## The window sum is dominated by the first half -/

lemma winSum_le_firstSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) {δ : ℝ}
    {R : ℝ} (hR : |s.im| + 2 ≤ R) : winSum χ s δ ≤ firstSum χ s R := by
  have han : AnalyticOnNhd ℂ (completedLFunction χ)
      (Metric.closedBall (0:ℂ) (|s.im| + 2) ∪ Metric.closedBall (0:ℂ) R) :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  refine finsum_le_finsum' (finiteSupport_window χ hχ) (finiteSupport_first χ hχ) ?_
  intro u
  show ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0) ≤
      ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) * (1/(s-u)).re
  by_cases hD : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℤ) = 0
  · have hD' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℤ) : ℝ) = 0 := by
      rw [hD]; simp
    rw [hD', zero_mul]
    by_cases hE : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) = 0
    · rw [hE]; simp
    · apply mul_nonneg
      · exact divisor_nonneg χ hχ R u
      · exact kernel_first_nonneg χ hχ hχprim hs hE
  · have hu1 : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := mem_of_divisor_ne_zero hD
    have hu2 : u ∈ Metric.closedBall (0:ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right] at hu1 ⊢
      linarith
    have hEq : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2)) u =
        MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) u :=
      Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset han hu1 hu2
    have hEq' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℤ) : ℝ) =
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) := by
      rw [hEq]
    rw [hEq']
    refine mul_le_mul_of_nonneg_left ?_ (divisor_nonneg χ hχ R u)
    by_cases hc : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
    · rw [if_pos hc]
    · rw [if_neg hc]
      exact kernel_first_nonneg χ hχ hχprim hs hD

/-! ## The window sum is dominated by the second half (reflection) -/

lemma winSum_le_secondSum_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) {δ : ℝ}
    {R : ℝ} (hR : |s.im| + 3 ≤ R)
    (hrefl : ∀ v : ℂ, ‖(1:ℂ) + (s.im : ℂ) * Complex.I - (1 - (starRingEnd ℂ) v)‖ ≤ δ →
      MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))
          (1 - (starRingEnd ℂ) v) =
        MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R) v) :
    winSum χ s δ ≤ secondSum χ s R := by
  let e : ℂ ≃ ℂ :=
    { toFun := fun v => 1 - (starRingEnd ℂ) v
      invFun := fun v => 1 - (starRingEnd ℂ) v
      left_inv := fun v => by simp [map_sub]
      right_inv := fun v => by simp [map_sub] }
  set WIN : ℂ → ℝ := fun u =>
    (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0) with hWIN
  set SEC : ℂ → ℝ := fun v =>
    (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) v : ℤ) : ℝ) *
      (1/(s - e v)).re with hSEC
  have hkraw : ∀ w : ℂ, (1/(s - (1 - (starRingEnd ℂ) w))).re = (1/((starRingEnd ℂ) s + w - 1)).re := by
    intro w
    have h := kernel_conj (s := s) (u := 1 - (starRingEnd ℂ) w)
    have hw : (1 : ℂ) - (starRingEnd ℂ) (1 - (starRingEnd ℂ) w) = w := by simp [map_sub]
    rw [hw] at h
    exact h
  have hk : ∀ w : ℂ, (1/((starRingEnd ℂ) s + w - 1)).re = (1/(s - e w)).re :=
    fun w => (hkraw w).symm
  have hWINfin : (Function.support WIN).Finite := by
    refine (divisor_hasFiniteSupport χ hχ (|s.im| + 2)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    simp only [hWIN]
    rw [h0]; simp
  have hfin1 : Function.HasFiniteSupport (fun w : ℂ => WIN (e w)) := by
    refine (hWINfin.image e.symm).subset ?_
    intro w hw
    rw [Function.mem_support] at hw
    exact ⟨e w, hw, by simp⟩
  have hfin2 : Function.HasFiniteSupport SEC := by
    refine (divisor_hasFiniteSupport χ hχ R).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    simp only [hSEC]
    rw [h0]; simp
  have hwin : winSum χ s δ = ∑ᶠ w : ℂ, WIN (e w) := by
    have h1 : winSum χ s δ = ∑ᶠ u : ℂ, WIN u := rfl
    rw [h1]
    exact (finsum_comp_equiv e (f := WIN)).symm
  have hsec : secondSum χ s R = ∑ᶠ w : ℂ, SEC w := by
    have h1 : secondSum χ s R = ∑ᶠ w : ℂ,
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) : ℝ) *
          (1/((starRingEnd ℂ) s + w - 1)).re := rfl
    rw [h1]
    apply finsum_congr
    intro w
    rw [hk w]
  rw [hwin, hsec]
  refine finsum_le_finsum' hfin1 hfin2 ?_
  intro w
  show WIN (e w) ≤ SEC w
  simp only [hWIN, hSEC]
  rw [show e w = (1 - (starRingEnd ℂ) w) from rfl]
  by_cases hc : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - (1 - (starRingEnd ℂ) w)‖ ≤ δ
  · rw [if_pos hc]
    by_cases hD : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) (1 - (starRingEnd ℂ) w) : ℤ) = 0
    · have hD' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) (|s.im| + 2))) (1 - (starRingEnd ℂ) w) : ℤ) : ℝ) = 0 := by
        rw [hD]; simp
      rw [hD', zero_mul]
      by_cases hE : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) = 0
      · have hE' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) : ℝ) = 0 := by
          rw [hE]; simp
        rw [hE']; simp
      · apply mul_nonneg
        · exact divisor_nonneg χ hχ R w
        · rw [hkraw w]
          exact kernel_second_nonneg χ hχ hχprim hs hE
    · rw [hrefl w hc]
  · rw [if_neg hc, mul_zero]
    by_cases hE : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) = 0
    · have hE' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) w : ℤ) : ℝ) = 0 := by
        rw [hE]; simp
      rw [hE']; simp
    · apply mul_nonneg
      · exact divisor_nonneg χ hχ R w
      · rw [hkraw w]
        exact kernel_second_nonneg χ hχ hχprim hs hE

/-- The window sum is dominated by the second half of the truncated symmetric partial-fraction
sum, via the reflection `ρ ↦ 1 - conj ρ` of the zero set. -/
lemma winSum_le_secondSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) {δ : ℝ} (hδ1 : δ < 1)
    {R : ℝ} (hR : |s.im| + 3 ≤ R) : winSum χ s δ ≤ secondSum χ s R := by
  refine winSum_le_secondSum_aux χ hχ hχprim hs hR ?_
  intro v hv
  refine divisor_refl χ hχ hχprim ?_ ?_
  · -- `v` lies in the large ball `closedBall 0 R`
    rw [Metric.mem_closedBall, dist_zero_right]
    have harg : (1:ℂ) + (s.im : ℂ) * Complex.I - (1 - (starRingEnd ℂ) v) =
        (starRingEnd ℂ) v + (s.im : ℂ) * Complex.I := by ring
    have hδ : ‖(starRingEnd ℂ) v + (s.im : ℂ) * Complex.I‖ ≤ δ := by
      rw [← harg]; exact hv
    have htri : ‖(starRingEnd ℂ) v‖ ≤
        ‖(starRingEnd ℂ) v + (s.im : ℂ) * Complex.I‖ + ‖(s.im : ℂ) * Complex.I‖ := by
      have := norm_sub_le ((starRingEnd ℂ) v + (s.im : ℂ) * Complex.I) ((s.im : ℂ) * Complex.I)
      simpa using this
    have him : ‖(s.im : ℂ) * Complex.I‖ = |s.im| := by simp
    have hnorm : ‖(starRingEnd ℂ) v‖ = ‖v‖ := by simp
    linarith
  · -- the reflected point lies in the window ball `closedBall 0 (|Im s| + 2)`
    rw [Metric.mem_closedBall, dist_zero_right]
    have harg : (1:ℂ) + (s.im : ℂ) * Complex.I - (1 - (starRingEnd ℂ) v) =
        (starRingEnd ℂ) v + (s.im : ℂ) * Complex.I := by ring
    have hδ : ‖(starRingEnd ℂ) v + (s.im : ℂ) * Complex.I‖ ≤ δ := by
      rw [← harg]; exact hv
    have hsplit : (1:ℂ) - (starRingEnd ℂ) v =
        ((1:ℂ) + (s.im : ℂ) * Complex.I) - ((starRingEnd ℂ) v + (s.im : ℂ) * Complex.I) := by ring
    have htri : ‖1 - (starRingEnd ℂ) v‖ ≤
        ‖(starRingEnd ℂ) v + (s.im : ℂ) * Complex.I‖ + ‖(1:ℂ) + (s.im : ℂ) * Complex.I‖ := by
      rw [hsplit]
      simpa [add_comm] using norm_sub_le ((1:ℂ) + (s.im : ℂ) * Complex.I)
        ((starRingEnd ℂ) v + (s.im : ℂ) * Complex.I)
    have hb : ‖(1:ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 1 + |s.im| := by
      calc ‖(1:ℂ) + (s.im : ℂ) * Complex.I‖
          ≤ ‖(1:ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = 1 + |s.im| := by simp
    linarith

/-! ## The completed-`L` bound -/

/-- The truncated symmetric partial-fraction sums are non-decreasing in the truncation radius:
every summand is non-negative, because the zeros of `Λ` lie in the strip `0 < Re ρ < 1`. -/
lemma kernSum_mono {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) : Monotone (fun R : ℝ => kernSum χ s R) := by
  intro R₁ R₂ h12
  have han : AnalyticOnNhd ℂ (completedLFunction χ)
      (Metric.closedBall (0:ℂ) R₁ ∪ Metric.closedBall (0:ℂ) R₂) :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  have hfin1 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) : ℝ) *
        ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re)) := by
    refine (divisor_hasFiniteSupport χ hχ R₁).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0]; simp)
  have hfin2 : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) : ℝ) *
        ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re)) := by
    refine (divisor_hasFiniteSupport χ hχ R₂).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0]; simp)
  refine finsum_le_finsum' hfin1 hfin2 ?_
  intro u
  show (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) : ℝ) *
        ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re) ≤
      (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) : ℝ) *
        ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re)
  by_cases hD : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) = 0
  · have hD' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) : ℝ) = 0 := by
      rw [hD]; simp
    rw [hD', zero_mul]
    by_cases hE : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) = 0
    · have hE' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) : ℝ) = 0 := by
        rw [hE]; simp
      rw [hE', zero_mul]
    · apply mul_nonneg
      · exact divisor_nonneg χ hχ R₂ u
      · have h1 := kernel_first_nonneg χ hχ hχprim hs hE
        have h2 := kernel_second_nonneg χ hχ hχprim hs hE
        linarith
  · have hu1 : u ∈ Metric.closedBall (0:ℂ) R₁ := mem_of_divisor_ne_zero hD
    have hu2 : u ∈ Metric.closedBall (0:ℂ) R₂ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hu1 ⊢
      linarith
    have hEq : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁) u =
        MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂) u :=
      Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset han hu1 hu2
    have hEq' : (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₁)) u : ℤ) : ℝ) =
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R₂)) u : ℤ) : ℝ) := by
      rw [hEq]
    rw [hEq']

/-- **Core estimate.** For a primitive non-trivial character and `Re s > 1`, subtracting the
windowed zero sum from `-Re (Λ'/Λ)(s)` costs at most `(log N)/2`. -/
theorem core {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {s : ℂ} (hs : 1 < s.re) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (-(logDeriv (completedLFunction χ) s).re) + winSum χ s δ ≤ (1/2) * Real.log N := by
  have htend := tendsto_kernSum χ hχ hχprim hs
  have hmono := kernSum_mono χ hχ hχprim hs
  have hbound : ∀ R : ℝ, kernSum χ s R ≤ 2 * (logDeriv (completedLFunction χ) s).re + Real.log N :=
    fun R => le_of_monotone_tendsto hmono htend R
  have hsplit : ∀ R : ℝ, kernSum χ s R = firstSum χ s R + secondSum χ s R := by
    intro R
    have hfun : (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
          ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re)) =
        (fun u : ℂ =>
          (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
              (1/(s-u)).re +
            (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
              (1/((starRingEnd ℂ) s + u - 1)).re) := by
      funext u; ring
    have hf : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
          (1/(s-u)).re) := finiteSupport_first χ hχ
    have hg : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
          (1/((starRingEnd ℂ) s + u - 1)).re) := finiteSupport_second χ hχ
    rw [show kernSum χ s R = ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℝ) *
          ((1/(s-u)).re + (1/((starRingEnd ℂ) s + u - 1)).re) from rfl]
    rw [hfun, finsum_add_distrib hf hg]
    simp only [firstSum, secondSum]
  set R : ℝ := |s.im| + 4 with hRdef
  have hfirst : winSum χ s δ ≤ firstSum χ s R :=
    winSum_le_firstSum χ hχ hχprim hs (by rw [hRdef]; linarith)
  have hsecond : winSum χ s δ ≤ secondSum χ s R :=
    winSum_le_secondSum χ hχ hχprim hs hδ1 (by rw [hRdef]; linarith)
  have hb : kernSum χ s R ≤ 2 * (logDeriv (completedLFunction χ) s).re + Real.log N := hbound R
  rw [hsplit R] at hb
  linarith


/-! ## The archimedean (gamma-factor) bound -/

/-- The real part of the logarithmic derivative of the archimedean factor is controlled by
`log π / 2 + (log (2 + |Im s|) + 8)/2` on the strip `1/2 ≤ Re s ≤ 15`. -/
lemma gammaFactor_logDeriv_re_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h1 : (1:ℝ)/2 ≤ s.re) (h2 : s.re ≤ 15) :
    (logDeriv (DirichletCharacter.gammaFactor χ) s).re ≤
      Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |s.im|) + 8) := by
  have hre : (logDeriv (DirichletCharacter.gammaFactor χ) s).re ≤
      ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ := Complex.re_le_norm _
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := funext hE.gammaFactor_def
    rw [hfun] at hre ⊢
    have hb : ‖logDeriv Complex.Gammaℝ s‖ ≤
        Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |s.im|) + 8) := by
      have hle := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le s.re s.im h1
        (by linarith : s.re ≤ 16)
      rwa [show (((s.re : ℝ)) : ℂ) + Complex.I * (((s.im : ℝ)) : ℂ) = s from by
        apply Complex.ext <;> simp] at hle
    exact le_trans hre hb
  · have hfun : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext hO.gammaFactor_def
    rw [hfun] at hre ⊢
    have hld : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by
      have hf : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) :=
        Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ (s + 1) (by rw [Complex.add_re]; simp; linarith)
      have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s) hf hg
      have hder : deriv (fun z : ℂ => z + 1) s = 1 := by simp
      rw [hder] at h
      simpa [Function.comp_def, mul_comm] using h
    rw [hld] at hre ⊢
    have hb : ‖logDeriv Complex.Gammaℝ (s + 1)‖ ≤
        Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |s.im|) + 8) := by
      have hle := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le (s.re + 1) s.im
        (by linarith) (by linarith : s.re + 1 ≤ 16)
      rwa [show (((s.re + 1 : ℝ)) : ℂ) + Complex.I * (((s.im : ℝ)) : ℂ) = s + 1 from by
        apply Complex.ext <;> simp <;> ring] at hle
    exact le_trans hre hb

/-! ## The `L`-function form of the estimate -/

theorem shape {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {s : ℂ} (hs : 1 < s.re) (hs15 : s.re ≤ 15) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (-(logDeriv (DirichletCharacter.LFunction χ) s).re) + winSum χ s δ
      ≤ (1/2) * Real.log N + Real.log Real.pi / 2 + (1/2) * (Real.log (2 + |s.im|) + 8) := by
  have hcore := core χ hχ hχprim hs hδ0 hδ1
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_lt hs)
  have hdec := Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add χ hχ s (lt_trans zero_lt_one hs) hLs
  have hgam := gammaFactor_logDeriv_re_le χ (s := s) (by linarith) hs15
  have hsplit : (-(logDeriv (DirichletCharacter.LFunction χ) s).re) =
      (-(logDeriv (completedLFunction χ) s).re) +
        (logDeriv (DirichletCharacter.gammaFactor χ) s).re := by
    rw [hdec, Complex.add_re]; ring
  rw [hsplit]
  linarith

/-! ## The requested lemma -/

theorem l52Hyp_supply : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
    ∀ {ε δ : ℝ}, 0 < ε → 0 < δ → δ < 1 → Commons.NumberTheory.Linnik.L52Hyp χ c ε δ := by
  refine ⟨2, by norm_num, 10 ^ 6, ?_⟩
  intro q hq _inst χ _instc hχ ε δ hε hδ0 hδ1
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hNle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  -- size of `log q`
  have hq1e6 : (10 ^ 6 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog10 : (2 : ℝ) < Real.log 10 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 10)]
    calc Real.exp 2 = (Real.exp 1)^2 := by rw [← Real.exp_nat_mul]; norm_num
      _ < 3^2 := by nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
      _ < 10 := by norm_num
  have hlogq : (12 : ℝ) ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 10 ^ 6) hq1e6
    have h2 : Real.log ((10:ℝ) ^ 6) = 6 * Real.log 10 := by
      rw [Real.log_pow]; norm_num
    have h3 : (12 : ℝ) ≤ 6 * Real.log 10 := by nlinarith [hlog10]
    rw [h2] at h; linarith
  have hlogqpos : (0 : ℝ) < Real.log (q : ℝ) := by linarith
  -- the region conditions
  have hloglogqpos : 0 < Real.log (Real.log (q : ℝ)) := by
    apply Real.log_pos; linarith
  have hden : 0 < Real.log (q : ℝ) * Real.log (Real.log (q : ℝ)) := mul_pos hlogqpos hloglogqpos
  intro s hs1 hs2 hs3
  have hs1' : 1 < s.re := by
    have : 0 < 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) := by positivity
    linarith
  have hs15 : s.re ≤ 15 := by
    have hle : Real.log (Real.log (q : ℝ)) ≤ Real.log (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos hlogqpos
      linarith
    have h1 : Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) ≤ 1 := by
      rw [div_le_one hlogqpos]; exact hle
    linarith
  have hshape := shape χ.primitiveCharacter hχ' hprim hs1' hs15 hδ0 hδ1
  have hgoal : (-(logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re) +
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
      ≤ (2 + ε/4) * Real.log (q : ℝ) := by
    refine le_trans hshape ?_
    have hN1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
      have := Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
      exact_mod_cast this
    have hlogN : Real.log (χ.conductor : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by linarith) (by exact_mod_cast hNle)
    have hpi : Real.log Real.pi / 2 ≤ 1 := by
      have h1 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
      have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log (2:ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    have hlog12 : Real.log (12:ℝ) ≤ 4 := by
      have h1 : Real.log (12:ℝ) ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
      have h2 : Real.log (16:ℝ) = 4 * Real.log 2 := by
        rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log (2:ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    have hhalf : Real.log (Real.log (q:ℝ)) ≤ (1/2) * Real.log (q:ℝ) := by
      have h4 : (4:ℝ) ≤ Real.log (q:ℝ) := by linarith
      have hspos : 0 < Real.sqrt (Real.log (q:ℝ)) := Real.sqrt_pos.mpr hlogqpos
      have hsq2 : (2:ℝ) ≤ Real.sqrt (Real.log (q:ℝ)) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]
        linarith
      have hsq : (Real.sqrt (Real.log (q:ℝ)))^2 = Real.log (q:ℝ) :=
        Real.sq_sqrt (le_of_lt hlogqpos)
      have hlog_eq : Real.log (Real.log (q:ℝ)) = 2 * Real.log (Real.sqrt (Real.log (q:ℝ))) := by
        rw [Real.log_sqrt (le_of_lt hlogqpos)]; ring
      have hbound : Real.log (Real.sqrt (Real.log (q:ℝ))) ≤ Real.sqrt (Real.log (q:ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos hspos
      rw [hlog_eq]
      nlinarith [hsq2, hsq, hbound]
    have h2t : Real.log (2 + |s.im|) ≤ Real.log 12 + Real.log (Real.log (q:ℝ)) := by
      have h1 : Real.log (2 + |s.im|) ≤ Real.log (2 + 10 * Real.log (q:ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith [abs_nonneg s.im, hs3]
      have h2 : Real.log (2 + 10 * Real.log (q:ℝ)) ≤ Real.log (12 * Real.log (q:ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith
      have h3 : Real.log (12 * Real.log (q:ℝ)) = Real.log 12 + Real.log (Real.log (q:ℝ)) :=
        Real.log_mul (by norm_num) (ne_of_gt hlogqpos)
      linarith
    have hA : (1/2) * Real.log (χ.conductor : ℝ) ≤ (1/2) * Real.log (q : ℝ) := by linarith
    have hB : (1/2) * (Real.log (2 + |s.im|) + 8) ≤
        (1/2) * (Real.log 12 + (1/2) * Real.log (q:ℝ) + 8) := by linarith
    have hC : (2:ℝ) * Real.log (q : ℝ) ≤ (2 + ε/4) * Real.log (q : ℝ) := by
      have := mul_le_mul_of_nonneg_right (by linarith : (2:ℝ) ≤ 2 + ε/4) (le_of_lt hlogqpos)
      linarith
    nlinarith [hA, hB, hC, hpi, hlog12, hlogq]
  simpa only [Complex.neg_re] using hgoal

end Work.LinnikAreas.DhRepel
