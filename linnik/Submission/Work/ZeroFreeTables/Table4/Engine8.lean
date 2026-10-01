/-
# ZeroFreeTables/Table4/Engine8 — the kept `P₃` near sum

For a prescribed finite set `S` of zeros (HB §8.2 keeps `ρ₁, ρ₀, ρ̄₀`, together with the
near disk), the `P₃`-weighted near sums

* `keptInvSum`  (`k = 1`), `keptSqSum` (`k = 2`), `keptCubSum` (`k = 3`),
* `keptP3Sum`   (the combined weight `Re P₃(α/((s-u)L))`),

with the split `keptP3Sum = c·keptInvSum + c²·keptSqSum + (2/3)c³·keptCubSum` (`c = (a+λ₁)/L`)
and the extraction `zeroMult χ u · Re P₃(α/((s-u)L)) ≤ keptP3Sum` for `u ∈ S`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4.FarNear
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.ZeroFreeTables.P9.prim.SigmaP3L_eq_moments
import Submission.Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.tsum_inv_add_two_shift

namespace Work.ZeroFreeTables.Table4

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- The `k = 1` kept near sum, `Σ_u zm(u)·keptInd(u)·Re (1/(s-u))`. -/
noncomputable def keptInvSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (δ : ℝ) (S : Finset ℂ) : ℝ :=
  ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)).re)

/-- The `k = 2` kept near sum. -/
noncomputable def keptSqSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (δ : ℝ) (S : Finset ℂ) : ℝ :=
  ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 2).re

/-- The `k = 3` kept near sum. -/
noncomputable def keptCubSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (δ : ℝ) (S : Finset ℂ) : ℝ :=
  ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u * ((1 / (s - u)) ^ 3).re

/-- The kept `P₃` near sum: the single combined sum of `zm(u)·keptInd(u)·Re P₃(α/((s-u)L))`. -/
noncomputable def keptP3Sum (N : ℕ) [NeZero N] (L : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ)
    (a lam₁ δ : ℝ) (S : Finset ℂ) : ℝ :=
  ∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u *
    (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re

/-- **Split of the kept `P₃` near sum** into its three `k = 1,2,3` pieces.

The proof binds the three components as local definitions `A`, `B`, `C` once and for all
(otherwise the nested `∑'`-expressions blow the `whnf` heartbeat budget), names their
summabilities, and closes with `Summable.tsum_add` twice and `Summable.tsum_mul_left`
three times. -/
theorem keptP3Sum_split {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {L : ℝ} {s : ℂ}
    {a lam₁ δ : ℝ} {S : Finset ℂ}
    (h1 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)).re)))
    (h2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)) ^ 2).re))
    (h3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)) ^ 3).re)) :
    keptP3Sum N L χ s a lam₁ δ S
      = ((a + lam₁) / L) * keptInvSum N χ s δ S
        + ((a + lam₁) / L) ^ 2 * keptSqSum N χ s δ S
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * keptCubSum N χ s δ S := by
  classical
  set A : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
    * ((1 / (s - u)).re) with hA
  set B : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
    * ((1 / (s - u)) ^ 2).re with hB
  set Cc : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
    * ((1 / (s - u)) ^ 3).re with hC
  have hsA : Summable A := by rw [hA]; exact h1
  have hsB : Summable B := by rw [hB]; exact h2
  have hsC : Summable Cc := by rw [hC]; exact h3
  rw [keptP3Sum, keptInvSum, keptSqSum, keptCubSum]
  -- fold the `P₃` summand into the `A/B/C` combination
  have hcomb : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re)
      = ∑' u : ℂ, (((a + lam₁) / L) * A u + ((a + lam₁) / L) ^ 2 * B u
          + (2 / 3) * ((a + lam₁) / L) ^ 3 * Cc u) := by
    refine tsum_congr (fun u => ?_)
    rw [hA, hB, hC]
    rw [show ((((a + lam₁ : ℝ)) : ℂ)) / ((s - u) * (L : ℂ))
        = ((a : ℂ) + (lam₁ : ℂ)) / ((s - u) * (L : ℂ)) by push_cast; ring]
    have hP3 := Work.ZeroFreeTables.P9.P3_re_div_eq a lam₁ L s u
    rw [hP3]
    ring
  rw [hcomb]
  rw [Summable.tsum_add
        (f := fun u : ℂ => ((a + lam₁) / L) * A u + ((a + lam₁) / L) ^ 2 * B u)
        (g := fun u : ℂ => (2 / 3) * ((a + lam₁) / L) ^ 3 * Cc u)
        ((hsA.mul_left ((a + lam₁) / L)).add (hsB.mul_left (((a + lam₁) / L) ^ 2)))
        (hsC.mul_left ((2 / 3) * ((a + lam₁) / L) ^ 3)),
      Summable.tsum_add
        (f := fun u : ℂ => ((a + lam₁) / L) * A u)
        (g := fun u : ℂ => ((a + lam₁) / L) ^ 2 * B u)
        (hsA.mul_left ((a + lam₁) / L)) (hsB.mul_left (((a + lam₁) / L) ^ 2)),
      Summable.tsum_mul_left ((a + lam₁) / L) hsA,
      Summable.tsum_mul_left (((a + lam₁) / L) ^ 2) hsB,
      Summable.tsum_mul_left ((2 / 3) * ((a + lam₁) / L) ^ 3) hsC]

/-- Summability of the combined kept `P₃` summand, from the three component summabilities. -/
theorem keptP3Sum_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {L : ℝ} {s : ℂ}
    {a lam₁ δ : ℝ} {S : Finset ℂ}
    (h1 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)).re)))
    (h2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)) ^ 2).re))
    (h3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)) ^ 3).re)) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re) := by
  classical
  set A : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
    * ((1 / (s - u)).re) with hA
  set B : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
    * ((1 / (s - u)) ^ 2).re with hB
  set Cc : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
    * ((1 / (s - u)) ^ 3).re with hC
  have hsA : Summable A := by rw [hA]; exact h1
  have hsB : Summable B := by rw [hB]; exact h2
  have hsC : Summable Cc := by rw [hC]; exact h3
  refine (((hsA.mul_left ((a + lam₁) / L)).add (hsB.mul_left (((a + lam₁) / L) ^ 2))).add
    (hsC.mul_left ((2 / 3) * ((a + lam₁) / L) ^ 3))).congr (fun u => ?_)
  rw [hA, hB, hC]
  rw [show ((((a + lam₁ : ℝ)) : ℂ)) / ((s - u) * (L : ℂ))
      = ((a : ℂ) + (lam₁ : ℂ)) / ((s - u) * (L : ℂ)) by push_cast; ring]
  have hP3 := Work.ZeroFreeTables.P9.P3_re_div_eq a lam₁ L s u
  rw [hP3]
  ring

/-- **Extraction of a single kept zero** from the combined `P₃` near sum: for a zero `u ∈ S`
the whole `P₃`-contribution of `u` is at most the kept sum.  The non-negativity of the
summands comes from `P3_inv_re_nonneg` (`P3Pos`) together with HB's minimality `hmin`. -/
theorem keptP3Sum_extract {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {L : ℝ} {s : ℂ}
    {a lam₁ δ : ℝ} {S : Finset ℂ}
    (hL : 0 < L) (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hsre : s.re = 1 + a / L)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → lam₁ ≤ (1 - u.re) * L)
    {u : ℂ} (hu : u ∈ S) (hzu : Work.LinnikContract.zeroMult χ u ≠ 0)
    (h1 : Summable (fun v : ℂ => (Work.LinnikContract.zeroMult χ v : ℝ) * keptInd S s δ v
        * ((1 / (s - v)).re)))
    (h2 : Summable (fun v : ℂ => (Work.LinnikContract.zeroMult χ v : ℝ) * keptInd S s δ v
        * ((1 / (s - v)) ^ 2).re))
    (h3 : Summable (fun v : ℂ => (Work.LinnikContract.zeroMult χ v : ℝ) * keptInd S s δ v
        * ((1 / (s - v)) ^ 3).re)) :
    (Work.LinnikContract.zeroMult χ u : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re
      ≤ keptP3Sum N L χ s a lam₁ δ S := by
  classical
  have hα : 0 < a + lam₁ := by linarith
  have hsumm : Summable (fun v : ℂ => (Work.LinnikContract.zeroMult χ v : ℝ) * keptInd S s δ v
      * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - v) * (L : ℂ)))).re) :=
    keptP3Sum_summable (L := L) (a := a) (lam₁ := lam₁) (δ := δ) χ h1 h2 h3
  have hnn : ∀ v : ℂ, 0 ≤ (Work.LinnikContract.zeroMult χ v : ℝ) * keptInd S s δ v
      * (Work.ZeroFreeTables.P3 (((a + lam₁ : ℝ) : ℂ) / ((s - v) * (L : ℂ)))).re := by
    intro v
    by_cases hzv : Work.LinnikContract.zeroMult χ v = 0
    · rw [hzv]; simp
    · have hzvpos : 0 < (Work.LinnikContract.zeroMult χ v : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzv
      have hkept : 0 ≤ keptInd S s δ v := keptInd_nonneg S s δ v
      have hLsr : L * s.re = L + a := by rw [hsre]; field_simp
      have hzre : 1 ≤ ((((s - v) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ))).re := by
        have h3 : ((((s - v) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ))).re
            = L * (s.re - v.re) / (a + lam₁) := by
          rw [show ((s - v) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ)
              = (((L / (a + lam₁) : ℝ)) : ℂ) * (s - v) by push_cast; ring]
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.sub_re]
          ring
        rw [h3, le_div_iff₀ hα]
        have h1' : lam₁ ≤ (1 - v.re) * L := hmin v hzv
        nlinarith [h1', hLsr]
      have hnn' : 0 ≤ (Work.ZeroFreeTables.P3
          ((((s - v) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ)))⁻¹).re :=
        Work.ZeroFreeTables.P3_inv_re_nonneg _ hzre
      have harg : ((((s - v) * (L : ℂ)) / (((a + lam₁ : ℝ)) : ℂ)))⁻¹
          = (((a + lam₁ : ℝ)) : ℂ) / ((s - v) * (L : ℂ)) := by rw [inv_div]
      rw [← harg]
      exact mul_nonneg (mul_nonneg hzvpos.le hkept) hnn'
  rw [keptP3Sum]
  refine le_of_eq_of_le ?_ (Summable.le_tsum hsumm u (fun v _ => hnn v))
  rw [keptInd_eq_ite, if_pos (Or.inl hu)]
  ring

/-- **The moment-identity chain** (HB §8.2): the `P₃`-weighted von Mangoldt functional is a
real combination of the derivatives of `L'/L`.  Immediate from
`P9.prim.SigmaP3L_eq_moments` and `P9.prim.iteratedDeriv_logDeriv_re`. -/
theorem SigmaP3L_eq_derivs {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (a lam₁ L : ℝ) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      = -((a + lam₁) / L) * (logDeriv (DirichletCharacter.LFunction χ) s).re
        + ((a + lam₁) / L) ^ 2
            * (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re
        - (1 / 3) * ((a + lam₁) / L) ^ 3
            * (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s).re := by
  have hB := Work.ZeroFreeTables.P9.prim.SigmaP3L_eq_moments χ hs a lam₁ L
  have hA0 := Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re χ 0 hs
  have hA1 := Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re χ 1 hs
  have hA2 := Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re χ 2 hs
  have h0 : (logDeriv (DirichletCharacter.LFunction χ) s).re
      = - Work.ZeroFreeTables.vonMangoldtMoment χ s 0 := by simpa using hA0
  have h1 : (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction χ)) s).re
      = Work.ZeroFreeTables.vonMangoldtMoment χ s 1 := by simpa using hA1
  have h2 : (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction χ)) s).re
      = - Work.ZeroFreeTables.vonMangoldtMoment χ s 2 := by rw [hA2]; ring_nf
  rw [hB, h0, h1, h2]
  ring

/-- Points within `δ ≤ 1` of `1 + i·Im s` lie in the closed ball of radius `|s.im| + 2`. -/
private lemma mem_closedBall_of_near {s u : ℂ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h3 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 1 + |s.im| := by
    calc ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖
        ≤ ‖(1 : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |s.im| := by simp
  calc ‖u‖ ≤ ‖u - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by
        have hh := norm_add_le (u - ((1 : ℂ) + (s.im : ℂ) * Complex.I))
          ((1 : ℂ) + (s.im : ℂ) * Complex.I)
        simpa using hh
    _ = ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by rw [norm_sub_rev]
    _ ≤ δ + (1 + |s.im|) := by linarith
    _ ≤ 1 + (1 + |s.im|) := by linarith
    _ = |s.im| + 2 := by ring

/-- **The `k = 1` near summand is summable**: its support consists of zeros lying in the near
disk, hence in the ball on which the divisor of `completedLFunction χ` has finite support. -/
theorem nearInvSum_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
      * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)).re)) := by
  classical
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hfinDiv : (Function.support (fun u : ℂ => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u)).Finite := by
    simpa [Function.HasFiniteSupport] using
      (MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0 : ℂ) (|s.im| + 2))
        (V := Metric.closedBall (0 : ℂ) (|s.im| + 2))
        hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _))
  refine summable_of_ne_finset_zero (s := hfinDiv.toFinset) ?_
  intro u hu
  have hdiv0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u = 0 := by
    by_contra hne
    exact hu (by rw [Set.Finite.mem_toFinset, Function.mem_support]; exact hne)
  by_cases hball : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
  · have hzm0 : Work.LinnikContract.zeroMult χ u = 0 := by
      have hqr : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u
          = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hball]
        simp only [analyticOrderNatAt]
        cases h : analyticOrderAt (DirichletCharacter.completedLFunction χ) u with
        | top => simp
        | coe n => simp
      have hzero : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u = 0 := by
        have : (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) = 0 := by
          rw [← hqr]; exact hdiv0
        exact_mod_cast this
      rw [Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
      exact hzero
    rw [hzm0]; ring
  · have hni : Work.ZeroFreeTables.P9.nearInd s δ u = 0 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg]
      intro hc
      exact hball (mem_closedBall_of_near hδ1 hc)
    rw [hni]; ring

/-- **The `k = 1` identity.**  `keptInd` and `nearInd` differ exactly on the prescribed zeros
outside the near disk, so the difference of the two `k = 1` sums is that finite sum. -/
theorem keptInvSum_sub_nearInvSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {S : Finset ℂ}
    (h1 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ)
        * keptInd S s δ u * ((1 / (s - u)).re))) :
    keptInvSum N χ s δ S - Work.ZeroFreeTables.P9.nearInvSum N χ s δ
      = ∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re)) := by
  classical
  have hnear := nearInvSum_summable χ hχ hprim (s := s) (δ := δ) hδ0 hδ1
  have hdiff : ∀ u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)).re) - (Work.LinnikContract.zeroMult χ u : ℝ)
        * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)).re)
      = ((keptInd S s δ u - Work.ZeroFreeTables.P9.nearInd s δ u)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))) := by
    intro u; ring
  have hkey : ∀ u : ℂ, u ∉ S → ((keptInd S s δ u - Work.ZeroFreeTables.P9.nearInd s δ u)
      * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))) = 0 := by
    intro u hS
    have hk : keptInd S s δ u = Work.ZeroFreeTables.P9.nearInd s δ u := by
      by_cases hn : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [keptInd_eq_ite, if_pos (Or.inr hn), Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hn]
      · rw [keptInd_eq_ite, if_neg (fun h => h.elim hS hn),
          Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hn]
    rw [hk, sub_self, zero_mul]
  have hsupp : (Function.support (fun u : ℂ => ((keptInd S s δ u
      - Work.ZeroFreeTables.P9.nearInd s δ u)
      * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))))) ⊆ (S : Set ℂ) := by
    intro u hu
    by_contra hnot
    exact (Function.mem_support.mp hu) (hkey u hnot)
  have htail : (∑' u : ℂ, ((keptInd S s δ u - Work.ZeroFreeTables.P9.nearInd s δ u)
      * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))))
      = ∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re)) := by
    have hfinf : Function.HasFiniteSupport (fun u : ℂ => ((keptInd S s δ u
        - Work.ZeroFreeTables.P9.nearInd s δ u)
        * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re)))) :=
      (S.finite_toSet).subset hsupp
    rw [tsum_eq_finsum hfinf, finsum_eq_sum_of_support_subset _ hsupp]
    exact Finset.sum_congr rfl (fun u hu => by rw [keptInd_eq_ite, if_pos (Or.inl hu)])
  rw [keptInvSum, Work.ZeroFreeTables.P9.nearInvSum, ← Summable.tsum_sub h1 hnear]
  rw [tsum_congr hdiff, htail]

/-- **The `k = 1` link of the engine.**  From the log-derivative hypothesis (HB Lemma 3.1)
and the `keptInvSum`/`nearInvSum` identity, the `k = 1` term `-M₀·(α/L)` is bounded by
`α·c - (α/L)·keptInvSum` plus `(α/L)` times the finite sum over the prescribed zeros outside
the near disk. -/
theorem k1_link {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {a lam₁ δ c L : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hL : 0 < L)
    {s : ℂ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
        + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L)
    {S : Finset ℂ}
    (ksum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * keptInd S s δ u
        * ((1 / (s - u)).re))) :
    -(logDeriv (DirichletCharacter.LFunction χ) s).re * ((a + lam₁) / L)
      ≤ (a + lam₁) * c - ((a + lam₁) / L) * keptInvSum N χ s δ S
        + ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
            * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))) := by
  have hc : 0 ≤ (a + lam₁) / L := div_nonneg (by linarith) hL.le
  have hlog' : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      ≤ c * L - Work.ZeroFreeTables.P9.nearInvSum N χ s δ := by linarith
  rw [Complex.neg_re] at hlog'
  have h1 : -(logDeriv (DirichletCharacter.LFunction χ) s).re * ((a + lam₁) / L)
      ≤ (a + lam₁) * c - ((a + lam₁) / L) * Work.ZeroFreeTables.P9.nearInvSum N χ s δ := by
    have h := mul_le_mul_of_nonneg_right hlog' hc
    have h4 : (c * L) * ((a + lam₁) / L) = (a + lam₁) * c := by field_simp
    rw [sub_mul, h4, mul_comm (Work.ZeroFreeTables.P9.nearInvSum N χ s δ) ((a + lam₁) / L)] at h
    exact h
  have hid := keptInvSum_sub_nearInvSum χ hχ hprim (s := s) (δ := δ) hδ hδ1 ksum
  have h2 : Work.ZeroFreeTables.P9.nearInvSum N χ s δ
      = keptInvSum N χ s δ S - (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
          * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))) := by
    linarith [hid]
  have h3 : ((a + lam₁) / L) * Work.ZeroFreeTables.P9.nearInvSum N χ s δ
      = ((a + lam₁) / L) * keptInvSum N χ s δ S
        - ((a + lam₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
            * ((Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)).re))) := by
    rw [h2]; ring
  linarith [h1, h3]

/-
## Next: closing `engine8` (everything else is proved)

The statement is fixed (see `NOTE_HB83_status.md`); the proof body is complete except for the
final combination step.  Concretely, all of the following compile and are in scope:

* `hsig := SigmaP3L_eq_derivs χ hs_gt a lam₁ L` — `Σ = -(α/L)·Re(L'/L) + (α/L)²·M₁ - (1/3)(α/L)³·M₂`;
* `hM1rel`, `hM2rel` (hypotheses, from `Table4/engine_moment_relations`);
* `hquad`, `hcub` — direct applications of `quadNearFar_kept`, `cubicNearFar_kept`;
* `hb2ge`, `hb3ge` — `abs_le.mp hS2/hS3` after `Complex.re_tsum` with the parity-summability
  `(P9.tsum_inv_add_two_shift k hk (s := s + par) hs').1` (import added);
* `hk1 := k1_link …` and `hfold := keptP3Sum_split …`.

The one blocking step is the final `linarith`/`nlinarith`, which does not see through the
*products*: the hypotheses carry `((a+λ₁)/L)^2 · ((1+4/δ²)·J)` while the goal carries
`((a+λ₁)^2/L^2) · ((1+4/δ²)·J)` (and likewise `(2/3)((a+λ₁)/L)^3` vs `(2/3)((a+λ₁)^3/L^3)`),
and the `1/δ²`, `1/L` factors defeat the lineariser.  Two working routes:

1. **`set`-name the composite coefficients** — e.g.
   `set ca : ℝ := (a + lam₁) / L`, `set cb : ℝ := 1 + 4 / δ ^ 2`,
   `set J : ℝ := ∑' u, …` and `set Ex : ℝ := ∑ u ∈ S, …` — then restate `hquad`/`hcub`/`hb2ge`/
   `hb3ge`/`hk1`/`hfold` in those names (`simpa only [← ca, …]`) and close with `linarith`;
2. **explicit monotonicity steps** — multiply `hquad` by `ca^2 ≥ 0`, `hcub` by
   `(2/3)·ca^3 ≥ 0`, `hb2ge` by `ca^2 ≥ 0`, `hb3ge` by `(2/3)·ca^3 ≥ 0`, `hk1` as is, and
   `add_le_add` them, then `rw [hfold]` and `ring_nf`.
-/

end Work.ZeroFreeTables.Table4
