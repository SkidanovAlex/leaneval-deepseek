import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1M.muPart_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

-- `ℝ³` is the global notation `EuclideanSpace ℝ (Fin 3)` of
-- `Submission.Work.BoseKinLoc.Defs`, already in the import cone.

open Submission.BoseGases

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## 1. Support and fibre facts of the localised kernels -/

/-- `χ_{B(u)}(z) ≠ 0` forces `z ∈ B(u) = dlBox ℓ d u`. -/
private theorem chiSmallB_mem_dlBox' {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : ℝ³) (hz : chiSmallB M ℓ d u z ≠ 0) : z ∈ dlBox ℓ d u := by
  rw [Work.SmallBoxSliding.mem_dlBox_iff_scaled hℓ hd]
  refine ⟨?_, ?_⟩
  · exact chiScale_mem_acube hℓ (fun h => hz (by rw [chiSmallB, h, zero_mul]))
  · rw [mem_acube_iff]
    intro j
    have h := chiSmall_support_mem_abs_le hM (fun h => hz (by rw [chiSmallB, h, mul_zero])) j
    rw [Set.mem_Icc]
    exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- `wSmallPair M ℓ d u f x y = 0` as soon as `x ∉ B(u)`. -/
private theorem wSmallPair_eq_zero_of_notMem {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) (f : ℝ³ → ℝ) {x y : ℝ³} (hx : x ∉ dlBox ℓ d u) :
    wSmallPair M ℓ d u f x y = 0 := by
  have hχ : chiSmallB M ℓ d u x = 0 := by
    by_contra hne
    exact hx (chiSmallB_mem_dlBox' hM hℓ hd u x hne)
  simp only [wSmallPair, hχ, zero_mul]

/-- **The support of the localised kernel**: `wSmallPair M ℓ d u f x y ≠ 0` forces both
arguments into `B(u) = dlBox ℓ d u`. -/
private theorem wSmallPair_support {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) (f : ℝ³ → ℝ) {x y : ℝ³} (hxy : wSmallPair M ℓ d u f x y ≠ 0) :
    x ∈ dlBox ℓ d u ∧ y ∈ dlBox ℓ d u := by
  have hx : chiSmallB M ℓ d u x ≠ 0 := by
    intro h
    exact hxy (by simp only [wSmallPair, h, zero_mul])
  have hy : chiSmallB M ℓ d u y ≠ 0 := by
    intro h
    exact hxy (by simp only [wSmallPair, h, mul_zero])
  exact ⟨chiSmallB_mem_dlBox' hM hℓ hd u x hx, chiSmallB_mem_dlBox' hM hℓ hd u y hy⟩

/-- The `w₁`-fibre vanishes outside the box. -/
private theorem w1Fibre_eq_zero_of_notMem {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) (f : ℝ³ → ℝ) (z : ℝ³) (hz : z ∉ dlBox ℓ d u) :
    w1Fibre ℓ (wSmallPair M ℓ d u f) z = 0 := by
  unfold w1Fibre
  have h0 : (fun y : ℝ³ => wSmallPair M ℓ d u f z y) = fun _ : ℝ³ => (0 : ℝ) := by
    funext y
    exact wSmallPair_eq_zero_of_notMem hM hℓ hd u f hz
  rw [h0]
  simp

/-- The box indicator in a slot fixes the `w₁`-fibre. -/
private theorem aind_mul_w1Fibre {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : ℝ³) (f : ℝ³ → ℝ) :
    Work.BoseFixB1S.Aind (dlBox ℓ d u) z * w1Fibre ℓ (wSmallPair M ℓ d u f) z
      = w1Fibre ℓ (wSmallPair M ℓ d u f) z := by
  by_cases hz : z ∈ dlBox ℓ d u
  · simp [Work.BoseFixB1S.Aind, Set.indicator_of_mem hz]
  · rw [w1Fibre_eq_zero_of_notMem hM hℓ hd u f z hz]
    simp [Work.BoseFixB1S.Aind, Set.indicator_of_notMem hz]

/-- `|Q_i Ψ| ≤ 2B` on the analysis box whenever `|Ψ| ≤ B` there. -/
private theorem abs_boxQInd_le' {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure ℝ³) A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ B) :
    ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * B := by
  intro x hx
  have hP := Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i (C := B) hb x hx
  rw [Work.BoseFixB1S.boxQInd_eq volA A i Ψ x]
  calc |Work.BoseFixB1S.Aind A (x i) * Ψ x - Work.UBBInputs8.boxPInd volA A i Ψ x|
      ≤ |Work.BoseFixB1S.Aind A (x i) * Ψ x|
          + |Work.UBBInputs8.boxPInd volA A i Ψ x| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (Work.BoseFixB1S.Aind A (x i) * Ψ x)
            (-(Work.UBBInputs8.boxPInd volA A i Ψ x))
    _ ≤ 1 * B + B := by
        refine add_le_add ?_ hP
        rw [abs_mul]
        exact mul_le_mul (Work.BoseFixB1S.Aind_abs_le_one A (x i)) (hb x hx)
          (abs_nonneg _) (by norm_num)
    _ = 2 * B := by ring

/-! ## 4. The five box words unfolded -/

/-- `boxQSum` unfolded: the pair parts of the five words reassemble into `pairRaw`, and the
`μ`-parts with coefficients `1, 2, 1` into the three `boxMu`-sums. -/
private theorem boxQSum_eq' {N : ℕ} (volA ℓ μ : ℝ) (A : Set ℝ³)
    (w w1 w2 om : ℝ³ → ℝ³ → ℝ) (Φ : X N → ℝ) :
    Work.BoseFixB1S.boxQSum volA ℓ μ A w w1 w2 om Φ
      = Work.BoseFixB1S.pairRaw volA ℓ A w w1 w2 om Φ
        - μ * ((∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
            + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
            + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)) := by
  unfold Work.BoseFixB1S.boxQSum Work.BoseFixB1S.boxQ0 Work.BoseFixB1S.boxQ1
    Work.BoseFixB1S.boxQ2 Work.BoseFixB1S.boxQ3 Work.BoseFixB1S.boxQ4
    Work.BoseFixB1S.pairRaw Work.BoseFixB1S.boxMuP Work.BoseFixB1S.boxMuQP
    Work.BoseFixB1S.boxMuQ
  ring

/-! ## 2. The pair part: `pairRaw` telescopes to `½ Σ_p ∫ Φ² w` -/

/-- `pairRaw` is the sum of the `pairInts` (pure `Finset` algebra; no integrability needed,
because each word's pair-summand integral carries its word coefficient already). -/
private theorem pairRaw_eq_sum_pairInts {N : ℕ} (volA ℓ : ℝ) (A : Set ℝ³)
    (w w1 w2 om : ℝ³ → ℝ³ → ℝ) (Φ : X N → ℝ) :
    Work.BoseFixB1S.pairRaw volA ℓ A w w1 w2 om Φ
      = ∑ p ∈ pairSet N, Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.1 p.2 := by
  unfold Work.BoseFixB1S.pairRaw Work.BoseFixB1S.pairInts
  have h0 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg0 volA A w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ)
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
        * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg0
    ring
  have h1 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg1 volA A w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ)
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg1
    ring
  have h2a : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg2a volA A w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2b : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg2b volA A w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2c : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg2c volA A w1 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h3 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg3 volA A w1 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ)
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w1 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg3
    ring
  have h4 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg4 volA A w om Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ)
      (fun x : X N => (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg4
    ring
  rw [h0, h1, h2a, h2b, h2c, h3, h4]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- **The pair part.**  `pairRaw` at the sliding box equals `½ Σ_p ∫ Φ²·w(x_p.1,x_p.2)`. -/
private theorem pairRaw_eq_dlBox {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0)
    (u : ℝ³) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.pairRaw (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (dlBox ℓ d u)
        (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) (wSmallPair M ℓ d u (g2 v h))
        (omC (Classical.choose h)) Φ
      = (1 / 2) * (∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
  classical
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  set A : Set ℝ³ := dlBox ℓ d u with hAdef
  set W : ℝ³ → ℝ³ → ℝ := wSmallPair M ℓ d u v with hWdef
  set W1 : ℝ³ → ℝ³ → ℝ := wSmallPair M ℓ d u (g0 v h) with hW1def
  set W2 : ℝ³ → ℝ³ → ℝ := wSmallPair M ℓ d u (g2 v h) with hW2def
  set OM : ℝ³ → ℝ³ → ℝ := omC (Classical.choose h) with hOMdef
  have hvol' : 0 < volA := by rw [hvolAdef]; exact hvol
  have hA : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : volA = ((volume : Measure ℝ³) A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
  have hsupA : ∀ x y : ℝ³, W x y ≠ 0 → x ∈ A ∧ y ∈ A := by
    intro x y hxy
    have hw : wSmallPair M ℓ d u v x y ≠ 0 := by rwa [hWdef] at hxy
    obtain ⟨hx, hy⟩ := wSmallPair_support (M := M) hM hℓ hd u v hw
    exact ⟨by rwa [hAdef], by rwa [hAdef]⟩
  obtain ⟨C, hC0, hCΦ, hCP, hCQ⟩ :=
    Work.BoseFixB1S.boxBounds (N := N) hℓ hvol' hA hvolA hAc hΦc
  -- measurability of the four two-slot patterns
  have hQmeas : ∀ (i : Fin N) {Ψ : X N → ℝ}, Measurable Ψ →
      Measurable (Work.UBBInputs8.boxQInd volA A i Ψ) := by
    intro i Ψ hΨ
    have heq : Work.UBBInputs8.boxQInd volA A i Ψ
        = fun x : X N => Work.BoseFixB1S.Aind A (x i) * Ψ x
            - Work.UBBInputs8.boxPInd volA A i Ψ x := by
      funext x; exact Work.BoseFixB1S.boxQInd_eq volA A i Ψ x
    rw [heq]
    exact ((Work.BoseFixB1S.measurable_sigAt A hA i).mul hΨ).sub
      (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΨ)
  have hPP : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) :=
    fun i j => Work.BoseFixB1S.measurable_boxPInd volA A hA i
      (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦc.measurable)
  have hPQ : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) :=
    fun i j => Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQmeas j hΦc.measurable)
  have hQP : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) :=
    fun i j => hQmeas j (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦc.measurable)
  have hQQ : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) :=
    fun i j => hQmeas j (hQmeas i hΦc.measurable)
  -- pointwise bounds on the box
  have bPP : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| ≤ C :=
    fun i j => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol' hA hvolA hAc i (C := C) (hCP j)
  have bPQ : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x| ≤ 2 * C :=
    fun i j => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol' hA hvolA hAc i (C := 2 * C) (hCQ j)
  have bQP : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| ≤ 2 * C := by
    intro i j x hx
    have := abs_boxQInd_le' hℓ hvol' hA hvolA hAc j (B := C) hC0 (hCP i) x hx
    linarith
  have bQQ : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ 4 * C := by
    intro i j x hx
    have := abs_boxQInd_le' hℓ hvol' hA hvolA hAc j (B := 2 * C) (by linarith) (hCQ i) x hx
    linarith
  -- generic fragment integrability from the slot lemma
  have fragInt : ∀ (S : X N → ℝ) (B : ℝ), 0 ≤ B →
      (∀ᵐ x ∂(volume.restrict (abox N ℓ)), |S x| ≤ B) →
      AEStronglyMeasurable S (volume.restrict (abox N ℓ)) →
      ∀ (f : ℝ³ → ℝ), Integrable f → (∀ z : ℝ³, R0 ≤ ‖z‖ → f z = 0) →
      ∀ (i j : Fin N), i ≠ j →
      IntegrableOn (fun x : X N => S x * wSmallPair M ℓ d u f (x i) (x j)) (abox N ℓ) volume := by
    intro S B hB0 hSb hSm f hf hfsupp i j hij
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (R := R0) hℓ hd hf hfsupp hM hR hRχ
      u hij hSm hB0 hSb
  have aeBound : ∀ (S : X N → ℝ) (B : ℝ), (∀ x ∈ abox N ℓ, |S x| ≤ B) →
      ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |S x| ≤ B :=
    fun S B hb => (ae_restrict_iff' (abox_measurable N ℓ)).mpr (ae_of_all _ hb)
  have hI0 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg0 volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(1 / 2) * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2|
          ≤ (1 / 2) * C ^ 2 := by
      intro x hx
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (bPP i j x hx) 2)
        (by norm_num)
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      (measurable_const.mul ((hPP i j).pow_const 2)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg0, hW2def] using hInt
  have hI1 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg1 volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)|
          = (2 * |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|)
              * |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 * (2 * C)) * C := mul_le_mul
            (mul_le_mul_of_nonneg_left (bPQ i j x hx) (by norm_num))
            (bPP i j x hx) (abs_nonneg _) (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((measurable_const.mul (hPQ i j)).mul (hPP i j)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg1, hW2def] using hInt
  have hI2a : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg2a volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|
              * |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| :=
            abs_mul _ _
        _ ≤ (2 * C) * (2 * C) := mul_le_mul (bPQ i j x hx) (bPQ j i x hx) (abs_nonneg _)
            (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((hPQ i j).mul (hPQ j i)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg2a, hW2def] using hInt
  have hI2b : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg2b volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)|
          = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|
              * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| :=
            abs_mul _ _
        _ ≤ (2 * C) * (2 * C) := mul_le_mul (bPQ i j x hx) (bQP i j x hx) (abs_nonneg _)
            (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((hPQ i j).mul (hQP i j)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg2b, hW2def] using hInt
  have hI2c : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg2c volA A W1 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
            * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x|
              * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| :=
            abs_mul _ _
        _ ≤ C * (4 * C) := mul_le_mul (bPP i j x hx) (bQQ i j x hx) (abs_nonneg _)
            (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((hPP i j).mul (hQQ i j)).aestronglyMeasurable
      (g0 v h) (g0_integrable hR0 hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg2c, hW1def] using hInt
  have hI3 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg3 volA A W1 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          ≤ 16 * C ^ 2 := by
      intro x hx
      calc |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          = (2 * |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|)
              * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 * (2 * C)) * (4 * C) := mul_le_mul
            (mul_le_mul_of_nonneg_left (bPQ i j x hx) (by norm_num))
            (bQQ i j x hx) (abs_nonneg _) (by linarith [hC0])
        _ = 16 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((measurable_const.mul (hPQ i j)).mul (hQQ i j)).aestronglyMeasurable
      (g0 v h) (g0_integrable hR0 hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg3, hW1def] using hInt
  have hI4 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg4 volA A W OM Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hbnds := scattering_bounds_ae (w := Classical.choose h) hR0 hv hvrad hv_supp
      (w0_spec h).1 (w0_spec h).2
    have hom : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |OM (x i) (x j)| ≤ 1 := by
      have hfull : ∀ᵐ z : ℝ³, |Classical.choose h z| ≤ 1 := by
        filter_upwards [hbnds.1, hbnds.2] with z h1 h2
        rw [abs_of_nonneg h1]; exact h2
      have hpull := ae_pair_pullback (N := N) hℓ hij hfull
      filter_upwards [hpull] with x hx
      simpa [hOMdef, omC] using hx
    have hb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
        |(1 / 2) * (Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) ^ 2|
          ≤ (1 / 2) * (9 * C) ^ 2 := by
      filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ), hom] with x hxmem homx
      have h4 : |Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x| ≤ 9 * C := by
        have h1 := bQQ i j x hxmem
        have h2 := bPP j i x hxmem
        have h3 := bPQ j i x hxmem
        have h5 := bQP i j x hxmem
        have hsum : |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
              + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x|
            ≤ C + 2 * C + 2 * C :=
          le_trans (abs_add_le _ _)
            (add_le_add (le_trans (abs_add_le _ _) (add_le_add h2 h3)) h5)
        calc |Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x|
            = |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                + OM (x i) (x j)
                  * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                    + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                    + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)| := rfl
          _ ≤ |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x|
                + |OM (x i) (x j)
                  * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                    + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                    + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)| :=
              abs_add_le _ _
          _ ≤ 4 * C + 1 * (C + 2 * C + 2 * C) := by
              refine add_le_add h1 ?_
              rw [abs_mul]
              exact mul_le_mul homx hsum (abs_nonneg _) (by norm_num)
          _ ≤ 9 * C := by linarith
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h4 2) (by norm_num)
    have homm : AEStronglyMeasurable (fun x : X N => OM (x i) (x j))
        (volume.restrict (abox N ℓ)) := by
      have hli : LocallyIntegrable (Classical.choose h) := (w0_spec h).2.lhs_integrable
      have hpull := w0_diff_aem (N := N) hℓ hij hli
      simpa [hOMdef, omC] using hpull
    have hmid : AEStronglyMeasurable (fun x : X N =>
        Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
          + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        (volume.restrict (abox N ℓ)) :=
      ((hPP j i).aestronglyMeasurable.add (hPQ j i).aestronglyMeasurable).add
        (hQP i j).aestronglyMeasurable
    have h4aem : AEStronglyMeasurable (fun x : X N =>
        Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) (volume.restrict (abox N ℓ)) := by
      have heq : (fun x : X N => Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x)
          = fun x : X N => Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
              + OM (x i) (x j)
                * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                  + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                  + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) := rfl
      rw [heq]
      exact (hQQ i j).aestronglyMeasurable.add (homm.mul hmid)
    have hS4aem : AEStronglyMeasurable (fun x : X N =>
        (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) ^ 2)
        (volume.restrict (abox N ℓ)) := by
      have h1 := (h4aem.pow 2).const_mul (1 / 2 : ℝ)
      have hfe : (fun x : X N => (1 / 2) * ((fun y : X N =>
            Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) y) ^ 2) x)
          = fun x : X N => (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) ^ 2 := by
        funext x
        rw [Pi.pow_apply]
      rwa [hfe] at h1
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) hb hS4aem
      (v) (v_integrable hv1) (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) i j hij
    simpa [Work.BoseFixB1S.fg4, hWdef, hOMdef] using hInt
  -- per-pair telescoping
  have hpair : ∀ (i j : Fin N), i ≠ j →
      Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ i j
        + Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ j i
      = ∫ x in abox N ℓ, (Φ x) ^ 2 * W (x i) (x j) := by
    intro i j hij
    have ip1 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x) (abox N ℓ) volume :=
      (hI0 i j hij).add (hI1 i j hij)
    have ip2 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x) (abox N ℓ) volume := ip1.add (hI2a i j hij)
    have ip3 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x) (abox N ℓ) volume := ip2.add (hI2b i j hij)
    have ip4 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x) (abox N ℓ) volume := ip3.add (hI2c i j hij)
    have ip5 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
        + Work.BoseFixB1S.fg3 volA A W1 Φ i j x) (abox N ℓ) volume := ip4.add (hI3 i j hij)
    have ip6 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
        + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
        + Work.BoseFixB1S.fg4 volA A W OM Φ i j x) (abox N ℓ) volume := ip5.add (hI4 i j hij)
    have iq1 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x) (abox N ℓ) volume :=
      (hI0 j i hij.symm).add (hI1 j i hij.symm)
    have iq2 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x) (abox N ℓ) volume := iq1.add (hI2a j i hij.symm)
    have iq3 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x) (abox N ℓ) volume := iq2.add (hI2b j i hij.symm)
    have iq4 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x) (abox N ℓ) volume := iq3.add (hI2c j i hij.symm)
    have iq5 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
        + Work.BoseFixB1S.fg3 volA A W1 Φ j i x) (abox N ℓ) volume := iq4.add (hI3 j i hij.symm)
    have iq6 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
        + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
        + Work.BoseFixB1S.fg4 volA A W OM Φ j i x) (abox N ℓ) volume := iq5.add (hI4 j i hij.symm)
    have hA' : Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ i j
        = ∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ i j x
            + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
            + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
            + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
            + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
            + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
            + Work.BoseFixB1S.fg4 volA A W OM Φ i j x) := by
      unfold Work.BoseFixB1S.pairInts
      rw [← integral_add (hI0 i j hij) (hI1 i j hij)]
      rw [← integral_add ip1 (hI2a i j hij)]
      rw [← integral_add ip2 (hI2b i j hij)]
      rw [← integral_add ip3 (hI2c i j hij)]
      rw [← integral_add ip4 (hI3 i j hij)]
      rw [← integral_add ip5 (hI4 i j hij)]
    have hB' : Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ j i
        = ∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ j i x
            + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
            + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
            + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
            + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
            + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
            + Work.BoseFixB1S.fg4 volA A W OM Φ j i x) := by
      unfold Work.BoseFixB1S.pairInts
      rw [← integral_add (hI0 j i hij.symm) (hI1 j i hij.symm)]
      rw [← integral_add iq1 (hI2a j i hij.symm)]
      rw [← integral_add iq2 (hI2b j i hij.symm)]
      rw [← integral_add iq3 (hI2c j i hij.symm)]
      rw [← integral_add iq4 (hI3 j i hij.symm)]
      rw [← integral_add iq5 (hI4 j i hij.symm)]
    have hF : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
        + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
        + Work.BoseFixB1S.fg4 volA A W OM Φ i j x) (abox N ℓ) volume := ip6
    have hG : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
        + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
        + Work.BoseFixB1S.fg4 volA A W OM Φ j i x) (abox N ℓ) volume := iq6
    calc Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ i j
          + Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ j i
        = (∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
              + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
              + Work.BoseFixB1S.fg4 volA A W OM Φ i j x))
            + (∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
              + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
              + Work.BoseFixB1S.fg4 volA A W OM Φ j i x)) := by rw [hA', hB']
      _ = ∫ x in abox N ℓ, ((Work.BoseFixB1S.fg0 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
              + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
              + Work.BoseFixB1S.fg4 volA A W OM Φ i j x)
            + (Work.BoseFixB1S.fg0 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
              + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
              + Work.BoseFixB1S.fg4 volA A W OM Φ j i x)) := by
          rw [← integral_add hF hG]
      _ = ∫ x in abox N ℓ, Work.BoseFixB1S.fgsum volA A W W1 W2 OM Φ i j x := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Work.BoseFixB1S.fgsum]
          ring
      _ = ∫ x in abox N ℓ, (Φ x) ^ 2 * W (x i) (x j) := by
          apply integral_congr_ae
          filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
          rw [Work.BoseFixB1S.boxPairPointwise hℓ hvol' hA hvolA hAc
            (fun a b => by
              rw [hWdef]
              exact wSmallPair_symm hM u (fun z => radial_neg hvrad z) a b)
            (fun a b => by
              rw [hOMdef]; exact omC_chosen_sym h a b)
            (fun a b => by
              rw [hW1def, hWdef, hOMdef]
              simp only [wSmallPair, wSmallScaled, g0, omC]
              ring)
            (fun a b => by
              rw [hW2def, hWdef, hOMdef]
              simp only [wSmallPair, wSmallScaled, g2, omC]
              ring)
            hij hΦc x hx]
          by_cases hw : W (x i) (x j) = 0
          · rw [hw]; ring
          · obtain ⟨hxi, hxj⟩ := hsupA (x i) (x j) hw
            have h1 : Work.BoseFixB1S.Aind A (x i) = 1 := Set.indicator_of_mem hxi _
            have h2 : Work.BoseFixB1S.Aind A (x j) = 1 := Set.indicator_of_mem hxj _
            rw [h1, h2]; ring
  -- assemble
  rw [pairRaw_eq_sum_pairInts volA ℓ A W W1 W2 OM Φ]
  have hsym : (∑ p ∈ pairSet N, Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.1 p.2)
      = (1 / 2) * ∑ p ∈ pairSet N,
          (Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.1 p.2
            + Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.2 p.1) := by
    rw [Finset.sum_add_distrib,
      pairSet_swap_sum (fun p : Fin N × Fin N => Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.1 p.2)]
    ring
  rw [hsym]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact hpair p.1 p.2 (by simpa [pairSet] using hp)

/-- `pairRaw` at the sliding box equals `pairRaw`-free form (the mirror statement used by the
assembly): `pairRaw = ∫ Φ²·(½ Σ_p w)`. -/
private theorem pairRaw_eq_integral {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0)
    (u : ℝ³) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ pairSet N,
        wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = Work.BoseFixB1S.pairRaw (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (dlBox ℓ d u)
          (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) (wSmallPair M ℓ d u (g2 v h))
          (omC (Classical.choose h)) Φ := by
  have h1 : (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ pairSet N,
      wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N,
          wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
    rw [← integral_const_mul (1 / 2 : ℝ)
      (fun x : X N => (Φ x) ^ 2 * (∑ p ∈ pairSet N, wSmallPair M ℓ d u v (x p.1) (x p.2)))]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have h2 : (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N,
        wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2) := by
    rw [show (fun x : X N => (Φ x) ^ 2 * (∑ p ∈ pairSet N,
          wSmallPair M ℓ d u v (x p.1) (x p.2)))
        = fun x : X N => ∑ p ∈ pairSet N,
            (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2) from by
      funext x; rw [Finset.mul_sum]]
    exact integral_finsetSum (pairSet N) (fun p hp => by
      have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
      have hS : Continuous (fun x : X N => (Φ x) ^ 2) := by fun_prop
      obtain ⟨B, hBb⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
        (s := abox N ℓ) (f := fun x : X N => (Φ x) ^ 2) hS.continuousOn
      have hB0' : 0 ≤ B := le_trans (norm_nonneg _) (hBb 0 (zero_mem_abox hℓ.le))
      have hSb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |(Φ x) ^ 2| ≤ B :=
        (ae_restrict_iff' (abox_measurable N ℓ)).mpr (ae_of_all _ (fun x hx => by
          simpa [Real.norm_eq_abs] using hBb x hx))
      exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (R := R0) hℓ hd
        (v_integrable hv1) (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hM hR hRχ u hne
        hS.aestronglyMeasurable hB0' hSb)
  rw [h1, h2, pairRaw_eq_dlBox hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦc]

theorem bqPotsplit {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      = Work.BoseFixB1S.boxQSum (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          (Submission.BoseGases.omC (Classical.choose h)) Φ := by
  classical
  -- the two `μ`-free abbreviations used throughout
  set Cfib : ℝ := (chiSupAbs * chiSmallDecay M)
    * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
        * (8 * π * _root_.BoseGases.a v)) with hCfibdef
  have hfibb : ∀ z : ℝ³, |∫ y in acube ℓ, wSmallPair M ℓ d u (g0 v h) z y| ≤ Cfib := by
    intro z
    rw [hCfibdef]
    exact wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  have hfibmeas : AEStronglyMeasurable
      (fun z : ℝ³ => ∫ y in acube ℓ, wSmallPair M ℓ d u (g0 v h) z y)
      (volume.restrict (acube ℓ)) :=
    aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (g0_integrable hR0 hv_supp h).aemeasurable
  -- per-slot integrability of `Φ²·w₁-fibre`
  have hfibInt : ∀ i : Fin N, IntegrableOn (fun x : X N =>
      (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
      (abox N ℓ) volume := by
    intro i
    exact integrableOn_slot_fibre (N := N) (ℓ := ℓ) hℓ i hfibmeas (C := Cfib)
      (fun z _ => hfibb z) (S := fun x : X N => (Φ x) ^ 2) (by fun_prop)
  -- integrability of the `μ`-part of the left-hand side
  have hAint : IntegrableOn (fun x : X N => (Φ x) ^ 2 * (-μ * (∑ i : Fin N,
      w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i)))) (abox N ℓ) volume := by
    have hsum : IntegrableOn (fun x : X N => ∑ i : Fin N,
        (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
        (abox N ℓ) volume := by
      change Integrable (fun x : X N => ∑ i : Fin N,
        (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
        (volume.restrict (abox N ℓ))
      exact integrable_finsetSum (Finset.univ : Finset (Fin N))
        (fun i _ => by simpa [IntegrableOn] using hfibInt i)
    refine (hsum.const_mul (-μ)).congr ?_
    filter_upwards with x
    have h1 : (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
        = (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1]; ring
  -- integrability of the pair part of the left-hand side
  have hpairInt : ∀ p ∈ pairSet N, IntegrableOn (fun x : X N =>
      (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox N ℓ) volume := by
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    have hS : Continuous (fun x : X N => (Φ x) ^ 2) := by fun_prop
    obtain ⟨B, hBb⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
      (s := abox N ℓ) (f := fun x : X N => (Φ x) ^ 2) hS.continuousOn
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBb 0 (zero_mem_abox hℓ.le))
    have hSb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |(Φ x) ^ 2| ≤ B :=
      (ae_restrict_iff' (abox_measurable N ℓ)).mpr (ae_of_all _ (fun x hx => by
        simpa [Real.norm_eq_abs] using hBb x hx))
    exact integrableOn_slot_wSmallPair (N := N) (R := R0) hℓ hd (v_integrable hv1)
      (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hM hR hRχ u hne
      hS.aestronglyMeasurable hB0 hSb
  have hBint : IntegrableOn (fun x : X N => (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N,
      wSmallPair M ℓ d u v (x p.1) (x p.2)))) (abox N ℓ) volume := by
    have hsum : IntegrableOn (fun x : X N => ∑ p ∈ pairSet N,
        (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox N ℓ) volume := by
      change Integrable (fun x : X N => ∑ p ∈ pairSet N,
        (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2))
        (volume.restrict (abox N ℓ))
      exact integrable_finsetSum (pairSet N)
        (fun p hp => by simpa [IntegrableOn] using hpairInt p hp)
    refine (hsum.const_mul (1 / 2)).congr ?_
    filter_upwards with x
    have h1 : (∑ p ∈ pairSet N, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2))
        = (Φ x) ^ 2 * (∑ p ∈ pairSet N, wSmallPair M ℓ d u v (x p.1) (x p.2)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1]; ring
  -- the left-hand side splits into its `μ`-part and its pair part
  have hsplit : Submission.BoseGases.qLHSword (N := N) ℓ μ
        (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) Φ
      = (∫ x in abox N ℓ, (Φ x) ^ 2 * (-μ * (∑ i : Fin N,
          w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))))
        + (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N,
            wSmallPair M ℓ d u v (x p.1) (x p.2)))) := by
    rw [show Submission.BoseGases.qLHSword (N := N) ℓ μ
          (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) Φ
        = ∫ x in abox N ℓ, (Φ x) ^ 2 * ((-μ * (∑ i : Fin N,
              w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i)))
            + ((1 / 2) * (∑ p ∈ pairSet N,
                wSmallPair M ℓ d u v (x p.1) (x p.2)))) from rfl]
    rw [← integral_add hAint hBint]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [show wSmall1Pair h M ℓ d u = wSmallPair M ℓ d u (g0 v h) from rfl]
  rw [hsplit]
  rw [Work.BoseFixB1M.muPart_dlBox hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦc]
  rw [pairRaw_eq_integral hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦc]
  rw [boxQSum_eq' (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ (dlBox ℓ d u)
    (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h))
    (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h)) Φ]
  ring


end Work.BoseFixB1
