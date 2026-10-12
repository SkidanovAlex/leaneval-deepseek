import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.BoseBoxFock.frame_sampling_L2
import Submission.Work.BoseBoxFock.kinFirst_le_of_heatSpec_closed
import Submission.Work.BoseBoxFock.sampling_unitCube_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kinFT_lattice_tail_sq_lt`

The tail of the lattice sampling of the `p`-convention Fourier transform of a bounded,
compactly supported `W`:

    ∀ ε > 0, ∃ Λ, ∀ Λ' ≥ Λ,  Σ'_{n : ‖k_n‖ ≥ Λ'} ‖Ŵ(k_n)‖² ≤ ε ,   k_n = kmomInt ℓ n = (2π/ℓ)·n .

The mathematical content is the **`L²` frame (Poisson/aliasing) identity at the scale `μ`**: for
`g ∈ L²(ℝ³)` supported in the cube `boxL μ` of side `μ`,

    Σ'_n ‖ĝ(kmomInt μ n)‖² = μ³ ∫ ‖g‖²                                    (FRAME)

(`hasSum_kinFT_lattice_L2`), obtained by rescaling `g` into the unit cube and applying the proved
`L²` unit-cube Parseval identity `sampling_unitCube_L2`; the dilation is handled by
`MeasureTheory.Measure.map_addHaar_smul` (`Measure.map (y ↦ μ • y) volume = (μ³)⁻¹ • volume`), so
that `MemLp g 2` transports to the dilated function via `MemLp.smul_measure` and
`MemLp.comp_measurePreserving`.

Since the `ℓ`-lattice `(2π/ℓ)ℤ³` is a **sub-lattice** of the `μ`-lattice `(2π/μ)ℤ³` whenever
`μ = N·ℓ` with `N ∈ ℕ`, `N ≥ 1`, (FRAME) at a scale `μ ≥ 2R` gives the *summability* of
`n ↦ ‖Ŵ(kmomInt ℓ n)‖²` for every bounded `W` vanishing outside the ball of radius `R`
(`summable_kinFT_lattice_of_bounded`).  The tail statement then follows from the elementary
"complement of a finite set" argument `tail_le_of_summable` (a summable nonnegative family has
arbitrarily small sums over the complements of finite sets, and the lattice ball
`{n | ‖k_n‖ < Λ}` is finite and increasing in `Λ`).

Non-measurable `W` are handled separately: then the Bochner integral is everywhere `0`
(`integral_undef`), so every term of the series vanishes.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The `L²` frame identity at an arbitrary scale -/

/-- **The `L²` frame (Poisson/aliasing) identity at the scale `μ`.**  For `g ∈ L²(ℝ³)` supported in
the cube `boxL μ`,

    `Σ'_n ‖ĝ(kmomInt μ n)‖² = μ³ ∫ ‖g‖²`.

Proof: the dilated state `y ↦ g (μ • y)` is `L²` (`MemLp.smul_measure` +
`MemLp.comp_measurePreserving`, using `Measure.map (y ↦ μ • y) volume = (μ³)⁻¹ • volume`,
`MeasureTheory.Measure.map_addHaar_smul`) and supported in the unit cube (`flb_tsupport_sub`); the
unit-cube Parseval identity `sampling_unitCube_L2` then gives the series, and
`kinFT_comp_smul` (`∫ e^{−i⟪p,y⟫} g(μ y) dy = (μ³)⁻¹ ĝ(μ⁻¹p)`) together with
`flb_integral_norm_sq_comp_smul` (`∫‖g(μ·)‖² = (μ³)⁻¹∫‖g‖²`) converts it into the statement. -/
theorem hasSum_kinFT_lattice_L2 {μ : ℝ} (hμ : 0 < μ) {g : E3 → ℂ}
    (hg : MemLp g 2 (volume : Measure E3))
    (hsupp : tsupport g ⊆ Work.BoseK15.corpusBox.boxL μ) :
    HasSum (fun n : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT g (kmomInt μ n)‖ ^ 2)
      (μ ^ 3 * ∫ x : E3, ‖g x‖ ^ 2) := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  -- the pushforward of Lebesgue measure under the dilation `y ↦ μ • y`
  have hmap : Measure.map (fun y : E3 => μ • y) (volume : Measure E3)
      = ENNReal.ofReal (μ ^ 3)⁻¹ • volume := by
    rw [MeasureTheory.Measure.map_addHaar_smul (volume : Measure E3) hμne,
      finrank_euclideanSpace, Fintype.card_fin, abs_of_pos (by positivity)]
  have hmp : MeasurePreserving (fun y : E3 => μ • y) (volume : Measure E3)
      (ENNReal.ofReal (μ ^ 3)⁻¹ • volume) := ⟨measurable_const_smul μ, hmap⟩
  -- the dilated state is `L²` and supported in the unit cube
  have hg' : MemLp (fun y : E3 => g (μ • y)) 2 (volume : Measure E3) :=
    (hg.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving hmp
  have hgsupp' : tsupport (fun y : E3 => g (μ • y))
      ⊆ {y : E3 | ∀ i : Fin 3, |y.ofLp i| ≤ (1 / 2 : ℝ)} :=
    flb_tsupport_sub hμ hsupp
  have hS := sampling_unitCube_L2 hg' hgsupp'
  -- identify the sampling coefficients
  have hcoef : ∀ n : Fin 3 → ℤ,
      (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g (μ • y))
        = ((μ ^ 3)⁻¹ : ℝ) * Submission.BoseGases.kinFT g (kmomInt μ n) := by
    intro n
    rw [kinFT_comp_smul hμ g (Work.BoseB4.vec n)]
    rfl
  have hsq : ∀ n : Fin 3 → ℤ,
      ‖(∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g (μ • y))‖ ^ 2
        = ((μ ^ 3)⁻¹) ^ 2 * ‖Submission.BoseGases.kinFT g (kmomInt μ n)‖ ^ 2 := by
    intro n
    rw [hcoef n]
    exact flb_normSq_ofReal_mul _ _
  have hS' : HasSum (fun n : Fin 3 → ℤ =>
      ((μ ^ 3)⁻¹) ^ 2 * ‖Submission.BoseGases.kinFT g (kmomInt μ n)‖ ^ 2)
      (∫ y : E3, ‖g (μ • y)‖ ^ 2) := hS.congr_fun (fun n => (hsq n).symm)
  rw [flb_integral_norm_sq_comp_smul hμ g] at hS'
  -- solve for the series
  have hca : (((μ ^ 3)⁻¹) ^ 2 : ℝ) ≠ 0 := by positivity
  have hmain : HasSum (fun n : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT g (kmomInt μ n)‖ ^ 2)
      ((((μ ^ 3)⁻¹) ^ 2)⁻¹ * ((μ ^ 3)⁻¹ * ∫ x : E3, ‖g x‖ ^ 2)) := by
    have h := hS'.mul_left ((((μ ^ 3)⁻¹) ^ 2)⁻¹)
    exact h.congr_fun (fun n => (inv_mul_cancel_left₀ hca _).symm)
  rw [show ((((μ ^ 3)⁻¹) ^ 2)⁻¹ * ((μ ^ 3)⁻¹ * ∫ x : E3, ‖g x‖ ^ 2))
      = μ ^ 3 * ∫ x : E3, ‖g x‖ ^ 2 from by
    field_simp] at hmain
  exact hmain

/-! ## 2. The tail of a summable nonnegative family over the sampling lattice -/

/-- A set indicator of a nonnegative function is bounded by the function. -/
private lemma indicator_le_self_of_nonneg {ι : Type*} {f : ι → ℝ} (hnn : ∀ x, 0 ≤ f x) (s : Set ι) :
    s.indicator f ≤ f := by
  intro x
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    exact hnn x

/-- **The lattice tail of a summable nonnegative family is arbitrarily small.**  For
`f : ℤ³ → ℝ` nonnegative and summable and any norm function `k`,

    ∀ ε > 0, ∃ Λ, ∀ Λ' ≥ Λ, Σ'_{n : ‖k_n‖ ≥ Λ'} f n ≤ ε .

Proof: pick a finite `F₀` with `Σ'_{n ∉ F₀} f n < ε` (from `HasSum` for the filter `atTop` on
finsets), then `Λ := Σ_{n ∈ F₀} |k n| + 1`; for `Λ' ≥ Λ` the set `{Λ' ≤ k n}` is contained in the
complement of `F₀`, and the two sums are compared pointwise. -/
theorem tail_le_of_summable {k : (Fin 3 → ℤ) → ℝ} {f : (Fin 3 → ℤ) → ℝ}
    (hnn : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ∀ ε > 0, ∃ Λ : ℝ, ∀ Λ' : ℝ, Λ ≤ Λ' →
      (∑' n : Fin 3 → ℤ, (if Λ' ≤ k n then f n else 0)) ≤ ε := by
  intro ε hε
  -- a finite set outside which the series is small
  have hev : ∀ᶠ s : Finset (Fin 3 → ℤ) in Filter.atTop,
      dist (∑ n ∈ s, f n) (∑' n, f n) < ε :=
    hf.hasSum.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp hev
  have hcompl : (∑' b : ↑((F₀ : Set (Fin 3 → ℤ))ᶜ), f b) < ε := by
    have h1 := hF₀ F₀ le_rfl
    rw [Real.dist_eq] at h1
    have h2 := hf.sum_add_tsum_compl (s := F₀)
    have h3 := abs_lt.mp h1
    linarith [h3.1, h2]
  refine ⟨(∑ m ∈ F₀, |k m|) + 1, fun Λ' hΛ' => ?_⟩
  -- the index sets
  have hΛbnd : ∀ n ∈ F₀, k n < (∑ m ∈ F₀, |k m|) + 1 := by
    intro n hn
    have h1 : |k n| ≤ ∑ m ∈ F₀, |k m| :=
      Finset.single_le_sum (f := fun m => |k m|) (fun i _ => abs_nonneg _) hn
    have h2 : k n ≤ |k n| := le_abs_self _
    linarith
  have hpt : ∀ n : Fin 3 → ℤ,
      (if (∑ m ∈ F₀, |k m|) + 1 ≤ k n then f n else 0)
        ≤ ((F₀ : Set (Fin 3 → ℤ))ᶜ).indicator f n := by
    intro n
    by_cases hn : n ∈ F₀
    · have hlt := hΛbnd n hn
      rw [Set.indicator_of_notMem (by simpa using hn), if_neg (not_le.mpr hlt)]
    · rw [Set.indicator_of_mem (by simpa using hn)]
      by_cases h2 : (∑ m ∈ F₀, |k m|) + 1 ≤ k n
      · rw [if_pos h2]
      · rw [if_neg h2]; exact hnn n
  have hsumΛ : Summable (fun n : Fin 3 → ℤ => (if (∑ m ∈ F₀, |k m|) + 1 ≤ k n then f n else 0)) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [hnn])
      (fun n => hpt n) (hf.indicator _)
  have hsumΛ0 : Summable (((F₀ : Set (Fin 3 → ℤ))ᶜ).indicator f) := hf.indicator _
  have hkey : (∑' n : Fin 3 → ℤ, (if (∑ m ∈ F₀, |k m|) + 1 ≤ k n then f n else 0)) ≤ ε :=
    calc (∑' n : Fin 3 → ℤ, (if (∑ m ∈ F₀, |k m|) + 1 ≤ k n then f n else 0))
        ≤ ∑' n : Fin 3 → ℤ, ((F₀ : Set (Fin 3 → ℤ))ᶜ).indicator f n :=
          Summable.tsum_le_tsum hpt hsumΛ hsumΛ0
      _ = ∑' b : {x : Fin 3 → ℤ // x ∉ F₀}, f b :=
          (tsum_subtype ((F₀ : Set (Fin 3 → ℤ))ᶜ) f).symm
      _ ≤ ε := hcompl.le
  -- monotonicity in `Λ'`
  have hpt2 : ∀ n : Fin 3 → ℤ, (if Λ' ≤ k n then f n else 0)
      ≤ (if (∑ m ∈ F₀, |k m|) + 1 ≤ k n then f n else 0) := by
    intro n
    by_cases h2 : Λ' ≤ k n
    · have h3 : (∑ m ∈ F₀, |k m|) + 1 ≤ k n := le_trans hΛ' h2
      rw [if_pos h2, if_pos h3]
    · rw [if_neg h2]
      by_cases h3 : (∑ m ∈ F₀, |k m|) + 1 ≤ k n
      · rw [if_pos h3]; exact hnn n
      · rw [if_neg h3]
  have hsumΛ' : Summable (fun n : Fin 3 → ℤ => (if Λ' ≤ k n then f n else 0)) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [hnn])
      (fun n => hpt2 n) hsumΛ
  exact le_trans (Summable.tsum_le_tsum hpt2 hsumΛ' hsumΛ) hkey

/-! ## 3. Summability of the lattice samples of a bounded compactly supported state -/

/-- **Summability of the `ℓ`-lattice samples.**  For `g : ℝ³ → ℂ` which is a.e. strongly measurable,
bounded and vanishes outside the ball of radius `R`, the family `n ↦ ‖ĝ(kmomInt ℓ n)‖²` is
summable.

Proof: with `R' = max R 0` the state is supported in the ball of radius `R'`, hence `L²`
(`HasCompactSupport.memLp_of_bound`).  Choose `N ∈ ℕ`, `N ≥ 1`, with `μ := N·ℓ ≥ 2R'`.  Then
`tsupport g ⊆ closedBall 0 R' ⊆ closedBall 0 (μ/2) ⊆ boxL μ`, so the frame identity at scale `μ`
applies, and the `ℓ`-lattice is the image of the `μ`-lattice under the injection `n ↦ N·n`. -/
theorem summable_kinFT_lattice_of_bounded {ℓ R : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hbdd : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) (hsupp : ∀ x, R < ‖x‖ → g x = 0)
    (hmeas : AEStronglyMeasurable g (volume : Measure E3)) :
    Summable (fun n : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
  set R' : ℝ := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right R 0
  -- the state vanishes outside the ball of radius `R'`
  have hW0 : ∀ x : E3, R' < ‖x‖ → g x = 0 := by
    intro x hx
    rcases le_or_gt R 0 with h | h
    · have h0 : R' = 0 := max_eq_right h
      rw [h0] at hx
      exact hsupp x (lt_of_le_of_lt h hx)
    · have hR : R' = R := max_eq_left h.le
      rw [hR] at hx
      exact hsupp x hx
  have hsupp' : Function.support g ⊆ Metric.closedBall (0 : E3) R' := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra hcon
    rw [not_le] at hcon
    exact hx (hW0 x hcon)
  have htsup' : tsupport g ⊆ Metric.closedBall (0 : E3) R' :=
    closure_minimal hsupp' Metric.isClosed_closedBall
  have hcomp : HasCompactSupport g :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) R') (isClosed_tsupport g) htsup'
  obtain ⟨C, hC⟩ := hbdd
  have hC' : ∀ᵐ x ∂(volume : Measure E3), ‖g x‖ ≤ max C 0 :=
    Eventually.of_forall (fun x => le_trans (hC x) (le_max_left C 0))
  have hL2 : MemLp g 2 (volume : Measure E3) := hcomp.memLp_of_bound hmeas (max C 0) hC'
  -- the fine scale `μ = N·ℓ ≥ 2R'`
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * R' / ℓ)
  set N : ℕ := max 1 N₀ with hNdef
  have hN1 : 1 ≤ N := le_max_left 1 N₀
  have hNge : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right 1 N₀
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNz : (N : ℤ) ≠ 0 := by
    intro h
    exact absurd (by exact_mod_cast h : (N : ℝ) = 0) (ne_of_gt hNpos)
  set μ : ℝ := (N : ℝ) * ℓ with hμdef
  have hμpos : 0 < μ := by rw [hμdef]; positivity
  have hμ2R : 2 * R' ≤ μ := by
    have h2 : 2 * R' / ℓ ≤ (N : ℝ) := le_trans hN₀ hNge
    rw [div_le_iff₀ hℓ] at h2
    rw [hμdef]; linarith
  have hsuppμ : tsupport g ⊆ Work.BoseK15.corpusBox.boxL μ := by
    refine htsup'.trans ((Metric.closedBall_subset_closedBall ?_).trans
      (closedBall_subset_corpusBox_boxL hμpos))
    linarith
  have hframe := hasSum_kinFT_lattice_L2 hμpos hL2 hsuppμ
  -- the `ℓ`-lattice is a sub-lattice of the `μ`-lattice
  set NN : (Fin 3 → ℤ) → (Fin 3 → ℤ) := fun n i => (N : ℤ) * n i with hNNdef
  have hscal : ∀ x : E3, ℓ⁻¹ • x = ((N : ℝ) * ℓ)⁻¹ • ((N : ℝ) • x) := by
    intro x
    rw [smul_smul, mul_inv_rev]
    congr 1
    field_simp
  have hrel : ∀ n : Fin 3 → ℤ, kmomInt ℓ n = kmomInt μ (NN n) := by
    intro n
    show ℓ⁻¹ • Work.BoseB4.vec n = μ⁻¹ • Work.BoseB4.vec (NN n)
    have hvec : Work.BoseB4.vec (NN n) = (N : ℝ) • Work.BoseB4.vec n := by
      rw [Work.BoseB4.vec, Work.BoseB4.vec, ← WithLp.toLp_smul]
      congr 1
      ext i
      simp only [hNNdef, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [hvec, hμdef]
    exact hscal _
  have hinj : Function.Injective NN := by
    intro a b hab
    funext i
    have h1 : (N : ℤ) * a i = (N : ℤ) * b i := by
      have := congrFun hab i
      simpa only [hNNdef] using this
    exact mul_left_cancel₀ hNz h1
  have hsummμ : Summable (fun m : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT g (kmomInt μ m)‖ ^ 2) :=
    hframe.summable
  exact (hsummμ.comp_injective hinj).congr
    (fun n => by dsimp only [Function.comp_apply]; rw [hrel n])

/-! ## 4. The tail statement -/

/-- The tail statement for a bounded, compactly supported `ℂ`-valued state: if `g` is bounded and
vanishes outside the ball of radius `R`, then the mass of its lattice samples beyond momentum `Λ'`
is arbitrarily small for large `Λ'`.  Non-measurable `g` is a degenerate case in which every
Bochner integral vanishes (`integral_undef`). -/
theorem lattice_tail_le_of_bounded {ℓ R : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hbdd : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) (hsupp : ∀ x, R < ‖x‖ → g x = 0) :
    ∀ ε > 0, ∃ Λ : ℝ, ∀ Λ' : ℝ, Λ ≤ Λ' →
      (∑' n : Fin 3 → ℤ,
        (if Λ' ≤ ‖kmomInt ℓ n‖ then ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 else 0)) ≤ ε := by
  intro ε hε
  by_cases hmeas : AEStronglyMeasurable g (volume : Measure E3)
  · exact tail_le_of_summable (k := fun n => ‖kmomInt ℓ n‖)
      (f := fun n => ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      (fun n => by positivity) (summable_kinFT_lattice_of_bounded hℓ hbdd hsupp hmeas) ε hε
  · -- degenerate case: all the integrals vanish
    have hzero : ∀ p : E3, Submission.BoseGases.kinFT g p = 0 := by
      intro p
      rw [Submission.BoseGases.kinFT]
      refine integral_undef (f := fun y : E3 =>
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y) ?_
      intro hint
      refine hmeas ?_
      have hcont : Continuous fun y : E3 => Complex.exp (Complex.I * (inner ℝ p y : ℂ)) :=
        Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)))
      have h2 : AEStronglyMeasurable (fun y : E3 => Complex.exp (Complex.I * (inner ℝ p y : ℂ))
          * (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * g y)) volume :=
        hcont.measurable.aestronglyMeasurable.mul hint.aestronglyMeasurable
      refine h2.congr (Eventually.of_forall (fun y => ?_))
      dsimp only
      rw [← mul_assoc, ← Complex.exp_add, show Complex.I * (inner ℝ p y : ℂ)
          + -(Complex.I * (inner ℝ p y : ℂ)) = 0 by ring, Complex.exp_zero, one_mul]
    refine ⟨0, fun Λ' hΛ' => ?_⟩
    have hz : (fun n : Fin 3 → ℤ =>
        (if Λ' ≤ ‖kmomInt ℓ n‖ then ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 else 0))
        = fun _ => 0 := by
      funext n
      rw [hzero (kmomInt ℓ n)]
      simp
    rw [hz, tsum_zero]
    exact hε.le

/-! ## 5. The target -/

theorem kinFT_lattice_tail_sq_lt {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∀ ε > 0, ∃ Λ : ℝ, ∀ Λ' : ℝ, Λ ≤ Λ' →
      (∑' n : Fin 3 → ℤ,
        (if Λ' ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖
          then ‖Submission.BoseGases.kinFT (fun z =>
            (W z : ℂ)) (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
          else 0)) ≤ ε := by
  exact lattice_tail_le_of_bounded (ℓ := ℓ) (R := R) (g := fun z => (W z : ℂ)) hℓ
    ⟨hWb.choose, fun x => by simpa using hWb.choose_spec x⟩
    (fun x hx => by simp [hWs x hx])

end Work.BoseBoxFock
