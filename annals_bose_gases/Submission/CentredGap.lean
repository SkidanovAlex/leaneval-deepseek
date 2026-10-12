import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.CentredSector
import Submission.Shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5/6 — the O1 brick: kinetic word over the centred analysis box and
# the sector (gap-above-condensate) inequality

The Fournais--Solovej box analysis is carried out on the centred box
`acube ℓ = [−ℓ/2, ℓ/2]³` whose condensate mode is the constant function
(projection `aP ℓ i Φ` = mean over `acube ℓ`).  The first Section-6 (a
priori bounds) input is the control of the excited-particle count

    cnPlus ℓ Φ = Σᵢ ∫_{abox N ℓ} (aQ ℓ i Φ)²      (aQ = 1 − aP)

by the *kinetic word* over the centred box

    kinWord N ℓ Φ := Σᵢ Σ_k ∫_{abox N ℓ} (fderiv ℝ Φ x (kcDir N i k))²

through the per-slot Poincaré (Neumann-type) gap above constants:

    centredGap_i : ∫_{abox N ℓ} (aQ ℓ i Φ)² ≤ 36·ℓ²·∫_{abox N ℓ} Σ_k (∂ᵢₖΦ)²
    centredGap   : cnPlus ℓ Φ ≤ 36·ℓ²·kinWord N ℓ Φ

This module is the centred mirror of `SectorProj.sectQ_gap` (which lives on
the positive cube `[0,L]³` and whose 1-particle atom is `CubeGap.cube_gap`).

## Statements

1. `acube_gap` — the 1-particle atom on the centred cube: for `φ : ℝ³ → ℝ`
   of class `ContDiff ℝ ∞` and `0 < ℓ`,
   `∫_{acube ℓ} (φ − mean_acube φ)² ≤ 36·ℓ²·∫_{acube ℓ} Σ_k (fderiv φ (euclBasis3 k))²`
   where `mean_acube φ := (1/ℓ³)·∫_{acube ℓ} φ`.
2. `kinWord` — the definition above (finite, nonnegative).
3. `centredGap_i` — per-particle gap (state above).
4. `centredGap` — summed gap: `cnPlus ℓ Φ ≤ 36·ℓ²·kinWord N ℓ Φ`.

## Proof outline

* `acube_gap` is reduced to `CubeGap.cube_gap` by the coordinate translation
  `T x := x − (ℓ/2,…,ℓ/2)` mapping the standard cube `[0,ℓ]³` onto the
  centred cube `[−ℓ/2,ℓ/2]³` (a measure-preserving measurable embedding, so
  set integrals are transported by `MeasurePreserving.setIntegral_preimage_emb`),
  and the Fréchet derivative is invariant under translation.
* `centredGap_i` mirrors `SectorProj.sectQ_gap` line by line with
  `abox N ℓ`/`acube ℓ`/`aP`/`aQ` in place of `box N L`/`cube L`/`sectP`/
  `sectQ`: peel the centred box at particle `i` with
  `Q0Sector.abox_integral_peel`, express `aQ ℓ i Φ (kcInsN n i (y,r))` via
  `Q0Sector.aP_kcInsN`, apply `acube_gap` to the fibre `fib r := fun y => Φ (kcInsN n i (y,r))`
  (the fibre facts `SectorProj.fiber_contDiff`, `fiber_fderiv_kcDir` and
  `sum_fderiv_onb_eq_coord` are box-independent), then integrate the
  pointwise inequality over the other particles `r : X n` and peel back.
* `centredGap` sums `centredGap_i` over `i : Fin N` (using the finite
  sum–integral interchange over the compact centred box).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Translation of the standard cube onto the centred cube

`cube ℓ = [0,ℓ]³` is mapped onto `acube ℓ = [−ℓ/2,ℓ/2]³` by the translation
`x ↦ x − c` with `c = (ℓ/2,…,ℓ/2)`.  We record the coordinate facts, the
measure-preserving measurable-embedding and the resulting integral identity.
-/

/-- The vector `(ℓ/2, …, ℓ/2)` of `ℝ³` (every coordinate equals `ℓ/2`). -/
noncomputable def cgHalfShift (ℓ : ℝ) : ℝ³ := cgEuc3 (fun _ : Fin 3 => ℓ / 2)

/-- Coordinate value of the half-shift vector. -/
lemma cgHalfShift_coord (ℓ : ℝ) (m : Fin 3) : (cgHalfShift ℓ) m = ℓ / 2 := by
  simp [cgHalfShift, cgEuc3]

/-- Subtracting the half-shift subtracts `ℓ/2` in every coordinate. -/
lemma cgSubHalf_coord (x : ℝ³) (ℓ : ℝ) (m : Fin 3) : (x - cgHalfShift ℓ) m = x m - ℓ / 2 := by
  simp [cgHalfShift, cgEuc3]

/-- The preimage of the centred cube under the translation `x ↦ x − c`
(`c = (ℓ/2,…,ℓ/2)`) is the standard cube `[0,ℓ]³`. -/
lemma cgPreimage_subHalf_acube_eq_cube (ℓ : ℝ) :
    ((fun x : ℝ³ => x - cgHalfShift ℓ) ⁻¹' acube ℓ) = cube ℓ := by
  ext x
  constructor
  · intro hx
    have hx' : x - cgHalfShift ℓ ∈ acube ℓ := by simpa using hx
    rw [mem_acube_iff] at hx'
    intro m
    have hxm := hx' m
    have hxm1 : -ℓ / 2 ≤ (x - cgHalfShift ℓ) m := hxm.1
    have hxm2 : (x - cgHalfShift ℓ) m ≤ ℓ / 2 := hxm.2
    have hc := cgSubHalf_coord x ℓ m
    constructor
    · nlinarith
    · nlinarith
  · intro hx
    have hgoal : x - cgHalfShift ℓ ∈ acube ℓ := by
      rw [mem_acube_iff]
      intro m
      have hxm : x m ∈ Set.Icc (0 : ℝ) ℓ := by simpa using hx m
      have hxm1 : 0 ≤ x m := hxm.1
      have hxm2 : x m ≤ ℓ := hxm.2
      have hc := cgSubHalf_coord x ℓ m
      constructor
      · rw [hc]; nlinarith
      · rw [hc]; nlinarith
    simpa using hgoal

/-- The derivative of the translation `x ↦ x − c` is the identity. -/
lemma cgFderiv_subHalf (c : ℝ³) (x : ℝ³) :
    fderiv ℝ (fun z : ℝ³ => z - c) x = ContinuousLinearMap.id ℝ (ℝ³) := by
  have hf : DifferentiableAt ℝ (fun z : ℝ³ => z) x := differentiableAt_id
  have hg : DifferentiableAt ℝ (fun _ : ℝ³ => c) x := differentiableAt_const c
  have hstep : fderiv ℝ ((fun z : ℝ³ => z) - fun _ : ℝ³ => c) x = ContinuousLinearMap.id ℝ (ℝ³) := by
    rw [fderiv_sub hf hg]
    simp
  convert hstep using 1
  all_goals ext z; rfl

/-- The Fréchet derivative is invariant under the translation
`x ↦ x − c`: `fderiv (φ ∘ (· − c)) x = fderiv φ (x − c)`. -/
lemma cgFderiv_translate_apply {c : ℝ³} {f : ℝ³ → ℝ} (hf : ContDiff ℝ 1 f) (x v : ℝ³) :
    fderiv ℝ (fun z : ℝ³ => f (z - c)) x v = fderiv ℝ f (x - c) v := by
  have hT : DifferentiableAt ℝ (fun z : ℝ³ => z - c) x := by
    exact differentiableAt_id.sub (differentiableAt_const c)
  have hfT : DifferentiableAt ℝ f (x - c) :=
    hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (x - c)
  have hcomp := fderiv_comp x hfT hT
  rw [cgFderiv_subHalf c x] at hcomp
  have hmain : fderiv ℝ (fun z : ℝ³ => f (z - c)) x = fderiv ℝ f (x - c) := by
    simpa [Function.comp_def] using hcomp
  calc
    fderiv ℝ (fun z : ℝ³ => f (z - c)) x v = (fderiv ℝ f (x - c)) v := by rw [hmain]

/-- Translation is smooth (so translated smooth functions are smooth). -/
lemma cgContDiff_subHalf (ℓ : ℝ) : ContDiff ℝ ∞ (fun x : ℝ³ => x - cgHalfShift ℓ) := by
  exact contDiff_id.sub (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ³ => cgHalfShift ℓ)

/-- **Integral transport**: the integral over the standard cube of the
translated integrand equals the integral over the centred cube —
`∫_{x ∈ cube ℓ} G (x − c) = ∫_{y ∈ acube ℓ} G y`. -/
lemma cgIntegral_translate_cube_acube (ℓ : ℝ) (G : ℝ³ → ℝ) :
    (∫ x in cube ℓ, G (x - cgHalfShift ℓ)) = (∫ y in acube ℓ, G y) := by
  let c : ℝ³ := cgHalfShift ℓ
  let T : ℝ³ → ℝ³ := fun x => x - c
  have hmp : MeasurePreserving T volume volume := by
    have h := measurePreserving_add_right (μ := volume) (-c)
    simpa [T, sub_eq_add_neg] using h
  have hemb : MeasurableEmbedding T := by
    have h := (Homeomorph.addRight (-c)).measurableEmbedding
    simpa [T, sub_eq_add_neg] using h
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb (f := T) (μ := volume) (ν := volume)
    hmp hemb G (acube ℓ)
  have hpre : T ⁻¹' acube ℓ = cube ℓ := by
    dsimp [T, c]
    exact cgPreimage_subHalf_acube_eq_cube ℓ
  rw [hpre] at h
  simpa [T, c] using h

/-- The 1-particle centred-cube gap above the mean: for a smooth `φ` on the
centred cube `acube ℓ = [−ℓ/2, ℓ/2]³`,
`∫ (φ − mean)² ≤ 36·ℓ²·∫ Σ_k (∂ₖφ)²`.  (Any explicit constant `≤ 36` is
acceptable; the constant `36` mirrors `CubeGap.cube_gap`.) -/
lemma acube_gap {ℓ : ℝ} (hℓ : 0 < ℓ) {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ) :
    (∫ y in acube ℓ, (φ y - (1 / ℓ ^ 3) * (∫ z in acube ℓ, φ z)) ^ 2) ≤
      (36 : ℝ) * ℓ ^ 2 *
        (∫ y in acube ℓ, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) := by
  let ψ : ℝ³ → ℝ := fun x => φ (x - cgHalfShift ℓ)
  have hψc : ContDiff ℝ ∞ ψ := by
    dsimp [ψ]
    exact hφc.comp (cgContDiff_subHalf ℓ)
  have hφ1 : ContDiff ℝ 1 φ := hφc.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  have hmain := cube_gap ℓ hℓ (φ := ψ) hψc
  have hmean1 : (∫ z in cube ℓ, ψ z) = (∫ z in acube ℓ, φ z) := by
    calc
      (∫ z in cube ℓ, ψ z) = ∫ z in cube ℓ, φ (z - cgHalfShift ℓ) := by rfl
      _ = ∫ z in acube ℓ, φ z := cgIntegral_translate_cube_acube ℓ φ
  let meanA : ℝ := (1 / ℓ ^ 3) * (∫ z in acube ℓ, φ z)
  have hL : (∫ x in cube ℓ, (ψ x - (1 / ℓ ^ 3) * (∫ z in cube ℓ, ψ z)) ^ 2)
      = (∫ y in acube ℓ, (φ y - meanA) ^ 2) := by
    calc
      (∫ x in cube ℓ, (ψ x - (1 / ℓ ^ 3) * (∫ z in cube ℓ, ψ z)) ^ 2)
          = (∫ x in cube ℓ, (ψ x - (1 / ℓ ^ 3) * (∫ z in acube ℓ, φ z)) ^ 2) := by
              rw [hmean1]
      _ = ∫ x in cube ℓ, (φ (x - cgHalfShift ℓ) - meanA) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            dsimp [ψ, meanA]
      _ = ∫ y in acube ℓ, (φ y - meanA) ^ 2 :=
            cgIntegral_translate_cube_acube ℓ (fun y => (φ y - meanA) ^ 2)
  have hR : (∫ x in cube ℓ, ∑ k : Fin 3, (fderiv ℝ ψ x (euclBasis3 k)) ^ 2)
      = (∫ y in acube ℓ, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) := by
    calc
      (∫ x in cube ℓ, ∑ k : Fin 3, (fderiv ℝ ψ x (euclBasis3 k)) ^ 2)
          = ∫ x in cube ℓ, (∑ k : Fin 3, (fderiv ℝ φ (x - cgHalfShift ℓ) (euclBasis3 k)) ^ 2) := by
              apply integral_congr_ae
              filter_upwards with x
              apply Finset.sum_congr rfl
              intro k hk
              congr 1
              dsimp [ψ]
              exact cgFderiv_translate_apply (f := φ) (hf := hφ1) x (euclBasis3 k)
      _ = ∫ y in acube ℓ, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2 :=
            cgIntegral_translate_cube_acube ℓ
              (fun y => ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2)
  calc
    (∫ y in acube ℓ, (φ y - (1 / ℓ ^ 3) * (∫ z in acube ℓ, φ z)) ^ 2)
        = (∫ y in acube ℓ, (φ y - meanA) ^ 2) := by rfl
    _ = (∫ x in cube ℓ, (ψ x - (1 / ℓ ^ 3) * (∫ z in cube ℓ, ψ z)) ^ 2) := by rw [← hL]
    _ ≤ (36 : ℝ) * ℓ ^ 2 * (∫ x in cube ℓ, ∑ k : Fin 3, (fderiv ℝ ψ x (euclBasis3 k)) ^ 2) := hmain
    _ = (36 : ℝ) * ℓ ^ 2 * (∫ y in acube ℓ, ∑ k : Fin 3, (fderiv ℝ φ y (euclBasis3 k)) ^ 2) := by
        rw [hR]

/-! ## Kinetic word: integrability and nonnegativity on the centred box -/

/-- The squared kinetic sum of particle `i` is integrable over the centred
box (the integrand is continuous on the compact centred box). -/
lemma kinSum_integrableOn_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    IntegrableOn (fun x : X N => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) (abox N ℓ) volume := by
  have hsum : Integrable (fun x : X N => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2)
      (volume.restrict (abox N ℓ)) := by
    exact integrable_finsetSum (s := Finset.univ) (μ := (volume : Measure (X N)).restrict (abox N ℓ))
      (f := fun k : Fin 3 => fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2) (by
        intro k hk
        have hc : Continuous (fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
          exact (firstDir_contDiff (f := Φ) hΦc (kcDir N i k)).continuous.pow 2
        exact integrableOn_abox_of_continuous hℓ hc)
  exact hsum

/-- The kinetic word over the centred analysis box `abox N ℓ`:
`Σᵢ Σ_k ∫ (∂ᵢₖΦ)²` (particle-`i`, coordinate-`k` partial derivatives,
`kcDir N i k` = the `k`-th Euclidean coordinate axis of particle `i`).  This
is the corpus expectation-form of the FS kinetic energy operator `𝒯`. -/
noncomputable def kinWord (N : ℕ) (ℓ : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-- The kinetic word is a sum of integrals of squares, hence nonnegative. -/
lemma kinWord_nonneg (N : ℕ) (ℓ : ℝ) (Φ : X N → ℝ) : 0 ≤ kinWord N ℓ Φ := by
  unfold kinWord
  exact Finset.sum_nonneg (fun i hi =>
    Finset.sum_nonneg (fun k hk =>
      integral_nonneg (μ := (volume : Measure (X N)).restrict (abox N ℓ))
        (by intro x; exact sq_nonneg _)))

/-- Finite sum–integral interchange over the centred box: for smooth `Φ`,
`∫ (Σ_k ∂²ₖ) = Σ_k ∫ ∂²ₖ` for every particle. -/
lemma kinSum_sum_integral {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (Φ : X N → ℝ)
    (hΦc : ContDiff ℝ ∞ Φ) :
    (∑ i : Fin N, ∫ x in abox N ℓ, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) =
      (∑ i : Fin N, ∑ k : Fin 3, ∫ x in abox N ℓ, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  have hfs := integral_finsetSum (s := Finset.univ) (μ := (volume : Measure (X N)).restrict (abox N ℓ))
    (f := fun k : Fin 3 => fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2) (by
      intro k hk
      have hc : Continuous (fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
        exact (firstDir_contDiff (f := Φ) hΦc (kcDir N i k)).continuous.pow 2
      exact integrableOn_abox_of_continuous hℓ hc)
  exact hfs

/-- Per-particle sector gap over the centred box: the excited part of
particle `i` costs kinetic energy —
`∫_{abox N ℓ} (aQ ℓ i Φ)² ≤ 36·ℓ²·∫_{abox N ℓ} Σ_k (fderiv Φ (kcDir N i k))²`. -/
theorem centredGap_i {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) ≤
      (36 : ℝ) * ℓ ^ 2 *
        (∫ x in abox N ℓ, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      let ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ)
      let fib : X n → ℝ³ → ℝ := fun r y => Φ (kcInsN n i (y, r))
      let I1 : X n → ℝ := fun r => ∫ y in acube ℓ, (aQ ℓ i Φ (kcInsN n i (y, r))) ^ 2
      let I2 : X n → ℝ := fun r => ∫ y in acube ℓ,
          ∑ k : Fin 3, (fderiv ℝ Φ (kcInsN n i (y, r)) (kcDir (n + 1) i k)) ^ 2
      have hident : ∀ r y, aQ ℓ i Φ (kcInsN n i (y, r))
          = fib r y - (1 / ℓ ^ 3) * (∫ z in acube ℓ, fib r z) := by
        intro r y
        dsimp [fib]
        unfold aQ
        simp [aP_kcInsN (ℓ := ℓ) (Φ := Φ) i y r]
      have hfibc : ∀ r : X n, ContDiff ℝ ∞ (fib r) := by
        intro r
        dsimp [fib]
        exact fiber_contDiff i hΦc r
      -- pointwise inequality: I1 ≤ 36 ℓ² · I2
      have hpt : ∀ r : X n, I1 r ≤ (36 : ℝ) * ℓ ^ 2 * I2 r := by
        intro r
        have hc := acube_gap hℓ (φ := fib r) (hfibc r)
        have hcL : I1 r = (∫ y in acube ℓ,
            ((fib r y) - (1 / ℓ ^ 3) * (∫ z in acube ℓ, fib r z)) ^ 2) := by
          dsimp [I1]
          apply integral_congr_ae
          filter_upwards with y
          rw [hident r y]
        have hcR : I2 r = (∫ y in acube ℓ,
            ∑ k : Fin 3, (fderiv ℝ (fib r) y (euclBasis3 k)) ^ 2) := by
          dsimp [I2]
          apply integral_congr_ae
          filter_upwards with y
          -- Σ over euclBasis3 = Σ over master kcDir-terms
          calc
            (∑ k : Fin 3, (fderiv ℝ Φ (kcInsN n i (y, r)) (kcDir (n + 1) i k)) ^ 2)
                = (∑ k : Fin 3, (fderiv ℝ (fib r) y (kcStdBasis k)) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  congr 1
                  dsimp [fib]
                  exact (fiber_fderiv_kcDir i hΦc r y k).symm
            _ = (∑ k : Fin 3, (fderiv ℝ (fib r) y (euclBasis3 k)) ^ 2) := by
                  exact (sum_fderiv_onb_eq_coord (φ := fib r) y).symm
        have hI : I1 r ≤ (36 : ℝ) * ℓ ^ 2 * I2 r := by
          rw [hcL, hcR]
          simpa using hc
        exact hI
      -- integrability of the peeled fibres
      have hI1_int : Integrable I1 ν := by
        exact abox_peel_inner_integrable (i := i)
          (F := fun x : X (n + 1) => (aQ ℓ i Φ x) ^ 2) (integrableOn_sq_aQ hℓ i hΦc.continuous)
      have hI2_int : Integrable I2 ν := by
        exact abox_peel_inner_integrable (i := i)
          (F := fun x : X (n + 1) => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
          (kinSum_integrableOn_abox hℓ i hΦc)
      have hI2m_int : Integrable (fun r : X n => (36 : ℝ) * ℓ ^ 2 * I2 r) ν := by
        exact (hI2_int.mul_const ((36 : ℝ) * ℓ ^ 2)).congr (by
          filter_upwards with r
          ring)
      -- peel equalities
      have hPeelL : (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2) = ∫ r : X n, I1 r ∂ν := by
        exact abox_integral_peel (i := i)
          (F := fun x : X (n + 1) => (aQ ℓ i Φ x) ^ 2) (integrableOn_sq_aQ hℓ i hΦc.continuous)
      have hPeelR : (∫ x in abox (n + 1) ℓ, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2) =
          ∫ r : X n, I2 r ∂ν := by
        exact abox_integral_peel (i := i)
          (F := fun x : X (n + 1) => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2)
          (kinSum_integrableOn_abox hℓ i hΦc)
      calc
        (∫ x in abox (n + 1) ℓ, (aQ ℓ i Φ x) ^ 2) = ∫ r : X n, I1 r ∂ν := hPeelL
        _ ≤ ∫ r : X n, ((36 : ℝ) * ℓ ^ 2 * I2 r) ∂ν := by
              exact integral_mono_ae (μ := ν) hI1_int hI2m_int (by filter_upwards with r; exact hpt r)
        _ = (36 : ℝ) * ℓ ^ 2 * (∫ r : X n, I2 r ∂ν) := by
              rw [MeasureTheory.integral_const_mul]
        _ = (36 : ℝ) * ℓ ^ 2 * (∫ x in abox (n + 1) ℓ,
              ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (n + 1) i k)) ^ 2) := by
              rw [hPeelR]

/-- Summed sector gap over the centred box: the total number of excited
particles is bounded by the kinetic word —
`cnPlus ℓ Φ ≤ 36·ℓ²·kinWord N ℓ Φ`. -/
theorem centredGap {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    cnPlus ℓ Φ ≤ (36 : ℝ) * ℓ ^ 2 * kinWord N ℓ Φ := by
  unfold cnPlus kinWord
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
        ≤ ∑ i : Fin N, (36 : ℝ) * ℓ ^ 2 *
            (∫ x in abox N ℓ, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
          exact Finset.sum_le_sum (fun i hi => centredGap_i hℓ i hΦc)
    _ = (36 : ℝ) * ℓ ^ 2 *
          (∑ i : Fin N, ∫ x in abox N ℓ, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (36 : ℝ) * ℓ ^ 2 * kinWord N ℓ Φ := by
          dsimp [kinWord]
          rw [kinSum_sum_integral hℓ Φ hΦc]

end BoseGases

end Submission
