/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-`z` bound for the level-`3` `ℋ`-integrand

`Work.FTS.StrongEps.E5G.HkIntegrand_three_perz_le`: there is a universal constant `C` with

  `∫_{Iθ} HkIntegrand α 3 f z θ ≤ C * (1 + (w z) ^ 2) * (1 + |f|_{ℋ⁴}) ^ 2`

for every `α ∈ (0,1]`, every `f` of class `C^∞` on the open quadrant (`SmoothOpen f`) which is
honestly in `ℋ⁴` (`HkMem α 4 f`), and every `z ∈ Iz = [0,∞)`.

## Proof

At `z = 0` the weight `w` vanishes and every summand of the integrand is `0`; for `z > 0` the
level-`3` integrand is the sum of its `z`-slots (`i ≤ 3`) and its mixed slots (`1 ≤ i`,
`i + j ≤ 3`), estimated separately at the fixed radius `z`:

* **`z`-slots**: the window form of the radial Hardy inequality at level `4`
  (`Work.FTS.StrongEps.E5Aux.zslot_window_perz` with `k = 4`, `i ≤ 3`) bounds the slot at the
  angle `σ` by `(w z)² * (2 + 2/R₀) * ∫_s HkIntegrand α 4 f s σ` with `R₀ = max z 2`; the
  Tonelli identity `sda_HkSqSwap_open` turns the `θ`-integral of the right-hand side into
  `(w z)² * (2 + 2/R₀) * HkSq α 4 f ≤ 3 (w z)² HkSq α 4 f`.  (The extra `sin(2σ)^{-η}` of the
  slot's weight is absorbed by the inequality `i + 1 ≤ 4` used inside.)
* **mixed slots**: `(Wt α z θ)² = (w z)² sin(2θ)^{-γ}`, and the uniform angular slice bound
  `Work.FTS.OpenPkg.ProdOpen.sliceAng_le` at `(b,a) = (j,i)` (with `a ≥ 1`, `a + b ≤ 3`)
  bounds the `θ`-integral of `(mixed j i f)² sin(2θ)^{-γ}` by `C * HkSq α 4 f`; again the
  missing `z`-decay is bought by the radius-`R₀` window at each angle.

Summing the finitely many slots (`≤ 4`, resp. `≤ 16` of them) and using
`HkSq α 4 f ≤ (1 + |f|_{ℋ⁴})²` gives the claim.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.GalBasis.cc.intervalIntegrable_mixed_div_sin
import Submission.Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le
import Submission.Work.FTS.StrongEps.E5Aux.zslot_window_perz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Integrability of a finite sum of integrable functions -/

private lemma integrable_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, MeasureTheory.Integrable (g i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MeasureTheory.integrable_zero ℝ ℝ μ
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (g a) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [show (fun x : ℝ => ∑ i ∈ insert a s, g i x)
          = fun x : ℝ => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      exact h1.add h2

/-! ## The integrand at `z = 0` -/

private theorem HkIntegrand_three_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α 3 f 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
  have h1 : ∀ i : ℕ, (Work.Spaces.DzIter i f 0 θ
      * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i; rw [hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have h2 : ∀ i j : ℕ, (Work.Spaces.mixed j i f 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 = 0 := by
    intro i j
    rw [Work.Spaces.Wt, hw, zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [Work.Spaces.HkIntegrand]
  simp only [h1, h2, ite_self, Finset.sum_const_zero, add_zero]

/-! ## The per-`z` bound for a single `z`-slot, against the level-`4` norm -/

private theorem zslot_perz_le_four (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {i : ℕ} (hi : i ≤ 3) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 3 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f := by
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  set R₀ : ℝ := max z 2 with hR₀
  have hzR : z ≤ R₀ := le_max_left z 2
  have h2R : (2 : ℝ) ≤ R₀ := le_max_right z 2
  have hRpos : 0 < R₀ := lt_of_lt_of_le (by norm_num) h2R
  have hcoef : (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀) ≤ 3 * (Work.Spaces.w z) ^ 2 := by
    have h1 : 2 / R₀ ≤ 1 := by
      rw [div_le_one hRpos]
      linarith
    nlinarith [sq_nonneg (Work.Spaces.w z)]
  have hle : (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
        * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ : ℝ => (3 * (Work.Spaces.w z) ^ 2)
        * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)) := by
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ, hGslice] with σ hσ hσint
    have hwin :=
      Work.FTS.StrongEps.E5Aux.zslot_window_perz α hF 4 i (by omega) hz hzR hσ hσint
    have hI : 0 ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ :=
      integral_nonneg fun s => Work.Spaces.HkIntegrand_nonneg α 4 f s σ
    calc (Work.Spaces.DzIter i f z σ
            * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (2 + 2 / R₀)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := hwin
      _ = ((Work.Spaces.w z) ^ 2 * (2 + 2 / R₀))
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := by ring
      _ ≤ (3 * (Work.Spaces.w z) ^ 2)
            * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
          mul_le_mul_of_nonneg_right hcoef hI
  have hLI : MeasureTheory.Integrable (fun σ : ℝ => (Work.Spaces.DzIter i f z σ
      * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_zSummand α 4 hF hmem i (by omega)
      (Set.mem_Ici.mpr hz.le)
  have hRI : MeasureTheory.Integrable (fun σ : ℝ => (3 * (Work.Spaces.w z) ^ 2)
      * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hGint.const_mul _
  have hmain := MeasureTheory.integral_mono_ae hLI hRI hle
  rw [MeasureTheory.integral_const_mul, hswap] at hmain
  exact hmain

/-! ## The per-`z` bound for a single mixed slot, against the level-`4` norm -/

/-- The uniform angular slice bound `Work.FTS.OpenPkg.ProdOpen.sliceAng_le`, as a predicate
in its constant, so that it can be passed around. -/
private def SliceAngBd (C : ℝ) : Prop :=
  ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f → 1 ≤ a → a + b ≤ 3 →
    ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ C * Work.Spaces.HkSq α 4 f

private theorem mixed_perz_le_four {C : ℝ} (hC : SliceAngBd C) {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 4 f) {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 3) {z : ℝ}
    (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ (C * (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 4 f := by
  have hcongr : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [← MeasureTheory.integral_const_mul]
    refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hs]
    ring
  rw [hcongr]
  have hb := hC α f j i hα0 hα1 hF hmem hi hij z hz
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (Work.Spaces.w z) ^ 2 * (C * Work.Spaces.HkSq α 4 f) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (C * (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 4 f := by ring

/-! ## Integrability of a mixed slot of the level-`3` integrand -/

private lemma integrableOn_if_mixed_three (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 3
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ 3
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 3
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff'
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j h.1 (by omega)
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 3
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The target -/

theorem HkIntegrand_three_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
      α ∈ Set.Ioc 0 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 4 f) ^ 2 := by
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.OpenPkg.ProdOpen.sliceAng_le
  have hSAB : SliceAngBd Cang := hCang
  refine ⟨12 + 16 * Cang, by linarith, ?_⟩
  intro α f hα hF hmem z hz
  obtain ⟨hα0, hα1⟩ := hα
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- ### the degenerate case `z = 0`
    subst hz0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 f 0 θ) = 0 := by
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α 3 f 0 θ) = fun _ : ℝ => (0 : ℝ)
        from funext (fun θ => HkIntegrand_three_zero α f θ)]
      simp
    rw [hzero]
    have hCpos : 0 < 12 + 16 * Cang := by linarith
    have hw : (0 : ℝ) ≤ 1 + (Work.Spaces.w 0) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hCpos.le hw) (sq_nonneg _)
  · -- ### the main case `z > 0`
    have hPint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum _ (fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hF hmem i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          (if 1 ≤ i ∧ i + j ≤ 3
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j _ => integrableOn_if_mixed_three α hF hmem i j hzpos))
    have hdec : (fun θ : ℝ => Work.Spaces.HkIntegrand α 3 f z θ)
        = fun θ : ℝ => (∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
              (if 1 ≤ i ∧ i + j ≤ 3
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      funext θ
      rw [Work.Spaces.HkIntegrand]
    have hPb : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 12 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 4) (hf := fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hF hmem i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))]
      calc ∑ i ∈ Finset.range 4, (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 4,
              (3 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) :=
            Finset.sum_le_sum fun i hi => zslot_perz_le_four α hF hmem
              (by rw [Finset.mem_range] at hi; omega) hzpos
        _ = 12 * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
            ring
    have hMb : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
          (if 1 ≤ i ∧ i + j ≤ 3
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 16 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 4) (hf := fun i _ =>
        integrable_finsetSum _ (fun j _ => integrableOn_if_mixed_three α hF hmem i j hzpos))]
      calc ∑ i ∈ Finset.range 4, (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range 4,
              (if 1 ≤ i ∧ i + j ≤ 3
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range 4,
              (4 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range 4) (hf := fun j _ =>
              integrableOn_if_mixed_three α hF hmem i j hzpos)]
            calc ∑ j ∈ Finset.range 4, (∫ θ in Work.Spaces.Iθ,
                    (if 1 ≤ i ∧ i + j ≤ 3
                      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
                ≤ ∑ _j ∈ Finset.range 4,
                    (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  by_cases hij : 1 ≤ i ∧ i + j ≤ 3
                  · simp only [if_pos hij]
                    exact mixed_perz_le_four hSAB hα0 hα1 hF hmem hij.1 (by omega) hzpos
                  · simp only [if_neg hij]
                    have h1 : 0 ≤ Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f :=
                      mul_nonneg (mul_nonneg hCangpos.le (sq_nonneg _))
                        (Work.Spaces.HkSq_nonneg α 4 f)
                    simpa using h1
              _ = 4 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                  norm_num
        _ = 16 * (Cang * (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    rw [hdec, MeasureTheory.integral_add hPint hMint]
    refine le_trans (add_le_add hPb hMb) ?_
    have hXnn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
    have hNnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
    have hXle : Work.Spaces.HkSq α 4 f ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 2 := by
      have hsq : Work.Spaces.HkSq α 4 f = (Work.Spaces.HkNorm α 4 f) ^ 2 := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt hXnn]
      nlinarith [hsq, hNnn, hXnn]
    have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hWle : (Work.Spaces.w z) ^ 2 ≤ 1 + (Work.Spaces.w z) ^ 2 := by linarith
    have h1 : (Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f
        ≤ (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 4 f) ^ 2 :=
      mul_le_mul hWle hXle hXnn (by linarith)
    have h2 : (12 + 16 * Cang)
          * ((Work.Spaces.w z) ^ 2 * Work.Spaces.HkSq α 4 f)
        ≤ (12 + 16 * Cang)
          * ((1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 4 f) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith [h2]

end Work.FTS.StrongEps.E5G
