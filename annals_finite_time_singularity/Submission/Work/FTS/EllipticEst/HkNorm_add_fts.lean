/-
Copyright: work module for the Elgindi finite-time singularity project.

# Subadditivity of the weighted `H^k`-norm (with constant `√2`)

The weighted `H^k`-norm of the paper is `Work.Spaces.HkNorm α k f = sqrt (HkSq α k f)`, where
`HkSq` is the iterated integral, over `[0,∞) × [0,π/2]` with the measure `dz dθ`, of the sum of
squares of the weighted derivatives `D_z^i f · w/sin(2θ)^{η/2}` and `D_z^j D_θ^i f · W`.

The pointwise elementwise inequality `(a+b)² ≤ 2a² + 2b²` on the open quadrant (together with the
additivity of the operators `D_z`, `D_θ` there, packaged below as `HkIntegrand_add_le_Q0`) gives

  `HkSq α k (f+g) ≤ 2·HkSq α k f + 2·HkSq α k g`,

and the elementary inequality `√(2a+2b) ≤ √2·(√a + √b)` (`a, b ≥ 0`) then yields

  `HkNorm α k (f+g) ≤ √2·(HkNorm α k f + HkNorm α k g)`.

Both integrals are compared with `MeasureTheory.integral_mono_of_nonneg`, which only requires the
integrability of the *larger* function: that is exactly the content of the two membership
hypotheses `HkMem α k f`, `HkMem α k g` (no membership of `f + g` is needed).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas -/

/-- A property of angles which holds on the open interval `(0, π/2)` holds almost everywhere on
the closed interval `Iθ`: the two endpoints form a null set and are exactly the complement of
`(0, π/2)` inside `Iθ`. -/
private lemma ae_restrict_Iθ_of_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo 0 (π / 2), p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  refine (MeasureTheory.ae_restrict_congr_set hIoo).mp ?_
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => h θ hθ

/-- **Pointwise subadditivity of the `ℋ^k`-integrand on the open quadrant.**  The `D`-operators
are additive on `(0,∞) × (0,π/2)` for `C^∞` data, and `(a+b)² ≤ 2a² + 2b²` termwise.

(This is the same statement as `Work.FTS.EllipticEst.HkIntegrand_add_le_open`; it is reproduced
here — with a proof — so that this module depends only on `Spaces.Defs`, `SmoothOpenAdd` and
`LocData.HkMem_of_majorant`.) -/
private lemma HkIntegrand_add_le_Q0 {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ := fun i =>
    SmoothOpen.DzIter_add hf hg i z θ hz hθ.1 hθ.2
  have hMixed : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := fun j i =>
    SmoothOpen.mixed_add hf hg j i z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.HkIntegrand]
  have hZ : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + 2 * (Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hDz i, add_mul]
          nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            - Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
      _ = 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
              + 2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hMixed j i, add_mul]
            nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
              - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
          · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
            norm_num
      _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith [hZ, hM]

/-- **The angular slice estimate.**  For every `z ∈ Iz`, the `θ`-integral of the `ℋ^k`-integrand
of `f + g` is at most twice the sum of the `θ`-integrals of the integrands of `f` and of `g`.
The integrability input is only for `f` and `g` (`HkMem`). -/
private lemma HkIntegrand_add_slice_le {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      ≤ 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · -- at `z = 0` the radial weight vanishes, so all three integrands are identically zero
    subst h0
    simp [Work.FTS.LocData.HkIntegrand_zero_fst]
  · have hle : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) :=
      MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ))
        (((hmf.1 z hz).add (hmg.1 z hz)).const_mul 2)
        (ae_restrict_Iθ_of_Ioo fun θ hθ => HkIntegrand_add_le_Q0 hf hg hz0 hθ)
    rwa [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hmf.1 z hz) (hmg.1 z hz)] at hle

/-- **Additivity of the squared `H^k`-norm up to the factor `2`.** -/
private lemma HkSq_add_le {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g := by
  have hmono : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fun z θ => f z θ + g z θ) z θ)
      ((hmf.2.add hmg.2).const_mul 2)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
        fun z hz => HkIntegrand_add_slice_le hf hg hmf hmg hz)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmg.2]
  linarith

/-! ## The main statement -/

theorem HkNorm_add_fts (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
  have hfS : SmoothOpen f := smoothOpen_of_forall (by simpa [Q0] using hf)
  have hgS : SmoothOpen g := smoothOpen_of_forall (by simpa [Q0] using hg)
  have hsq := HkSq_add_le hfS hgS hmf hmg
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt hsq) ?_
  have ha0 : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hb0 : 0 ≤ Work.Spaces.HkSq α k g := Work.Spaces.HkSq_nonneg α k g
  have h2 : 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g
      ≤ (Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α k f)
          + Real.sqrt (Work.Spaces.HkSq α k g))) ^ 2 := by
    have h2s : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hfs : (Real.sqrt (Work.Spaces.HkSq α k f)) ^ 2 = Work.Spaces.HkSq α k f :=
      Real.sq_sqrt ha0
    have hgs : (Real.sqrt (Work.Spaces.HkSq α k g)) ^ 2 = Work.Spaces.HkSq α k g :=
      Real.sq_sqrt hb0
    have hnn : 0 ≤ Real.sqrt (Work.Spaces.HkSq α k f) * Real.sqrt (Work.Spaces.HkSq α k g) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [h2s, hfs, hgs, hnn]
  refine le_trans (Real.sqrt_le_sqrt h2) ?_
  rw [Real.sqrt_sq (by positivity)]

end Work.FTS.EllipticEst
