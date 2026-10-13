import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS_EllLimOK.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Fatou for the `ℋ^k`-energy along pointwise-convergent sequences

`Work.FTS_EllLimOK.HkSq_le_of_JConv`: if every `Ψn n` lies in `ℋ^k` (`HkMem`), the energies
`HkSq α k (Ψn n)` are uniformly bounded by `B`, and all mixed slots `D_z^j D_θ^i (Ψn n)` with
`j + i ≤ k` converge pointwise on the open quadrant `Qd` to the corresponding slot of `Ψ`, then
`HkSq α k Ψ ≤ B`.

The proof is Fatou's lemma, applied once in `θ` and once in `z`:

* **the integrands converge**, and in fact at every point of `Iz × Iθ`: on `Qd` this is the
  hypothesis on the slots (the weights only depend on the point), while at `z = 0` the weight
  `w 0 = (1+0)²/0² = 0` kills the integrand, and at `sin (2θ) = 0` every summand carries a
  factor `sin (2θ)` or `1/sin(2θ)^{η/2}` and vanishes.  Hence no exceptional set at all;
* **the slices of the limit integrand are a.e. measurable** (`AEMeasurable.liminf`: a pointwise --
  hence a.e. -- limit of a.e. measurable functions is a.e. measurable);
* **Fatou in `θ`** (`MeasureTheory.lintegral_liminf_le'`) gives, for each `z ∈ Iz`, the `ℝ≥0∞`
  inequality `∫⁻_θ ofReal (HkIntegrand α k Ψ z ·) ≤ liminf_n ∫⁻_θ ofReal (HkIntegrand α k (Ψn n) z ·)`;
  converting on both sides with `integral_eq_lintegral_of_nonneg_ae` and `ofReal_toReal_le` turns
  this into the real inequality `ofReal (∫_θ HkIntegrand α k Ψ z ·) ≤ liminf_n ofReal (∫_θ HkIntegrand α k (Ψn n) z ·)`;
* **Fatou in `z`** does the same at the outer level, the sequence of `z`-functions being
  integrable (the second half of `HkMem`) and nonnegative, and the `z`-integrals of the sequence
  being exactly the `HkSq α k (Ψn n)`, bounded by `B`.  This gives
  `∫⁻_z ofReal (∫_θ HkIntegrand α k Ψ z ·) ≤ ofReal B`;
* **conclusion**: either `z ↦ ∫_θ HkIntegrand α k Ψ z ·` is integrable, in which case
  `HkSq α k Ψ = (∫⁻_z ...).toReal ≤ B`; or it is not, in which case Lean's Bochner integral is
  `0` (`MeasureTheory.integral_undef`), so `HkSq α k Ψ = 0 ≤ B`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Vanishing of the `ℋ^k`-integrand on the boundary of the domain -/

/-- The `ℋ^k`-integrand vanishes at `z = 0`: the radial weight `w 0 = (1+0)²/0² = 0` kills both
blocks of the defining sum. -/
theorem HkIntegrand_fst_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  have hw : Work.Spaces.w (0 : ℝ) = 0 := by norm_num [Work.Spaces.w]
  have hW : Work.Spaces.Wt α 0 θ = 0 := by rw [Work.Spaces.Wt, hw, zero_mul]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f 0 θ *
        (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hw, zero_div, mul_zero, sq, mul_zero]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, hW, mul_zero, sq, mul_zero]
    · rw [ite_eq_right hc]
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]

/-- At an angle where `sin (2θ) = 0`, every `D_θ`-iterate `D_θ^i u` with `i ≥ 1` vanishes: the
outermost `D_θ` is `sin (2θ) · ∂_θ`. -/
lemma DthIter_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.DthIter i u z θ = 0 := by
  cases i with
  | zero => omega
  | succ m => simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h, zero_mul]

/-- If `g (·) θ` vanishes identically, then so does every `D_z`-iterate `D_z^j g (·) θ`. -/
lemma DzIter_eq_zero_of_forall_eq_zero (g : ℝ → ℝ → ℝ) (θ : ℝ) (hg : ∀ z, g z θ = 0)
    (j : ℕ) (z : ℝ) : Work.Spaces.DzIter j g z θ = 0 := by
  induction j generalizing z with
  | zero => simpa using hg z
  | succ m ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hfun : (fun z' => Work.Spaces.DzIter m g z' θ) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.pz, hfun, deriv_const, mul_zero]

/-- At an angle where `sin (2θ) = 0`, every mixed derivative `D_z^j D_θ^i u` with `i ≥ 1`
vanishes. -/
lemma mixed_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.mixed j i u z θ = 0 := by
  rw [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_forall_eq_zero (Work.Spaces.DthIter i u) θ
    (fun z' => DthIter_eq_zero_of_sin_eq_zero u i hi θ h z') j z

/-- The `ℋ^k`-integrand vanishes at any angle `θ` with `sin (2θ) = 0`. -/
theorem HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (k : ℕ) (u : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k u z θ = 0 := by
  have hden : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [h, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i u z θ *
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hden, mul_zero, sq, mul_zero]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left hc, mixed_eq_zero_of_sin_eq_zero u j i hc.1 θ h z, zero_mul, sq, mul_zero]
    · rw [ite_eq_right hc]
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]

/-! ## Convergence of the integrand from convergence of the slots -/

/-- The `ℋ^k`-integrand is a finite sum of squares of terms `slot · weight`, where the weight
depends only on the point: hence convergence of the slots at a point gives convergence of the
integrand there. -/
theorem tendsto_HkIntegrand_of_tendsto_mixed {α : ℝ} {k : ℕ} {fn : ℕ → ℝ → ℝ → ℝ}
    {f : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : ∀ j i : ℕ, j + i ≤ k →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (fn n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2))) :
    Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (fn n) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.HkIntegrand α k f p.1 p.2)) := by
  have key : ∀ (c : ℝ) (j i : ℕ), j + i ≤ k →
      Filter.Tendsto (fun n => (Work.Spaces.mixed j i (fn n) p.1 p.2 * c) ^ 2) Filter.atTop
        (nhds ((Work.Spaces.mixed j i f p.1 p.2 * c) ^ 2)) :=
    fun c j i hji => ((h j i hji).mul_const c).pow 2
  simp only [Work.Spaces.HkIntegrand]
  refine Tendsto.add ?_ ?_
  · refine tendsto_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact key _ i 0 (by have := Finset.mem_range.mp hi; omega)
  · refine tendsto_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    refine tendsto_finsetSum (Finset.range (k + 1)) (fun j hj => ?_)
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [ite_eq_left hc]
      exact key _ j i (by omega)
    · simp only [ite_eq_right hc]
      exact tendsto_const_nhds

/-! ## The main theorem -/

theorem HkSq_le_of_JConv {α : ℝ} {k : ℕ} {Ψn : ℕ → Work.FTS.Galerkin.Fn}
    {Ψ : Work.FTS.Galerkin.Fn} {B : ℝ}
    (hMem : ∀ n, Work.Spaces.HkMem α k (Ψn n))
    (hB : ∀ n, Work.Spaces.HkSq α k (Ψn n) ≤ B)
    (h : ∀ j i : ℕ, j + i ≤ k → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (Ψn n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Ψ z θ))) :
    Work.Spaces.HkSq α k Ψ ≤ B := by
  classical
  have hB0 : 0 ≤ B := le_trans (Work.Spaces.HkSq_nonneg α k (Ψn 0)) (hB 0)
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici

  -- (i) the integrands converge, at every point of `Iz × Iθ`
  have hconv : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) Filter.atTop
        (nhds (Work.Spaces.HkIntegrand α k Ψ z θ)) := by
    intro z hz θ hθ
    by_cases hz0 : z = 0
    · subst hz0
      have h1 : ∀ n, Work.Spaces.HkIntegrand α k (Ψn n) 0 θ = 0 :=
        fun n => HkIntegrand_fst_zero α k (Ψn n) θ
      have h2 : Work.Spaces.HkIntegrand α k Ψ 0 θ = 0 := HkIntegrand_fst_zero α k Ψ θ
      rw [show (fun n => Work.Spaces.HkIntegrand α k (Ψn n) 0 θ) = fun _ => (0 : ℝ) from
        funext h1, h2]
      exact tendsto_const_nhds
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      by_cases hsin : Real.sin (2 * θ) = 0
      · have h1 : ∀ n, Work.Spaces.HkIntegrand α k (Ψn n) z θ = 0 :=
          fun n => HkIntegrand_eq_zero_of_sin_eq_zero α k (Ψn n) z θ hsin
        have h2 : Work.Spaces.HkIntegrand α k Ψ z θ = 0 :=
          HkIntegrand_eq_zero_of_sin_eq_zero α k Ψ z θ hsin
        rw [show (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) = fun _ => (0 : ℝ) from
          funext h1, h2]
        exact tendsto_const_nhds
      · have hθ0 : 0 < θ := by
          rcases lt_or_eq_of_le hθ.1 with h' | h'
          · exact h'
          · exact absurd (by rw [← h']; simp) hsin
        have hθpi : θ < π / 2 := by
          rcases lt_or_eq_of_le hθ.2 with h' | h'
          · exact h'
          · exact absurd (by rw [h', show 2 * (π / 2) = π by ring]; exact Real.sin_pi) hsin
        exact tendsto_HkIntegrand_of_tendsto_mixed (α := α) (k := k) (fn := Ψn) (f := Ψ)
          (p := (z, θ))
          (fun j i hji => h j i hji z θ (by
            rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
            exact ⟨hzpos, hθ0, hθpi⟩))

  -- (ii) the slices of the limit integrand are a.e. strongly measurable
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => Work.Spaces.HkIntegrand α k Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hlim : AEMeasurable
        (fun θ => Filter.liminf
          (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) Filter.atTop)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      AEMeasurable.liminf (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable)
    have hEq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.liminf (fun n => Work.Spaces.HkIntegrand α k (Ψn n) z θ) Filter.atTop
          = Work.Spaces.HkIntegrand α k Ψ z θ := by
      rw [MeasureTheory.ae_restrict_iff' hIθ]
      exact Filter.Eventually.of_forall fun θ hθ => (hconv z hz θ hθ).liminf_eq
    exact hlim.congr hEq

  -- (iii) Fatou in `θ`, for each fixed `z`
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := by
    intro z hz
    have hfat := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
      (f := fun n θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ))
      (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hEq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
          = Filter.liminf
              (fun n => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ))
                Filter.atTop := by
      rw [MeasureTheory.ae_restrict_iff' hIθ]
      exact Filter.Eventually.of_forall fun θ hθ =>
        ((ENNReal.continuous_ofReal.tendsto (Work.Spaces.HkIntegrand α k Ψ z θ)).comp
          (hconv z hz θ hθ)).liminf_eq.symm
    rw [MeasureTheory.lintegral_congr_ae hEq]
    exact hfat

  -- (iv) the same statement for the real `θ`-integrals
  have hGle : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
        ≤ Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ)) Filter.atTop := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
        = (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k Ψ z θ)
        ((hslice z hz).aestronglyMeasurable)
    calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
        = ENNReal.ofReal ((∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal) := by rw [h1]
      _ ≤ (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k Ψ z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := ENNReal.ofReal_toReal_le
      _ ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Ψn n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := hinner z hz
      _ = Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ)) Filter.atTop := by
          refine Filter.liminf_congr (Filter.Eventually.of_forall fun n => ?_)
          exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).1 z hz)
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k (Ψn n) z θ)).symm

  -- (v) Fatou in `z`
  have hFatouZ := MeasureTheory.lintegral_liminf_le'
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (u := Filter.atTop)
    (f := fun n z => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ))
    (fun n => ((hMem n).2).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hchain : (∫⁻ z, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) ≤ ENNReal.ofReal B := by
    refine le_trans (MeasureTheory.lintegral_mono_ae ?_) (le_trans hFatouZ ?_)
    · have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
            ≤ Filter.liminf (fun n => ENNReal.ofReal
                (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ))
                  Filter.atTop := by
        rw [MeasureTheory.ae_restrict_iff' hIz]
        exact Filter.Eventually.of_forall fun z hz => hGle z hz
      exact hle
    · have hrew : Filter.liminf (fun n => ∫⁻ z, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Ψn n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) Filter.atTop
          = Filter.liminf (fun n => ENNReal.ofReal (Work.Spaces.HkSq α k (Ψn n)))
              Filter.atTop := by
        refine Filter.liminf_congr (Filter.Eventually.of_forall fun n => ?_)
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).2)
          (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
            (fun θ => Work.Spaces.HkIntegrand_nonneg α k (Ψn n) z θ))).symm
      rw [hrew, Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun n =>
        (iInf_le _ n).trans ((iInf_le _ le_rfl).trans (ENNReal.ofReal_le_ofReal (hB n)))

  -- (vi) conclusion
  by_cases hInt : MeasureTheory.Integrable
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
  · have h4 : Work.Spaces.HkSq α k Ψ
        = (∫⁻ z, ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)).toReal := by
      rw [show Work.Spaces.HkSq α k Ψ
          = (∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ) from rfl]
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
          (fun θ => Work.Spaces.HkIntegrand_nonneg α k Ψ z θ))
        hInt.aestronglyMeasurable
    rw [h4]
    exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain)
      (by rw [ENNReal.toReal_ofReal hB0])
  · have h0 : Work.Spaces.HkSq α k Ψ = 0 := by
      rw [show Work.Spaces.HkSq α k Ψ
          = (∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k Ψ z θ) from rfl]
      exact MeasureTheory.integral_undef hInt
    rw [h0]
    exact hB0

end Work.FTS_EllLimOK
