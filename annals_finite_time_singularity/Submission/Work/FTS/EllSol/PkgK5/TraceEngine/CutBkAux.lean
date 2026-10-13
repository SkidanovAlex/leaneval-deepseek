/-
Auxiliary material for `Work.FTS.EllSol.PkgK5.TraceEngine.cutBkBound`: the local
abbreviations, the continuity/measurability of the joint integrands, the weighted
Cauchy–Schwarz lemma and the pointwise bounds.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore
import Submission.Work.FTS.EllSol.PkgK5.gK_ibp_fts
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine
namespace CutBk

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Local abbreviations -/

/-- The drift coefficient `(z-3)/(1+z)` of the radial weight identity `(z w²)' = w²·b`. -/
def cutB (z : ℝ) : ℝ := (z - 3) / (1 + z)

/-- `D_z²G + b·D_zG`, the radial factor produced by the integration by parts. -/
def cutXi (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.DzIter 2 G p.1 p.2
    + cutB p.1 * Work.Spaces.Dz G p.1 p.2

/-- `∂_θ²G`. -/
def cutD2 (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.pthIter 2 G p.1 p.2

/-- `D_zG`. -/
def cutPs (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.Dz G p.1 p.2

/-- The weight `ρ = w(z)²·thEta(θ)`. -/
def cutRho : ℝ × ℝ → ℝ :=
  fun p => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2

/-- The strip `Iz ×ˢ Iθ`. -/
def Izθ : Set (ℝ × ℝ) := Work.Spaces.Iz ×ˢ Work.Spaces.Iθ

/-- The (restricted Lebesgue) measure on the strip. -/
def Mu : Measure (ℝ × ℝ) := volume.restrict Izθ

/-! ## Elementary facts -/

lemma thEta_zero : Work.FTS.EllipticEst.thEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.thEta, mul_zero, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

lemma thEta_piHalf : Work.FTS.EllipticEst.thEta (π / 2) = 0 := by
  have h2 : 2 * (π / 2) = π := by ring
  rw [Work.FTS.EllipticEst.thEta, h2, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

lemma measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

lemma measurableSet_Izθ : MeasurableSet Izθ := by
  rw [Izθ, Work.Spaces.Iz, Work.Spaces.Iθ]
  exact measurableSet_Ici.prod measurableSet_Icc

lemma Mu_eq_prod :
    Mu = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [Mu, Izθ, Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- The set integral over the strip is the integral for the product of the two restricted
measures. -/
lemma setIntegral_Izθ_eq_prod {f : ℝ × ℝ → ℝ} :
    (∫ p in Izθ, f p)
      = ∫ p, f p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  show (∫ p, f p ∂Mu) = _
  rw [Mu_eq_prod]

/-- A pointwise statement on the strip is an almost-everywhere statement. -/
lemma ae_of_mem_Izθ {P : ℝ × ℝ → Prop} (h : ∀ p ∈ Izθ, P p) :
    ∀ᵐ p ∂Mu, P p := by
  rw [Mu, ae_restrict_iff' measurableSet_Izθ]
  exact Eventually.of_forall h

/-- A pointwise statement on `Iθ` is an almost-everywhere statement. -/
lemma ae_of_mem_Iθ {P : ℝ → Prop} (h : ∀ θ ∈ Work.Spaces.Iθ, P θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), P θ := by
  rw [ae_restrict_iff' measurableSet_Iθ]
  exact Eventually.of_forall h

/-- `cutRho` is nonnegative on the strip. -/
lemma cutRho_nonneg {p : ℝ × ℝ} (hp : p ∈ Izθ) : 0 ≤ cutRho p :=
  mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hp.2)

/-- `cutRho (0,θ) = 0`: the radial weight vanishes at `z = 0`. -/
lemma cutRho_zero_fst (θ : ℝ) : cutRho (0, θ) = 0 := by
  simp [cutRho, Work.Spaces.w]

/-! ## Continuity on the open quadrant -/

lemma contOn_comp_fst {f : ℝ → ℝ} {s t : Set ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1) (s ×ˢ t) := by
  have hmap : Set.MapsTo (Prod.fst : ℝ × ℝ → ℝ) (s ×ˢ t) s := fun p hp => hp.1
  have h := hf.comp continuousOn_fst hmap
  simpa only [Function.comp_def] using h

lemma contOn_comp_snd {f : ℝ → ℝ} {s t : Set ℝ} (hf : ContinuousOn f s) :
    ContinuousOn (fun p : ℝ × ℝ => f p.2) (t ×ˢ s) := by
  have hmap : Set.MapsTo (Prod.snd : ℝ × ℝ → ℝ) (t ×ˢ s) s := fun p hp => hp.2
  have h := hf.comp continuousOn_snd hmap
  simpa only [Function.comp_def] using h

lemma continuousOn_cutB_comp :
    ContinuousOn (fun p : ℝ × ℝ => cutB p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h : ContinuousOn (fun z : ℝ => (z - 3) / (1 + z)) (Set.Ioi 0) := by
    refine ContinuousOn.div (continuousOn_id.sub continuousOn_const)
      (continuousOn_const.add continuousOn_id) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    linarith
  have h2 := contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) h
  simpa only [cutB] using h2

lemma continuousOn_cutRho :
    ContinuousOn cutRho (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hmain : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.mul ?_ ?_
    · have h : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := by
        refine ContinuousOn.pow (ContinuousOn.div
          ((continuousOn_const.add continuousOn_id).pow 2) (continuousOn_id.pow 2) ?_) 2
        intro z hz
        exact pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < z from hz))
      have h2 := contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) h
      simpa only [Work.Spaces.w] using h2
    · have h : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          (Set.Ioo 0 (π / 2)) := by
        refine ContinuousOn.rpow_const
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
        intro θ hθ
        left
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))
      have h2 := contOn_comp_snd (t := Set.Ioi (0 : ℝ)) h
      simpa only [Work.FTS.EllipticEst.thEta] using h2
  exact hmain

lemma continuousOn_cutXi {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (cutXi G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hmain : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 2 G p.1 p.2
      + cutB p.1 * Work.Spaces.Dz G p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.add (hG.DzIter 2).continuousOn ?_
    exact continuousOn_cutB_comp.mul (hG.Dz).continuousOn
  exact hmain

lemma continuousOn_cutD2 {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (cutD2 G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (hG.pth.pth).continuousOn

lemma continuousOn_cutPs {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (cutPs G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (hG.Dz).continuousOn

lemma continuousOn_cutChi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => χ k p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ 1 (χ k) (Set.Ioi 0) :=
    (hχ.sm k).of_le (by simp [Work.Stability.smoothOrder])
  exact contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) h1.continuousOn

lemma continuousOn_cutDchi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (χ k) p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h1 : ContDiffOn ℝ 1 (χ k) (Set.Ioi 0) :=
    (hχ.sm k).of_le (by simp [Work.Stability.smoothOrder])
  have hd : ContinuousOn (fun z : ℝ => deriv (χ k) z) (Set.Ioi 0) :=
    h1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  exact contOn_comp_fst (t := Set.Ioo (0 : ℝ) (π / 2)) hd

/-! ## A.e. strong measurability of the joint integrands -/

lemma aesm_of_Qd {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) : AEStronglyMeasurable g Mu := by
  rw [Mu_eq_prod]
  exact Work.Spaces.aesm_of_continuousOn_Qd g hg

lemma aesm_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p) Mu :=
  aesm_of_Qd ((continuousOn_cutRho.mul (continuousOn_cutChi hχ k)).mul
    (continuousOn_cutXi hG) |>.mul (continuousOn_cutD2 hG))

lemma aesm_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) Mu :=
  aesm_of_Qd ((((continuousOn_fst.mul (continuousOn_cutDchi hχ k)).mul continuousOn_cutRho).mul
    (continuousOn_cutPs hG)).mul (continuousOn_cutD2 hG))

/-! ## Cauchy–Schwarz in `L²` with an a.e.-nonnegative weight -/

lemma csSqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ Ξ Φ : α → ℝ}
    (hρ : 0 ≤ ρ) (hΞ : Integrable (fun x => ρ x * Ξ x ^ 2) μ)
    (hΦ : Integrable (fun x => ρ x * Φ x ^ 2) μ) :
    Integrable (fun x => ρ x * |Ξ x| * |Φ x|) μ
      ∧ (∫ x, ρ x * |Ξ x| * |Φ x| ∂μ)
        ≤ Real.sqrt (∫ x, ρ x * Ξ x ^ 2 ∂μ) * Real.sqrt (∫ x, ρ x * Φ x ^ 2 ∂μ) := by
  set f : α → ℝ := fun x => Real.sqrt (ρ x * Ξ x ^ 2) with hf
  set g : α → ℝ := fun x => Real.sqrt (ρ x * Φ x ^ 2) with hg
  have hfm : AEStronglyMeasurable f μ :=
    (hΞ.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g μ :=
    (hΦ.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hf2 : (fun x => f x ^ 2) = fun x => ρ x * Ξ x ^ 2 := by
    funext x; rw [hf]; exact Real.sq_sqrt (mul_nonneg (hρ x) (sq_nonneg _))
  have hg2 : (fun x => g x ^ 2) = fun x => ρ x * Φ x ^ 2 := by
    funext x; rw [hg]; exact Real.sq_sqrt (mul_nonneg (hρ x) (sq_nonneg _))
  have hfmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).mpr (by rw [hf2]; exact hΞ)
  have hgmem : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).mpr (by rw [hg2]; exact hΦ)
  have hsq : ∀ x, f x * g x = ρ x * |Ξ x| * |Φ x| := by
    intro x
    have h1 : Real.sqrt (ρ x * Ξ x ^ 2) * Real.sqrt (ρ x * Φ x ^ 2)
        = Real.sqrt ((ρ x * Ξ x ^ 2) * (ρ x * Φ x ^ 2)) :=
      (Real.sqrt_mul (mul_nonneg (hρ x) (sq_nonneg _)) _).symm
    rw [hf, hg, h1]
    have h2 : (ρ x * Ξ x ^ 2) * (ρ x * Φ x ^ 2) = (ρ x * |Ξ x| * |Φ x|) ^ 2 := by
      rw [← sq_abs (Ξ x), ← sq_abs (Φ x)]
      ring
    rw [h2, Real.sqrt_sq]
    exact mul_nonneg (mul_nonneg (hρ x) (abs_nonneg _)) (abs_nonneg _)
  have hfun : (fun x => f x * g x) = fun x => ρ x * |Ξ x| * |Φ x| := funext hsq
  have hdom : Integrable (fun x => (1 / 2) * (ρ x * Ξ x ^ 2 + ρ x * Φ x ^ 2)) μ :=
    (hΞ.add hΦ).const_mul (1 / 2)
  have hInt : Integrable (fun x => f x * g x) μ := by
    refine Integrable.mono' hdom (hfm.mul hgm) (Eventually.of_forall fun x => ?_)
    have hnn : (0 : ℝ) ≤ f x * g x := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_of_nonneg hnn, hsq]
    have hxn : (0 : ℝ) ≤ ρ x := hρ x
    have hΞx : (0 : ℝ) ≤ |Ξ x| := abs_nonneg _
    have hΦx : (0 : ℝ) ≤ |Φ x| := abs_nonneg _
    have hsq1 : |Ξ x| ^ 2 = Ξ x ^ 2 := sq_abs (Ξ x)
    have hsq2 : |Φ x| ^ 2 = Φ x ^ 2 := sq_abs (Φ x)
    nlinarith [sq_nonneg (|Ξ x| - |Φ x|)]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (f := f) (g := g)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (by simpa using hfmem) (by simpa using hgmem)
  have hf2' : (∫ x, f x ^ (2 : ℝ) ∂μ) = ∫ x, ρ x * Ξ x ^ 2 ∂μ := by
    rw [show (fun x => f x ^ (2 : ℝ)) = fun x => ρ x * Ξ x ^ 2 from by
      funext x; rw [Real.rpow_two]; exact congrFun hf2 x]
  have hg2' : (∫ x, g x ^ (2 : ℝ) ∂μ) = ∫ x, ρ x * Φ x ^ 2 ∂μ := by
    rw [show (fun x => g x ^ (2 : ℝ)) = fun x => ρ x * Φ x ^ 2 from by
      funext x; rw [Real.rpow_two]; exact congrFun hg2 x]
  refine ⟨by rwa [hfun] at hInt, ?_⟩
  calc (∫ x, ρ x * |Ξ x| * |Φ x| ∂μ)
      = ∫ x, f x * g x ∂μ := by rw [hfun]
    _ ≤ (∫ x, f x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
          * (∫ x, g x ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := hholder
    _ = Real.sqrt (∫ x, ρ x * Ξ x ^ 2 ∂μ) * Real.sqrt (∫ x, ρ x * Φ x ^ 2 ∂μ) := by
        rw [hf2', hg2', Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-! ## Cauchy–Schwarz with an only-a.e.-nonnegative weight -/

lemma csSqrt_ae {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ Ξ Φ : α → ℝ}
    (hρ : 0 ≤ᵐ[μ] ρ) (hΞ : Integrable (fun x => ρ x * Ξ x ^ 2) μ)
    (hΦ : Integrable (fun x => ρ x * Φ x ^ 2) μ) :
    Integrable (fun x => ρ x * |Ξ x| * |Φ x|) μ
      ∧ (∫ x, ρ x * |Ξ x| * |Φ x| ∂μ)
        ≤ Real.sqrt (∫ x, ρ x * Ξ x ^ 2 ∂μ) * Real.sqrt (∫ x, ρ x * Φ x ^ 2 ∂μ) := by
  set ρ' : α → ℝ := fun x => max 0 (ρ x) with hρ'
  have hρ'nn : 0 ≤ ρ' := fun x => le_max_left _ _
  have hae : ρ' =ᵐ[μ] ρ := hρ.mono fun x hx => by
    simp only [hρ', Pi.zero_apply] at *
    exact max_eq_right hx
  have hΞ' : Integrable (fun x => ρ' x * Ξ x ^ 2) μ :=
    hΞ.congr (hae.symm.mul EventuallyEq.rfl)
  have hΦ' : Integrable (fun x => ρ' x * Φ x ^ 2) μ :=
    hΦ.congr (hae.symm.mul EventuallyEq.rfl)
  obtain ⟨hint, hle⟩ := csSqrt hρ'nn hΞ' hΦ'
  have hfun : (fun x => ρ' x * |Ξ x| * |Φ x|) =ᵐ[μ] (fun x => ρ x * |Ξ x| * |Φ x|) :=
    (hae.mul EventuallyEq.rfl).mul EventuallyEq.rfl
  have hfun2 : (fun x => ρ' x * Ξ x ^ 2) =ᵐ[μ] (fun x => ρ x * Ξ x ^ 2) := hae.mul EventuallyEq.rfl
  have hfun3 : (fun x => ρ' x * Φ x ^ 2) =ᵐ[μ] (fun x => ρ x * Φ x ^ 2) := hae.mul EventuallyEq.rfl
  refine ⟨hint.congr hfun, ?_⟩
  rw [integral_congr_ae hfun, integral_congr_ae hfun2, integral_congr_ae hfun3] at hle
  exact hle


/-! ## Pointwise bounds for the two joint integrands -/

lemma log_k_pos (k : ℕ) : 0 < Real.log ((k : ℝ) + 2) := by
  refine Real.log_pos ?_
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

lemma abs_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |cutRho p * χ k p.1 * cutXi G p * cutD2 G p|
      = cutRho p * |χ k p.1| * |cutXi G p| * |cutD2 G p| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (cutRho_nonneg hp)]

lemma abs_cutPsi_le {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |cutRho p * χ k p.1 * cutXi G p * cutD2 G p|
      ≤ cutRho p * |cutXi G p| * |cutD2 G p| := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ p.1 from hp.1) with h0 | hpos
  · have hp0 : p = (0, p.2) := Prod.ext h0.symm rfl
    rw [hp0, cutRho_zero_fst]
    simp
  · have hb := hχ.bnd k p.1 hpos
    have hρnn : (0 : ℝ) ≤ cutRho p := cutRho_nonneg hp
    have hχa : |χ k p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
    rw [abs_cutPsi hχ k hp]
    calc cutRho p * |χ k p.1| * |cutXi G p| * |cutD2 G p|
        = (cutRho p * |cutXi G p| * |cutD2 G p|) * |χ k p.1| := by ring
      _ ≤ (cutRho p * |cutXi G p| * |cutD2 G p|) * 1 :=
          mul_le_mul_of_nonneg_left hχa
            (mul_nonneg (mul_nonneg hρnn (abs_nonneg _)) (abs_nonneg _))
      _ = cutRho p * |cutXi G p| * |cutD2 G p| := by ring

lemma cutPsi_le_abs {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    cutRho p * χ k p.1 * cutXi G p * cutD2 G p
      ≤ cutRho p * |cutXi G p| * |cutD2 G p| :=
  le_trans (le_abs_self _) (abs_cutPsi_le hχ k hp)

lemma abs_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p|
      = |p.1 * deriv (χ k) p.1| * cutRho p * |cutPs G p| * |cutD2 G p| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (cutRho_nonneg hp)]

lemma abs_cutPsiB_le {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    |(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p|
      ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) := by
  have hKL : 0 ≤ K / Real.log ((k : ℝ) + 2) := div_nonneg hχ.K0 (log_k_pos k).le
  have hle : |p.1 * deriv (χ k) p.1| ≤ K / Real.log ((k : ℝ) + 2) := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ p.1 from hp.1) with h0 | hpos
    · rw [← h0, zero_mul, abs_zero]; exact hKL
    · exact hχ.d1 k p.1 hpos
  have hρnn : (0 : ℝ) ≤ cutRho p := cutRho_nonneg hp
  have hPx : (0 : ℝ) ≤ |cutPs G p| := abs_nonneg _
  have hDx : (0 : ℝ) ≤ |cutD2 G p| := abs_nonneg _
  rw [abs_cutPsiB hχ k hp]
  calc |p.1 * deriv (χ k) p.1| * cutRho p * |cutPs G p| * |cutD2 G p|
      = |p.1 * deriv (χ k) p.1| * (cutRho p * |cutPs G p| * |cutD2 G p|) := by ring
    _ ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg (mul_nonneg hρnn hPx) hDx)

lemma cutPsiB_le {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {G : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p ∈ Izθ) :
    (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p
      ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) :=
  le_trans (le_abs_self _) (abs_cutPsiB_le hχ k hp)

lemma amgm_le {a b ρ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : 0 ≤ ρ) :
    ρ * a * b ≤ (1 / 2) * (ρ * a ^ 2 + ρ * b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-! ## Integrability of the two joint integrands -/

lemma integrable_cutPsi {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hXi : Integrable (fun p : ℝ × ℝ => cutRho p * cutXi G p ^ 2) Mu)
    (hT : Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu) :
    Integrable (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p) Mu := by
  refine Integrable.mono' ((hXi.add hT).const_mul (1 / 2)) (aesm_cutPsi hχ k hG) ?_
  refine ae_of_mem_Izθ (fun p hp => ?_)
  show ‖cutRho p * χ k p.1 * cutXi G p * cutD2 G p‖
      ≤ 1 / 2 * (cutRho p * cutXi G p ^ 2 + cutRho p * cutD2 G p ^ 2)
  have h1 : ‖cutRho p * χ k p.1 * cutXi G p * cutD2 G p‖
      ≤ cutRho p * |cutXi G p| * |cutD2 G p| :=
    le_trans (le_of_eq (Real.norm_eq_abs _)) (abs_cutPsi_le hχ k hp)
  have hsq1 : |cutXi G p| ^ 2 = cutXi G p ^ 2 := sq_abs _
  have hsq2 : |cutD2 G p| ^ 2 = cutD2 G p ^ 2 := sq_abs _
  have h2 : cutRho p * |cutXi G p| * |cutD2 G p|
      ≤ (1 / 2) * (cutRho p * cutXi G p ^ 2 + cutRho p * cutD2 G p ^ 2) := by
    have h := amgm_le (a := |cutXi G p|) (b := |cutD2 G p|) (ρ := cutRho p)
      (abs_nonneg _) (abs_nonneg _) (cutRho_nonneg hp)
    rwa [hsq1, hsq2] at h
  linarith

lemma integrable_cutPsiB {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hD : Integrable (fun p : ℝ × ℝ => cutRho p * cutPs G p ^ 2) Mu)
    (hT : Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu) :
    Integrable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) Mu := by
  have hKL : 0 ≤ K / Real.log ((k : ℝ) + 2) := div_nonneg hχ.K0 (log_k_pos k).le
  refine Integrable.mono'
    (((hD.add hT).const_mul (1 / 2)).const_mul (K / Real.log ((k : ℝ) + 2)))
    (aesm_cutPsiB hχ k hG) ?_
  refine ae_of_mem_Izθ (fun p hp => ?_)
  show ‖(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p‖
      ≤ K / Real.log ((k : ℝ) + 2)
        * (1 / 2 * (cutRho p * cutPs G p ^ 2 + cutRho p * cutD2 G p ^ 2))
  have h3 : ‖(p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p‖
      ≤ (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|) :=
    le_trans (le_of_eq (Real.norm_eq_abs _)) (abs_cutPsiB_le hχ k hp)
  have hsq1 : |cutPs G p| ^ 2 = cutPs G p ^ 2 := sq_abs _
  have hsq2 : |cutD2 G p| ^ 2 = cutD2 G p ^ 2 := sq_abs _
  have h2 : (K / Real.log ((k : ℝ) + 2)) * (cutRho p * |cutPs G p| * |cutD2 G p|)
      ≤ (K / Real.log ((k : ℝ) + 2))
        * (1 / 2 * (cutRho p * cutPs G p ^ 2 + cutRho p * cutD2 G p ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hKL
    have h := amgm_le (a := |cutPs G p|) (b := |cutD2 G p|) (ρ := cutRho p)
      (abs_nonneg _) (abs_nonneg _) (cutRho_nonneg hp)
    rwa [hsq1, hsq2] at h
  linarith

end CutBk
end Work.FTS.EllSol.PkgK5.TraceEngine
