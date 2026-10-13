/-
# The interior class `RegQ` : basic API

`Work.FTS.Nonlin.RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f` is the class in which
the whole a-priori chapter is stated (`Submission/Work/FTS/Vocab.lean`, design §3.1 of
`FTS/N45_DESIGN_LEAD.md`).  This module provides the closure properties every caller needs:

* `regQ_mono` — `RegQ α k f → l ≤ k → RegQ α l f`;
* `regQ_smul` — closure under multiplication by a constant;
* `regQ_add` — closure under addition,
* and the derived `regQ_zero`, `regQ_neg`, `regQ_sub`, `regQ_finset_sum`.

The two ingredients are that `HkMem` descends along `l ≤ k` because `HkIntegrand` is a sum of
squares monotonically growing in `k` (`Work.Spaces.HkIntegrand_mono`), the descent being certified
through the *open-quadrant* measurability route `Work.FTS.EllipticEst.HkMem_of_majorant_ae` (the
closed-quadrant `SmoothNbhd`-based `HkMem_mono` is inapplicable: `SmoothNbhd` is analyticity), and
that `BdryTraces` is closed under `+` and `·c` because the mixed operators are additive on the open
quadrant (`mixed_add_quad`) and scalar homogeneous everywhere (`mixed_const_mul`), so that the
boundary limits obey the squeeze theorem with the weights `z` and `sin(2θ)^{1-γ} ≥ 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.AprioriOpen

open Work.FTS.Nonlin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Scalar homogeneity of the iterated operators (unconditional)

`deriv (c · u) = c · deriv u` holds with no differentiability hypothesis (both sides vanish when
`u` is not differentiable at the point and `c ≠ 0`; the claim is trivial for `c = 0`). -/

private theorem deriv_const_mul' (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul']

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul']

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, Dz_const_mul]

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- **The mixed operators are scalar homogeneous** (unconditionally). -/
theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## Additivity of the iterated operators on the open quadrant (`SmoothQuad` data) -/

private lemma DzIter_congr_quad {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, -1 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j F z θ = Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n F z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq]

private lemma DthIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ := by
  induction i with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => a z θ + b z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n a z θ') θ :=
        ha.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        hb.differentiableAt_slice_DthIter n hz ⟨h1, h2⟩
      have hd : deriv (fun θ' => Work.Spaces.DthIter n a z θ' + Work.Spaces.DthIter n b z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n a z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n b z θ') θ :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

private lemma DzIter_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.DzIter j a z θ + Work.Spaces.DzIter j b z θ := by
  induction j with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => a z θ + b z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n a z' θ) z :=
        ha.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        hb.differentiableAt_slice_DzIter n hz ⟨h1, h2⟩
      have hd : deriv (fun z' => Work.Spaces.DzIter n a z' θ + Work.Spaces.DzIter n b z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n a z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n b z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- **The mixed operators `D_z^jD_θ^i` are additive on the open quadrant** for `SmoothQuad` data. -/
theorem mixed_add_quad {a b : ℝ → ℝ → ℝ} (ha : Work.FTS.LocData.SmoothQuad a)
    (hb : Work.FTS.LocData.SmoothQuad b) (j i : ℕ) :
    ∀ z θ, -1 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => a z θ + b z θ) z θ
        = Work.Spaces.mixed j i a z θ + Work.Spaces.mixed j i b z θ := by
  intro z θ hz h1 h2
  have hcongr := DzIter_congr_quad (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => a z θ + b z θ))
    (G := fun z θ => Work.Spaces.DthIter i a z θ + Work.Spaces.DthIter i b z θ)
    (fun z θ hz h1 h2 => DthIter_add_quad ha hb i z θ hz h1 h2) z θ hz h1 h2
  have hadd := DzIter_add_quad (ha.DthIter i) (hb.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-- **Membership in `ℋ^k` by an almost-everywhere majorant.**  The closed-quadrant version
`Work.FTS.LocData.HkMem_of_majorant` requires the domination at every point of
`[0,∞) × [0,π/2]`; here it is only required for almost every interior angle, which is what
the additivity of the `D`-operators on the open quadrant delivers. -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {f M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      Work.Spaces.HkIntegrand α k f z θ ≤ M z θ) :
    Work.Spaces.HkMem α k f := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) := MeasureTheory.Ioo_ae_eq_Icc
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ := by
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k f θ).symm
    · refine MeasureTheory.IntegrableOn.congr_set_ae ?_ hIoo.symm
      have hMioo : IntegrableOn (fun θ => M z θ) (Set.Ioo 0 (π / 2)) :=
        (hMslice z hz).congr_set_ae hIoo
      have hsl : ContinuousOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.continuousOn_slice_theta (G := Work.Spaces.HkIntegrand α k f) hcont hz0
      refine MeasureTheory.Integrable.mono' hMioo
        (hsl.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
      exact hθ
  have houter : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := by
    have hKnn : ∀ z ∈ Work.Spaces.Iz,
        0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
    have hKle : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      intro z hz
      have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) := by
        show Set.Icc (0 : ℝ) (π / 2) =ᵐ[volume] Set.Ioo 0 (π / 2)
        exact hIoo.symm
      rw [MeasureTheory.setIntegral_congr_set hIθ,
        MeasureTheory.setIntegral_congr_set hIθ]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
        ((hMslice z hz).congr_set_ae hIoo) ?_
      filter_upwards [hle z hz] with θ hθ
      exact hθ
    refine MeasureTheory.Integrable.mono' hMz ?_ ?_
    · have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h1 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict (Set.Ioi 0)) :=
        hprod.integral_prod_right'
      have h2 : AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (π / 2),
          Work.Spaces.HkIntegrand α k f z θ) (volume.restrict Work.Spaces.Iz) := by
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (π / 2), Work.Spaces.HkIntegrand α k f z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set hIoo
      rw [← hfun]
      exact h2
    · have hbnd : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
          ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
            ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
        exact Filter.Eventually.of_forall fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hKnn z hz)]
          exact hKle z hz
      exact hbnd
  exact ⟨hslice, houter⟩

/-! ## `RegQ` is monotone in the order -/

private theorem HkIntegrand_mono_le_aux (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    ∀ d : ℕ,
      Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α (l + d) f z θ := by
  intro d
  induction d with
  | zero => simp
  | succ n ih =>
      have h2 : Work.Spaces.HkIntegrand α (l + n) f z θ
          ≤ Work.Spaces.HkIntegrand α (l + n + 1) f z θ :=
        Work.Spaces.HkIntegrand_mono α (l + n) f z θ
      have heq : l + n + 1 = l + (n + 1) := by omega
      rw [heq] at h2
      exact le_trans ih h2

private theorem HkIntegrand_mono_le (α : ℝ) {l k : ℕ} (hkl : l ≤ k) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α l f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  have h := HkIntegrand_mono_le_aux α l f z θ (k - l)
  rwa [Nat.add_sub_of_le hkl] at h

private theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) : Work.FTS.EllipticEst.SmoothOpen f := by
  refine hf.mono ?_
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp1]), hp2⟩

/-- **`RegQ` descends in the order**: `RegQ α k f → l ≤ k → RegQ α l f`. -/
theorem regQ_mono {α : ℝ} {k l : ℕ} {f : ℝ → ℝ → ℝ} (hkl : l ≤ k)
    (hf : RegQ α k f) : RegQ α l f := by
  obtain ⟨hsm, hmem, htr⟩ := hf
  refine ⟨hsm, ?_, fun a b hab => htr a b (le_trans hab hkl)⟩
  refine HkMem_of_majorant_ae α l
    (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand (smoothOpen_of_smoothQuad hsm) α l)
    hmem.1 hmem.2 ?_
  intro z _
  exact Eventually.of_forall fun θ => HkIntegrand_mono_le α hkl f z θ

/-! ## `RegQ` is closed under multiplication by a constant -/

private theorem bdryTraces_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (htr : BdryTraces α k f) : BdryTraces α k (fun z θ => c * f z θ) := by
  intro a b hab
  have hfab := htr a b hab
  have hfun : ∀ z θ, Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed b a f z θ := by
    intro z θ
    rw [mixed_const_mul]
  have hz : ∀ θ, (fun z => z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ
        * Work.Spaces.w z) ^ 2)
      = fun z => c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2) := by
    intro θ
    funext z
    show z * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ * Work.Spaces.w z) ^ 2
      = c ^ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
    rw [hfun z θ]; ring
  have ht : ∀ z, (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2)
      = fun θ => c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    intro z
    funext θ
    show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
      * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2
      = c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2)
    rw [hfun z θ]; ring
  constructor
  · intro θ hθ
    have h := hfab.1 θ hθ
    constructor
    · rw [hz θ]
      simpa using h.1.const_mul (c ^ 2)
    · rw [hz θ]
      simpa using h.2.const_mul (c ^ 2)
  · intro z hzmem
    have h := hfab.2 z hzmem
    constructor
    · rw [ht z]
      simpa using h.1.const_mul (c ^ 2)
    · rw [ht z]
      simpa using h.2.const_mul (c ^ 2)

/-- **`RegQ` is closed under multiplication by a constant.** -/
theorem regQ_smul {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) : RegQ α k (fun z θ => c * f z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_const_mul c hf.1,
    Work.FTS.LocData.HkMem_const_mul α k c hf.2.1, bdryTraces_smul c hf.2.2⟩

/-! ## `RegQ` is closed under addition -/

/-- Additivity of `BdryTraces`: by `mixed_add_quad` the boundary limits of the sum are those of
the sum of the limits, and `z ≥ 0` resp. `sin(2θ)^{1-γ} ≥ 0` let the squeeze theorem conclude. -/
theorem bdryTraces_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (htf : BdryTraces α k f) (htg : BdryTraces α k g) :
    BdryTraces α k (fun z θ => f z θ + g z θ) := by
  intro a b hab
  have hfab := htf a b hab
  have hgab := htg a b hab
  have hpt : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ :=
    fun z θ hz h1 h2 => mixed_add_quad hsmf hsmg b a z θ (by linarith) h1 h2
  -- the algebraic comparison of the weighted squares (open quadrant, hence nonnegative weights)
  have hwsq : ∀ z θ, (Work.Spaces.w z
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ)) ^ 2
      ≤ 2 * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2
        + 2 * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2 := by
    intro z θ
    nlinarith [sq_nonneg (Work.Spaces.w z * Work.Spaces.mixed b a f z θ
        - Work.Spaces.w z * Work.Spaces.mixed b a g z θ)]
  have hssq : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) → (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f z θ + Work.Spaces.mixed b a g z θ) ^ 2
      ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2)
        + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2) := by
    intro z θ hθ
    have h1 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _
    nlinarith [sq_nonneg (Work.Spaces.mixed b a f z θ - Work.Spaces.mixed b a g z θ), h1]
  constructor
  · intro θ hθ
    have hA := hfab.1 θ hθ
    have hB := hgab.1 θ hθ
    have hlim : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimT : Tendsto (fun z => 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)) atTop (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hsq : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt (Set.mem_Ioi.mp hzmem)) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ (Set.mem_Ioi.mp hzmem) hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt (Set.mem_Ioi.mp hzmem)]
    have hsqT : Tendsto (fun z => z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ
          * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimT ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show 0 ≤ z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (le_of_lt hzmem) (sq_nonneg _)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hzmem
        show z * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ * Work.Spaces.w z) ^ 2
          ≤ 2 * (z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
            + 2 * (z * (Work.Spaces.mixed b a g z θ * Work.Spaces.w z) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        nlinarith [hwsq z θ, le_of_lt hzmem]
    exact ⟨hsq, hsqT⟩
  · intro z hzmem
    have hA := hfab.2 z hzmem
    have hB := hgab.2 z hzmem
    have hlim : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hA.1.const_mul 2).add (hB.1.const_mul 2)
    have hlimL : Tendsto (fun θ => 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2) + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a g z θ) ^ 2)) (𝓝[<] (π / 2)) (𝓝 0) := by
      simpa using (hA.2.const_mul 2).add (hB.2.const_mul 2)
    have hmemGT : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith [Real.pi_pos])
    have hmemLT : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) := Ioo_mem_nhdsLT (by linarith [Real.pi_pos])
    have hsq : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [hmemGT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemGT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    have hsqL : Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2)
        (𝓝[<] (π / 2)) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimL ?_ ?_
      · filter_upwards [hmemLT] with θ hθ
        show 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _) (sq_nonneg _)
      · filter_upwards [hmemLT] with θ hθ
        show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (fun z θ => f z θ + g z θ) z θ) ^ 2
          ≤ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a f z θ) ^ 2)
            + 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a g z θ) ^ 2)
        rw [hpt z θ hzmem hθ.1 hθ.2]
        exact hssq z θ hθ
    exact ⟨hsq, hsqL⟩

/-- **`ℋ^k` is closed under addition** for data which are `C^∞` on the open quadrant (the
open-quadrant copy of `Work.FTS.EllipticEst.HkMem_add_open`, proved with the additivity lemmas of
this file). -/
theorem HkMem_add_quad {α : ℝ} (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  refine HkMem_of_majorant_ae (α := α) (k := k) (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (Work.FTS.EllipticEst.smoothOpen_add (smoothOpen_of_smoothQuad hf)
        (smoothOpen_of_smoothQuad hg)) α k) ?_ ?_ ?_
  · intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · have h1 : MeasureTheory.IntegrableOn
        (fun z => 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        Work.Spaces.Iz := hmf.2.const_mul 2
    have h2 : MeasureTheory.IntegrableOn
        (fun z => 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        Work.Spaces.Iz := hmg.2.const_mul 2
    refine (h1.add h2).congr_fun ?_ measurableSet_Ici
    intro z hz
    change 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      = ∫ θ in Work.Spaces.Iθ, 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst α k (fun z θ => f z θ + g z θ) θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k f θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k g θ]
        norm_num
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun θ hθ => ?_
      have hzm : -1 < z := by linarith
      have hθ1 : 0 < θ := hθ.1
      have hθ2 : θ < π / 2 := hθ.2
      have hRad : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ)
            z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 2 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + 2 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [DzIter_add_quad hf hg i z θ hzm hθ1 hθ2]
        nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            - Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
      have hMix : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ)
              z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
            + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with hij
        · rw [mixed_add_quad hf hg j i z θ hzm hθ1 hθ2]
          nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
              - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
        · norm_num
      rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
      rw [mul_add, mul_add]
      linarith [hRad, hMix]

/-- **`RegQ` is closed under addition.** -/
theorem regQ_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_add hf.1 hg.1,
    HkMem_add_quad k hf.1 hg.1 hf.2.1 hg.2.1,
    bdryTraces_add hf.1 hg.1 hf.2.2 hg.2.2⟩

/-! ## Derived closure properties -/

/-- `RegQ` contains the zero profile. -/
theorem regQ_zero (α : ℝ) (k : ℕ) : RegQ α k (fun _ _ : ℝ => (0 : ℝ)) := by
  have hsm : Work.FTS.LocData.SmoothQuad (fun _ _ : ℝ => (0 : ℝ)) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ × ℝ => (0 : ℝ)) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
    exact contDiffOn_const
  refine ⟨hsm, Work.FTS.EllipticEst.HkMem_zero α k, ?_⟩
  intro a b _
  have hmix : Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ : ℝ => (0 : ℝ) := by
    have h := mixed_const_mul (0 : ℝ) (fun _ _ : ℝ => (1 : ℝ)) b a
    simpa using h
  have hmix_pt : ∀ z θ : ℝ, Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 :=
    fun z θ => congrFun (congrFun hmix z) θ
  constructor
  · intro θ _
    have hz : (fun z => z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ
        * Work.Spaces.w z) ^ 2) = fun _ => (0 : ℝ) := by
      funext z
      show z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ * Work.Spaces.w z) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [hz]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  · intro z _
    have ht : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2) = fun _ => (0 : ℝ) := by
      funext θ
      show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2 = 0
      rw [hmix_pt z θ]; ring
    rw [ht]
    exact ⟨tendsto_const_nhds, tendsto_const_nhds⟩

/-- `RegQ` is closed under negation. -/
theorem regQ_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hf : RegQ α k f) :
    RegQ α k (fun z θ => -f z θ) := by
  have h := regQ_smul (α := α) (k := k) (-1) hf
  simpa using h

/-- `RegQ` is closed under subtraction. -/
theorem regQ_sub {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ - g z θ) := by
  have h := regQ_add hf (regQ_neg hg)
  simpa [sub_eq_add_neg] using h

/-- `RegQ` is closed under finite linear combinations. -/
theorem regQ_finset_sum {α : ℝ} {k : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℝ)
    (F : ι → ℝ → ℝ → ℝ) (hF : ∀ i ∈ s, RegQ α k (F i)) :
    RegQ α k (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (fun z θ => ∑ i ∈ (∅ : Finset ι), c i * F i z θ) = fun _ _ : ℝ => (0 : ℝ) := by
        funext z θ; simp
      rw [h0]
      exact regQ_zero α k
  | insert a s' ha ih =>
      have hsum : (fun z θ => ∑ i ∈ insert a s', c i * F i z θ)
          = (fun z θ => c a * F a z θ) + (fun z θ => ∑ i ∈ s', c i * F i z θ) := by
        funext z θ
        rw [Finset.sum_insert ha]; rfl
      rw [hsum]
      refine regQ_add (regQ_smul (c a) (hF a (Finset.mem_insert_self a s')))
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

end Work.FTS.OpenPkg.AprioriOpen
