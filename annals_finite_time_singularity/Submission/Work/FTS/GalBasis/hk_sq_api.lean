import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.Apriori.RegQApi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

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
  refine Work.FTS.EllipticEst.HkMem_of_majorant_ae α l
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

/-- **`RegQ` is closed under addition.** -/
theorem regQ_add {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : RegQ α k f) (hg : RegQ α k g) : RegQ α k (fun z θ => f z θ + g z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_add hf.1 hg.1,
    Work.FTS.EllipticEst.HkMem_add_open (smoothOpen_of_smoothQuad hf.1)
      (smoothOpen_of_smoothQuad hg.1) hf.2.1 hg.2.1,
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

end Work.FTS.Apriori
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Repair.DzShift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Repair

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools -/

/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots: for `f` of class `C^∞` on the open quadrant and `(z,θ)` in the open
quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Work.FTS.EllipticEst.remov.Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.remov.Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.remov.Step.DzIter_congr_of_isOpen Work.FTS.EllipticEst.remov.Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Work.FTS.EllipticEst.remov.Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The pointwise `D_z`-shift bound on the open quadrant.**  Every slot of
`HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the commutation of `D_z`
with `D_θ^i`), and each single slot is dominated by the whole integrand; counting `k` radial and
`k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Work.FTS.EllipticEst.remov.Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2 := by
      unfold Work.FTS.EllipticEst.remov.Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Work.FTS.EllipticEst.remov.Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Zsum k f z θ + Work.FTS.EllipticEst.remov.Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine Work.FTS.EllipticEst.HkMem_of_majorant_ae α (k - 1) (f := Work.Spaces.Dz f)
    (M := fun z θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
    ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllipticEst.SmoothOpen.Dz hf).continuousOn_HkIntegrand α (k - 1)
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · show MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [MeasureTheory.integral_const_mul] using hmem.2.const_mul _
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · subst h0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst α (k - 1) (Work.Spaces.Dz f) θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ =>
        HkIntegrand_Dz_shift_le α hk f hz0 hθ hf

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice. -/
theorem pz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp
      (Work.FTS.EllipticEst.SmoothOpen.pth hΨ) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp => by
        obtain ⟨z', θ'⟩ := p
        exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.** -/
theorem Dz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) := by
  have hplain := pz_pthIter_two_comm hΨ
  have hmul : Work.Spaces.pth (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ
    rw [deriv_const_mul_field]
  have hstep : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
        = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) := by
      rw [← hmul]
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    rw [h2]
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
    rw [deriv_const_mul_field]
  intro z θ hz hθ hlt
  show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z θ
  rw [hstep, hplain z θ hz hθ hlt]

/-! ## The shift -/

/-- **The assembly of the shift, given the two moment conditions.**  All nine fields of
`EllWeakPos α (k-1) (D_z F) (D_z Ψ)` are produced here except the two moment conditions, which
are supplied as explicit hypotheses. -/
theorem EllWeakPos_DzIter_one_shift_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k)
    {F Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · exact hmomF
  · exact hmomΨ
  · intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.SmoothOpen.zsq_mul (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.memA
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- the tenth field: the diagonal honesty `z ∂_z∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hGs : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :=
      HkMem_Dz_shift hk hGs h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)))
        (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rintro ⟨z', θ'⟩ ⟨hz', hθ'⟩
      exact Dz_pthIter_two_comm hSΨ z' θ' hz' hθ'.1 hθ'.2
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        hEqOn.symm ⟨hz, hθ⟩
    rw [hpe]
    rfl

/-- **The shift, for `2 ≤ k`** — the instance needed by the induction step of `prop:Hk` (the
shifted data are consumed at level `k-1 ≥ 2`) and by the level-`2` assembly.  Both moment
conditions are available from proved lemmas: the `F`-half from `Fstar_DzIter_one_F_ge_two`
(which needs `k ≥ 2`) and the `Ψ`-half from `Mine.FstarDzOnePsi`. -/
theorem EllWeakPos_DzIter_one_shift_of_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {F Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments (by omega) h
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two hk h)
    (Work.FTS.EllipticEst.Mine.FstarDzOnePsi α (by omega) F Ψ h)

end Work.FTS.EllipticEst.Cores.Repair
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.HkMem_sub_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **`ℋ^k` is closed under differences** for data which are `C^∞` on the open quadrant.

The point is that `f - g = f + (-1)·g` pointwise, and the right-hand side is `ℋ^k` because
scalar multiples of `SmoothOpen` functions are `SmoothOpen` (`SmoothOpen.const_mul'`), `ℋ^k`
is closed under scalar multiples (`Work.FTS.LocData.HkMem_const_mul`) and under sums
(`HkMem_add_open`). -/
theorem HkMem_sub_open {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hneg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-1 : ℝ) * g z θ) :=
    SmoothOpen.const_mul' (-1) hg
  have hmneg : Work.Spaces.HkMem α k (fun z θ => (-1 : ℝ) * g z θ) :=
    Work.FTS.LocData.HkMem_const_mul α k (-1) hmg
  have hadd : Work.Spaces.HkMem α k (fun z θ => f z θ + (-1 : ℝ) * g z θ) :=
    HkMem_add_open hf hneg hmf hmneg
  have hfun : (fun z θ => f z θ + (-1 : ℝ) * g z θ) = fun z θ => f z θ - g z θ := by
    funext z θ
    ring
  rwa [hfun] at hadd

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.GalBasis.hk_sq_api =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## Pointwise helpers -/

/-- Scalar homogeneity of the `ℋ^k`-integrand, pointwise and with no regularity hypothesis. -/
theorem hkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : Fn) :
    ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
  fun z θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ

/-- The `ℋ^k`-integrand of the *(Pi-)negation* of `g` is that of `g`: the operators
`D_z^i`, `D_z^j D_θ^i` commute with `-` (totally, `deriv (-f) = -deriv f` for every `f`),
so this holds for the negated function as well. -/
theorem hkIntegrand_neg_fun (α : ℝ) (k : ℕ) (g : Fn) :
    Work.Spaces.HkIntegrand α k (fun z θ => -g z θ) = Work.Spaces.HkIntegrand α k g :=
  Work.FTS.EllipticEst.HkIntegrand_neg α k g

/-- `HkMem` is closed under negation, with no regularity and no positivity hypothesis
(the integrand of `-g` is *equal* to that of `g`). -/
theorem hkMem_neg_open (α : ℝ) (k : ℕ) {g : Fn} (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => -g z θ) := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α k (fun z θ => -g z θ) z θ
      = Work.Spaces.HkIntegrand α k g z θ :=
    fun z θ => congrFun (congrFun (hkIntegrand_neg_fun α k g) z) θ
  constructor
  · intro z hz
    exact (hmg.1 z hz).congr_fun (fun θ _ => (hpt z θ).symm) measurableSet_Icc
  · refine hmg.2.congr_fun (fun z _ => ?_) measurableSet_Ici
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => (hpt z θ).symm)

/-- `SmoothOpen` is closed under negation. -/
theorem smoothOpen_neg {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -g z θ) := by
  have hfun : Function.uncurry (fun z θ => -g z θ) = -(Function.uncurry g) := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact hg.neg

/-- **`HkMem` is closed under subtraction** for `C^∞`-on-the-open-quadrant data, with no
positivity hypothesis on `α`: write `f - g = f + (-g)` and use `HkMem_add_open` together with
the negation case above. -/
theorem hkMem_sub_open (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hfun : (fun z θ => f z θ - g z θ) = (fun z θ => f z θ + -g z θ) := by
    funext z θ; ring
  rw [hfun]
  exact Work.FTS.EllipticEst.HkMem_add_open hf (smoothOpen_neg hg) hmf
    (hkMem_neg_open α k hmg)

/-! ## The API lemma -/


end Work.FTS.GalBasis
end
end
