import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.Dchan_dzero_word_split_v2
import Submission.Work.BoseBoxFock.PCFU.W1fun_chat_small
import Submission.Work.PCFU.chDW1sum_summable
import Submission.Work.PCFU.chDpoisson_E
import Submission.Work.PCFU.chDpoisson_uvSmear
import Submission.Work.PCFU.conv_le_of_rapidDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.PCFU.chD_split` — the pointwise decomposition of the `(D)`-slot kernel

The `(D)`-channel kernel `F = KχfrU − chDC` splits into the truncation piece and the alias piece:

    KχfrU v h μ fu N z − chDC h ℓ z
      = Σ'_d (χ_ℓ ⋆ chDkerE)(z + ℓ•d)  +  Σ'_{d ≠ 0} (χ_ℓ ⋆ W1fun)(z + ℓ•d) ,    ℓ = ellH v μ .

`chDC h ℓ z = ∫_y χ_ℓ(y)·W₁(y − z) dy` is the value at `z` of the `χ_ℓ`-convolution of the (even)
kernel `W₁ = W1fun v h ℓ` — this is the only place where the *radiality* hypothesis `hvrad` (via the
evenness of `W1fun`) enters.  Adding and subtracting `W1fun` inside the Poisson identity
`chDpoisson_uvSmear` (`KχfrU z = Σ'_d (χ_ℓ ⋆ uvSmear(W₁))(z + ℓ•d)`) and cancelling the `d = 0`
term gives the claim.

The two `d`-families are summable: the `W1fun` family because `W1fun` is supported in `ball 0 R`
and `2R ≤ ℓ` makes it finitely supported (`Work.PCFU.chDW1sum_summable`), the `uvSmear` family
because `chDconv` of the rapidly decreasing `uvSmear` inherits that decay
(`Work.PCFU.conv_le_of_rapidDecay` + `Work.BoseBoxFock.summable_shift_latVec`).
-/

/-- `latVec 0 = 0`. -/
private lemma latVec_zero : Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = 0 := by
  refine PiLp.ext fun i => ?_
  simp [Work.BoseBoxFock.latVec]

/-- The integrand `χ_ℓ(·)·f(u − ·)` is integrable for every integrable real kernel `f`. -/
private lemma integrable_chiLam_mul {ℓ : ℝ} {f : E3 → ℝ} (hf : Integrable f) (u : E3) :
    Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((f (u - w) : ℝ) : ℂ)) := by
  have hg : Integrable (fun w : E3 => ((f (u - w) : ℝ) : ℂ)) := (hf.comp_sub_left u).ofReal
  refine Integrable.bdd_mul
    (f := fun w : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ))
    (c := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) hg ?_ ?_
  · exact (Complex.continuous_ofReal.comp
      (Work.BoseBoxFock.PCFU.chiLam_continuous ℓ)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.BoseBoxFock.PCFU.chiLam_abs_le ℓ w

/-- The integrand `χ_ℓ(·)·f(u − ·)` is integrable for every continuous, bounded real kernel `f`:
`χ_ℓ` is in `L¹`. -/
private lemma integrable_chiLam_mul_of_bounded {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℝ} {C : ℝ}
    (hf : Continuous f) (hfC : ∀ x : E3, |f x| ≤ C) (u : E3) :
    Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((f (u - w) : ℝ) : ℂ)) := by
  have hχint : Integrable (fun w : E3 => Work.BoseK15.corpusBox.chiLam ℓ w) :=
    (Work.BoseBoxFock.PCFU.chiLam_continuous ℓ).integrable_of_hasCompactSupport
      (Work.BoseBoxFock.chiLam_hasCompactSupport_tauPhi hℓ)
  refine Integrable.mul_bdd (g := fun w : E3 => ((f (u - w) : ℝ) : ℂ)) (c := C)
    hχint.ofReal ?_ ?_
  · exact (Complex.continuous_ofReal.comp
      (hf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hfC (u - w)

/-- Additivity of `chDconv` on real kernels. -/
private lemma chDconv_ofReal_add {ℓ : ℝ} {f g : E3 → ℝ} (u : E3)
    (hf : Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((f (u - w) : ℝ) : ℂ)))
    (hg : Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((g (u - w) : ℝ) : ℂ))) :
    Work.BoseBoxFock.PCFU.chDconv ℓ (fun x => (((f + g) x : ℝ) : ℂ)) u
      = Work.BoseBoxFock.PCFU.chDconv ℓ (fun x => ((f x : ℝ) : ℂ)) u
        + Work.BoseBoxFock.PCFU.chDconv ℓ (fun x => ((g x : ℝ) : ℂ)) u := by
  simp only [Work.BoseBoxFock.PCFU.chDconv]
  rw [← MeasureTheory.integral_add hf hg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Pi.add_apply]
  push_cast
  ring

/-- **Summability of the `χ_ℓ ⋆ uvSmear` family over the lattice**: `uvSmear` is rapidly
decreasing, so `chDconv` of it is rapidly decreasing and the lattice sum converges. -/
private lemma summable_chDconv_kerS {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N)
    (hWint : Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hWcs : HasCompactSupport (Work.BoseFixR.W1fun v h ℓ)) (z : E3) :
    Summable (fun d : Fin 3 → ℤ => Work.BoseBoxFock.PCFU.chDconv ℓ
      (Work.BoseBoxFock.PCFU.chDkerS (h := h) fu ℓ N)
      (z + ℓ • Work.BoseBoxFock.latVec d)) := by
  have hΛ : 0 < Work.BoseBoxFock.uvRad ℓ N := by
    rw [Work.BoseBoxFock.uvRad]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hScont : Continuous (Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N)
      (Work.BoseFixR.W1fun v h ℓ)) :=
    Work.BoseBoxFock.uvSmear_continuous fu hΛ hWint
  have hSmeas : AEStronglyMeasurable (fun x : E3 =>
      ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N)
        (Work.BoseFixR.W1fun v h ℓ) x : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hScont).aestronglyMeasurable
  have hSdec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3,
      ‖((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N)
        (Work.BoseFixR.W1fun v h ℓ) x : ℝ) : ℂ)‖ ≤ C * (1 + ‖x‖) ^ (-(n : ℤ)) := by
    intro n
    obtain ⟨C, hC0, hC⟩ := Work.BoseBoxFock.uvSmear_rapidDecay fu hΛ hWint hWcs n
    exact ⟨C, hC0, fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hC x⟩
  obtain ⟨C, hC0, hC⟩ := conv_le_of_rapidDecay
    (Work.BoseBoxFock.PCFU.chiLam_continuous ℓ)
    (Work.BoseBoxFock.chiLam_hasCompactSupport_tauPhi hℓ) hSmeas hSdec 4
  refine Work.BoseBoxFock.summable_shift_latVec hC0 ?_ hℓ z
  intro q
  simpa only [Work.BoseBoxFock.PCFU.chDconv, Work.BoseBoxFock.PCFU.chDkerS,
    Nat.cast_ofNat] using hC q

theorem chD_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) {N : ℕ} (hN : 1 ≤ N)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
        - Work.BoseBoxFock.PCFU.chDC h (Work.BoseBoxFock.ellH v μ) z
      = (∑' d : Fin 3 → ℤ, Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
            (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu
              (Work.BoseBoxFock.ellH v μ) N u : ℝ) : ℂ))
            (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d))
        + (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
            Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
              (fun u => ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ))
              (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d))) := by
  classical
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  have hℓE : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact hℓE
  -- positivity of the box side at the diluteness parameters
  have hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := by
    simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
      Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  -- `W₁`-facts in the spelling of `chDpoisson_uvSmear`
  have hWintE : Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) :=
    Work.BoseBoxFock.PCFU.W1fun_integrable hR hℓE hv_supp hRℓ
  have hWcsE : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) := by
    show IsCompact (tsupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    refine (isCompact_closedBall (0 : E3) R).of_isClosed_subset isClosed_closure ?_
    exact subset_trans (Work.BoseFixR.tsupport_W1fun_subset h hv_supp _)
      Metric.ball_subset_closedBall
  have hevE : ∀ x, Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x :=
    Work.BoseFixR.isEven_W1fun h hvrad _
  -- the same facts at `ℓ`
  have hWint : Integrable (Work.BoseFixR.W1fun v h ℓ) := by rw [hℓdef]; exact hWintE
  have hWcs : HasCompactSupport (Work.BoseFixR.W1fun v h ℓ) := by rw [hℓdef]; exact hWcsE
  have hev : ∀ x, Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x := by
    intro x; rw [hℓdef]; exact hevE x
  -- the Poisson identity
  have huv := chDpoisson_uvSmear (v := v) (h := h) (μ := μ) (fu := fu) (N := N)
    hℓ0 hN hWintE hWcsE hevE z
  simp only [← hℓdef] at huv
  -- `chDC` is the `χ_ℓ`-convolution of `W₁` (evenness of `W₁`)
  have hDC : Work.BoseBoxFock.PCFU.chDC h ℓ z
      = Work.BoseBoxFock.PCFU.chDconv ℓ
          (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ)) z := by
    rw [Work.BoseBoxFock.PCFU.chDC, Work.BoseBoxFock.PCFU.chDconv]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (y - z) : ℝ) : ℂ)
      = ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ)
        * ((Work.BoseFixR.W1fun v h ℓ (z - y) : ℝ) : ℂ)
    rw [show y - z = -(z - y) by abel, hev (z - y)]
  -- the pointwise splitting of the smoothed kernel
  have hfun : Work.BoseBoxFock.PCFU.chDkerS (h := h) fu ℓ N
      = fun x : E3 => (((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N) x
          + (Work.BoseFixR.W1fun v h ℓ) x : ℝ) : ℂ) := by
    funext x
    simp only [Work.BoseBoxFock.PCFU.chDkerS, Work.BoseBoxFock.PCFU.chDkerE]
    push_cast
    ring
  have hsplit : ∀ u : E3,
      Work.BoseBoxFock.PCFU.chDconv ℓ (Work.BoseBoxFock.PCFU.chDkerS (h := h) fu ℓ N) u
        = Work.BoseBoxFock.PCFU.chDconv ℓ
            (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N u : ℝ) : ℂ)) u
          + Work.BoseBoxFock.PCFU.chDconv ℓ
            (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ)) u := by
    intro u
    rw [hfun]
    have hΛ : 0 < Work.BoseBoxFock.uvRad ℓ N := by
      rw [Work.BoseBoxFock.uvRad]
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      positivity
    obtain ⟨Cb, hCb0, hCb⟩ := Work.BoseBoxFock.uvSmear_rapidDecay fu hΛ hWint hWcs 0
    have hbdd : ∀ x : E3, |Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N)
        (Work.BoseFixR.W1fun v h ℓ) x| ≤ Cb := fun x => by simpa using hCb x
    have h1 : Integrable (fun w : E3 =>
        ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseFixR.W1fun v h ℓ) (u - w) : ℝ) : ℂ)) :=
      integrable_chiLam_mul_of_bounded hℓ
        (Work.BoseBoxFock.uvSmear_continuous fu hΛ hWint) hbdd u
    have h2 : Integrable (fun w : E3 =>
        ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
          * ((Work.BoseFixR.W1fun v h ℓ (u - w) : ℝ) : ℂ)) :=
      integrable_chiLam_mul hWint u
    have hE : Integrable (fun w : E3 =>
        ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
          * ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N (u - w) : ℝ) : ℂ)) := by
      refine (h1.sub h2).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Work.BoseBoxFock.PCFU.chDkerE, Pi.sub_apply]
      push_cast
      ring
    exact chDconv_ofReal_add u hE h2
  -- summability of the two families
  have hSsumm : Summable (fun d : Fin 3 → ℤ => Work.BoseBoxFock.PCFU.chDconv ℓ
      (Work.BoseBoxFock.PCFU.chDkerS (h := h) fu ℓ N)
      (z + ℓ • Work.BoseBoxFock.latVec d)) := summable_chDconv_kerS hℓ hN hWint hWcs z
  have hWsumm : Summable (fun d : Fin 3 → ℤ => Work.BoseBoxFock.PCFU.chDconv ℓ
      (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
      (z + ℓ • Work.BoseBoxFock.latVec d)) := by
    refine Summable.of_norm ?_
    rw [hℓdef]
    exact Work.PCFU.chDW1sum_summable (v := v) (h := h) hR hv_supp hℓE z
  have hEsumm : Summable (fun d : Fin 3 → ℤ => Work.BoseBoxFock.PCFU.chDconv ℓ
      (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
      (z + ℓ • Work.BoseBoxFock.latVec d)) :=
    (hSsumm.sub hWsumm).congr fun d => by rw [hsplit _]; ring
  -- the assembly
  have hcongr : (∑' d : Fin 3 → ℤ, Work.BoseBoxFock.PCFU.chDconv ℓ
        (Work.BoseBoxFock.PCFU.chDkerS (h := h) fu ℓ N)
        (z + ℓ • Work.BoseBoxFock.latVec d))
      = ∑' d : Fin 3 → ℤ, (Work.BoseBoxFock.PCFU.chDconv ℓ
            (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
            (z + ℓ • Work.BoseBoxFock.latVec d)
          + Work.BoseBoxFock.PCFU.chDconv ℓ
            (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
            (z + ℓ • Work.BoseBoxFock.latVec d)) :=
    tsum_congr fun d => hsplit _
  rw [huv, hDC, hcongr, Summable.tsum_add hEsumm hWsumm]
  rw [Summable.tsum_eq_add_tsum_ite hWsumm (0 : Fin 3 → ℤ)]
  have hzero : Work.BoseBoxFock.PCFU.chDconv ℓ
      (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ))
      (z + ℓ • Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ))
      = Work.BoseBoxFock.PCFU.chDconv ℓ
          (fun u => ((Work.BoseFixR.W1fun v h ℓ u : ℝ) : ℂ)) z := by
    rw [latVec_zero, smul_zero, add_zero]
  rw [hzero]
  ring

end Work.PCFU
