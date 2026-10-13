import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Mine.SlotDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceRegular
import Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers

The a.e.-form of the radial variable, the additivity/const-multiple rules for the iterates of
`∂_θ` (the module `remov.PsiSlotBounds`, which contains `pthIter_add`, cannot be imported at the
moment, so the two-line induction is redone here), the measurability of the slots, and the
monotonicity of the angular weight `sin(2θ)^a` in the exponent. -/

/-- Almost every `z ∈ Iz = [0,∞)` is positive (the only missing point is `0`). -/
private theorem ts_ae_pos_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
  have h1 : {x : ℝ | ¬ (x ∈ Set.Ici (0 : ℝ) → (0 : ℝ) < x)} = {0} := by
    ext x
    simp only [Set.mem_Ici, not_imp, not_lt, Set.mem_singleton_iff]
    constructor
    · intro h; linarith [h.1, h.2]
    · intro h; subst h; norm_num
  rw [h1]
  exact MeasureTheory.measure_singleton 0

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
private theorem ts_sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
private theorem ts_pthIter_add (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- `∂_θ^n (c·f) = c·∂_θ^n f` for a constant `c` (no smoothness needed). -/
private theorem ts_pthIter_const_mul (c : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter n f z θ := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      simp only [Work.Spaces.pth]
      rw [deriv_const_mul_field']

/-- The angular slice `θ ↦ ∂_θ^{n+1} f z θ` is measurable (no smoothness needed). -/
private theorem ts_measurable_pthIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Measurable (fun θ => Work.Spaces.pthIter (n + 1) f z θ) := by
  have h : (fun θ => Work.Spaces.pthIter (n + 1) f z θ)
      = deriv (fun θ' => Work.Spaces.pthIter n f z θ') := by
    funext θ
    rw [Work.Spaces.pthIter_succ]
    rfl
  rw [h]
  exact measurable_deriv _

/-- The angular weight `θ ↦ sin(2θ)^q` is measurable. -/
private theorem ts_measurable_sin_rpow (q : ℝ) :
    Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ q) :=
  (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const q

/-- For `θ` in the open interval the weight `sin(2θ)^a` is antitone in the exponent. -/
private theorem ts_sin_rpow_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {a b : ℝ}
    (hab : a ≤ b) : (Real.sin (2 * θ)) ^ b ≤ (Real.sin (2 * θ)) ^ a := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsplit : (Real.sin (2 * θ)) ^ b
      = (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a) := by
    rw [← Real.rpow_add hs, show a + (b - a) = b from by ring]
  have hle : (Real.sin (2 * θ)) ^ (b - a) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (by linarith)
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ a := Real.rpow_nonneg hs.le a
  rw [hsplit]
  calc (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a)
      ≤ (Real.sin (2 * θ)) ^ a * 1 := mul_le_mul_of_nonneg_left hle hnn
    _ = (Real.sin (2 * θ)) ^ a := mul_one _

/-- `SmoothOpen` is closed under multiplication by a constant. -/
private theorem ts_smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have hfun : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
  exact (contDiffOn_const : ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => c)
    Work.FTS.EllipticEst.Q0).mul hf

/-- `SmoothOpen` is closed under the iterated `∂_θ`. -/
private theorem ts_smoothOpen_pthIter {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `SmoothOpen` is closed under addition. -/
private theorem ts_smoothOpen_add {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.EllipticEst.Q0 := hf.forall n
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 := hg.forall n
  have h3 := h1.add h2
  have hfun : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => f p.1 p.2 + g p.1 p.2 := by
    funext p; rfl
  rw [hfun]
  exact h3

/-- `Work.Stability.smoothOrder` is not zero (it is the genuine smooth order `∞`). -/
private theorem ts_smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- On the open quadrant the iterated `∂_θ` is additive for `SmoothOpen` data. -/
private theorem ts_pthIter_add_on_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) (n : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter n f z θ + Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((ts_smoothOpen_pthIter hf n).curry_θ hz).differentiableOn ts_smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((ts_smoothOpen_pthIter hg n).curry_θ hz).differentiableOn ts_smoothOrder_ne_zero
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      exact heq.deriv_eq.trans (deriv_add hd1 hd2)

/-! ## The `a.e.`-integrability bundle -/

/- **Discharge of the a.e.-in-`z` integrability bundle consumed by `TopSlotTwoD`.**
Intended namespace: `Work.FTS.EllipticEst.Cores.Pieces`.

From the hypotheses of the target statement alone (a weak datum `EllWeakPos α k F Ψ` with `k ≥ 3`
and the two level-`(k-1)` norm bounds, with the parameter `D`), conclude for almost every `z > 0`:

* `θ ↦ Ψ z θ` is continuous on the closed interval (the proved
  `Work.FTS.EllipticEst.remov.weakSliceRegular`);
* the `(k+2)`-nd angular derivative slot with weight `σ^{2k-γ}` is integrable — it is the mixed
  level-`k` slot of `HkSq α k (∂_θθΨ)`, honest by `EllWeakPos.memB`;
* the `k`-th angular derivative slot of `Gsrc α F Ψ = F + α²z²∂_z²Ψ + α(5+α)D_zΨ` is integrable —
  the pieces come from `EllWeakPos.memF` (levels `≤ k` of `F`), `EllWeakPos.memA`
  (levels `≤ k` of `z²∂_z²Ψ`) and from `EllWeakPos.memB` for the `D_zΨ`-piece (via the proved
  `Work.FTS.EllipticEst.remov.EllWeakPos_DzIter_one_shift_of_two_le`, which supplies
  `HkMem α (k-1) (pthIter 2 (DzIter 1 Ψ))`, together with `∂_θ^k(D_zΨ) = ∂_θ^{k-2}(∂_θθ(D_zΨ))`
  and `σ^{2k-γ} ≤ σ^{2(k-2)-γ}`; note that the real-valued bound (2) alone is *not* enough here,
  because `HkSq` is a Bochner integral and returns junk `0` when the integrand is non-integrable);
* the `u`-family `Icc 3 (k+1)`, the `η`-term and the two unweighted `L²` terms (the last two follow
  from the slice continuity and smoothness on the open interval).

The transfer "integrability of the `D_θ`-slots ↦ integrability of the plain slots" is the sharp
forward expansion `σ^{2m}(∂_θ^m f)² ≤ C Σ_{q∈Icc 1 m}(D_θ^q f)²` in which the `q = 0` term is absent
(the coefficient of `∂_θ^0` in `D_θ^m` vanishes because `D_θ(const) = 0`);
`Work.FTS.EllipticEst.remov.DthIter_expansion` (`dthCoef_eq_sin_pow_mul_dB`, `DthCoef_sin_pow_bound`,
`dthCoef_self`) and `Work.FTS.EllipticEst.Cores.Pieces.pthIter_sq_mul_sin_pow_le` are the available
ingredients. -/
theorem TopSlotIntegrability (k : ℕ) (hk : 3 ≤ k) (D : ℝ) (hD : 0 < D) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        ContinuousOn (fun t => Ψ z t) (Set.Icc 0 (Real.pi / 2)) ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        (∀ i ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.pthIter i Ψ z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * (i : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ) := by
  intro α F Ψ hα hα4 h _hH1 _hH2
  filter_upwards [ts_ae_pos_Iz] with z hz
  have hk1 : 1 ≤ k := by omega
  -- the smoothness of `Ψ` and of its iterates
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hG : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hΨ.pth.pth
  -- the slice bundle of `weakSliceRegular`
  obtain ⟨hcont, -, -, -, hPsi2, hPsi1, hPsi2sEta⟩ :=
    Work.FTS.EllipticEst.remov.weakSliceRegular k hk1 α F Ψ hα hα4 h z hz
  have hPsi2' : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using
      hPsi2sEta
  have hPsi1' : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hPsi1
  refine ⟨hcont, ?_, ?_, ?_, hPsi2', hPsi1', hPsi2⟩
  · -- the top slot `∂_θ^{k+2}Ψ`
    have h := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := Work.Spaces.pthIter 2 Ψ)
      (fun n => hG.forall n) h.memB hz (m := k) (by omega) le_rfl
    have hfun : (fun θ => (Work.Spaces.pthIter k (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = fun θ => (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) := by
      funext θ
      rw [← ts_pthIter_add k 2 Ψ]
    rw [hfun] at h
    exact h
  · -- the angular source `Gsrc α F Ψ`
    set A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hAdef
    set B : ℝ → ℝ → ℝ := Work.Spaces.DzIter 1 Ψ with hBdef
    set c : ℝ := α * (5 + α) with hcdef
    have hFs : Work.FTS.EllipticEst.SmoothOpen F :=
      Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
    have hAs : Work.FTS.EllipticEst.SmoothOpen A :=
      show Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) from
        Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hΨ
    have hBs : Work.FTS.EllipticEst.SmoothOpen B :=
      show Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) from hΨ.DzIter 1
    have hiF := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := F)
      (fun n => hFs.forall n) h.memF hz (m := k) (by omega) le_rfl
    have hiA := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := A)
      (fun n => hAs.forall n) h.memA hz (m := k) (by omega) le_rfl
    -- the `D_zΨ`-piece: `HkMem α (k-1) (∂_θ²(D_zΨ))` from the radial shift
    have hBmem0 : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift (α := α) (k := k) hk1 hG h.memB
    have hBmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.pthIter 2 B) := by
      rw [hBdef]
      refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hBmem0 ?_
      intro z' hz' θ hθ
      exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1
        (show ((z', θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz', hθ⟩)).symm
    have hiB0 := pthSlotInt_of_HkMem (α := α) hα (k := k - 1) (g := Work.Spaces.pthIter 2 B)
      (fun n => (ts_smoothOpen_pthIter hBs 2).forall n)
      hBmem hz (m := k - 2) (by omega) (by omega)
    have hexpB : 2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α
        ≤ 2 * (k : ℝ) - Work.Spaces.gam α := by
      have : ((k - 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 2
      linarith
    have hiB1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k B z θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      have hfun : (fun θ => (Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 B) z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α))
          = fun θ => (Work.Spaces.pthIter k B z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α) := by
        funext θ
        rw [← ts_pthIter_add (k - 2) 2 B, show k - 2 + 2 = k from by omega]
      rw [hfun] at hiB0
      exact hiB0
    have hiB : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k B z θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      have hm : Measurable (fun θ => Work.Spaces.pthIter k B z θ) := by
        have h := ts_measurable_pthIter_succ (k - 1) B z
        rwa [show k - 1 + 1 = k from by omega] at h
      have hmeasw : Measurable (fun θ : ℝ =>
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) :=
        ts_measurable_sin_rpow _
      refine MeasureTheory.Integrable.mono' hiB1
        (((hm.pow_const 2).mul hmeasw).aestronglyMeasurable) ?_
      refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      have hsin : 0 ≤ Real.sin (2 * θ) :=
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])).le
      have hw : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
        Real.rpow_nonneg hsin _
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw)]
      exact mul_le_mul_of_nonneg_left (ts_sin_rpow_le hθ hexpB) (sq_nonneg _)
    -- the pointwise expansion of `∂_θ^k(Gsrc α F Ψ)`
    have hgrp : Work.FTS.EllipticEst.Mine.Gsrc α F Ψ
        = fun z θ => (F z θ + α ^ 2 * A z θ) + c * B z θ := by
      funext z θ
      rw [hAdef, hBdef, hcdef]
      simp only [Work.FTS.EllipticEst.Mine.Gsrc, Work.Spaces.DzIter_succ,
        Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    have hsm1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ + α ^ 2 * A z θ) :=
      ts_smoothOpen_add hFs (ts_smoothOpen_const_mul (α ^ 2) hAs)
    have hsm2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * B z θ) :=
      ts_smoothOpen_const_mul c hBs
    have hAc : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α ^ 2 * A z θ) :=
      ts_smoothOpen_const_mul (α ^ 2) hAs
    have hdecomp : ∀ {z' θ : ℝ}, 0 < z' → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z' θ
          = Work.Spaces.pthIter k F z' θ + α ^ 2 * Work.Spaces.pthIter k A z' θ
            + c * Work.Spaces.pthIter k B z' θ := by
      intro z' θ hz' hθ0 hθ1
      rw [hgrp, ts_pthIter_add_on_Q0 hsm1 hsm2 k z' θ hz' hθ0 hθ1,
        ts_pthIter_add_on_Q0 hFs hAc k z' θ hz' hθ0 hθ1]
      rw [ts_pthIter_const_mul (α ^ 2) k A, ts_pthIter_const_mul c k B]
    -- the three integrable pieces, with the constants pulled out
    have hpartF : MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k F z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := hiF
    have hpartA : MeasureTheory.IntegrableOn (fun θ =>
        (α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      (hiA.const_mul ((α ^ 2) ^ 2)).congr
        (Filter.Eventually.of_forall (fun θ => by ring))
    have hpartB : MeasureTheory.IntegrableOn (fun θ =>
        (c * Work.Spaces.pthIter k B z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      (hiB.const_mul (c ^ 2)).congr (Filter.Eventually.of_forall (fun θ => by ring))
    have hmaj : MeasureTheory.IntegrableOn (fun θ => 3 *
        ((Work.Spaces.pthIter k F z θ) ^ 2 *
            (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
          + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            + (c * Work.Spaces.pthIter k B z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))) Work.Spaces.Iθ :=
      (hpartF.add (hpartA.add hpartB)).const_mul 3
    have hm : Measurable (fun θ =>
        Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) := by
      have h := ts_measurable_pthIter_succ (k - 1) (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z
      rwa [show k - 1 + 1 = k from by omega] at h
    have haesm : AEStronglyMeasurable (fun θ =>
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hm.pow_const 2).mul (ts_measurable_sin_rpow _)).aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' hmaj haesm ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hdec := hdecomp (z' := z) (θ := θ) hz hθ.1 hθ.2
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
      Real.rpow_nonneg hsin _
    have hsq : (Work.Spaces.pthIter k F z θ
          + α ^ 2 * Work.Spaces.pthIter k A z θ + c * Work.Spaces.pthIter k B z θ) ^ 2
        ≤ 3 * ((Work.Spaces.pthIter k F z θ) ^ 2
            + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2
              + (c * Work.Spaces.pthIter k B z θ) ^ 2)) := by
      nlinarith [sq_nonneg (Work.Spaces.pthIter k F z θ
          - α ^ 2 * Work.Spaces.pthIter k A z θ),
        sq_nonneg (α ^ 2 * Work.Spaces.pthIter k A z θ
          - c * Work.Spaces.pthIter k B z θ),
        sq_nonneg (c * Work.Spaces.pthIter k B z θ
          - Work.Spaces.pthIter k F z θ)]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)), hdec]
    calc (Work.Spaces.pthIter k F z θ + α ^ 2 * Work.Spaces.pthIter k A z θ
            + c * Work.Spaces.pthIter k B z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        ≤ (3 * ((Work.Spaces.pthIter k F z θ) ^ 2
            + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2
              + (c * Work.Spaces.pthIter k B z θ) ^ 2))) *
          (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
          mul_le_mul_of_nonneg_right hsq hw
      _ = 3 * ((Work.Spaces.pthIter k F z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
            + ((α ^ 2 * Work.Spaces.pthIter k A z θ) ^ 2 *
                (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
              + (c * Work.Spaces.pthIter k B z θ) ^ 2 *
                (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := by ring

  · -- the family `Icc 3 (k+1)`
    intro i hi
    have hi3 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k + 1 := (Finset.mem_Icc.mp hi).2
    have h := pthSlotInt_of_HkMem (α := α) hα (k := k) (g := Work.Spaces.pthIter 2 Ψ)
      (fun n => hG.forall n) h.memB hz (m := i - 2) (by omega) (by omega)
    have hexp : 2 * ((i - 2 : ℕ) : ℝ) - Work.Spaces.gam α
        = 2 * (i : ℝ) - 4 - Work.Spaces.gam α := by
      rw [Nat.cast_sub (by omega : 2 ≤ i)]
      push_cast
      ring
    have hfun : (fun θ => (Work.Spaces.pthIter (i - 2) (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * ((i - 2 : ℕ) : ℝ) - Work.Spaces.gam α))
        = fun θ => (Work.Spaces.pthIter i Ψ z θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 * (i : ℝ) - 4 - Work.Spaces.gam α) := by
      funext θ
      rw [← ts_pthIter_add (i - 2) 2 Ψ, show i - 2 + 2 = i from by omega, hexp]
    rw [hfun] at h
    exact h
end

end Work.FTS.EllipticEst.Cores.Pieces
