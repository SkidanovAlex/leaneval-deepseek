import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic
import Submission.Work.CR.Flat.Cauchy.isClosedForm_iteratedFDeriv
import Submission.Work.NN.Core.transform_fderiv
import Submission.Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ

namespace Work.NN.Core.TelTwoDF

open scoped NNReal ENNReal
open Set
open Work.CR.Flat.Cauchy (dbarTransform)

/-- The coercion `ℕ → WithTop ℕ∞` turns successors into `+ 1`. -/
private lemma coe_succ (i : ℕ) : ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 := by
  rw [Nat.cast_add, Nat.cast_one]

/-! ## Support of the iterated derivatives of fibre-supported data

A derivative of a function vanishing on a closed set vanishes on the *interior* of the
complement, i.e. the support of `D^i g` is contained in the closure of the support of `g`. -/

private lemma iteratedFDeriv_eq_zero_of_fiberSupport {n : ℕ} {B : ℝ} (s : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hsupp : ∀ y, B ≤ ‖y s‖ → g y = 0) (i : ℕ) :
    ∀ y : Fin n → ℂ, B < ‖y s‖ → iteratedFDeriv ℝ i g y = 0 := by
  have hclosed : IsClosed {y : Fin n → ℂ | ‖y s‖ ≤ B} :=
    isClosed_le ((continuous_apply s).norm) continuous_const
  have hsub : tsupport g ⊆ {y : Fin n → ℂ | ‖y s‖ ≤ B} := by
    refine closure_minimal (fun z hz => ?_) hclosed
    by_contra h
    exact hz (hsupp z (le_of_lt (lt_of_not_ge h)))
  intro y hy
  have h1 : y ∉ tsupport g := fun h => absurd (hsub h) (not_le.mpr hy)
  have h2 : y ∉ tsupport (iteratedFDeriv ℝ i g) :=
    fun h => h1 (tsupport_iteratedFDeriv_subset i h)
  by_contra hne
  exact h2 (subset_tsupport _ (Function.mem_support.mpr hne))

private lemma iteratedFDeriv_apply_eq_zero_of_fiberSupport {n : ℕ} {B : ℝ} (s : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hsupp : ∀ y, B ≤ ‖y s‖ → g y = 0) (i : ℕ)
    (v : Fin i → (Fin n → ℂ)) {b : ℝ} (hb : B < b) :
    ∀ y : Fin n → ℂ, b ≤ ‖y s‖ → iteratedFDeriv ℝ i g y v = 0 := by
  intro y hy
  rw [iteratedFDeriv_eq_zero_of_fiberSupport s hsupp i y (lt_of_lt_of_le hb hy)]
  simp

/-! ## Smoothness of the evaluated iterated derivatives -/

private lemma contDiff_iteratedFDeriv_apply {n k i : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ k g) (hi : i + 1 ≤ k) (v : Fin i → (Fin n → ℂ)) :
    ContDiff ℝ 1 (fun y => iteratedFDeriv ℝ i g y v) := by
  have h2 : ContDiff ℝ 1 (iteratedFDeriv ℝ i g) :=
    hg.iteratedFDeriv_right (m := 1) (i := i) (by rw [add_comm]; exact_mod_cast hi)
  exact (ContinuousLinearMap.contDiff
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ v)).comp h2

private lemma continuous_iteratedFDeriv_apply {n k i : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ k g) (hi : i ≤ k) (v : Fin i → (Fin n → ℂ)) :
    Continuous (fun y => iteratedFDeriv ℝ i g y v) := by
  have h2 : ContDiff ℝ 0 (iteratedFDeriv ℝ i g) :=
    hg.iteratedFDeriv_right (m := 0) (i := i) (by rw [zero_add]; exact_mod_cast hi)
  exact ((ContinuousLinearMap.contDiff
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ v)).comp h2).continuous

/-! ## Commutation of the transform with iterated derivatives -/

/-- **The Cauchy-type transform commutes with all iterated derivatives.**

For `g` of class `C^k` supported in the fibre `B ≤ ‖y s‖` and every `i ≤ k`, the `i`-th iterated
derivative of `dbarTransform R s g` is the transform of the `i`-th iterated derivative of `g`:

`D^i (T g)(z)[v] = T (fun y => D^i g(y)[v])(z)`.

The induction is on `i`: the step rewrites `D^{i+1} (T g)(z)[v]` as the directional derivative of
`D^i (T g)(·)[tail v]` (the repo lemma `iteratedFDeriv_succ_apply_eq_fderiv`, which needs the
`C^{i+1}`-regularity of `T g` supplied by `contDiff_dbarTransform_univ`), replaces `D^i (T g)` by
the transform of `D^i g` (induction hypothesis), and differentiates under the integral sign with
`Work.NN.Core.transform_fderiv`. -/
private lemma iteratedFDeriv_dbarTransform_eq {n : ℕ} {ρ B : ℝ} (hB : 0 ≤ B) (s : Fin n)
    {k : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ k g) (hsupp : ∀ y, B ≤ ‖y s‖ → g y = 0) :
    ∀ (i : ℕ), i ≤ k → ∀ (v : Fin i → (Fin n → ℂ)) (z : Fin n → ℂ),
      iteratedFDeriv ℝ i (fun z => dbarTransform ρ s g z) z v
        = dbarTransform ρ s (fun y => iteratedFDeriv ℝ i g y v) z := by
  intro i
  induction i with
  | zero =>
      intro hi v z
      simp
  | succ i ih =>
      intro hi v z
      have hi' : i ≤ k := le_trans (Nat.le_succ i) hi
      have hgc : ContDiff ℝ (i + 1) g := hg.of_le (by exact_mod_cast hi)
      have hgd : ContDiff ℝ ((i : WithTop ℕ∞) + 1) g := hg.of_le (by exact_mod_cast hi)
      have hT : ContDiff ℝ ((i : WithTop ℕ∞) + 1) (fun z => dbarTransform ρ s g z) := by
        have h0 : ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (fun z => dbarTransform ρ s g z) :=
          contDiff_dbarTransform_univ hB s (i + 1) hgc hsupp
        rwa [coe_succ i] at h0
      rw [Work.CR.Flat.Cauchy.iteratedFDeriv_succ_apply_eq_fderiv hT v z]
      have hfun : (fun t => iteratedFDeriv ℝ i (fun z => dbarTransform ρ s g z) t
            (Fin.tail v))
          = fun t => dbarTransform ρ s (fun y => iteratedFDeriv ℝ i g y (Fin.tail v)) t :=
        funext fun t => ih hi' (Fin.tail v) t
      rw [hfun, Work.NN.Core.transform_fderiv s
        (contDiff_iteratedFDeriv_apply hg hi (Fin.tail v)) z (v 0)]
      congr 1
      funext y
      rw [← Work.CR.Flat.Cauchy.iteratedFDeriv_succ_apply_eq_fderiv hgd v y]

/-- **The Cauchy-type transform `dbarTransform R s` is bounded on the `C^{k,α}` scale, with no
loss of derivatives, for data supported in the fibre `‖y s‖ ≤ B`.**

`Work.CR.Flat.Cauchy.dbarTransform R s g z = -(1/π) ∫_{‖w‖<R} g (z + w e_s) / w dw` is the
one-variable Cauchy-type transform in the `s`-th coordinate.  The region of integration is the
disc `‖w‖ < R`, fixed in the fibre variable, and the pole sits at `w = 0`, so the kernel `1/w` is
locally integrable and independent of `z`.

The point is the *absence of any derivative loss*: the `C^{k,α}`-norm of the transform on the
polydisc `polydisc 0 r` is controlled by the `C^{k,α}`-norm of the datum over *all* of `ℂⁿ`.
(This is in contrast with `holderNorm_one_cauchyTransform_le`, which is the `C^{0,α}`-to-`C^{1,α}`
gain statement; here the conclusion is at the same order `k`.)

Route.  Since the kernel does not depend on `z` and the region of integration is fixed, every
derivative passes through the integral sign: for `g` of class `C^m` and every tuple
`v : Fin m → (Fin n → ℂ)`,

  `iteratedFDeriv ℝ m (dbarTransform R s g) z v
     = dbarTransform R s (fun y => iteratedFDeriv ℝ m g y v) z`,

by induction on `m` from the single-differentiation step

  `fderiv ℝ (dbarTransform R s g) z v = dbarTransform R s (fun y => fderiv ℝ g y v) z`,

which is differentiation under the integral sign (domination by
`(sup ‖fderiv ℝ g‖) ‖v‖ / ‖w‖`, and `1/‖w‖` is integrable on the disc).  The support hypothesis is
not needed for this step; it only serves to make the fibre slices bounded, and the domination is
local in any case.  (The suggested convolution route is *not* applicable: fibre support is not
compact support.)

Then the `m`-th derivative of the transform is the transform of the `m`-th derivative of the datum,
and the order-zero bounds `‖dbarTransform R s h z‖ ≤ 2 R ‖h‖_sup` and
`‖dbarTransform R s h x - dbarTransform R s h y‖ ≤ 2 R [h]_α ‖x - y‖^α` (obtained by dominating
against the integrable `1/‖w‖`) give the bounds on `iteratedFDeriv` and on the Hölder seminorms.

References: `Work.CR.Flat.Cauchy.dbarTransform_basic` (order-zero estimates in exactly this fibre
form), `Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv` and
`Work.CR.Flat.Cauchy.bmPotential_fderiv_of_hasCompactSupport` (the same commutation for the
Bochner–Martinelli potential, a good template), `Work.CR.Flat.Cauchy.contDiff_dbarTransform`,
`Work.CR.Flat.le_iterDerivNorm`, `Work.CR.Flat.le_holderSeminorm`, `Work.CR.Flat.holderNorm`,
`Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball`. -/
theorem holderNorm_dbarTransform_le {n : ℕ} {R B α : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (s : Fin n)
    (hα : 0 < α) (hα1 : α < 1) (k : ℕ) {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : (Fin n → ℂ) → ℂ, ContDiff ℝ k g →
      (∀ y : Fin n → ℂ, B ≤ ‖y s‖ → g y = 0) →
      Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform R s g)
        (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α g Set.univ := by
  refine ⟨2 * R + 1, by linarith, ?_⟩
  intro g hg hsupp
  have hΩopen : IsOpen (Work.CR.Flat.polydisc (0 : Fin n → ℂ) r) :=
    Work.CR.Flat.isOpen_polydisc 0 r
  by_cases htop : Work.CR.Flat.holderNorm k α g Set.univ = ⊤
  · rw [htop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; linarith)]
    exact le_top
  · have hfin : Work.CR.Flat.holderNorm k α g Set.univ < ⊤ := lt_top_iff_ne_top.mpr htop
    have hAfin : ∀ j, j ≤ k → Work.CR.Flat.iterDerivNorm j g Set.univ < ⊤ := fun j hj =>
      lt_of_le_of_lt (Work.CR.Flat.iterDerivNorm_le_holderNorm k α g Set.univ hj) hfin
    have hKfin : ∀ j, j ≤ k → Work.CR.Flat.holderSeminorm j α g Set.univ < ⊤ := fun j hj =>
      lt_of_le_of_lt (Work.CR.Flat.holderSeminorm_le_holderNorm k α g Set.univ hj) hfin
    let A : ℕ → ℝ := fun j => (Work.CR.Flat.iterDerivNorm j g Set.univ).toReal
    let K : ℕ → ℝ := fun j => (Work.CR.Flat.holderSeminorm j α g Set.univ).toReal
    have hAeq : ∀ j (hj : j ≤ k),
        ENNReal.ofReal (A j) = Work.CR.Flat.iterDerivNorm j g Set.univ :=
      fun j hj => ENNReal.ofReal_toReal (ne_top_of_lt (hAfin j hj))
    have hKeq : ∀ j (hj : j ≤ k),
        ENNReal.ofReal (K j) = Work.CR.Flat.holderSeminorm j α g Set.univ :=
      fun j hj => ENNReal.ofReal_toReal (ne_top_of_lt (hKfin j hj))
    have hAb : ∀ j (hj : j ≤ k) (y : Fin n → ℂ), ‖iteratedFDeriv ℝ j g y‖ ≤ A j := by
      intro j hj y
      have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ j g y‖
          ≤ Work.CR.Flat.iterDerivNorm j g Set.univ := by
        rw [Work.CR.Flat.iterDerivNorm]
        refine le_iSup₂_of_le y (Set.mem_univ y) ?_
        rw [iteratedFDerivWithin_univ]
      rw [← hAeq j hj] at h1
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
    have hKb : ∀ j (hj : j ≤ k) (y₁ y₂ : Fin n → ℂ),
        ‖iteratedFDeriv ℝ j g y₁ - iteratedFDeriv ℝ j g y₂‖ ≤ K j * ‖y₁ - y₂‖ ^ α := by
      intro j hj y₁ y₂
      rcases eq_or_ne y₁ y₂ with rfl | hne
      · simp [Real.zero_rpow (ne_of_gt hα)]
      · have h1 : ENNReal.ofReal
            (‖iteratedFDeriv ℝ j g y₁ - iteratedFDeriv ℝ j g y₂‖ / ‖y₁ - y₂‖ ^ α)
            ≤ Work.CR.Flat.holderSeminorm j α g Set.univ := by
          have h := Work.CR.Flat.le_holderSeminorm j α g Set.univ
            (Set.mem_univ y₁) (Set.mem_univ y₂) hne
          simpa only [iteratedFDerivWithin_univ] using h
        rw [← hKeq j hj] at h1
        have h2 := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
        have hpos : 0 < ‖y₁ - y₂‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) α
        rwa [div_le_iff₀ hpos] at h2
    have hTrans : ∀ i (hi : i ≤ k) (v : Fin i → (Fin n → ℂ)) (z : Fin n → ℂ),
        iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) z v
          = dbarTransform R s (fun y => iteratedFDeriv ℝ i g y v) z :=
      fun i hi v z => iteratedFDeriv_dbarTransform_eq hB s hg hsupp i hi v z
    have hN : ∀ i (hi : i ≤ k),
        Work.CR.Flat.iterDerivNorm i (fun z => dbarTransform R s g z)
            (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal (2 * R) * Work.CR.Flat.iterDerivNorm i g Set.univ := by
      intro i hi
      rw [Work.CR.Flat.iterDerivNorm]
      refine iSup₂_le fun x hx => ?_
      rw [show iteratedFDerivWithin ℝ i (fun z => dbarTransform R s g z)
              (Work.CR.Flat.polydisc 0 r) x
            = iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) x from
          iteratedFDerivWithin_of_isOpen i hΩopen hx]
      have hbnd : ‖iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) x‖ ≤ 2 * R * A i := by
        have hAi : 0 ≤ A i := ENNReal.toReal_nonneg
        refine ContinuousMultilinearMap.opNorm_le_bound (M := 2 * R * A i) (by positivity) fun v => ?_
        rw [hTrans i hi v x]
        have hc : Continuous fun y : Fin n → ℂ => iteratedFDeriv ℝ i g y v :=
          continuous_iteratedFDeriv_apply hg hi v
        have hs : ∀ y : Fin n → ℂ, (B + 1) ≤ ‖y s‖ → iteratedFDeriv ℝ i g y v = 0 :=
          iteratedFDeriv_apply_eq_zero_of_fiberSupport s hsupp i v (by linarith)
        have hbd : ∀ y : Fin n → ℂ, (∀ l, l ≠ s → y l = x l) → ‖y s‖ ≤ B + 1 →
            ‖iteratedFDeriv ℝ i g y v‖ ≤ A i * ∏ l, ‖v l‖ := by
          intro y _ _
          calc ‖iteratedFDeriv ℝ i g y v‖
              ≤ ‖iteratedFDeriv ℝ i g y‖ * ∏ l, ‖v l‖ :=
                ContinuousMultilinearMap.le_opNorm _ _
            _ ≤ A i * ∏ l, ‖v l‖ := mul_le_mul_of_nonneg_right (hAb i hi y)
                (Finset.prod_nonneg fun l _ => norm_nonneg _)
        have hmain := (Work.CR.Flat.Cauchy.dbarTransform_basic (ρ := R) (b := B + 1) hR
          (by linarith) (j := s)).1 hc hs (A i * ∏ l, ‖v l‖) x hbd
        calc ‖dbarTransform R s (fun y => iteratedFDeriv ℝ i g y v) x‖
            ≤ 2 * R * (A i * ∏ l, ‖v l‖) := hmain
          _ = 2 * R * A i * ∏ l, ‖v l‖ := by ring
      calc ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) x‖
          ≤ ENNReal.ofReal (2 * R * A i) := ENNReal.ofReal_le_ofReal hbnd
        _ = ENNReal.ofReal (2 * R) * ENNReal.ofReal (A i) := ENNReal.ofReal_mul (by linarith)
        _ = ENNReal.ofReal (2 * R) * Work.CR.Flat.iterDerivNorm i g Set.univ := by
            rw [hAeq i hi]
    have hH : ∀ i (hi : i ≤ k),
        Work.CR.Flat.holderSeminorm i α (fun z => dbarTransform R s g z)
            (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal (2 * R) * Work.CR.Flat.holderSeminorm i α g Set.univ := by
      intro i hi
      rw [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      rw [show iteratedFDerivWithin ℝ i (fun z => dbarTransform R s g z)
              (Work.CR.Flat.polydisc 0 r) x
            = iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) x from
          iteratedFDerivWithin_of_isOpen i hΩopen hx,
          show iteratedFDerivWithin ℝ i (fun z => dbarTransform R s g z)
              (Work.CR.Flat.polydisc 0 r) y
            = iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) y from
          iteratedFDerivWithin_of_isOpen i hΩopen hy]
      have hbnd : ‖iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) x
            - iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) y‖
          ≤ 2 * R * K i * ‖x - y‖ ^ α := by
        have hKi : 0 ≤ K i := ENNReal.toReal_nonneg
        refine ContinuousMultilinearMap.opNorm_le_bound (M := 2 * R * K i * ‖x - y‖ ^ α)
          (by positivity) fun v => ?_
        rw [ContinuousMultilinearMap.sub_apply, hTrans i hi v x, hTrans i hi v y]
        have hc : Continuous fun y' : Fin n → ℂ => iteratedFDeriv ℝ i g y' v :=
          continuous_iteratedFDeriv_apply hg hi v
        have hs : ∀ y' : Fin n → ℂ, (B + 1) ≤ ‖y' s‖ → iteratedFDeriv ℝ i g y' v = 0 :=
          iteratedFDeriv_apply_eq_zero_of_fiberSupport s hsupp i v (by linarith)
        have hholder : ∀ a a' : Fin n → ℂ,
            ‖iteratedFDeriv ℝ i g a v - iteratedFDeriv ℝ i g a' v‖
              ≤ (K i * ∏ l, ‖v l‖) * ‖a - a'‖ ^ α := by
          intro a a'
          have h1 : ‖(iteratedFDeriv ℝ i g a - iteratedFDeriv ℝ i g a') v‖
              ≤ ‖iteratedFDeriv ℝ i g a - iteratedFDeriv ℝ i g a'‖ * ∏ l, ‖v l‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
          rw [ContinuousMultilinearMap.sub_apply] at h1
          calc ‖iteratedFDeriv ℝ i g a v - iteratedFDeriv ℝ i g a' v‖
              ≤ ‖iteratedFDeriv ℝ i g a - iteratedFDeriv ℝ i g a'‖ * ∏ l, ‖v l‖ := h1
            _ ≤ (K i * ‖a - a'‖ ^ α) * ∏ l, ‖v l‖ :=
                mul_le_mul_of_nonneg_right (hKb i hi a a')
                  (Finset.prod_nonneg fun l _ => norm_nonneg _)
            _ = (K i * ∏ l, ‖v l‖) * ‖a - a'‖ ^ α := by ring
        have hmain := (Work.CR.Flat.Cauchy.dbarTransform_basic (ρ := R) (b := B + 1) hR
          (by linarith) (j := s)).2.1 hc hs α (K i * ∏ l, ‖v l‖) x y
          (fun a a' _ _ => hholder a a')
        calc ‖dbarTransform R s (fun y' => iteratedFDeriv ℝ i g y' v) x
              - dbarTransform R s (fun y' => iteratedFDeriv ℝ i g y' v) y‖
            ≤ 2 * R * (K i * ∏ l, ‖v l‖) * ‖x - y‖ ^ α := hmain
          _ = (2 * R * K i * ‖x - y‖ ^ α) * ∏ l, ‖v l‖ := by ring
      have hpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      calc ENNReal.ofReal (‖iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) x
              - iteratedFDeriv ℝ i (fun z => dbarTransform R s g z) y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (2 * R * K i) :=
            ENNReal.ofReal_le_ofReal (by rw [div_le_iff₀ hpos]; linarith [hbnd])
        _ = ENNReal.ofReal (2 * R) * ENNReal.ofReal (K i) := ENNReal.ofReal_mul (by linarith)
        _ = ENNReal.ofReal (2 * R) * Work.CR.Flat.holderSeminorm i α g Set.univ := by
            rw [hKeq i hi]
    calc Work.CR.Flat.holderNorm k α (fun z => dbarTransform R s g z)
          (Work.CR.Flat.polydisc 0 r)
        = ∑ i ∈ Finset.range (k + 1),
            (Work.CR.Flat.iterDerivNorm i (fun z => dbarTransform R s g z)
                (Work.CR.Flat.polydisc 0 r)
              + Work.CR.Flat.holderSeminorm i α (fun z => dbarTransform R s g z)
                (Work.CR.Flat.polydisc 0 r)) := rfl
      _ ≤ ∑ i ∈ Finset.range (k + 1),
            ENNReal.ofReal (2 * R) *
              (Work.CR.Flat.iterDerivNorm i g Set.univ
                + Work.CR.Flat.holderSeminorm i α g Set.univ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [mul_add]
          exact add_le_add (hN i hik) (hH i hik)
      _ = ENNReal.ofReal (2 * R) * Work.CR.Flat.holderNorm k α g Set.univ := by
          rw [Work.CR.Flat.holderNorm, Finset.mul_sum]
      _ ≤ ENNReal.ofReal (2 * R + 1) * Work.CR.Flat.holderNorm k α g Set.univ :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end Work.NN.Core.TelTwoDF
