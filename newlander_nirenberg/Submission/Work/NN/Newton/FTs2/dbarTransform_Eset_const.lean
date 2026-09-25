import Mathlib
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_Eset_le
import Submission.Work.NN.Core.TelTwoDF.EstimateDefs
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.holder_norm_sub_le_closure
import Submission.Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ
import Submission.Work.NN.Core.transform_fderiv
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic
import Submission.Work.CR.Flat.Cauchy.isClosedForm_iteratedFDeriv
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton.FTs2

open Work.NN.Core.TelTwoDF
open Work.CR.Flat.Cauchy (dbarTransform)

/-- The coercion `ℕ → WithTop ℕ∞` turns successors into `+ 1`. -/
private lemma coe_succ (i : ℕ) : ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 := by
  rw [Nat.cast_add, Nat.cast_one]

/-! ## Commutation of the transform with iterated derivatives -/

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

/-- **The Cauchy-type transform commutes with all iterated derivatives.** -/
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

/-! ## The identity of the two tracking radii -/

/-- The two tracking polydiscs of one step differ only in the `s`-th coordinate: replacing the
`e s`-radius of `Erad G (s+1)` there by the support radius `b s` gives `Erad G s`. -/
private lemma update_Erad_succ {n : ℕ} (G : Geom n) (s : Fin n) :
    Function.update (Erad G ((s : ℕ) + 1)) s (G.b s) = Erad G (s : ℕ) := by
  funext l
  by_cases hl : l = s
  · subst hl; rw [Function.update_self, Erad_self]
  · rw [Function.update_of_ne hl, Erad_succ_of_ne G hl]

/-- A point of the polydisc of radius `Erad G (s+1)` with the `s`-coordinate relaxed to the
support radius `G.b s` (i.e. of the enlarged polydisc `Eset G s`) lies in `Eset G s`. -/
private lemma mem_Eset_of_mem_update {n : ℕ} (G : Geom n) (s : Fin n) {z : Fin n → ℂ}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ)
      (Function.update (Erad G ((s : ℕ) + 1)) s (G.b s))) : z ∈ Eset G (s : ℕ) := by
  rw [mem_Eset]
  intro k
  rw [← update_Erad_succ G s]
  have h := hz k
  simp only [Pi.zero_apply, sub_zero] at h
  exact h

/-- Membership in a polydisc centred at the origin, in coordinates. -/
private lemma mem_polydisc_zero {n : ℕ} {Q : Fin n → ℝ} {z : Fin n → ℂ} :
    z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q ↔ ∀ l, ‖z l‖ < Q l := by
  simp [Work.CR.Flat.mem_polydisc]

/-! ## The fibre-pair analysis for a polydisc

The one-variable Cauchy-type transform at a point `z` reads its datum on the whole fibre
`{(z with fixed coordinates ≠ s)} × ℂ`; the following lemma extends the Hölder bound of the datum
from the polydisc `polydisc 0 (Function.update Q s B)` to *all* points of such a fibre, using the
continuity of the datum and its vanishing beyond the strip `‖· s‖ ≥ B`. -/

/-- Membership in the enlarged polydisc along a fibre: a point whose non-`s` coordinates agree
with those of a point of `polydisc 0 Q` and whose `s`-coordinate is small enough lies in
`polydisc 0 (Function.update Q s B)`. -/
private lemma mem_polydisc_update_of_fiber {n : ℕ} {Q : Fin n → ℝ} {s : Fin n} {B : ℝ}
    {z y : Fin n → ℂ} (hz : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q)
    (hy : ∀ l, l ≠ s → y l = z l) (hys : ‖y s‖ < B) :
    y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B) := by
  rw [mem_polydisc_zero] at hz ⊢
  intro l
  by_cases hl : l = s
  · subst hl; rw [Function.update_self]; exact hys
  · rw [Function.update_of_ne hl, hy l hl]; exact hz l

/-- A point of the fibre of an interior point whose `s`-coordinate has modulus exactly `B` lies in
the closure of the polydisc. -/
private lemma mem_closure_polydisc_update {n : ℕ} {Q : Fin n → ℝ} {s : Fin n} {B : ℝ}
    (hB : 0 < B) {v c : Fin n → ℂ} (hv : ∀ l, l ≠ s → ‖v l‖ < Q l) (hvs : ‖v s‖ < B)
    (hc : ∀ l, l ≠ s → c l = v l) (hcs : ‖c s‖ = B) :
    c ∈ closure (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (ε / (2 * B)) (1 / 2) with hδdef
  have hδpos : 0 < δ := lt_min (div_pos hε (by linarith)) (by norm_num)
  have hδle : δ ≤ ε / (2 * B) := min_le_left _ _
  have hδlt : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨Function.update c s (((1 - δ : ℝ) : ℂ) * c s), ?_, ?_⟩
  · rw [mem_polydisc_zero]
    intro l
    by_cases hl : l = s
    · subst hl
      rw [Function.update_self, Function.update_self]
      have h3 : ‖(((1 - δ : ℝ) : ℂ) * c l)‖ = (1 - δ) * ‖c l‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ)]
      rw [h3, hcs]
      nlinarith [hδpos, hB, hδlt]
    · rw [Function.update_of_ne hl, Function.update_of_ne hl, hc l hl]
      exact hv l hl
  · rw [dist_eq_norm, norm_sub_rev]
    have h1 : Function.update c s (((1 - δ : ℝ) : ℂ) * c s) - c
        = Function.update (0 : Fin n → ℂ) s (((1 - δ : ℝ) : ℂ) * c s - c s) := by
      funext l
      by_cases hl : l = s
      · subst hl; simp
      · simp [Function.update_of_ne hl]
    rw [h1, show Function.update (0 : Fin n → ℂ) s (((1 - δ : ℝ) : ℂ) * c s - c s)
        = Pi.single s (((1 - δ : ℝ) : ℂ) * c s - c s) from by
      funext l
      by_cases hl : l = s
      · subst hl; simp
      · rw [Function.update_of_ne hl, Pi.single_eq_of_ne hl]; rfl]
    rw [Pi.norm_single]
    have h2 : ‖(((1 - δ : ℝ) : ℂ) * c s - c s)‖ = δ * ‖c s‖ := by
      rw [show (((1 - δ : ℝ) : ℂ) * c s - c s) = (-(δ : ℂ)) * c s by push_cast; ring]
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt hδpos)]
    rw [h2, hcs]
    calc δ * B ≤ (ε / (2 * B)) * B := mul_le_mul_of_nonneg_right hδle hB.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith

/-- **The boundary decay of a fibre-Hölder datum on a polydisc.**

If `f` is continuous, vanishes for `B ≤ ‖· s‖` and is `α`-Hölder with constant `H` on
`polydisc 0 (Function.update Q s B)` (`B > 0`), then at an interior point `v` of that polydisc,
`‖f v‖ ≤ H (B - ‖v s‖) ^ α`: comparing `v` with a boundary point of the same fibre. -/
private lemma fiber_pair_boundary {n : ℕ} {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {s : Fin n}
    {f : (Fin n → ℂ) → ℂ} (hf : Continuous f)
    (hvan : ∀ y : Fin n → ℂ, B ≤ ‖y s‖ → f y = 0)
    {Q : Fin n → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hhol : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B),
      ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α)
    {v : Fin n → ℂ} (hv : v ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B)) :
    ‖f v‖ ≤ H * (B - ‖v s‖) ^ α := by
  rw [mem_polydisc_zero] at hv
  have hvs : ‖v s‖ < B := by simpa using hv s
  have hvl : ∀ l, l ≠ s → ‖v l‖ < Q l := by
    intro l hl
    have h3 := hv l
    rwa [Function.update_of_ne hl] at h3
  obtain ⟨c, hc1, hc2, hc3⟩ : ∃ c : Fin n → ℂ, (∀ l, l ≠ s → c l = v l) ∧ ‖c s‖ = B ∧
      ‖v - c‖ = B - ‖v s‖ := by
    by_cases hv0 : v s = 0
    · refine ⟨Function.update v s (B : ℂ), fun l hl => Function.update_of_ne hl _ _, ?_, ?_⟩
      · rw [Function.update_self, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
      · rw [← dist_eq_norm, dist_comm, dist_update_self, hv0, norm_zero, sub_zero, sub_zero,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    · have hpos : 0 < ‖v s‖ := norm_pos_iff.mpr hv0
      refine ⟨Function.update v s (((B / ‖v s‖ : ℝ) : ℂ) * v s),
        fun l hl => Function.update_of_ne hl _ _, ?_, ?_⟩
      · rw [Function.update_self, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hB.le hpos.le), div_mul_cancel₀ _ (ne_of_gt hpos)]
      · rw [← dist_eq_norm, dist_comm, dist_update_self]
        rw [show (((B / ‖v s‖ : ℝ) : ℂ) * v s) - v s
            = ((B / ‖v s‖ - 1 : ℝ) : ℂ) * v s by push_cast; ring]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [show B / ‖v s‖ - 1 = (B - ‖v s‖) / ‖v s‖ by field_simp]
        rw [abs_div, abs_of_nonneg hpos.le,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ B - ‖v s‖),
          div_mul_cancel₀ _ (ne_of_gt hpos)]
  have hclos := mem_closure_polydisc_update hB hvl hvs hc1 hc2
  have h0 : f c = 0 := hvan c (le_of_eq hc2.symm)
  have hvP : v ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B) := by
    rw [mem_polydisc_zero]
    intro l
    by_cases hl : l = s
    · subst hl; rw [Function.update_self]; exact hvs
    · rw [Function.update_of_ne hl]; exact hvl l hl
  have hmain := holder_norm_sub_le_closure hα hH hf hhol (subset_closure hvP) hclos
  rw [h0, sub_zero, hc3] at hmain
  exact hmain

/-- **The Hölder bound on a polydisc extends to all fibre points above a larger polydisc.**

This is the fibre-pair analysis needed by `dbarTransform_polydisc_bounds_aux`: the transform at a
point of the inner polydisc `polydisc 0 Q` reads the datum on the whole fibre, so the Hölder bound
on `polydisc 0 (Function.update Q s B)` has to be extended to arbitrary fibre points; the points
outside that polydisc are either in the vanishing region (`f = 0`, by `hvan`) or are compared with
a boundary point of the same fibre (by continuity and `fiber_pair_boundary`). -/
private lemma polydisc_fiber_pair_aux {n : ℕ} {α B : ℝ} (hα : 0 < α) (hB : 0 < B) {s : Fin n}
    {f : (Fin n → ℂ) → ℂ} (hf : Continuous f)
    (hvan : ∀ y : Fin n → ℂ, B ≤ ‖y s‖ → f y = 0)
    {Q : Fin n → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hhol : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B),
      ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α) :
    ∀ (x y : Fin n → ℂ), x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q →
      y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q →
      ∀ (a a' : Fin n → ℂ), (∀ l, l ≠ s → a l = x l) → (∀ l, l ≠ s → a' l = y l) →
      ‖f a - f a'‖ ≤ H * ‖a - a'‖ ^ α := by
  have hbd : ∀ v : Fin n → ℂ,
      v ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B) →
      ‖f v‖ ≤ H * (B - ‖v s‖) ^ α :=
    fun v hv => fiber_pair_boundary hα hB hf hvan hH hhol hv
  intro x y hx hy a a' ha ha'
  by_cases h1 : ‖a s‖ < B
  · by_cases h2 : ‖a' s‖ < B
    · exact hhol a (mem_polydisc_update_of_fiber hx ha h1) a'
        (mem_polydisc_update_of_fiber hy ha' h2)
    · rw [hvan a' (le_of_not_gt h2), sub_zero]
      refine le_trans (hbd a (mem_polydisc_update_of_fiber hx ha h1)) ?_
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ?_ hα.le) hH
      have h2' : B ≤ ‖a' s‖ := le_of_not_gt h2
      calc B - ‖a s‖ ≤ ‖a' s‖ - ‖a s‖ := by linarith
        _ ≤ ‖a' s - a s‖ := norm_sub_norm_le _ _
        _ ≤ ‖a' - a‖ := norm_le_pi_norm (a' - a) s
        _ = ‖a - a'‖ := norm_sub_rev _ _
  · by_cases h2 : ‖a' s‖ < B
    · rw [hvan a (le_of_not_gt h1), zero_sub, norm_neg]
      refine le_trans (hbd a' (mem_polydisc_update_of_fiber hy ha' h2)) ?_
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) ?_ hα.le) hH
      have h1' : B ≤ ‖a s‖ := le_of_not_gt h1
      calc B - ‖a' s‖ ≤ ‖a s‖ - ‖a' s‖ := by linarith
        _ ≤ ‖a s - a' s‖ := norm_sub_norm_le _ _
        _ ≤ ‖a - a'‖ := norm_le_pi_norm (a - a') s
    · rw [hvan a (le_of_not_gt h1), hvan a' (le_of_not_gt h2), sub_self, norm_zero]
      exact mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)

/-! ## The transform bounds on a polydisc -/

/-- **The one-variable Cauchy-type transform is bounded, with no loss of derivatives, on an inner
polydisc, against the size and Hölder constant of the datum on a larger polydisc.**

`Work.CR.Flat.Cauchy.dbarTransform R s f z = -(1/π) ∫_{‖w‖<R} f (z + w e_s)/w dw`; the estimates
are `dbarTransform_basic` applied to the pointwise bound and the fibre-pair bound supplied by
`hsup` and `polydisc_fiber_pair_aux`. -/
private lemma dbarTransform_polydisc_bounds_aux {n : ℕ} {α R B : ℝ} (hα : 0 < α) (hR : 0 < R)
    (hB : 0 < B) {s : Fin n} {f : (Fin n → ℂ) → ℂ} (hf : Continuous f)
    (hvan : ∀ y : Fin n → ℂ, B ≤ ‖y s‖ → f y = 0)
    {Q : Fin n → ℝ} {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hsup : ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B), ‖f z‖ ≤ A)
    (hhol : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B),
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (Function.update Q s B),
      ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α) :
    (∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
        ‖Work.CR.Flat.Cauchy.dbarTransform R s f z‖ ≤ 2 * R * A) ∧
    (∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      ∀ y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) Q,
      ‖Work.CR.Flat.Cauchy.dbarTransform R s f x - Work.CR.Flat.Cauchy.dbarTransform R s f y‖
        ≤ 2 * R * H * ‖x - y‖ ^ α) := by
  have hb : 0 ≤ B := hB.le
  have hmain := Work.CR.Flat.Cauchy.dbarTransform_basic (n := n) (ρ := R) (b := B) hR hb (j := s)
  constructor
  · intro z hz
    refine hmain.1 hf hvan A z fun y hy hyB => ?_
    by_cases hy' : ‖y s‖ < B
    · exact hsup y (mem_polydisc_update_of_fiber hz hy hy')
    · rw [hvan y (le_of_not_gt hy')]
      simpa using hA
  · intro x hx y hy
    refine hmain.2.1 hf hvan α H x y fun a a' ha ha' => ?_
    exact polydisc_fiber_pair_aux hα hB hf hvan hH hhol x y hx hy a a' ha ha'

/-! ## The main bound, with the constant exposed -/

/-- **The localised `C^{k,α}` bound for the Cauchy-type transform on a tracking polydisc, with the
explicit constant `4 * ∑ t, G.r t + 1`.**

This is the conclusion of `Work.NN.Core.TelTwoDF.dbarTransform_Eset_le` with the existential
constant exposed; the proof is a verbatim copy of that theorem's body with the `∃ C` wrapper
replaced by the concrete constant. -/
theorem dbarTransform_Eset_const {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ)
    (G : Work.NN.Core.TelTwoDF.Geom n) (s : Fin n) (g : (Fin n → ℂ) → ℂ)
    (hg : ContDiff ℝ (k : ℕ∞) g) (hsupp : ∀ y : Fin n → ℂ, G.b s ≤ ‖y s‖ → g y = 0) :
    Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform (G.r s) s g)
        (Work.NN.Core.TelTwoDF.Eset G ((s : ℕ) + 1))
      ≤ ENNReal.ofReal (4 * ∑ t : Fin n, G.r t + 1) *
          Work.CR.Flat.holderNorm k α g (Work.NN.Core.TelTwoDF.Eset G (s : ℕ)) := by
  have hR : 0 < G.r s := G.hr s
  have hB : 0 < G.b s := G.b_pos s
  have hCnz : ENNReal.ofReal (4 * ∑ t : Fin n, G.r t + 1) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have h1 : 0 ≤ ∑ t : Fin n, G.r t := Finset.sum_nonneg fun t _ => (G.hr t).le
    linarith
  by_cases htop : Work.CR.Flat.holderNorm k α g (Eset G (s : ℕ)) = ⊤
  · rw [htop, ENNReal.mul_top hCnz]
    exact le_top
  · have hfin : Work.CR.Flat.holderNorm k α g (Eset G (s : ℕ)) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hAfin : ∀ i, i ≤ k → Work.CR.Flat.iterDerivNorm i g (Eset G (s : ℕ)) < ⊤ := fun i hi =>
      lt_of_le_of_lt (Work.CR.Flat.iterDerivNorm_le_holderNorm k α g (Eset G (s : ℕ)) hi) hfin
    have hKfin : ∀ i, i ≤ k → Work.CR.Flat.holderSeminorm i α g (Eset G (s : ℕ)) < ⊤ := fun i hi =>
      lt_of_le_of_lt (Work.CR.Flat.holderSeminorm_le_holderNorm k α g (Eset G (s : ℕ)) hi) hfin
    let A : ℕ → ℝ := fun i => (Work.CR.Flat.iterDerivNorm i g (Eset G (s : ℕ))).toReal
    let K : ℕ → ℝ := fun i => (Work.CR.Flat.holderSeminorm i α g (Eset G (s : ℕ))).toReal
    have hAeq : ∀ i (hi : i ≤ k),
        ENNReal.ofReal (A i) = Work.CR.Flat.iterDerivNorm i g (Eset G (s : ℕ)) :=
      fun i hi => ENNReal.ofReal_toReal (ne_top_of_lt (hAfin i hi))
    have hKeq : ∀ i (hi : i ≤ k),
        ENNReal.ofReal (K i) = Work.CR.Flat.holderSeminorm i α g (Eset G (s : ℕ)) :=
      fun i hi => ENNReal.ofReal_toReal (ne_top_of_lt (hKfin i hi))
    have hAnn : ∀ i, 0 ≤ A i := fun i => ENNReal.toReal_nonneg
    have hKnn : ∀ i, 0 ≤ K i := fun i => ENNReal.toReal_nonneg
    have hΩopen : IsOpen (Eset G (s : ℕ)) := isOpen_Eset G (s : ℕ)
    have hAb : ∀ i, i ≤ k → ∀ y : Fin n → ℂ, y ∈ Eset G (s : ℕ) →
        ‖iteratedFDeriv ℝ i g y‖ ≤ A i := by
      intro i hi y hy
      have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g (Eset G (s : ℕ)) y‖
          ≤ Work.CR.Flat.iterDerivNorm i g (Eset G (s : ℕ)) := by
        rw [Work.CR.Flat.iterDerivNorm]
        exact le_iSup₂_of_le y hy le_rfl
      rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (s := Eset G (s : ℕ)) (f := g) i hΩopen) hy] at h1
      rw [← hAeq i hi] at h1
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
    have hKb : ∀ i, i ≤ k → ∀ x : Fin n → ℂ, x ∈ Eset G (s : ℕ) →
        ∀ y : Fin n → ℂ, y ∈ Eset G (s : ℕ) →
        ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ K i * ‖x - y‖ ^ α := by
      intro i hi x hx y hy
      rcases eq_or_ne x y with rfl | hne
      · simp [Real.zero_rpow (ne_of_gt hα0)]
      · have h1 : ENNReal.ofReal
            (‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ / ‖x - y‖ ^ α)
            ≤ Work.CR.Flat.holderSeminorm i α g (Eset G (s : ℕ)) := by
          have h := Work.CR.Flat.le_holderSeminorm i α g (Eset G (s : ℕ)) hx hy hne
          rwa [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
              (s := Eset G (s : ℕ)) (f := g) i hΩopen) hx,
            (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
              (s := Eset G (s : ℕ)) (f := g) i hΩopen) hy] at h
        rw [← hKeq i hi] at h1
        have h2 := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
        have hpos : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) α
        rwa [div_le_iff₀ hpos] at h2
    -- commutation with the derivatives
    have hcomm : ∀ i, i ≤ k → ∀ (v : Fin i → (Fin n → ℂ)) (z : Fin n → ℂ),
        iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) z v
          = dbarTransform (G.r s) s (fun y => iteratedFDeriv ℝ i g y v) z :=
      fun i hi v z => iteratedFDeriv_dbarTransform_eq hB.le s hg hsupp i hi v z
    -- the two bounds furnished by the polydisc estimate for the scalar datum `y ↦ D^i g y v`
    have hT : ∀ i, i ≤ k → ∀ v : Fin i → (Fin n → ℂ),
        (∀ z ∈ Eset G ((s : ℕ) + 1),
            ‖dbarTransform (G.r s) s (fun y => iteratedFDeriv ℝ i g y v) z‖
              ≤ 2 * G.r s * (A i * ∏ l, ‖v l‖)) ∧
        (∀ x ∈ Eset G ((s : ℕ) + 1), ∀ y ∈ Eset G ((s : ℕ) + 1),
            ‖dbarTransform (G.r s) s (fun y' => iteratedFDeriv ℝ i g y' v) x
              - dbarTransform (G.r s) s (fun y' => iteratedFDeriv ℝ i g y' v) y‖
              ≤ 2 * G.r s * (K i * ∏ l, ‖v l‖) * ‖x - y‖ ^ α) := by
      intro i hi v
      have hP : 0 ≤ ∏ l, ‖v l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
      have hc : Continuous (fun y : Fin n → ℂ => iteratedFDeriv ℝ i g y v) :=
        continuous_iteratedFDeriv_apply hg hi v
      have hvan' : ∀ y : Fin n → ℂ, G.b s ≤ ‖y s‖ → iteratedFDeriv ℝ i g y v = 0 :=
        fun y hy => by
          rw [iteratedFDeriv_eq_zero_of_ge hB hi hg hsupp y hy]; simp
      have hsup' : ∀ z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ)
            (Function.update (Erad G ((s : ℕ) + 1)) s (G.b s)),
          ‖iteratedFDeriv ℝ i g z v‖ ≤ A i * ∏ l, ‖v l‖ := by
        intro z hz
        have hz' : z ∈ Eset G (s : ℕ) := mem_Eset_of_mem_update G s hz
        calc ‖iteratedFDeriv ℝ i g z v‖ ≤ ‖iteratedFDeriv ℝ i g z‖ * ∏ l, ‖v l‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ ≤ A i * ∏ l, ‖v l‖ := mul_le_mul_of_nonneg_right (hAb i hi z hz') hP
      have hhol' : ∀ x ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ)
            (Function.update (Erad G ((s : ℕ) + 1)) s (G.b s)),
          ∀ y ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ)
            (Function.update (Erad G ((s : ℕ) + 1)) s (G.b s)),
          ‖iteratedFDeriv ℝ i g x v - iteratedFDeriv ℝ i g y v‖
            ≤ (K i * ∏ l, ‖v l‖) * ‖x - y‖ ^ α := by
        intro x hx y hy
        have hx' : x ∈ Eset G (s : ℕ) := mem_Eset_of_mem_update G s hx
        have hy' : y ∈ Eset G (s : ℕ) := mem_Eset_of_mem_update G s hy
        have h1 : ‖(iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y) v‖
            ≤ ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ * ∏ l, ‖v l‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        rw [ContinuousMultilinearMap.sub_apply] at h1
        calc ‖iteratedFDeriv ℝ i g x v - iteratedFDeriv ℝ i g y v‖
            ≤ ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ * ∏ l, ‖v l‖ := h1
          _ ≤ (K i * ‖x - y‖ ^ α) * ∏ l, ‖v l‖ :=
              mul_le_mul_of_nonneg_right (hKb i hi x hx' y hy') hP
          _ = (K i * ∏ l, ‖v l‖) * ‖x - y‖ ^ α := by ring
      exact dbarTransform_polydisc_bounds_aux hα0 hR hB hc hvan'
        (mul_nonneg (hAnn i) hP) (mul_nonneg (hKnn i) hP) hsup' hhol'
    have hN : ∀ i, i ≤ k →
        Work.CR.Flat.iterDerivNorm i (fun z => dbarTransform (G.r s) s g z)
            (Eset G ((s : ℕ) + 1))
          ≤ ENNReal.ofReal (2 * G.r s) * Work.CR.Flat.iterDerivNorm i g (Eset G (s : ℕ)) := by
      intro i hi
      rw [Work.CR.Flat.iterDerivNorm]
      refine iSup₂_le fun x hx => ?_
      rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Eset G ((s : ℕ) + 1))
        (f := fun z => dbarTransform (G.r s) s g z) i (isOpen_Eset G ((s : ℕ) + 1))) hx]
      have hbnd : ‖iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) x‖
          ≤ 2 * G.r s * A i := by
        refine ContinuousMultilinearMap.opNorm_le_bound (M := 2 * G.r s * A i) (by positivity)
          fun v => ?_
        calc ‖iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) x v‖
            = ‖dbarTransform (G.r s) s (fun y => iteratedFDeriv ℝ i g y v) x‖ := by
              rw [hcomm i hi v x]
          _ ≤ 2 * G.r s * (A i * ∏ l, ‖v l‖) := (hT i hi v).1 x hx
          _ = 2 * G.r s * A i * ∏ l, ‖v l‖ := by ring
      calc ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) x‖
          ≤ ENNReal.ofReal (2 * G.r s * A i) := ENNReal.ofReal_le_ofReal hbnd
        _ = ENNReal.ofReal (2 * G.r s) * ENNReal.ofReal (A i) := ENNReal.ofReal_mul (by positivity)
        _ = ENNReal.ofReal (2 * G.r s) * Work.CR.Flat.iterDerivNorm i g (Eset G (s : ℕ)) := by
            rw [hAeq i hi]
    have hH : ∀ i, i ≤ k →
        Work.CR.Flat.holderSeminorm i α (fun z => dbarTransform (G.r s) s g z)
            (Eset G ((s : ℕ) + 1))
          ≤ ENNReal.ofReal (2 * G.r s) * Work.CR.Flat.holderSeminorm i α g (Eset G (s : ℕ)) := by
      intro i hi
      rw [Work.CR.Flat.holderSeminorm]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Eset G ((s : ℕ) + 1))
            (f := fun z => dbarTransform (G.r s) s g z) i (isOpen_Eset G ((s : ℕ) + 1))) hx,
          (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Eset G ((s : ℕ) + 1))
            (f := fun z => dbarTransform (G.r s) s g z) i (isOpen_Eset G ((s : ℕ) + 1))) hy]
      have hbnd : ‖iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) x
            - iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) y‖
          ≤ (2 * G.r s * K i) * ‖x - y‖ ^ α := by
        refine ContinuousMultilinearMap.opNorm_le_bound (M := (2 * G.r s * K i) * ‖x - y‖ ^ α)
          (by positivity) fun v => ?_
        have hP : 0 ≤ ∏ l, ‖v l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
        rw [ContinuousMultilinearMap.sub_apply, hcomm i hi v x, hcomm i hi v y]
        calc ‖dbarTransform (G.r s) s (fun y' => iteratedFDeriv ℝ i g y' v) x
              - dbarTransform (G.r s) s (fun y' => iteratedFDeriv ℝ i g y' v) y‖
            ≤ 2 * G.r s * (K i * ∏ l, ‖v l‖) * ‖x - y‖ ^ α := (hT i hi v).2 x hx y hy
          _ = (2 * G.r s * K i * ‖x - y‖ ^ α) * ∏ l, ‖v l‖ := by ring
      have hpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      calc ENNReal.ofReal (‖iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) x
            - iteratedFDeriv ℝ i (fun z => dbarTransform (G.r s) s g z) y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (2 * G.r s * K i) :=
            ENNReal.ofReal_le_ofReal (by rw [div_le_iff₀ hpos]; exact hbnd)
        _ = ENNReal.ofReal (2 * G.r s) * ENNReal.ofReal (K i) := ENNReal.ofReal_mul (by positivity)
        _ = ENNReal.ofReal (2 * G.r s) * Work.CR.Flat.holderSeminorm i α g (Eset G (s : ℕ)) := by
            rw [hKeq i hi]
    have hle : 2 * G.r s ≤ 4 * ∑ t : Fin n, G.r t + 1 := by
      have h1 : G.r s ≤ ∑ t : Fin n, G.r t :=
        Finset.single_le_sum (fun t _ => (G.hr t).le) (Finset.mem_univ s)
      linarith
    calc Work.CR.Flat.holderNorm k α (fun z => dbarTransform (G.r s) s g z)
          (Eset G ((s : ℕ) + 1))
        = ∑ i ∈ Finset.range (k + 1),
            (Work.CR.Flat.iterDerivNorm i (fun z => dbarTransform (G.r s) s g z)
                (Eset G ((s : ℕ) + 1))
              + Work.CR.Flat.holderSeminorm i α (fun z => dbarTransform (G.r s) s g z)
                (Eset G ((s : ℕ) + 1))) := rfl
      _ ≤ ∑ i ∈ Finset.range (k + 1),
            ENNReal.ofReal (2 * G.r s) *
              (Work.CR.Flat.iterDerivNorm i g (Eset G (s : ℕ))
                + Work.CR.Flat.holderSeminorm i α g (Eset G (s : ℕ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [mul_add]
          exact add_le_add (hN i hik) (hH i hik)
      _ = ENNReal.ofReal (2 * G.r s) * Work.CR.Flat.holderNorm k α g (Eset G (s : ℕ)) := by
          rw [Work.CR.Flat.holderNorm, Finset.mul_sum]
      _ ≤ ENNReal.ofReal (4 * ∑ t : Fin n, G.r t + 1) *
            Work.CR.Flat.holderNorm k α g (Eset G (s : ℕ)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl

end Work.NN.Newton.FTs2
