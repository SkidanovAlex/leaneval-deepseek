import Mathlib
import Submission.Work.NN.Final.twoRec

noncomputable section
open scoped NNReal ENNReal ContDiff
open MeasureTheory Set Finset

namespace Work.NN.Final
open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## Auxiliary lemmas for `uS2_solves` -/

/-- Every point of `solveSet` lies in the tracking region `E n s` for every `s`. -/
lemma mem_E_of_solveSet {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ solveSet) (s : ℕ) : z ∈ E n s := by
  have hz' : ∀ l, ‖z l‖ < eqRad := mem_solveSet.mp hz
  intro m
  refine ⟨fun _ => hz' m, fun _ => ?_⟩
  exact lt_trans (hz' m) (lt_trans eqRad_lt_cutIn cutIn_lt_cutOut)

/-- The one-coordinate identity behind the telescoping: for a `C¹` function `D` and
`‖z s‖ < cutIn`, the Cauchy transform of `c_s ∂̄_s D` plus the transform of `b_s D` is `D`. -/
lemma dTLM_cutF_dbarCoord_add {n : ℕ} {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) {z : Fin n → ℂ} (hzs : ‖z s‖ < cutIn) :
    dTLM s (fun y => cutF s y * dbarCoord s D y) z
      + dTLM s (fun y => cutFbar s y * D y) z = D z := by
  have hG : ContDiff ℝ 1 (fun y => cutF s y * D y) :=
    ((contDiff_cutF s).of_le (by exact_mod_cast le_top)).mul hD
  have hsum : (fun y => cutF s y * dbarCoord s D y)
      + (fun y : Fin n → ℂ => cutFbar s y * D y)
      = fun y => dbarCoord s (fun y' => cutF s y' * D y') y := by
    funext y
    rw [Pi.add_apply,
      Work.CR.Flat.Polydisc.dbarCoord_mul s (cutF s) D y
        ((contDiff_cutF s).contDiffAt.differentiableAt (by simp))
        ((hD.differentiable one_ne_zero).differentiableAt),
      dbarCoord_cutF s y]
    ring
  change ((dTLM s) (fun y => cutF s y * dbarCoord s D y)
      + (dTLM s) (fun y => cutFbar s y * D y)) z = D z
  rw [← map_add, hsum, dTLM_eq (continuous_dbarCoord hG s)]
  have hsupp : ∀ y : Fin n → ℂ, trRho / 2 ≤ ‖y s‖ → cutF s y * D y = 0 := by
    intro y hy
    rw [← cutOut_eq_half_trRho] at hy
    rw [cutF_eq_zero hy, zero_mul]
  have hzs' : ‖z s‖ < trRho / 2 := by
    rw [← cutOut_eq_half_trRho]; exact lt_trans hzs cutIn_lt_cutOut
  rw [dbarTransform_dbarCoord_self (ρ := trRho) trRho_pos s hG hsupp hzs',
    cutF_eq_one (le_of_lt hzs), one_mul]

/-- The difference of two transforms, pushed inside. -/
lemma tLM_sub {n : ℕ} (j : Fin n) (g h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    dTLM j g z - dTLM j h z = dTLM j (g - h) z := by
  rw [show dTLM j g z - dTLM j h z = (dTLM j g - dTLM j h) z from rfl, map_sub]

/-- The sum of two transforms, pushed inside. -/
lemma tLM_add {n : ℕ} (j : Fin n) (g h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    dTLM j (g + h) z = dTLM j g z + dTLM j h z := by
  rw [map_add]; rfl

/-- The per-term computation: the `(0,2)`-form of `Ψ^{(s)}` is `D^{(s)} - D^{(s+1)}`. -/
lemma dbarCoord_uPsi_sub {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, z ∈ polydisc 0 (fun _ => 1) →
      dbarCoord i (η l m') z - dbarCoord l (η i m') z + dbarCoord m' (η i l) z = 0)
    (s : Fin n) (a b : Fin n) {z : Fin n → ℂ} (hz : z ∈ solveSet) :
    dbarCoord a (uPsi η s b) z - dbarCoord b (uPsi η s a) z
      = uD η (s : ℕ) a b z - uStep s (uD η (s : ℕ)) a b z := by
  have hsn : (s : ℕ) ≤ n := le_of_lt s.isLt
  have hzr : ∀ l, ‖z l‖ < eqRad := mem_solveSet.mp hz
  have hzs : ‖z s‖ < cutIn := lt_trans (hzr s) eqRad_lt_cutIn
  have hcut : cutF s z = 1 := cutF_eq_one (le_of_lt hzs)
  have hD : ∀ i l, ContDiff ℝ 1 (uD η (s:ℕ) i l) := fun i l => uD_contDiff hη (s:ℕ) hsn i l
  have hantiD : ∀ i l w, uD η (s:ℕ) i l w = - uD η (s:ℕ) l i w :=
    fun i l w => uD_antisymm hanti (s:ℕ) i l w
  have hss_pt : ∀ w : Fin n → ℂ, uD η (s:ℕ) s s w = 0 :=
    fun w => add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (hantiD s s w))
  have hss_fun : uD η (s:ℕ) s s = 0 := funext hss_pt
  have hclosed := uD_closed hη hanti hcl (s:ℕ) hsn
  have h1 : dbarCoord a (uPsi η s b) z
      = if a = s then uD η (s:ℕ) s b z
        else dTLM s (fun y => cutF s y * dbarCoord a (uD η (s:ℕ) s b) y) z := by
    show dbarCoord a (dTLM s (fun y => cutF s y * uD η (s:ℕ) s b y)) z = _
    exact dbarCoord_dTLM_cutF (hD s b) hzs a
  have h2 : dbarCoord b (uPsi η s a) z
      = if b = s then uD η (s:ℕ) s a z
        else dTLM s (fun y => cutF s y * dbarCoord b (uD η (s:ℕ) s a) y) z := by
    show dbarCoord b (dTLM s (fun y => cutF s y * uD η (s:ℕ) s a y)) z = _
    exact dbarCoord_dTLM_cutF (hD s a) hzs b
  rw [h1, h2, uStep_apply]
  have hzero_a : dTLM s (fun y => cutF s y * dbarCoord b (uD η (s:ℕ) s s) y) z = 0 := by
    have hfun : (fun y => cutF s y * dbarCoord b (uD η (s:ℕ) s s) y) = (0 : (Fin n → ℂ) → ℂ) := by
      funext y
      simp [hss_fun, dbarCoord_zero']
    rw [hfun, map_zero]
    rfl
  have hzero_b : dTLM s (fun y => cutF s y * dbarCoord a (uD η (s:ℕ) s s) y) z = 0 := by
    have hfun : (fun y => cutF s y * dbarCoord a (uD η (s:ℕ) s s) y) = (0 : (Fin n → ℂ) → ℂ) := by
      funext y
      simp [hss_fun, dbarCoord_zero']
    rw [hfun, map_zero]
    rfl
  by_cases ha : a = s
  · by_cases hb : b = s
    · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (Or.inl ha), hcut, ha, hb, hss_pt z]
      ring
    · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_left (Or.inl ha), hcut, ha, hzero_a]
      ring
  · by_cases hb : b = s
    · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_left (Or.inr hb), hcut, hb, hzero_b, hantiD a s z]
      ring
    · rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right (fun h : a = s ∨ b = s => h.elim ha hb),
        hcut, sub_self, zero_mul, zero_add]
      have hzero : dTLM s (fun y => cutF s y * (dbarCoord a (uD η (s:ℕ) s b) y
          - dbarCoord b (uD η (s:ℕ) s a) y - dbarCoord s (uD η (s:ℕ) a b) y)) z = 0 := by
        have hcont : Continuous (fun y : Fin n → ℂ => cutF s y * (dbarCoord a (uD η (s:ℕ) s b) y
            - dbarCoord b (uD η (s:ℕ) s a) y - dbarCoord s (uD η (s:ℕ) a b) y)) :=
          (contDiff_cutF s).continuous.mul
            (((continuous_dbarCoord (hD s b) a).sub (continuous_dbarCoord (hD s a) b)).sub
              (continuous_dbarCoord (hD a b) s))
        rw [dTLM_eq hcont]
        refine dbarTransform_eq_zero_of_fiber (j := s) (fun y hy => ?_)
        by_cases hyc : ‖y s‖ < cutOut
        · have hyE : y ∈ E n (s:ℕ) := by
            intro m
            refine ⟨?_, ?_⟩
            · intro hm
              have hms : m ≠ s := by intro h; rw [h] at hm; exact absurd hm (lt_irrefl _)
              rw [hy m hms]; exact hzr m
            · intro hm
              rcases eq_or_ne m s with hms | hms
              · rw [hms]; exact hyc
              · rw [hy m hms]; exact lt_trans (hzr m) (lt_trans eqRad_lt_cutIn cutIn_lt_cutOut)
          have hcl' := hclosed s a b y hyE
          have hZ : dbarCoord a (uD η (s:ℕ) s b) y - dbarCoord b (uD η (s:ℕ) s a) y
              - dbarCoord s (uD η (s:ℕ) a b) y = 0 := by
            linear_combination -hcl'
          rw [hZ, mul_zero]
        · rw [cutF_eq_zero (le_of_not_gt hyc), zero_mul]
      have hAB : (fun y : Fin n → ℂ => cutF s y * dbarCoord a (uD η (s:ℕ) s b) y)
          - (fun y => cutF s y * dbarCoord b (uD η (s:ℕ) s a) y)
          = (fun y => cutF s y * dbarCoord s (uD η (s:ℕ) a b) y)
            + (fun y => cutF s y * (dbarCoord a (uD η (s:ℕ) s b) y
                - dbarCoord b (uD η (s:ℕ) s a) y - dbarCoord s (uD η (s:ℕ) a b) y)) := by
        funext y
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [tLM_sub, hAB, tLM_add, hzero, add_zero]
      have hself := dTLM_cutF_dbarCoord_add (s := s) (D := uD η (s:ℕ) a b) (hD a b) hzs
      linear_combination hself

theorem uS2_solves {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, z ∈ Work.CR.Flat.polydisc 0 (fun _ => 1) →
      Work.CR.Flat.dbarCoord i (η l m') z - Work.CR.Flat.dbarCoord l (η i m') z
        + Work.CR.Flat.dbarCoord m' (η i l) z = 0) :
    ∀ a b : Fin n, ∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.Cauchy.solveSet →
      Work.CR.Flat.dbarCoord a (Work.NN.Final.uS2 η b) z
        - Work.CR.Flat.dbarCoord b (Work.NN.Final.uS2 η a) z = η a b z := by
  intro a b z hz
  have hzr : ∀ l, ‖z l‖ < eqRad := mem_solveSet.mp hz
  have hdiff : ∀ (s l : Fin n), DifferentiableAt ℝ (uPsi η s l) z := by
    intro s l
    have hs : (s : ℕ) ≤ n := le_of_lt s.isLt
    have hD : ContDiff ℝ 1 (uD η (s:ℕ) s l) := uD_contDiff hη (s:ℕ) hs s l
    have hCd : ContDiff ℝ 1 (uPsi η s l) := by
      show ContDiff ℝ 1 (dTLM s (fun y => cutF s y * uD η (s:ℕ) s l y))
      exact contDiff_dTLM (((contDiff_cutF s).of_le (by exact_mod_cast le_top)).mul hD)
        (fun y hy => by rw [cutF_eq_zero hy, zero_mul])
    exact (hCd.differentiable one_ne_zero).differentiableAt
  have h1 : dbarCoord a (uS2 η b) z = ∑ s : Fin n, dbarCoord a (uPsi η s b) z := by
    rw [show uS2 η b = fun w => ∑ s : Fin n, uPsi η s b w from by
      funext w; simp [uS2, Finset.sum_apply]]
    exact dbarCoord_finset_sum a Finset.univ (fun s w => uPsi η s b w) z
      (fun s _ => hdiff s b)
  have h2 : dbarCoord b (uS2 η a) z = ∑ s : Fin n, dbarCoord b (uPsi η s a) z := by
    rw [show uS2 η a = fun w => ∑ s : Fin n, uPsi η s a w from by
      funext w; simp [uS2, Finset.sum_apply]]
    exact dbarCoord_finset_sum b Finset.univ (fun s w => uPsi η s a w) z
      (fun s _ => hdiff s a)
  have hterm : ∀ s : Fin n, dbarCoord a (uPsi η s b) z - dbarCoord b (uPsi η s a) z
      = uD η (s:ℕ) a b z - uD η ((s:ℕ)+1) a b z := by
    intro s
    have hstep : uStep s (uD η (s:ℕ)) a b z = uD η ((s:ℕ)+1) a b z := by
      rw [uD_succ_of_lt η s.isLt]
    rw [dbarCoord_uPsi_sub hη hanti hcl s a b hz, hstep]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [Fin.sum_univ_eq_sum_range (fun m => uD η m a b z - uD η (m + 1) a b z) n,
    Finset.sum_range_sub' (fun m => uD η m a b z) n, uD_zero,
    uD_vanish hη n le_rfl a b (Or.inl a.isLt) z (fun k _ => lt_trans (hzr k) eqRad_lt_cutIn),
    sub_zero]

end Work.NN.Final
