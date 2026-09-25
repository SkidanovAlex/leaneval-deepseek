/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The parameterised `(0,2)`-telescoping solves the equation

Adapts `Submission/Work/NN/Final/uS2_solves.lean` to the parametric cutoffs: the per-stage identity
`∂̄_a (uPsi G η s)_b - ∂̄_b (uPsi G η s)_a = (uD G η s)_{ab} - (uD G η (s+1))_{ab}` on the tracking
region, and the telescoping sum giving `∂̄_a (S2 G η)_b - ∂̄_b (S2 G η)_a = η_{ab}` on the solving
polydisc `solveSet G`, for data which are `∂̄`-closed on `{∀ k, ‖z k‖ < G.b k}`.
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Final.TelAux

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Finset

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-- The one-coordinate identity behind the telescoping: the transform of `kappa · ∂̄_s D` plus the
transform of `kappabar · D` is `D`. -/
lemma TL_kappa_dbarCoord_add (G : Geom n) {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) {z : Fin n → ℂ} (hzs : ‖z s‖ < G.a s) :
    TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y) z
      + TL G s (fun y => kappabar G s y * D y) z = D z := by
  have hG : ContDiff ℝ 1 (fun y => kappa G s y * D y) :=
    ((contDiff_kappa G s).of_le (le_infty'' 1)).mul hD
  have hsum : (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y)
      + (fun y : Fin n → ℂ => kappabar G s y * D y)
      = fun y => Work.CR.Flat.dbarCoord s (fun y' => kappa G s y' * D y') y := by
    funext y
    rw [Pi.add_apply,
      Work.CR.Flat.Polydisc.dbarCoord_mul s (kappa G s) D y
        ((contDiff_kappa G s).contDiffAt.differentiableAt (by simp))
        ((hD.differentiable one_ne_zero).differentiableAt),
      dbarCoord_kappa G s y]
    ring
  have hcont1 : Continuous (fun y : Fin n → ℂ => kappa G s y * Work.CR.Flat.dbarCoord s D y) :=
    (contDiff_kappa G s).continuous.mul (continuous_dbarCoord hD s)
  have hcont2 : Continuous (fun y : Fin n → ℂ => kappabar G s y * D y) :=
    (contDiff_kappabar G s).continuous.mul hD.continuous
  rw [show TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y) z
        + TL G s (fun y => kappabar G s y * D y) z
      = (TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord s D y)
        + TL G s (fun y => kappabar G s y * D y)) z from rfl,
    ← map_add, hsum, TL_eq G s (continuous_dbarCoord hG s)]
  have hsupp : ∀ y : Fin n → ℂ, G.r s / 2 ≤ ‖y s‖ → kappa G s y * D y = 0 := fun y hy => by
    rw [kappa_eq_zero G s (le_trans (G.hbr s) hy), zero_mul]
  have hzs' : ‖z s‖ < G.r s / 2 :=
    lt_of_lt_of_le hzs (le_trans (G.hab s).le (G.hbr s))
  rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (G.hr s) s hG hsupp hzs']
  rw [kappa_eq_one G s (le_of_lt hzs), one_mul]

/-- The difference of two transforms is the transform of the difference. -/
lemma TL_sub (G : Geom n) (s : Fin n) (g h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    TL G s g z - TL G s h z = TL G s (g - h) z := by
  rw [show TL G s g z - TL G s h z = (TL G s g - TL G s h) z from rfl, map_sub]

/-- The sum of two transforms is the transform of the sum. -/
lemma TL_add (G : Geom n) (s : Fin n) (g h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    TL G s (g + h) z = TL G s g z + TL G s h z := by
  rw [map_add]; rfl

/-- The per-term computation: the `(0,2)`-form of `uPsi G η s` is `uD G η s - uD G η (s+1)`. -/
lemma dbarCoord_uPsi_sub (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, (∀ k : Fin n, ‖z k‖ < G.b k) →
      Work.CR.Flat.dbarCoord i (η l m') z - Work.CR.Flat.dbarCoord l (η i m') z
        + Work.CR.Flat.dbarCoord m' (η i l) z = 0)
    (s : Fin n) (a b : Fin n) {z : Fin n → ℂ} (hz : z ∈ solveSet G) :
    Work.CR.Flat.dbarCoord a (uPsi G η s b) z - Work.CR.Flat.dbarCoord b (uPsi G η s a) z
      = uD G η (s : ℕ) a b z - uStep G s (uD G η (s : ℕ)) a b z := by
  have hsn : (s : ℕ) ≤ n := le_of_lt s.isLt
  have hzr : ∀ l, ‖z l‖ < G.e l := hz
  have hzs : ‖z s‖ < G.a s := lt_trans (hzr s) (G.hea s)
  have hD : ∀ i l, ContDiff ℝ 1 (uD G η (s : ℕ) i l) :=
    fun i l => uD_contDiff G hη (s : ℕ) hsn i l
  have hantiD : ∀ i l w, uD G η (s : ℕ) i l w = - uD G η (s : ℕ) l i w :=
    fun i l w => uD_antisymm G hanti (s : ℕ) i l w
  have hss_pt : ∀ w : Fin n → ℂ, uD G η (s : ℕ) s s w = 0 :=
    fun w => add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (hantiD s s w))
  have hss_fun : uD G η (s : ℕ) s s = 0 := funext hss_pt
  have hclosed := uD_closed_E G hη hanti hcl (s : ℕ) hsn
  have h1 : Work.CR.Flat.dbarCoord a (uPsi G η s b) z
      = if a = s then uD G η (s : ℕ) s b z
        else TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y) z := by
    show Work.CR.Flat.dbarCoord a
      (TL G s (fun y => kappa G s y * uD G η (s : ℕ) s b y)) z = _
    exact dbarCoord_TL_kappa G (hD s b) hzs a
  have h2 : Work.CR.Flat.dbarCoord b (uPsi G η s a) z
      = if b = s then uD G η (s : ℕ) s a z
        else TL G s (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y) z := by
    show Work.CR.Flat.dbarCoord b
      (TL G s (fun y => kappa G s y * uD G η (s : ℕ) s a y)) z = _
    exact dbarCoord_TL_kappa G (hD s a) hzs b
  rw [h1, h2, uStep_apply]
  have hzero_a : TL G s
      (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s s) y) z = 0 := by
    have hfun : (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s s) y)
        = (0 : (Fin n → ℂ) → ℂ) := by
      funext y
      simp [hss_fun, dbarCoord_zero]
    rw [hfun, map_zero]
    rfl
  have hzero_b : TL G s
      (fun y => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s s) y) z = 0 := by
    have hfun : (fun y => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s s) y)
        = (0 : (Fin n → ℂ) → ℂ) := by
      funext y
      simp [hss_fun, dbarCoord_zero]
    rw [hfun, map_zero]
    rfl
  by_cases ha : a = s
  · by_cases hb : b = s
    · rw [ite_eq_left ha, ite_eq_left hb, ite_eq_left (Or.inl ha), kappa_eq_one G s (le_of_lt hzs),
        ha, hb, hss_pt z]
      ring
    · rw [ite_eq_left ha, ite_eq_right hb, ite_eq_left (Or.inl ha),
        kappa_eq_one G s (le_of_lt hzs), ha, hzero_a]
      ring
  · by_cases hb : b = s
    · rw [ite_eq_right ha, ite_eq_left hb, ite_eq_left (Or.inr hb),
        kappa_eq_one G s (le_of_lt hzs), hb, hzero_b, hantiD a s z]
      ring
    · rw [ite_eq_right ha, ite_eq_right hb,
        ite_eq_right (fun h : a = s ∨ b = s => h.elim ha hb),
        kappa_eq_one G s (le_of_lt hzs), sub_self, zero_mul, zero_add]
      have hzero : TL G s (fun y => kappa G s y
          * (Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
            - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
            - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)) z = 0 := by
        have hcont : Continuous (fun y : Fin n → ℂ => kappa G s y
            * (Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
              - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
              - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)) :=
          (contDiff_kappa G s).continuous.mul
            (((continuous_dbarCoord (hD s b) a).sub (continuous_dbarCoord (hD s a) b)).sub
              (continuous_dbarCoord (hD a b) s))
        rw [TL_eq G s hcont]
        refine Work.CR.Flat.Cauchy.dbarTransform_eq_zero_of_fiber (ρ := G.r s) (j := s)
          (fun y hy => ?_)
        by_cases hyc : ‖y s‖ < G.b s
        · have hyE : y ∈ E G (s : ℕ) := by
            intro m
            refine ⟨?_, ?_⟩
            · intro hm
              have hms : m ≠ s := by intro h; rw [h] at hm; omega
              rw [hy m hms]
              exact hzr m
            · intro hm
              rcases eq_or_ne m s with hms | hms
              · rw [hms]; exact hyc
              · rw [hy m hms]
                exact lt_trans (hzr m) (G.e_lt_b m)
          have hcl' := hclosed s a b y hyE
          have hZ : Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
              - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
              - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y = 0 := by
            linear_combination -hcl'
          rw [hZ, mul_zero]
        · rw [kappa_eq_zero G s (le_of_not_gt hyc), zero_mul]
      have hAB : (fun y : Fin n → ℂ => kappa G s y * Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y)
          - (fun y => kappa G s y * Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y)
          = (fun y => kappa G s y * Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)
            + (fun y => kappa G s y
                * (Work.CR.Flat.dbarCoord a (uD G η (s : ℕ) s b) y
                  - Work.CR.Flat.dbarCoord b (uD G η (s : ℕ) s a) y
                  - Work.CR.Flat.dbarCoord s (uD G η (s : ℕ) a b) y)) := by
        funext y
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      rw [TL_sub, hAB, TL_add, hzero, add_zero]
      have hself := TL_kappa_dbarCoord_add G (s := s) (D := uD G η (s : ℕ) a b) (hD a b) hzs
      linear_combination hself

/-- **The parameterised telescoping solves the `(0,2)`-equation** on `solveSet G`, for data which
are antisymmetric and `∂̄`-closed on `{∀ k, ‖z k‖ < G.b k}`. -/
theorem S2_solves (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, (∀ k : Fin n, ‖z k‖ < G.b k) →
      Work.CR.Flat.dbarCoord i (η l m') z - Work.CR.Flat.dbarCoord l (η i m') z
        + Work.CR.Flat.dbarCoord m' (η i l) z = 0) :
    ∀ a b : Fin n, ∀ z : Fin n → ℂ, z ∈ solveSet G →
      Work.CR.Flat.dbarCoord a (S2 G η b) z - Work.CR.Flat.dbarCoord b (S2 G η a) z = η a b z := by
  intro a b z hz
  have hzr : ∀ l, ‖z l‖ < G.e l := hz
  have hdiff : ∀ (s l : Fin n), DifferentiableAt ℝ (uPsi G η s l) z := by
    intro s l
    have hs : (s : ℕ) ≤ n := le_of_lt s.isLt
    have hD : ContDiff ℝ 1 (uD G η (s : ℕ) s l) := uD_contDiff G hη (s : ℕ) hs s l
    have hCd : ContDiff ℝ 1 (uPsi G η s l) := by
      show ContDiff ℝ 1 (TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y))
      exact contDiff_TL G (((contDiff_kappa G s).of_le (le_infty'' 1)).mul hD)
        (fun y hy => by rw [kappa_eq_zero G s hy, zero_mul])
    exact (hCd.differentiable one_ne_zero).differentiableAt
  have h1 : Work.CR.Flat.dbarCoord a (S2 G η b) z
      = ∑ s : Fin n, Work.CR.Flat.dbarCoord a (uPsi G η s b) z := by
    rw [show S2 G η b = fun w => ∑ s : Fin n, uPsi G η s b w from by
      funext w; simp [S2_apply]]
    exact Work.NN.Final.dbarCoord_finset_sum Finset.univ (fun s w => uPsi G η s b w) a z
      (fun s _ => hdiff s b)
  have h2 : Work.CR.Flat.dbarCoord b (S2 G η a) z
      = ∑ s : Fin n, Work.CR.Flat.dbarCoord b (uPsi G η s a) z := by
    rw [show S2 G η a = fun w => ∑ s : Fin n, uPsi G η s a w from by
      funext w; simp [S2_apply]]
    exact Work.NN.Final.dbarCoord_finset_sum Finset.univ (fun s w => uPsi G η s a w) b z
      (fun s _ => hdiff s a)
  have hterm : ∀ s : Fin n, Work.CR.Flat.dbarCoord a (uPsi G η s b) z
      - Work.CR.Flat.dbarCoord b (uPsi G η s a) z
      = uD G η (s : ℕ) a b z - uD G η ((s : ℕ) + 1) a b z := by
    intro s
    have hstep : uStep G s (uD G η (s : ℕ)) a b z = uD G η ((s : ℕ) + 1) a b z := by
      rw [uD_succ_of_lt G η s.isLt]
    rw [dbarCoord_uPsi_sub G hη hanti hcl s a b hz, hstep]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [Fin.sum_univ_eq_sum_range (fun m => uD G η m a b z - uD G η (m + 1) a b z) n,
    Finset.sum_range_sub' (fun m => uD G η m a b z) n, uD_zero,
    uD_vanish G hη n le_rfl a b (Or.inl a.isLt) z (fun k _ => lt_trans (hzr k) (G.hea k)),
    sub_zero]

end Work.NN.Core.TelTwoDF
