/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The invariants of the parameterised `(0,2)`-recursion

Adapts `Submission/Work/NN/Final/twoRec.lean` to the parametric cutoffs: the regularity of the
stages, antisymmetry, the vanishing of the stages on the already-processed coordinates, the
`∂̄`-closedness of the stages on the tracking regions, and the linearity of the recursion.
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.Rec

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-! ## Regularity and antisymmetry of the stages -/

lemma uD_contDiff (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l)) :
    ∀ m ≤ n, ∀ i l, ContDiff ℝ 1 (uD G η m i l) := by
  intro m
  induction m with
  | zero => intro _; simpa using hη
  | succ m ih =>
      intro hm i l
      have hm' : m < n := by omega
      rw [uD_succ_of_lt G η hm']
      exact contDiff_uStep G (fun i l => ih (by omega) i l) i l

lemma uStep_antisymm (G : Geom n) {s : Fin n}
    {D : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hD : ∀ i l z, D i l z = - D l i z) (i l : Fin n) :
    ∀ z, uStep G s D i l z = - uStep G s D l i z := by
  intro z
  by_cases hc : i = s ∨ l = s
  · have hc' : l = s ∨ i = s := hc.symm
    rw [uStep_apply, uStep_apply, if_pos hc, if_pos hc', hD i l z]
    ring
  · have hc' : ¬ (l = s ∨ i = s) := by tauto
    rw [uStep_apply, uStep_apply, if_neg hc, if_neg hc']
    have h2 : (fun y => kappabar G s y * D i l y)
        = - (fun y => kappabar G s y * D l i y) := by
      funext y; simp only [Pi.neg_apply]; rw [hD i l y]; ring
    rw [h2, map_neg, hD i l z]
    simp only [Pi.neg_apply]; ring

lemma uD_antisymm (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l z, η i l z = - η l i z) :
    ∀ m i l z, uD G η m i l z = - uD G η m l i z := by
  intro m
  induction m with
  | zero => intro i l z; simpa using hη i l z
  | succ m ih =>
      intro i l z
      by_cases hm : m < n
      · rw [uD_succ_of_lt G η hm]
        exact uStep_antisymm G (fun i l z => ih i l z) i l z
      · rw [uD_succ]; simp only [hm, dite_false]; exact ih i l z

/-! ## The tracking regions -/

/-- The region on which the stage-`m` data are tracked: the coordinates already processed are in
the solving polydisc, the others only in the support of their cutoff. -/
def E (G : Geom n) (m : ℕ) : Set (Fin n → ℂ) :=
  {z | ∀ k : Fin n, ((k : ℕ) < m → ‖z k‖ < G.e k) ∧ (m ≤ (k : ℕ) → ‖z k‖ < G.b k)}

/-- The polydisc on which the recursion solves the equation. -/
def solveSet (G : Geom n) : Set (Fin n → ℂ) := {z | ∀ k : Fin n, ‖z k‖ < G.e k}

lemma mem_solveSet {G : Geom n} {z : Fin n → ℂ} : z ∈ solveSet G ↔ ∀ k, ‖z k‖ < G.e k := Iff.rfl

lemma mem_E_of_solveSet (G : Geom n) {z : Fin n → ℂ} (hz : z ∈ solveSet G) (m : ℕ) :
    z ∈ E G m := by
  intro k
  refine ⟨fun _ => hz k, fun _ => lt_trans (hz k) (G.e_lt_b k)⟩

lemma E_mono (G : Geom n) {m m' : ℕ} (h : m ≤ m') : E G m' ⊆ E G m := by
  intro z hz k
  refine ⟨fun hk => (hz k).1 (by omega), fun hk => ?_⟩
  by_cases hkm : (k : ℕ) < m'
  · exact lt_trans ((hz k).1 hkm) (G.e_lt_b k)
  · exact (hz k).2 (by omega)

lemma E_fiber (G : Geom n) {s : Fin n} {z y : Fin n → ℂ} (hz : z ∈ E G ((s : ℕ) + 1))
    (hys : ‖y s‖ < G.b s) (hy : ∀ m : Fin n, m ≠ s → y m = z m) : y ∈ E G (s : ℕ) := by
  intro m
  constructor
  · intro hm
    have hne : m ≠ s := by intro h; rw [h] at hm; omega
    rw [hy m hne]
    exact (hz m).1 (by omega)
  · intro hm
    rcases eq_or_ne m s with hms | hne
    · rw [hms]; exact hys
    · rw [hy m hne]
      by_cases h : (m : ℕ) < (s : ℕ) + 1
      · exact lt_trans (lt_trans ((hz m).1 h) (G.hea m)) (G.hab m)
      · exact (hz m).2 (by omega)

/-- `∂̄` of the identically zero function vanishes. -/
lemma dbarCoord_zero (a : Fin n) (z : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord a (0 : (Fin n → ℂ) → ℂ) z = 0 := by
  rw [show (0 : (Fin n → ℂ) → ℂ) = fun _ => (0 : ℂ) from rfl, dbarCoord_const' a 0 z]

/-! ## Vanishing on the processed coordinates -/

lemma uD_vanish (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l)) :
    ∀ m ≤ n, ∀ i l : Fin n, ((i : ℕ) < m ∨ (l : ℕ) < m) →
      ∀ z, (∀ k : Fin n, (k : ℕ) < m → ‖z k‖ < G.a k) → uD G η m i l z = 0 := by
  intro m
  induction m with
  | zero => intro _ i l h; omega
  | succ m ih =>
      intro hm i l hlt z hz
      have hm' : m < n := by omega
      rw [uD_succ_of_lt G η hm']
      by_cases hc : i = (⟨m, hm'⟩ : Fin n) ∨ l = (⟨m, hm'⟩ : Fin n)
      · rw [uStep_apply, if_pos hc]
        have hcut : kappa G (⟨m, hm'⟩ : Fin n) z = 1 :=
          kappa_eq_one G _ (le_of_lt (hz (⟨m, hm'⟩ : Fin n) (by simp)))
        rw [hcut, sub_self, zero_mul, zero_add]
      · rw [uStep_apply, if_neg hc]
        have hcut : kappa G (⟨m, hm'⟩ : Fin n) z = 1 :=
          kappa_eq_one G _ (le_of_lt (hz (⟨m, hm'⟩ : Fin n) (by simp)))
        rw [hcut, sub_self, zero_mul, zero_add]
        have hcont : Continuous
            (fun y => kappabar G (⟨m, hm'⟩ : Fin n) y * uD G η m i l y) :=
          (contDiff_kappabar G _).continuous.mul
            ((uD_contDiff G hη m (by omega) i l).continuous)
        rw [TL_eq G _ hcont,
          Work.CR.Flat.Cauchy.dbarTransform_eq_zero_of_fiber (ρ := G.r (⟨m, hm'⟩ : Fin n))
            (j := (⟨m, hm'⟩ : Fin n))]
        intro y hy
        by_cases hbc : kappabar G (⟨m, hm'⟩ : Fin n) y = 0
        · rw [hbc, zero_mul]
        · have hy_out : ‖y (⟨m, hm'⟩ : Fin n)‖ < G.b (⟨m, hm'⟩ : Fin n) := by
            by_contra hcon
            exact hbc (kappabar_eq_zero_of_ge G _ (le_of_not_gt hcon))
          have hyz : ∀ k : Fin n, (k : ℕ) < m → ‖y k‖ < G.a k := by
            intro k hk
            have hne : k ≠ (⟨m, hm'⟩ : Fin n) := by
              intro h; rw [h] at hk; exact absurd hk (by simp)
            rw [hy k hne]
            exact hz k (by omega)
          have hlt' : (i : ℕ) < m ∨ (l : ℕ) < m := by
            rcases hlt with h | h
            · left; have hmne : (i : ℕ) ≠ m := fun he => hc (Or.inl (Fin.ext he)); omega
            · right; have hmne : (l : ℕ) ≠ m := fun he => hc (Or.inr (Fin.ext he)); omega
          rw [ih (by omega) i l hlt' y hyz, mul_zero]

/-! ## Closedness of the stages on the tracking regions -/

lemma uStep_closed_zero (G : Geom n) {s : Fin n}
    {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l, ContDiff ℝ 1 (D i l)) (hanti : ∀ i l z, D i l z = - D l i z)
    {a b c : Fin n} {z : Fin n → ℂ} (hzs : ‖z s‖ < G.a s)
    (hclz : Work.CR.Flat.dbarCoord a (D b c) z - Work.CR.Flat.dbarCoord b (D a c) z
      + Work.CR.Flat.dbarCoord c (D a b) z = 0)
    (hfib : ∀ y, (∀ m : Fin n, m ≠ s → y m = z m) →
      kappabar G s y * (Work.CR.Flat.dbarCoord a (D b c) y - Work.CR.Flat.dbarCoord b (D a c) y
        + Work.CR.Flat.dbarCoord c (D a b) y) = 0) :
    Work.CR.Flat.dbarCoord a (uStep G s D b c) z - Work.CR.Flat.dbarCoord b (uStep G s D a c) z
      + Work.CR.Flat.dbarCoord c (uStep G s D a b) z = 0 := by
  have hss : D s s = 0 := by
    funext w
    exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (hanti s s w))
  have hdbar_zero : ∀ a' : Fin n,
      Work.CR.Flat.dbarCoord a' (0 : (Fin n → ℂ) → ℂ) z = 0 := by
    intro a'
    rw [show (0 : (Fin n → ℂ) → ℂ) = fun _ => (0 : ℂ) from rfl, dbarCoord_const' a' 0 z]
  have hneg : ∀ a' {u : (Fin n → ℂ) → ℂ} (hu : DifferentiableAt ℝ u z),
      Work.CR.Flat.dbarCoord a' (fun w => - u w) z = - Work.CR.Flat.dbarCoord a' u z := by
    intro a' u hu
    have h := dbarCoord_sub' a' (differentiableAt_const (c := (0 : ℂ))) hu
    rw [show (fun w : Fin n → ℂ => -u w) = ((fun _ : Fin n → ℂ => (0 : ℂ)) - u) from by
        funext w; simp,
      h, dbarCoord_const' a' 0 z, zero_sub]
  rw [dbarCoord_uStep G hD hzs a b c,
      dbarCoord_uStep G hD hzs b a c,
      dbarCoord_uStep G hD hzs c a b]
  by_cases ha : a = s <;> by_cases hb : b = s <;> by_cases hc : c = s
  · rw [ha, hb, hc] at *
    simp only [ite_true, or_true, eq_self_iff_true, hss, hdbar_zero,
      Pi.zero_apply, neg_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
  · rw [ha, hb] at *
    simp only [ite_true, ite_false, true_or, or_true, false_or, or_false, eq_self_iff_true,
      hc, hss, hdbar_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
    ring
  · rw [ha, hc] at *
    simp only [ite_true, ite_false, true_or, or_true, false_or, or_false, eq_self_iff_true,
      hb, hss, hdbar_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
    have hd : Work.CR.Flat.dbarCoord s (D s b) z = - Work.CR.Flat.dbarCoord s (D b s) z := by
      rw [show D s b = fun w => - D b s w from funext fun w => hanti s b w]
      exact hneg s (((hD b s).differentiable one_ne_zero).differentiableAt)
    rw [hd, hanti s b z]
    ring
  · simp only [ite_eq_left ha, ite_eq_right (fun h : b = s ∨ c = s => h.elim hb hc),
      ite_eq_right hb, ite_eq_left (Or.inl ha), ite_eq_right hc]
    linear_combination (1 - kappa G s z) * hclz
  · rw [hb, hc] at *
    simp only [ite_true, ite_false, true_or, or_true, false_or, or_false, eq_self_iff_true,
      ha, hss, hdbar_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
    ring
  · simp only [ite_eq_right ha, ite_eq_left (Or.inl hb), ite_eq_left hb,
      ite_eq_right (fun h : a = s ∨ c = s => h.elim ha hc), ite_eq_right hc,
      ite_eq_left (Or.inr hb)]
    linear_combination (1 - kappa G s z) * hclz
  · simp only [ite_eq_right ha, ite_eq_left (Or.inr hc), ite_eq_right hb,
      ite_eq_right (fun h : a = s ∨ b = s => h.elim ha hb), ite_eq_left hc]
    linear_combination (1 - kappa G s z) * hclz
  · simp only [ite_eq_right ha, ite_eq_right hb, ite_eq_right hc,
      ite_eq_right (fun h : b = s ∨ c = s => h.elim hb hc),
      ite_eq_right (fun h : a = s ∨ c = s => h.elim ha hc),
      ite_eq_right (fun h : a = s ∨ b = s => h.elim ha hb)]
    have hdtlm : TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord a (D b c) y) z
        - TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord b (D a c) y) z
        + TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord c (D a b) y) z = 0 := by
      have hcomb : TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord a (D b c) y)
            - TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord b (D a c) y)
            + TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord c (D a b) y)
          = TL G s (fun y => kappabar G s y * (Work.CR.Flat.dbarCoord a (D b c) y
              - Work.CR.Flat.dbarCoord b (D a c) y
              + Work.CR.Flat.dbarCoord c (D a b) y)) := by
        rw [← map_sub, ← map_add]
        congr 1
        funext y
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      have hgcont : Continuous (fun y => kappabar G s y *
          (Work.CR.Flat.dbarCoord a (D b c) y - Work.CR.Flat.dbarCoord b (D a c) y
            + Work.CR.Flat.dbarCoord c (D a b) y)) :=
        (contDiff_kappabar G s).continuous.mul
          (((continuous_dbarCoord (hD b c) a).sub (continuous_dbarCoord (hD a c) b)).add
            (continuous_dbarCoord (hD a b) c))
      rw [show TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord a (D b c) y) z
            - TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord b (D a c) y) z
            + TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord c (D a b) y) z
          = (TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord a (D b c) y)
              - TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord b (D a c) y)
              + TL G s (fun y => kappabar G s y * Work.CR.Flat.dbarCoord c (D a b) y)) z
            from rfl,
        hcomb, TL_eq G s hgcont]
      exact Work.CR.Flat.Cauchy.dbarTransform_eq_zero_of_fiber (ρ := G.r s) (j := s) hfib
    linear_combination (1 - kappa G s z) * hclz + hdtlm

theorem uD_closed_E (G : Geom n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, (∀ k : Fin n, ‖z k‖ < G.b k) →
      Work.CR.Flat.dbarCoord i (η l m') z - Work.CR.Flat.dbarCoord l (η i m') z
        + Work.CR.Flat.dbarCoord m' (η i l) z = 0) :
    ∀ s ≤ n, ∀ a b c : Fin n, ∀ z ∈ E G s,
      Work.CR.Flat.dbarCoord a (uD G η s b c) z - Work.CR.Flat.dbarCoord b (uD G η s a c) z
        + Work.CR.Flat.dbarCoord c (uD G η s a b) z = 0 := by
  intro s
  induction s with
  | zero =>
      intro _ a b c z hz
      exact hcl a b c z (fun k => (hz k).2 (Nat.zero_le k))
  | succ s ih =>
      intro hs a b c z hz
      have hs' : s < n := by omega
      rw [uD_succ_of_lt G η hs']
      have hD : ∀ i l, ContDiff ℝ 1 (uD G η s i l) := fun i l => uD_contDiff G hη s (by omega) i l
      have hantiD : ∀ i l w, uD G η s i l w = - uD G η s l i w :=
        fun i l w => uD_antisymm G hanti s i l w
      have hzs : ‖z (⟨s, hs'⟩ : Fin n)‖ < G.a (⟨s, hs'⟩ : Fin n) := by
        exact lt_trans ((hz (⟨s, hs'⟩ : Fin n)).1 (by simp)) (G.hea (⟨s, hs'⟩ : Fin n))
      have hclz : Work.CR.Flat.dbarCoord a (uD G η s b c) z
          - Work.CR.Flat.dbarCoord b (uD G η s a c) z
          + Work.CR.Flat.dbarCoord c (uD G η s a b) z = 0 := ih (by omega) a b c z (E_mono G (by omega) hz)
      have hfib : ∀ y, (∀ m : Fin n, m ≠ (⟨s, hs'⟩ : Fin n) → y m = z m) →
          kappabar G (⟨s, hs'⟩ : Fin n) y *
            (Work.CR.Flat.dbarCoord a (uD G η s b c) y - Work.CR.Flat.dbarCoord b (uD G η s a c) y
              + Work.CR.Flat.dbarCoord c (uD G η s a b) y) = 0 := by
        intro y hy
        by_cases hcb : kappabar G (⟨s, hs'⟩ : Fin n) y = 0
        · rw [hcb, zero_mul]
        · have hys : ‖y (⟨s, hs'⟩ : Fin n)‖ < G.b (⟨s, hs'⟩ : Fin n) := by
            by_contra hcon
            exact hcb (kappabar_eq_zero_of_ge G _ (le_of_not_gt hcon))
          rw [ih (by omega) a b c y (E_fiber G hz hys hy), mul_zero]
      exact uStep_closed_zero G hD hantiD hzs hclz hfib

/-! ## Linearity of the recursion -/

lemma uStep_add (G : Geom n) {s : Fin n} {D D' : Fin n → Fin n → (Fin n → ℂ) → ℂ} :
    uStep G s (D + D') = uStep G s D + uStep G s D' := by
  funext i l z
  simp only [Pi.add_apply, uStep_apply]
  by_cases hc : i = s ∨ l = s
  · simp only [ite_eq_left hc]; ring
  · simp only [ite_eq_right hc]
    have harg : (fun y => kappabar G s y * (D i l y + D' i l y))
        = (fun y => kappabar G s y * D i l y) + (fun y => kappabar G s y * D' i l y) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [harg, map_add, Pi.add_apply]
    ring

lemma uStep_smul (G : Geom n) {s : Fin n} (c : ℝ) {D : Fin n → Fin n → (Fin n → ℂ) → ℂ} :
    uStep G s (c • D) = c • uStep G s D := by
  funext i l z
  simp only [Pi.smul_apply, uStep_apply]
  by_cases hc : i = s ∨ l = s
  · simp only [ite_eq_left hc, Complex.real_smul]
    ring
  · simp only [ite_eq_right hc]
    have harg : (fun y => kappabar G s y * (c • D i l y))
        = c • (fun y => kappabar G s y * D i l y) := by
      funext y
      simp only [Pi.smul_apply, Complex.real_smul]
      ring
    rw [harg, map_smul]
    simp only [Pi.smul_apply, Complex.real_smul]
    ring

lemma uD_add (G : Geom n) (η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    ∀ m, uD G (η + η') m = uD G η m + uD G η' m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [uD_succ, uD_succ, uD_succ]
      by_cases h : m < n
      · rw [dif_pos h, dif_pos h, dif_pos h, ih, uStep_add]
      · rw [dif_neg h, dif_neg h, dif_neg h, ih]

lemma uD_smul (G : Geom n) (c : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    ∀ m, uD G (c • η) m = c • uD G η m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [uD_succ, uD_succ]
      by_cases h : m < n
      · rw [dif_pos h, dif_pos h, ih, uStep_smul]
      · rw [dif_neg h, dif_neg h, ih]

lemma uPsi_add (G : Geom n) (η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ) (s : Fin n) :
    uPsi G (η + η') s = uPsi G η s + uPsi G η' s := by
  funext l
  show TL G s (fun y => kappa G s y * uD G (η + η') (s : ℕ) s l y)
    = TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y)
      + TL G s (fun y => kappa G s y * uD G η' (s : ℕ) s l y)
  rw [uD_add G η η' (s : ℕ)]
  have harg : (fun y => kappa G s y * (uD G η (s : ℕ) + uD G η' (s : ℕ)) s l y)
      = (fun y => kappa G s y * uD G η (s : ℕ) s l y)
        + (fun y => kappa G s y * uD G η' (s : ℕ) s l y) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [harg, map_add]

lemma uPsi_smul (G : Geom n) (c : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (s : Fin n) :
    uPsi G (c • η) s = c • uPsi G η s := by
  funext l
  show TL G s (fun y => kappa G s y * uD G (c • η) (s : ℕ) s l y)
    = c • TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y)
  rw [uD_smul G c η (s : ℕ)]
  have harg : (fun y => kappa G s y * (c • uD G η (s : ℕ)) s l y)
      = c • (fun y => kappa G s y * uD G η (s : ℕ) s l y) := by
    funext y; simp only [Pi.smul_apply, Complex.real_smul]; ring
  rw [harg, map_smul]

lemma S2_add (G : Geom n) (η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    S2 G (η + η') = S2 G η + S2 G η' := by
  funext l z
  simp only [S2_apply, Pi.add_apply, uPsi_add, Finset.sum_add_distrib]

lemma S2_smul (G : Geom n) (c : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    S2 G (c • η) = c • S2 G η := by
  funext l z
  simp only [S2_apply, Pi.smul_apply, uPsi_smul, Finset.smul_sum, Complex.real_smul]

end Work.NN.Core.TelTwoDF
