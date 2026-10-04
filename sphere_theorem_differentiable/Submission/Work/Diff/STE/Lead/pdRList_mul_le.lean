import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Filter

/-!
# The Leibniz rule for the iterated partial derivatives `pdRList` of order `≤ 2`

`Work.Diff.STE.pdRList l f` is the iterated partial derivative of a real function on `Fin d → ℝ`
along the list of directions `l` (`l.foldr (fun i g => pdR i g) f`), where
`pdR i f x = fderiv ℝ f x (Pi.single i 1)`.

The main result is that the jets of order `≤ 2` of a pointwise product `y ↦ f y * g y` are bounded
by a *universal* constant times `Kf * Kg`, whenever the jets of order `≤ 2` of `f` and of `g` are
bounded by `Kf` resp. `Kg` at the same point `z`.  Concretely, `C = 4` works:

* order 0: `(f g)(z) = f z · g z`, one term;
* order 1: `∂_p (f g)(z) = f z · ∂_p g z + g z · ∂_p f z`, two terms;
* order 2: `∂_q∂_p (f g)(z) = f z · ∂_q∂_p g z + ∂_p g z · ∂_q f z + ∂_q g z · ∂_p f z
  + g z · ∂_q∂_p f z`, four terms.

This is the Leibniz rule `pdR_mul` together with the "second order Leibniz" rule `pdR2_mul`.
-/

/-- **Leibniz rule for the first partial derivative.**  For functions `f g` differentiable at `z`,
`∂_p (f · g)(z) = f z · ∂_p g z + g z · ∂_p f z`. -/
private lemma pdR_mul {d : ℕ} {f g : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} (p : Fin d)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    Work.Diff.STE.pdR p (fun y => f y * g y) z
      = f z * Work.Diff.STE.pdR p g z + g z * Work.Diff.STE.pdR p f z := by
  show fderiv ℝ (fun y => f y * g y) z (Pi.single p 1) = _
  rw [fderiv_fun_mul hf hg]
  simp [Work.Diff.STE.pdR, smul_eq_mul]

/-- **Second order Leibniz rule.**  For `f` and `g` of class `C²` at `z`,

`∂_q∂_p (f · g)(z) = f z · ∂_q∂_p g z + ∂_p g z · ∂_q f z + ∂_q g z · ∂_p f z
  + g z · ∂_q∂_p f z`.

The proof differentiates the `C⁰` Leibniz identity `pdR p (f · g) = f · ∂_p g + g · ∂_p f` valid on
a neighbourhood of `z` (`ContDiffAt.eventually`), using `EventuallyEq.fderiv_eq`, `fderiv_add` and
`fderiv_fun_mul`. -/
private lemma pdR2_mul {d : ℕ} {f g : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} (q p : Fin d)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => f y * g y)) z
      = f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
        + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
        + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
        + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z := by
  have hdf : DifferentiableAt ℝ f z := hf.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hdfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hdgd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hdfp : DifferentiableAt ℝ (Work.Diff.STE.pdR p f) z := by
    have h :=
      (hdfd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1 : ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single p (1 : ℝ))) z
    exact h
  have hdgp : DifferentiableAt ℝ (Work.Diff.STE.pdR p g) z := by
    have h :=
      (hdgd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single p (1 : ℝ)) z)).differentiableAt
    show DifferentiableAt ℝ (fun y => fderiv ℝ g y (Pi.single p (1 : ℝ))) z
    exact h
  have hev : Work.Diff.STE.pdR p (fun y => f y * g y) =ᶠ[nhds z]
      (fun y => f y * Work.Diff.STE.pdR p g y + g y * Work.Diff.STE.pdR p f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact pdR_mul p (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hd1 : DifferentiableAt ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z := hdf.mul hdgp
  have hd2 : DifferentiableAt ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z := hdg.mul hdfp
  have hsum : fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y
        + g y * Work.Diff.STE.pdR p f y) z
      = fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z
        + fderiv ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z := fderiv_add hd1 hd2
  calc Work.Diff.STE.pdR q (Work.Diff.STE.pdR p (fun y => f y * g y)) z
      = fderiv ℝ (Work.Diff.STE.pdR p (fun y => f y * g y)) z (Pi.single q 1) := rfl
    _ = fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y + g y * Work.Diff.STE.pdR p f y) z
          (Pi.single q 1) := by rw [hev.fderiv_eq]
    _ = (fderiv ℝ (fun y => f y * Work.Diff.STE.pdR p g y) z
           + fderiv ℝ (fun y => g y * Work.Diff.STE.pdR p f y) z) (Pi.single q 1) := by
          rw [hsum]
    _ = f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
        + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
        + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
        + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z := by
          rw [fderiv_fun_mul hdf hdgp, fderiv_fun_mul hdg hdfp]
          simp only [Work.Diff.STE.pdR, add_apply, smul_apply, smul_eq_mul]
          ring

/-- A list of length `≤ 2` is empty, a singleton, or a pair. -/
private lemma length_le_two_cases {d : ℕ} (l : List (Fin d)) (h : l.length ≤ 2) :
    l = [] ∨ (∃ p, l = [p]) ∨ (∃ q p, l = [q, p]) := by
  cases l with
  | nil => exact Or.inl rfl
  | cons p t =>
    cases t with
    | nil => exact Or.inr (Or.inl ⟨p, rfl⟩)
    | cons q t =>
      cases t with
      | nil => exact Or.inr (Or.inr ⟨p, q, rfl⟩)
      | cons s t =>
        simp only [List.length_cons] at h
        omega

/-- Triangle inequality for a sum of four terms. -/
private lemma abs_add4_le (a b c e : ℝ) : |a + b + c + e| ≤ |a| + |b| + |c| + |e| := by
  calc |a + b + c + e| ≤ |a + b + c| + |e| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |e| := by linarith [abs_add_le (a + b) c]
    _ ≤ ((|a| + |b|) + |c|) + |e| := by linarith [abs_add_le a b]
    _ = |a| + |b| + |c| + |e| := by ring

/-- **Product bound for the jets of order `≤ 2`.**  With `C = 4`, the iterated partial derivatives of
order `≤ 2` of a pointwise product are bounded by `C * (Kf * Kg)`, where `Kf` (resp. `Kg`) bounds
all iterated partial derivatives of order `≤ 2` of `f` (resp. `g`) at `z`. -/
theorem pdRList_mul_le {d : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f g : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) (Kf Kg : ℝ),
        0 ≤ Kf → 0 ≤ Kg → ContDiffAt ℝ 2 f z → ContDiffAt ℝ 2 g z →
        (∀ l : List (Fin d), l.length ≤ 2 → |Work.Diff.STE.pdRList l f z| ≤ Kf) →
        (∀ l : List (Fin d), l.length ≤ 2 → |Work.Diff.STE.pdRList l g z| ≤ Kg) →
        ∀ l : List (Fin d), l.length ≤ 2 →
          |Work.Diff.STE.pdRList l (fun y => f y * g y) z| ≤ C * (Kf * Kg) := by
  refine ⟨4, by norm_num, ?_⟩
  intro f g z Kf Kg hKf hKg hf hg hbf hbg l hl
  have hfg : 0 ≤ Kf * Kg := mul_nonneg hKf hKg
  have hf0 : |f z| ≤ Kf := hbf [] (by simp)
  have hg0 : |g z| ≤ Kg := hbg [] (by simp)
  rcases length_le_two_cases l hl with rfl | ⟨p, rfl⟩ | ⟨q, p, rfl⟩
  · -- order 0
    have hval : Work.Diff.STE.pdRList ([] : List (Fin d)) (fun y => f y * g y) z
        = f z * g z := by simp [Work.Diff.STE.pdRList]
    rw [hval, abs_mul]
    have h1 : |f z| * |g z| ≤ Kf * Kg := mul_le_mul hf0 hg0 (abs_nonneg _) hKf
    nlinarith [h1, hfg]
  · -- order 1
    have hp_f : |Work.Diff.STE.pdR p f z| ≤ Kf := hbf [p] (by simp)
    have hp_g : |Work.Diff.STE.pdR p g z| ≤ Kg := hbg [p] (by simp)
    have hd := pdR_mul p (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num))
    have hval : Work.Diff.STE.pdRList [p] (fun y => f y * g y) z
        = f z * Work.Diff.STE.pdR p g z + g z * Work.Diff.STE.pdR p f z := by
      simpa [Work.Diff.STE.pdRList] using hd
    rw [hval]
    have h1 : |f z * Work.Diff.STE.pdR p g z| ≤ Kf * Kg := by
      rw [abs_mul]; exact mul_le_mul hf0 hp_g (abs_nonneg _) hKf
    have h2 : |g z * Work.Diff.STE.pdR p f z| ≤ Kg * Kf := by
      rw [abs_mul]; exact mul_le_mul hg0 hp_f (abs_nonneg _) hKg
    have h3 : |f z * Work.Diff.STE.pdR p g z + g z * Work.Diff.STE.pdR p f z|
        ≤ Kf * Kg + Kg * Kf := le_trans (abs_add_le _ _) (add_le_add h1 h2)
    nlinarith [h3, hfg]
  · -- order 2
    have hq_f : |Work.Diff.STE.pdR q f z| ≤ Kf := hbf [q] (by simp)
    have hp_f : |Work.Diff.STE.pdR p f z| ≤ Kf := hbf [p] (by simp)
    have hqp_f : |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z| ≤ Kf := hbf [q, p] (by simp)
    have hq_g : |Work.Diff.STE.pdR q g z| ≤ Kg := hbg [q] (by simp)
    have hp_g : |Work.Diff.STE.pdR p g z| ≤ Kg := hbg [p] (by simp)
    have hqp_g : |Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z| ≤ Kg := hbg [q, p] (by simp)
    have hd := pdR2_mul q p hf hg
    have hval : Work.Diff.STE.pdRList [q, p] (fun y => f y * g y) z
        = f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
          + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
          + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
          + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z := by
      simpa [Work.Diff.STE.pdRList] using hd
    rw [hval]
    have h1 : |f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z| ≤ Kf * Kg := by
      rw [abs_mul]; exact mul_le_mul hf0 hqp_g (abs_nonneg _) hKf
    have h2 : |Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z| ≤ Kg * Kf := by
      rw [abs_mul]; exact mul_le_mul hp_g hq_f (abs_nonneg _) hKg
    have h3 : |Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z| ≤ Kg * Kf := by
      rw [abs_mul]; exact mul_le_mul hq_g hp_f (abs_nonneg _) hKg
    have h4 : |g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z| ≤ Kg * Kf := by
      rw [abs_mul]; exact mul_le_mul hg0 hqp_f (abs_nonneg _) hKg
    have h3' : |f z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p g) z
          + Work.Diff.STE.pdR p g z * Work.Diff.STE.pdR q f z
          + Work.Diff.STE.pdR q g z * Work.Diff.STE.pdR p f z
          + g z * Work.Diff.STE.pdR q (Work.Diff.STE.pdR p f) z|
        ≤ Kf * Kg + Kg * Kf + Kg * Kf + Kg * Kf :=
      le_trans (abs_add4_le _ _ _ _) (by linarith [h1, h2, h3, h4])
    nlinarith [h3', hfg]

end Work.Diff.STE.Lead
