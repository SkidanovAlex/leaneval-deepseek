import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_facts
import Submission.Work.Horn.FatouQ.chartdict
import Submission.Work.Horn.FatouQ.Xfun_basic
import Submission.Work.Horn.FatouQ.Xfun_sum_bound
import Submission.Work.Horn.FatouQ.Xfun_log_bound

namespace Work.Horn.FatouQ

open Work.Horn.Flower

noncomputable section

/-- The middle sum of `Acorr`, evaluated along the inverse chart. -/
theorem Xfun_sub_sum {f : ℂ → ℂ} {q : ℕ} {a : ℂ} (j : Fin q) {w : ℂ}
    (h : chartQ q a (zBranch q a j w) = w) :
    Xfun f q a j w - w =
      (∑ i ∈ Finset.Icc 1 (q - 1),
          gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i))
        + (gcoef f q a q + ((q : ℂ) + 1) / 2) * Lbranch q a (zBranch q a j w) := by
  have h' : cc q a / (zBranch q a j w) ^ q = w := h
  simp only [Xfun, Acorr]
  rw [h']
  ring

/-- Combining two Hölder-type bounds with exponents `θu, θv < 1` into a single one. -/
theorem holder_pair_add {X u v Cu Cv θu θv K1 K2 : ℝ} (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (hθu0 : 0 ≤ θu) (hθv0 : 0 ≤ θv) (hθu1 : θu ≤ 1) (hθv1 : θv ≤ 1) (hX : 0 ≤ X)
    (hu : u ≤ Cu * X ^ θu + K1) (hv : v ≤ Cv * X ^ θv + K2) :
    u + v ≤ (Cu + Cv) * X ^ max θu θv + (K1 + Cu + K2 + Cv) := by
  have hθ1 : max θu θv ≤ 1 := max_le hθu1 hθv1
  have h1 : X ^ θu ≤ X ^ max θu θv + 1 :=
    rpow_le_rpow_add_one hθu0 (le_max_left _ _) hθ1 hX
  have h2 : X ^ θv ≤ X ^ max θu θv + 1 :=
    rpow_le_rpow_add_one hθv0 (le_max_right _ _) hθ1 hX
  have e1 : Cu * X ^ θu ≤ Cu * X ^ max θu θv + Cu := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hCu]
  have e2 : Cv * X ^ θv ≤ Cv * X ^ max θu θv + Cv := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hCv]
  linarith

/-- The Hölder bound for `Xfun`, from the two bounds for the middle sum and the logarithmic
term of `Acorr`. -/
theorem Xfun_holder_of_bounds {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : PetalDatum f D q a ρ M) (j : Fin q)
    (hchart : ∀ w : ℂ, M < w.re → chartQ q a (zBranch q a j w) = w)
    (hsum : ∃ C0 C1 θ : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ w : ℂ, M < w.re →
      ‖∑ i ∈ Finset.Icc 1 (q - 1),
          gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖
        ≤ C0 * ‖w‖ ^ θ + C1)
    (hlog : ∃ C0 C1 θ : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ w : ℂ, M < w.re →
      ‖(gcoef f q a q + ((q : ℂ) + 1) / 2) * Lbranch q a (zBranch q a j w)‖
        ≤ C0 * ‖w‖ ^ θ + C1) :
    ∃ C0 C1 θ : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ θ < 1 ∧ ∀ w : ℂ, M < w.re →
      ‖Xfun f q a j w - w‖ ≤ C0 * ‖w‖ ^ θ + C1 := by
  obtain ⟨C0a, C1a, θa, hC0a, hC1a, hθa0, hθa1, hsum'⟩ := hsum
  obtain ⟨C0b, C1b, θb, hC0b, hC1b, hθb0, hθb1, hlog'⟩ := hlog
  refine ⟨C0a + C0b, C1a + C0a + C1b + C0b, max θa θb, by linarith, by linarith,
    max_lt hθa1 hθb1, ?_⟩
  intro w hw
  have hid := Xfun_sub_sum (f := f) (q := q) (a := a) j (hchart w hw)
  have h1 := hsum' w hw
  have h2 := hlog' w hw
  have h3 : ‖Xfun f q a j w - w‖ ≤
      ‖∑ i ∈ Finset.Icc 1 (q - 1),
          gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (zBranch q a j w)⁻¹ ^ (q - i)‖
        + ‖(gcoef f q a q + ((q : ℂ) + 1) / 2) * Lbranch q a (zBranch q a j w)‖ := by
    rw [hid]
    exact norm_add_le _ _
  exact le_trans h3 (holder_pair_add hC0a hC0b hθa0 hθb0 (le_of_lt hθa1) (le_of_lt hθb1)
    (norm_nonneg w) h1 h2)

/-- **Hölder continuity of the approximate Fatou coordinate at the ends of the petal.**
Both corrections to the chart `w` in `Xfun` are: the finitely many sublinear powers `(1/z)^(q-i)`
of the inverse chart (each of them `O(‖w‖^((q-i)/q))` with `(q-i)/q < 1`) and the logarithm
`log z ~ (1/q) log(1/w)`; hence `Xfun − id` is dominated by `C0 * ‖w‖ ^ θ + C1` with `θ < 1`. -/
theorem Xfun_holder {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j)
    (hchart : ∀ w : ℂ, M < w.re → Work.Horn.Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w) = w) :
    ∃ C0 C1 θ : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ θ < 1 ∧ ∀ w : ℂ, M < w.re →
      ‖Work.Horn.FatouQ.Xfun f q a j w - w‖ ≤ C0 * ‖w‖ ^ θ + C1 := by
  exact Xfun_holder_of_bounds hd j hchart
    (Xfun_sum_bound hd j hchart) (Xfun_log_bound hd j hchart)

end

end Work.Horn.FatouQ
