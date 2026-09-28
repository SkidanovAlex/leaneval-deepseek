import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.rNorm_smul

/-!
# `Work.HP.cone_scale`

Scaling of Lebesgue measure on the coefficient space `Mon d n → ℝ`, as used for the
Archimedean factor in the proof of the Hasse principle for random Fano hypersurfaces.

The paper's norm is the *Euclidean* norm `rNorm` on coefficient vectors (`Defs.lean` warns that
Lean's `‖·‖` on `ι → ℝ` is the sup norm and must not be identified with it).  The statement
records three things:

* a scale-invariant set `X` satisfies `vol (X ∩ {‖·‖ ≤ A}) = A^{N_{d,n}} vol (X ∩ B(1))`,
  for `A > 0` (`N_{d,n} = NN d n` is the dimension of the coefficient space);
* the Euclidean unit ball has finite, nonzero volume;
* the volume of a (sup-norm) ball of radius `ρ` scales as `ρ^{N_{d,n}}`.

The proofs rest on `Measure.addHaar_smul_of_nonneg` and `Measure.addHaar_ball_of_pos` for the
canonical Haar measure `volume` on the finite-dimensional real vector space `Mon d n → ℝ`,
together with `Module.finrank_fintype_fun_eq_card` and the two elementary comparisons between
`rNorm` and the sup norm.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

open MeasureTheory MvPolynomial
open scoped Pointwise

variable {ι : Type*} [Fintype ι]

/-- An exponent vector of degree `d`, namely `x_0^d`; in particular `Mon d n` is nonempty. -/
private lemma nonemptyMon (d n : ℕ) : Nonempty (Mon d n) :=
  ⟨⟨fun i => ⟨if i = 0 then d else 0, by split_ifs <;> omega⟩, by
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h⟩⟩

/-- Each coordinate of `v` is bounded by the Euclidean norm `rNorm v`. -/
private lemma abs_le_rNorm (v : ι → ℝ) (i : ι) : |v i| ≤ rNorm v := by
  have h : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc |v i| = √((v i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(∑ j, (v j) ^ 2) := Real.sqrt_le_sqrt h
    _ = rNorm v := rfl

/-- The sup norm on `ι → ℝ` is dominated by the Euclidean norm `rNorm`. -/
private lemma norm_le_rNorm (v : ι → ℝ) : ‖v‖ ≤ rNorm v := by
  rw [rNorm, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  exact abs_le_rNorm v i

/-- The Euclidean norm `rNorm` is at most `√(card ι)` times the sup norm. -/
private lemma rNorm_le_sqrt_card_mul_norm (v : ι → ℝ) :
    rNorm v ≤ √(Fintype.card ι) * ‖v‖ := by
  have h2 : ∀ i ∈ Finset.univ, (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i _
    have h := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (v i), norm_nonneg v, sq_abs (v i)]
  have hsum : ∑ i, (v i) ^ 2 ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
    calc ∑ i, (v i) ^ 2 ≤ ∑ i, ‖v‖ ^ 2 := Finset.sum_le_sum h2
      _ = (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc rNorm v = √(∑ i, (v i) ^ 2) := rfl
    _ ≤ √((Fintype.card ι : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = √(Fintype.card ι : ℝ) * √(‖v‖ ^ 2) := Real.sqrt_mul (Nat.cast_nonneg _) _
    _ = √(Fintype.card ι : ℝ) * ‖v‖ := by rw [Real.sqrt_sq (norm_nonneg v)]

theorem cone_scale (d n : ℕ) :
    (∀ (X : Set (Mon d n → ℝ)) (A : ℝ), 0 < A → (∀ (t : ℝ), 0 < t → ∀ a, a ∈ X ↔ t • a ∈ X) →
        volume (X ∩ {a : Mon d n → ℝ | rNorm a ≤ A})
          = ENNReal.ofReal (A ^ NN d n) * volume (X ∩ {a : Mon d n → ℝ | rNorm a ≤ 1})) ∧
    (volume {a : Mon d n → ℝ | rNorm a ≤ 1} ≠ 0) ∧
    (volume {a : Mon d n → ℝ | rNorm a ≤ 1} ≠ ⊤) ∧
    (∀ (ρ : ℝ), 0 < ρ → volume (Metric.ball (0 : Mon d n → ℝ) ρ) = ENNReal.ofReal (ρ ^ NN d n) *
        volume (Metric.ball (0 : Mon d n → ℝ) 1)) := by
  have hfr : Module.finrank ℝ (Mon d n → ℝ) = NN d n := by
    rw [Module.finrank_fintype_fun_eq_card]
  have hcard : (0 : ℝ) < (Fintype.card (Mon d n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (nonemptyMon d n))
  have hsqrt : 0 < √(Fintype.card (Mon d n) : ℝ) := Real.sqrt_pos.mpr hcard
  have hδ : 0 < 1 / √(Fintype.card (Mon d n) : ℝ) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- scaling of a homogeneous set
    intro X A hA hX
    have hset : X ∩ {a : Mon d n → ℝ | rNorm a ≤ A}
        = A • (X ∩ {a : Mon d n → ℝ | rNorm a ≤ 1}) := by
      ext a
      constructor
      · rintro ⟨haX, haA⟩
        have haA' : rNorm a ≤ A := haA
        refine ⟨A⁻¹ • a, ⟨?_, ?_⟩, ?_⟩
        · -- `A⁻¹ • a ∈ X`, since `a ∈ X` and `X` is stable under positive scalars
          have h2 : A • (A⁻¹ • a) ∈ X := by
            rwa [smul_smul, mul_inv_cancel₀ (ne_of_gt hA), one_smul]
          exact (hX A hA (A⁻¹ • a)).mpr h2
        · change rNorm (A⁻¹ • a) ≤ 1
          rw [rNorm_smul, abs_of_pos (inv_pos.mpr hA)]
          have h1 : A⁻¹ * rNorm a ≤ A⁻¹ * A :=
            mul_le_mul_of_nonneg_left haA' (le_of_lt (inv_pos.mpr hA))
          rwa [inv_mul_cancel₀ (ne_of_gt hA)] at h1
        · show A • (A⁻¹ • a) = a
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hA), one_smul]
      · rintro ⟨b, ⟨hbX, hb1⟩, rfl⟩
        have hb1' : rNorm b ≤ 1 := hb1
        exact ⟨(hX A hA b).mp hbX, by
          show rNorm (A • b) ≤ A
          rw [rNorm_smul, abs_of_pos hA]
          exact mul_le_of_le_one_right (le_of_lt hA) hb1'⟩
    rw [hset, Measure.addHaar_smul_of_nonneg (volume : Measure (Mon d n → ℝ)) (le_of_lt hA), hfr]
  · -- the Euclidean unit ball has positive volume
    have hsub : Metric.ball (0 : Mon d n → ℝ) (1 / √(Fintype.card (Mon d n) : ℝ))
        ⊆ {a : Mon d n → ℝ | rNorm a ≤ 1} := by
      intro a ha
      rw [Metric.mem_ball, dist_zero_right] at ha
      have hmul : √(Fintype.card (Mon d n) : ℝ) * ‖a‖
          < √(Fintype.card (Mon d n) : ℝ) * (1 / √(Fintype.card (Mon d n) : ℝ)) :=
        mul_lt_mul_of_pos_left ha hsqrt
      have hone : √(Fintype.card (Mon d n) : ℝ) * (1 / √(Fintype.card (Mon d n) : ℝ)) = 1 := by
        rw [mul_one_div, div_self (ne_of_gt hsqrt)]
      have ha' : rNorm a ≤ 1 := by linarith [rNorm_le_sqrt_card_mul_norm a]
      exact ha'
    have hpos : 0 < volume (Metric.ball (0 : Mon d n → ℝ) (1 / √(Fintype.card (Mon d n) : ℝ))) :=
      pos_iff_ne_zero.mpr (Measure.IsOpenPosMeasure.open_pos _
        Metric.isOpen_ball ⟨0, Metric.mem_ball_self hδ⟩)
    exact (lt_of_lt_of_le hpos (measure_mono hsub)).ne'
  · -- the Euclidean unit ball has finite volume
    have hsub : {a : Mon d n → ℝ | rNorm a ≤ 1} ⊆ Metric.closedBall (0 : Mon d n → ℝ) 1 := by
      intro a ha
      have ha' : rNorm a ≤ 1 := ha
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (norm_le_rNorm a) ha'
    have hcomp : volume (Metric.closedBall (0 : Mon d n → ℝ) 1) < ⊤ :=
      IsCompact.measure_lt_top (isCompact_closedBall 0 1)
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hcomp)
  · -- scaling of balls
    intro ρ hρ
    rw [Measure.addHaar_ball_of_pos (volume : Measure (Mon d n → ℝ)) (0 : Mon d n → ℝ) hρ, hfr]

end Work.HP
