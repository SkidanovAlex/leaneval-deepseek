import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.similar_R_of_dims
import Submission.Work.RPV.exists_R_of_hrect
import Submission.Work.RPV.sin_cos_arctan_div
import Submission.Work.RPV.degenerate_R_pair

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-- `R z z θ` is the constant family with value `z * θ.toCircle`. -/
lemma R_eq_self_const (z : ℂ) (θ : Real.Angle) (i : Fin 4) :
    RectangularPegProblem.R z z θ i = z * (θ.toCircle : ℂ) := by
  fin_cases i <;> simp [RectangularPegProblem.R, Complex.re_add_im]

/-- Two constant rectangle families are similar (all distances vanish on both sides). -/
lemma similar_const_R (z c : ℂ) (θ : Real.Angle) :
    Similar (RectangularPegProblem.R z z θ) (RectangularPegProblem.R c c (0 : Real.Angle)) := by
  have h1 : ∀ i, RectangularPegProblem.R z z θ i = z * (θ.toCircle : ℂ) := R_eq_self_const z θ
  have h2 : ∀ i, RectangularPegProblem.R c c (0 : Real.Angle) i
      = c * (((0 : Real.Angle).toCircle : Circle) : ℂ) := by
    intro i; exact R_eq_self_const c 0 i
  refine ⟨1, one_ne_zero, fun i j => ?_⟩
  rw [h1 i, h1 j, h2 i, h2 j]
  simp

/-- The challenge statement follows from the normalised `φ`-rectangle existence (for
`0 < φ < π`) together with the degenerate cases; `θ` is any angle, `z w` any pair of points,
and the rectangle `R z w θ` is instantiating `Similar` with a rectangle whose vertices lie on
`γ`.  Hints for the proof.  If `z = w` the four entries of `R z w θ` are all equal; take
`θ' = 0` and `z' = w' = γ p`.  If `z ≠ w` but `z.re = w.re` (or `z.im = w.im`) the four entries
are `z c, z c, w c, w c` (resp. `w c, z c, z c, w c`), so it suffices to take two distinct
points `p ≠ q` of `γ`; a suitable pair is produced by the degenerate-case lemma
`Work.RPV.exists_two_points`.  Otherwise `z.re ≠ w.re` and `z.im ≠ w.im` and the source is a
genuine `Δx × Δy` rectangle; use `main` at `φ = 2 * Real.arctan (|z.re - w.re| / |z.im - w.im|)`
(which lies in `(0,π)`) and note `|1 - e^{iφ}| / |1 + e^{iφ}| = tan(φ/2)` so the inscribed
rectangle has the correct aspect ratio; conclude by `Similar` being invariant under the
rotation and translation relating the two rectangles. -/
theorem theorem_1_of_main
    (main : ∀ (γ : Circle → ℂ), Work.RPV.IsSmoothJordan γ →
      ∀ φ : ℝ, 0 < φ → φ < π → Work.RPV.HasThetaRect (Set.range γ) φ)
    (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle) (hγ : Work.RPV.IsSmoothJordan γ) :
    ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ),
      Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') ∧
      ∀ i : Fin 4, RectangularPegProblem.R z' w' θ' i ∈ Set.range γ := by
  -- two distinct points of `γ`, obtained from `main` at `φ = π / 2`
  have htwo : ∃ A ∈ Set.range γ, ∃ B ∈ Set.range γ, A ≠ B := by
    obtain ⟨A, hA, B, hB, C, hC, D, hD, hne, _, _⟩ :=
      main γ hγ (Real.pi / 2) (by positivity) (by linarith [Real.pi_pos])
    exact ⟨A, hA, B, hB, hne⟩
  by_cases hzw : z = w
  · -- `z = w`: the source family is constant
    refine ⟨0, γ 1, γ 1, ?_, ?_⟩
    · rw [hzw]
      exact similar_const_R w (γ 1) θ
    · intro i
      rw [R_eq_self_const]
      simp
  · rcases htwo with ⟨A, hA, B, hB, hAB⟩
    have hABpos : 0 < ‖A - B‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hAB
    by_cases hre : z.re = w.re
    · -- degenerate: `z` and `w` have the same real part, source is `z c, z c, w c, w c`
      have hbpos : 0 < |z.im - w.im| := by
        rw [abs_pos]
        intro h
        exact hzw (Complex.ext hre (sub_eq_zero.mp h))
      obtain ⟨θ', z', w', hR, hx0, hy0⟩ := (degenerate_R_pair A B).1
      refine ⟨θ', z', w', ?_, ?_⟩
      · refine similar_R_of_dims z w z' w' θ θ' (|z.im - w.im| / ‖A - B‖)
          (by positivity) ?_ ?_
        · have h0 : z.re - w.re = 0 := sub_eq_zero.mpr hre
          rw [h0, abs_zero, hx0, mul_zero]
        · rw [hy0, div_mul_cancel₀ _ (ne_of_gt hABpos)]
      · intro i
        rw [hR]
        fin_cases i <;> simp [hA, hB]
    · by_cases him : z.im = w.im
      · -- degenerate: `z` and `w` have the same imaginary part, source is `z c, w c, w c, z c`
        have hapos : 0 < |z.re - w.re| := by
          rw [abs_pos]; exact sub_ne_zero.mpr hre
        obtain ⟨θ', z', w', hR, hx0, hy0⟩ := (degenerate_R_pair A B).2
        refine ⟨θ', z', w', ?_, ?_⟩
        · refine similar_R_of_dims z w z' w' θ θ' (|z.re - w.re| / ‖A - B‖)
            (by positivity) ?_ ?_
          · rw [hx0, div_mul_cancel₀ _ (ne_of_gt hABpos)]
          · have h0 : z.im - w.im = 0 := sub_eq_zero.mpr him
            rw [h0, abs_zero, hy0, mul_zero]
        · intro i
          rw [hR]
          fin_cases i <;> simp [hA, hB]
      · -- generic case
        have hapos : 0 < |z.re - w.re| := by
          rw [abs_pos]; exact sub_ne_zero.mpr hre
        have hbpos : 0 < |z.im - w.im| := by
          rw [abs_pos]; exact sub_ne_zero.mpr him
        have hratio : 0 < |z.re - w.re| / |z.im - w.im| := div_pos hapos hbpos
        set φ : ℝ := 2 * Real.arctan (|z.re - w.re| / |z.im - w.im|) with hφ
        have hφhalf : φ / 2 = Real.arctan (|z.re - w.re| / |z.im - w.im|) := by
          rw [hφ]; ring
        have hφpos : 0 < φ := by
          rw [hφ]
          have h := (Real.arctan_pos).2 hratio
          linarith
        have hφlt : φ < π := by
          rw [hφ]
          have h := Real.arctan_lt_pi_div_two (|z.re - w.re| / |z.im - w.im|)
          linarith [Real.pi_pos]
        obtain ⟨x, hx, y, hy, x', hx', y', hy', hne, hsum, hdiff⟩ :=
          main γ hγ φ hφpos hφlt
        obtain ⟨θ', z', w', hR, hdr, hdi⟩ :=
          exists_R_of_hrect (x := x) (y := y) (x' := x') (y' := y') (φ := φ)
            hφpos hφlt hne hsum hdiff
        have hd0 : 0 < ‖x - y‖ := by
          rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
        have hd0' : ‖x - y‖ ≠ 0 := ne_of_gt hd0
        have hs0 : 0 < Real.sqrt (|z.re - w.re| ^ 2 + |z.im - w.im| ^ 2) :=
          Real.sqrt_pos_of_pos (by positivity)
        have hs0' : Real.sqrt (|z.re - w.re| ^ 2 + |z.im - w.im| ^ 2) ≠ 0 := ne_of_gt hs0
        refine ⟨θ', z', w', ?_, ?_⟩
        · refine similar_R_of_dims z w z' w' θ θ'
            (Real.sqrt (|z.re - w.re| ^ 2 + |z.im - w.im| ^ 2) / ‖x - y‖)
            (div_pos hs0 hd0) ?_ ?_
          · rw [hdr, hφhalf, (sin_cos_arctan_div |z.re - w.re| |z.im - w.im| hapos hbpos).1]
            field_simp
          · rw [hdi, hφhalf, (sin_cos_arctan_div |z.re - w.re| |z.im - w.im| hapos hbpos).2]
            field_simp
        · intro i
          rw [hR]
          fin_cases i
          · simpa using hx
          · simpa using hx'
          · simpa using hy
          · simpa using hy'

end Work.RPV
