import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.PhiStar.LinvFlat.Lop_iter_sin_cos_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux.AngSlot

open scoped Real
open Work.FTS.PhiStar.LinvFlat

/-- The basic angular profile `S2 θ = sin (2θ)`. -/
private noncomputable def S2 : ℝ → ℝ := fun θ => Real.sin (2 * θ)

/-- The constant function `1` is a trigonometric polynomial. -/
private lemma TP_one : LopTrig.TP (fun _ : ℝ => (1 : ℝ)) := by
  have h : (fun θ : ℝ => Real.sin (2 * θ) * Real.sin (2 * θ)
      + Real.cos (2 * θ) * Real.cos (2 * θ)) = (fun _ : ℝ => (1 : ℝ)) := by
    funext θ
    rw [← sq (Real.sin (2 * θ)), ← sq (Real.cos (2 * θ)), Real.sin_sq_add_cos_sq]
  rw [← h]
  exact LopTrig.TP.add (LopTrig.TP.mul LopTrig.TP.sin2 LopTrig.TP.sin2)
    (LopTrig.TP.mul LopTrig.TP.cos2 LopTrig.TP.cos2)

/-- **Divisibility of the `Lop`-iterates of `sin (2·)`.**  For every `r` there is a trigonometric
polynomial `P` with `Lop^[r] (sin 2·) = sin (2·) · P` as functions. -/
private lemma Lop_iter_sin2_div (r : ℕ) : ∃ P : ℝ → ℝ,
    LopTrig.TP P ∧ (Work.Spaces.Lop^[r]) S2 = S2 * P := by
  induction r with
  | zero =>
      refine ⟨fun _ => (1 : ℝ), TP_one, ?_⟩
      funext θ
      show S2 θ = S2 θ * 1
      ring
  | succ r ih =>
      obtain ⟨P, hP, hdiv⟩ := ih
      refine ⟨deriv S2 * P + S2 * deriv P, ?_, ?_⟩
      · exact LopTrig.TP.add (LopTrig.TP.mul (LopTrig.TP_deriv LopTrig.TP.sin2) hP)
          (LopTrig.TP.mul LopTrig.TP.sin2 (LopTrig.TP_deriv hP))
      · rw [Function.iterate_succ_apply', hdiv]
        funext θ
        rw [show Work.Spaces.Lop (S2 * P) θ = S2 θ * deriv (S2 * P) θ from rfl,
          LopTrig.deriv_mul_TP (f := S2) (g := P) LopTrig.TP.sin2 hP]
        simp only [Pi.add_apply, Pi.mul_apply]

/-- **The iterates of `Lop` applied to `sin (2·)` are divisible by `sin (2·)`, with a constant
uniform for the finitely many orders `≤ n`.**

With `Lop u = sin(2θ)·u'` one has `Lop^r (sin 2·) = sin(2·) · P_r` for a trigonometric polynomial
`P_r` (the class `Work.FTS.PhiStar.LinvFlat.LopTrig.TP` of
`Submission/Work/FTS/PhiStar/LinvFlat/Lop_iter_sin_cos_bound.lean` is closed under `Lop` and under
`deriv`), hence the bound.  This is the angular coefficient bound used by the Leibniz expansion
of `D_θ^j` in terms of `∂_θ`-slots. -/
theorem sfun_Lop_iter_le (n : ℕ) : ∃ A : ℝ, 0 < A ∧ ∀ r : ℕ, r ≤ n →
    ∀ θ ∈ Work.Spaces.Iθ,
      |(Work.Spaces.Lop^[r]) (fun θ' => Real.sin (2 * θ')) θ| ≤ A * Real.sin (2 * θ) := by
  -- choose the trigonometric polynomials `P r` dividing the iterates
  have hex : ∀ r : ℕ, ∃ P : ℝ → ℝ, LopTrig.TP P ∧ (Work.Spaces.Lop^[r]) S2 = S2 * P :=
    Lop_iter_sin2_div
  choose P hP using hex
  -- and bound each of them
  have hbdd : ∀ r : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : ℝ, |P r θ| ≤ M :=
    fun r => LopTrig.TP_bdd (hP r).1
  choose M hM using hbdd
  refine ⟨1 + ∑ s ∈ Finset.range (n + 1), M s, ?_, ?_⟩
  · have hnn : 0 ≤ ∑ r ∈ Finset.range (n + 1), M r :=
      Finset.sum_nonneg fun r _ => (hM r).1
    linarith
  · intro r hr θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · have : (0 : ℝ) ≤ θ := hθ.1
        linarith
      · have : θ ≤ Real.pi / 2 := hθ.2
        linarith
    have hdivr : (Work.Spaces.Lop^[r]) (fun θ' : ℝ => Real.sin (2 * θ')) θ
        = Real.sin (2 * θ) * P r θ := by
      have h1 : (fun θ' : ℝ => Real.sin (2 * θ')) = S2 := rfl
      rw [h1, (hP r).2]
      rfl
    have hMr : M r ≤ ∑ s ∈ Finset.range (n + 1), M s :=
      Finset.single_le_sum (fun i _ => (hM i).1) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
    have hA : M r ≤ 1 + ∑ s ∈ Finset.range (n + 1), M s := by
      have hnn : 0 ≤ ∑ s ∈ Finset.range (n + 1), M s :=
        Finset.sum_nonneg fun s _ => (hM s).1
      linarith
    rw [hdivr, abs_mul, abs_of_nonneg hsin]
    calc Real.sin (2 * θ) * |P r θ| ≤ Real.sin (2 * θ) * M r :=
          mul_le_mul_of_nonneg_left ((hM r).2 θ) hsin
      _ ≤ Real.sin (2 * θ) * (1 + ∑ s ∈ Finset.range (n + 1), M s) :=
          mul_le_mul_of_nonneg_left hA hsin
      _ = (1 + ∑ s ∈ Finset.range (n + 1), M s) * Real.sin (2 * θ) := by ring

end Work.FTS.PhiStar.CoreAux.AngSlot
