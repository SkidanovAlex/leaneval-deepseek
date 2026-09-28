import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.veronese_key
import Submission.Work.HP.IntForm

/-!
# Upper bound for `det Γ_{x,y}`

For primitive linearly independent `x, y`, the covolume of `Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)}` is at
most `N_{d,n} · (‖x‖‖y‖)^d`.  This is (the upper half of) Lemma "upper and lower bounds det" of
Browning--Le Boudec--Sawin (Annals 2023); only an upper bound is needed here, to absorb the
`A log(μ(x,y))` error term of the ball-counting estimate.

Route.  `detL (Gam d n x y) = wedgeNorm (νx) (νy) / |gcdMinors2 x y|` (`Work.HP.veronese_key`),
`wedgeNorm v w = √(‖v‖²‖w‖² - ⟪v,w⟫²) ≤ ‖v‖‖w‖`, and `‖ν(z)‖ ≤ √(N_{d,n}) · ‖z‖^d`
(`Work.HP.rNorm_veronese_le` in `Submission/Work/HP/IntForm.lean`).
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.MDEstimates

open Work.HP

theorem detL_Gam_upper (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hli : LinearIndependent ℤ ![x, y]) :
    detL (Gam d n x y) ≤ (NN d n : ℝ) * (eNorm x * eNorm y) ^ d := by
  obtain ⟨-, -, hdet⟩ := veronese_key d n hd hn x y hx hy hli
  rw [hdet]
  have hwnn : 0 ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
    rw [wedgeNorm]; exact Real.sqrt_nonneg _
  have hsplit : wedgeNorm (veronese d n x) (veronese d n y) / |(gcdMinors2 x y : ℝ)|
      ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
    by_cases hg : gcdMinors2 x y = 0
    · rw [hg, Int.cast_zero, abs_zero, div_zero]; exact hwnn
    · refine div_le_self hwnn ?_
      have h1 : (1 : ℤ) ≤ |gcdMinors2 x y| := Int.one_le_abs hg
      exact_mod_cast h1
  have hwedge : wedgeNorm (veronese d n x) (veronese d n y)
      ≤ eNorm (veronese d n x) * eNorm (veronese d n y) := by
    have h1 : eNorm (veronese d n x) ^ 2 * eNorm (veronese d n y) ^ 2
        - dotR (toR (veronese d n x)) (toR (veronese d n y)) ^ 2
        ≤ (eNorm (veronese d n x) * eNorm (veronese d n y)) ^ 2 := by
      rw [mul_pow]
      linarith [sq_nonneg (dotR (toR (veronese d n x)) (toR (veronese d n y)))]
    rw [wedgeNorm]
    exact (Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr h1
  have htoR : ∀ z : Fin (n + 1) → ℤ, toR (veronese d n z) = veronese d n (toR z) := by
    intro z
    funext m
    simp only [toR, veronese]
    push_cast
    rfl
  have hxle : eNorm (veronese d n x) ≤ Real.sqrt (NN d n) * eNorm x ^ d := by
    have h := rNorm_veronese_le (d := d) (n := n) (x := toR x) (R := eNorm x)
      (Real.sqrt_nonneg _) (le_of_eq rfl)
    rwa [← htoR x] at h
  have hyle : eNorm (veronese d n y) ≤ Real.sqrt (NN d n) * eNorm y ^ d := by
    have h := rNorm_veronese_le (d := d) (n := n) (x := toR y) (R := eNorm y)
      (Real.sqrt_nonneg _) (le_of_eq rfl)
    rwa [← htoR y] at h
  have henorn : ∀ {ι : Type} [Fintype ι] (v : ι → ℤ), 0 ≤ eNorm v := fun v =>
    Real.sqrt_nonneg _
  refine le_trans hsplit ?_
  refine le_trans hwedge ?_
  calc eNorm (veronese d n x) * eNorm (veronese d n y)
      ≤ (Real.sqrt (NN d n) * eNorm x ^ d) * (Real.sqrt (NN d n) * eNorm y ^ d) :=
        mul_le_mul hxle hyle (henorn (veronese d n y))
          (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (henorn x) d))
    _ = (NN d n : ℝ) * (eNorm x * eNorm y) ^ d := by
        have hsq : Real.sqrt (NN d n) * Real.sqrt (NN d n) = (NN d n : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg _)
        calc (Real.sqrt (NN d n) * eNorm x ^ d) * (Real.sqrt (NN d n) * eNorm y ^ d)
            = (Real.sqrt (NN d n) * Real.sqrt (NN d n)) * (eNorm x ^ d * eNorm y ^ d) := by ring
          _ = (NN d n : ℝ) * (eNorm x ^ d * eNorm y ^ d) := by rw [hsq]
          _ = (NN d n : ℝ) * (eNorm x * eNorm y) ^ d := by rw [mul_pow]

end Work.HP.MDEstimates
