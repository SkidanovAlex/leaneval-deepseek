import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.halasz_inequality
import Submission.Work.ZeroDensity.Jutila.dualityAchieves

namespace Work.ZeroDensity.Jutila

open Finset

/-- **The Halász + duality frame of Jutila §3.**  This is the joint that turns the detector into a
bound on the size `J` of the well-spaced system, and it is the only step of §3 that is genuinely a
*duality* step rather than a computation with the specific mollifier.

Given a finite index set `ι` (the `Δ`-well-spaced system `(χ_j, ρ_j)`, `J = #ι`), coefficients
`a : ℕ → ℂ` and a weight `β > 0` on `1 ≤ n ≤ N`, functions `f i : ℕ → ℂ` (for a zero `ρ` of `χ`,
`f i n = χ(n) n^{-ρ}`), a level `V ≥ 0` with `‖Σ_{n ≤ N} a n · f i n‖ ≥ V` for every `i` (the
*detector* lower bound, slot (6.d)), and a bound `B ≥ 0` with
`Σ_{n ≤ N} β n · ‖Σ_i η i · f i n‖² ≤ B` for every `η` with `Σ_i ‖η i‖² ≤ 1` (the *bilinear form*
evaluation, the slot of Lemmas 3 and 4), one has `J · V² ≤ (Σ_{n ≤ N} ‖a n‖² / β n) · B`.

Proof (two halves, both already in the workspace): Halász's inequality — file
`Submission/Commons/NumberTheory/DirichletCharacter/halasz_inequality.lean`, module
`Commons.NumberTheory.DirichletCharacter.halasz_inequality`, which must be imported explicitly —
gives `‖Σ_i η_i P_i‖² ≤ (Σ_n ‖a n‖²/β n)·(Σ_n β n ‖Σ_i η_i f i n‖²)` for the Dirichlet polynomials
`P_i = Σ_{n ≤ N} a n f i n`; Cauchy–Schwarz duality in the finite-dimensional space `ι → ℂ` gives
`Σ_i ‖P_i‖² = (sup_{Σ‖η‖² ≤ 1} ‖Σ_i η_i P_i‖)²`; combining with the detector lower bound
`J·V² ≤ Σ_i ‖P_i‖²` gives the claim. -/
theorem halaszDualityFrame {ι : Type*} [Fintype ι] {N : ℕ} (a : ℕ → ℂ) (β : ℕ → ℝ)
    (hβ : ∀ n ∈ Finset.Icc 1 N, 0 < β n) (f : ι → ℕ → ℂ) (V B : ℝ) (hV : 0 ≤ V)
    (hdet : ∀ i, V ≤ ‖∑ n ∈ Finset.Icc 1 N, a n * f i n‖)
    (hbilin : ∀ η : ι → ℂ, (∑ i, ‖η i‖ ^ 2) ≤ 1 →
      (∑ n ∈ Finset.Icc 1 N, β n * ‖∑ i, η i * f i n‖ ^ 2) ≤ B)
    (hB : 0 ≤ B) :
    (Fintype.card ι : ℝ) * V ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / β n) * B := by
  classical
  -- The Dirichlet polynomials of the well-spaced system.
  let P : ι → ℂ := fun i => ∑ n ∈ Finset.Icc 1 N, a n * f i n
  -- The two quantities of the frame: the weighted `ℓ²` mass of `a`, and the `ℓ²` mass of the `P i`.
  let A : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / β n
  let Z : ℝ := ∑ i, ‖P i‖ ^ 2
  have hdet' : ∀ i, V ≤ ‖P i‖ := fun i => hdet i
  have hAnn : 0 ≤ A :=
    Finset.sum_nonneg (fun n hn => div_nonneg (sq_nonneg _) (le_of_lt (hβ n hn)))
  have hZnn : 0 ≤ Z := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- Half one: the detector lower bound summed over the system gives `J · V² ≤ ∑_i ‖P_i‖²`.
  have hJV : (Fintype.card ι : ℝ) * V ^ 2 ≤ Z := by
    have h1 : ∀ i, V ^ 2 ≤ ‖P i‖ ^ 2 := fun i => by
      have h := hdet' i
      nlinarith [norm_nonneg (P i), hV, h]
    calc (Fintype.card ι : ℝ) * V ^ 2 = ∑ _i : ι, V ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i, ‖P i‖ ^ 2 := Finset.sum_le_sum (fun i _ => h1 i)
      _ = Z := rfl
  rcases lt_or_eq_of_le hZnn with hZpos | hZeq
  · -- Half two: duality picks the extremal weight in the unit ball, and Halász bounds it.
    obtain ⟨η, hη, hηeq⟩ := dualityAchieves P hZpos
    have hX : (∑ n ∈ Finset.Icc 1 N, β n * ‖∑ i, η i * f i n‖ ^ 2) ≤ B := hbilin η hη
    have hmain : Z ≤ A * (∑ n ∈ Finset.Icc 1 N, β n * ‖∑ i, η i * f i n‖ ^ 2) := by
      rw [show Z = ‖∑ i, η i * P i‖ ^ 2 from hηeq.symm]
      exact Commons.NumberTheory.DirichletCharacter.halasz_inequality a β hβ f η
    calc (Fintype.card ι : ℝ) * V ^ 2 ≤ Z := hJV
      _ ≤ A * (∑ n ∈ Finset.Icc 1 N, β n * ‖∑ i, η i * f i n‖ ^ 2) := hmain
      _ ≤ A * B := mul_le_mul_of_nonneg_left hX hAnn
  · -- Degenerate case: all the `P i` vanish, so `V = 0` and the left side is `0`.
    have hJV' : (Fintype.card ι : ℝ) * V ^ 2 ≤ 0 := by
      rw [hZeq.symm] at hJV
      exact hJV
    have hcnn : 0 ≤ (Fintype.card ι : ℝ) * V ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hAB : 0 ≤ A * B := mul_nonneg hAnn hB
    linarith

end Work.ZeroDensity.Jutila
