import Mathlib
import Submission.Work.Peluse.SwapC.GCS

namespace Work.Peluse.SwapC

open scoped BigOperators

/-- **The multilinear Gowers–Cauchy–Schwarz inequality for the multiset cube sum** (Peluse's
Lemma 2.3 in the vocabulary of this chapter).  For `1 ≤ d` and finitely supported functions
`F ω`, the general cube sum over the index type `X` is bounded by the product of the
`d`-dimensional box norms of the `F ω`, each normalised by the *same* index set `X`.

This is `Work.Peluse.BoxNorm.prodCubeSum_norm_le` with the coordinate type product
`(i : Fin d) → {x // x ∈ Q i}` replaced by `(i : Fin d) → X` and the direction sets `Q i` replaced
by an arbitrary direction map `ν i : X → ℤ`; the existing proof (`winForm_norm_le`: Cauchy–Schwarz
at `d = 1`, then split the first coordinate, Cauchy–Schwarz, induction and generalized Hölder) is
index-set agnostic, so the statement is the honest generalisation and not a weakening.
(The case `d = 0` is *excluded* on purpose: there the cube sum is `|S|⁻¹∑_x F 0 x`, which need not
be bounded by `‖F 0‖`.)

Consumed by `concatStep` (KKL Lemma 6.1), whose `(E)` box inner product is a `mCubeSum` with
`X := Fin M × Fin M`. -/
theorem mCubeSum_norm_le (d : ℕ) (hd : 1 ≤ d) (X : Type) [Fintype X] (ν : Fin d → X → ℤ)
    (S : Finset ℤ) (F : (Fin d → Bool) → ℤ → ℂ) (hF : ∀ ω : Fin d → Bool,
      Work.Peluse.FinSuppZ (F ω)) :
    ‖Work.Peluse.SwapC.mCubeSum d X ν S F‖
      ≤ ∏ ω : Fin d → Bool,
          (‖Work.Peluse.SwapC.mCubeSum d X ν S (fun _ => F ω)‖) ^ (1 / (2 : ℝ) ^ d) := by
  classical
  choose N hN using hF
  set N₀ : ℕ := ∑ ω : Fin d → Bool, N ω with hN₀
  have hsupp : ∀ ω : Fin d → Bool, Work.Peluse.SupportIn (F ω) N₀ := by
    intro ω
    refine (hN ω).mono ?_
    rw [hN₀]
    exact Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ ω)
  set W : Finset ℤ := gWindow N₀ (dirMass ν) with hW
  set c : ℝ := ((S.card : ℝ))⁻¹ * ((Fintype.card X : ℝ))⁻¹ ^ (2 * d) with hc
  have hcpos : 0 ≤ c := by rw [hc]; positivity
  have key : ∀ φ : (Fin d → Bool) → ℤ → ℂ, (∀ ω, Work.Peluse.SupportIn (φ ω) N₀) →
      ‖mCubeSum d X ν S φ‖ = c * ‖cWinForm d X ν W φ‖ := by
    intro φ hφ
    rw [norm_mCubeSum_eq d X ν S φ hφ, hc, hW, ← cWinForm_eq_gWinForm]
  have hmain := cWinForm_norm_le d hd X ν W F
  have hR : (∏ ω : Fin d → Bool,
      (‖mCubeSum d X ν S (fun _ => F ω)‖) ^ (1 / (2 : ℝ) ^ d))
      = c * ∏ ω : Fin d → Bool, cWinNorm d X ν W (F ω) := by
    rw [Real.finsetProd_rpow Finset.univ (fun ω => ‖mCubeSum d X ν S (fun _ => F ω)‖)
      (fun ω _ => norm_nonneg _) (1 / (2 : ℝ) ^ d)]
    have hfac : ∀ ω ∈ (Finset.univ : Finset (Fin d → Bool)),
        ‖mCubeSum d X ν S (fun _ => F ω)‖ = c * (cWinNorm d X ν W (F ω)) ^ (2 ^ d) := by
      intro ω _
      rw [key (fun _ => F ω) (fun _ => hsupp ω)]
      congr 1
      exact (cWinNorm_pow d X ν W (F ω)).symm
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Finset.prod_pow]
    have hexp : (((2 : ℕ) ^ d : ℕ) : ℝ) * (1 / (2 : ℝ) ^ d) = 1 := by
      push_cast; field_simp
    have hP : 0 ≤ ∏ ω : Fin d → Bool, cWinNorm d X ν W (F ω) :=
      Finset.prod_nonneg fun ω _ => cWinNorm_nonneg
    rw [← mul_pow]
    rw [← Real.rpow_natCast (c * (∏ ω : Fin d → Bool, cWinNorm d X ν W (F ω))) (2 ^ d),
      ← Real.rpow_mul (mul_nonneg hcpos hP), hexp, Real.rpow_one]
  rw [key F hsupp, hR]
  exact mul_le_mul_of_nonneg_left hmain hcpos

end Work.Peluse.SwapC
