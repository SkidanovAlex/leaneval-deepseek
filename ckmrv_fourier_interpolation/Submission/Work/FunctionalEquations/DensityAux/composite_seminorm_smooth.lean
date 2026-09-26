import Mathlib
import Submission.Work.RadialSpace.Basic
import Submission.Work.Radial.composite_seminorm

/-!
# The composite seminorm bound for a `C^∞` profile

This is the `C^∞` (as opposed to analytic) version of
`Work.Radial.composite_seminorm`.  If `Ψ : ℝ → ℂ` is `C^∞` on `[0,∞)` with all its
derivatives up to order `l` bounded by `(1+t)^{-(k+2l)} L`, then the radial
function `x ↦ Ψ(‖x‖²)` on `ℝ^n` satisfies

  `‖x‖^k * ‖D^l (Ψ ∘ ‖·‖²) x‖ ≤ C * L`

for a constant `C` depending only on `n`, `k`, `l`.  The proof is the Faà di
Bruno/Taylor-composition argument of `composite_seminorm`, run at the finite
order `l` (which is all that is needed) rather than at the analytic order `⊤`.
-/

noncomputable section

open scoped ContDiff
open Set

namespace Work.FunctionalEquations.DensityAux

theorem composite_seminorm_smooth (n : ℕ) [NeZero n] (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → ℂ) (L : ℝ),
      ContDiffOn ℝ Work.RadialSpace.Smooth Ψ (Set.Ici 0) →
      (∀ j : ℕ, j ≤ l → ∀ t : ℝ, 0 ≤ t →
        (1 + t) ^ (k + 2 * l) * ‖iteratedDerivWithin j Ψ (Set.Ici 0) t‖ ≤ L) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x : EuclideanSpace ℝ (Fin n) => Ψ (‖x‖ ^ 2)) x‖
          ≤ C * L := by
  refine ⟨(4:ℝ)^l * (Fintype.card (OrderedFinpartition l) : ℝ), by positivity, ?_⟩
  intro Ψ L hΨ hL x
  -- `L` is nonnegative, since the `0`-th derivative inequality at `t = 0` reads `‖Ψ 0‖ ≤ L`.
  have hL0 : 0 ≤ L := by
    have h := hL 0 (Nat.zero_le l) 0 (le_refl 0)
    have h2 : ‖iteratedDerivWithin 0 Ψ (Set.Ici (0:ℝ)) (0:ℝ)‖ ≤ L := by simpa using h
    exact le_trans (norm_nonneg _) h2
  -- The order `l` is below `Smooth`, so `Ψ` is `C^l` within `[0,∞)`.
  have hle : (l : ℕ∞ω) ≤ Work.RadialSpace.Smooth := by
    rw [Work.RadialSpace.Smooth]
    exact WithTop.coe_le_coe.mpr le_top
  -- Faà di Bruno for `Ψ ∘ (‖·‖²)` on the domain `[0,∞)`, at the finite order `l`.
  have hkey : iteratedFDeriv ℝ l (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖^2)) x
      = (ftaylorSeriesWithin ℝ Ψ (Set.Ici (0:ℝ)) (‖x‖^2)).taylorComp
          (ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x) l := by
    have hcomp := iteratedFDerivWithin_comp (𝕜 := ℝ) (s := Set.univ) (t := Set.Ici (0:ℝ))
      (f := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) (g := Ψ) (x := x)
      (n := (l : ℕ∞ω)) (i := l)
      ((hΨ.contDiffWithinAt (sq_nonneg ‖x‖)).of_le hle)
      ((contDiff_norm_sq ℝ (n := (l : ℕ∞ω))).contDiffAt)
      (uniqueDiffOn_Ici 0) uniqueDiffOn_univ (mem_univ x) (fun y _ => sq_nonneg ‖y‖) le_rfl
    rw [iteratedFDerivWithin_univ] at hcomp
    exact hcomp
  -- Uniform bound on the `q`-terms, coming from the hypothesis on `Ψ`.
  have hq : ∀ j : ℕ, j ≤ l →
      ‖ftaylorSeriesWithin ℝ Ψ (Set.Ici (0:ℝ)) (‖x‖^2) j‖
        ≤ L / (1 + ‖x‖^2)^(k+2*l) := by
    intro j hj
    have hqj : ftaylorSeriesWithin ℝ Ψ (Set.Ici (0:ℝ)) (‖x‖^2) j
        = iteratedFDerivWithin ℝ j Ψ (Set.Ici 0) (‖x‖^2) := rfl
    rw [hqj, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    rw [le_div_iff₀ (by positivity)]
    have h := hL j hj (‖x‖^2) (sq_nonneg ‖x‖)
    have h' : ‖iteratedDerivWithin j Ψ (Set.Ici 0) (‖x‖^2)‖ * (1 + ‖x‖^2)^(k+2*l) ≤ L := by
      rw [mul_comm]; exact h
    exact h'
  -- Uniform bound on the `p`-terms, coming from the quadratic nature of `‖·‖²`.
  have hp : ∀ m : ℕ, m ≤ l →
      ‖ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x m‖
        ≤ 2*(1+‖x‖)^2 := by
    intro m _
    have hpm : ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x m
        = iteratedFDeriv ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) x := by
      rw [show ftaylorSeriesWithin ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x m
            = iteratedFDerivWithin ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^2) Set.univ x
            from rfl, iteratedFDerivWithin_univ]
    rw [hpm]
    exact Work.Radial.norm_iteratedFDeriv_norm_sq_le m x
  have hnorm : ‖iteratedFDeriv ℝ l (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖^2)) x‖
      ≤ (Fintype.card (OrderedFinpartition l) : ℝ)
          * (L / (1 + ‖x‖^2)^(k+2*l)) * (2*(1+‖x‖)^2)^l := by
    rw [hkey]
    exact Work.Radial.norm_taylorComp_le l (L / (1 + ‖x‖^2)^(k+2*l)) (2*(1+‖x‖)^2)
      (by nlinarith [norm_nonneg x]) _ _ hq hp
  -- The elementary numerical inequality `‖x‖^k * (2(1+‖x‖)^2)^l ≤ 4^l * (1+‖x‖^2)^(k+2l)`.
  have hmain : ‖x‖^k * (2*(1+‖x‖)^2)^l ≤ 4^l * (1 + ‖x‖^2)^(k+2*l) := by
    have hx1 : ‖x‖ ≤ 1 + ‖x‖^2 := by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1/2)]
    have hxk : ‖x‖^k ≤ (1 + ‖x‖^2)^k := pow_le_pow_left₀ (norm_nonneg x) hx1 k
    have hB_le : (2*(1+‖x‖)^2)^l ≤ 4^l * (1 + ‖x‖^2)^l := by
      have h1 : (1 + ‖x‖)^2 ≤ 2*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
      calc (2*(1+‖x‖)^2)^l
          = 2^l * ((1+‖x‖)^2)^l := by rw [mul_pow]
        _ ≤ 2^l * (2*(1+‖x‖^2))^l :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 l) (by positivity)
        _ = 2^l * (2^l * (1 + ‖x‖^2)^l) := by rw [mul_pow]
        _ = ((2:ℝ)^l * 2^l) * (1 + ‖x‖^2)^l := by ring
        _ = 4^l * (1 + ‖x‖^2)^l := by
              rw [show (2:ℝ)^l * 2^l = 4^l from by rw [← mul_pow]; norm_num]
    calc ‖x‖^k * (2*(1+‖x‖)^2)^l
        ≤ (1 + ‖x‖^2)^k * (4^l * (1 + ‖x‖^2)^l) :=
          mul_le_mul hxk hB_le (by positivity) (by positivity)
      _ = 4^l * (1 + ‖x‖^2)^(k+l) := by
          rw [show (1 + ‖x‖^2)^k * (4^l * (1 + ‖x‖^2)^l)
                = 4^l * ((1 + ‖x‖^2)^k * (1 + ‖x‖^2)^l) from by ring, ← pow_add]
      _ ≤ 4^l * (1 + ‖x‖^2)^(k+2*l) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by linarith [sq_nonneg ‖x‖]) (by omega)
  have hDle : ‖x‖^k * (2*(1+‖x‖)^2)^l / (1 + ‖x‖^2)^(k+2*l) ≤ 4^l := by
    rw [div_le_iff₀ (by positivity)]
    exact hmain
  calc ‖x‖^k * ‖iteratedFDeriv ℝ l (fun y : EuclideanSpace ℝ (Fin n) => Ψ (‖y‖^2)) x‖
      ≤ ‖x‖^k * ((Fintype.card (OrderedFinpartition l) : ℝ)
            * (L / (1 + ‖x‖^2)^(k+2*l)) * (2*(1+‖x‖)^2)^l) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (Fintype.card (OrderedFinpartition l) : ℝ) * L
          * (‖x‖^k * (2*(1+‖x‖)^2)^l / (1 + ‖x‖^2)^(k+2*l)) := by ring
    _ ≤ (Fintype.card (OrderedFinpartition l) : ℝ) * L * 4^l := by
          apply mul_le_mul_of_nonneg_left hDle
          exact mul_nonneg (Nat.cast_nonneg _) hL0
    _ = ((4:ℝ)^l * (Fintype.card (OrderedFinpartition l) : ℝ)) * L := by ring

end Work.FunctionalEquations.DensityAux
