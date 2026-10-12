import ChallengeDeps
import Submission.Work.BoseFixR.BigMVRatio
import Submission.Work.BoseFixR.ErrLHYBudget
import Submission.Work.BoseFixR.ErrResRegimeA
import Submission.Work.BoseFixR.ErrResRegimeB
import Submission.Work.BoseFixR.FsXPowBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/RB5FSArith2.lean` — the far-leg arithmetic (FS §9)

The far-leg bound `Work.BoseFixR.RB5FSHonest` consumes the purely scalar statement
proved here: on the far region `FarCond v μ ρ` (i.e. `|ρ − μ| ≥ μK_ℓ^{-2}`), the
crude residual budget `ErrRes v μ ρ`, the `n₊`-slot error
`|ρ−μ|·16πa·16𝓜` and the LHY margin `errLHY v μ` together fit into the
`c`-number's quadratic margin `4πa(ρ−μ)²ℓ³` of FS `eq:SimplifyKz`.

**The mathematics.**  Write `A = a v`, `T = μA³` (the diluteness), `X = T^{1/323}`
(FS's `X`), `L = ℓ = K_ℓ(μA)^{-1/2}` and `M = 𝓜 = K_𝓜(μA³)^{-1/4}`
(`Work.BoseFixR.bigMV`).  Two identities (the child `BigMVRatio`) reduce
everything to powers of `X`:

* `M = X^{337/4} · (μL³)`, i.e. `M/(μL³) = X^{337/4}` and `μL³ = X^{-166}`,
  so `√(L³M) = L³·X^{337/8}·√μ` and every ratio below is a monomial in `X`.

The diluteness bound `T ≤ ε₀ ≤ 10^{-4000}` gives `X^{289/8} ≤ 10^{-400}`
(`FsXPowBound`), hence the single numeric slack used throughout,

  `10^{300}·X^{289/8} ≤ 1/6`

(the `10^{300}` is the absolute constant of `ErrRes`).  Splitting on
`ρ ≤ 2μ` / `ρ ≥ 2μ`, FS's `FarCond` gives in the first regime `|ρ−μ| ≤ μ`,
`ρ+μ ≤ 3μ` and `(ρ−μ)² ≥ μ²X⁶`, in the second `|ρ−μ| ≥ ρ/2`, `ρ+μ ≤ 3ρ/2`; in
both regimes each of the four terms of the left-hand side is at most a quarter of
the margin `4πA(ρ−μ)²L³` (children `ErrResRegimeA`/`ErrResRegimeB`), the LHY term
using `errLHY v μ ≤ πAμ²L³X⁶` (`ErrLHYBudget`, i.e. `8·lhyC·√T ≤ X⁶`; the sharp
`lhyC = 128/(15√π)` is defeated by the astronomical power `X^{-311/646}` of the
diluteness).

All four children are pure real arithmetic; this file is their assembly.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix

set_option linter.unusedVariables false

-- the numeric slacks below are `10^{300}·10^{-400} ≤ 1/6`, so `norm_num` has to be
-- allowed to evaluate powers of `10` with exponent up to `4000`
set_option exponentiation.threshold 5000

theorem RB5FSArith2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < BoseGases.a v)
    {ε₀ μ ρ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ))) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hρ : 0 ≤ ρ) (hfar : Work.BoseFixR.FarCond v μ ρ) :
    Work.BoseFixR.ErrRes v μ ρ
      + |ρ - μ| * (16 * Real.pi * BoseGases.a v) * (16 * Work.BoseFixR.bigMV v μ)
      + Work.BoseFixR.errLHY v μ
      ≤ 4 * Real.pi * BoseGases.a v * (ρ - μ) ^ 2 * Work.BoseFixR.ell v μ ^ 3 := by
  obtain ⟨hμ, hdilε₀, -⟩ := hAdm
  -- the diluteness and its consequences
  have hdil : dil v μ ≤ (10 : ℝ) ^ (-(4000 : ℤ)) := le_trans hdilε₀ hε₀
  have ht0 : 0 < dil v μ := by rw [dil]; positivity
  have ht1 : dil v μ ≤ 1 := le_trans hdil (by norm_num)
  have hell : 0 < ell v μ := by
    rw [ell, sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact mul_pos (Work.BoseBox.fsXp_pos ht0) (Real.rpow_pos_of_pos (by positivity) _)
  -- FS's `X = (μa³)^{1/323}`
  set X := fsX v μ with hXdef
  have hX0 : 0 < X := by
    rw [hXdef, fsX, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos ht0 _
  have hX1 : X ≤ 1 := by
    rw [hXdef, fsX, Work.BoseBox.fsXp]
    calc (dil v μ) ^ (1 / 323 : ℝ) ≤ 1 ^ (1 / 323 : ℝ) :=
          Real.rpow_le_rpow ht0.le ht1 (by norm_num)
      _ = 1 := by norm_num
  -- the FS identity, in the form of the ratio `𝓜/(μℓ³) = X^{337/4}`
  have hML : bigMV v μ = X ^ (337 / 4 : ℝ) * (μ * ell v μ ^ 3) := BigMVRatio hav hμ
  have hM0 : 0 < bigMV v μ := by rw [hML]; positivity
  -- the numeric slack: `10^300 · X^{289/8} ≤ 1/6`
  have hslack : (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ 1 / 6 := by
    have hb : X ^ (289 / 8 : ℝ) ≤ (1 : ℝ) / 10 ^ 400 := by
      refine le_trans (FsXPowBound hav hμ hdil) ?_
      norm_num
    calc (10 : ℝ) ^ 300 * X ^ (289 / 8 : ℝ) ≤ (10 : ℝ) ^ 300 * (1 / 10 ^ 400) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 1 / 10 ^ 100 := by norm_num
      _ ≤ 1 / 6 := by norm_num
  -- the LHY budget
  have hE : Work.BoseFixR.errLHY v μ
      ≤ Real.pi * BoseGases.a v * μ ^ 2 * ell v μ ^ 3 * X ^ 6 := ErrLHYBudget hav hμ hdil
  -- `FarCond` in the form the children consume: `μX³ ≤ |ρ−μ|`
  have hfarX : μ * X ^ 3 ≤ |ρ - μ| := by
    have hcl : closeThreshold v μ = μ * (dil v μ) ^ (3 / 323 : ℝ) := by
      rw [closeThreshold, Kl_inv_sq v hμ hav]
    have hX3 : X ^ 3 = (dil v μ) ^ (3 / 323 : ℝ) := by
      rw [hXdef, fsX, Work.BoseBox.fsXp, ← Real.rpow_natCast (dil v μ ^ (1 / 323 : ℝ)) 3,
        ← Real.rpow_mul ht0.le]
      congr 1
      norm_num
    rw [hX3, ← hcl]
    exact hfar
  -- reassociate the `n₊`-slot error into the children's normal form
  have hkey : Work.BoseFixR.ErrRes v μ ρ
        + |ρ - μ| * (16 * Real.pi * BoseGases.a v) * (16 * bigMV v μ)
        + Work.BoseFixR.errLHY v μ
      = (10 : ℝ) ^ 300 * ((ρ + μ) * BoseGases.a v * bigMV v μ
            + (ρ + μ) ^ (3 / 2 : ℝ) * BoseGases.a v
                * Real.sqrt (ell v μ ^ 3 * bigMV v μ))
          + |ρ - μ| * (256 * Real.pi * BoseGases.a v * bigMV v μ)
          + Work.BoseFixR.errLHY v μ := by
    rw [ErrRes]
    ring
  rw [hkey]
  rcases le_total ρ (2 * μ) with hc | hc
  · -- the near regime `ρ ≤ 2μ`
    have hreg := ErrResRegimeA (A := BoseGases.a v) (μ := μ) (ρ := ρ)
      (L := ell v μ) (M := bigMV v μ) (X := X)
      hav hμ hρ hc hell hM0 hX0 hX1 hfarX hML hslack
    exact le_trans (add_le_add (le_refl _) hE) hreg
  · -- the far regime `2μ ≤ ρ`
    have hreg := ErrResRegimeB (A := BoseGases.a v) (μ := μ) (ρ := ρ)
      (L := ell v μ) (M := bigMV v μ) (X := X)
      hav hμ hc hell hM0 hX0 hX1 hfarX hML hslack
    exact le_trans (add_le_add (le_refl _) hE) hreg

end Work.BoseFixR
