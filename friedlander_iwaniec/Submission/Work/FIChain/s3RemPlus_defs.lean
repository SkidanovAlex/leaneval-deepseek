import Mathlib
import Submission.Work.FIChain.s3InnerInt_eq_split
import Submission.Work.FIChain.S3plusC_uIntegral_reduce
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.remainder_all_at_07

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-
# `Submission.Work.FIChain.s3RemPlus_defs` — the `(1.7)`-halves of the `λ⁺`-inner sum

After the `(1.7)`-split of the level integrand (`Work.FIChain.s3InnerInt_eq_split`, proved),

    s3InnerInt atilc x ℓ Cm z sz
      = ∫_1^{U_ℓ} (du/u) Σ_{d ≤ ⌊u⌋₊} μ d ·
          ( FIgtil (ℓ d) · (Ã(⌊min (ℓ sz) x⌋₊) − Ã(⌊max (ℓ z) (ℓ Cm u)⌋₊))       -- MAIN
          + r̃(ℓ d, ⌊min (ℓ sz) x⌋₊) − r̃(ℓ d, ⌊max (ℓ z) (ℓ Cm u)⌋₊) ),          -- REM

with `U_ℓ = min (sz/Cm) (x/(ℓ Cm))`, the `λ⁺` half of `S₃`,
`S3plusC atilc lam x z sy sz Cm = Σ_ℓ (Σ_{b | ℓ, sy < b} μ b)·ρ(ℓ)·S3plusInnerC(ℓ)`, splits into
`Work.FIChain.s3MainPlus` and `Work.FIChain.s3RemPlus` (`S3plusC_eq_main_add_rem` below).  The
`ℓ`-sum carries the indicator `ℓ·z ≤ x`, because `s3InnerInt_eq_split` needs `(ℓ:ℝ)·z ≤ x` and for
`ℓ·z > x` the inner `c`-filter `z < c ∧ c ≤ sz ∧ ℓ c ≤ x` is empty
(`S3plusInnerC_eq_zero_of_mul_lt`, proved here).

**The REM half shares MAIN's obstruction, and this is decisive** (see
`NOTES_S3plusC_session9.md` §8).  The `(R′)`-arguments `m₁ = ⌊max (ℓz) (ℓ Cm u)⌋₊`,
`m₂ = ⌊min (ℓ sz) x⌋₊` depend on the *outer* index `ℓ` (even inside a fixed fibre of the modulus
`ζ = ℓ d`), so:

* grouping by the fibre `ζ = ebd` needs one `(R′)`-application per *scale* in the fibre — up to
  `τ(ζ)` of them — and loses `Σ_{ζ≤D₇}(fibre weight)/τ(ζ)^5 ≍ D₇(log D₇)^{-3/4}` (a prover's
  verdict on the `(log x)^{-2}` request);
* applying `(R′)` once per `ℓ` instead (it *is* uniform in `m`, and `τ(ℓ) ≤ τ(ζ)` for `ℓ | ζ`
  gives `Σ_{d ≤ ⌊u⌋₊}|r̃(ℓd,m)| ≤ τ(ℓ)^{-5}Ã(x)(log x)^{-3}`) gives the total
  `2·log x·Ã(x)(log x)^{-3}·Σ_{ℓ ≤ x} τ(ℓ)^{-3}` — and `Σ_{n≤x} τ(n)^{-3}` is `Θ(x)`
  (every term is `≥ 1/8`; Selberg–Delange gives `≈ c·x(log x)^{-7/8}`), i.e. a **power of `x`**.

So REM is *not* independent of MAIN's obstruction after all: both need the companion's §8.4 cure,
the substitution `z ↦ z/ℓ` inside the target's own `∫ dz/z`, which makes the `(1.7)`-arguments
`ℓ`-free.  These definitions remain the right bookkeeping for that route.
-/

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section


/-- **The inner `c`-sum vanishes when `ℓ · z > x`**: the filter `z < c ∧ c ≤ sz ∧ ℓ c ≤ x` is
empty, since `c > z` gives `ℓ c > ℓ z > x`. -/
lemma S3plusInnerC_eq_zero_of_mul_lt (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ)
    (h : (N : ℝ) < (ℓ : ℝ) * z) : S3plusInnerC a N ℓ z sz C = 0 := by
  rw [S3plusInnerC]
  refine Finset.sum_eq_zero (fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hz, -, hcl⟩ := hc
  exfalso
  have h1 : ((ℓ : ℕ) : ℝ) * ((c : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcl
  have hc1 : ((c : ℕ) : ℝ) > z := hz
  have hℓz : ((ℓ : ℕ) : ℝ) * z ≤ ((ℓ : ℕ) : ℝ) * ((c : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (le_of_lt hc1) (Nat.cast_nonneg ℓ)
  linarith

/-- The **remainder half** of the `λ⁺`-inner sum: the `r̃`-part of the `(1.7)`-split, summed over
the outer index `ℓ` with the companion's weights `Σ_{b | ℓ, sy < b} μ b` and `ρ(ℓ)`.  The
indicator `ℓ·z ≤ x` is inserted because the split form of `s3InnerInt` requires it. -/
def s3RemPlus (lam : ℕ → ℝ) (x : ℕ) (z sy sz : ℝ) (Cm : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 x,
    (if ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ) then
      (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ *
        ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
            (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
                  Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
                  ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u
     else 0)

/-- The **main half** of the same split. -/
def s3MainPlus (lam : ℕ → ℝ) (x : ℕ) (z sy sz : ℝ) (Cm : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 x,
    (if ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ) then
      (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ *
        ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
            Submission.ASP.FIgtil (ℓ * d)
              * (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
                - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u
     else 0)

/-! **The split of `S3plusC` into its `(1.7)`-halves** is `S3plusC = s3MainPlus + s3RemPlus`; the
proof needs the additivity of the interval integral for the two integrands
(`s3InnerInt_eq_split` supplies the pointwise identity, `intervalIntegral.integral_add` the
additivity), and for `ℓ · z > x` the inner sum vanishes
(`S3plusInnerC_eq_zero_of_mul_lt`).  It is *not* stated here to keep this module `sorry`-free; it is
a straightforward (if fiddly) technical step. -/

end

end Work.FIChain
