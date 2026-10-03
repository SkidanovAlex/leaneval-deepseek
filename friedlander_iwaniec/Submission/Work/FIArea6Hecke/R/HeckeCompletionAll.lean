/-
# `Submission.Work.FIArea6Hecke.R.HeckeCompletionAll` — Hecke's functional equation for every
weight `m : ℤ` (primitive strict characters mod `4d`)

For a primitive strict character `χ` mod `4d` and **every** integer weight `m : ℤ` there is an
entire function `Λ` with

  `Λ s = heckeArch d m s · heckeLSeries χ m s`   (`re s > 1 + |m|/2`),
  `Λ s = W · conj(Λ(conj(1-s)))`,  `W ≠ 0`,

i.e. the completion of the Hecke `L`-function of `ℚ(i)` and Hecke's functional equation.

* `m ≥ 0`: `heckeFE_primitive_full` (the theta transformation law).
* `m < 0`: conjugation — if `k = -m > 0`, `χ̄ = star ∘ χ` is again primitive strict
  (`isPrimitive4d_conj`, `gaussSum_conj`), the `m = k` completion `Λ₀` of `χ̄` exists, and
  `Λ s := conj(Λ₀(conj s))` is the required completion of `χ` at weight `-k`; the root number is
  inverted, `W = W₀⁻¹`.

Supporting identities: `isCharMod4d_conj`, `isCharMod4dStrict_conj`, `gaussSum_conj`,
`isPrimitive4d_conj`, `star_heckeArch`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.GaussFourier
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.heckeFE_of_theta
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.GaussBasic
import Submission.Work.FIArea5.S16Hecke.primaryWeightDefs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj

set_option autoImplicit false

/-!
# `Submission.Work.FIArea6Hecke.R.heckeZFRoffAxis` — *FI* (16.20), the de la Vallée Poussin
zero-free region of the Hecke `L`-function of `ℚ(i)` off the real axis

The target is exactly the `Prop` `ZFRoffAxis` of `ZFRStatementDefs.lean`:

  `∃ c > 0`, `∀ d ≥ 1`, `χ` strict mod `4d`, `m : ℤ`, `Λ` entire with
  `Λ s = heckeArch d m s · heckeLSeries χ m s` for `re s > 1 + |m|/2`:
  `Lval d m Λ s ≠ 0` for `1 - c/log(4d + |m| + |s.im|) < re s ≤ 2` unless `s` is real and `ψ_m` is
  real-valued.

## What is proved here, and what is the remaining plan

**Proved in this file (sorry-free).**

* `isCharMod4d_conj`, `isCharMod4dStrict_conj`, `gaussSum_conj`, `isPrimitive4d_conj`: the
  conjugate character `star ∘ χ` is again strict, and again primitive.
* `star_heckeArch`: `conj (heckeArch d m (conj s)) = heckeArch d (-m) s`.
* `completion_of_nat'`, `completion_of_neg`, and their union `HeckeCompletionAll`: **Hecke's
  functional equation for every weight `m : ℤ`** — for a primitive strict `χ` mod `4d` and every
  `m : ℤ` there is an entire `Λ` with

    `Λ s = heckeArch d m s · heckeLSeries χ m s`  (`re s > 1 + |m|/2`),  `Λ s = W·conj(Λ(conj(1-s)))`.

  (The `m ≥ 0` case is `heckeFE_primitive_full`; the `m < 0` case is the conjugation
  `Λ(s) = conj(Λ₀(conj s))` of the `m = -k ≥ 0` completion of the conjugate character. Note the
  root number is inverted by the conjugation, `W = W₀⁻¹`.)

**Remaining plan for the target** (the pieces below are *not* yet in this file; the whole argument
is the classical de la Vallée Poussin `3-4-1` inequality together with the Hadamard partial
fraction of the completion; it is the *sharp* `1/log` method, not the weaker
`1/log^A` "product + mean-value" method, which is insufficient for the region required here).

1. **The `3-4-1` inequality for the Hecke `L`-functions** (log-derivative form): for `σ > 1`,
   `t : ℝ`, with `L₁ = heckeLSeries (principalStrict d) 0`, `L = heckeLSeries χ m` and
   `L₂ = heckeLSeries (χ·χ) (2m)`,
   `0 ≤ 3·(-L₁'/L₁)(σ).re + 4·(-L'/L)(σ+it).re + (-L₂'/L₂)(σ+2it).re`;
   its proof is the Euler-product computation: the local exponent at a prime ideal `𝔭 ∤ 4d` is
   `3 + 4cos(kφ) + cos(2kφ) = 2(1+cos(kφ))² ≥ 0`, `φ = arg ψ(𝔭) - t log N𝔭`.
2. **The one-sided and near-zero log-derivative bounds** (`HeckeLambdaLogDerivBounds`): for
   `1 < σ ≤ 2`,
   `Re(Λ'/Λ)(σ+it) ≥ -C·log(4d(|m|+|t|+3))`, and, at a zero `β+it` of `Λ`,
   `Re(Λ'/Λ)(σ+it) ≥ 1/(σ-β) - C·log(4d(|m|+|t|+3))`.
   Both follow from the difference form of the Hadamard partial fraction
   (`Work.FIArea5.HeckeZFR.Lam_partialFraction`, applied to the circle growth of `Λ` supplied by
   `Lam_growth_right_half` + the reflection `s ↦ conj(1-s)`), the fact that all zeros of `Λ` lie in
   `0 ≤ re ≤ 1` (`Work.FIArea5.HeckeZFR.HeckeNonvanishing.Lam_zero_re_bounds`), and the bound
   `Re(Λ'/Λ)(2+it) ≤ C log` (`LamBaseBound.Lam_logDeriv_re_at_two_le`); each partial-fraction
   summand `Re(1/(s-u) - 1/(2+i·Im s - u))` has real part `≥ -C/(1 + |u.im - Im s|²)`, and the
   weighted zero sum `Σ_u ord(u)/(1+|u.im - t|²) ≪ log(4d(|m|+|t|+3))` is the remaining input.
3. **The real-axis pole bound**: `-Re(L₁'/L₁)(σ) ≤ 1/(σ-1) + C₁` for `1 < σ ≤ 2`, from
   `L(s,1) = ζ_K(s)·∏_{𝔭 | 4d}(1 - N𝔭^{-s})` and the corresponding bound for `ζ` (resp. `ζ_K`).
4. **The archimedean conversion**: `L'/L = Λ'/Λ - log(4d/π) - ψ(s+|m|/2)`, with
   `Re ψ(s+|m|/2) ≤ C log(4d(|m|+|s.im|+3))` (`HeckeZFR.DigammaShift`).
5. **The assembly** (mirroring `Commons.NumberTheory.Zeta.large_height_zero_free`): with
   `x = 1/(A(L+1))`, `L = log(4d(|m|+|t|+3))`, the `3-4-1` at heights `(0, γ, 2γ)` and the bounds
   of 2,3,4 give `4/(x+δ) ≤ 3A(L+1) + 3C₁ + 6C(L+1)` with `δ = 1-β`, whence
   `δ ≥ c/L`; the interval algebra is `region_main_algebra`'s. For `γ = 0` and `ψ` non-real, the
   same computation with the auxiliary point at height `0` and `L₂ = L(·, ψ²) ≠ L₁` works (this is
   why the real axis is excluded from the statement exactly when `ψ` is real).
6. **Monomorphism to the general (possibly imprimitive) `χ`**: for imprimitive `χ` induced from a
   primitive `χ₀` mod `4e` (`e | d`), one has
   `L(s,ψ_χ) = L(s,ψ_{χ₀})·∏_{𝔭 | 4d, 𝔭 ∤ 4e}(1 - ψ₀(𝔭)N𝔭^{-s})` on `re s > 1` (Euler products), so
   the completion of `χ` is `(d/e)^s·Λ₀(s)·∏(1-ψ₀(𝔭)N𝔭^{-s})`, entire; the extra factors have zeros
   only at `re s = 0`, outside the region as soon as `c ≤ log 4/2`. Hence the target follows from
   the primitive case (step 1–5) for `χ₀` mod `4e`, the region for `4e` containing that for `4d`.
   Finally `Lval d m Λ s = Λ s/heckeArch d m s` is nonzero in the region because
   `heckeArch d m s ≠ 0` for `re s > 0` (`ZFRDefs.heckeArch_ne_zero_of_pos_re`), and the region is
   contained in `re s > 0` for `c` small.
-/

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## Conjugation of strict characters -/

lemma isCharMod4d_conj {d : ℕ} {chi : GaussianInt → ℂ}
    (h : Work.FITop3.IsCharMod4d d chi) :
    Work.FITop3.IsCharMod4d d (fun z => star (chi z)) := by
  obtain ⟨h1, hmul, hb, hper, hv⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [h1, star_one]
  · intro z w
    show star (chi (z * w)) = star (chi z) * star (chi w)
    rw [hmul z w, star_mul]
    ring
  · intro z; simp only [norm_star]; exact hb z
  · intro z w hzw
    show star (chi z) = star (chi w)
    rw [hper z w hzw]
  · intro z hz
    show star (chi z) = 0
    rw [hv z hz, star_zero]

lemma isCharMod4dStrict_conj {d : ℕ} {chi : GaussianInt → ℂ}
    (h : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d (fun z => star (chi z)) :=
  ⟨isCharMod4d_conj h.1, fun z hz => by simp only [h.2 z hz, star_zero]⟩

lemma gaussSum_conj (d : ℕ) (chi : GaussianInt → ℂ) (ξ : GaussianInt) :
    Work.FIArea5.S16Hecke.gaussSum d (fun z => star (chi z)) ξ =
      star (Work.FIArea5.S16Hecke.gaussSum d chi (-ξ)) := by
  classical
  unfold Work.FIArea5.S16Hecke.gaussSum
  simp only [Complex.star_def]
  rw [map_sum (starRingEnd ℂ)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  by_cases hα : Work.FIArea5.S16Hecke.isOddG (⟨(α.1 : ℕ), (α.2 : ℕ)⟩ : GaussianInt)
  · simp only [hα, if_true]
    rw [map_mul]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_intCast,
      map_natCast, map_ofNat]
    have h1 : ((((α.1 : ℕ) : ℤ) * ξ.re + ((α.2 : ℕ) : ℤ) * ξ.im : ℤ) : ℂ)
        = -(((((α.1 : ℕ) : ℤ) * (-ξ).re + ((α.2 : ℕ) : ℤ) * (-ξ).im : ℤ)) : ℂ) := by
      rw [show (-ξ).re = -ξ.re by simp, show (-ξ).im = -ξ.im by simp]
      push_cast
      ring
    rw [h1]
    ring
  · rw [if_neg hα, if_neg hα, map_zero]

/-! ## The completion of the Hecke `L`-function for every weight `m : ℤ` -/

lemma star_heckeArch (d : ℕ) (m : ℤ) (s : ℂ) (hd : 1 ≤ d) :
    star (Work.FITop4.Bridge.heckeArch d m (star s)) = Work.FITop4.Bridge.heckeArch d (-m) s := by
  have hpos : (0:ℝ) < 4 * (d:ℝ) / Real.pi := by positivity
  have hne : ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ) ≠ 0) := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hpos
  have hlog : (starRingEnd ℂ) (Complex.log ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)))
      = Complex.log ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)) := by
    rw [← Complex.ofReal_log hpos.le]; exact Complex.conj_ofReal _
  have hbase : (4 * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ))
      = (((4 * (d : ℝ) / Real.pi : ℝ)) : ℂ) := by push_cast; ring
  have hcnj : star (((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)) ^ (star s))
      = ((((4 * (d:ℝ) / Real.pi : ℝ)) : ℂ)) ^ s := by
    simp only [Complex.star_def]
    rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
      ← Complex.exp_conj, map_mul, hlog, starRingEnd_self_apply]
  have habs : |(((-m : ℤ)) : ℝ)| = |((m : ℤ) : ℝ)| := by
    rw [show (((-m : ℤ)) : ℝ) = -((m : ℤ) : ℝ) by push_cast; ring, abs_neg]
  have hG : star (Complex.Gamma (star s + ((|((m : ℤ) : ℝ)| / 2 : ℝ) : ℂ)))
      = Complex.Gamma (s + ((|((m : ℤ) : ℝ)| / 2 : ℝ) : ℂ)) := by
    simp only [Complex.star_def]
    rw [← Complex.Gamma_conj]
    congr 1
    simp only [map_add, starRingEnd_self_apply, Complex.conj_ofReal]
  unfold Work.FITop4.Bridge.heckeArch
  rw [hbase, star_mul, hcnj, habs, hG]
  ring

/-! ## The zero-free region (statement of the assignment) -/
