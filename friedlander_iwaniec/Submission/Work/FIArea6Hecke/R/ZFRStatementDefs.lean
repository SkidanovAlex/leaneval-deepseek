/-
# `Submission.Work.FIArea6Hecke.R.ZFRStatementDefs` — the two classical inputs of the zero-free
region, as `Prop`s shared between the target file `R/heckeStripZFR` and the lemmas delegated for it.

The target `Work.FIArea6Hecke.R.heckeStripZFR` (the non-vanishing half of *FI* (16.20)+(16.24)) is

  `Lval d m Lam s ≠ 0`  for  `1 - c/(d^ε·log(|m|+|s.im|+3)) ≤ s.re ≤ 2`,

where `Lval d m Lam = Lam s / heckeArch d m s` and `Lam` is an entire completion of
`Λ(s,ψ) = (4d/π)^s Γ(s+|m|/2)L(s,ψ)`, `ψ(z) = χ(z)(z/|z|)^m`.

Following *FI* §16 (p. 1006–1009), this is the combination of exactly two classical statements.

* **`ZFRoffAxis`** — (16.20): the de la Vallée Poussin `3-4-1` zero-free region
  `σ > 1 - c/log(4d + |m| + |t|)`, *apart from a possible exceptional simple real zero in the case
  that `ψ` is real*.  Its proof uses Hecke's functional equation (available:
  `FIArea5/S16Hecke/heckeFE_of_theta`, `heckeFE_primitive_full`), the convexity bounds
  (16.18)/(16.19) (Phragmén–Lindelöf), the Hadamard/partial-fraction machinery
  (`FIArea5/HeckeZFR/*`) and the `3+4cos θ+cos 2θ ≥ 0` positivity of the Euler products of
  `ζ_K, L(·,ψ), L(·,ψ²)`.  The exceptional set is exactly `s.im = 0 ∧ PsiReal χ m`.

* **`ZFRrealAxis`** — Lemma 16.1: Siegel's uniform bound for the real zero, in the `ε`-form
  `σ > 1 - c(ε)d^{-ε}`, giving the target's depth `d^{-ε}` on the real axis for real `ψ`
  (Goldfeld's argument applied to `ζ_K(s)L(s,ψ₁)L(s,ψ₂)L(s,ψ₁ψ₂) ≥ 0`, for which the coefficient
  non-negativity is already formalised in `FIArea5/S16Hecke/hecke_prod_coeff_nonneg`).

The two regions combine into the target because `d^{-ε}·log(...) ≫ d^{-ε}` and
`1/log(4d+|m|+|t|) ≫ d^{-ε}/log(|m|+|t|+3)` uniformly in `d ≥ 1` (see
`region_le_offAxis` in `R/heckeStripZFR`).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- **`ψ` is real-valued**: `ψ_m(z) = χ(z)(z/|z|)^m ∈ ℝ` for every Gaussian integer `z`. -/
def PsiReal (chi : GaussianInt → ℂ) (m : ℤ) : Prop :=
  ∀ z : GaussianInt, star (Work.FIArea5.S16Hecke.psi chi m z) = Work.FIArea5.S16Hecke.psi chi m z

/-- **`ψ` is real on the primary elements** — the correct notion of "`ψ` real" of *FI* (16.20) and
Lemma 16.1: `ψ` is a character on *odd ideals* (16.16), given in terms of primary generators
`ψ(𝔞) = ψ(z)`, so the Hecke eigenvalue `λ(n) = Σ_{z primary, |z|²=n} ψ(z)` (*and hence the whole
`L`-function*) depends only on the values of `ψ` on the primary elements.

This is *strictly weaker* than `PsiReal χ m` (real-valuedness on all of `ℤ[i]`): the primary
elements generate only a tiny subgroup of `(ℤ[i]/4dℤ[i])^*`, so there are strict `χ` real on the
primary units which are not real-valued (`exists_realCharacter_agreeing_on_primary`,
`heckeLSeries_eq_of_primary_agree` in this directory).  Since the `L`-functions agree, the
exceptional-zero phenomenon is exactly the case `PsiRealPrimary`, and using the narrower `PsiReal`
in the exceptional set of (16.20) would claim the *Siegel-zero-free* region on the real axis
(the `d^{-ε}`-depth being strictly smaller than the depth-free `1/log`-region for large `d`). -/
def PsiRealPrimary (chi : GaussianInt → ℂ) (m : ℤ) : Prop :=
  ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
    star (Work.FIArea5.S16Hecke.psi chi m z) = Work.FIArea5.S16Hecke.psi chi m z

lemma psiReal_implies_psiRealPrimary {chi : GaussianInt → ℂ} {m : ℤ} (h : PsiReal chi m) :
    PsiRealPrimary chi m := fun z _ => h z

lemma psiRealPrimary_zero_iff {chi : GaussianInt → ℂ} :
    PsiRealPrimary chi 0 ↔ ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      star (chi z) = chi z := by
  unfold PsiRealPrimary Work.FIArea5.S16Hecke.psi
  constructor
  · intro h z hz
    have := h z hz
    simpa using this
  · intro h z hz
    simpa using h z hz

/-- `PsiReal` for `m = 0` is just: `χ` is real-valued. -/
lemma psiReal_zero_iff {chi : GaussianInt → ℂ} :
    PsiReal chi 0 ↔ ∀ z : GaussianInt, star (chi z) = chi z := by
  unfold PsiReal Work.FIArea5.S16Hecke.psi
  constructor
  · intro h z
    have := h z
    simpa using this
  · intro h z
    simpa using h z

/-- **The de la Vallée Poussin zero-free region off the real axis (*FI* (16.20))**, i.e. (16.20)
together with the observation that the only exceptional zeros of a Hecke `L`-function are *real*
zeros of an `L`-function with *real* `ψ`: there is `c > 0` such that for every strict character
`χ` mod `4d`, every `m : ℤ`, every entire completion `Lam`, and every `s` with
`re s > 1 - c/log(4d + |m| + |s.im|)` and `re s ≤ 2`, the value `Lval d m Lam s` is nonzero —
*unless* `s` is real *and* `ψ` is real-valued. -/
def ZFRoffAxis : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      ∀ s : ℂ,
        1 - c / Real.log (4 * (d : ℝ) + |(m : ℝ)| + |s.im|) < s.re → s.re ≤ 2 →
          ¬ (s.im = 0 ∧ PsiRealPrimary chi m) → Lval d m Lam s ≠ 0

/-- **Lemma 16.1 (Landau–Siegel) on the real axis, in the `ε`-form (16.21)**: for every
`0 < ε ≤ 1/4` there is `c > 0` such that for every strict character `χ` mod `4d`, every `m : ℤ`,
every real-valued `ψ_m` and every entire completion `Lam`, the value `Lval d m Lam s` is nonzero at
every *real* `s` with `1 - c·d^{-ε} < re s ≤ 2`.

The paper states the excluded set as the segment `s > 1 - c(ε)d^{-ε}` in the real character case;
the statement here is the same region intersected with the strip `re s ≤ 2` of the target, with
`ψ` real formulated as `PsiReal χ m`. -/
def ZFRrealAxis (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      PsiReal chi m →
      ∀ s : ℂ, s.im = 0 →
        1 - c / (d : ℝ) ^ ε < s.re → s.re ≤ 2 → Lval d m Lam s ≠ 0

/-- **Lemma 16.1 (Landau–Siegel) on the real axis, with the hypothesis `PsiRealPrimary`.**

The paper's hypothesis is "`ψ` real" in the sense of the *odd-ideal* character (16.16), i.e.
`PsiRealPrimary`; this version (equivalent to `ZFRrealAxis` by `heckeZFRrealAxisP_of_psiReal`,
which replaces `ψ` by the real-valued character `chiReal χ` agreeing with it on the primary
elements) is the one whose hypothesis matches the exceptional set of `ZFRoffAxis`, so that the
two halves cover the target region exhaustively. -/
def ZFRrealAxisP (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      PsiRealPrimary chi m →
      ∀ s : ℂ, s.im = 0 →
        1 - c / (d : ℝ) ^ ε < s.re → s.re ≤ 2 → Lval d m Lam s ≠ 0

end

end Work.FIArea6Hecke.R
