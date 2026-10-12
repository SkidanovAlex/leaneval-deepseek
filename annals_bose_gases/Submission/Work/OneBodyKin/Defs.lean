import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.OneBodyKin.Defs` — the symbol of the projected moving-box family

This chapter attacks the residual `Work.BSKinetic.FamilyBoundCut C` — FS `lem:LocKinEn` for the
bratteli–Solovej/Fournais–Solovej *sliding box family* with the mean-free box projection, at the
cut-off `c ≥ C/ℓ` — by reducing it to a **pointwise inequality about the bump `χ` alone**.

## The reduction in one paragraph

Write `χ_u(x) = χ(x/ℓ − u)` for the big-box window family (an exact `L²`-partition,
`∫_u χ_u(x)² du = 1`), `Q_u = 1 − |Λ(u)|⁻¹∫_{Λ(u)}` for the mean-free projection and
`F = F(√−Δ)` for a radial symbol.  The one-body family form is

    `bsFamilyForm ℓ F ψ = ∫_u ⟨χ_u Q_u ψ, F(√−Δ) χ_u Q_u ψ⟩ du`,

a *translation-invariant* (hence convolution) quadratic form in `ψ`, so it is diagonal in
Fourier and equal to `(2π)⁻³ ∫_q famSym ℓ F q · ‖kinFT ψ q‖² dq` for an explicit radial symbol
`q ↦ famSym ℓ F q` (`bsFamilyForm_eq_symbolIntegral`, the **projected half of BS Lemma 3.3**).
Therefore `FamilyBound ℓ c` (i.e. `bsFamilyForm ℓ (fsKinCoeff c) ψ ≤ dSpace ψ`) follows from the
single **pointwise** inequality

    `∀ q, famSym ℓ (fsKinCoeff c) q ≤ ‖q‖²`.

That pointwise inequality is `SymBound ℓ c`; it only involves the bump's Fourier profile
`profHat`, the box Fourier profile `boxHat` and the symbol.  This file *defines* the symbol and
the residuals; `Reduce.lean` proves the conditional reductions, `Scaled.lean` shows that
`SymBound ℓ c` depends only on the product `c·ℓ`, and `Symbol/` attacks the pointwise inequality.

## The three terms of the symbol

Expanding `Q_uψ = ψ − m_u` (`m_u = bsMean ℓ u ψ`, a constant) and using self-adjointness,

    `⟨χ_uQ_uψ, Fχ_uQ_uψ⟩ = ⟨χ_uψ,Fχ_uψ⟩ − 2m_u⟨χ_u,Fχ_uψ⟩ + m_u²⟨χ_u,Fχ_u⟩`,

and each of the three `u`-integrals is translation invariant, with symbols

* `symA ℓ F q  = (2π)⁻³ ∫_p F(‖q + p/ℓ‖)·profHat(p)² dp`  (the unprojected family form);
* `symD ℓ F q  = ∫_p F(‖p‖)·profHat(ℓp)·profHat(ℓ(q−p)) dp`;
* `symC ℓ F q  = symA ℓ F 0 · ℓ⁻⁶ · boxHat(ℓq)²`

so that `famSym ℓ F q = symA ℓ F q − 2(2π)⁻³·boxHat(ℓq)·symD ℓ F q + symC ℓ F q`.
Here `profHat p = ∫_z χ z · cos⟪p,z⟫ dz` and `boxHat ℓ q = ∫_{acube ℓ} cos⟪q,z⟫ dz`.

## Consistency checks (both are theorems of this chapter)

* `famSym ℓ F 0 = 0` for **every** symbol `F` — the form annihilates constants, since `Q_u 1 = 0`;
* at `F = 1` the symbol is manifestly nonnegative (the form is `∫_u ‖χ_uQ_uψ‖² ≥ 0`).

Both are proved directly from the definitions (`SymZero.lean`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The two Fourier profiles -/

/-- **The Fourier profile of the bump** `χ`: `profHat p = ∫_z χ z · cos⟪p,z⟫ dz`.
This is the real Fourier transform of `χ` (`χ` is even, so the sine part vanishes;
`kinFT_profHat` identifies it with `kinFT (χ : ℝ³ → ℂ)`). -/
noncomputable def profHat (p : ℝ³) : ℝ := ∫ z : ℝ³, chi z * Real.cos (inner ℝ p z)

/-- **The Fourier profile of the box indicator** `1_{acube ℓ}`:
`boxHat ℓ q = ∫_{acube ℓ} cos⟪q,z⟫ dz`.  It is the real Fourier transform of the box indicator
(the sine part vanishes by symmetry of the cube). -/
noncomputable def boxHat (ℓ : ℝ) (q : ℝ³) : ℝ := ∫ z in acube ℓ, Real.cos (inner ℝ q z)

/-! ## 2. The three terms of the symbol -/

/-- **The symbol of the unprojected family form** `∫_u⟨χ_uψ,F(√−Δ)χ_uψ⟩ du`:
`symA ℓ F q = (2π)⁻³ ∫_p F(‖q + p/ℓ‖)·profHat(p)² dp`. -/
noncomputable def symA (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖q + ℓ⁻¹ • p‖ * (profHat p) ^ 2

/-- The second symbol term: `symD ℓ F q = ∫_p F(‖p‖)·profHat(ℓp)·profHat(ℓ(q−p)) dp`. -/
noncomputable def symD (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) : ℝ :=
  ∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * profHat (ℓ • (q - p))

/-- The third symbol term: `symC ℓ F q = symA ℓ F 0 · ℓ⁻⁶ · boxHat(ℓq)²`. -/
noncomputable def symC (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) : ℝ :=
  symA ℓ F 0 * (ℓ ^ 6)⁻¹ * (boxHat ℓ q) ^ 2

/-- **The symbol of the projected moving-box family form** `∫_u⟨χ_uQ_uψ,F(√−Δ)χ_uQ_uψ⟩ du`:
`famSym ℓ F q = symA ℓ F q − 2(2π)⁻³·boxHat(ℓq)·symD ℓ F q + symC ℓ F q`. -/
noncomputable def famSym (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) : ℝ :=
  symA ℓ F q - 2 * ((2 * Real.pi) ^ 3)⁻¹ * boxHat ℓ (q) * symD ℓ F q + symC ℓ F q

/-- **The `χ_u`-weighted cross form** `⟨χ_u, F(√−Δ)(χ_uψ)⟩` appearing in the mean-correction
term of the expansion of `bsFamilyForm`.  It is the *off-diagonal* companion of
`Work.BSKinetic.bsOneBodyUnproj` (which is the diagonal form `⟨χ_uψ,F(√−Δ)(χ_uψ)⟩`); in `p`-space
it is `(2π)⁻³∫_p F(‖p‖)·Re[kinFT χ_u (p)·conj(kinFT (χ_uψ) (p))] dp`. -/
noncomputable def bsPair (ℓ : ℝ) (F : ℝ → ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ p : ℝ³, F ‖p‖ *
      (kinFT (fun z : ℝ³ => ((Work.BSKinetic.bsWin ℓ u z : ℝ) : ℂ)) p *
        star (kinFT (fun z : ℝ³ =>
          (((Work.BSKinetic.bsWin ℓ u z : ℝ) : ℂ) * (ψ z : ℂ))) p)).re

/-! ## 3. The residuals -/

/-- **The pointwise symbol bound at the cut-off `c`.** For every momentum `q`, the symbol of the
projected family form with the FS cut-off `fsKinCoeff c = [·−c]₊²` is dominated by `‖q‖²`.

This is *the* analytic content of FS `lem:LocKinEn` (Bratteli–Solovej Lemma 3.3 + FS's symbol
bound `H(p) ≤ C b min{‖p‖²,d⁻²}`), stripped of all operator theory: it is a pointwise inequality
about the bump `χ`.  By `bsFamilyForm_eq_symbolIntegral` and `Reduce.FamilyBound_of_SymBound` it
implies `Work.BSKinetic.FamilyBound ℓ c`. -/
def SymBound (ℓ c : ℝ) : Prop := ∀ q : ℝ³, famSym ℓ (fsKinCoeff c) q ≤ ‖q‖ ^ 2

/-- **The pointwise symbol bound in FS's parameter regime**: the cut-off `c` is at least `C/ℓ`
with a universal `C` (depending only on the bump `χ`). -/
def SymBoundCut (C : ℝ) : Prop :=
  0 < C ∧ ∀ (ℓ c : ℝ), 0 < ℓ → C / ℓ ≤ c → SymBound ℓ c

/-- **The symbol-integral identity** (the *projected half of BS Lemma 3.3*, in the corpus's
`p`-convention): the projected moving-box family form is the Fourier integral of its symbol,

    `bsFamilyForm ℓ F ψ = (2π)⁻³ ∫_q famSym ℓ F q · ‖kinFT ψ q‖² dq`.

This is a *computation*, not an inequality: every term is an explicit integral and the `u`-integral
makes the form translation invariant, hence diagonal in Fourier.  It is proved for
compactly supported (hence `L¹`) symbols `F` in
`OneBodyKin/bsFamilyForm_eq_symbolIntegral`; the extension to the FS cut-off
`F = fsKinCoeff c = [·−c]₊²` (which is *not* in `L¹`) goes by monotone convergence
(`IdentCut.lean`). -/
def SymbolIntegral (ℓ : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ³ → ℝ, ContDiff ℝ (⊤ : ENat) ψ → HasCompactSupport ψ →
    Work.BSKinetic.bsFamilyForm ℓ F ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, famSym ℓ F q *
          ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2

/-- The symbol bound at scale `1` — the *scale-free* form of `SymBound ℓ c`: by the change of
variables `p ↦ ℓp` in `symA` and `symD` and `q ↦ ℓ⁻¹q`, only the product `c·ℓ` matters
(`Scaled.symBound_iff_one`). -/
def SymBoundOne (C : ℝ) : Prop := ∀ ρ : ℝ³, famSym 1 (fsKinCoeff C) ρ ≤ ‖ρ‖ ^ 2

/-! ## 4. Elementary API of the profiles

The full API (continuity, bounds, the identification with `kinFT`, the decay estimates, the value
at the origin) is in `Submission/Work/OneBodyKin/Profiles.lean`.  Here we record only the
parity of the two profiles, which is what makes the symbol even. -/

lemma profHat_even (p : ℝ³) : profHat (-p) = profHat p := by
  unfold profHat
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [inner_neg_left, Real.cos_neg]

lemma boxHat_even (ℓ : ℝ) (q : ℝ³) : boxHat ℓ (-q) = boxHat ℓ q := by
  unfold boxHat
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [inner_neg_left, Real.cos_neg]

/-- The symbol is even in the momentum: it is the Fourier transform of the (symmetric) kernel of
the projected family form. -/
lemma symA_even (ℓ : ℝ) (F : ℝ → ℝ) (q : ℝ³) : symA ℓ F (-q) = symA ℓ F q := by
  unfold symA
  congr 1
  rw [← integral_comp_neg
    (fun p : ℝ³ => F ‖(-q : ℝ³) + ℓ⁻¹ • p‖ * (profHat p) ^ 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only
  rw [show (-q : ℝ³) + ℓ⁻¹ • (-p) = -(q + ℓ⁻¹ • p) from by module, norm_neg]
  rw [profHat_even]

end Work.OneBodyKin
