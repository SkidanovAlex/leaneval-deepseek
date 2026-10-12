import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.SymKzBogC_blocks
import Submission.Work.BoseBoxFock.SymLinOpTC_blocks
import Submission.Work.BoseBoxFock.SymQ2exC_blocks
import Submission.Work.BoseBoxFock.SymQ3TC_blocks
import Submission.Work.BoseBoxFock.SymSlots
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.symDiscrep` — the `r`-polynomial discrepancy identity

At a real condensate parameter `r ≥ 0` (so that `√(ρ_z ℓ³) = r` for `ρ_z = r²/ℓ³`) the
anti-Wick symbol `symR r = Σ_{i<25} r^{p_i+q_i} KvecF i` of the honest model differs from
FS's substituted operator `𝒦(r²/ℓ³)` (`KzOpC`) by an `r`-*polynomial* of degree ≤ 2:

    symR r − KzOpC (r²/ℓ³) = r² • D2F + r • D1F + D0F,

where the three `r`-independent operators `D0F`, `D1F`, `D2F` are the `KafzSym` ones.

**Proof strategy.**  Both sides are normalised into a ℂ-linear combination of a fixed
list of *word blocks* (`SymBlocks.lean`: single lattice sums with `k`-independent
weight), namely

* the scalars `1`, the number blocks `Bkin`, `BNW`, `BNω`, `nPlusChi` and the `k = 0`
  word `nmF f 0`;
* the pairing blocks `BPa`, `BPc`;
* the `χ̂`- and `χ̂²`-linear blocks `BχC`, `BχA`, `BchiSqC`, `BchiSqA`;

with the pairings and the cubic blocks cancelling identically and the `χ̂`-rows
combining into the coefficient `−2rℓ⁻³Ŵ₁(0)` (resp. `−2rℓ⁻³Ŵ₁ω(0)`).

The normalisation never *fuses* two lattice sums: instead every occurrence is *split*
into monomial blocks (`SymSum.sum_add_smul_split`), which keeps the rewriting local and
lets the final comparison be pure scalar arithmetic (`module`).  The `k ↔ −k`
reindexing of the `N_k + N_{−k}` and `A_k + C_k + A_{−k} + C_{−k}` terms uses exactly the
parity hypotheses `hτ`, `hχ`, `hW`; the `k = 0` term of the `𝒬₂^{ex}` row is the source
of the `nmF f 0` block, with `hωval` identifying `Ŵ₁ω(0)` (note `Ŵ₁ω` itself is never
used in the final coefficients, only `Ŵ₁ω(0) = ω(0)` and the evenness of `Ŵ₁ω` inside the
`KzOpC` rows).  The scalar bookkeeping (`ρ = r²ℓ⁻³ = r²·i3F E`, `√(ρℓ³) = r`, the
`c`-number row `ℓ³(…) = cHCF r⁴ − μĝ(0)r²`) is in `SymScalar.lean`.

The two halves are `lhs_canon` (the expansion of `symR`, the `k ↔ −k` reindexings and
the row normalisations) and `rhs_canon` (`D0F`/`D1F`/`D2F`), both with the common
right-hand side `SymCanon`; the target is their composite.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m : ℕ} [NeZero m]

/-- The corpus' `nOpC` is the same word as `nmF`. -/
theorem nOpC_eq_nmF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (k : Mode) : nOpC (f k) = nmF f k := rfl

/-- **The canonical block form** of both sides of the discrepancy identity: the
`c`-number part, the `k = 0` number word, the two number blocks with weights `Ŵ₁` and
`Ŵ₁ω`, the excited-number block and the four `χ̂`/`χ̂²`-linear blocks. -/
noncomputable def SymCanon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 r : ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((((2 * cHCF E gHat0 - 4 * cHCF E gHat0 * r ^ 2 + E.mu * gHat0 : ℝ)) : ℂ)) •
      (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
  + ((((2 * (r ^ 2 * i3F E) * E.W1omega0 : ℝ)) : ℂ)) • (nmF f 0)
  + ((((-(i3F E)) : ℝ) : ℂ)) • (BNW f E)
  + ((((-(i3F E)) : ℝ) : ℂ)) • (BNω f E)
  + ((((-(i3F E * (E.W1 0 + E.W1omega0)) : ℝ)) : ℂ)) • (nPlusChi f)
  + ((((-(2 * r * i3F E * E.W1 0) : ℝ)) : ℂ)) • (BχC f E)
  + ((((-(2 * r * i3F E * E.W1 0) : ℝ)) : ℂ)) • (BχA f E)
  + ((((-(2 * r * i3F E * E.W1omega0) : ℝ)) : ℂ)) • (BchiSqC g E)
  + ((((-(2 * r * i3F E * E.W1omega0) : ℝ)) : ℂ)) • (BchiSqA g E)

/-! ## The right-hand side `r²•D2F + r•D1F + D0F` in block form -/

theorem D0F_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    D0F f E gHat0 = (((2 * cHCF E gHat0 + E.mu * gHat0 : ℝ)) : ℂ) •
        (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
      + (((-(i3F E) : ℝ)) : ℂ) • (BNW f E + BNω f E)
      + (((-(i3F E * (E.W1 0 + E.W1omega0)) : ℝ)) : ℂ) • (nPlusChi f) := by
  rw [D0F, BW_split]

theorem D1F_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    D1F f g E = (((-(2 * i3F E * E.W1 0) : ℝ)) : ℂ) • (BχC f E + BχA f E)
      + (((-(2 * i3F E * E.W1omega0) : ℝ)) : ℂ) • (BchiSqC g E + BchiSqA g E) := by
  rw [D1F]
  simp only [BχC, BχA, BchiSqC, BchiSqA]

theorem D2F_blocks {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    D2F f E gHat0 = (((-(4 * cHCF E gHat0) : ℝ)) : ℂ) •
        (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
      + (((2 * i3F E * E.W1omega0 : ℝ)) : ℂ) • (nmF f 0) := by
  rw [D2F, nOpC_eq_nmF]

/-- The right-hand side is the canonical block combination. -/
theorem rhs_canon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 r : ℝ) :
    ((r ^ 2 : ℝ) : ℂ) • D2F f E gHat0 + ((r : ℝ) : ℂ) • D1F f g E + D0F f E gHat0
      = SymCanon f g E gHat0 r := by
  rw [D0F_blocks, D1F_blocks, D2F_blocks, SymCanon]
  push_cast
  module

/-! ## The left-hand side `symR r − KzOpC (r²/ℓ³)` in block form -/

/-- The left-hand side is the canonical block combination. -/
theorem lhs_canon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) (hℓ : 0 < E.ell)
    (hPH : PHs = F.PHset E)
    (hτ : ∀ k : Mode, E.tau (-k) = E.tau k)
    (hχ : ∀ k : Mode, E.hatChi (-k) = E.hatChi k)
    (hW : ∀ k : Mode, E.W1 (-k) = E.W1 k)
    (hωval : E.W1omega 0 = E.W1omega0)
    (r : ℝ) (hr : 0 ≤ r) :
    symR f g BNH PHs E gHat0 r - KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
      = SymCanon f g E gHat0 r := by
  -- the four `KzOpC` rows in block form
  have hKzBogC := SymKzBogC_blocks f E (r ^ 2 * i3F E) hτ hχ hW
  have hQ2 := SymQ2exC_blocks f (Work.BoseFixR.KzEnvAt E (r ^ 2 * i3F E))
  have hLin := SymLinOpTC_blocks g (Work.BoseFixR.KzEnvAt E (r ^ 2 * i3F E))
  have hQ3 := SymQ3TC_blocks f g F (Work.BoseFixR.KzEnvAt E (r ^ 2 * i3F E))
  have hρ : r ^ 2 / E.ell ^ 3 = r ^ 2 * i3F E := rho_eq_mul_i3 E hℓ r
  rw [hρ]
  -- expand `symR` into its 25 slots and `KzOpC` into its eight rows
  simp only [symR, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pvecF, qvecF,
    KvecF_0, KvecF_1, KvecF_2, KvecF_3, KvecF_4, KvecF_5, KvecF_6, KvecF_7, KvecF_8,
    KvecF_9, KvecF_10, KvecF_11, KvecF_12, KvecF_13, KvecF_14, KvecF_15, KvecF_16,
    KvecF_17, KvecF_18, KvecF_19, KvecF_20, KvecF_21, KvecF_22, KvecF_23, KvecF_24,
    KzOpC]
  -- the `symR` slots in block form
  rw [Bgap_eq_nPlusC]
  rw [BW_split]
  rw [Bbog1_eq_BPa, Bbog2_eq_BPc]
  rw [BW_one]
  rw [Bc8_blocks, Bc8'_blocks, Ba8_blocks, Ba8'_blocks]
  rw [Bc9_blocks, Bc9'_blocks, Ba9_blocks, Ba9'_blocks]
  rw [BQ3a_blocks, BQ3b_blocks]
  -- the `KzOpC` rows
  rw [hKzBogC, hQ2, hLin, hQ3]
  rw [← BχC, ← BχA]
  -- the scalar bookkeeping
  rw [sqrt_rho_ell3 E hℓ r hr]
  rw [← nPlusChi]
  rw [BNω_KzEnvAt, BchiSqC_KzEnvAt, BchiSqA_KzEnvAt, BQa_KzEnvAt, BQb_KzEnvAt]
  rw [PHset_KzEnvAt, ← hPH]
  rw [KzOpC_scalar_row E gHat0 r hℓ]
  rw [Work.BoseFixR.KzEnvAt, Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
  rw [sqrt_rho_ell3 E hℓ r hr, rho_eq_mul_i3 E hℓ r]
  rw [div_ell3_eq_mul_i3 E hℓ r]
  simp only [nOpC_eq_nmF]
  rw [hωval]
  rw [cMuF, SymCanon]
  push_cast
  module

/-! ## The discrepancy identity -/

theorem symDiscrep {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (PHs : Finset Mode) (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) (hℓ : 0 < E.ell)
    (hPH : PHs = F.PHset E)
    (hτ : ∀ k : Mode, E.tau (-k) = E.tau k)
    (hχ : ∀ k : Mode, E.hatChi (-k) = E.hatChi k)
    (hW : ∀ k : Mode, E.W1 (-k) = E.W1 k)
    (hWω : ∀ k : Mode, E.W1omega (-k) = E.W1omega k)
    (hωval : E.W1omega 0 = E.W1omega0)
    (r : ℝ) (hr : 0 ≤ r) :
    Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
        - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
      = ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2F f E gHat0
        + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
        + Work.BoseBoxFock.D0F f E gHat0 :=
  (lhs_canon f g BNH PHs F E gHat0 hℓ hPH hτ hχ hW hωval r hr).trans
    (rhs_canon f g E gHat0 r).symm

end Work.BoseBoxFock
