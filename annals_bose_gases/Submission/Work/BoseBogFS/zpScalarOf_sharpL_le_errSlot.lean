import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.Canonical
import Submission.Work.BoseBogFS.ChatChiFun
import Submission.Work.BoseBogFS.CloseFS
import Submission.Work.BoseBogFS.FsMatchEnvDefs
import Submission.Work.BoseBogFS.ViewRows
import Submission.Work.BoseBogFS.W1fun_mass_pos
import Submission.Work.BoseBogFS.bogOpBoundAtFSWith_of_honestRows
import Submission.Work.BoseBogFS.card_le_of_separated
import Submission.Work.BoseBogFS.chat_W1fun_pos_near_zero
import Submission.Work.BoseBogFS.chat_zero_eq_integral
import Submission.Work.BoseBogFS.continuous_chat
import Submission.Work.BoseBogFS.lhyEps_le_errSlot
import Submission.Work.BoseFixR.Rb5Lin.radial_fourier_sinc
import Submission.Work.BoseGateFS.TauRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.zpScalarOf_sharpL_le_errSlot` — the `hEzero` slot at the
`zpRiemErrSharpL` budget

The capstone `bogOpBoundAtFSWith_of_sharpMatchL` consumes (`SharpL.lean`) the slot

```
hEzeroL : zpErrorOf (ell v μ) (a v) R εT Kl s d μ ρ n
            (zpRiemErrSharpL n K η (lhyEps (a v) R εT Kl s d μ))  ≤  C₄ · errBracket v R μ,
```

and `zpErrorOf_eq_zpScalarOf` factors the physical prefactors `ℓ³ρ²a√(ρa³)` out of
`zpErrorOf`, reducing `hEzeroL` to a **scalar** inequality at the §11 bracket
(`zpErrorOf_le_scalar`, `SharpSlots.lean`).  This module supplies that scalar inequality:

```
zpScalarOf (a v) R εT Kl s d μ n (zpRiemErrSharpL n K η ε)  ≤  C · errSlot v R μ,
ε := lhyEps (a v) R εT Kl s d μ,
```

from the four honest rows

* `hEpsL : latticeMeshErr (8π) n ≤ 2·10¹¹·ε`   (the lattice-Riemann error of the mesh),
* `hlhy  : ε ≤ 10⁸·errSlot`                     (`Work.BoseBogFS.lhyEps_le_errSlot`),
* `hδl   : meshD n · log(1/meshD n) ≤ 10²⁰·errSlot`  (the sharp Riemann scale),
* `hprod : η·(1 + ε + fsI2 K) ≤ 10²⁰·errSlot`   (the mismatch weight `η` against the two
  terms the mismatch rescales, `FINDING_mismatch_weighting.md`),

and the constant row `10⁴⁵(1+K.B) ≤ C`.

## The arithmetic

Unfolding `zpScalarOf` and `zpRiemErrSharpL` the goal is

```
½(2π)⁻³·(L + 10¹⁴(1+B)·(δlog + η(1+ε+fsI2))) + ½·10¹⁰·ε  ≤  C·errSlot,
```

with `L = latticeMeshErr (8π) n`, `δlog = meshD n·log(1/meshD n)`, `B = K.B`.

* `L ≥ 0` (every summand of `latticeMeshErr` is nonnegative; the only non-obvious one is
  `log (gridD n) ≥ 0`, from `gridD n = (n+1)² ≥ 1`), hence `L ≤ 2·10¹¹ε` forces
  `ε ≥ 0` and then `hlhy` forces `errSlot ≥ 0` — the two sign facts the comparison
  `coef·errSlot ≤ C·errSlot` needs;
* `L ≤ 2·10¹¹ε ≤ 2·10¹⁹·errSlot ≤ 2·10¹⁹(1+B)·errSlot` (using `B ≥ 0`, so `1+B ≥ 1`);
* `δlog + η(1+ε+fsI2) ≤ 2·10²⁰·errSlot`, so
  `10¹⁴(1+B)(δlog + η(…)) ≤ 2·10³⁴(1+B)·errSlot` (using `1+B ≥ 0`);
* `½(2π)⁻³ ≤ ½` (from `2π ≥ 1`), so the first half is
  `≤ ½·(2·10¹⁹(1+B) + 2·10³⁴(1+B))·errSlot = (10¹⁹(1+B) + 10³⁴(1+B))·errSlot`, and the
  second half is `½·10¹⁰·ε ≤ 5·10¹⁷·errSlot ≤ 5·10¹⁷(1+B)·errSlot`;
* the coefficient `10¹⁹(1+B) + 10³⁴(1+B) + 5·10¹⁷(1+B) ≤ 2·10³⁴(1+B)` (pure numerals,
  times `1+B ≥ 0`) is below `10⁴⁵(1+B) ≤ C`.

The hypothesis `hC0 : 0 ≤ C` is not needed: the constant row `10⁴⁵(1+B) ≤ C` together with
`0 ≤ 1+B` already gives the comparison.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The arithmetic core of the `hEzero` slot at the `zpRiemErrSharpL` budget.**  See the
module header: everything is a comparison of the four budget rows against the §11 bracket. -/
private lemma zpScalar_arith {L dl ep I2 S B C η : ℝ}
    (hL0 : 0 ≤ L) (hB0 : 0 ≤ B)
    (hEpsL : L ≤ 2 * 10 ^ 11 * ep) (hlhy : ep ≤ 10 ^ 8 * S)
    (hdl : dl ≤ 10 ^ 20 * S) (hprod : η * (1 + ep + I2) ≤ 10 ^ 20 * S)
    (hC0 : 0 ≤ C) (hC : 10 ^ 45 * (1 + B) ≤ C) :
    (1 / 2) * ((2 * Real.pi) ^ 3)⁻¹ * (L + 10 ^ 14 * (1 + B) * (dl + η * (1 + ep + I2)))
      + (1 / 2) * 10 ^ 10 * ep ≤ C * S := by
  have hB1 : (0:ℝ) ≤ 1 + B := by linarith
  have hB1' : (1:ℝ) ≤ 1 + B := by linarith
  -- sign facts: `L ≥ 0` and `L ≤ 2·10¹¹ε` give `ε ≥ 0`, then `hlhy` gives `errSlot ≥ 0`
  have hep0 : 0 ≤ ep := by
    have h := hL0.trans hEpsL
    linarith
  have hS0 : 0 ≤ S := by
    have h := hep0.trans hlhy
    linarith
  -- the lattice-mesh row
  have hLb : L ≤ 2 * 10^19 * S := by
    calc L ≤ 2 * 10^11 * ep := hEpsL
      _ ≤ 2 * 10^11 * (10^8 * S) := mul_le_mul_of_nonneg_left hlhy (by norm_num)
      _ = 2 * 10^19 * S := by ring
  have hLb' : L ≤ (2 * 10^19 * (1 + B)) * S := by
    refine hLb.trans ?_
    have h2 : (2 * 10^19 : ℝ) ≤ 2 * 10^19 * (1 + B) := by
      calc (2 * 10^19 : ℝ) = 2 * 10^19 * 1 := by ring
        _ ≤ 2 * 10^19 * (1 + B) := mul_le_mul_of_nonneg_left hB1' (by norm_num)
    calc 2 * 10^19 * S = (2 * 10^19) * S := by ring
      _ ≤ (2 * 10^19 * (1 + B)) * S := mul_le_mul_of_nonneg_right h2 hS0
  -- the mesh/mismatch row through the budget
  have hEb : 10^14 * (1 + B) * (dl + η * (1 + ep + I2)) ≤ (2 * 10^34 * (1 + B)) * S := by
    have hsum : dl + η * (1 + ep + I2) ≤ 2 * 10^20 * S := by linarith
    calc 10^14 * (1+B) * (dl + η*(1+ep+I2))
        ≤ 10^14 * (1+B) * (2*10^20*S) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (2*10^34*(1+B))*S := by ring
  have hLE : L + 10^14*(1+B)*(dl + η*(1+ep+I2))
      ≤ (2*10^19*(1+B) + 2*10^34*(1+B)) * S := by
    calc L + 10^14*(1+B)*(dl + η*(1+ep+I2))
        ≤ (2*10^19*(1+B))*S + (2*10^34*(1+B))*S := add_le_add hLb' hEb
      _ = (2*10^19*(1+B) + 2*10^34*(1+B)) * S := by ring
  -- the scalar prefactor `½(2π)⁻³ ≤ ½`
  have hA0 : 0 ≤ (1/2) * ((2*Real.pi)^3)⁻¹ := by positivity
  have hApr : (1/2) * ((2*Real.pi)^3)⁻¹ ≤ 1/2 := by
    have h1 : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h2 : (1:ℝ) ≤ (2*Real.pi)^3 := one_le_pow₀ h1
    have h3 : ((2*Real.pi)^3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
    linarith
  have hK0 : 0 ≤ 2*10^19*(1+B) + 2*10^34*(1+B) := by positivity
  have hA1 : (1/2)*((2*Real.pi)^3)⁻¹ * (L + 10^14*(1+B)*(dl + η*(1+ep+I2)))
      ≤ ((1/2)*((2*Real.pi)^3)⁻¹) * ((2*10^19*(1+B) + 2*10^34*(1+B))*S) :=
    mul_le_mul_of_nonneg_left hLE hA0
  have hA2 : ((1/2)*((2*Real.pi)^3)⁻¹) * ((2*10^19*(1+B) + 2*10^34*(1+B))*S)
      ≤ (10^19*(1+B) + 10^34*(1+B))*S := by
    calc ((1/2)*((2*Real.pi)^3)⁻¹) * ((2*10^19*(1+B) + 2*10^34*(1+B))*S)
        = (((1/2)*((2*Real.pi)^3)⁻¹) * (2*10^19*(1+B) + 2*10^34*(1+B))) * S := by ring
      _ ≤ ((1/2) * (2*10^19*(1+B) + 2*10^34*(1+B))) * S :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hApr hK0) hS0
      _ = (10^19*(1+B) + 10^34*(1+B))*S := by ring
  -- the `lhyEps` row
  have he1 : (1/2)*10^10*ep ≤ 5*10^17*S := by
    calc (1/2)*10^10*ep ≤ (1/2)*10^10*(10^8*S) := mul_le_mul_of_nonneg_left hlhy (by norm_num)
      _ = 5*10^17*S := by ring
  have he2 : 5*10^17*S ≤ 5*10^17*(1+B)*S := by
    have h2 : (5*10^17:ℝ) ≤ 5*10^17*(1+B) := by
      calc (5*10^17:ℝ) = 5*10^17*1 := by ring
        _ ≤ 5*10^17*(1+B) := mul_le_mul_of_nonneg_left hB1' (by norm_num)
    calc 5*10^17*S = (5*10^17)*S := by ring
      _ ≤ (5*10^17*(1+B))*S := mul_le_mul_of_nonneg_right h2 hS0
  -- the total coefficient
  have hcoef : (10^19*(1+B) + 10^34*(1+B) + 5*10^17*(1+B)) ≤ 2*10^34*(1+B) := by
    have h1 : (10^19 + 10^34 + 5*10^17 : ℝ) ≤ 2*10^34 := by norm_num
    have h2 := mul_le_mul_of_nonneg_right h1 hB1
    calc 10^19*(1+B) + 10^34*(1+B) + 5*10^17*(1+B) = (10^19 + 10^34 + 5*10^17)*(1+B) := by
          ring
      _ ≤ (2*10^34)*(1+B) := h2
  have h2e34 : (2:ℝ)*10^34*(1+B) ≤ 10^45*(1+B) :=
    mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)*10^34 ≤ 10^45) hB1
  calc (1/2)*((2*Real.pi)^3)⁻¹ * (L + 10^14*(1+B)*(dl + η*(1+ep+I2))) + (1/2)*10^10*ep
      ≤ (10^19*(1+B) + 10^34*(1+B))*S + 5*10^17*(1+B)*S :=
        add_le_add (hA1.trans hA2) (he1.trans he2)
    _ = (10^19*(1+B) + 10^34*(1+B) + 5*10^17*(1+B))*S := by ring
    _ ≤ (2*10^34*(1+B))*S := mul_le_mul_of_nonneg_right hcoef hS0
    _ ≤ (10^45*(1+B))*S := mul_le_mul_of_nonneg_right h2e34 hS0
    _ ≤ C*S := mul_le_mul_of_nonneg_right hC hS0

/-- `latticeMeshErr (8π) n ≥ 0`: every summand is a nonnegative factor times a nonnegative
power of the mesh `meshD n ≥ 0`; the only summand that is not visibly so is
`128π√3(8π)²·meshD n·log (gridD n)`, and `gridD n = (n+1)² ≥ 1` gives `log ≥ 0`. -/
private lemma latticeMeshErr_nonneg (n : ℕ) : 0 ≤ Work.BoseB6.latticeMeshErr (8 * Real.pi) n := by
  rw [Work.BoseB6.latticeMeshErr]
  have hδ : 0 ≤ Work.BoseB6.meshD n := by rw [Work.BoseB6.meshD]; positivity
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hg : (1 : ℝ) ≤ (Work.BoseB6.gridD n : ℝ) := by
    rw [Work.BoseB6.gridD]; push_cast; nlinarith [hn]
  have hl : 0 ≤ Real.log (Work.BoseB6.gridD n) := Real.log_nonneg hg
  have h1 : 0 ≤ 512 * Real.pi * Real.sqrt 3 * (8 * Real.pi) * Work.BoseB6.meshD n ^ 3 :=
    mul_nonneg (by positivity) (pow_nonneg hδ 3)
  have h2 : 0 ≤ 520 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * Work.BoseB6.meshD n :=
    mul_nonneg (by positivity) hδ
  have h3 : 0 ≤ 128 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * Work.BoseB6.meshD n
      * Real.log (Work.BoseB6.gridD n) :=
    mul_nonneg (mul_nonneg (by positivity) hδ) hl
  have h4 : 0 ≤ 4 * (8 * Real.pi) ^ 3 / ((n : ℝ) + 1) := by positivity
  linarith [h1, h2, h3, h4]

theorem zpScalarOf_sharpL_le_errSlot (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (R μ : ℝ) (n : ℕ)
    (K : Work.BoseB6Est.FsKernel) {εT Kl s d η : ℝ} (C : ℝ)
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (hEpsL : Work.BoseB6.latticeMeshErr (8 * Real.pi) n
      ≤ 2 * 10 ^ 11 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R εT Kl s d μ)
    (hlhy : Work.BoseB6.lhyEps (_root_.BoseGases.a v) R εT Kl s d μ
      ≤ 10 ^ 8 * Work.BoseBogFS.errSlot v R μ)
    (hδl : Work.BoseB6.meshD n * Real.log (1 / Work.BoseB6.meshD n)
      ≤ 10 ^ 20 * Work.BoseBogFS.errSlot v R μ)
    (hprod : η * (1 + Work.BoseB6.lhyEps (_root_.BoseGases.a v) R εT Kl s d μ
        + Work.BoseB6Est.fsI2 K)
      ≤ 10 ^ 20 * Work.BoseBogFS.errSlot v R μ)
    (hC0 : 0 ≤ C) (hC : 10 ^ 45 * (1 + K.B) ≤ C) :
    Work.BoseBogFS.zpScalarOf (_root_.BoseGases.a v) R εT Kl s d μ n
        (Work.BoseBogFS.zpRiemErrSharpL n K η
          (Work.BoseB6.lhyEps (_root_.BoseGases.a v) R εT Kl s d μ))
      ≤ C * Work.BoseBogFS.errSlot v R μ :=
  zpScalar_arith (latticeMeshErr_nonneg n) K.Bnn hEpsL hlhy hδl hprod hC0 hC

end Work.BoseBogFS
