import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.K2ndDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Q3Defs` — FS `eq:3Qtilde` (`Q̃₃`) on the mode lattice

FS's `Q̃₃` (the last row of `lem:2ndQuand`, and the `Q̃₃` of `eq:3Qtilde`) is the
second-quantised operator

    `Q̃₃ = ℓ³ (2π)⁻⁶ ∬_{k ∈ P_H} f_L(s) Ŵ₁(k) (a₀† ã_s† a_{s−k} a_k + a_k† a_{s−k}† ã_s a₀)`,

with `ã_s` the **localized** (smeared) modes, i.e. those *orthogonal to the
condensate* (`Q_j` in `Σ_{i≠j}(P_iQ_{L,j}w₁Q_jQ_i + h.c.)` is a projector off `θ`),
and `s`, `k` on the momentum lattice.  `Work.BoseB4.H2nd` deliberately omits this
row (it is what `lem:Q3-splitting2` compares with); this module supplies its
mode-lattice and complex-spectator versions.

## The model

* the smeared mode `ã_s` is a superposition of **excited** modes only:
  `ã_s = Σ_{j : Excited m} (phi s j) a_j` (`annOfExc`), so it carries no
  condensate component — the faithful counterpart of `Q_jθ = 0`;
* `a_{s−k}`, `a_k` are lattice modes (`k ∈ P_H ∩ (modes ≠ 0)`);
* the momentum measure `(2π)⁻⁶∫dk ds` is folded into the weights `fL`, `W1` (the
  header of `Work.BoseB4.H2nd` records this convention), while the explicit `ℓ³`
  prefactor is kept;
* `PHexc E` is the index set `(exc m).filter (· ∈ E.PHset)`.

## Contents

* `specA`, `specC` — the spectator annihilation/creation of the smeared mode;
* `AnnT`, `CreT` — the transported lattice mode operators (`a0`/`a0d` at the
  condensate, `lift (annX ·)`/`lift (creX ·)` elsewhere);
* `Q3Data` — the data of the row (`ell`, `W1`, `fL`, `phi`, `PHset`);
* `Q3sq` — the row on the mode lattice `RealFock m`;
* `Q3C` — its image under `Work.BoseB4.split`, as an explicit ℂ-linear word
  (`Q3Fwd` is the `a₀†ã_s†a_{s−k}a_k` half, `Q3Adj` the `h.c.` half);
* `Q3p`, `Q3q`, `Q3B01`, `Q3B11`, `Q3B00`, `Q3B10`, `Q3B`, `Q3nf` — the
  anti-normal normal form of `Q3C` (`Q3nf = Σ_{i : Fin 4} monoOp (Q3p i) (Q3q i)
  (Q3B E i)`), i.e. the family that `Work.BoseB4.Kafz_sum` consumes.

The two theorems connecting them,

* `Work.BoseB4.split_Q3sq` (the transport `split ∘ Q3sq = Q3C ∘ split`) and
* `Work.BoseB4.Q3C_eq_family` (`Q3C = Q3nf`, the anti-normal reordering),

and the resulting `c`-number substitution `Work.BoseB4.Kafz_Q3sq`, live in their
own files.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## The smeared (localized) modes -/

/-- The spectator **annihilation of the localized mode with coordinates `f`**:
`Σ_{j : Excited m} f_j a_j`, a combination of excited modes only (localized modes
are orthogonal to the condensate). -/
noncomputable def specA (f : Excited m → ℝ) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ j : Excited m, ((f j : ℝ) : ℂ) • annC (Excited m) j

/-- The spectator **creation of the localized mode with coordinates `f`**
(`specC = specA†`, in the same mode ordering). -/
noncomputable def specC (f : Excited m → ℝ) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ j : Excited m, ((f j : ℝ) : ℂ) • creC (Excited m) j

/-- The lattice annihilation of the localized mode `ã_s` with coordinates `phi s`
(`annOfExc`): `Σ_{j : Excited m} (phi s j) a_j`. -/
noncomputable def annOfExc (f : Excited m → ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ j : Excited m, (f j) • ann m j.1

/-- The lattice creation of the localized mode with coordinates `f`. -/
noncomputable def creOfExc (f : Excited m → ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ j : Excited m, (f j) • cre m j.1

/-! ## The transported lattice mode operators -/

/-- The image of the lattice mode annihilation `ann m j` under `split`:
`a0` at the condensate, `lift (annX m j)` on the excited modes. -/
noncomputable def AnnT (j : Fin m) : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  if j = 0 then a0 else lift (annX m j)

/-- The image of the lattice mode creation `cre m j` under `split`. -/
noncomputable def CreT (j : Fin m) : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  if j = 0 then a0d else lift (creX m j)

/-! ## The data of the row -/

/-- The scalar and kernel data of FS `eq:3Qtilde`: the box side `ℓ`, the momentum
weight `Ŵ₁` (with the normalised measure `(2π)⁻⁶` folded in), the localization
weights `f_L(s)`, the coordinates `phi s` of the smeared modes `ã_s` on the
excited modes, and the high-momentum set `P_H`. -/
structure Q3Data (m : ℕ) [NeZero m] where
  /-- FS's box side `ℓ` (the explicit `ℓ³` prefactor of `eq:3Qtilde`). -/
  ell : ℝ
  /-- FS's `Ŵ₁(k)`, with the normalised momentum weight included. -/
  W1 : Fin m → ℝ
  /-- FS's `f_L(s)`, with the normalised `s`-weight included. -/
  fL : Fin m → ℝ
  /-- The coordinates of the localized mode `ã_s` in the excited-mode basis. -/
  phi : Fin m → Excited m → ℝ
  /-- FS's high-momentum region `P_H`. -/
  PHset : Finset (Fin m)

/-- The mode index set of the row: excited modes that also lie in `P_H`. -/
noncomputable def PHexc (E : Q3Data m) : Finset (Fin m) :=
  (exc m).filter (fun k => k ∈ E.PHset)

/-- The weight `ℓ³ f_L(s) Ŵ₁(k)` of the `(k,s)` summand, as a complex scalar. -/
noncomputable def Q3w (E : Q3Data m) (k s : Fin m) : ℂ :=
  ((E.ell ^ 3 * E.fL s * E.W1 k : ℝ) : ℂ)

/-! ## The row and its image under `split` -/

/-- The `a₀† ã_s† a_{s−k} a_k` half of FS `eq:3Qtilde` on the **mode lattice**. -/
noncomputable def Q3sqFwd (E : Q3Data m) (k s : Fin m) : RealFock m →ₗ[ℝ] RealFock m :=
  (cre m 0).comp ((creOfExc (E.phi s)).comp ((ann m (s - k)).comp (ann m k)))

/-- The `a_k† a_{s−k}† ã_s a₀` (`h.c.`) half of FS `eq:3Qtilde` on the mode lattice. -/
noncomputable def Q3sqAdj (E : Q3Data m) (k s : Fin m) : RealFock m →ₗ[ℝ] RealFock m :=
  (cre m k).comp ((cre m (s - k)).comp ((annOfExc (E.phi s)).comp (ann m 0)))

/-- **FS `eq:3Qtilde` on the mode lattice.** -/
noncomputable def Q3sq (E : Q3Data m) : RealFock m →ₗ[ℝ] RealFock m :=
  (∑ k ∈ PHexc E, ∑ s : Fin m, (E.ell ^ 3 * E.fL s * E.W1 k) • Q3sqFwd E k s)
    + (∑ k ∈ PHexc E, ∑ s : Fin m, (E.ell ^ 3 * E.fL s * E.W1 k) • Q3sqAdj E k s)

/-- The `a₀† ã_s† a_{s−k} a_k` half of `Q̃₃` on the **complex Fock core** (the image
of `Q3sqFwd` under `split`). -/
noncomputable def Q3Fwd (E : Q3Data m) (k s : Fin m) :
    FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  a0d.comp ((lift (specC (E.phi s))).comp ((AnnT (s - k)).comp (AnnT k)))

/-- The `h.c.` half of `Q̃₃` on the complex Fock core. -/
noncomputable def Q3Adj (E : Q3Data m) (k s : Fin m) :
    FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  (CreT k).comp ((CreT (s - k)).comp ((lift (specA (E.phi s))).comp a0))

/-- **The image of `Q3sq` under `Work.BoseB4.split`**, as an explicit ℂ-linear word. -/
noncomputable def Q3C (E : Q3Data m) :
    FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  (∑ k ∈ PHexc E, ∑ s : Fin m, Q3w E k s • Q3Fwd E k s)
    + (∑ k ∈ PHexc E, ∑ s : Fin m, Q3w E k s • Q3Adj E k s)

/-! ## The anti-normal normal form of `Q3C`

Each `(k,s)` summand is a word in `a0`, `a0d` and levelwise lifts.  For `s ≠ k` the
two middle factors `AnnT (s−k)` and `AnnT k` are lifts (both indices are excited)
and the whole word is a single anti-normal monomial; for `s = k` the factor
`AnnT 0 = a0` appears and the word needs the Wick identity
`a0d ∘ a0 = monoOp 1 1 1 − monoOp 0 0 1`, i.e. two anti-normal monomials.  The four
families below collect the contributions with exponent pairs
`(0,1)`, `(1,1)`, `(0,0)` and `(1,0)` respectively. -/

/-- The `(0,1)` spectator family (`a₀† ã_s† a_{s−k} a_k` with `s ≠ k`). -/
noncomputable def Q3B01 (E : Q3Data m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ PHexc E, ∑ s : Fin m, Q3w E k s •
    (if s = k then 0
      else (specC (E.phi s)).comp ((annX m (s - k)).comp (annX m k)))

/-- The `(1,1)` spectator family (`a₀†a₀ × spectator`, from the `s = k` terms of both
halves). -/
noncomputable def Q3B11 (E : Q3Data m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (∑ k ∈ PHexc E, ∑ s : Fin m, Q3w E k s •
      (if s = k then (specC (E.phi s)).comp (annX m k) else 0))
    + (∑ k ∈ PHexc E, ∑ s : Fin m, Q3w E k s •
      (if s = k then (creX m k).comp (specA (E.phi s)) else 0))

/-- The `(0,0)` spectator family (the `−1` of `a0d ∘ a0 = monoOp 1 1 1 − monoOp 0 0 1`,
from the `s = k` terms of both halves). -/
noncomputable def Q3B00 (E : Q3Data m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (∑ k ∈ PHexc E, ∑ s : Fin m, (-(Q3w E k s)) •
      (if s = k then (specC (E.phi s)).comp (annX m k) else 0))
    + (∑ k ∈ PHexc E, ∑ s : Fin m, (-(Q3w E k s)) •
      (if s = k then (creX m k).comp (specA (E.phi s)) else 0))

/-- The `(1,0)` spectator family (`a_k† a_{s−k}† ã_s a₀` with `s ≠ k`). -/
noncomputable def Q3B10 (E : Q3Data m) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ PHexc E, ∑ s : Fin m, Q3w E k s •
    (if s = k then 0
      else (creX m k).comp ((creX m (s - k)).comp (specA (E.phi s))))

/-- The exponent pairs of the four spectator families, in the order
`(0,1), (1,1), (0,0), (1,0)`. -/
def Q3p : Fin 4 → ℕ := ![0, 1, 0, 1]

/-- The creation exponents, see `Q3p`. -/
def Q3q : Fin 4 → ℕ := ![1, 1, 0, 0]

/-- The four spectator families, in the order of `Q3p`/`Q3q`. -/
noncomputable def Q3B (E : Q3Data m) : Fin 4 → cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ![Q3B01 E, Q3B11 E, Q3B00 E, Q3B10 E]

/-- **The anti-normal normal form of `Q3C`**: four anti-normal families. -/
noncomputable def Q3nf (E : Q3Data m) :
    FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) :=
  ∑ i : Fin 4, monoOp (Q3p i) (Q3q i) (Q3B E i)

end Work.BoseB4
