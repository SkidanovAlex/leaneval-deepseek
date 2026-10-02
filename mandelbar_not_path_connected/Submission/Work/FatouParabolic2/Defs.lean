/-
Copyright: subproject `Submission/Work/FatouParabolic2/` of `mandelbar_not_path_connected`.

# Fatou's theorem for simple parabolic points: definitions

This area discharges the **simple case** of the primitive classical input
`Work.FatouParabolic.FatouParabolicInput` of the area `Submission/Work/FatouParabolic/`, i.e. it
proves `FatouParabolicInput_simple`: for a polynomial map `F` of degree `≥ 2` with a fixed point
`z₀` of multiplier `1` and nonvanishing second derivative (`iteratedDeriv 2 F z₀ ≠ 0`), the basin
of `z₀` contains a critical point of `F`.

The proof of the general `FatouParabolicInput` in the simple case runs through the Leau--Fatou
theory of `Submission/Work/FatouCoord/`, which is available for a *simple* parabolic germ
(`iteratedDeriv 2 ≠ 0`) and needs no antiholomorphic square root: the explicit petal
`Petal r M` of `exists_petal_fatouCoord` carries a holomorphic injective Fatou coordinate whose
image exhausts the tails of all horizontal strips, and `exists_iterate_mem_Petal` shows that every
orbit converging to the parabolic point enters it.

The one interface of this area is `Work.FatouParabolic2.PetalData`: an attracting petal of `z₀`
with a holomorphic injective Fatou coordinate and the strip-exhaustion property, **preconnected**
(which the delivered `Work.FatouParabolic.PetalData` does not record, but which the construction
supplies).  On it the Liouville/covering argument of `NOTES_LEAD_mandelbar_gaps2.md` §2.1 gives a
critical point of `F` in the immediate basin.

## Main definitions

* `Work.FatouParabolic2.PetalData` — the petal interface, preconnected petal;
* `Work.FatouParabolic2.FatouParabolicInput_simple` — the simple case of the classical input;
* `Work.FatouParabolic2.ParabolicCyclesSimple` — the simplicity hypothesis used by the re-wired
  tricorn statements.

## Main results

* `Work.FatouParabolic2.fatouParabolicInput_simple` — Fatou's theorem in the simple case;
* `Work.FatouParabolic2.parabolicCycleInOmegaLimit_of_simple`,
  `Work.FatouParabolic2.quarterParabolicIsFixed_of_simple` — the two ledger statements re-wired to
  the simple input.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-! ## The petal interface -/

/-- **An attracting petal of a parabolic fixed point** `z₀` of `F`, with its Fatou coordinate:
the exact interface consumed by the Liouville/covering argument.  It is
`Work.FatouParabolic.PetalData` (the flower-free interface of the delivered area) with the
additional field that the petal is **preconnected**, which the construction from the explicit
Laue--Fatou petal `Work.FatouCoord.Petal r M` supplies. -/
structure PetalData (F : ℂ → ℂ) (z₀ : ℂ) where
  /-- the attracting petal -/
  Pa : Set ℂ
  /-- the Fatou coordinate on the petal -/
  φa : ℂ → ℂ
  isOpen_Pa : IsOpen Pa
  /-- the petal is connected (it is the image of a half-plane under the parabolic chart) -/
  isPreconnected_Pa : IsPreconnected Pa
  z₀_not_mem : z₀ ∉ Pa
  mapsTo_Pa : MapsTo F Pa Pa
  /-- the orbits in the petal converge to `z₀` -/
  tendsto_Pa : ∀ z ∈ Pa, Tendsto (fun n : ℕ => F^[n] z) atTop (𝓝 z₀)
  /-- every orbit converging to `z₀` without attaining it enters the petal -/
  enters_Pa : ∀ z : ℂ, Tendsto (fun n : ℕ => F^[n] z) atTop (𝓝 z₀) →
    (∀ n : ℕ, F^[n] z ≠ z₀) → ∃ n : ℕ, F^[n] z ∈ Pa
  φa_diff : DifferentiableOn ℂ φa Pa
  /-- the Abel equation -/
  φa_shift : ∀ z ∈ Pa, φa (F z) = φa z + 1
  φa_inj : Set.InjOn φa Pa
  /-- the image of the petal exhausts the tail of every horizontal strip -/
  image_strip : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
    ∃ z ∈ Pa, φa z = τ

/-- A `PetalData` is in particular a `Work.FatouParabolic.PetalData`. -/
def PetalData.toPetalData {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) :
    Work.FatouParabolic.PetalData F z₀ where
  Pa := pd.Pa
  φa := pd.φa
  isOpen_Pa := pd.isOpen_Pa
  z₀_not_mem := pd.z₀_not_mem
  mapsTo_Pa := pd.mapsTo_Pa
  tendsto_Pa := pd.tendsto_Pa
  enters_Pa := pd.enters_Pa
  φa_diff := pd.φa_diff
  φa_shift := pd.φa_shift
  φa_inj := pd.φa_inj
  image_strip := pd.image_strip

/-- **The petal is nonempty**: the strip-exhaustion property (applied to the horizontal strip of
height `1`) produces a point of it. -/
theorem PetalData.nonempty {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) : pd.Pa.Nonempty := by
  obtain ⟨C, hC⟩ := pd.image_strip 1 (by norm_num)
  obtain ⟨z, hz, -⟩ := hC ((C + 1 : ℝ) : ℂ) (by simp) (by simp)
  exact ⟨z, hz⟩

/-! ## The simple case of the classical input -/

/-- **Fatou's theorem on parabolic cycles, simple case.**  For a polynomial map `F : ℂ → ℂ` of
degree `≥ 2`, a fixed point `z₀` of multiplier `1` at which the second derivative does not vanish,
the basin of `z₀` contains a critical point of `F`.

This is the statement of `Work.FatouParabolic.FatouParabolicInput` with the additional simplicity
hypothesis `iteratedDeriv 2 F z₀ ≠ 0`; it is proved in this area
(`Work.FatouParabolic2.fatouParabolicInput_simple`).  Both uses of the classical input in the
tricorn project (the root-parabolic parameter and `c = 1/4`) are of this form. -/
def FatouParabolicInput_simple : Prop :=
  ∀ (F : ℂ → ℂ) (z₀ : ℂ), Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F →
    F z₀ = z₀ → deriv F z₀ = 1 → iteratedDeriv 2 F z₀ ≠ 0 →
    ∃ w : ℂ, Work.FatouParabolic.IsCriticalPoint F w ∧ w ∈ Work.FatouParabolic.basin F z₀

/-- The simple case implies the general input *at simple parabolic points*. -/
theorem FatouParabolicInput_simple.apply (h : FatouParabolicInput_simple) {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ ≠ 0) :
    ∃ w : ℂ, Work.FatouParabolic.IsCriticalPoint F w ∧ w ∈ Work.FatouParabolic.basin F z₀ :=
  h F z₀ hF hfix h1 h2

/-! ## The simplicity hypothesis of the tricorn re-wiring -/

/-- **The degenerate case of the classical input.**  Fatou's result on parabolic cycles for a
polynomial map `F` of degree `≥ 2` at a multiplier-one fixed point `z₀` at which the second
derivative *vanishes* (a multi-petal parabolic point).  Together with
`FatouParabolicInput_simple` (proved in this area) it gives the general
`Work.FatouParabolic.FatouParabolicInput`; see `Work.FatouParabolic2.fatouParabolicInput_split`. -/
def FatouParabolicInput_degenerate : Prop :=
  ∀ (F : ℂ → ℂ) (z₀ : ℂ), Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F →
    F z₀ = z₀ → deriv F z₀ = 1 → iteratedDeriv 2 F z₀ = 0 →
    ∃ w : ℂ, Work.FatouParabolic.IsCriticalPoint F w ∧ w ∈ Work.FatouParabolic.basin F z₀

/-- **The classical input splits into the simple and the degenerate case.**  This is the exact
form in which the delivered general input `Work.FatouParabolic.FatouParabolicInput` is obtained
from the two cases: the simple one is proved here
(`Work.FatouParabolic2.fatouParabolicInput_simple`), the degenerate one is the single remaining
named input. -/
theorem fatouParabolicInput_split (hSimple : FatouParabolicInput_simple)
    (hDeg : FatouParabolicInput_degenerate) : Work.FatouParabolic.FatouParabolicInput := by
  intro F z₀ hF hfix h1
  by_cases h2 : iteratedDeriv 2 F z₀ = 0
  · exact hDeg F z₀ hF hfix h1 h2
  · exact hSimple F z₀ hF hfix h1 h2

/-- **Every parabolic point of `T_c` is a simple parabolic point of its holomorphic return map.**
For every parabolic point `z` of `T_c` of (a) period `m` (in the sense of
`Work.Landing.IsParabolic c m z`, so `(T_c)^[m] z = z` and the multiplier of the holomorphic
return map `(Tsq c)^[m]` is `1`), the second derivative of that return map at `z` does not
vanish.  This is the extra hypothesis under which the simple input
`Work.FatouParabolic2.FatouParabolicInput_simple` replaces the general one in
`Work.FatouParabolic.parabolicCycleInOmegaLimit`. -/
def ParabolicCyclesSimple (c : ℂ) : Prop :=
  ∀ (z : ℂ) (m : ℕ), Work.Landing.IsParabolic c m z →
    iteratedDeriv 2 ((Work.Landing.Tsq c)^[m]) z ≠ 0

end

end Work.FatouParabolic2
