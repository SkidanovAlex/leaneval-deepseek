/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# The petal/Liouville core of Fatou's theorem: definitions

This module sets up the objects of the *design* of `Submission/Work/FatouParabolic/NOTES.md`
§3: the immediate parabolic basin of a parabolic point, the self-map it carries, the extended
Fatou coordinate obtained by running the orbit into the attracting petal, and the two classical
inputs of the design (the petal image and the simple connectivity of the basin).

* `Work.FatouParabolic.basinMap` — the self-map `z ↦ F z` of the punctured basin;
* `Work.FatouParabolic.entryTime`, `Work.FatouParabolic.extFatou` — the entry time of the orbit
  into the petal `fl.Pa` and the **extended Fatou coordinate** `φ (F z) = φ z + 1` on the whole
  punctured basin; the coordinate agrees with `fl.φa` on the petal (up to the entry time), and by
  the Abel equation on the invariant petal it does not depend on the entry time chosen;
* `Work.FatouParabolic.PetalImageStrip` — the petal image property supplied by the construction
  of `Submission/Work/FatouCoord/` (the Fatou coordinate of the petal contains the tail of every
  horizontal strip);
* `Work.FatouParabolic.ParabolicBasinSimplyConnected` — the classical topological input: the
  immediate parabolic basin of a polynomial is simply connected;
* `Work.FatouParabolic.BasinEscape` — the elementary growth condition on `F` which makes the
  basin bounded.
-/
import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FatouParabolic.Basin.mapsTo_puncturedBasin
import Submission.Work.FatouParabolic.Basin.preimage_mem_puncturedBasin
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter
open Set

namespace Work.FatouParabolic

open LeanEval.ComplexAnalysis (Tantibar)
open Classical

noncomputable section

/-! ## The self-map of the punctured basin -/

/-- The self-map `z ↦ F z` of the punctured basin of the fixed point `z₀`.  It is well defined
because a preimage of a point whose orbit converges to `z₀` without attaining it again has that
property (`Work.FatouParabolic.Basin.preimage_mem_puncturedBasin`, used through
`mapsTo_puncturedBasin`). -/
def basinMap (F : ℂ → ℂ) (z₀ : ℂ) (hfix : F z₀ = z₀) :
    ↥(puncturedBasin F z₀) → ↥(puncturedBasin F z₀) :=
  fun z => ⟨F z.1, Basin.mapsTo_puncturedBasin hfix z.2⟩

@[simp] theorem basinMap_coe {F : ℂ → ℂ} {z₀ : ℂ} (hfix : F z₀ = z₀)
    (z : ↥(puncturedBasin F z₀)) : (basinMap F z₀ hfix z : ℂ) = F z.1 := rfl

/-! ## The extended Fatou coordinate -/

/-- The **entry time** of the orbit of `z` into the petal `fl.Pa`: the first (some) time at
which the orbit of a point of the punctured basin reaches the attracting petal.  It exists by the
flower's `enters_Pa`, since a point of the punctured basin has an orbit converging to `z₀` which
never attains `z₀`. -/
noncomputable def entryTime {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) (z : ℂ)
    (hz : z ∈ puncturedBasin F z₀) : ℕ :=
  Classical.choose (fl.enters_Pa z (mem_basin.mp hz.2) hz.1)

theorem entryTime_spec {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) (z : ℂ)
    (hz : z ∈ puncturedBasin F z₀) :
    (F^[entryTime fl z hz]) z ∈ fl.Pa :=
  Classical.choose_spec (fl.enters_Pa z (mem_basin.mp hz.2) hz.1)

/-- The **extended Fatou coordinate** of the punctured basin: run the orbit of `z` into the
petal and read off the Fatou coordinate of the flower there, subtracting the number of steps.
Outside the basin the function is set to `0` (it is never used there). -/
noncomputable def extFatou {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) (z : ℂ) : ℂ :=
  if hz : z ∈ puncturedBasin F z₀ then
    fl.φa ((F^[entryTime fl z hz]) z) - (entryTime fl z hz : ℂ)
  else 0

theorem extFatou_eq {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) {z : ℂ}
    (hz : z ∈ puncturedBasin F z₀) :
    extFatou fl z = fl.φa ((F^[entryTime fl z hz]) z) - (entryTime fl z hz : ℂ) := by
  rw [extFatou]
  exact dite_eq_left hz

/-! ## The inputs of the design -/

/-- **The petal image property**: the image of the attracting petal `fl.Pa` under the Fatou
coordinate `fl.φa` contains the tail of every horizontal strip.  This is what the explicit
construction of the Fatou coordinate in `Submission/Work/FatouCoord/` produces
(`Work.FatouCoord.fatouCoordW_image_bdd`, through the wide petal `WidePetal`); it is the
analytic input which makes the extended coordinate surjective onto `ℂ`. -/
def PetalImageStrip {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoord.ParabolicFlower F g z₀) : Prop :=
  ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
    ∃ z ∈ fl.Pa, fl.φa z = τ

/-- **The classical topological input of the (superseded) first form of the design.**

⚠ This is **FALSE** in general: `puncturedBasin` is the *whole* basin, including every preimage
component, so it is not connected (at a root-parabolic parameter `F = T_c^10` has degree `1024`
while its degree on the immediate basin is `4`), and `SimplyConnectedSpace` requires
path-connectedness.  It is kept only because the files `Core/extFatou_*`,
`Core/false_of_bounded_of_injOn_of_surjective` and the first form of `Core/Main.lean` are stated
with it; the corrected design (lead note `NOTES_LEAD_mandelbar_gaps2.md` §2.1, implemented in
`Core/ImmBasin/`) uses the *immediate basin component* `Core.immBasin` and the lifting property
of the coverings `F^[n]`, and needs no simple-connectivity hypothesis at all. -/
def ParabolicBasinSimplyConnected (F : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  SimplyConnectedSpace ↥(puncturedBasin F z₀)

/-- The elementary growth condition on `F` which makes the basin bounded: outside a large disc,
`F` at least doubles the modulus.  A polynomial of degree `≥ 2` satisfies it. -/
def BasinEscape (F : ℂ → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖F z‖


/-! ## The flower together with its petal image property -/

/-- A `ParabolicFlowerFix` whose Fatou coordinate exhausts horizontal strips on the petal, i.e.
which satisfies `PetalImageStrip`.  This is the exact form in which the construction of
`Submission/Work/FatouCoord/` (the explicit Fatou coordinate `φ z = -1/z - c log(-1/z) + O(z)`
plus its strip-tail image statement) is consumed by the Liouville step of the design. -/
structure FlowerImageFix (F g : ℂ → ℂ) (z₀ : ℂ) extends
    Work.FatouCoordFix.ParabolicFlowerFix F g z₀ where
  /-- the image of the petal contains the tail of every horizontal strip -/
  image_strip : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
    ∃ z ∈ toParabolicFlowerFix.Pa, toParabolicFlowerFix.φa z = τ

/-- The petal image property of `FlowerImageFix`, in the form used by the design. -/
theorem FlowerImageFix.petalImageStrip {F g : ℂ → ℂ} {z₀ : ℂ} (fl : FlowerImageFix F g z₀) :
    PetalImageStrip fl.toParabolicFlowerFix.toParabolicFlower :=
  fl.image_strip


/-! ## The petal data of a parabolic fixed point -/

/-- **The data of an attracting petal** of the fixed point `z₀` of `F`: an open `F`-invariant
domain `Pa` with `z₀ ∉ Pa` whose orbits converge to `z₀`, which attracts every orbit converging
to `z₀`, together with an injective holomorphic Fatou coordinate `φa` on it satisfying the Abel
equation, and whose image exhausts the tail of every horizontal strip.

This is the exact interface consumed by the Liouville step of the design; it is satisfied by the
Leau–Fatou flowers of `Submission/Work/FatouCoord/` and `Submission/Work/FatouCoordFix/` (see
`PetalData.ofFlowerImageFix`), but it does not mention the flower, the antiholomorphic square
root or the germ, so it also applies to parabolic points with several petals, as soon as such
data is available. -/
structure PetalData (F : ℂ → ℂ) (z₀ : ℂ) where
  /-- the attracting petal -/
  Pa : Set ℂ
  /-- the Fatou coordinate on the petal -/
  φa : ℂ → ℂ
  isOpen_Pa : IsOpen Pa
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

/-- The petal data of a Leau–Fatou flower with its petal image property. -/
def PetalData.ofFlowerImageFix {F g : ℂ → ℂ} {z₀ : ℂ} (fl : FlowerImageFix F g z₀) :
    PetalData F z₀ where
  Pa := fl.Pa
  φa := fl.φa
  isOpen_Pa := fl.isOpen_Pa
  z₀_not_mem := fl.z₀_not_mem
  mapsTo_Pa := fl.mapsTo_Pa
  tendsto_Pa := fl.tendsto_Pa
  enters_Pa := fl.enters_Pa
  φa_diff := fl.φa_fatou.1.2.1
  φa_shift := fl.φa_shift
  φa_inj := fl.φa_fatou.2
  image_strip := fl.image_strip


/-! ## The extended Fatou coordinate of petal data -/

/-- The entry time of the orbit of `z` into the petal of the petal data. -/
noncomputable def pdEntryTime {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) (z : ℂ)
    (hz : z ∈ puncturedBasin F z₀) : ℕ :=
  Classical.choose (pd.enters_Pa z (mem_basin.mp hz.2) hz.1)

theorem pdEntryTime_spec {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) (z : ℂ)
    (hz : z ∈ puncturedBasin F z₀) : (F^[pdEntryTime pd z hz]) z ∈ pd.Pa :=
  Classical.choose_spec (pd.enters_Pa z (mem_basin.mp hz.2) hz.1)

/-- The extended Fatou coordinate of petal data: the same construction as `extFatou`, for the
flower-free interface `PetalData`. -/
noncomputable def pdExtFatou {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) (z : ℂ) : ℂ :=
  if hz : z ∈ puncturedBasin F z₀ then
    pd.φa ((F^[pdEntryTime pd z hz]) z) - (pdEntryTime pd z hz : ℂ)
  else 0

theorem pdExtFatou_eq {F : ℂ → ℂ} {z₀ : ℂ} (pd : PetalData F z₀) {z : ℂ}
    (hz : z ∈ puncturedBasin F z₀) :
    pdExtFatou pd z = pd.φa ((F^[pdEntryTime pd z hz]) z) - (pdEntryTime pd z hz : ℂ) := by
  rw [pdExtFatou]
  exact dite_eq_left hz

end

end Work.FatouParabolic
