import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.FibreProjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sectorSliceDefs` — the slice of a sector at a complement configuration

The BF3c fibre selection of `Work.BoseBoxFock.box_to_model` (see
`FINDING_BF3c_selection_s8.md` §1 and `FINDING_BF3c_realcomplex_RESOLUTION.md` §3) selects, after
a sector `S` and a complement configuration `y`, the *slice*

    `sectorSlice e S Φ y u = slotExact e S Φ (pairCoord S u y)`

of the sector state `Φ_S = slotExact e S Φ` at `y`: the `S`-slots are put at `u`, the
complementary slots at `y`.  It is the object the model map consumes:

* it is *symmetric* in `u` (`slotExact e S` commutes with every permutation of the slots that
  preserves `S`, and `Φ` is symmetric);
* it lies in the `ℂ`-span of the monomials `∏_{i∈S} e (l i) (u i)` (the `PV`-product expands),
  hence — being symmetric — in `Sym^{|S|}(V_ℂ) = span_ℂ{M_α : |α| = |S|}`, i.e. in the image of
  `boxRealiseC` (`complexRealise.lean`);
* the form and the norm of the sector *integrate* over `y` into the forms/norms of the slices
  (Fubini, with the complement slots as spectators).

This module contains **definitions only** plus the trivial evaluation lemmas; the three
mathematical statements are the delegated lemmas
`Work.BoseBoxFock.exists_boxRealiseC_eq_sectorSlice`,
`Work.BoseBoxFock.slotSum_sector_pointwise` and the supporting symmetry statement.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The configuration obtained by putting the slots in `S` at the values `u` (indexed by `↥S`)
and the remaining slots at the values `y` (indexed by the complement). -/
def pairCoord {n : ℕ} (S : Finset (Fin n)) (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω) :
    Fin n → Ω :=
  fun i => if h : i ∈ S then u ⟨i, h⟩ else y ⟨i, h⟩

@[simp]
lemma pairCoord_mem {n : ℕ} (S : Finset (Fin n)) (u : {i // i ∈ S} → Ω)
    (y : {i // i ∉ S} → Ω) (i : Fin n) (h : i ∈ S) :
    pairCoord S u y i = u ⟨i, h⟩ :=
  dif_pos h

@[simp]
lemma pairCoord_notMem {n : ℕ} (S : Finset (Fin n)) (u : {i // i ∈ S} → Ω)
    (y : {i // i ∉ S} → Ω) (i : Fin n) (h : i ∉ S) :
    pairCoord S u y i = y ⟨i, h⟩ :=
  dif_neg h

/-- **The slice of the sector `S` of `Φ` at the complement configuration `y`**: the function of
the `S`-slots obtained by freezing the complementary slots at `y`. -/
def sectorSlice {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (y : {i // i ∉ S} → Ω) : ({i // i ∈ S} → Ω) → ℂ :=
  fun u => slotExact e S Φ (pairCoord S u y)

/-- The slice transported to the standard index type `Fin S.card` along `S.equivFin`, so that
the model's `boxRealiseC e S.card` (whose variables are `Fin S.card → Ω`) can be applied to it
directly. -/
def sliceF {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (y : {i // i ∉ S} → Ω) : (Fin S.card → Ω) → ℂ :=
  fun u => sectorSlice e S Φ y (fun i => u (S.equivFin i))

end Work.BoseBoxFock
