/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# R4: from "the `∗`-regular closure is a division ring" to `DivLoc`

This file contains the *unconditional* half of the bridge of `Submission/Work/ORDivLoc`: the
reduction of `DivLoc` (division of the division closure `D H = D_{K[H]}(U(G))`) to the division of
the `∗`-regular closure `V = R(K[H], U(G))` of the image of `K[H]` in `U(G)`.

The mathematics is two lines long.

* `IsDivisionClosed (V.toSubring)` in `U(G)`: `V` is a von Neumann regular subring of the directly
  finite ring `U(G)` (direct finiteness follows from the faithful rank function `rk_G`), and a von
  Neumann regular subring of a directly finite ring containing `1` is division closed — the same
  argument as `Work.ORBridgeLinnell.isDivisionClosed_range`. Hence the *division closure*
  `D H`, being the smallest division closed subring containing the image of `K[H]`, is contained
  in `V`.
* If `V` is a division ring, then for `0 ≠ x ∈ D H ⊆ V` there is `y ∈ V` with `x * y = 1`; since
  `D H` is division closed in `U(G)`, `y ∈ D H`; so `x` is a unit of `D H`.

In particular the *only* analytic input of the bridge is `StarClosureDivOn`: the statement that the
`∗`-regular closure of the image of `K[H]` is a division ring.  That statement is exactly what the
JZLA20 engine (node N6) delivers from [JZLA20, Proposition 3.11]; see `N6.lean`.
-/
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORDivLoc.Vocabulary
import Submission.Work.ORHughesFree.DivisionClosure.divisionClosure_idem
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

universe u v

namespace Work.ORDivLoc

open Work.ORHughesFree

variable {G : Type v} [Group G] {K : Type u} [Field K]

/-! ## A von Neumann regular subring of a directly finite ring is division closed -/

/-- **A von Neumann regular subring `R ⊆ U` of a directly finite ring is division closed in `U`.**

Let `R` be von Neumann regular, `U` directly finite (`a * b = 1 → b * a = 1`), `x ∈ R` and
`x * y = 1` in `U`.  Choose a weak inverse `w ∈ R` of `x`; then `x * w = (x * w * x) * y = x * y
= 1`, so direct finiteness gives `w * x = 1`, and `y = 1 * y = (w * x) * y = w * (x * y) = w ∈ R`.

The same argument in the form used by `Work.ORBridgeLinnell.isDivisionClosed_range` is applied
there to the range of an injective homomorphism out of a directly finite von Neumann regular ring;
here it is the `∗`-regular closure `V = R(K[H], U(G))` of `U(G)`. -/
theorem isDivisionClosed_starRegularClosure {U : Type*} [Ring U] [StarRing U] [IsStarRegular U]
    (hdf : ∀ a b : U, a * b = 1 → b * a = 1) (R : StarSubring U) :
    IsDivisionClosed (starRegularClosure R).toSubring := by
  intro x hx y hxy
  haveI : IsStarRegular ↥(starRegularClosure R) :=
    StarRegular.starRegularClosure_isStarRegular R
  obtain ⟨w, hw⟩ := VonNeumannRegularRing.exists_mul_inverse
    (R := ↥(starRegularClosure R)) (⟨x, hx⟩ : ↥(starRegularClosure R))
  -- `x * w = 1` in `U`, because `x * w * x = x`
  have h2 : (x : U) * (w : U) * (x : U) = (x : U) :=
    congrArg (fun z : ↥(starRegularClosure R) => (z : U)) hw
  have hxw : (x : U) * (w : U) = 1 := by
    calc (x : U) * (w : U) = (x : U) * (w : U) * 1 := (mul_one _).symm
      _ = (x : U) * (w : U) * ((x : U) * y) := by rw [hxy]
      _ = ((x : U) * (w : U) * (x : U)) * y := (mul_assoc _ _ _).symm
      _ = (x : U) * y := by rw [h2]
      _ = 1 := hxy
  have hwx : (w : U) * (x : U) = 1 := hdf _ _ hxw
  have hy : y = (w : U) := by
    calc y = 1 * y := (one_mul y).symm
      _ = ((w : U) * (x : U)) * y := by rw [hwx]
      _ = (w : U) * ((x : U) * y) := mul_assoc _ _ _
      _ = (w : U) * 1 := by rw [hxy]
      _ = (w : U) := mul_one _
  rw [hy]
  exact w.2

/-- `U(G)` is directly finite, with the direct finiteness coming from the faithful Sylvester rank
function `rk_G` of the envelope (`Work.ORBridgeLinnell.directlyFinite_of_faithful`). -/
theorem directlyFinite_envelope (E : Work.ORVonNeumann.StarRegularEnvelope G) :
    ∀ a b : E.U, a * b = 1 → b * a = 1 :=
  fun _ _ hab => Work.ORBridgeLinnell.directlyFinite_of_faithful E.rk E.rk_faithful hab

/-- The `∗`-regular closure `V = R(K[H], U(G))` of the image of `K[H]` is division closed in
`U(G)`. -/
theorem isDivisionClosed_starClosureOfSubgroup (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    IsDivisionClosed (starClosureOfSubgroup E φK H).toSubring := by
  haveI : IsStarRegular E.U := isStarRegular_envelope E
  exact isDivisionClosed_starRegularClosure (directlyFinite_envelope E) _

/-! ## The bridge -/

/-- **`D H ⊆ V`**: the division closure of `K[H]` in `U(G)` is contained in the `∗`-regular
closure of the image of `K[H]`.  This is the minimality of the division closure applied to the
division closedness of `V`. -/
theorem D_le_starClosureOfSubgroup (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    Work.ORBridgeLinnell.D E φK H ≤ (starClosureOfSubgroup E φK H).toSubring :=
  (Work.ORBridgeLinnell.D_le_iff E φK (isDivisionClosed_starClosureOfSubgroup E φK H)).mpr
    (range_toUK_subset_starClosure E φK H)

/-- **R4: node N6's division ring at the `∗`-regular closure implies `DivLoc` at `H`.**

If the `∗`-regular closure `V = R(K[H], U(G))` of the image of `K[H]` in `U(G)` is a division
ring, then every nonzero element of the division closure `D H = D_{K[H]}(U(G))` is a unit.

Note that no hypothesis on `H` is used: local indicability enters only through the availability of
`StarClosureDivOn` (the JZLA20 engine needs `H` locally indicable to produce it). -/
theorem divOn_of_starClosureDivOn (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) (h : StarClosureDivOn E φK H) :
    DivOn E φK H := by
  intro x hx0
  have hxmem : (x : E.U) ∈ (starClosureOfSubgroup E φK H : Set E.U) :=
    D_le_starClosureOfSubgroup E φK H x.2
  obtain ⟨u, hu⟩ := h.2 (⟨(x : E.U), hxmem⟩ : ↥(starClosureOfSubgroup E φK H)) (by
    intro hh
    refine hx0 (Subtype.ext ?_)
    have := congrArg (fun z : ↥(starClosureOfSubgroup E φK H) => (z : E.U)) hh
    simpa using this)
  set wv : ↥(starClosureOfSubgroup E φK H) := ((u⁻¹ : (↥(starClosureOfSubgroup E φK H))ˣ) :
    ↥(starClosureOfSubgroup E φK H)) with hwv
  have hxw : (x : E.U) * (wv : E.U) = 1 := by
    have h2 : (⟨(x : E.U), hxmem⟩ : ↥(starClosureOfSubgroup E φK H)) * wv = 1 := by
      rw [← hu]; exact Units.mul_inv u
    exact congrArg (fun z : ↥(starClosureOfSubgroup E φK H) => (z : E.U)) h2
  have hwx : (wv : E.U) * (x : E.U) = 1 := by
    have h2 : wv * (⟨(x : E.U), hxmem⟩ : ↥(starClosureOfSubgroup E φK H)) = 1 := by
      rw [← hu]; exact Units.inv_mul u
    exact congrArg (fun z : ↥(starClosureOfSubgroup E φK H) => (z : E.U)) h2
  have hwmem : (wv : E.U) ∈ Work.ORBridgeLinnell.D E φK H :=
    Work.ORBridgeLinnell.isDivisionClosed_D E φK H (x : E.U) x.2 (wv : E.U) hxw
  exact isUnit_iff_exists.mpr ⟨⟨(wv : E.U), hwmem⟩, Subtype.ext hxw, Subtype.ext hwx⟩

/-! ## The direct route from node N6's output to `DivLoc` -/

/-- The image in `U(G)` of the division closure of the image of `K[H]` in `V = R(K[H], U(G))`:
this is the subring of `U(G)` whose division-ring property is node N6's output. -/
noncomputable def codDivClosure (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) : Subring E.U :=
  (divisionClosure (Set.range (starClosureCod E φK H))).map
    (Subring.subtype (starClosureOfSubgroup E φK H).toSubring)

/-- `↥V` is directly finite: it is a subring of the directly finite ring `U(G)`. -/
theorem directlyFinite_starClosure (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    ∀ a b : ↥(starClosureOfSubgroup E φK H), a * b = 1 → b * a = 1 := by
  intro a b hab
  have habU : (a : E.U) * (b : E.U) = 1 :=
    congrArg (fun z : ↥(starClosureOfSubgroup E φK H) => (z : E.U)) hab
  exact Subtype.ext (directlyFinite_envelope E _ _ habU)

/-- The image in `U(G)` of the division closure of the image of `K[H]` in `V` is division closed
in `U(G)`: it is the image of a subring of `V` which is closed under inverses in `V`, and `V` is
division closed in `U(G)`. -/
theorem isDivisionClosed_codDivClosure (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    IsDivisionClosed (codDivClosure E φK H) := by
  intro x hx y hxy
  obtain ⟨a, ha, rfl⟩ := (Subring.mem_map).mp hx
  -- `y` lies in `V`, because `V` is division closed in `U(G)`
  have hyV : y ∈ (starClosureOfSubgroup E φK H : Set E.U) :=
    isDivisionClosed_starClosureOfSubgroup E φK H (a : E.U) a.2 y hxy
  refine (Subring.mem_map).mpr ⟨⟨y, hyV⟩, ?_, rfl⟩
  -- `⟨y, hyV⟩` is the inverse in `V` of `a ∈ divisionClosure (Set.range φ')`
  have hab : a * (⟨y, hyV⟩ : ↥(starClosureOfSubgroup E φK H)) = 1 := Subtype.ext hxy
  have hba : (⟨y, hyV⟩ : ↥(starClosureOfSubgroup E φK H)) * a = 1 := by
    have hyx : y * (a : E.U) = 1 := directlyFinite_envelope E _ _ hxy
    exact Subtype.ext hyx
  exact Work.ORHughesFree.DivisionClosure.divisionClosure_inv_mem
    (Set.range (starClosureCod E φK H)) ha hab hba

/-- The image of `K[H]` in `U(G)` lies in the image of the division closure of its image in `V`. -/
theorem range_toUK_subset_codDivClosure (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    Set.range (Work.ORBridgeLinnell.toUK E φK H) ⊆ (codDivClosure E φK H : Set E.U) := by
  rintro _ ⟨w, rfl⟩
  refine (Subring.mem_map).mpr ⟨(starClosureCod E φK H w : ↥(starClosureOfSubgroup E φK H)),
    Work.ORHughesFree.subset_divisionClosure _ ⟨w, rfl⟩, ?_⟩
  rfl

/-- `D H ≤ codDivClosure`: the division closure of `K[H]` in `U(G)` is contained in the image of
the division closure of `K[H]` in the `∗`-regular closure `V`. -/
theorem D_le_codDivClosure (E : Work.ORVonNeumann.StarRegularEnvelope G)
    (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    Work.ORBridgeLinnell.D E φK H ≤ codDivClosure E φK H :=
  (divisionClosureOf_le_iff (isDivisionClosed_codDivClosure E φK H)).mpr
    (range_toUK_subset_codDivClosure E φK H)

/-- **Node N6's output implies `DivLoc` at `H`, with no epicity hypothesis.**

If the division closure `D_{K[H],V}` of the image of `K[H]` in the `∗`-regular closure `V` is a
division ring, then every nonzero element of `D_{K[H]}(U(G))` is a unit: such an `x` is already in
`codDivClosure`, so its inverse in `V` exists, and it is in `D_{K[H]}(U(G))` by division
closedness.

This is the form in which the bridge consumes node N6's output
(`Work.ORHughesFree.Section6.isUnit_of_mem_divisionClosure`, which needs no epicity either), and
it is stated at arbitrary universes. -/
theorem divOn_of_clDivOn (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ)
    [Algebra K E.U] (H : Subgroup G) (h : ClDivOn E φK H) : DivOn E φK H := by
  intro x hx0
  have hxA : (x : E.U) ∈ codDivClosure E φK H := D_le_codDivClosure E φK H x.2
  obtain ⟨a, ha, hax⟩ := (Subring.mem_map).mp hxA
  have ha0 : (⟨a, ha⟩ : ↥(divisionClosure (Set.range (starClosureCod E φK H)))) ≠ 0 := by
    intro h0
    have h1 : a = 0 := congrArg Subtype.val h0
    refine hx0 (Subtype.ext ?_)
    rw [← hax, h1]
    rfl
  obtain ⟨u, hu⟩ := h.2 (⟨a, ha⟩ : ↥(divisionClosure (Set.range (starClosureCod E φK H)))) ha0
  let w : ↥(divisionClosure (Set.range (starClosureCod E φK H))) :=
    (u⁻¹ : (↥(divisionClosure (Set.range (starClosureCod E φK H))))ˣ)
  have hxw : (x : E.U) * (w : E.U) = 1 := by
    have h2 : (⟨a, ha⟩ : ↥(divisionClosure (Set.range (starClosureCod E φK H)))) * w = 1 := by
      rw [← hu]; exact Units.mul_inv u
    have h3 := congrArg (fun z : ↥(divisionClosure (Set.range (starClosureCod E φK H))) =>
      ((z : ↥(starClosureOfSubgroup E φK H)) : E.U)) h2
    rw [← hax]
    exact h3
  have hwmem : (w : E.U) ∈ Work.ORBridgeLinnell.D E φK H :=
    Work.ORBridgeLinnell.isDivisionClosed_D E φK H (x : E.U) x.2 (w : E.U) hxw
  have hwx : (w : E.U) * (x : E.U) = 1 := by
    have h2 : w * (⟨a, ha⟩ : ↥(divisionClosure (Set.range (starClosureCod E φK H)))) = 1 := by
      rw [← hu]; exact Units.inv_mul u
    have h3 := congrArg (fun z : ↥(divisionClosure (Set.range (starClosureCod E φK H))) =>
      ((z : ↥(starClosureOfSubgroup E φK H)) : E.U)) h2
    rw [← hax]
    exact h3
  exact isUnit_iff_exists.mpr ⟨⟨w, hwmem⟩, Subtype.ext hxw, Subtype.ext hwx⟩

/-- **The deliverable of the subproject, in the vocabulary of node N6.**  If for every locally
indicable `H ≤ G` the division closure of the image of `K[H]` in the `∗`-regular closure `V` is a
division ring (node N6's output), then `DivLoc K G φK` holds.

This is stated at arbitrary universes and needs no epicity, no rank function and no
Hughes-freeness: those are the inputs of the *construction* (`thm61Step_nonempty`) of node N6. -/
theorem divLoc_of_clDivLoc (K : Type u) [Field K] (G : Type v) [Group G] [Countable G]
    (φK : K →+* ℂ) (h : ClDivLoc K G φK) : DivLoc K G φK := by
  letI := Work.ORBridgeLinnell.kAlgebra (Work.ORBridgeLinnell.countableEnvelope G) φK
  intro H hLI
  exact divOn_of_clDivOn (Work.ORBridgeLinnell.countableEnvelope G) φK H (h H hLI)

/-- **R4 at the level of `DivLoc`**: if the `∗`-regular closure of the image of `K[H]` in
`U(G) = countableEnvelope G` is a division ring for every locally indicable `H ≤ G`, then
`DivLoc K G φK` holds. -/
theorem divLoc_of_starClosureDivLoc (K : Type u) [Field K] (G : Type v) [Group G] [Countable G]
    (φK : K →+* ℂ) (h : StarClosureDivLoc K G φK) : DivLoc K G φK := by
  letI := Work.ORBridgeLinnell.kAlgebra (Work.ORBridgeLinnell.countableEnvelope G) φK
  intro H hLI
  exact divOn_of_starClosureDivOn (Work.ORBridgeLinnell.countableEnvelope G) φK H (h H hLI)

end Work.ORDivLoc
