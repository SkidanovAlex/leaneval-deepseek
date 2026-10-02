import Mathlib
import Submission.Work.StemsB.FibreTrivial
import Submission.Work.StemsB.hasHLP_pullback
import Submission.Work.StemsB.SerreSphereStep
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.uctDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational homology of the fibres of a Hurewicz fibration over the ends of a path

For a Hurewicz fibration `p : C(E,B)` and a path `γ : I → B`, the fibre homology `H_j(p⁻¹{γ 0})`
and `H_j(p⁻¹{γ 1})` are isomorphic for every `j`; hence the fibre homology does not depend on the
base point along a path.

**Restoration note (this session).**  This module was accidentally overwritten by another agent of
the same flight: two areas were using the file name `FibreTransport.lean`.  The declarations below
have been restored, name for name and with the same statements, from the compiled artifact of the
previous version.  Please do not reuse this file name; the STEMSB counterpart of the construction
below (`cylFibreRes`, `pathPsi`, `fibreRestriction_transport_of_inputs`) lives in
`Submission/Work/StemsB/CylFibreTransport.lean`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-! ## The two contractions of the unit interval -/

/-- The straight-line contraction `(t,s) ↦ t * (1-s)` of the interval to `0`. -/
def unitContrZeroFun : ↑unitInterval × ↑unitInterval → ↑unitInterval :=
  fun q => ⟨(q.1 : ℝ) * (1 - (q.2 : ℝ)), by
    have h1 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
    have h2 : (q.1 : ℝ) ≤ 1 := q.1.2.2
    have h3 : (0 : ℝ) ≤ (q.2 : ℝ) := q.2.2.1
    have h4 : (q.2 : ℝ) ≤ 1 := q.2.2.2
    exact ⟨by nlinarith, by nlinarith⟩⟩

/-- The contraction `(t,s) ↦ t*(1-s)` as a continuous map. -/
def unitContrZero : C(↑unitInterval × ↑unitInterval, ↑unitInterval) where
  toFun := unitContrZeroFun
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem unitContrZero_zero (t : ↑unitInterval) : unitContrZero (t, 0) = t := by
  refine Subtype.ext ?_
  show (t : ℝ) * (1 - ((0 : ↑unitInterval) : ℝ)) = (t : ℝ)
  simp

theorem unitContrZero_one (t : ↑unitInterval) : unitContrZero (t, 1) = 0 := by
  refine Subtype.ext ?_
  show (t : ℝ) * (1 - ((1 : ↑unitInterval) : ℝ)) = ((0 : ↑unitInterval) : ℝ)
  simp

theorem unitContrZero_fixes (s : ↑unitInterval) : unitContrZero (0, s) = 0 := by
  refine Subtype.ext ?_
  show ((0 : ↑unitInterval) : ℝ) * (1 - (s : ℝ)) = ((0 : ↑unitInterval) : ℝ)
  simp

/-- The straight-line contraction `(t,s) ↦ 1 - (1-t)*(1-s)` of the interval to `1`. -/
def unitContrOneFun : ↑unitInterval × ↑unitInterval → ↑unitInterval :=
  fun q => ⟨1 - (1 - (q.1 : ℝ)) * (1 - (q.2 : ℝ)), by
    have h1 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
    have h2 : (q.1 : ℝ) ≤ 1 := q.1.2.2
    have h3 : (0 : ℝ) ≤ (q.2 : ℝ) := q.2.2.1
    have h4 : (q.2 : ℝ) ≤ 1 := q.2.2.2
    exact ⟨by nlinarith, by nlinarith⟩⟩

/-- The contraction `(t,s) ↦ 1 - (1-t)*(1-s)` as a continuous map. -/
def unitContrOne : C(↑unitInterval × ↑unitInterval, ↑unitInterval) where
  toFun := unitContrOneFun
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem unitContrOne_zero (t : ↑unitInterval) : unitContrOne (t, 0) = t := by
  refine Subtype.ext ?_
  show 1 - (1 - (t : ℝ)) * (1 - ((0 : ↑unitInterval) : ℝ)) = (t : ℝ)
  simp

theorem unitContrOne_one (t : ↑unitInterval) : unitContrOne (t, 1) = 1 := by
  refine Subtype.ext ?_
  show 1 - (1 - (t : ℝ)) * (1 - ((1 : ↑unitInterval) : ℝ)) = ((1 : ↑unitInterval) : ℝ)
  simp

theorem unitContrOne_fixes (s : ↑unitInterval) : unitContrOne (1, s) = 1 := by
  refine Subtype.ext ?_
  show 1 - (1 - ((1 : ↑unitInterval) : ℝ)) * (1 - (s : ℝ)) = ((1 : ↑unitInterval) : ℝ)
  simp

/-- The straight-line contraction `(x,s) ↦ (1-s)*x + s*t` of the interval onto a point `t`. -/
def unitContrAtFun (t : ↑unitInterval) : ↑unitInterval × ↑unitInterval → ↑unitInterval :=
  fun q => ⟨(1 - (q.2 : ℝ)) * (q.1 : ℝ) + (q.2 : ℝ) * (t : ℝ), by
    have h1 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1
    have h2 : (q.1 : ℝ) ≤ 1 := q.1.2.2
    have h3 : (0 : ℝ) ≤ (q.2 : ℝ) := q.2.2.1
    have h4 : (q.2 : ℝ) ≤ 1 := q.2.2.2
    have h5 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have h6 : (t : ℝ) ≤ 1 := t.2.2
    exact ⟨by nlinarith, by nlinarith⟩⟩

/-- The contraction `(x,s) ↦ (1-s)*x + s*t` of the interval onto `t`, as a continuous map.
This is the form in which the engine `Work.Serre.isZero_relChains_fibre_of_contraction` consumes a
contraction, and it is needed for *every* `t` — the special cases `t = 0` and `t = 1` are
`unitContrZero`/`unitContrOne`. -/
def unitContrAt (t : ↑unitInterval) : C(↑unitInterval × ↑unitInterval, ↑unitInterval) where
  toFun := unitContrAtFun t
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem unitContrAt_zero (t x : ↑unitInterval) : unitContrAt t (x, 0) = x := by
  refine Subtype.ext ?_
  show (1 - ((0 : ↑unitInterval) : ℝ)) * (x : ℝ) + ((0 : ↑unitInterval) : ℝ) * (t : ℝ) = (x : ℝ)
  simp

theorem unitContrAt_one (t x : ↑unitInterval) : unitContrAt t (x, 1) = t := by
  refine Subtype.ext ?_
  show (1 - ((1 : ↑unitInterval) : ℝ)) * (x : ℝ) + ((1 : ↑unitInterval) : ℝ) * (t : ℝ) = (t : ℝ)
  simp

theorem unitContrAt_fixes (t s : ↑unitInterval) : unitContrAt t (t, s) = t := by
  refine Subtype.ext ?_
  show (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) * (t : ℝ) = (t : ℝ)
  ring

/-- The contraction `unitContrAt t` packaged as the datum consumed by
`Work.Serre.isZero_relChains_fibre_of_contraction`. -/
theorem unitContrAt_spec (t : ↑unitInterval) :
    (∀ x : ↑unitInterval, unitContrAt t (x, 0) = x) ∧
      (∀ x : ↑unitInterval, unitContrAt t (x, 1) = t) ∧
      (∀ s : ↑unitInterval, unitContrAt t (t, s) = t) :=
  ⟨unitContrAt_zero t, unitContrAt_one t, unitContrAt_fixes t⟩

/-! ## The trivialization of the pullback of a Hurewicz fibration over an interval -/

/-- The base change of a Hurewicz fibration is a Hurewicz fibration. -/
theorem isHurewiczFibration_pullbackSnd {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    IsHurewiczFibration (pullbackSnd p γ) :=
  fun Z => hasHLP_pullback p γ (hp Z)

/-- **The pullback of a Hurewicz fibration over the interval is trivial at `0`**: there is a map
`g` to the fibre over `0` and a homotopy from the identity to `fibreIncl ∘ g` in the total space. -/
theorem fibreTrivial_zero {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    ∃ (g : C(Pullback p γ, fibre (pullbackSnd p γ) 0))
      (G : C(Pullback p γ × ↑unitInterval, Pullback p γ)),
      (∀ x : Pullback p γ, G (x, 0) = x) ∧
      (∀ x : Pullback p γ, G (x, 1) = (fibreIncl (pullbackSnd p γ) 0) (g x)) ∧
      ∀ (x : Pullback p γ) (t : ↑unitInterval),
        (pullbackSnd p γ) (G (x, t)) = unitContrZero ((pullbackSnd p γ) x, t) :=
  fibreTrivial_of_contraction (pullbackSnd p γ) (isHurewiczFibration_pullbackSnd p hp γ) 0
    unitContrZero unitContrZero_zero unitContrZero_one unitContrZero_fixes

/-- **The pullback of a Hurewicz fibration over the interval is trivial at `1`.** -/
theorem fibreTrivial_one {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    ∃ (g : C(Pullback p γ, fibre (pullbackSnd p γ) 1))
      (G : C(Pullback p γ × ↑unitInterval, Pullback p γ)),
      (∀ x : Pullback p γ, G (x, 0) = x) ∧
      (∀ x : Pullback p γ, G (x, 1) = (fibreIncl (pullbackSnd p γ) 1) (g x)) ∧
      ∀ (x : Pullback p γ) (t : ↑unitInterval),
        (pullbackSnd p γ) (G (x, t)) = unitContrOne ((pullbackSnd p γ) x, t) :=
  fibreTrivial_of_contraction (pullbackSnd p γ) (isHurewiczFibration_pullbackSnd p hp γ) 1
    unitContrOne unitContrOne_zero unitContrOne_one unitContrOne_fixes

/-! ## The two trivializations, unpacked -/

section Triv

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The trivialization at `0`, as a map to the fibre over `0`. -/
def pzG (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    C(Pullback p γ, fibre (pullbackSnd p γ) 0) :=
  Classical.choose (fibreTrivial_zero p hp γ)

/-- The homotopy underlying the trivialization at `0`. -/
def pzH (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    C(Pullback p γ × ↑unitInterval, Pullback p γ) :=
  Classical.choose (Classical.choose_spec (fibreTrivial_zero p hp γ))

theorem pzH_zero (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : Pullback p γ) : pzH p hp γ (x, 0) = x :=
  (Classical.choose_spec (Classical.choose_spec (fibreTrivial_zero p hp γ))).1 x

theorem pzH_one (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : Pullback p γ) : pzH p hp γ (x, 1) = (fibreIncl (pullbackSnd p γ) 0) (pzG p hp γ x) :=
  (Classical.choose_spec (Classical.choose_spec (fibreTrivial_zero p hp γ))).2.1 x

theorem pzH_base (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : Pullback p γ) (t : ↑unitInterval) :
    (pullbackSnd p γ) (pzH p hp γ (x, t)) = unitContrZero ((pullbackSnd p γ) x, t) :=
  (Classical.choose_spec (Classical.choose_spec (fibreTrivial_zero p hp γ))).2.2 x t

/-- The restriction of the homotopy at `0` to the fibre over `0`. -/
def pzHfib (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    C(fibre (pullbackSnd p γ) 0 × ↑unitInterval, fibre (pullbackSnd p γ) 0) where
  toFun z := ⟨pzH p hp γ ((fibreIncl (pullbackSnd p γ) 0) z.1, z.2), by
    have h : (pullbackSnd p γ) (fibreIncl (pullbackSnd p γ) 0 z.1) = 0 := z.1.2
    rw [pzH_base, h, unitContrZero_fixes]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem pzHfib_zero (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : fibre (pullbackSnd p γ) 0) : pzHfib p hp γ (x, 0) = x :=
  Subtype.ext (pzH_zero p hp γ ((fibreIncl (pullbackSnd p γ) 0) x))

theorem pzHfib_one (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : fibre (pullbackSnd p γ) 0) :
    pzHfib p hp γ (x, 1) = pzG p hp γ ((fibreIncl (pullbackSnd p γ) 0) x) :=
  Subtype.ext (pzH_one p hp γ ((fibreIncl (pullbackSnd p γ) 0) x))

/-- The trivialization at `1`, as a map to the fibre over `1`. -/
def poG (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    C(Pullback p γ, fibre (pullbackSnd p γ) 1) :=
  Classical.choose (fibreTrivial_one p hp γ)

/-- The homotopy underlying the trivialization at `1`. -/
def poH (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    C(Pullback p γ × ↑unitInterval, Pullback p γ) :=
  Classical.choose (Classical.choose_spec (fibreTrivial_one p hp γ))

theorem poH_zero (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : Pullback p γ) : poH p hp γ (x, 0) = x :=
  (Classical.choose_spec (Classical.choose_spec (fibreTrivial_one p hp γ))).1 x

theorem poH_one (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : Pullback p γ) : poH p hp γ (x, 1) = (fibreIncl (pullbackSnd p γ) 1) (poG p hp γ x) :=
  (Classical.choose_spec (Classical.choose_spec (fibreTrivial_one p hp γ))).2.1 x

theorem poH_base (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : Pullback p γ) (t : ↑unitInterval) :
    (pullbackSnd p γ) (poH p hp γ (x, t)) = unitContrOne ((pullbackSnd p γ) x, t) :=
  (Classical.choose_spec (Classical.choose_spec (fibreTrivial_one p hp γ))).2.2 x t

/-- The restriction of the homotopy at `1` to the fibre over `1`. -/
def poHfib (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B)) :
    C(fibre (pullbackSnd p γ) 1 × ↑unitInterval, fibre (pullbackSnd p γ) 1) where
  toFun z := ⟨poH p hp γ ((fibreIncl (pullbackSnd p γ) 1) z.1, z.2), by
    have h : (pullbackSnd p γ) (fibreIncl (pullbackSnd p γ) 1 z.1) = 1 := z.1.2
    rw [poH_base, h, unitContrOne_fixes]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

theorem poHfib_zero (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : fibre (pullbackSnd p γ) 1) : poHfib p hp γ (x, 0) = x :=
  Subtype.ext (poH_zero p hp γ ((fibreIncl (pullbackSnd p γ) 1) x))

theorem poHfib_one (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(↑unitInterval, B))
    (x : fibre (pullbackSnd p γ) 1) :
    poHfib p hp γ (x, 1) = poG p hp γ ((fibreIncl (pullbackSnd p γ) 1) x) :=
  Subtype.ext (poH_one p hp γ ((fibreIncl (pullbackSnd p γ) 1) x))

end Triv

/-! ## The fibres over the two ends are canonically the same space -/

section Hom

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The fibre of the pullback over `0` is canonically the preimage of `{γ 0}`. -/
def fibreZeroHom (p : C(E, B)) (γ : C(↑unitInterval, B)) :
    C(fibre (pullbackSnd p γ) 0, ↥(p ⁻¹' {γ 0})) where
  toFun := fun y => ⟨y.1.1.1, by
    have h1 : p y.1.1.1 = γ y.1.1.2 := y.1.2
    have h2 : y.1.1.2 = (0 : ↑unitInterval) := y.2
    rw [h2] at h1
    exact h1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- Its inverse. -/
def fibreZeroHomInv (p : C(E, B)) (γ : C(↑unitInterval, B)) :
    C(↥(p ⁻¹' {γ 0}), fibre (pullbackSnd p γ) 0) where
  toFun e := ⟨⟨(e.1, 0), by
      show p e.1 = γ (0 : ↑unitInterval)
      exact Set.mem_singleton_iff.mp e.2⟩, rfl⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.prodMk continuous_const

theorem fibreZeroHomInv_comp (p : C(E, B)) (γ : C(↑unitInterval, B))
    (x : fibre (pullbackSnd p γ) 0) : fibreZeroHomInv p γ (fibreZeroHom p γ x) = x := by
  refine Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  show (0 : ↑unitInterval) = x.1.1.2
  exact x.2.symm

theorem fibreZeroHom_comp_inv (p : C(E, B)) (γ : C(↑unitInterval, B))
    (e : ↥(p ⁻¹' {γ 0})) : fibreZeroHom p γ (fibreZeroHomInv p γ e) = e := by
  refine Subtype.ext rfl

/-- The fibre of the pullback over `1` is canonically the preimage of `{γ 1}`. -/
def fibreOneHom (p : C(E, B)) (γ : C(↑unitInterval, B)) :
    C(fibre (pullbackSnd p γ) 1, ↥(p ⁻¹' {γ 1})) where
  toFun := fun y => ⟨y.1.1.1, by
    have h1 : p y.1.1.1 = γ y.1.1.2 := y.1.2
    have h2 : y.1.1.2 = (1 : ↑unitInterval) := y.2
    rw [h2] at h1
    exact h1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- Its inverse. -/
def fibreOneHomInv (p : C(E, B)) (γ : C(↑unitInterval, B)) :
    C(↥(p ⁻¹' {γ 1}), fibre (pullbackSnd p γ) 1) where
  toFun e := ⟨⟨(e.1, 1), by
      show p e.1 = γ (1 : ↑unitInterval)
      exact Set.mem_singleton_iff.mp e.2⟩, rfl⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.prodMk continuous_const

theorem fibreOneHomInv_comp (p : C(E, B)) (γ : C(↑unitInterval, B))
    (x : fibre (pullbackSnd p γ) 1) : fibreOneHomInv p γ (fibreOneHom p γ x) = x := by
  refine Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
  show (1 : ↑unitInterval) = x.1.1.2
  exact x.2.symm

theorem fibreOneHom_comp_inv (p : C(E, B)) (γ : C(↑unitInterval, B))
    (e : ↥(p ⁻¹' {γ 1})) : fibreOneHom p γ (fibreOneHomInv p γ e) = e := by
  refine Subtype.ext rfl

end Hom

/-! ## The induced isomorphism on homology -/

section Homology

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The trivialization at `1` exhibits the fibre inclusion as a homotopy equivalence. -/
theorem isIso_homologyMap_po (p : C(E, B)) (hp : IsHurewiczFibration p)
    (γ : C(↑unitInterval, B)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (Pullback p γ))
      (TopCat.of (fibre (pullbackSnd p γ) 1)) (TopCat.ofHom (poG p hp γ))) j) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of (Pullback p γ)) (TopCat.of (fibre (pullbackSnd p γ) 1))
    (TopCat.ofHom (poG p hp γ)) (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 1))
    (topCatHomotopyOf (poH p hp γ) (fun x => poH_zero p hp γ x)
      (fun x => poH_one p hp γ x))
    (topCatHomotopyOf (poHfib p hp γ) (fun x => poHfib_zero p hp γ x)
      (fun x => poHfib_one p hp γ x)) j

/-- The trivialization at `0` exhibits the fibre inclusion as a homotopy equivalence. -/
theorem isIso_homologyMap_pz (p : C(E, B)) (hp : IsHurewiczFibration p)
    (γ : C(↑unitInterval, B)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (fibre (pullbackSnd p γ) 0)) (TopCat.of (Pullback p γ))
      (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0))) j) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of (fibre (pullbackSnd p γ) 0))
    (TopCat.of (Pullback p γ)) (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0))
    (TopCat.ofHom (pzG p hp γ))
    (topCatHomotopyOf (pzHfib p hp γ) (fun x => pzHfib_zero p hp γ x)
      (fun x => pzHfib_one p hp γ x))
    (topCatHomotopyOf (pzH p hp γ) (fun x => pzH_zero p hp γ x)
      (fun x => pzH_one p hp γ x)) j

/-- Two mutually inverse continuous maps induce an isomorphism on singular homology. -/
theorem isIso_homologyMap_of_comp_eq {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (h1 : ∀ x, g (f x) = x) (h2 : ∀ y, f (g y) = y) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f)) j) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) (TopCat.ofHom g)
    (topCatHomotopyOf (⟨fun z : X × ↑unitInterval => z.1, continuous_fst⟩ : C(X × ↑unitInterval, X))
      (fun x => rfl) (fun x => (h1 x).symm))
    (topCatHomotopyOf (⟨fun z : Y × ↑unitInterval => z.1, continuous_fst⟩ : C(Y × ↑unitInterval, Y))
      (fun y => rfl) (fun y => (h2 y).symm)) j

/-- **The fibre homology of a Hurewicz fibration does not depend on the base point along a path.** -/
theorem nonempty_homology_fibre_iso (p : C(E, B)) (hp : IsHurewiczFibration p)
    (γ : C(↑unitInterval, B)) (j : ℕ) :
    Nonempty (HomologicalComplex.homology (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(p ⁻¹' {γ 0}))) j ≅
      HomologicalComplex.homology (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(p ⁻¹' {γ 1}))) j) := by
  haveI h1 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 0})) (TopCat.of (fibre (pullbackSnd p γ) 0))
      (TopCat.ofHom (fibreZeroHomInv p γ))) j) :=
    isIso_homologyMap_of_comp_eq (fibreZeroHomInv p γ) (fibreZeroHom p γ)
      (fun x => fibreZeroHom_comp_inv p γ x) (fun y => fibreZeroHomInv_comp p γ y) j
  haveI h2 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (fibre (pullbackSnd p γ) 0)) (TopCat.of (Pullback p γ))
      (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0))) j) :=
    isIso_homologyMap_pz p hp γ j
  haveI h3 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (Pullback p γ)) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (poG p hp γ))) j) :=
    isIso_homologyMap_po p hp γ j
  haveI h4 : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 1})) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (fibreOneHomInv p γ))) j) :=
    isIso_homologyMap_of_comp_eq (fibreOneHomInv p γ) (fibreOneHom p γ)
      (fun x => fibreOneHom_comp_inv p γ x) (fun y => fibreOneHomInv_comp p γ y) j
  exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 0})) (TopCat.of (fibre (pullbackSnd p γ) 0))
      (TopCat.ofHom (fibreZeroHomInv p γ))) j) ≪≫
    asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (fibre (pullbackSnd p γ) 0)) (TopCat.of (Pullback p γ))
      (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0))) j) ≪≫
    asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of (Pullback p γ)) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (poG p hp γ))) j) ≪≫
    (asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 1})) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (fibreOneHomInv p γ))) j)).symm⟩

/-- The vanishing of the fibre homology at one end of a path is equivalent to the vanishing at the
other end. -/
theorem isZero_homology_fibre_of_path (p : C(E, B)) (hp : IsHurewiczFibration p)
    (γ : C(↑unitInterval, B)) (j : ℕ) :
    IsZero (HomologicalComplex.homology (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(p ⁻¹' {γ 0}))) j) ↔
      IsZero (HomologicalComplex.homology (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(p ⁻¹' {γ 1}))) j) :=
  Nonempty.casesOn (nonempty_homology_fibre_iso p hp γ j) fun e =>
    ⟨fun h => IsZero.of_iso h e.symm, fun h => IsZero.of_iso h e⟩

/-- The degree-`0` homology of the two end fibres are linearly equivalent over `ℤ` as soon as one of
them is. -/
theorem nonempty_homologyZero_fibre_linEquiv (p : C(E, B)) (hp : IsHurewiczFibration p)
    (γ : C(↑unitInterval, B)) :
    Nonempty (↥(HomologicalComplex.homology (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(p ⁻¹' {γ 0}))) 0) ≃ₗ[ℤ] ℤ) →
      Nonempty (↥(HomologicalComplex.homology (Work.Cohomology.singularChains ℤ
        (TopCat.of ↥(p ⁻¹' {γ 1}))) 0) ≃ₗ[ℤ] ℤ) := by
  intro h
  obtain ⟨e⟩ := nonempty_homology_fibre_iso p hp γ 0
  obtain ⟨e0⟩ := h
  exact ⟨Work.Cohomology.uctIsoToLinearEquiv e.symm ≪≫ₗ e0⟩

end Homology

end

end Work.StemsB
