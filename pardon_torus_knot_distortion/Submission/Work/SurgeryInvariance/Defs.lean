import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# The vocabulary of surgery invariance for a family of spheres

Pardon's Lemma (`spherefamily`, p. 3 of *On the distortion of knots on embedded surfaces*)
propagates the property

> `F ∩ int(S_t)` contains a loop which is essential in `F`

along a one-parameter family `{S_t}` of embedded spheres in `ℝ³` which are transverse to the
torus `F` except at finitely many parameters, where a single `2`-surgery occurs.  The sibling
subproject `Work.CoreTopology` formalised the *numerical* core of that argument
(`Work.CoreTopology.sphere_family`, `Work.CoreTopology.double_bubble`) but left three
geometric/topological inputs as explicit hypotheses: the dichotomy `W t ∈ {⊥, ⊤}`, the local
`1`-Lipschitz bound on the dimension, and the identification
`HasEssentialLoop ↔ ContainsEssentialLoop`.

This file sets up the vocabulary in which the invariance is *proved* directly, without the
dichotomy: instead of the homology of subsurfaces we use the **winding span**

  `WindingSpan P X =` the `ℚ`-span in `ℚ² = H₁(T²; ℚ)` of the winding vectors of the closed
  curves of `F = P.carrier` whose image lies in `X ⊆ ℝ³`.

* `WindingSpan P X = ⊥` says exactly that `X` contains **no** essential loop, i.e. that every
  closed curve of the torus inside `X` is null-homotopic in the torus
  (`WindingSpan_eq_bot_iff`); so the winding span carries the same information as Pardon's
  `F ∩ X ↦ im(H₁(F ∩ X; ℚ) → H₁(F; ℚ))` as far as the *vanishing* is concerned.
* `SurgeryStep P A A'` is the local model of a single `2`-surgery of the sphere family: the
  region `A = F ∩ int(S_t)` changes by adding or removing an *embedded disc* of `F`, and no
  loop of `A` crosses the boundary curve of that disc.  It is the only geometric input of the
  invariance theorem.
* `Sweep P` bundles a family of regions together with a finite set of exceptional parameters:
  away from them the region is moved by an ambient isotopy of `ℝ³` preserving `F`
  (`RegionIsotopic`), at them a single `2`-surgery takes place (`SurgeryStep`).
* `Sweep.windingSpan_eq` / `Sweep.containsEssentialLoop_iff` / `Sweep.spherefamily` prove that
  the invariant is *constant* along the whole family, and hence Pardon's lemma, with no
  dichotomy and no Lipschitz hypothesis.

Everything here is stated for an arbitrary `ParamTorus P`; specialising to
`P = Work.CoreTopology.standard` recovers Pardon's setting.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.SurgeryInvariance

noncomputable section

/-- **The winding vector of a closed curve of a parametrised torus.**  Any closed curve admits
a lift to the parameter plane (`Work.TorusCover.ParamTorus_exists_liftOf`), and the winding
vector (the pair of integer multiples of `2π` by which the two parameters advance over one
period) does not depend on the choice of lift (`Work.CoreTopology.LiftOf.winding_eq`). -/
def windingOf (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) : ℤ × ℤ :=
  (Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ)).winding

/-- The winding vector computed from any lift. -/
theorem windingOf_eq (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) (L : Work.CoreTopology.LiftOf P γ) :
    windingOf P γ = L.winding :=
  L.winding_eq (Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ))

/-- A closed curve of a parametrised torus is essential exactly when its winding vector is
nonzero. -/
theorem isEssential_iff_windingOf_ne_zero (P : Work.CoreTopology.ParamTorus)
    (γ : Work.CoreTopology.ClosedCurve P) :
    Work.CoreTopology.IsEssential P γ ↔ windingOf P γ ≠ (0, 0) := by
  constructor
  · rintro ⟨L, hL⟩ h
    exact hL ((windingOf_eq P γ L).symm.trans h)
  · intro h
    exact ⟨Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ),
      fun hc => h ((windingOf_eq P γ _).trans hc)⟩

/-- The set of winding vectors of the closed curves of the torus contained in `X`, pushed into
`ℚ²`. -/
def windingVectors (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Set (ℚ × ℚ) :=
  {v | ∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) ∧
    ((((windingOf P γ).1 : ℤ) : ℚ), (((windingOf P γ).2 : ℤ) : ℚ)) = v}

/-- **The winding span of a region `X`**: the `ℚ`-subspace of `ℚ² = H₁(T²; ℚ)` spanned by the
winding vectors of all closed curves of the torus `F = P.carrier` whose image lies in `X`.

This is the curve-level replacement for Pardon's `im(H₁(F ∩ X; ℚ) → H₁(F; ℚ))`: it vanishes
exactly when `X` contains no essential loop. -/
def WindingSpan (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Submodule ℚ (ℚ × ℚ) :=
  Submodule.span ℚ (windingVectors P X)

/-- The winding span of a subregion is contained in that of a larger region. -/
theorem WindingSpan_mono (P : Work.CoreTopology.ParamTorus) {X Y : Set R3} (h : X ⊆ Y) :
    WindingSpan P X ≤ WindingSpan P Y :=
  Submodule.span_mono (by rintro v ⟨γ, hγ, rfl⟩; exact ⟨γ, fun t => h (hγ t), rfl⟩)

/-- A pair of integer windings has zero image in `ℚ²` only if it is zero. -/
theorem intPair_cast_eq_zero_iff (v : ℤ × ℤ) :
    ((((v.1 : ℤ) : ℚ), (((v.2 : ℤ) : ℚ))) = 0) ↔ v = 0 := by
  constructor
  · intro h
    have h1 : (v.1 : ℚ) = 0 := congrArg Prod.fst h
    have h2 : (v.2 : ℚ) = 0 := congrArg Prod.snd h
    have h1' : v.1 = 0 := by exact_mod_cast h1
    have h2' : v.2 = 0 := by exact_mod_cast h2
    exact Prod.ext h1' h2'
  · rintro rfl; simp

/-- **`WindingSpan P X = ⊥` iff `X` contains no essential loop of the torus.**  This is the
curve-level form of "the image of `H₁(F ∩ X; ℚ)` in `H₁(F; ℚ)` is zero". -/
theorem WindingSpan_eq_bot_iff (P : Work.CoreTopology.ParamTorus) (X : Set R3) :
    WindingSpan P X = ⊥ ↔ ¬ P.ContainsEssentialLoop X := by
  rw [WindingSpan, Submodule.span_eq_bot]
  constructor
  · intro h hcon
    obtain ⟨γ, hess, hγ⟩ := hcon
    have hw : windingOf P γ ≠ (0, 0) := (isEssential_iff_windingOf_ne_zero P γ).mp hess
    exact hw (intPair_cast_eq_zero_iff (windingOf P γ) |>.mp
      (h _ ⟨γ, hγ, rfl⟩))
  · intro h v ⟨γ, hγ, hv⟩
    have hzero : windingOf P γ = 0 := by
      by_contra hw
      exact h ⟨γ, (isEssential_iff_windingOf_ne_zero P γ).mpr hw, hγ⟩
    rw [← hv, hzero]
    simp

/-- The winding span of a region is nonzero exactly when the region contains an essential
loop. -/
theorem windingSpan_ne_bot_iff (P : Work.CoreTopology.ParamTorus) (X : Set R3) :
    WindingSpan P X ≠ ⊥ ↔ P.ContainsEssentialLoop X := by
  rw [ne_eq, WindingSpan_eq_bot_iff, not_not]

/-- `X` is open in the surface `F = P.carrier` (for the subspace topology). -/
def IsOpenInCarrier (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Prop :=
  IsOpen (Subtype.val ⁻¹' X : Set P.carrier)

theorem isOpenInCarrier_univ (P : Work.CoreTopology.ParamTorus) :
    IsOpenInCarrier P Set.univ := isOpen_univ

theorem isOpenInCarrier_inter (P : Work.CoreTopology.ParamTorus) {X Y : Set R3}
    (hX : IsOpenInCarrier P X) (hY : IsOpenInCarrier P Y) :
    IsOpenInCarrier P (X ∩ Y) := hX.inter hY

theorem isOpenInCarrier_union (P : Work.CoreTopology.ParamTorus) {X Y : Set R3}
    (hX : IsOpenInCarrier P X) (hY : IsOpenInCarrier P Y) :
    IsOpenInCarrier P (X ∪ Y) := hX.union hY

/-- **An embedded disc of the surface `F`**: the image of an injective continuous map of the
closed unit disc of `ℂ` into `F`.  This is the shape in which the local model of a `2`-surgery
of the sphere family appears: the change of `F ∩ int(S_t)` is by the interior of such a disc.

The field `open_interior` records that the interior of an embedded disc is open in the surface;
this is the local flatness of `F` at a point of the disc (equivalently, the existence of a
tubular neighbourhood of the disc), which is a fact of the smooth/topological theory of
surfaces that we take as data rather than prove. -/
structure DiscRegion (P : Work.CoreTopology.ParamTorus) where
  /-- the parametrisation of the disc -/
  e : C(Metric.closedBall (0 : ℂ) 1, R3)
  /-- the disc is embedded -/
  inj : Function.Injective e
  /-- the disc lies on the surface -/
  mem : ∀ z : Metric.closedBall (0 : ℂ) 1, e z ∈ P.carrier
  /-- the interior of the disc is open in the surface -/
  open_interior : IsOpenInCarrier P
    (e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1})

namespace DiscRegion

variable {P : Work.CoreTopology.ParamTorus}

/-- The closed disc, as a subset of `ℝ³`. -/
def carrier (D : DiscRegion P) : Set R3 := Set.range D.e

/-- The interior of the disc, as a subset of `ℝ³`. -/
def interior (D : DiscRegion P) : Set R3 :=
  D.e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}

/-- The boundary circle of the disc, as a subset of `ℝ³`. -/
def boundary (D : DiscRegion P) : Set R3 :=
  D.e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1}

theorem interior_def (D : DiscRegion P) :
    D.interior = D.e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} := rfl

theorem carrier_def (D : DiscRegion P) : D.carrier = Set.range D.e := rfl

theorem boundary_def (D : DiscRegion P) :
    D.boundary = D.e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} := rfl

theorem open_interior' (D : DiscRegion P) : IsOpenInCarrier P D.interior := D.open_interior

theorem interior_subset_carrier (D : DiscRegion P) : D.interior ⊆ D.carrier := by
  rintro _ ⟨z, -, rfl⟩
  exact ⟨z, rfl⟩

theorem boundary_subset_carrier (D : DiscRegion P) : D.boundary ⊆ D.carrier := by
  rintro _ ⟨z, -, rfl⟩
  exact ⟨z, rfl⟩

theorem carrier_subset_surface (D : DiscRegion P) : D.carrier ⊆ P.carrier := by
  rintro _ ⟨z, rfl⟩
  exact D.mem z

theorem interior_subset_surface (D : DiscRegion P) : D.interior ⊆ P.carrier :=
  fun _ h => D.carrier_subset_surface (D.interior_subset_carrier h)

theorem mem_carrier_iff (D : DiscRegion P) (x : R3) :
    x ∈ D.carrier ↔ ∃ z : Metric.closedBall (0 : ℂ) 1, D.e z = x := Iff.rfl

end DiscRegion

/-- **No loop of `A` crosses the boundary of the disc `D`**: every closed curve of the torus
contained in `A` is contained either in `A'` or in the closed disc `D`.

This is the curve-level form of the local model of a `2`-surgery, where the region
`A = F ∩ int(S)` changes by adding or removing the interior of a small disc `D` and the
boundary curve of `D` is part of the sphere (hence not part of either region). -/
def SplitsBy (P : Work.CoreTopology.ParamTorus) (A A' : Set R3) (D : DiscRegion P) : Prop :=
  ∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ A) →
    (∀ t : ℝ, γ t ∈ A') ∨ (∀ t : ℝ, γ t ∈ D.carrier)

/-- **The geometric shape of a single `2`-surgery of the sphere family.**  The two regions
differ by exactly the interior of an embedded disc `D` of `F`, both being open in the surface and
the two pieces disjoint.

Geometrically this is what happens at an exceptional parameter of the sweep: around the critical
point of the saddle, `int(S_t)` gains or loses the part of a small ball, whose intersection with
the surface `F` is an embedded disc, and the newly created (or destroyed) curve of `S_t ∩ F` —
the boundary of that disc — is not part of either region. -/
def SurgeryShape (P : Work.CoreTopology.ParamTorus) (A A' : Set R3) : Prop :=
  ∃ D : DiscRegion P, IsOpenInCarrier P A ∧ IsOpenInCarrier P A' ∧
    ((A = A' ∪ D.interior ∧ Disjoint A' D.interior) ∨
      (A' = A ∪ D.interior ∧ Disjoint A D.interior))

/-- **The local model of a single `2`-surgery of the sphere family.**

`SurgeryStep P A A'` says that the region `A = F ∩ int(S_t)` is turned into `A' = F ∩ int(S_u)`
by a single `2`-surgery: there is an embedded disc `D` of `F` such that `A` and `A'` differ
only by the interior of `D`, and no loop of either region crosses the boundary curve of `D`.

Geometrically this is exactly what happens at an exceptional parameter of the sweep: around
the critical point of the saddle, the region `int(S_t)` gains or loses the part of a small ball,
whose intersection with the surface `F` is an embedded disc, and the newly created (or
destroyed) curve of `S_t ∩ F` — the boundary of that disc — is not part of either region. -/
def SurgeryStep (P : Work.CoreTopology.ParamTorus) (A A' : Set R3) : Prop :=
  ∃ D : DiscRegion P, SplitsBy P A A' D ∧ SplitsBy P A' A D ∧
    (A \ A') ∪ (A' \ A) ⊆ D.carrier

/-- The geometric shape of a single `2`-surgery, without the openness certificates on the two
regions: if a region is obtained from another by adding or removing the interior of an embedded
disc, the two pieces being disjoint.  This is the form in which the local model of the saddle is
stated for a *family of spheres* (`SphereSweep`), where the regions are traces `F ∩ int(S_t)` of
open sets and their openness in `F` is automatic
(`Work.SurgeryInvariance.isOpenInCarrier_carrier_inter`). -/
def SurgeryShapeRaw (P : Work.CoreTopology.ParamTorus) (A A' : Set R3) : Prop :=
  ∃ D : DiscRegion P, ((A = A' ∪ D.interior ∧ Disjoint A' D.interior) ∨
    (A' = A ∪ D.interior ∧ Disjoint A D.interior))

/-- **A single `2`-surgery in the "zero winding content" form.**  The region changes by adding or
removing an open piece `Z` whose winding span vanishes, the two pieces being disjoint.

This is the purely curve-level form of the local model of a `2`-surgery: at a saddle the region
`int(S_t)` gains or loses the part of a small ball; that part is an embedded disc of `F` (so
`Z = D.interior` for a `DiscRegion D`, see `SurgeryShape.toZero`), but any piece of zero winding
span will do — for instance a piece through which Pardon's hypothesis "every curve of `S_t ∩ F` is
inessential" is known by `Work.CoreTopology.mustbeinessential`
(`Work.SurgeryInvariance.MustBeInessential.windingSpan_eq_bot`). -/
def SurgeryStepZero (P : Work.CoreTopology.ParamTorus) (A A' : Set R3) : Prop :=
  ∃ Z : Set R3, WindingSpan P Z = ⊥ ∧ IsOpenInCarrier P A ∧ IsOpenInCarrier P A' ∧
    IsOpenInCarrier P Z ∧
    ((A = A' ∪ Z ∧ Disjoint A' Z) ∨ (A' = A ∪ Z ∧ Disjoint A Z))

/-- **An ambient isotopy of `ℝ³` carrying `F` to itself, taking the region `X` to the region
`Y`.**  `h` is a homeomorphism of `ℝ³` preserving the surface `F = P.carrier`, mapping `X` onto
`Y`, which is homotopic to the identity through maps preserving `F`, both `h` and `h⁻¹`.

This is the translation into the region vocabulary of "the sphere family varies without
surgery": between two exceptional parameters the sphere `S_t` is moved by an ambient isotopy of
`ℝ³` (isotopy extension), hence so is the region `F ∩ int(S_t)` and every loop it contains. -/
def RegionIsotopic (P : Work.CoreTopology.ParamTorus) (X Y : Set R3) : Prop :=
  ∃ h : R3 ≃ₜ R3,
    (∀ x : R3, x ∈ P.carrier → h x ∈ P.carrier) ∧
    (∀ y : R3, y ∈ P.carrier → h.symm y ∈ P.carrier) ∧
    h '' X = Y ∧
    (∃ H : ℝ → R3 → R3, Continuous (Function.uncurry H) ∧ (∀ x : R3, H 0 x = x) ∧
      (∀ x : R3, H 1 x = h x) ∧ ∀ u : ℝ, ∀ x : R3, x ∈ P.carrier → H u x ∈ P.carrier) ∧
    (∃ K : ℝ → R3 → R3, Continuous (Function.uncurry K) ∧ (∀ x : R3, K 0 x = x) ∧
      (∀ x : R3, K 1 x = h.symm x) ∧ ∀ u : ℝ, ∀ x : R3, x ∈ P.carrier → K u x ∈ P.carrier)

theorem RegionIsotopic.refl (P : Work.CoreTopology.ParamTorus) (X : Set R3) :
    RegionIsotopic P X X := by
  refine ⟨Homeomorph.refl R3, ?_, ?_, by simp, ?_, ?_⟩
  · intro x _; exact ‹x ∈ P.carrier›
  · intro y _; exact ‹y ∈ P.carrier›
  · exact ⟨fun _ x => x, continuous_snd, fun x => rfl, fun x => rfl, fun _ x hx => hx⟩
  · exact ⟨fun _ x => x, continuous_snd, fun x => rfl, fun x => rfl, fun _ x hx => hx⟩

/-- The curve-level content of a region isotopy: loops are transported to loops with the same
winding vector, in both directions.  This is the shape in which the invariance of the winding
span under a surgery-free variation of the family is used. -/
def RegionEquivalent (P : Work.CoreTopology.ParamTorus) (X Y : Set R3) : Prop :=
  (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ Y) ∧
        windingOf P γ' = windingOf P γ) ∧
  (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ Y) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ X) ∧
        windingOf P γ' = windingOf P γ)

/-- **A one-parameter family of spheres with finitely many `2`-surgeries**, recorded through the
regions `A t = F ∩ int(S_t)` that it cuts out of the torus.

* `exc` is the finite set of exceptional parameters;
* `regular` says that away from the exceptional parameters, nearby regions are related by an
  ambient isotopy of `ℝ³` preserving `F` (no surgery has taken place);
* `surgery` says that at an exceptional parameter, the region is related to the nearby
  regions by a single `2`-surgery, i.e. by adding or removing an embedded disc of `F`
  (`SurgeryShape`), or by an ambient isotopy (on the far side of the critical parameter). -/
structure Sweep (P : Work.CoreTopology.ParamTorus) where
  /-- the region `F ∩ int(S_t)` -/
  region : ℝ → Set R3
  /-- the exceptional (surgery) parameters -/
  exc : Finset ℝ
  /-- away from the exceptional parameters the region moves by an ambient isotopy -/
  regular : ∀ t : ℝ, t ∉ exc → ∃ ε : ℝ, 0 < ε ∧ (∀ s : ℝ, |s - t| < ε → s ∉ exc) ∧
    ∀ s : ℝ, |s - t| < ε → RegionIsotopic P (region t) (region s)
  /-- at an exceptional parameter the region either changes by a single `2`-surgery or is moved
  by an ambient isotopy (the latter happens on the far side of the critical parameter) -/
  surgery : ∀ t : ℝ, t ∈ exc → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
    SurgeryShape P (region t) (region s) ∨ RegionIsotopic P (region t) (region s)

end

end Work.SurgeryInvariance
