/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The bridge from node N5 (the analytic envelope) to node N7 (the Linnell datum)

This file, and the rest of `Submission/Work/ORBridgeLinnell/`, closes interface mismatch **(M1)**
of `Submission/Work/ORAssembly/README.md`: the construction of a
`Work.ORLinnell.LinnellDatum K G U` — the structure consumed by node N7 — from

* node N5's analytic envelope `Work.ORVonNeumann.StarRegularEnvelope G` (the algebra `U(G)` of
  operators affiliated to the group von Neumann algebra `N(G)`, over `ℂ`, for a countable group
  `G`), and
* an embedding `K →+* ℂ` of the coefficient field (`K = ℚ` for the group half of the assembly, or
  a finitely generated subfield of an arbitrary field of characteristic zero, see
  `Submission.Work.ORReductions.Field`).

## The mathematical content

For `G` countable, `U := U(G) = E.U` and `H ≤ G`:

* `gen : G →* Uˣ` is the image of the group basis (`g ↦ ι_G(g)`, a unit of `U(G)`);
* `D H` is the **division closure** `D_{K[H]}(U(G))` of `K[H]` inside `U(G)`, i.e.
  `divisionClosureOf` of the image of the `K`-algebra homomorphism `K[H] → U(G)`;
* Linnell independence **(I1)/(I1′)** is deduced from the envelope's cosetwise independence
  `EnvelopeInclusion.linnell` (a theorem of node N5 for the concrete model), the identification
  `D H ≤ (E.sub H).φ.range` following from the *division closedness* of `U(H) ⊆ U(G)`: `U(H)` is
  von Neumann regular and directly finite (the latter from the faithful Sylvester rank function
  `EnvelopeInclusion.rkV_faithful`), so a right inverse in `U(G)` of an element of `U(H)` already
  lies in `U(H)` — see `Work.ORBridgeLinnell.isDivisionClosed_range`;
* **(I2)** (conjugation) and the minimality of `D H` are formal consequences of the definition of
  the division closure;
* **(I4)**, **(I4′)** are *not* consequences of the N5 interface: they are the Hughes-free /
  Atiyah statement of node N6 (and Linnell's Ore field of fractions lemma), and are therefore
  recorded as the explicit hypothesis structure `HughesFreeInput` (see `Defs.lean`).

## Main results of this file

* `Work.ORBridgeLinnell.gen`, `...genU`, `...gen_injective`, `...gen_inv_apply`;
* `Work.ORBridgeLinnell.toUK`, `...D`, `...toUK_mem_D`, `...gen_mem_D`, `...algebraMap_mem_D`,
  `...isDivisionClosed_D`, `...D_minimal`, `...mem_D_iff`, `...D_mono`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.CountableEnvelope
import Submission.Work.ORLinnell.Main

set_option autoImplicit false

namespace Work.ORBridgeLinnell

open Work.ORVonNeumann

variable {G : Type*} [Group G]

/-! ## The group basis of the envelope -/

/-- The image of the group basis of `ℂ[G]` in `U(G)`, as a monoid homomorphism into `U(G)`. -/
noncomputable def genU (E : StarRegularEnvelope G) : G →* E.U where
  toFun g := E.ι (MonoidAlgebra.single g 1)
  map_one' := by rw [← MonoidAlgebra.one_def, map_one]
  map_mul' g g' := by rw [← map_mul, MonoidAlgebra.single_mul_single, mul_one]

@[simp]
theorem genU_apply (E : StarRegularEnvelope G) (g : G) :
    genU E g = E.ι (MonoidAlgebra.single g 1) := rfl

/-- The image of the group basis of `ℂ[G]` in the units of `U(G)`: every `g` is a unit of `ℂ[G]`,
hence its image is a unit of `U(G)`. -/
noncomputable def gen (E : StarRegularEnvelope G) : G →* E.Uˣ := MonoidHom.toHomUnits (genU E)

@[simp]
theorem gen_apply (E : StarRegularEnvelope G) (g : G) :
    ((gen E g : E.Uˣ) : E.U) = E.ι (MonoidAlgebra.single g 1) := by
  rw [gen, MonoidHom.coe_toHomUnits, genU_apply]

@[simp]
theorem gen_inv_apply (E : StarRegularEnvelope G) (g : G) :
    (((gen E g)⁻¹ : E.Uˣ) : E.U) = E.ι (MonoidAlgebra.single g⁻¹ 1) := by
  rw [← MonoidHom.map_inv (gen E) g]
  exact gen_apply E g⁻¹

/-- The group basis of `U(G)` is injective: `ι_G` is injective on the group algebra. -/
theorem gen_injective (E : StarRegularEnvelope G) : Function.Injective (gen E) := by
  intro g g' h
  have h1 : E.ι (MonoidAlgebra.single g 1) = E.ι (MonoidAlgebra.single g' 1) := by
    rw [← gen_apply E g, ← gen_apply E g', h]
  exact MonoidAlgebra.single_left_injective (R := ℂ) one_ne_zero (E.ι_injective h1)

/-- The image of a group element under `ι_G` is the value of `gen` — the form in which the
envelope's `LinnellIndependent` (stated with `MonoidAlgebra.single q 1`) is used below. -/
theorem iota_single_eq_gen (E : StarRegularEnvelope G) (g : G) :
    E.ι (MonoidAlgebra.single g 1) = (gen E g : E.U) := (gen_apply E g).symm

/-- `(gen g)⁻¹ = gen g⁻¹`. -/
theorem gen_inv_eq (E : StarRegularEnvelope G) (g : G) :
    (gen E g)⁻¹ = gen E g⁻¹ := (map_inv (gen E) g).symm

/-! ## The division closure `D H` inside `U(G)` -/

variable {K : Type*} [Field K]

/-- The `K`-algebra homomorphism `K[H] → U(G)` obtained by restricting the structure map
`ℂ[G] → U(G)` along the embedding `K ↪ ℂ` and the inclusion `H ≤ G`.  The embedding `K →+* ℂ` is
only used to record the coefficient field; the map itself is the composite of the `K`-algebra
structure of `U(G)` with the image of the group basis. -/
noncomputable def toUK (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) : MonoidAlgebra K ↥H →ₐ[K] E.U :=
  MonoidAlgebra.lift K E.U ↥H ((genU E).comp (Subgroup.subtype H))

theorem toUK_single (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) (h : ↥H) (k : K) :
    toUK E φK H (MonoidAlgebra.single h k) = k • (genU E (h : G)) :=
  MonoidAlgebra.lift_single ((genU E).comp (Subgroup.subtype H)) h k

theorem toUK_of (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G)
    (h : ↥H) : toUK E φK H (MonoidAlgebra.of K ↥H h) = (genU E (h : G)) :=
  MonoidAlgebra.lift_of ((genU E).comp (Subgroup.subtype H)) h

/-- **The division closure of `K[H]` inside `U(G)`**: this is the `D H` of the Linnell datum, i.e.
`D_{K[H]}(U(G))` in the notation of Jaikin-Zapirain--Linton. -/
noncomputable def D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) : Subring E.U :=
  divisionClosureOf (Set.range (toUK E φK H))

theorem toUK_mem_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G)
    (x : MonoidAlgebra K ↥H) : toUK E φK H x ∈ D E φK H :=
  le_divisionClosure _ (Subring.subset_closure ⟨x, rfl⟩)

theorem toUK_range_le_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) : Set.range (toUK E φK H) ⊆ (D E φK H : Set E.U) :=
  fun _ hx => by obtain ⟨x, rfl⟩ := hx; exact toUK_mem_D E φK H x

theorem mem_D_iff (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] {H : Subgroup G}
    {x : E.U} :
    x ∈ D E φK H ↔ ∀ A : Subring E.U, Set.range (toUK E φK H) ⊆ (A : Set E.U) →
      IsDivisionClosed A → x ∈ A := by
  rw [D, divisionClosureOf, mem_divisionClosure_iff]
  constructor
  · intro h A hA hA'
    exact h A (Subring.closure_le.mpr hA) hA'
  · intro h A hRA hA
    exact h A (fun y hy => hRA (Subring.subset_closure hy)) hA

theorem isDivisionClosed_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) : IsDivisionClosed (D E φK H) :=
  isDivisionClosed_divisionClosure _

theorem D_le_iff (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] {H : Subgroup G}
    {A : Subring E.U} (hA : IsDivisionClosed A) :
    D E φK H ≤ A ↔ Set.range (toUK E φK H) ⊆ (A : Set E.U) :=
  ⟨fun h _ hy => h (toUK_range_le_D E φK H hy),
    fun h => (divisionClosureOf_le_iff hA).mpr h⟩

theorem D_minimal (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] {H : Subgroup G}
    {A : Subring E.U} (h : Set.range (toUK E φK H) ⊆ (A : Set E.U)) (hA : IsDivisionClosed A) :
    D E φK H ≤ A :=
  (D_le_iff E φK hA).mpr h

theorem gen_mem_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G)
    (h : ↥H) : (gen E (h : G) : E.U) ∈ D E φK H := by
  have h1 : toUK E φK H (MonoidAlgebra.of K ↥H h) = (gen E (h : G) : E.U) := by
    rw [toUK_of, genU_apply, gen_apply]
  rw [← h1]
  exact toUK_mem_D E φK H _

theorem gen_mem_D' (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] {H : Subgroup G}
    {g : G} (hg : g ∈ H) : (gen E g : E.U) ∈ D E φK H :=
  gen_mem_D E φK H ⟨g, hg⟩

theorem algebraMap_mem_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U]
    (H : Subgroup G) (k : K) : algebraMap K E.U k ∈ D E φK H := by
  have h1 : toUK E φK H (MonoidAlgebra.single (1 : ↥H) k) = algebraMap K E.U k := by
    rw [toUK_single, Subgroup.coe_one, map_one (genU E), Algebra.smul_def, mul_one]
  rw [← h1]
  exact toUK_mem_D E φK H _

/-- `D` is monotone in the subgroup. -/
theorem D_mono (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] {H₁ H₂ : Subgroup G}
    (h : H₁ ≤ H₂) : D E φK H₁ ≤ D E φK H₂ := by
  refine D_minimal E φK ?_ (isDivisionClosed_D E φK H₂)
  rintro _ ⟨y, rfl⟩
  have key : ∀ z : MonoidAlgebra K ↥H₁, toUK E φK H₁ z ∈ D E φK H₂ := by
    intro z
    induction z using MonoidAlgebra.induction_on with
    | of m =>
      have h2 : toUK E φK H₁ (MonoidAlgebra.of K ↥H₁ m) = toUK E φK H₂
          (MonoidAlgebra.of K ↥H₂ (Subgroup.inclusion h m)) := by
        rw [toUK_of, toUK_of]
        rfl
      rw [h2]
      exact toUK_mem_D E φK H₂ _
    | add x y hx hy =>
      rw [map_add]
      exact (D E φK H₂).add_mem hx hy
    | smul r x hx =>
      rw [map_smul, Algebra.smul_def]
      exact (D E φK H₂).mul_mem (algebraMap_mem_D E φK H₂ r) hx
  exact key y

/-- The `K`-scalars of `U(G)` lie in every `D H`. -/
theorem toUK_le_D (E : StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G) :
    Set.range (toUK E φK H) ⊆ (D E φK H : Set E.U) := toUK_range_le_D E φK H

end Work.ORBridgeLinnell
