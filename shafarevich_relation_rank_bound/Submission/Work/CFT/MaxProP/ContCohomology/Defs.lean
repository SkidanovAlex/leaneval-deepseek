import Mathlib
import Submission.Work.CFT.KochTransfer.Defs
import Submission.Work.Tower.Shafarevich.Defs

/-!
# Continuous cohomology of a profinite group with trivial `𝔽_p` coefficients

Mathlib's `groupCohomology` is the **abstract** group cohomology of a group.  For an *infinite*
pro-`p` group `G` it is the wrong invariant: `H²(G, 𝔽_p)` is typically infinite-dimensional, so
`Module.finrank` is `0` and statements such as Shafarevich's estimate or Koch's transfer are
*false* for it.  The correct invariant is the **continuous** cohomology

`Hⁿ_cont(G, 𝔽_p) := colim_U Hⁿ(G ⧸ U, 𝔽_p)`,

the filtered colimit over the *open normal* subgroups `U ◁ G`.

This file defines `H1FpCont` (degree one) and `H2FpCont` (degree two).

## Main definitions

* `Work.CFT.MaxProP.OpenNormal G` — the open normal subgroups of a topological group, ordered by
  reverse inclusion.
* `Work.CFT.MaxProP.H1FpCont p G` — `H¹_cont(G, 𝔽_p) = Hom_cts(G, 𝔽_p)`.
* `Work.CFT.MaxProP.H2FpCont p G` — `H²_cont(G, 𝔽_p) = colim_U H²(G ⧸ U, 𝔽_p)`.
-/

open NumberField
open scoped Classical nonZeroDivisors

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Work.CFT.MaxProP

/-! ## Degree one: continuous homomorphisms -/

/-- **`H¹_cont(G, 𝔽_p)`**: the group of continuous homomorphisms from the topological group `G`
to the discrete group `𝔽_p = ZMod p`. -/
abbrev H1FpCont (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] : Type :=
  Additive (ContinuousMonoidHom G (Multiplicative (ZMod p)))

instance (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] :
    AddCommGroup (H1FpCont p G) := inferInstanceAs (AddCommGroup (Additive _))

/-- The `𝔽_p`-vector space structure on `H¹_cont(G, 𝔽_p)`. -/
instance (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] :
    Module (ZMod p) (H1FpCont p G) :=
  AddCommGroup.zmodModule (fun x => by
    have hA : ∀ f : ContinuousMonoidHom G (Multiplicative (ZMod p)), f ^ p = 1 := by
      intro f; ext g; simp
    simpa using congrArg Additive.ofMul (hA (Additive.toMul x)))

/-! ## The open normal subgroups -/

/-- The **open normal subgroups** of a topological group `G`, ordered by *reverse* inclusion:
`U ≤ V` iff `V ≤ U` as subgroups. -/
structure OpenNormal (G : Type) [Group G] [TopologicalSpace G] where
  /-- The underlying subgroup. -/
  carrier : Subgroup G
  /-- It is normal. -/
  normal : carrier.Normal
  /-- It is open. -/
  isOpen : IsOpen (carrier : Set G)

namespace OpenNormal

variable {G : Type} [Group G] [TopologicalSpace G]

/-- The underlying subgroup of an open normal subgroup is normal, as an instance. -/
instance (U : OpenNormal G) : U.carrier.Normal := U.normal

instance : Preorder (OpenNormal G) where
  le U V := V.carrier ≤ U.carrier
  lt U V := V.carrier < U.carrier
  le_refl U := _root_.le_refl U.carrier
  le_trans U V W hUV hVW := _root_.le_trans hVW hUV
  lt_iff_le_not_ge U V := by
    show V.carrier < U.carrier ↔ V.carrier ≤ U.carrier ∧ ¬ U.carrier ≤ V.carrier
    exact lt_iff_le_not_ge

instance : Nonempty (OpenNormal G) :=
  ⟨⟨⊤, inferInstance, isOpen_univ⟩⟩

instance : IsDirectedOrder (OpenNormal G) where
  directed U V := by
    haveI : U.carrier.Normal := U.normal
    haveI : V.carrier.Normal := V.normal
    have hO : IsOpen ((U.carrier ⊓ V.carrier : Subgroup G) : Set G) := by
      rw [Subgroup.coe_inf]; exact U.isOpen.inter V.isOpen
    refine ⟨⟨(U.carrier ⊓ V.carrier : Subgroup G), inferInstance, hO⟩, ?_, ?_⟩
    · show (U.carrier ⊓ V.carrier : Subgroup G) ≤ U.carrier
      exact inf_le_left
    · show (U.carrier ⊓ V.carrier : Subgroup G) ≤ V.carrier
      exact inf_le_right

theorem le_def {U V : OpenNormal G} : U ≤ V ↔ V.carrier ≤ U.carrier := Iff.rfl

/-- The natural surjection `G ⧸ V → G ⧸ U` for open normal subgroups `V ≤ U` (i.e. `U ≤ V` in the
reverse-inclusion order). -/
noncomputable def quotientMap (U V : OpenNormal G) (h : U ≤ V) :
    G ⧸ V.carrier →* G ⧸ U.carrier :=
  QuotientGroup.lift V.carrier (QuotientGroup.mk' U.carrier) (by
    rw [QuotientGroup.ker_mk']
    exact h)

theorem quotientMap_surjective (U V : OpenNormal G) (h : U ≤ V) :
    Function.Surjective (quotientMap U V h) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective U.carrier x
  exact ⟨QuotientGroup.mk y, by
    show QuotientGroup.mk' U.carrier y = QuotientGroup.mk y
    rw [QuotientGroup.mk'_apply]⟩

end OpenNormal

/-! ## Degree two: the colimit over the finite quotients -/

/-- The inflation map of the direct system underlying `H2FpCont`: for `U ≤ V` (i.e. `V ≤ U` as
subgroups) it is the inflation `H²(G ⧸ U, 𝔽_p) → H²(G ⧸ V, 𝔽_p)` along the surjection
`G ⧸ V → G ⧸ U`. -/
noncomputable def contMap (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    (U V : OpenNormal G) (h : U ≤ V) :
    (Work.Tower.Shafarevich.H2Fp p (G ⧸ U.carrier) : Type) →ₗ[ZMod p]
      (Work.Tower.Shafarevich.H2Fp p (G ⧸ V.carrier) : Type) :=
  Work.CFT.KochTransfer.infl (OpenNormal.quotientMap U V h)

/-- The family of `𝔽_p`-modules whose colimit is `H²_cont`. -/
noncomputable abbrev H2FpContFamily (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    (U : OpenNormal G) : Type :=
  (Work.Tower.Shafarevich.H2Fp p (G ⧸ U.carrier) : Type)

/-- **`H²_cont(G, 𝔽_p)`**: the filtered colimit of the second cohomology of the finite quotients
`G ⧸ U` over the open normal subgroups `U ◁ G`, along the inflation maps.  This is the correct
replacement for Mathlib's abstract `H2Fp p G`, which is infinite-dimensional for an infinite
pro-`p` group `G`. -/
noncomputable abbrev H2FpCont (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] : Type :=
  letI := Classical.decEq (OpenNormal G)
  Module.DirectLimit (H2FpContFamily p G) (contMap p G)

end Work.CFT.MaxProP

namespace Work.CFT.MaxProP

instance instAddCommGroupH2FpCont (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] :
    AddCommGroup (H2FpCont p G) := inferInstance

instance instModuleH2FpCont (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] :
    Module (ZMod p) (H2FpCont p G) := inferInstance

/-- The canonical map `H²(G ⧸ U, 𝔽_p) → H²_cont(G, 𝔽_p)` from a finite quotient. -/
noncomputable def H2FpCont.of (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    (U : OpenNormal G) : (H2FpContFamily p G U) →ₗ[ZMod p] H2FpCont p G :=
  Module.DirectLimit.of (ZMod p) (OpenNormal G) (H2FpContFamily p G) (contMap p G) U

@[simp] theorem H2FpCont.of_f {p : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    {U V : OpenNormal G} (h : U ≤ V) (x : H2FpContFamily p G U) :
    H2FpCont.of p G V (contMap p G U V h x) = H2FpCont.of p G U x :=
  Module.DirectLimit.of_f

/-- The universal property of `H²_cont`: a compatible family of maps out of the finite quotients
factors uniquely through the colimit. -/
noncomputable def H2FpCont.lift {p : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    {P : Type} [AddCommMonoid P] [Module (ZMod p) P]
    (g : (U : OpenNormal G) → H2FpContFamily p G U →ₗ[ZMod p] P)
    (hg : ∀ (U V : OpenNormal G) (h : U ≤ V) (x : H2FpContFamily p G U),
      g V (contMap p G U V h x) = g U x) :
    H2FpCont p G →ₗ[ZMod p] P :=
  Module.DirectLimit.lift (ZMod p) (OpenNormal G) (H2FpContFamily p G) (contMap p G) g hg

@[simp] theorem H2FpCont.lift_of {p : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    {P : Type} [AddCommMonoid P] [Module (ZMod p) P]
    (g : (U : OpenNormal G) → H2FpContFamily p G U →ₗ[ZMod p] P)
    (hg : ∀ (U V : OpenNormal G) (h : U ≤ V) (x : H2FpContFamily p G U),
      g V (contMap p G U V h x) = g U x)
    (U : OpenNormal G) (x : H2FpContFamily p G U) :
    H2FpCont.lift g hg (H2FpCont.of p G U x) = g U x :=
  Module.DirectLimit.lift_of g hg x

end Work.CFT.MaxProP
