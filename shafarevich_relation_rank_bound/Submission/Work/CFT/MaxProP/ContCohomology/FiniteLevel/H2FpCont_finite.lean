import Mathlib
import Submission.Work.CFT.MaxProP.ContCohomology.Defs

/-!
# Continuous `H²` of a discrete group

`Work.CFT.MaxProP.H2FpCont p G` is the filtered colimit of the second cohomology groups
`H²(G ⧸ U, 𝔽_p)` over the *open normal* subgroups `U ◁ G`, along the inflation maps — the
correct replacement for Mathlib's abstract `H²(G, 𝔽_p)` when `G` is an infinite pro-`p` group.

If `G` is *discrete* then every subgroup is open, and in particular the trivial subgroup `⊥` is an
open normal subgroup.  Because the indexing order of `H2FpCont` is *reverse* inclusion, `⊥` is the
*greatest* element of the index set: every `U` satisfies `U ≤ ⊥`.  Hence the colimit collapses onto
the value at `⊥`, and since the quotient map `G ⧸ ⊥ → G` is an isomorphism, `H²_cont(G, 𝔽_p)` is
`H²(G, 𝔽_p)`.

This file proves that: `Work.CFT.MaxProP.H2FpCont_finite`.

## Main results

* `Work.CFT.KochTransfer.infl_id`, `Work.CFT.KochTransfer.infl_comp` — the inflation maps of the
  Koch-transfer vocabulary are functorial.
* `Work.CFT.KochTransfer.inflEquiv` — inflation along a group isomorphism `e : Q ≃* G` is a linear
  equivalence `H²(G, 𝔽_p) ≃ₗ H²(Q, 𝔽_p)`.
* `Work.CFT.MaxProP.contMap_comp`, `Work.CFT.MaxProP.contMap_self` — the transition maps `contMap`
  of the direct system defining `H2FpCont` are compatible, and `contMap` from `⊥` to `⊥` is the
  identity.
* `Work.CFT.MaxProP.H2FpCont.finiteBotEquiv` — the colimit is the value at the greatest index `⊥`.
* `Work.CFT.MaxProP.H2FpCont_finite` — `H²_cont(G, 𝔽_p) ≃ₗ H²(G, 𝔽_p)` for discrete `G`.
-/

open scoped Classical

namespace Work.CFT.KochTransfer

/-- The inflation maps are compatible with the identity homomorphism: `infl id = id`. -/
theorem infl_id {p : ℕ} (G : Type) [Group G] :
    infl (p := p) (MonoidHom.id G) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  refine groupCohomology.H2_induction_on x ?_
  intro c
  simp only [LinearMap.id_apply]
  rw [infl_H2π]
  congr 1

/-- Functoriality of inflation: for `α : G₁ →* G₂` and `β : G₂ →* G₃`,
`infl (β ∘ α) = infl α ∘ infl β`. -/
theorem infl_comp {p : ℕ} {G₁ G₂ G₃ : Type} [Group G₁] [Group G₂] [Group G₃]
    (α : G₁ →* G₂) (β : G₂ →* G₃) :
    infl (p := p) (β.comp α) = (infl (p := p) α).comp (infl (p := p) β) := by
  refine LinearMap.ext fun x => ?_
  refine groupCohomology.H2_induction_on x ?_
  intro c
  simp only [LinearMap.comp_apply]
  rw [infl_H2π, infl_H2π, infl_H2π]
  congr 1

/-- Inflation along a group isomorphism `e : Q ≃* G` is a linear equivalence on `H²`. -/
noncomputable def inflEquiv (p : ℕ) {G Q : Type} [Group G] [Group Q] (e : Q ≃* G) :
    groupCohomology.H2 (Rep.trivial (ZMod p) Q (ZMod p)) ≃ₗ[ZMod p]
      groupCohomology.H2 (Rep.trivial (ZMod p) G (ZMod p)) := by
  have hcomp1 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
    ext g; exact e.apply_symm_apply g
  have hcomp2 : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id Q := by
    ext g; exact e.symm_apply_apply g
  exact LinearEquiv.ofLinearMap
    (infl (p := p) e.symm.toMonoidHom) (infl (p := p) e.toMonoidHom)
    (by rw [← infl_comp, hcomp1, infl_id])
    (by rw [← infl_comp, hcomp2, infl_id])

end Work.CFT.KochTransfer

namespace Work.CFT.MaxProP

/-- The trivial subgroup `⊥` of a discrete group, as an open normal subgroup. -/
def OpenNormal.discreteBot (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    OpenNormal G := ⟨⊥, inferInstance, isOpen_discrete _⟩

/-- `⊥` is the *greatest* element of the index set `OpenNormal G`, i.e. every open normal subgroup
is contained in it (the order on `OpenNormal` is reverse inclusion). -/
theorem OpenNormal.le_discreteBot {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (U : OpenNormal G) : U ≤ OpenNormal.discreteBot G := by
  rw [OpenNormal.le_def]
  exact bot_le

/-- The quotient map `G ⧸ U → G ⧸ U` attached to `U ≤ U` is the identity. -/
theorem OpenNormal.quotientMap_self {G : Type} [Group G] [TopologicalSpace G]
    (U : OpenNormal G) (h : U ≤ U) : quotientMap U U h = MonoidHom.id _ := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.carrier x
  rfl

/-- The quotient maps are functorial: the composite `G ⧸ W → G ⧸ V → G ⧸ U` is the quotient map
`G ⧸ W → G ⧸ U`. -/
theorem OpenNormal.quotientMap_comp {G : Type} [Group G] [TopologicalSpace G]
    (U V W : OpenNormal G) (hUV : U ≤ V) (hVW : V ≤ W) :
    (quotientMap U V hUV).comp (quotientMap V W hVW) = quotientMap U W (le_trans hUV hVW) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W.carrier x
  rfl

/-- The transition maps `contMap` of the direct system defining `H2FpCont` are compatible. -/
theorem contMap_comp (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    (U V W : OpenNormal G) (hUV : U ≤ V) (hVW : V ≤ W) :
    (contMap p G V W hVW).comp (contMap p G U V hUV) = contMap p G U W (le_trans hUV hVW) := by
  simp only [contMap]
  rw [← Work.CFT.KochTransfer.infl_comp, OpenNormal.quotientMap_comp]

/-- The transition map `contMap` from `U` to itself is the identity. -/
theorem contMap_self (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    (U : OpenNormal G) (h : U ≤ U) : contMap p G U U h = LinearMap.id := by
  simp only [contMap]
  rw [OpenNormal.quotientMap_self, Work.CFT.KochTransfer.infl_id]

/-- The projection of the direct system defining `H2FpCont` onto its value at the greatest index
`⊥`: the inflation `H²(G ⧸ U, 𝔽_p) → H²(G ⧸ ⊥, 𝔽_p)`. -/
noncomputable def H2FpCont.finiteDesc (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (U : OpenNormal G) :
    H2FpContFamily p G U →ₗ[ZMod p] H2FpContFamily p G (OpenNormal.discreteBot G) :=
  contMap p G U (OpenNormal.discreteBot G) (OpenNormal.le_discreteBot U)

/-- The maps `finiteDesc` are compatible with the transition maps of the direct system, i.e. they
form a cocone on the index set of `H2FpCont`. -/
theorem H2FpCont.finiteDesc_compat (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (U V : OpenNormal G) (h : U ≤ V) (x : H2FpContFamily p G U) :
    H2FpCont.finiteDesc p G V (contMap p G U V h x) = H2FpCont.finiteDesc p G U x := by
  simp only [H2FpCont.finiteDesc]
  rw [← LinearMap.comp_apply, contMap_comp]

/-- Induction principle for the colimit `H2FpCont`: a property of elements of the colimit holds for
all of them as soon as it holds on the image of every finite level. -/
theorem H2FpCont.induction_on {p : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    {C : H2FpCont p G → Prop} (z : H2FpCont p G)
    (h : ∀ (U : OpenNormal G) (x : H2FpContFamily p G U), C (H2FpCont.of p G U x)) : C z :=
  Module.DirectLimit.induction_on z h

/-- **The colimit `H²_cont(G, 𝔽_p)` is the value at the greatest index `⊥`** when `G` is discrete:
the canonical map `H²(G ⧸ ⊥, 𝔽_p) → H²_cont(G, 𝔽_p)` is a linear equivalence. -/
noncomputable def H2FpCont.finiteBotEquiv (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] :
    H2FpCont p G ≃ₗ[ZMod p] H2FpContFamily p G (OpenNormal.discreteBot G) :=
  LinearEquiv.ofLinearMap
    (H2FpCont.lift (H2FpCont.finiteDesc p G) (H2FpCont.finiteDesc_compat p G))
    (H2FpCont.of p G (OpenNormal.discreteBot G))
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, H2FpCont.lift_of, H2FpCont.finiteDesc, contMap_self,
        LinearMap.id_apply])
    (by
      refine LinearMap.ext fun z => ?_
      refine H2FpCont.induction_on
        (C := fun w => (H2FpCont.of p G (OpenNormal.discreteBot G))
          (H2FpCont.lift (H2FpCont.finiteDesc p G) (H2FpCont.finiteDesc_compat p G) w) = w) z ?_
      intro U x
      simp only [H2FpCont.lift_of, H2FpCont.finiteDesc, H2FpCont.of_f])

/-- **Continuous cohomology of a discrete group**: `H²_cont(G, 𝔽_p) ≃ₗ H²(G, 𝔽_p)`, obtained by
evaluating the colimit at `⊥` and using `G ⧸ ⊥ ≃* G`. -/
noncomputable def H2FpCont.finiteEquiv (p : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] :
    H2FpCont p G ≃ₗ[ZMod p] (Work.Tower.Shafarevich.H2Fp p G : Type) :=
  (H2FpCont.finiteBotEquiv p G).trans
    (Work.CFT.KochTransfer.inflEquiv p (QuotientGroup.quotientBot (G := G)))

end Work.CFT.MaxProP

namespace Work.CFT.MaxProP.ContCohomology.FiniteLevel

/-- For a finite group `H` (with its discrete topology) the continuous cohomology
`H²_cont(H, 𝔽_p)` coincides with the abstract group cohomology `H²(H, 𝔽_p)`: the colimit over the
open normal subgroups is the value at the trivial subgroup. -/
theorem H2FpCont_finite (p : ℕ) (H : Type) [Group H] [Finite H] [TopologicalSpace H]
    [DiscreteTopology H] :
    Nonempty (Work.CFT.MaxProP.H2FpCont p H ≃ₗ[ZMod p] (Work.Tower.Shafarevich.H2Fp p H : Type)) :=
  ⟨Work.CFT.MaxProP.H2FpCont.finiteEquiv p H⟩

end Work.CFT.MaxProP.ContCohomology.FiniteLevel
