import Submission.Work.RelatorRank.API

/-!
# `Work.RelatorRank` -- transport of presentations

**Namespace** `Work.RelatorRank`; module `Submission.Work.RelatorRank.Transfer`.

What *is* provable about the bridge of `Submission/Work/RelatorRank/Bridge.lean`, and the exact
statement of the missing input:

* `denseGenerating_comp_continuousMulEquiv` -- a continuous automorphism of `Γ` carries a dense
  generating family to a dense generating family;
* `ker_lift_comp_continuousMulEquiv` -- **the kernel is *literally* unchanged**:
  `ker (lift (e ∘ gen)) = ker (lift gen)` for every continuous multiplicative equivalence `e`
  (injective, so composition with `e` does not change the kernel);
* `hasProP2Presentation_comp_continuousMulEquiv` -- consequently a presentation datum with
  generators `gen` and relators `rel` is also a presentation datum with generators `e ∘ gen` and the
  *same* relators;
* `relatorHalfOf_of_aut_transitive` -- **the diagnosis**: the bridge would follow from the
  `∃`-form together with the statement that *every* dense generating `d`-family is the image of the
  presented one under an automorphism of `Γ`.  The `README.md` records that this last statement is
  *false* already for the finite `2`-group `ℤ/4 × ℤ/2`, so the automorphism argument of
  `Submission/PLAN.md` §21 cannot prove the bridge;
* `normalClosure_image_le_ker` -- the "change of generators" (β-)transfer: if `φ = lift gen` presents
  `Γ` with relators `rel` and `ψ` is any homomorphism of free groups, then the images of the
  relators under `ψ` present the kernel of `φ ∘ ψ`;
* `hasProP2Presentation_of_ker_map_eq` -- and if the induced map on kernels is *onto*, the transfer
  is an equality of presentations.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Work.RelatorRank

variable {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']

/-! ## Transport along a continuous multiplicative equivalence -/

/-- A continuous multiplicative equivalence carries dense generating families to dense generating
families. -/
theorem denseGenerating_comp_continuousMulEquiv {ι : Type*} (e : Γ ≃ₜ* Γ') (gen : ι → Γ)
    (hgen : DenseGenerating gen) : DenseGenerating (fun i => e (gen i)) := by
  rw [denseGenerating_iff] at hgen ⊢
  have hmap : (Subgroup.closure (Set.range fun i => e (gen i)))
      = (Subgroup.closure (Set.range gen)).map (e : Γ →* Γ') := by
    rw [MonoidHom.map_closure]
    congr 1
    exact Set.range_comp e gen
  rw [hmap]
  exact DenseRange.topologicalClosure_map_subgroup (map_continuous e) e.surjective.denseRange hgen

/-- **The presentation kernel does not change under a continuous automorphism of `Γ`.**  For any
continuous multiplicative equivalence `e : Γ ≃ₜ* Γ'` and any family `gen`, the kernels of
`FreeGroup.lift gen` and of `FreeGroup.lift (e ∘ gen)` coincide (as subgroups of the free group). -/
theorem ker_lift_comp_continuousMulEquiv {ι : Type*} (e : Γ ≃ₜ* Γ') (gen : ι → Γ) :
    MonoidHom.ker (FreeGroup.lift fun i => e (gen i)) = MonoidHom.ker (FreeGroup.lift gen) := by
  have hcomp : FreeGroup.lift (fun i => e (gen i))
      = (e : Γ →* Γ').comp (FreeGroup.lift gen) := by
    refine MonoidHom.ext fun x => ?_
    exact (FreeGroup.lift_unique ((e : Γ →* Γ').comp (FreeGroup.lift gen))
      (fun i => by simp) (x := x)).symm
  rw [hcomp, MonoidHom.ker_comp_of_injective _ _ e.injective]

/-- **Transport of presentation data along a continuous automorphism of `Γ`**: the relators of a
presentation can be reused verbatim for the transported generating family. -/
theorem hasProP2Presentation_comp_continuousMulEquiv {d r : ℕ} (P : ProP2PresentationData Γ d r)
    (e : Γ ≃ₜ* Γ') : HasProP2Presentation Γ' d r :=
  ⟨{ gen := fun i => e (P.gen i),
     rel := P.rel,
     dense := denseGenerating_comp_continuousMulEquiv e P.gen P.dense,
     card_le := P.card_le,
     ker_eq := by rw [ker_lift_comp_continuousMulEquiv, P.ker_eq] }⟩

/-- **The diagnosis of the bridge.**  Suppose `gen₀` is a dense generating `d`-family presented by
`rel₀` with at most `r` relators, and suppose that every dense generating `d`-family of `Γ` is the
image of `gen₀` under a *continuous automorphism* of `Γ`.  Then the presentation-independent bound
`RelatorHalfOf Γ d r` holds.

The second hypothesis ("two minimal generating tuples are related by an automorphism of `Γ`"),
used in `Submission/PLAN.md` §21, is **false** in general -- see the `README.md` for the
counterexample `Γ = ℤ/4 × ℤ/2`.  With the `∃`-form `HasProP2Presentation Γ d r` in place of the
hypotheses on `gen₀` and `rel₀`, this lemma is `Work.RelatorRank.relatorHalfOf_of_autTransitive`. -/
theorem relatorHalfOf_of_aut_transitive {d r : ℕ} (gen₀ : Fin d → Γ) (hgen₀ : DenseGenerating gen₀)
    (rel₀ : Finset (FreeGroup (Fin d))) (hcard : rel₀.card ≤ r)
    (hker : MonoidHom.ker (FreeGroup.lift gen₀) = Subgroup.normalClosure (rel₀ : Set _))
    (htrans : ∀ gen : Fin d → Γ, DenseGenerating gen →
      ∃ e : Γ ≃ₜ* Γ, ∀ i, gen i = e (gen₀ i)) :
    RelatorHalfOf Γ d r := by
  intro gen hgen
  obtain ⟨e, he⟩ := htrans gen hgen
  refine ⟨rel₀, hcard, ?_⟩
  have hgen_eq : gen = fun i => e (gen₀ i) := funext he
  rw [hgen_eq, ker_lift_comp_continuousMulEquiv, hker]

/-! ## Change of generators (the β-transfer) -/

/-- **Change of generators.**  Let `φ, φ' : FreeGroup ι →* Γ` be two presentation maps related by a
self-map `β` of the free group, `φ ∘ β = φ'` (the typical situation: `gen` and `gen'` are two
generating families of `Γ` of the same size and `β` expresses the `gen'`-generators in terms of the
`gen`-generators).  If `rel'` presents `φ'`, then the images of `rel'` under `β` are relators of
`φ`.  This is the one inclusion that holds without any further hypothesis; the reverse inclusion is
exactly the statement that `β` is onto on the presentation kernels. -/
theorem normalClosure_image_le_ker {ι : Type*} [DecidableEq (FreeGroup ι)]
    (φ φ' : FreeGroup ι →* Γ) (β : FreeGroup ι →* FreeGroup ι) (hβ : φ.comp β = φ')
    (rel' : Finset (FreeGroup ι))
    (hker : MonoidHom.ker φ' = Subgroup.normalClosure (rel' : Set (FreeGroup ι))) :
    Subgroup.normalClosure (((rel'.image β : Finset (FreeGroup ι)) : Set (FreeGroup ι)))
      ≤ MonoidHom.ker φ := by
  refine Subgroup.normalClosure_le_normal ?_
  intro y hy
  rw [Finset.mem_coe, Finset.mem_image] at hy
  obtain ⟨r, hr, rfl⟩ := hy
  change β r ∈ MonoidHom.ker φ
  have hcomp : φ (β r) = φ' r := by rw [← MonoidHom.comp_apply, hβ]
  rw [MonoidHom.mem_ker, hcomp]
  have hr' : r ∈ MonoidHom.ker φ' := by
    rw [hker]
    exact Subgroup.subset_normalClosure (by simpa using hr)
  rwa [MonoidHom.mem_ker] at hr'

/-- **Change of generators, equality form.**  With the notation of `normalClosure_image_le_ker`, if
in addition `β` maps the kernel of `φ'` *onto* the kernel of `φ`
(`Subgroup.map β (ker φ') = ker φ`), then the transported relator set presents `φ` exactly.

This isolates the precise group-theoretic content of the bridge: for two dense generating families
`gen`, `gen'` of a finitely generated pro-`p` group `Γ` of the same size `d = d(Γ)`, the relevant
self-lift `β` of the free group is onto on the presentation kernels -- a theorem that requires the
identification of the minimal relation number with `dim_{𝔽₂} H²` and is not available here (it
*does* fail for non-minimal generating families, e.g. `ℤ → ℤ/4`, `x ↦ 5x`). -/
theorem ker_eq_normalClosure_image_of_map_ker_eq {ι : Type*} [DecidableEq (FreeGroup ι)]
    (φ φ' : FreeGroup ι →* Γ) (β : FreeGroup ι →* FreeGroup ι) (hβ : φ.comp β = φ')
    (rel' : Finset (FreeGroup ι))
    (hker : MonoidHom.ker φ' = Subgroup.normalClosure (rel' : Set (FreeGroup ι)))
    (hβker : Subgroup.map β (MonoidHom.ker φ') = MonoidHom.ker φ) :
    MonoidHom.ker φ =
      Subgroup.normalClosure (((rel'.image β : Finset (FreeGroup ι)) : Set (FreeGroup ι))) := by
  refine le_antisymm ?_ (normalClosure_image_le_ker φ φ' β hβ rel' hker)
  rw [← hβker, hker, Finset.coe_image]
  exact Subgroup.map_normalClosure_le (rel' : Set (FreeGroup ι)) β

/-- The same statement for the canonical presentation maps of two generating families
`gen, gen' : Fin d → Γ`: a self-map `β` of the free group with `lift gen' = lift gen ∘ β` transports
relators of `gen'` to relators of `gen`, and transports them *exactly* as soon as it is onto on the
kernels. -/
theorem ker_eq_normalClosure_image_of_lift_comp {d : ℕ} (gen gen' : Fin d → Γ)
    (β : FreeGroup (Fin d) →* FreeGroup (Fin d))
    (hβ : (FreeGroup.lift gen).comp β = FreeGroup.lift gen')
    (rel' : Finset (FreeGroup (Fin d)))
    (hker : MonoidHom.ker (FreeGroup.lift gen') = Subgroup.normalClosure (rel' : Set _)) :
    Subgroup.normalClosure ((rel'.image β : Finset (FreeGroup (Fin d))) : Set _)
      ≤ MonoidHom.ker (FreeGroup.lift gen) :=
  normalClosure_image_le_ker _ _ β hβ rel' hker

end Work.RelatorRank
