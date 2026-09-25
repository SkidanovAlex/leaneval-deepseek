import Mathlib
import Submission.Work.RelatorRank.CohomologyH2

/-!
# For a finite discrete group, the abstract and the continuous `H²(Γ, 𝔽₂)` agree

**Namespace** `Work.CFTLib`; module
`Submission.Work.CFTLib.finrank_groupCohomology_two_eq_log_card_contH2`.

The shared CFT interface `CFTLib.ShafBound` (`Submission/CFTLib/Interfaces.lean`) bounds the
`𝔽₂`-dimension of Mathlib's *abstract* group cohomology

`groupCohomology (Rep.trivial 𝔽₂ (K ≃ₐ[F] K) 𝔽₂) 2`

of a finite Galois group, while the pro-`2` presentation theory of the workspace
(`Work.RelatorRank.contH2`) computes the *continuous* cohomology `H²(Γ,𝔽₂)` of
`Submission.Work.ConCohomology` (`H2 Γ 𝔽₂ = Z² ⧸ B²` for locally constant cochains).  This
module proves that for a **finite** group `Γ` equipped with the discrete topology the two
objects have the same cardinality, whence

`dim_{𝔽₂} H²(Γ,𝔽₂) = log₂ #H²_cont(Γ,𝔽₂)`,

the bridge between the two conventions.

## The mathematics

For `Γ` finite and discrete, every function `Γ × Γ → 𝔽₂` is locally constant, so the map
`LocallyConstant.toFun` is an additive isomorphism `C^2_cont ≃ (Γ × Γ → 𝔽₂)` (and likewise in
degrees 1 and 3, `lcEquiv`).  With the trivial action of `Γ` on `𝔽₂` the two differentials
coincide (`e2_d1Hom`, and the analogous `e2_mem_Z2` for the cocycle condition), so `e2` carries
`Z²_cont` onto Mathlib's `cocycles₂` and `B²_cont = im d¹` onto Mathlib's `coboundaries₂`.
Hence `H²_cont(Γ,𝔽₂) ≃ H²(Γ,𝔽₂)` as additive groups (`Phi`, `Phi_eq_zero_iff`,
`Phi_surjective`, `natCard_eq`), and the two sides have the same number of elements.

Since `H²(Γ,𝔽₂)` is a finite-dimensional `𝔽₂`-vector space its cardinality is
`2 ^ dim`, so the `𝔽₂`-dimension of the abstract cohomology is the binary logarithm of the
cardinality of the continuous one -- the statement of
`finrank_groupCohomology_two_eq_log_card_contH2`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.dupNamespace false

namespace Work.CFTLib

open Work.ConCohomology

section Gen

variable (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [DiscreteTopology Γ]
  [DistribMulAction Γ (ZMod 2)] [IsDiscreteGModule Γ (ZMod 2)]

/-- On a discrete space every function (and in particular every locally constant function) is a
function: `LocallyConstant X M ≃+ (X → M)`, additively. -/
private noncomputable def lcEquiv (X : Type) [TopologicalSpace X] [DiscreteTopology X]
    (M : Type) [AddCommGroup M] : LocallyConstant X M ≃+ (X → M) where
  toFun f := ⇑f
  invFun f := ⟨f, IsLocallyConstant.of_discrete f⟩
  left_inv f := by ext x; rfl
  right_inv f := rfl
  map_add' f g := rfl

/-- The discrete group `Γ` is a one-point space for the purposes of the continuous cochain
complex: `C¹_cont ≃ Γ → 𝔽₂`. -/
private noncomputable def e1 : Cochain1 Γ (ZMod 2) ≃+ (Γ → ZMod 2) := lcEquiv Γ (ZMod 2)

/-- `C²_cont ≃ Γ × Γ → 𝔽₂`. -/
private noncomputable def e2 : Cochain2 Γ (ZMod 2) ≃+ (Γ × Γ → ZMod 2) :=
  lcEquiv (Γ × Γ) (ZMod 2)

/-- The trivial `𝔽₂`-linear representation of `Γ` whose abstract cohomology is compared with the
continuous one. -/
private abbrev trivRep : Rep (ZMod 2) Γ := Rep.trivial (ZMod 2) Γ (ZMod 2)

/-- The differentials agree: Mathlib's `d₁₂` on `Fun(Γ,𝔽₂)` corresponds under `e1`, `e2` to the
continuous `d¹` on locally constant cochains. -/
private lemma e2_d1Hom (hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x) (g : Cochain1 Γ (ZMod 2)) :
    e2 Γ (d1Hom Γ (ZMod 2) g) = groupCohomology.d₁₂ (trivRep Γ) (e1 Γ g) := by
  funext p
  obtain ⟨σ, τ⟩ := p
  simp only [e1, e2, lcEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    groupCohomology.d₁₂_hom_apply, d1Hom_apply, Representation.trivial_apply, hsmul]

/-- The cocycle conditions agree: a locally constant `2`-cochain is a continuous `2`-cocycle iff
its underlying function is a Mathlib `2`-cocycle for the trivial representation. -/
private lemma e2_mem_Z2 (hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x) (z : Cochain2 Γ (ZMod 2)) :
    z ∈ Z2 Γ (ZMod 2) ↔ e2 Γ z ∈ groupCohomology.cocycles₂ (trivRep Γ) := by
  rw [mem_Z2, groupCohomology.mem_cocycles₂_def]
  constructor
  · intro h σ τ ρ
    have := h σ τ ρ
    simpa only [IsCocycle2, e2, lcEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, hsmul,
      Representation.trivial_apply] using this
  · intro h σ τ ρ
    have := h σ τ ρ
    simpa only [IsCocycle2, e2, lcEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, hsmul,
      Representation.trivial_apply] using this

/-- The coboundary conditions agree: `x` is a continuous `2`-coboundary iff `e2 x` is a Mathlib
`2`-coboundary.  This is the content of `e2_d1Hom` together with the fact that `e1` and `e2` are
bijective. -/
private lemma exists_d1Hom_iff (hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x)
    (z : Cochain2 Γ (ZMod 2)) :
    (∃ g : Cochain1 Γ (ZMod 2), d1Hom Γ (ZMod 2) g = z) ↔
      ∃ f : Γ → ZMod 2, groupCohomology.d₁₂ (trivRep Γ) f = e2 Γ z := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨e1 Γ g, (e2_d1Hom Γ hsmul g).symm⟩
  · rintro ⟨f, hf⟩
    refine ⟨(e1 Γ).symm f, ?_⟩
    apply (e2 Γ).injective
    rw [e2_d1Hom Γ hsmul ((e1 Γ).symm f)]
    rw [AddEquiv.apply_symm_apply, hf]

/-- `e2` restricted to the continuous `2`-cocycles, as an additive map onto Mathlib's `2`-cocycles
for the trivial representation. -/
private noncomputable def cocycleHom (hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x) :
    Z2 Γ (ZMod 2) →+ ↥(groupCohomology.cocycles₂ (trivRep Γ)) where
  toFun z := ⟨e2 Γ (z : Cochain2 Γ (ZMod 2)),
    (e2_mem_Z2 Γ hsmul (z : Cochain2 Γ (ZMod 2))).1 z.2⟩
  map_zero' := by
    apply Subtype.ext
    simp only [Submodule.coe_zero, AddSubgroup.coe_zero]
    exact map_zero (e2 Γ)
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    exact map_add (e2 Γ) (x : Cochain2 Γ (ZMod 2)) (y : Cochain2 Γ (ZMod 2))

/-- The comparison map from the continuous `2`-cocycles to the abstract `H²(Γ,𝔽₂)`. -/
private noncomputable def Phi (hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x) :
    Z2 Γ (ZMod 2) →+ ↥(groupCohomology.H2 (trivRep Γ)) where
  toFun z := groupCohomology.H2π (trivRep Γ) (cocycleHom Γ hsmul z)
  map_zero' := by
    rw [map_zero (cocycleHom Γ hsmul)]
    exact map_zero _
  map_add' x y := by
    rw [map_add (cocycleHom Γ hsmul)]
    exact map_add _ _ _

/-- The kernel of the comparison map is the group of continuous `2`-coboundaries. -/
private lemma Phi_eq_zero_iff (hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x) (z : Z2 Γ (ZMod 2)) :
    Phi Γ hsmul z = 0 ↔ z ∈ B2' Γ (ZMod 2) := by
  have h1 : groupCohomology.H2π (trivRep Γ) (cocycleHom Γ hsmul z) = 0 ↔
      e2 Γ (z : Cochain2 Γ (ZMod 2)) ∈ groupCohomology.coboundaries₂ (trivRep Γ) :=
    groupCohomology.H2π_eq_zero_iff (cocycleHom Γ hsmul z)
  refine h1.trans ?_
  rw [groupCohomology.coboundaries₂, LinearMap.mem_range, mem_B2', mem_B2]
  exact (exists_d1Hom_iff Γ hsmul (z : Cochain2 Γ (ZMod 2))).symm

/-- The comparison map is onto. -/
private lemma Phi_surjective (hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x) :
    Function.Surjective (Phi Γ hsmul) := by
  intro y
  obtain ⟨w, hw⟩ :=
    (ModuleCat.epi_iff_surjective (groupCohomology.H2π (trivRep Γ))).1 inferInstance y
  obtain ⟨f, hf⟩ := w
  refine ⟨⟨(e2 Γ).symm f, ?_⟩, ?_⟩
  · exact (e2_mem_Z2 Γ hsmul ((e2 Γ).symm f)).mpr
      (by simpa [AddEquiv.apply_symm_apply] using hf)
  · rw [← hw]
    exact congrArg (groupCohomology.H2π (trivRep Γ)) (Subtype.ext (by
      change e2 Γ ((e2 Γ).symm f) = f
      exact AddEquiv.apply_symm_apply (e2 Γ) f))

end Gen

/-- **The bridge.**  For a finite group with the discrete topology the continuous cohomology
`H²_cont(Γ,𝔽₂) = Z² ⧸ B²` of `Work.ConCohomology` has the same cardinality as Mathlib's abstract
`H²(Γ,𝔽₂)`. -/
private theorem natCard_eq (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [DiscreteTopology Γ] :
    Nat.card (Work.RelatorRank.contH2 Γ) =
      Nat.card ↥(groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) := by
  letI : DistribMulAction Γ (ZMod 2) := Work.RelatorRank.f2TrivialAction Γ
  letI : Work.ConCohomology.IsDiscreteGModule Γ (ZMod 2) := Work.RelatorRank.f2Discrete Γ
  have hsmul : ∀ (γ : Γ) (x : ZMod 2), γ • x = x := fun γ x => rfl
  show Nat.card ((Z2 Γ (ZMod 2)) ⧸ (B2' Γ (ZMod 2))) =
    Nat.card ↥(groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2)
  have hker : (Phi Γ hsmul).ker = B2' Γ (ZMod 2) := by
    ext z
    rw [AddMonoidHom.mem_ker]
    exact Phi_eq_zero_iff Γ hsmul z
  have he : (Z2 Γ (ZMod 2)) ⧸ (B2' Γ (ZMod 2)) ≃+
      ↥(groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) := by
    rw [← hker]
    exact QuotientAddGroup.quotientKerEquivOfSurjective (Phi Γ hsmul) (Phi_surjective Γ hsmul)
  exact Nat.card_congr he.toEquiv

theorem finrank_groupCohomology_two_eq_log_card_contH2
    (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [DiscreteTopology Γ]
    [Fintype Γ] :
    Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) =
      Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Γ)) := by
  have hcard := natCard_eq Γ
  haveI : Module.Finite (ZMod 2) ↥(groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) := by
    haveI : Finite ↥(groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) Γ (ZMod 2))) := inferInstance
    exact Module.Finite.of_surjective
      (ModuleCat.Hom.hom (groupCohomology.H2π (Rep.trivial (ZMod 2) Γ (ZMod 2))))
      ((ModuleCat.epi_iff_surjective
        (groupCohomology.H2π (Rep.trivial (ZMod 2) Γ (ZMod 2)))).1 inferInstance)
  have hpow : Nat.card ↥(groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2)
      = 2 ^ Module.finrank (ZMod 2) ↥(groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 2) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard, hpow, Nat.log_pow (by norm_num)]

end Work.CFTLib
