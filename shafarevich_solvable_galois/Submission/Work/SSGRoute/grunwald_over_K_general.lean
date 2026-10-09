import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.Vocab
import Submission.Work.SSGRoute.grunwald_surjective_odd
import Submission.Work.SSGRoute.grunwald_surjective_two
import Submission.Work.SSGRoute.grunwald_setup
import Submission.Work.SSGRoute.grunwald_kummer_idx
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Grünwald's theorem over `K` with one place per prime of `K`

`Work.SSGRoute.grunwald_surjective_odd` / `_two` realise a continuous additive local datum on the
decomposition groups `decomp k A ⊓ G_K` of a finite set `T` of finite places of `Ω`, provided that
the elements of `T` are pairwise *non-`k`-conjugate* (one place per prime of the base field `k`).
The present statement relaxes that hypothesis to the natural one for a *local datum on `G_K`*:
the places of `T` only have to be pairwise non-`K`-conjugate (`Work.SSGRoute.gesKConj K A B`, i.e.
one place per prime of `K`); `T` may well contain several places over one prime of `k`.

The proof is a base change of the two Grünwald theorems to the base field `↥K`, with top field `⊥`:

* `Ω` is an algebraic closure of the number field `↥K`, and `⊥ : IntermediateField ↥K Ω` is the
  image of `↥K` in `Ω`, so `(⊥).fixingSubgroup = ⊤` and the local groups of the Grünwald theorem
  applied to `(↥K, Ω, ⊥)` are the decomposition groups `decomp ↥K A` themselves;
* `decomp ↥K A` is identified with `decomp k A ⊓ G_K` by `grunwaldSetupDecompEquiv` (the
  `IntermediateField.fixingSubgroupEquiv` transport), which transports the local datum `f A`;
* `IsConjPlace ↥K` is `gesKConj`, so the distinctness hypothesis transfers (`exists_smul_eq_of_comap_eq'`
  together with the fact that `Gal(Ω/↥K)` acts on the places over a prime of `K`);
* the resulting additive, locally constant `z' : Gal(Ω/↥K) → ZMod p` is extended to `G_k` by `0`
  off `G_K`; all three clauses of the conclusion only test elements of `G_K`, and local constancy
  transports because `K.fixingSubgroup` is open in `G_k` and `fixingSubgroupEquiv` is continuous.
-/

namespace Work.SSGRoute

open scoped Pointwise

noncomputable section

/-- **Padding a subgroup of `Gal(Ω/↥K)` to its intersection with `(⊥).fixingSubgroup = ⊤`.**

The local groups of the Grünwald theorems `grunwald_surjective_odd`/`_two` are of the form
`D ⊓ K₀.fixingSubgroup`; at `K₀ = ⊥` the fixing subgroup is `⊤`, so these are the decomposition
groups themselves, and this (multiplicative) equivalence makes the identification explicit. -/
private def botPadEquivK (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (A : ValuationSubring Ω) :
    ↥(SSGRoute.decomp ↥K A) ≃*
      ↥(SSGRoute.decomp ↥K A ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup) :=
{ toFun := fun x => ⟨x.1, Subgroup.mem_inf.mpr ⟨x.2, by
      rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _⟩⟩
  invFun := fun y => ⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl }

theorem grunwald_over_K_general (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (f : ∀ A : {A // A ∈ T},
      ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup) → ZMod p)
    (hf : ∀ A : {A // A ∈ T},
      ∀ a b : ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup),
      f A (a * b) = f A a + f A b)
    (hfc : ∀ A : {A // A ∈ T},
      ∃ U : Subgroup ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup)) ∧
        ∀ x ∈ U, f A x = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A : {A // A ∈ T},
        ∀ δ : ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup),
        z (δ : Ω ≃ₐ[k] Ω) = f A δ) := by
  classical
  haveI hNumK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hAlgClK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hFinBot : FiniteDimensional ↥K (⊥ : IntermediateField ↥K Ω) := inferInstance
  haveI hGalBot : IsGalois ↥K (⊥ : IntermediateField ↥K Ω) := inferInstance
  -- ## transport of the hypotheses to the level of `↥K`
  have hTfinK : ∀ A ∈ T, SSGRoute.IsFinPlace ↥K A := by
    intro A hA htop
    refine hTfin A hA ?_
    refine le_antisymm le_top ?_
    intro x _
    rw [ValuationSubring.mem_comap]
    have h1 : algebraMap ↥K Ω (algebraMap k ↥K x) ∈ A := by
      rw [← ValuationSubring.mem_comap, htop]
      exact trivial
    rwa [← IsScalarTower.algebraMap_apply k ↥K Ω] at h1
  have hTdisjK : ∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace ↥K A B → A = B := by
    intro A hA B hB h
    refine hTdisj A hA B hB ?_
    obtain ⟨σ, hσ⟩ := h
    exact ⟨(↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[k] Ω),
      ((IntermediateField.fixingSubgroupEquiv K).symm σ).2,
      (Work.SSGRoute.fixingSubgroupEquiv_symm_smul k Ω K A σ).trans hσ⟩
  have hζbot : ζ ∈ (⊥ : IntermediateField ↥K Ω) := ⟨⟨ζ, hζK⟩, rfl⟩
  -- ## the local datum, transported from `decomp k A ⊓ G_K` to `decomp ↥K A ⊓ (⊥).fixingSubgroup`
  have hpadHomeo : ∀ A : ValuationSubring Ω, IsHomeomorph (botPadEquivK k Ω K A) := by
    intro A
    haveI : CompactSpace ↥(SSGRoute.decomp ↥K A) := by
      have hclosed : IsClosed ((SSGRoute.decomp ↥K A : Subgroup (Ω ≃ₐ[↥K] Ω)) :
          Set (Ω ≃ₐ[↥K] Ω)) :=
        Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := ↥K) (K' := Ω) A
      haveI : CompactSpace (Ω ≃ₐ[↥K] Ω) := inferInstance
      exact isCompact_iff_compactSpace.mp hclosed.isCompact
    exact isHomeomorph_iff_continuous_bijective.mpr
      ⟨Continuous.subtype_mk continuous_subtype_val _, (botPadEquivK k Ω K A).bijective⟩
  let Φ : (A : {A // A ∈ T}) →
      ↥(SSGRoute.decomp k (A : ValuationSubring Ω) ⊓ K.fixingSubgroup) ≃*
      ↥(SSGRoute.decomp ↥K (A : ValuationSubring Ω) ⊓
        (⊥ : IntermediateField ↥K Ω).fixingSubgroup) :=
    fun A => (Work.SSGRoute.grunwaldSetupDecompEquiv k Ω K A.1).trans (botPadEquivK k Ω K A.1)
  have hΦhomeo : ∀ A : {A // A ∈ T}, IsHomeomorph (Φ A) := by
    intro A
    exact NK.Mine.isHomeomorph_trans _ _
      (Work.SSGRoute.isHomeomorph_decompEquiv k Ω K A.1) (hpadHomeo A.1)
  let f' : ∀ A : {A // A ∈ T},
      ↥(SSGRoute.decomp ↥K (A : ValuationSubring Ω) ⊓
        (⊥ : IntermediateField ↥K Ω).fixingSubgroup) → ZMod p :=
    fun A δ => f A ((Φ A).symm δ)
  have hf' : ∀ A : {A // A ∈ T},
      ∀ a b : ↥(SSGRoute.decomp ↥K (A : ValuationSubring Ω) ⊓
        (⊥ : IntermediateField ↥K Ω).fixingSubgroup),
      f' A (a * b) = f' A a + f' A b := by
    intro A a b
    show f A ((Φ A).symm (a * b)) = f A ((Φ A).symm a) + f A ((Φ A).symm b)
    rw [map_mul, hf A]
  have hfc' : ∀ A : {A // A ∈ T},
      ∃ U : Subgroup ↥(SSGRoute.decomp ↥K (A : ValuationSubring Ω) ⊓
        (⊥ : IntermediateField ↥K Ω).fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp ↥K (A : ValuationSubring Ω) ⊓
          (⊥ : IntermediateField ↥K Ω).fixingSubgroup)) ∧ ∀ x ∈ U, f' A x = 0 := by
    intro A
    obtain ⟨U, hUopen, hU⟩ := hfc A
    refine ⟨U.map (Φ A).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_map]
      exact IsHomeomorph.isOpenMap (hΦhomeo A) ↑U hUopen
    · rintro x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      subst hyx
      show f A ((Φ A).symm ((Φ A) y)) = 0
      rw [MulEquiv.symm_apply_apply]
      exact hU y hy
  -- ## Grünwald over the base field `↥K` (top field `⊥`): cases `p = 2` and `p ≠ 2`
  obtain ⟨z', hz'add, hz'loc, hz'agree⟩ : ∃ z' : (Ω ≃ₐ[↥K] Ω) → ZMod p,
      (∀ g ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup,
        ∀ h ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup, z' (g * h) = z' g + z' h) ∧
      SSGRoute.IsLocConstOn (⊥ : IntermediateField ↥K Ω).fixingSubgroup z' ∧
      (∀ A : {A // A ∈ T},
        ∀ δ : ↥(SSGRoute.decomp ↥K (A : ValuationSubring Ω) ⊓
          (⊥ : IntermediateField ↥K Ω).fixingSubgroup),
        z' (δ : Ω ≃ₐ[↥K] Ω) = f' A δ) := by
    by_cases hp2 : p = 2
    · exact @grunwald_surjective_two p (inferInstance : Fact p.Prime) hp2 ↥K Ω
        (inferInstance : Field ↥K) hNumK (inferInstance : Field Ω)
        (inferInstance : Algebra ↥K Ω) hAlgClK
        (⊥ : IntermediateField ↥K Ω) hFinBot hGalBot
        ζ hζ hζbot T hTfinK hTdisjK f' hf' hfc'
    · exact @grunwald_surjective_odd p (inferInstance : Fact p.Prime) hp2 ↥K Ω
        (inferInstance : Field ↥K) hNumK (inferInstance : Field Ω)
        (inferInstance : Algebra ↥K Ω) hAlgClK
        (⊥ : IntermediateField ↥K Ω) hFinBot hGalBot
        ζ hζ hζbot T hTfinK hTdisjK f' hf' hfc'
  -- the local groups of the Grünwald theorems are `decomp ↥K A ⊓ (⊥).fixingSubgroup` and their
  -- additivity/local-constancy clauses are stated on `(⊥).fixingSubgroup`; both are `⊤`
  have hz'add' : ∀ a b : Ω ≃ₐ[↥K] Ω, z' (a * b) = z' a + z' b := by
    intro a b
    exact hz'add a (by rw [IntermediateField.fixingSubgroup_bot]; exact trivial)
      b (by rw [IntermediateField.fixingSubgroup_bot]; exact trivial)
  have hz'loc' : SSGRoute.IsLocConstOn (⊤ : Subgroup (Ω ≃ₐ[↥K] Ω)) z' := by
    simpa only [IntermediateField.fixingSubgroup_bot] using hz'loc
  -- ## patching back to `G_k`, extended by `0` off `G_K`
  let z : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ =>
    if h : σ ∈ K.fixingSubgroup then z' ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, h⟩) else 0
  have hzmem : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      z σ = z' ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) := by
    intro σ hσ
    simp only [z, dif_pos hσ]
  refine ⟨z, ?_, ?_, ?_⟩
  · intro g hg h hh
    have hgh : g * h ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg hh
    have hmul : (IntermediateField.fixingSubgroupEquiv K) ⟨g * h, hgh⟩ =
        (IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩ *
          (IntermediateField.fixingSubgroupEquiv K) ⟨h, hh⟩ := by
      rw [← map_mul]; rfl
    calc z (g * h) = z' ((IntermediateField.fixingSubgroupEquiv K) ⟨g * h, hgh⟩) := hzmem _ hgh
      _ = z' ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩ *
            (IntermediateField.fixingSubgroupEquiv K) ⟨h, hh⟩) := by rw [hmul]
      _ = z' ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩) +
            z' ((IntermediateField.fixingSubgroupEquiv K) ⟨h, hh⟩) := hz'add' _ _
      _ = z g + z h := by rw [← hzmem g hg, ← hzmem h hh]
  · obtain ⟨U₀, hU₀open, hU₀⟩ := hz'loc'
    have hV : IsOpen (((U₀.comap (IntermediateField.fixingSubgroupEquiv K).toMonoidHom) :
        Subgroup ↥(K.fixingSubgroup)) : Set ↥(K.fixingSubgroup)) := by
      rw [Subgroup.coe_comap]
      exact hU₀open.preimage (Work.SSGRoute.continuous_fixingSubgroupEquiv k Ω K)
    refine ⟨((U₀.comap (IntermediateField.fixingSubgroupEquiv K).toMonoidHom).map
      (K.fixingSubgroup).subtype), ?_, ?_⟩
    · obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.mp hV
      rw [Subgroup.coe_map, ← hW, Subgroup.coe_subtype, Set.image_preimage_eq_inter_range,
        Subtype.range_coe]
      exact hWopen.inter (IntermediateField.fixingSubgroup_isOpen K)
    · intro g hg u hu huH
      obtain ⟨v, hvU, hvu⟩ := Subgroup.mem_map.mp hu
      rw [Subgroup.mem_comap] at hvU
      have hveq : ((IntermediateField.fixingSubgroupEquiv K) v) =
          ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huH⟩) := by
        apply AlgEquiv.ext
        intro x
        have h1 : ((IntermediateField.fixingSubgroupEquiv K) v : Ω ≃ₐ[↥K] Ω) x
            = ((K.fixingSubgroup).subtype v : Ω ≃ₐ[k] Ω) x := rfl
        rw [h1, hvu]
        rfl
      have hmul : (IntermediateField.fixingSubgroupEquiv K)
            ⟨g * u, K.fixingSubgroup.mul_mem hg huH⟩ =
          (IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩ *
            (IntermediateField.fixingSubgroupEquiv K) ⟨u, huH⟩ := by
        rw [← map_mul]; rfl
      calc z (g * u) = z' ((IntermediateField.fixingSubgroupEquiv K)
            ⟨g * u, K.fixingSubgroup.mul_mem hg huH⟩) := hzmem _ _
        _ = z' ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩ *
              (IntermediateField.fixingSubgroupEquiv K) ⟨u, huH⟩) := by rw [hmul]
        _ = z' ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩ *
              (IntermediateField.fixingSubgroupEquiv K) v) := by rw [hveq]
        _ = z' ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩) :=
              hU₀ _ (Subgroup.mem_top _) _ hvU (Subgroup.mem_top _)
        _ = z g := (hzmem g hg).symm
  · intro A δ
    have hΦδ : ((Φ A) δ : Ω ≃ₐ[↥K] Ω) =
        (IntermediateField.fixingSubgroupEquiv K) ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩ := rfl
    calc z (δ : Ω ≃ₐ[k] Ω)
        = z' ((IntermediateField.fixingSubgroupEquiv K)
            ⟨(δ : Ω ≃ₐ[k] Ω), δ.2.2⟩) := hzmem _ δ.2.2
      _ = z' ((Φ A) δ) := by rw [hΦδ]
      _ = f' A ((Φ A) δ) := hz'agree A ((Φ A) δ)
      _ = f A ((Φ A).symm ((Φ A) δ)) := rfl
      _ = f A δ := by rw [MulEquiv.symm_apply_apply]

end

end Work.SSGRoute
