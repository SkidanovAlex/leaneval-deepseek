import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.cokernel_map_shortExact
import Submission.Work.Cohomology.cokernel_biprod_map_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Mayer–Vietoris for the top relative homology of the complement of a disjoint union

Write `F(X) := (relChains M Xᶜ).homology N` for the relative homology `H_N(M, M∖X)` of the
"excluded set" `X`, contravariant in `X`.  This file proves that for closed disjoint compact sets
`A, B ⊆ M` the group `F(A ∪ B)` is free as soon as `F(A)` and `F(B)` are.

The proof is the Mayer–Vietoris argument for the "excluded set" functor.  Put `S := Aᶜ`,
`T := Bᶜ`; these are open with `S ∪ T = univ` (because `A ∩ B = ∅`) and `S ∩ T = (A ∪ B)ᶜ`.

* The **Mayer–Vietoris short exact sequence** of the cover `{S, T}`,
  `0 → C_*(S∩T) → C_*(S) ⊞ C_*(T) → C^{S,T} → 0` (`mvShort`), maps by a morphism `mvToTrivial`
  (with monomorphic components) into the split sequence
  `0 → C_*(M) → C_*(M) ⊞ C_*(M) → C_*(M) → 0` (`trivialShort`): the first component is the
  inclusion `C_*(S∩T) → C_*(M)`, the second is `C_*(S) ⊞ C_*(T) → C_*(M) ⊞ C_*(M)` and the third
  is the inclusion of the small chains `C^{S,T} → C_*(M)`.
* By the snake lemma (`cokernel_map_shortExact`) the cokernels form a short exact sequence
  `0 → C_*(M)/C_*(S∩T) → C_*(M)/C_*(S) ⊞ C_*(M)/C_*(T) → coker(smallToSing S T) → 0`.
* Since `S ∪ T = univ`, the inclusion of the small chains is a quasi-isomorphism
  (`smallChains_homology_iso`), so every homology group of `coker (smallToSing S T)` vanishes in
  positive degrees (`isZero_homology_coker_of_isIso`).
* The long exact sequence of the cokernel sequence in degree `N` is therefore
  `0 → F(A∪B) → F(A) ⊞ F(B) → 0` (`isIso_homologyMap_of_acyclic`), and freeness transfers using
  `H_N(X ⊞ Y) ≅ H_N(X) ⊞ H_N(Y)` (`homology_biprod_iso_chain`) and the freeness of a biproduct
  of free `ℤ`-modules (`ModuleCat.free_shortExact`).

## Main result

* `relChains_compl_union_free`
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-! ## The split short exact sequence `0 ⟶ C ⟶ C ⊞ C ⟶ C ⟶ 0` -/

/-- The diagonal `C_*(M) ⟶ C_*(M) ⊞ C_*(M)`, `x ↦ (x, x)`. -/
def complDiag (M : TopCat) : singularChains ℤ M ⟶ singularChains ℤ M ⊞ singularChains ℤ M :=
  biprod.lift (𝟙 _) (𝟙 _)

/-- The difference `C_*(M) ⊞ C_*(M) ⟶ C_*(M)`, `(a, b) ↦ a - b`. -/
def complDiff (M : TopCat) : singularChains ℤ M ⊞ singularChains ℤ M ⟶ singularChains ℤ M :=
  biprod.desc (𝟙 _) (-𝟙 _)

lemma complDiff_eq (M : TopCat) :
    complDiff M = (biprod.fst : singularChains ℤ M ⊞ singularChains ℤ M ⟶ singularChains ℤ M)
      - (biprod.snd : singularChains ℤ M ⊞ singularChains ℤ M ⟶ singularChains ℤ M) := by
  rw [complDiff, biprod.desc_eq, sub_eq_add_neg]
  simp only [Category.comp_id, Preadditive.comp_neg]

lemma complDiff_neg_one (M : TopCat) :
    complDiff M ≫ (-𝟙 (singularChains ℤ M)) = -(complDiff M) := by
  rw [Preadditive.comp_neg, Category.comp_id]

lemma complDiag_comp_complDiff (M : TopCat) : complDiag M ≫ complDiff M = 0 := by
  rw [complDiag, complDiff, biprod.lift_desc, Category.id_comp, Category.id_comp, add_neg_cancel]

/-- The trivial (split) short exact sequence
`0 ⟶ C_*(M) ⟶ C_*(M) ⊞ C_*(M) ⟶ C_*(M) ⟶ 0`. -/
def trivialShort (M : TopCat) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (complDiag M) (complDiff M) (complDiag_comp_complDiff M)

/-- **The trivial pair is short exact**, with splitting `r = fst`, `s = -inr`. -/
theorem trivialShort_shortExact (M : TopCat) : (trivialShort M).ShortExact := by
  apply ShortComplex.Splitting.shortExact
  refine { r := (biprod.fst : singularChains ℤ M ⊞ singularChains ℤ M ⟶ singularChains ℤ M)
           s := -(biprod.inr : singularChains ℤ M ⟶ singularChains ℤ M ⊞ singularChains ℤ M)
           f_r := biprod.lift_fst (𝟙 _) (𝟙 _)
           s_g := ?_
           id := ?_ }
  · show (-(biprod.inr) : singularChains ℤ M ⟶ singularChains ℤ M ⊞ singularChains ℤ M)
        ≫ complDiff M = 𝟙 _
    rw [Preadditive.neg_comp, complDiff, biprod.inr_desc, neg_neg]
  · show ((biprod.fst : singularChains ℤ M ⊞ singularChains ℤ M ⟶ singularChains ℤ M) ≫ complDiag M
        + complDiff M ≫ (-(biprod.inr) : singularChains ℤ M ⟶
            singularChains ℤ M ⊞ singularChains ℤ M))
        = 𝟙 (singularChains ℤ M ⊞ singularChains ℤ M)
    apply biprod.hom_ext
    · rw [Preadditive.add_comp, Category.id_comp]
      rw [Category.assoc, Category.assoc, complDiag, biprod.lift_fst]
      rw [Preadditive.neg_comp, biprod.inr_fst, neg_zero, comp_zero, Category.comp_id, add_zero]
    · rw [Preadditive.add_comp, Category.id_comp]
      rw [Category.assoc, Category.assoc, complDiag, biprod.lift_snd]
      rw [Preadditive.neg_comp, biprod.inr_snd, complDiff_neg_one, complDiff_eq, Category.comp_id]
      abel

/-! ## The morphism from the Mayer–Vietoris sequence to the trivial sequence -/

/-- The first component of the Mayer–Vietoris map `C_*(S ∩ T) ⟶ C_*(S)`: the inclusion of the
chains of `S ∩ T` into those of `S`, expressed as a `chainMap`. -/
lemma chainMap_inclUVU_comp (S T : Set M) :
    SSet.chainComplexMap (TopCat.toSSet.map (inclUVU S T)) (ModuleCat.of ℤ ℤ) ≫ inclChains M S
      = inclChains M (S ∩ T) := by
  have h : inclUVU S T ≫ subtypeIncl M S = subtypeIncl M (S ∩ T) := by ext x; rfl
  show chainMap ℤ (TopCat.of ↥(S ∩ T)) (TopCat.of S) (inclUVU S T) ≫ inclChains M S
      = inclChains M (S ∩ T)
  rw [show inclChains M S = chainMap ℤ (TopCat.of ↥S) M (subtypeIncl M S) from rfl,
      show inclChains M (S ∩ T) = chainMap ℤ (TopCat.of ↥(S ∩ T)) M (subtypeIncl M (S ∩ T))
        from rfl,
      ← h]
  exact chainMap_comp (TopCat.of ↥(S ∩ T)) (TopCat.of S) M (inclUVU S T) (subtypeIncl M S)

/-- The second component of the Mayer–Vietoris map `C_*(S ∩ T) ⟶ C_*(T)`. -/
lemma chainMap_inclUVV_comp (S T : Set M) :
    SSet.chainComplexMap (TopCat.toSSet.map (inclUVV S T)) (ModuleCat.of ℤ ℤ) ≫ inclChains M T
      = inclChains M (S ∩ T) := by
  have h : inclUVV S T ≫ subtypeIncl M T = subtypeIncl M (S ∩ T) := by ext x; rfl
  show chainMap ℤ (TopCat.of ↥(S ∩ T)) (TopCat.of T) (inclUVV S T) ≫ inclChains M T
      = inclChains M (S ∩ T)
  rw [show inclChains M T = chainMap ℤ (TopCat.of ↥T) M (subtypeIncl M T) from rfl,
      show inclChains M (S ∩ T) = chainMap ℤ (TopCat.of ↥(S ∩ T)) M (subtypeIncl M (S ∩ T))
        from rfl,
      ← h]
  exact chainMap_comp (TopCat.of ↥(S ∩ T)) (TopCat.of T) M (inclUVV S T) (subtypeIncl M T)

/-- The first square of the morphism `mvShort S T ⟶ trivialShort M` commutes. -/
lemma mvToTrivial_comm₁₂ (S T : Set M) :
    inclChains M (S ∩ T) ≫ complDiag M
      = mvLeft S T ≫ biprod.map (inclChains M S) (inclChains M T) := by
  apply biprod.hom_ext
  · conv_lhs => rw [Category.assoc, complDiag, biprod.lift_fst]
    conv_rhs => rw [Category.assoc, biprod.map_fst, ← Category.assoc]
    rw [Category.comp_id]
    rw [show mvLeft S T ≫ (biprod.fst : singularChains ℤ (TopCat.of ↑S) ⊞
          singularChains ℤ (TopCat.of ↑T) ⟶ singularChains ℤ (TopCat.of ↑S))
        = SSet.chainComplexMap (TopCat.toSSet.map (inclUVU S T)) (ModuleCat.of ℤ ℤ)
      from biprod.lift_fst _ _]
    exact (chainMap_inclUVU_comp S T).symm
  · conv_lhs => rw [Category.assoc, complDiag, biprod.lift_snd]
    conv_rhs => rw [Category.assoc, biprod.map_snd, ← Category.assoc]
    rw [Category.comp_id]
    rw [show mvLeft S T ≫ (biprod.snd : singularChains ℤ (TopCat.of ↑S) ⊞
          singularChains ℤ (TopCat.of ↑T) ⟶ singularChains ℤ (TopCat.of ↑T))
        = SSet.chainComplexMap (TopCat.toSSet.map (inclUVV S T)) (ModuleCat.of ℤ ℤ)
      from biprod.lift_snd _ _]
    exact (chainMap_inclUVV_comp S T).symm

/-- The second square of the morphism `mvShort S T ⟶ trivialShort M` commutes. -/
lemma mvToTrivial_comm₂₃ (S T : Set M) :
    biprod.map (inclChains M S) (inclChains M T) ≫ complDiff M
      = mvRight S T ≫ smallToSing S T := by
  apply biprod.hom_ext'
  · conv_lhs => rw [← Category.assoc, biprod.inl_map, Category.assoc]
    conv_rhs => rw [← Category.assoc]
    rw [complDiff, biprod.inl_desc, mvRight, biprod.inl_desc, Category.comp_id,
      smallOfU_comp_smallToSing]
  · conv_lhs => rw [← Category.assoc, biprod.inr_map, Category.assoc]
    conv_rhs => rw [← Category.assoc]
    rw [complDiff, biprod.inr_desc, mvRight, biprod.inr_desc, Preadditive.comp_neg,
      Category.comp_id, Preadditive.neg_comp, smallOfV_comp_smallToSing]

/-- **The morphism of short complexes** from the Mayer–Vietoris sequence of the cover `{S, T}` to
the trivial sequence: the three components are the inclusions of the chains of `S ∩ T`, of
`C_*(S) ⊞ C_*(T)` and of the small chains `C^{S,T}` into the singular chains of `M`. -/
def mvToTrivial (S T : Set M) : mvShort S T ⟶ trivialShort M where
  τ₁ := inclChains M (S ∩ T)
  τ₂ := biprod.map (inclChains M S) (inclChains M T)
  τ₃ := smallToSing S T
  comm₁₂ := mvToTrivial_comm₁₂ S T
  comm₂₃ := mvToTrivial_comm₂₃ S T

/-! ## Two general homological lemmas -/

/-- The homology of a biproduct of chain complexes is the biproduct of the homologies. -/
theorem homology_biprod_iso_chain (C D : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    Nonempty ((C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  exact ⟨F.mapBiprod C D⟩

/-- **If a chain map is a quasi-isomorphism and a monomorphism, the cokernel is acyclic in positive
degrees.** -/
theorem isZero_homology_coker_of_isIso {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L)
    [Mono f] (hiso : ∀ n, IsIso (HomologicalComplex.homologyMap f n)) :
    ∀ k, 1 ≤ k → IsZero ((cokernel f).homology k) := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) ‹Mono f› inferInstance
  have hij : (ComplexShape.down ℕ).Rel (m+1) m := by simp [ComplexShape.down]
  -- the map `H_{m+1}(X₂) ⟶ H_{m+1}(X₃)` is zero, as `H_{m+1}(X₁) ⟶ H_{m+1}(X₂)` is onto
  have hg0 : HomologicalComplex.homologyMap S.g (m+1) = 0 := by
    haveI := hiso (m+1)
    rw [← cancel_epi (HomologicalComplex.homologyMap S.f (m+1)), comp_zero,
      ← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero]
  -- hence the connecting map `δ : H_{m+1}(X₃) ⟶ H_m(X₁)` is injective
  haveI hmonoδ : Mono (hS.δ (m+1) m hij) :=
    ShortComplex.Exact.mono_g (hS.homology_exact₃ (m+1) m hij) hg0
  -- and it is zero, as `H_m(X₁) ⟶ H_m(X₂)` is injective
  have hδ0 : hS.δ (m+1) m hij = 0 := by
    haveI := hiso m
    rw [← cancel_mono (HomologicalComplex.homologyMap S.f m), zero_comp,
      hS.δ_comp (m+1) m hij]
  refine IsZero.iff_id_eq_zero _ |>.mpr ?_
  rw [← cancel_mono (hS.δ (m+1) m hij), Category.id_comp, hδ0, zero_comp]

/-- **The long exact sequence of a short exact sequence of chain complexes in degree `k`, when the
third term has vanishing homology in degrees `k` and `k+1`**: the first map is an isomorphism in
degree `k`. -/
theorem isIso_homologyMap_of_acyclic {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (hS : S.ShortExact) (k : ℕ) (h₁ : IsZero (S.X₃.homology (k+1)))
    (h₂ : IsZero (S.X₃.homology k)) :
    IsIso (HomologicalComplex.homologyMap S.f k) := by
  haveI hmono : Mono (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.mono_g (hS.homology_exact₁ (k+1) k (by simp [ComplexShape.down]))
      (IsZero.eq_zero_of_src h₁ _)
  haveI hepi : Epi (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.epi_f (hS.homology_exact₂ k) (IsZero.eq_zero_of_tgt h₂ _)
  exact isIso_of_mono_of_epi _

/-- An isomorphism of `ModuleCat R` objects, as a linear equivalence of the underlying modules. -/
def complUnionIsoToLinearEquiv {R : Type} [Ring R] {P Q : ModuleCat R} (e : P ≅ Q) :
    ↥P ≃ₗ[R] ↥Q :=
  LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

/-! ## The main argument -/

/-- **Mayer–Vietoris for the complement of a disjoint union** (the auxiliary form stated in terms
of the two open complements `S = Aᶜ`, `T = Bᶜ`).

For open `S, T ⊆ M` with `S ∪ T = univ` (so that `S ∩ T` is the complement of the corresponding
disjoint closed pair), the group `H_N(M, M∖(S∩T))` is free whenever `H_N(M, M∖S)` and
`H_N(M, M∖T)` are. -/
theorem relChains_compl_union_free_aux {N : ℕ} (hN : 1 ≤ N) {M : TopCat} (S T : Set M)
    (hS : IsOpen S) (hT : IsOpen T) (hcov : S ∪ T = Set.univ)
    (hFA : Module.Free ℤ ↥((relChains M S).homology N))
    (hFB : Module.Free ℤ ↥((relChains M T).homology N)) :
    Module.Free ℤ ↥((relChains M (S ∩ T)).homology N) := by
  -- the three components of the morphism of short complexes are monomorphisms
  haveI : Mono (inclChains M S) := mono_chainMap_subtypeIncl M S
  haveI : Mono (inclChains M T) := mono_chainMap_subtypeIncl M T
  haveI hmono1 : Mono ((mvToTrivial S T).τ₁) := mono_chainMap_subtypeIncl M (S ∩ T)
  haveI hmono2 : Mono ((mvToTrivial S T).τ₂) := biprod.map_mono _ _
  haveI hmono3 : Mono (smallToSing S T) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr (smallToSing_f_injective S T n)
  -- the snake lemma: the cokernels form a short exact sequence
  obtain ⟨f, g, hfg, hSE⟩ := cokernel_map_shortExact (mvShort_shortExact S T)
    (trivialShort_shortExact M) (mvToTrivial S T) hmono1 hmono2 hmono3
  -- the quotient by the small chains is acyclic in positive degrees
  have hacyc : ∀ k, 1 ≤ k → IsZero ((cokernel (smallToSing S T)).homology k) :=
    isZero_homology_coker_of_isIso (smallToSing S T)
      (fun n => smallChains_homology_iso S T hS hT hcov n)
  -- hence the first map of the cokernel sequence is an isomorphism in degree `N`
  haveI hisoN : IsIso (HomologicalComplex.homologyMap f N) :=
    isIso_homologyMap_of_acyclic hSE N (hacyc (N+1) (by omega)) (hacyc N hN)
  -- the middle cokernel is the biproduct of the two relative complexes
  obtain ⟨e₂⟩ := cokernel_biprod_map_iso (inclChains M S) (inclChains M T)
  obtain ⟨e₃⟩ := homology_biprod_iso_chain (cokernel (inclChains M S))
    (cokernel (inclChains M T)) N
  have eFull : (cokernel ((mvToTrivial S T).τ₁)).homology N ≅
      (cokernel (inclChains M S)).homology N ⊞ (cokernel (inclChains M T)).homology N :=
    (asIso (HomologicalComplex.homologyMap f N)).trans
      (((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) N).mapIso
        e₂).trans e₃)
  refine Module.Free.of_equiv' ?_ (complUnionIsoToLinearEquiv eFull.symm)
  -- freeness of the biproduct of two free `ℤ`-modules
  haveI hfreeA : Module.Free ℤ ↥((cokernel (inclChains M S)).homology N) := hFA
  haveI hfreeB : Module.Free ℤ ↥((cokernel (inclChains M T)).homology N) := hFB
  let A := (cokernel (inclChains M S)).homology N
  let B := (cokernel (inclChains M T)).homology N
  let S' : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) biprod.inl_snd
  have hS' : S'.ShortExact :=
    ShortComplex.Splitting.shortExact
      { r := (biprod.fst : A ⊞ B ⟶ A)
        s := (biprod.inr : B ⟶ A ⊞ B)
        f_r := biprod.inl_fst
        s_g := biprod.inr_snd
        id := biprod.total }
  exact ModuleCat.free_shortExact hS'

/-- **Mayer–Vietoris for the top relative homology of the complement of a disjoint union.**

Write `F(X) := (relChains M Xᶜ).homology N` for the relative homology `H_N(M, M∖X)` of the
"excluded set" `X` (contravariant in `X`).  If `A` and `B` are closed and disjoint then the
Mayer–Vietoris sequence of the excluded-set functor is `0 → F(A∪B) → F(A) ⊞ F(B) → F(A∩B)`, and
`F(A∩B) = F(∅) = (relChains M Set.univ).homology N = 0` (`Work.Cohomology.isZero_relChains_univ`),
so `F(A∪B) ≅ F(A) ⊞ F(B)` and freeness transfers.  Note `[T2Space M]`, `[ChartedSpace …]` and the
compactness hypotheses are *not* needed for this statement.

It suffices to conclude `Module.Free ℤ ↥(F(A∪B))` from the two freeness hypotheses. -/
theorem relChains_compl_union_free {N : ℕ} (hN : 1 ≤ N) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (A B : Set M) (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) (hAc : IsCompact A) (hBc : IsCompact B)
    (hFA : Module.Free ℤ ↥((Work.Cohomology.relChains M Aᶜ).homology N))
    (hFB : Module.Free ℤ ↥((Work.Cohomology.relChains M Bᶜ).homology N)) :
    Module.Free ℤ ↥((Work.Cohomology.relChains M (A ∪ B)ᶜ).homology N) := by
  have hcov : Aᶜ ∪ Bᶜ = Set.univ := by
    have h : A ∩ B = ∅ := Set.disjoint_iff_inter_eq_empty.mp hAB
    rw [← Set.compl_inter, h, Set.compl_empty]
  rw [Set.compl_union]
  exact relChains_compl_union_free_aux hN Aᶜ Bᶜ hA.isOpen_compl hB.isOpen_compl hcov hFA hFB

end

end Work.Cohomology
