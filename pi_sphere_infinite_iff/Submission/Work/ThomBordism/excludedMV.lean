import Mathlib
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChains_compl_union_free
import Submission.Work.Cohomology.relChains_compl_union_free_of_compact_inter
import Submission.Work.Cohomology.lk_twoSet_homologyMap_isIso
import Submission.Work.Cohomology.CompatTrans.prodSphereAux
import Submission.Work.Whitney.relABQuasiIso

/-!
# The Mayer–Vietoris exactness for the "excluded set" functor

For a topological space `M`, closed subsets `K, L ⊆ M` and a degree `n`, the relative homology
`H_*(M, M∖·)` of the "excluded set" satisfies the Mayer–Vietoris long exact sequence

`⋯ → H_{n+1}(M, M∖(K∩L)) → H_n(M, M∖(K∪L)) → H_n(M, M∖K) ⊕ H_n(M, M∖L)
     → H_n(M, M∖(K∩L)) → ⋯`

This file proves the exactness consequences at degree `n` that are used in the construction of
local orientation classes; the statement `excludedMV` is the two halves of that exactness.

The proof builds the short exact sequence of chain complexes

`0 → C_*(M)/(C_*(S∩T)) → C_*(M)/C_*(S) ⊞ C_*(M)/C_*(T) → C_*(M)/(C_*(S)+C_*(T)) → 0`

(for `S = Kᶜ`, `T = Lᶜ`s) as the cokernel of the morphism `mvToTrivial` between the Mayer–Vietoris
short exact sequence of the cover `{S,T}` and the split sequence of `M`, and compares the third
term with `C_*(M)/C_*(S∪T)` by the small-simplices theorem.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.ThomBordism

open CategoryTheory Limits
open Work.Cohomology
open scoped ZeroObject

noncomputable section

/-- Proof irrelevance for the cokernel maps: the map does not depend on the proof of the inclusion
`A ⊆ B`. -/
theorem relCokerMap_congr_h {M : TopCat} {A B : Set M} (h h' : A ⊆ B) :
    relCokerMap M A B h = relCokerMap M A B h' := by
  apply (cancel_epi (cokernel.π (inclChains M A))).mp
  simp only [relCokerMap_comp_π]

/-- The quotient of the singular chains of `M` by the small chains of the cover `{S,T}`: the third
term `C_*(M)/(C_*(S)+C_*(T))` of the Mayer–Vietoris cokernel sequence. -/
abbrev mvQuot (M : TopCat) (S T : Set M) : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (smallToSing S T)

/-- The canonical map `C_*(M,S) ⟶ C_*(M)/(C_*(S)+C_*(T))`. -/
def kappa (M : TopCat) (S T : Set M) : cokernel (inclChains M S) ⟶ mvQuot M S T :=
  cokernel.desc (inclChains M S) (cokernel.π (smallToSing S T))
    (by rw [← smallOfU_comp_smallToSing S T, Category.assoc, cokernel.condition, comp_zero])

/-- The canonical map `C_*(M,T) ⟶ C_*(M)/(C_*(S)+C_*(T))`. -/
def kappaT (M : TopCat) (S T : Set M) : cokernel (inclChains M T) ⟶ mvQuot M S T :=
  cokernel.desc (inclChains M T) (cokernel.π (smallToSing S T))
    (by rw [← smallOfV_comp_smallToSing S T, Category.assoc, cokernel.condition, comp_zero])

/-- The comparison map `C_*(M)/(C_*(S)+C_*(T)) ⟶ C_*(M,M∖(S∪T))`. -/
def rho (M : TopCat) (S T : Set M) : mvQuot M S T ⟶ cokernel (inclChains M (S ∪ T)) :=
  Work.Whitney.relABq S T

/-- The diagonal Mayer–Vietoris map `C_*(M,S∩T) ⟶ C_*(M,S) ⊞ C_*(M,T)`. -/
def mvLift (M : TopCat) (S T : Set M) (h₁ : S ∩ T ⊆ S) (h₂ : S ∩ T ⊆ T) :
    cokernel (inclChains M (S ∩ T)) ⟶
      cokernel (inclChains M S) ⊞ cokernel (inclChains M T) :=
  biprod.lift (relCokerMap M (S ∩ T) S h₁) (relCokerMap M (S ∩ T) T h₂)

/-- The difference map `C_*(M,S) ⊞ C_*(M,T) ⟶ C_*(M)/(C_*(S)+C_*(T))`. -/
def mvDesc (M : TopCat) (S T : Set M) :
    cokernel (inclChains M S) ⊞ cokernel (inclChains M T) ⟶ mvQuot M S T :=
  biprod.desc (kappa M S T) (-(kappaT M S T))

/-- The first map of the cokernel of the Mayer–Vietoris `mvToTrivial` morphism. -/
def cokerMap₁ (M : TopCat) (S T : Set M) :
    cokernel (inclChains M (S ∩ T)) ⟶ cokernel (biprod.map (inclChains M S) (inclChains M T)) :=
  cokernel.map (inclChains M (S ∩ T)) (biprod.map (inclChains M S) (inclChains M T))
    (mvLeft S T) (complDiag M) (mvToTrivial_comm₁₂ S T)

/-- The second map of the cokernel of the Mayer–Vietoris `mvToTrivial` morphism. -/
def cokerMap₂ (M : TopCat) (S T : Set M) :
    cokernel (biprod.map (inclChains M S) (inclChains M T)) ⟶ mvQuot M S T :=
  cokernel.map (biprod.map (inclChains M S) (inclChains M T)) (smallToSing S T)
    (mvRight S T) (complDiff M) (mvToTrivial_comm₂₃ S T)

theorem biprod_desc_comp_h {C : Type} [Category C] [Preadditive C] {A B X Y : C}
    [HasBinaryBiproduct A B] (f : A ⟶ X) (g : B ⟶ X) (h : X ⟶ Y) :
    biprod.desc f g ≫ h = biprod.desc (f ≫ h) (g ≫ h) := by
  apply biprod.hom_ext'
  · simp only [← Category.assoc, biprod.inl_desc]
  · simp only [← Category.assoc, biprod.inr_desc]

theorem comp_biprod_lift_h {C : Type} [Category C] [HasZeroMorphisms C] {X W Y Z : C}
    [HasBinaryBiproduct Y Z] (c : X ⟶ W) (a : W ⟶ Y) (b : W ⟶ Z) :
    c ≫ biprod.lift a b = biprod.lift (c ≫ a) (c ≫ b) := by
  apply biprod.hom_ext <;> simp [Category.assoc]

theorem complDiag_map_eq_lift_h {M : TopCat} {A B : Set M}
    (p : singularChains ℤ M ⟶ cokernel (inclChains M A))
    (q : singularChains ℤ M ⟶ cokernel (inclChains M B)) :
    complDiag M ≫ biprod.map p q = biprod.lift p q := by
  apply biprod.hom_ext <;> simp [complDiag]

theorem pi_comp_rho (M : TopCat) (S T : Set M) :
    cokernel.π (smallToSing S T) ≫ rho M S T = cokernel.π (inclChains M (S ∪ T)) := by
  rw [rho, Work.Whitney.relABq, cokernel.π_desc]

theorem kappa_comp_rho (M : TopCat) (S T : Set M) :
    kappa M S T ≫ rho M S T = relCokerMap M S (S ∪ T) Set.subset_union_left := by
  apply (cancel_epi (cokernel.π (inclChains M S))).mp
  rw [← Category.assoc, kappa, cokernel.π_desc, pi_comp_rho, relCokerMap_comp_π]

theorem kappaT_comp_rho (M : TopCat) (S T : Set M) :
    kappaT M S T ≫ rho M S T = relCokerMap M T (S ∪ T) Set.subset_union_right := by
  apply (cancel_epi (cokernel.π (inclChains M T))).mp
  rw [← Category.assoc, kappaT, cokernel.π_desc, pi_comp_rho, relCokerMap_comp_π]

theorem mvDesc_comp_rho (M : TopCat) (S T : Set M) :
    mvDesc M S T ≫ rho M S T
      = biprod.desc (relCokerMap M S (S ∪ T) Set.subset_union_left)
          (-(relCokerMap M T (S ∪ T) Set.subset_union_right)) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, mvDesc, biprod.inl_desc, kappa_comp_rho, biprod.inl_desc]
  · rw [← Category.assoc, mvDesc, biprod.inr_desc, Preadditive.neg_comp, kappaT_comp_rho,
      biprod.inr_desc]

theorem cokerMap_comp_zero (M : TopCat) (S T : Set M) :
    cokerMap₁ M S T ≫ cokerMap₂ M S T = 0 := by
  have hπf : cokernel.π (inclChains M (S ∩ T)) ≫ cokerMap₁ M S T
      = complDiag M ≫ cokernel.π (biprod.map (inclChains M S) (inclChains M T)) := by
    simp only [cokerMap₁, cokernel.map, cokernel.π_desc]
  have hπg : cokernel.π (biprod.map (inclChains M S) (inclChains M T)) ≫ cokerMap₂ M S T
      = complDiff M ≫ cokernel.π (smallToSing S T) := by
    simp only [cokerMap₂, cokernel.map, cokernel.π_desc]
  rw [← cancel_epi (cokernel.π (inclChains M (S ∩ T))), comp_zero, ← Category.assoc, hπf,
    Category.assoc, hπg, ← Category.assoc, complDiag_comp_complDiff, zero_comp]

/-- The cokernel of the morphism `mvToTrivial` of Mayer–Vietoris short complexes. -/
abbrev cokerComplex (M : TopCat) (S T : Set M) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (cokerMap₁ M S T) (cokerMap₂ M S T) (cokerMap_comp_zero M S T)

/-- **The cokernel of the `mvToTrivial` morphism is short exact.** -/
theorem cokerComplex_shortExact (M : TopCat) (S T : Set M) :
    (cokerComplex M S T).ShortExact := by
  haveI : Mono (inclChains M S) := mono_chainMap_subtypeIncl M S
  haveI : Mono (inclChains M T) := mono_chainMap_subtypeIncl M T
  haveI hmono1 : Mono ((mvToTrivial S T).τ₁) := mono_chainMap_subtypeIncl M (S ∩ T)
  haveI hmono2 : Mono ((mvToTrivial S T).τ₂) := biprod.map_mono _ _
  haveI hmono3 : Mono ((mvToTrivial S T).τ₃) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact (ModuleCat.mono_iff_injective _).mpr (smallToSing_f_injective S T n)
  let f := cokerMap₁ M S T
  let g := cokerMap₂ M S T
  have hπf : cokernel.π (inclChains M (S ∩ T)) ≫ f
      = complDiag M ≫ cokernel.π (biprod.map (inclChains M S) (inclChains M T)) := by
    simp only [f, cokerMap₁, cokernel.map, cokernel.π_desc]
  have hπg : cokernel.π (biprod.map (inclChains M S) (inclChains M T)) ≫ g
      = complDiff M ≫ cokernel.π (smallToSing S T) := by
    simp only [g, cokerMap₂, cokernel.map, cokernel.π_desc]
  have hfg : f ≫ g = 0 := by
    rw [← cancel_epi (cokernel.π (inclChains M (S ∩ T))), comp_zero, ← Category.assoc, hπf,
      Category.assoc, hπg, ← Category.assoc, complDiag_comp_complDiff, zero_comp]
  let C₀ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := ShortComplex.mk f g hfg
  let φ : trivialShort M ⟶ C₀ := ShortComplex.homMk (cokernel.π (inclChains M (S ∩ T)))
    (cokernel.π (biprod.map (inclChains M S) (inclChains M T))) (cokernel.π (smallToSing S T))
    hπf hπg
  have w₁₃ : mvToTrivial S T ≫ φ = 0 := by
    apply ShortComplex.hom_ext
    · rw [ShortComplex.comp_τ₁, ShortComplex.zero_τ₁]
      show (mvToTrivial S T).τ₁ ≫ cokernel.π ((mvToTrivial S T).τ₁) = 0
      exact cokernel.condition _
    · rw [ShortComplex.comp_τ₂, ShortComplex.zero_τ₂]
      show (mvToTrivial S T).τ₂ ≫ cokernel.π ((mvToTrivial S T).τ₂) = 0
      exact cokernel.condition _
    · rw [ShortComplex.comp_τ₃, ShortComplex.zero_τ₃]
      show (mvToTrivial S T).τ₃ ≫ cokernel.π ((mvToTrivial S T).τ₃) = 0
      exact cokernel.condition _
  let sn : ShortComplex.SnakeInput (ChainComplex (ModuleCat ℤ) ℕ) :=
    { L₀ := ShortComplex.mk (0 : (0 : ChainComplex (ModuleCat ℤ) ℕ) ⟶ 0)
        (0 : (0 : ChainComplex (ModuleCat ℤ) ℕ) ⟶ 0) (by simp)
      L₁ := mvShort S T
      L₂ := trivialShort M
      L₃ := C₀
      v₀₁ := 0
      v₁₂ := mvToTrivial S T
      v₂₃ := φ
      w₀₂ := by simp
      w₁₃ := w₁₃
      h₀ := by
        apply ShortComplex.isLimitOfIsLimitπ
        · exact (KernelFork.isLimitMapConeEquiv _ _).2
            (kernel.isLimitConeZeroCone (mvToTrivial S T).τ₁)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2
            (kernel.isLimitConeZeroCone (mvToTrivial S T).τ₂)
        · exact (KernelFork.isLimitMapConeEquiv _ _).2
            (kernel.isLimitConeZeroCone (mvToTrivial S T).τ₃)
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2
            (cokernelIsCokernel (mvToTrivial S T).τ₁)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2
            (cokernelIsCokernel (mvToTrivial S T).τ₂)
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).2
            (cokernelIsCokernel (mvToTrivial S T).τ₃)
      L₁_exact := (mvShort_shortExact S T).exact
      epi_L₁_g := (mvShort_shortExact S T).epi_g
      L₂_exact := (trivialShort_shortExact M).exact
      mono_L₂_f := (trivialShort_shortExact M).mono_f }
  have hex : C₀.Exact := sn.L₃_exact
  have hg : Epi sn.L₂.g := (trivialShort_shortExact M).epi_g
  have hepi : Epi g := sn.epi_L₃_g
  have hδ : sn.δ = 0 := IsZero.eq_zero_of_src (X := sn.L₀.X₃)
    (isZero_zero (ChainComplex (ModuleCat ℤ) ℕ)) sn.δ
  have hmono : Mono f := ShortComplex.Exact.mono_g sn.L₂'_exact hδ
  exact ShortComplex.ShortExact.mk' hex hmono hepi


lemma complDiff_comp_h {M : TopCat} {X : ChainComplex (ModuleCat ℤ) ℕ}
    (π : singularChains ℤ M ⟶ X) : complDiff M ≫ π = biprod.desc π (-π) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, complDiff, biprod.inl_desc, Category.id_comp, biprod.inl_desc]
  · rw [← Category.assoc, complDiff, biprod.inr_desc, Preadditive.neg_comp, Category.id_comp,
      biprod.inr_desc]

lemma biprod_map_mvDesc_h (M : TopCat) (S T : Set M) :
    biprod.map (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T)) ≫ mvDesc M S T
      = biprod.desc (cokernel.π (smallToSing S T)) (-(cokernel.π (smallToSing S T))) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, biprod.inl_map, Category.assoc, mvDesc, biprod.inl_desc]
    rw [show cokernel.π (inclChains M S) ≫ kappa M S T = cokernel.π (smallToSing S T) from
      cokernel.π_desc _ _ _, biprod.inl_desc]
  · rw [← Category.assoc, biprod.inr_map, Category.assoc, mvDesc, biprod.inr_desc]
    rw [Preadditive.comp_neg, show cokernel.π (inclChains M T) ≫ kappaT M S T
        = cokernel.π (smallToSing S T) from cokernel.π_desc _ _ _, biprod.inr_desc]

/-- The identification of the diagonal Mayer–Vietoris map with the first map of the cokernel
sequence, transported across the canonical isomorphism of the middle term with the biproduct. -/
theorem mvLift_eq_cokerMap₁ (M : TopCat) (S T : Set M) (h₁ : S ∩ T ⊆ S) (h₂ : S ∩ T ⊆ T)
    (e : cokernel (biprod.map (inclChains M S) (inclChains M T)) ≅
      cokernel (inclChains M S) ⊞ cokernel (inclChains M T))
    (he : cokernel.π (biprod.map (inclChains M S) (inclChains M T)) ≫ e.hom
      = biprod.map (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T))) :
    mvLift M S T h₁ h₂ = cokerMap₁ M S T ≫ e.hom := by
  apply (cancel_epi (cokernel.π (inclChains M (S ∩ T)))).mp
  have hL : cokernel.π (inclChains M (S ∩ T)) ≫ mvLift M S T h₁ h₂
      = biprod.lift (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T)) := by
    rw [mvLift]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, relCokerMap_comp_π]
    · simp only [Category.assoc, biprod.lift_snd, relCokerMap_comp_π]
  have hR : cokernel.π (inclChains M (S ∩ T)) ≫ (cokerMap₁ M S T ≫ e.hom)
      = biprod.lift (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T)) := by
    rw [← Category.assoc]
    rw [show cokernel.π (inclChains M (S ∩ T)) ≫ cokerMap₁ M S T
        = complDiag M ≫ cokernel.π (biprod.map (inclChains M S) (inclChains M T)) from by
      simp only [cokerMap₁, cokernel.map, cokernel.π_desc]]
    rw [Category.assoc, he, complDiag_map_eq_lift_h]
  rw [hL, hR]

/-- The identification of the difference map with the second map of the cokernel sequence,
transported across the canonical isomorphism of the middle term with the biproduct. -/
theorem mvDesc_eq_inv_comp_cokerMap₂ (M : TopCat) (S T : Set M)
    (e : cokernel (biprod.map (inclChains M S) (inclChains M T)) ≅
      cokernel (inclChains M S) ⊞ cokernel (inclChains M T))
    (he : cokernel.π (biprod.map (inclChains M S) (inclChains M T)) ≫ e.hom
      = biprod.map (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T))) :
    mvDesc M S T = e.inv ≫ cokerMap₂ M S T := by
  apply (cancel_epi (biprod.map (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T)))).mp
  have hA : biprod.map (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T))
      ≫ (e.inv ≫ cokerMap₂ M S T)
      = biprod.desc (cokernel.π (smallToSing S T)) (-(cokernel.π (smallToSing S T))) := by
    rw [← he, Category.assoc, Iso.hom_inv_id_assoc]
    rw [show cokernel.π (biprod.map (inclChains M S) (inclChains M T)) ≫ cokerMap₂ M S T
        = complDiff M ≫ cokernel.π (smallToSing S T) from by
      simp only [cokerMap₂, cokernel.map, cokernel.π_desc]]
    exact complDiff_comp_h (cokernel.π (smallToSing S T))
  rw [biprod_map_mvDesc_h M S T, hA]

theorem mvLift_comp_mvDesc (M : TopCat) (S T : Set M) (h₁ : S ∩ T ⊆ S) (h₂ : S ∩ T ⊆ T) :
    mvLift M S T h₁ h₂ ≫ mvDesc M S T = 0 := by
  have hlift : cokernel.π (inclChains M (S ∩ T)) ≫ mvLift M S T h₁ h₂
      = biprod.lift (cokernel.π (inclChains M S)) (cokernel.π (inclChains M T)) := by
    rw [mvLift]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, relCokerMap_comp_π]
    · simp only [Category.assoc, biprod.lift_snd, relCokerMap_comp_π]
  rw [← cancel_epi (cokernel.π (inclChains M (S ∩ T))), comp_zero, ← Category.assoc]
  rw [hlift, mvDesc, biprod.lift_desc]
  rw [Preadditive.comp_neg,
      show cokernel.π (inclChains M S) ≫ kappa M S T = cokernel.π (smallToSing S T) from
        cokernel.π_desc _ _ _,
      show cokernel.π (inclChains M T) ≫ kappaT M S T = cokernel.π (smallToSing S T) from
        cokernel.π_desc _ _ _]
  simp

/-- The Mayer–Vietoris complex `0 → C_*(M,S∩T) → C_*(M,S) ⊞ C_*(M,T) → C_*(M)/(C_S+C_T) → 0`
with the biproduct as the middle term. -/
abbrev mvComplex (M : TopCat) (S T : Set M) (h₁ : S ∩ T ⊆ S) (h₂ : S ∩ T ⊆ T) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (mvLift M S T h₁ h₂) (mvDesc M S T) (mvLift_comp_mvDesc M S T h₁ h₂)

/-- **The Mayer–Vietoris complex is short exact.** -/
theorem mvComplex_shortExact (M : TopCat) (S T : Set M) (h₁ : S ∩ T ⊆ S) (h₂ : S ∩ T ⊆ T) :
    (mvComplex M S T h₁ h₂).ShortExact := by
  obtain ⟨e, he⟩ := cokernelBiprodMapIsoChar (inclChains M S) (inclChains M T)
  have hJ := mvLift_eq_cokerMap₁ M S T h₁ h₂ e he
  have hK := mvDesc_eq_inv_comp_cokerMap₂ M S T e he
  have hcomm1 : (Iso.refl (cokernel (inclChains M (S ∩ T)))).hom ≫ (mvComplex M S T h₁ h₂).f
      = (cokerComplex M S T).f ≫ e.hom := by
    show 𝟙 _ ≫ mvLift M S T h₁ h₂ = cokerMap₁ M S T ≫ e.hom
    rw [Category.id_comp]
    exact hJ
  have hcomm2 : e.hom ≫ (mvComplex M S T h₁ h₂).g
      = (cokerComplex M S T).g ≫ (Iso.refl (mvQuot M S T)).hom := by
    show e.hom ≫ mvDesc M S T = cokerMap₂ M S T ≫ 𝟙 _
    rw [Category.comp_id, hK, Iso.hom_inv_id_assoc]
  have hiso : cokerComplex M S T ≅ mvComplex M S T h₁ h₂ :=
    ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) hcomm1 hcomm2
  have hex : (mvComplex M S T h₁ h₂).Exact :=
    (ShortComplex.exact_iff_of_iso hiso).mp (cokerComplex_shortExact M S T).exact
  haveI hmonof : Mono (cokerMap₁ M S T) := (cokerComplex_shortExact M S T).mono_f
  haveI hepig : Epi (cokerMap₂ M S T) := (cokerComplex_shortExact M S T).epi_g
  haveI : Mono (mvLift M S T h₁ h₂) := by rw [hJ]; infer_instance
  haveI : Epi (mvDesc M S T) := by rw [hK]; infer_instance
  exact ShortComplex.ShortExact.mk' hex inferInstance inferInstance

/-! ## The corestriction of the small chains of the cover is a quasi-isomorphism -/

/-- **The corestriction `C^{S,T}_*(M) ⟶ C_*(S∪T)` of the small chains of the cover `{S,T}` is a
quasi-isomorphism** (for `S, T` open). -/
theorem isIso_homologyMap_relABPhi {M : TopCat} {S T : Set M} (hS : IsOpen S) (hT : IsOpen T)
    (m : ℕ) : IsIso (HomologicalComplex.homologyMap (Work.Whitney.relABPhi S T) m) := by
  have hfac : Work.Whitney.relABPhi S T
      = SSet.chainComplexMap (Work.Whitney.relABUnionToSmall S T) (ModuleCat.of ℤ ℤ)
        ≫ coverToSing S T := by
    have h1 : Work.Whitney.relABUnionToSing S T
        = Work.Whitney.relABUnionToSmall S T
          ≫ (smallSubcomplex (Work.Whitney.relABTraceU S T)
              (Work.Whitney.relABTraceV S T)).ι :=
      (SSet.Subcomplex.lift_ι _ _).symm
    rw [Work.Whitney.relABPhi, h1]
    change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
          (Work.Whitney.relABUnionToSmall S T
            ≫ (smallSubcomplex (Work.Whitney.relABTraceU S T)
                (Work.Whitney.relABTraceV S T)).ι)
        = ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
            (Work.Whitney.relABUnionToSmall S T)
          ≫ ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
              (smallSubcomplex (Work.Whitney.relABTraceU S T)
                (Work.Whitney.relABTraceV S T)).ι
    rw [Functor.map_comp]
  rw [hfac, HomologicalComplex.homologyMap_comp]
  haveI hisoSS : IsIso (Work.Whitney.relABUnionToSmall S T) :=
    ⟨Work.Whitney.relABUnionOfSmall S T, Work.Whitney.relABUnionToSmall_hom_inv S T,
      Work.Whitney.relABUnionOfSmall_inv_hom S T⟩
  haveI : IsIso (SSet.chainComplexMap (Work.Whitney.relABUnionToSmall S T) (ModuleCat.of ℤ ℤ)) := by
    change IsIso (((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (Work.Whitney.relABUnionToSmall S T))
    exact Functor.map_isIso _ _
  haveI : IsIso (HomologicalComplex.homologyMap (coverToSing S T) m) :=
    smallChains_homology_iso (X := coverY S T) (smallCoverU S T) (smallCoverV S T)
      (isOpen_smallCoverU hS) (isOpen_smallCoverV hT) (smallCoverU_union_smallCoverV S T) m
  infer_instance

/-- **The comparison map `C_*(M)/(C_*(S)+C_*(T)) ⟶ C_*(M,M∖(S∪T))` is a quasi-isomorphism** (for
`S, T` open): the kernel is the quotient of the chains of `S∪T` by the small chains of the cover,
which is acyclic by the small-simplices theorem. -/
theorem isIso_homologyMap_relABq {M : TopCat} {S T : Set M} (hS : IsOpen S) (hT : IsOpen T)
    (m : ℕ) : IsIso (HomologicalComplex.homologyMap (Work.Whitney.relABq S T) m) := by
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallToSing S T) (cokernel.π (smallToSing S T)) (cokernel.condition _)
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) (Work.Whitney.mono_smallToSing S T)
      (inferInstance : Epi (cokernel.π (smallToSing S T)))
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) := hPairShort M (S ∪ T)
  have hS₂ : S₂.ShortExact := hPairShort_shortExact M (S ∪ T)
  have hcomm1 : Work.Whitney.relABPhi S T ≫ S₂.f = S₁.f ≫ 𝟙 S₁.X₂ := by
    rw [Category.comp_id]
    exact Work.Whitney.relABPhi_comp_incl' S T
  have hcomm2 : (𝟙 S₁.X₂) ≫ S₂.g = S₁.g ≫ Work.Whitney.relABq S T := by
    rw [Category.id_comp]
    show cokernel.π (inclChains M (S ∪ T)) = cokernel.π (smallToSing S T) ≫ Work.Whitney.relABq S T
    rw [show Work.Whitney.relABq S T = cokernel.desc (smallToSing S T)
        (cokernel.π (inclChains M (S ∪ T))) _ from rfl, cokernel.π_desc]
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk (Work.Whitney.relABPhi S T) (𝟙 S₁.X₂)
    (Work.Whitney.relABq S T) hcomm1 hcomm2
  have h1 : Epi (HomologicalComplex.homologyMap φ.τ₁ m) := by
    rw [show φ.τ₁ = Work.Whitney.relABPhi S T from rfl]
    haveI := isIso_homologyMap_relABPhi (M := M) hS hT m
    infer_instance
  have h2 : IsIso (HomologicalComplex.homologyMap φ.τ₂ m) := by
    rw [show φ.τ₂ = 𝟙 S₁.X₂ from rfl, HomologicalComplex.homologyMap_id]
    infer_instance
  have h3 : ∀ j, (ComplexShape.down ℕ).Rel m j → IsIso (HomologicalComplex.homologyMap φ.τ₁ j) := by
    intro j _
    rw [show φ.τ₁ = Work.Whitney.relABPhi S T from rfl]
    exact isIso_homologyMap_relABPhi (M := M) hS hT j
  have h4 : ∀ j, (ComplexShape.down ℕ).Rel m j → Mono (HomologicalComplex.homologyMap φ.τ₂ j) := by
    intro j _
    rw [show φ.τ₂ = 𝟙 S₁.X₂ from rfl, HomologicalComplex.homologyMap_id]
    infer_instance
  have hres := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ m h1 h2 h3 h4
  rwa [show φ.τ₃ = Work.Whitney.relABq S T from rfl] at hres

/-! ## Elementwise lemmas about the homology of a biproduct -/

lemma biprod_lift_apply_fst_h {X M N : ModuleCat ℤ} (f : X ⟶ M) (g : X ⟶ N) (x : X) :
    (biprod.fst : M ⊞ N ⟶ M) ((biprod.lift f g : X ⟶ M ⊞ N) x) = f x := by
  rw [← ModuleCat.comp_apply, biprod.lift_fst]

lemma biprod_lift_apply_snd_h {X M N : ModuleCat ℤ} (f : X ⟶ M) (g : X ⟶ N) (x : X) :
    (biprod.snd : M ⊞ N ⟶ N) ((biprod.lift f g : X ⟶ M ⊞ N) x) = g x := by
  rw [← ModuleCat.comp_apply, biprod.lift_snd]

lemma biprod_lift_apply_eq_h {X M N : ModuleCat ℤ} (f : X ⟶ M) (g : X ⟶ N) (x : X) :
    (biprod.lift f g : X ⟶ M ⊞ N) x
      = (biprod.inl : M ⟶ M ⊞ N) (f x) + (biprod.inr : N ⟶ M ⊞ N) (g x) := by
  apply Work.Cohomology.biprod_ext_apply
  · rw [map_add, Work.Cohomology.biprod_fst_inl_apply, Work.Cohomology.biprod_fst_inr_apply,
      add_zero]
    exact biprod_lift_apply_fst_h f g x
  · rw [map_add, Work.Cohomology.biprod_snd_inl_apply, Work.Cohomology.biprod_snd_inr_apply,
      zero_add]
    exact biprod_lift_apply_snd_h f g x

lemma biprod_lift_apply_eq_zero_h {X M N : ModuleCat ℤ} (f : X ⟶ M) (g : X ⟶ N) (x : X) :
    (biprod.lift f g : X ⟶ M ⊞ N) x = 0 ↔ f x = 0 ∧ g x = 0 := by
  constructor
  · intro h
    exact ⟨by rw [← biprod_lift_apply_fst_h f g x, h, map_zero],
      by rw [← biprod_lift_apply_snd_h f g x, h, map_zero]⟩
  · rintro ⟨h1, h2⟩
    rw [biprod_lift_apply_eq_h, h1, h2, map_zero, map_zero, add_zero]

lemma homologyMap_biprod_lift_apply_h {K C D : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (u : K ⟶ C) (v : K ⟶ D) (x : K.homology n) :
    (homologyBiprodIso C D n).hom ((HomologicalComplex.homologyMap (biprod.lift u v) n) x)
      = (biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n)
          ((HomologicalComplex.homologyMap u n) x)
        + (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n)
          ((HomologicalComplex.homologyMap v n) x) := by
  have h := congrArg (fun (φ : K.homology n ⟶ C.homology n ⊞ D.homology n) => φ x)
    (homologyMap_biprod_lift K C D n u v)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [biprod_lift_apply_eq_h] at h
  exact h

lemma homologyMap_biprod_lift_eq_zero_h {K C D : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (u : K ⟶ C) (v : K ⟶ D) (x : K.homology n)
    (h1 : (HomologicalComplex.homologyMap u n) x = 0)
    (h2 : (HomologicalComplex.homologyMap v n) x = 0) :
    (HomologicalComplex.homologyMap (biprod.lift u v) n) x = 0 := by
  refine (ModuleCat.mono_iff_injective (homologyBiprodIso C D n).hom).mp
    (inferInstance : Mono (homologyBiprodIso C D n).hom) ?_
  rw [map_zero, homologyMap_biprod_lift_apply_h n u v x, h1, h2, map_zero, map_zero, add_zero]

/-- The inverse of the biproduct-homology isomorphism followed by the homology of a difference map
is the difference of the homologies. -/
lemma homologyBiprodIso_inv_comp_desc_h {C D R : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (f : C ⟶ R) (g : D ⟶ R) :
    (homologyBiprodIso C D n).inv ≫ HomologicalComplex.homologyMap (biprod.desc f g) n
      = biprod.desc (HomologicalComplex.homologyMap f n) (HomologicalComplex.homologyMap g n) := by
  have hinl : (biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n)
      ≫ (homologyBiprodIso C D n).inv
      = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) n := by
    rw [← homologyMap_inl_comp_homologyBiprodIso, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hinr : (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n)
      ≫ (homologyBiprodIso C D n).inv
      = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) n := by
    rw [← homologyMap_inr_comp_homologyBiprodIso, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  apply biprod.hom_ext'
  · rw [← Category.assoc, hinl, ← HomologicalComplex.homologyMap_comp, biprod.inl_desc,
      biprod.inl_desc]
  · rw [← Category.assoc, hinr, ← HomologicalComplex.homologyMap_comp, biprod.inr_desc,
      biprod.inr_desc]

lemma homologyBiprodIso_inv_desc_apply_h {C D R : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ)
    (f : C ⟶ R) (g : D ⟶ R) (x : C.homology n) (y : D.homology n) :
    (HomologicalComplex.homologyMap (biprod.desc f g) n)
        ((homologyBiprodIso C D n).inv
          ((biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n) x
            + (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n) y))
      = (HomologicalComplex.homologyMap f n) x + (HomologicalComplex.homologyMap g n) y := by
  have h := congrArg (fun (φ : C.homology n ⊞ D.homology n ⟶ R.homology n) =>
      φ ((biprod.inl : C.homology n ⟶ C.homology n ⊞ D.homology n) x
        + (biprod.inr : D.homology n ⟶ C.homology n ⊞ D.homology n) y))
    (homologyBiprodIso_inv_comp_desc_h n f g)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [Work.Cohomology.biprod_desc_inl_add_inr] at h
  exact h

/-! ## The Mayer–Vietoris exactness for the excluded-set functor -/

theorem excludedMV_aux (n : ℕ) (M : TopCat) (S T W U : Set M)
    (hS : IsOpen S) (hT : IsOpen T)
    (hWS : W ⊆ S) (hWT : W ⊆ T) (hW : W = S ∩ T)
    (hSU : S ⊆ U) (hTU : T ⊆ U) (hU : U = S ∪ T)
    (hzero : CategoryTheory.Limits.IsZero ((cokernel (inclChains M U)).homology (n+1))) :
    (∀ u : (cokernel (inclChains M W)).homology n,
        (HomologicalComplex.homologyMap (relCokerMap M W S hWS) n).hom u = 0 →
        (HomologicalComplex.homologyMap (relCokerMap M W T hWT) n).hom u = 0 → u = 0) ∧
    (∀ a : (cokernel (inclChains M S)).homology n, ∀ b : (cokernel (inclChains M T)).homology n,
        (HomologicalComplex.homologyMap (relCokerMap M S U hSU) n).hom a =
          (HomologicalComplex.homologyMap (relCokerMap M T U hTU) n).hom b →
        ∃ u : (cokernel (inclChains M W)).homology n,
          (HomologicalComplex.homologyMap (relCokerMap M W S hWS) n).hom u = a ∧
          (HomologicalComplex.homologyMap (relCokerMap M W T hWT) n).hom u = b) := by
  subst hW
  subst hU
  have hSES : (mvComplex M S T hWS hWT).ShortExact := mvComplex_shortExact M S T hWS hWT
  have hE : IsZero ((mvQuot M S T).homology (n+1)) :=
    isZero_coker_smallToSing_of_isZero_relChains S T hS hT n hzero
  haveI hρiso : IsIso (HomologicalComplex.homologyMap (rho M S T) n) :=
    isIso_homologyMap_relABq hS hT n
  haveI hρmono : Mono (HomologicalComplex.homologyMap (rho M S T) n) := inferInstance
  refine ⟨?_, ?_⟩
  · intro u h1u h2u
    haveI hmono : Mono (HomologicalComplex.homologyMap (mvLift M S T hWS hWT) n) := by
      have hij : (ComplexShape.down ℕ).Rel (n+1) n := by simp [ComplexShape.down]
      have hδ : hSES.δ (n+1) n hij = 0 := IsZero.eq_zero_of_src hE _
      exact ShortComplex.Exact.mono_g (hSES.homology_exact₁ (n+1) n hij) hδ
    have hu : (HomologicalComplex.homologyMap (mvLift M S T hWS hWT) n) u = 0 :=
      homologyMap_biprod_lift_eq_zero_h n (relCokerMap M (S ∩ T) S hWS)
        (relCokerMap M (S ∩ T) T hWT) u h1u h2u
    exact (ModuleCat.mono_iff_injective _).mp hmono (by rw [hu, map_zero])
  · intro a b hab
    have hab' : (HomologicalComplex.homologyMap
          (relCokerMap M S (S ∪ T) Set.subset_union_left) n).hom a =
        (HomologicalComplex.homologyMap
          (relCokerMap M T (S ∪ T) Set.subset_union_right) n).hom b := by
      have h1 : (HomologicalComplex.homologyMap
            (relCokerMap M S (S ∪ T) Set.subset_union_left) n).hom =
          (HomologicalComplex.homologyMap (relCokerMap M S (S ∪ T) hSU) n).hom := by
        rw [relCokerMap_congr_h Set.subset_union_left hSU]
      have h2 : (HomologicalComplex.homologyMap
            (relCokerMap M T (S ∪ T) Set.subset_union_right) n).hom =
          (HomologicalComplex.homologyMap (relCokerMap M T (S ∪ T) hTU) n).hom := by
        rw [relCokerMap_congr_h Set.subset_union_right hTU]
      rw [h1, h2]; exact hab
    let eH := homologyBiprodIso (cokernel (inclChains M S)) (cokernel (inclChains M T)) n
    let x : (cokernel (inclChains M S) ⊞ cokernel (inclChains M T)).homology n :=
      eH.inv ((biprod.inl : (cokernel (inclChains M S)).homology n ⟶
            (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) a
          + (biprod.inr : (cokernel (inclChains M T)).homology n ⟶
            (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) b)
    have heHx : eH.hom x = (biprod.inl : (cokernel (inclChains M S)).homology n ⟶
            (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) a
          + (biprod.inr : (cokernel (inclChains M T)).homology n ⟶
            (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) b :=
      Iso.inv_hom_id_apply eH _
    have hxzero : (HomologicalComplex.homologyMap (mvDesc M S T) n) x = 0 := by
      refine (ModuleCat.mono_iff_injective
        (HomologicalComplex.homologyMap (rho M S T) n)).mp hρmono ?_
      rw [map_zero, ← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
        mvDesc_comp_rho]
      rw [homologyBiprodIso_inv_desc_apply_h n
        (relCokerMap M S (S ∪ T) Set.subset_union_left)
        (-(relCokerMap M T (S ∪ T) Set.subset_union_right)) a b]
      rw [HomologicalComplex.homologyMap_neg]
      rw [show (ConcreteCategory.hom (-(HomologicalComplex.homologyMap
            (relCokerMap M T (S ∪ T) Set.subset_union_right) n))) b =
          -((HomologicalComplex.homologyMap
            (relCokerMap M T (S ∪ T) Set.subset_union_right) n)) b from rfl]
      rw [hab', add_neg_cancel]
    have hxmem : x ∈ LinearMap.range
        (HomologicalComplex.homologyMap (mvLift M S T hWS hWT) n).hom := by
      rw [ShortComplex.Exact.moduleCat_range_eq_ker (hSES.homology_exact₂ n), LinearMap.mem_ker]
      exact hxzero
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hxmem
    have hu' : (HomologicalComplex.homologyMap (biprod.lift (relCokerMap M (S ∩ T) S hWS)
        (relCokerMap M (S ∩ T) T hWT)) n) u = x := hu
    refine ⟨u, ?_, ?_⟩
    · have h := homologyMap_biprod_lift_apply_h n (relCokerMap M (S ∩ T) S hWS)
        (relCokerMap M (S ∩ T) T hWT) u
      have hfst := congrArg (fun z => (biprod.fst : (cokernel (inclChains M S)).homology n ⊞
        (cokernel (inclChains M T)).homology n ⟶ (cokernel (inclChains M S)).homology n) z) h
      rw [LinearMap.map_add, Work.Cohomology.biprod_fst_inl_apply,
        Work.Cohomology.biprod_fst_inr_apply, add_zero] at hfst
      rw [hu', heHx] at hfst
      have hfq : (biprod.fst : (cokernel (inclChains M S)).homology n ⊞
            (cokernel (inclChains M T)).homology n ⟶ (cokernel (inclChains M S)).homology n)
          ((biprod.inl : (cokernel (inclChains M S)).homology n ⟶
              (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) a
            + (biprod.inr : (cokernel (inclChains M T)).homology n ⟶
              (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) b)
          = a := by
        rw [LinearMap.map_add, Work.Cohomology.biprod_fst_inl_apply,
          Work.Cohomology.biprod_fst_inr_apply, add_zero]
      rw [hfq] at hfst
      exact hfst.symm
    · have h := homologyMap_biprod_lift_apply_h n (relCokerMap M (S ∩ T) S hWS)
        (relCokerMap M (S ∩ T) T hWT) u
      have hsnd := congrArg (fun z => (biprod.snd : (cokernel (inclChains M S)).homology n ⊞
        (cokernel (inclChains M T)).homology n ⟶ (cokernel (inclChains M T)).homology n) z) h
      rw [LinearMap.map_add, Work.Cohomology.biprod_snd_inl_apply,
        Work.Cohomology.biprod_snd_inr_apply, zero_add] at hsnd
      rw [hu', heHx] at hsnd
      have hsq : (biprod.snd : (cokernel (inclChains M S)).homology n ⊞
            (cokernel (inclChains M T)).homology n ⟶ (cokernel (inclChains M T)).homology n)
          ((biprod.inl : (cokernel (inclChains M S)).homology n ⟶
              (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) a
            + (biprod.inr : (cokernel (inclChains M T)).homology n ⟶
              (cokernel (inclChains M S)).homology n ⊞ (cokernel (inclChains M T)).homology n) b)
          = b := by
        rw [LinearMap.map_add, Work.Cohomology.biprod_snd_inl_apply,
          Work.Cohomology.biprod_snd_inr_apply, zero_add]
      rw [hsq] at hsnd
      exact hsnd.symm

theorem excludedMV (n : ℕ) (M : TopCat) (K L : Set M) (hK : IsClosed K) (hL : IsClosed L)
    (hzero : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains M (K ∩ L)ᶜ).homology (n+1))) :
    (∀ (u : (Work.Cohomology.relChains M (K ∪ L)ᶜ).homology n),
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M (K ∪ L)ᶜ Kᶜ
          (Set.compl_subset_compl.mpr Set.subset_union_left)) n).hom u = 0 →
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M (K ∪ L)ᶜ Lᶜ
          (Set.compl_subset_compl.mpr Set.subset_union_right)) n).hom u = 0 → u = 0) ∧
    (∀ (a : (Work.Cohomology.relChains M Kᶜ).homology n)
      (b : (Work.Cohomology.relChains M Lᶜ).homology n),
      (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M Kᶜ (K ∩ L)ᶜ
          (Set.compl_subset_compl.mpr Set.inter_subset_left)) n).hom a =
        (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M Lᶜ (K ∩ L)ᶜ
          (Set.compl_subset_compl.mpr Set.inter_subset_right)) n).hom b →
      ∃ u : (Work.Cohomology.relChains M (K ∪ L)ᶜ).homology n,
        (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M (K ∪ L)ᶜ Kᶜ
            (Set.compl_subset_compl.mpr Set.subset_union_left)) n).hom u = a ∧
        (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M (K ∪ L)ᶜ Lᶜ
            (Set.compl_subset_compl.mpr Set.subset_union_right)) n).hom u = b) := by
  exact excludedMV_aux n M Kᶜ Lᶜ (K ∪ L)ᶜ (K ∩ L)ᶜ hK.isOpen_compl hL.isOpen_compl
    (Set.compl_subset_compl.mpr Set.subset_union_left)
    (Set.compl_subset_compl.mpr Set.subset_union_right) (Set.compl_union K L)
    (Set.compl_subset_compl.mpr Set.inter_subset_left)
    (Set.compl_subset_compl.mpr Set.inter_subset_right) (Set.compl_inter K L) hzero

end

end Work.ThomBordism
