import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.CompatTrans.homology_prod_sphere
import Submission.Work.Cohomology.homology_prod_contractible
import Submission.Work.Cohomology.inclAThreeSurjective
import Submission.Work.Cohomology.CompatTrans.inclAThreeKerIso

set_option synthInstance.maxHeartbeats 400000

/-!
# The singular homology of the pair `(S³ × D⁴, S³ × S³)`

`Hₙ(S³ × D⁴, S³ × S³; ℤ) ≅ ℤ` for `n = 4, 7`, and `0` otherwise.

The computation is by the long exact sequence of the pair
(`Work.Cohomology.hPair_exact₁/₂/₃`) together with the homology of the two spaces:
`S³ × D⁴ ≃ S³` (`D⁴` contractible) and `S³ × S³`
(`Work.Cohomology.homology_prod_sphere`).  The only place where the *maps* of the sequence are
needed is in degree `4`, where `H₄(X,A) ≅ ker(H₃(A) → H₃(X))`; the kernel is `ℤ`, computed by the
delegated lemma `Work.Cohomology.inclAThreeKerIso` (the class of the second sphere factor dies in
`D⁴`).
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module


open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-- The singular homology `Hₙ(S³ × D⁴)` of the total space. -/
abbrev HX (n : ℕ) : ModuleCat ℤ := (singularChains ℤ PairXT).homology n

/-- The singular homology `Hₙ(S³ × S³)` of the sphere bundle. -/
abbrev HA (n : ℕ) : ModuleCat ℤ := (singularChains ℤ (TopCat.of PairAT)).homology n

/-- The relative singular homology `Hₙ(S³ × D⁴, S³ × S³)`. -/
abbrev RelA (n : ℕ) : ModuleCat ℤ := (relChains PairXT PairAT).homology n

instance instContractibleDisc4T : ContractibleSpace ↥Disc4T :=
  Convex.contractibleSpace (convex_closedBall 0 1) ⟨0, by simp [Metric.mem_closedBall]⟩

/-! ## The homology of the total space -/

theorem HX_iso_three : Nonempty (HX 3 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv
    (homotopyEquiv_prod_fst ↥Sph3T ↥Disc4T).some 3
  obtain ⟨e2⟩ := sphereHomologyTop 3 (by norm_num)
  exact ⟨e ≪≫ e2⟩

theorem HX_isZero (n : ℕ) (hn : 1 ≤ n) (h3 : n ≠ 3) : IsZero (HX n) := by
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv
    (homotopyEquiv_prod_fst ↥Sph3T ↥Disc4T).some n
  exact IsZero.of_iso (sphereVanishing 3 n (by norm_num) (by omega) h3) e

/-! ## The homology of the sphere bundle -/

/-- The homeomorphism `S³ × S³ ⊆ S³ × D⁴ ≅ S³ × S³` with the honest product of the two
spheres. -/
def AHto : ↥PairAT ≃ₜ (↥Sph3T × ↥Sph3T) where
  toFun p := (p.1.1, sphereInUnitHomeomorph 4 ⟨p.1.2, p.2⟩)
  invFun q := ⟨(q.1, ((sphereInUnitHomeomorph 4).symm q.2).1),
    ((sphereInUnitHomeomorph 4).symm q.2).2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv q := by
    simp
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((sphereInUnitHomeomorph 4).continuous.comp
        (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) (fun p => p.2)))
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_fst.prodMk
        (continuous_subtype_val.comp
          ((sphereInUnitHomeomorph 4).symm.continuous.comp continuous_snd)))
      (fun q => ((sphereInUnitHomeomorph 4).symm q.2).2)

theorem HA_iso_expo (n : ℕ) :
    Nonempty (HA n ≅ ModuleCat.of ℤ (Fin (expo 3 3 n) → ℤ)) := by
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv AHto.toHomotopyEquiv n
  obtain ⟨e2⟩ := homology_prod_sphere 3 3 n (by norm_num) (by norm_num)
  exact ⟨e ≪≫ e2⟩

theorem HA_isZero (n : ℕ) (hn : n ≠ 0) (h3 : n ≠ 3) (h6 : n ≠ 6) : IsZero (HA n) := by
  obtain ⟨e⟩ := HA_iso_expo n
  have hexpo : expo 3 3 n = 0 := by
    simp [expo, hn, h3, h6]
  rw [hexpo] at e
  exact IsZero.of_iso isZero_fin_zero e

theorem HA_iso_three : Nonempty (HA 3 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) := by
  obtain ⟨e⟩ := HA_iso_expo 3
  rw [show expo 3 3 3 = 2 from by simp only [expo]; norm_num] at e
  exact ⟨e⟩

theorem HA_iso_six : Nonempty (HA 6 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := HA_iso_expo 6
  rw [show expo 3 3 6 = 1 from by simp only [expo]; norm_num] at e
  exact ⟨e ≪≫ nonempty_int_fin_one.some.symm⟩


/-! ## Path connectedness of the two spaces (for the degree-`0` augmentation) -/

/-- A homeomorphism transports path connectedness. -/
lemma pathConnectedSpace_of_homeomorph' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) [PathConnectedSpace β] : PathConnectedSpace α := by
  rw [pathConnectedSpace_iff_univ]
  have h : IsPathConnected (Set.univ : Set β) := pathConnectedSpace_iff_univ.mp inferInstance
  have h2 := (e.symm.isPathConnected_image (s := Set.univ)).mpr h
  rwa [Set.image_univ_of_surjective e.symm.surjective] at h2

instance instPathConnectedSph3T : PathConnectedSpace ↥Sph3T := by
  haveI : PathConnectedSpace ↥(sphSet 4) := pathConnected_sphSet 4 (by norm_num)
  exact pathConnectedSpace_of_homeomorph' (Homeomorph.setCongr (sphereSet_eq 4))

instance instPathConnectedPairXT : PathConnectedSpace ↥PairXT := inferInstance

instance instPathConnectedPairAT : PathConnectedSpace (TopCat.of PairAT) :=
  pathConnectedSpace_of_homeomorph' AHto

/-! ## The degree-`0` map `H₀(S³ × S³) ⟶ H₀(S³ × D⁴)` is an isomorphism -/

theorem h0_incl_isIso :
    IsIso (HomologicalComplex.homologyMap (inclChains PairXT PairAT) 0) := by
  haveI : IsIso (TopCat.singularHomology₀ε PairXT (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI : IsIso (TopCat.singularHomology₀ε (TopCat.of PairAT) (ModuleCat.of ℤ ℤ)) :=
    inferInstance
  have hnat := epsilonNaturality (TopCat.of PairAT) PairXT (subtypeIncl PairXT PairAT)
  have heq : HomologicalComplex.homologyMap (inclChains PairXT PairAT) 0
      = TopCat.singularHomology₀ε (TopCat.of PairAT) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε PairXT (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-! ## The reductions from the long exact sequence of the pair -/

/-- **Exactness in the long exact sequence of the pair**: if `H_{n+1}(X) = 0` then the connecting
map `δ = hPairδ` exhibits `H_{n+1}(X,A)` as the kernel of `H_n(A) → H_n(X)`. -/
theorem RelA_succ_iso_ker (n : ℕ) (hX : IsZero (HX (n + 1))) :
    Nonempty (RelA (n + 1) ≅ ModuleCat.of ℤ
      ↥(LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (inclChains PairXT PairAT) n)))) := by
  have hex₃ := hPair_exact₃ PairXT PairAT n
  have hf0 : (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (inclChains PairXT PairAT)) (n + 1))
      (hPairδ PairXT PairAT n) (hPair_comp_δ PairXT PairAT n)).f = 0 := hX.eq_of_src _ 0
  have hinj : Function.Injective (hPairδ PairXT PairAT n).hom :=
    (ModuleCat.mono_iff_injective _).mp ((ShortComplex.exact_iff_mono _ hf0).mp hex₃)
  have hrange : (hPairδ PairXT PairAT n).hom.range
      = (HomologicalComplex.homologyMap (inclChains PairXT PairAT) n).hom.ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker (hPair_exact₁ PairXT PairAT n)
  exact ⟨LinearEquiv.toModuleIso
    ((LinearEquiv.ofInjective (hPairδ PairXT PairAT n).hom hinj).trans
      (LinearEquiv.ofEq _ _ hrange))⟩

/-- **`H_{n+1}(X,A) = 0`** when `H_{n+1}(X) = 0` and `H_n(A) = 0`. -/
theorem RelA_isZero_of (n : ℕ) (hX : IsZero (HX (n + 1))) (hA : IsZero (HA n)) :
    IsZero (RelA (n + 1)) := by
  have hex₃ := hPair_exact₃ PairXT PairAT n
  have hf0 : (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (inclChains PairXT PairAT)) (n + 1))
      (hPairδ PairXT PairAT n) (hPair_comp_δ PairXT PairAT n)).f = 0 := hX.eq_of_src _ 0
  haveI : Mono (hPairδ PairXT PairAT n) := (ShortComplex.exact_iff_mono _ hf0).mp hex₃
  have hfz : hPairδ PairXT PairAT n = 0 := hA.eq_of_tgt _ 0
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  exact (cancel_mono (hPairδ PairXT PairAT n)).mp
    (by rw [Category.id_comp, zero_comp, hfz])

/-- **The connecting map `hPairδ` is an isomorphism** when `H_n(X) = H_{n+1}(X) = 0`. -/
theorem hPairδ_isIso_of (n : ℕ) (hX1 : IsZero (HX (n + 1))) (hX0 : IsZero (HX n)) :
    IsIso (hPairδ PairXT PairAT n) := by
  have hex₃ := hPair_exact₃ PairXT PairAT n
  have hf0 : (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (inclChains PairXT PairAT)) (n + 1))
      (hPairδ PairXT PairAT n) (hPair_comp_δ PairXT PairAT n)).f = 0 := hX1.eq_of_src _ 0
  have hmono : Mono (hPairδ PairXT PairAT n) := (ShortComplex.exact_iff_mono _ hf0).mp hex₃
  have hg0 : (ShortComplex.mk (hPairδ PairXT PairAT n)
      (HomologicalComplex.homologyMap (inclChains PairXT PairAT) n)
      (hPairδ_comp PairXT PairAT n)).g = 0 := hX0.eq_of_tgt _ 0
  have hepi : Epi (hPairδ PairXT PairAT n) :=
    (ShortComplex.exact_iff_epi _ hg0).mp (hPair_exact₁ PairXT PairAT n)
  exact isIso_of_mono_of_epi _

/-! ## The degrees `0, 7` -/

theorem RelA_zero : IsZero (RelA 0) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  haveI := h0_incl_isIso
  have h0 : Epi (HomologicalComplex.homologyMap (hPairShort PairXT PairAT).f 0) :=
    IsIso.epi_of_iso (HomologicalComplex.homologyMap (inclChains PairXT PairAT) 0)
  refine (hPairShort_shortExact PairXT PairAT).exactAt_X₃ 0 h0 ?_
  intro j hj
  simp [ComplexShape.down] at hj

theorem RelA_seven_iso_int : Nonempty (RelA 7 ≅ ModuleCat.of ℤ ℤ) := by
  haveI : IsIso (hPairδ PairXT PairAT 6) :=
    hPairδ_isIso_of 6 (HX_isZero 7 (by norm_num) (by norm_num))
      (HX_isZero 6 (by norm_num) (by norm_num))
  obtain ⟨e⟩ := HA_iso_six
  exact ⟨asIso (hPairδ PairXT PairAT 6) ≪≫ e⟩

/-! ## The remaining degrees -/

theorem RelA_isZero_of_two_le (k : ℕ) (h2 : 2 ≤ k) (h3 : k ≠ 3) (h4 : k ≠ 4) (h7 : k ≠ 7) :
    IsZero (RelA k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel (by omega)).symm⟩
  exact RelA_isZero_of m (HX_isZero (m + 1) (by omega) (by omega))
    (HA_isZero m (by omega) (by omega) (by omega))

theorem RelA_one_isZero : IsZero (RelA 1) := by
  obtain ⟨e⟩ := RelA_succ_iso_ker 0 (HX_isZero 1 (by norm_num) (by norm_num))
  haveI := h0_incl_isIso
  have hker : (HomologicalComplex.homologyMap (inclChains PairXT PairAT) 0).hom.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  haveI hz : IsZero (ModuleCat.of ℤ ↥(LinearMap.ker
      (HomologicalComplex.homologyMap (inclChains PairXT PairAT) 0).hom)) := by
    rw [ModuleCat.isZero_iff_subsingleton, hker]
    infer_instance
  exact IsZero.of_iso hz e


/-- If `f` is an epimorphism and `f = 0`, its target is a zero object. -/
lemma isZero_target_of_epi_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [Epi f] (hf : f = 0) : IsZero Y := by
  refine (IsZero.iff_id_eq_zero Y).mpr ?_
  have h : f ≫ 𝟙 Y = f ≫ (0 : Y ⟶ Y) := by rw [Category.comp_id, comp_zero, hf]
  exact (cancel_epi f).mp h

/-- Two `ModuleCat.of` objects built from the same type with two `ℤ`-module structures (which are
automatically equal over `ℤ`) are isomorphic. -/
def moduleCatOfEq {M : Type} [AddCommGroup M] {a b : Module ℤ M} :
    @ModuleCat.of ℤ _ M _ a ≅ @ModuleCat.of ℤ _ M _ b := by
  have h : a = b := Subsingleton.elim a b
  rw [h]

/-! ## `H₄(X,A) ≅ ℤ` and `H₃(X,A) = 0` -/

theorem RelA_four_iso_int : Nonempty (RelA 4 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := RelA_succ_iso_ker 3 (HX_isZero 4 (by norm_num) (by norm_num))
  obtain ⟨e2⟩ := inclAThreeKerIso
  exact ⟨e ≪≫ moduleCatOfEq ≪≫ e2⟩

theorem RelA_three_isZero : IsZero (RelA 3) := by
  have hs : Function.Surjective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (inclChains PairXT PairAT) 3)) := inclAThreeSurjective
  have hzero : (HomologicalComplex.homologyMap (cokernel.π (inclChains PairXT PairAT)) 3).hom
      = 0 := by
    apply LinearMap.ker_eq_top.mp
    rw [← ShortComplex.Exact.moduleCat_range_eq_ker (hPair_exact₂ PairXT PairAT 3)]
    exact LinearMap.range_eq_top.mpr hs
  haveI hA2 : IsZero (HA 2) := HA_isZero 2 (by norm_num) (by norm_num) (by norm_num)
  have hδz : hPairδ PairXT PairAT 2 = 0 := hA2.eq_of_tgt _ 0
  haveI hEpi : Epi (HomologicalComplex.homologyMap (cokernel.π (inclChains PairXT PairAT)) 3) :=
    (ShortComplex.exact_iff_epi _ hδz).mp (hPair_exact₃ PairXT PairAT 2)
  have hf0 : HomologicalComplex.homologyMap (cokernel.π (inclChains PairXT PairAT)) 3 = 0 :=
    ModuleCat.hom_ext hzero
  exact isZero_target_of_epi_eq_zero
    (HomologicalComplex.homologyMap (cokernel.π (inclChains PairXT PairAT)) 3) hf0

/-! ## The remaining vanishing -/

theorem RelA_isZero_of_ne (n : ℕ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h3 : n ≠ 3)
    (h4 : n ≠ 4) (h7 : n ≠ 7) : IsZero (RelA n) := by
  rcases eq_or_ne n 2 with rfl | h2
  · exact RelA_isZero_of_two_le 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact RelA_isZero_of_two_le n (by omega) h3 h4 h7

lemma index_eq_zero (n : ℕ) (h4 : n ≠ 4) (h7 : n ≠ 7) :
    ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) = 0 := by
  rw [if_neg h4, if_neg h7]

/-! ## The theorem -/

theorem sphere3DiscPairHomology (n : ℕ) :
    Nonempty (((Work.Cohomology.relChains
        (TopCat.of (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ×
          ↥(Work.Cohomology.diskUnit 4)))
        {p : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ×
            ↥(Work.Cohomology.diskUnit 4) |
          p.2 ∈ Work.Cohomology.sphereInUnit 4}).homology n) ≅
      ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ)) := by
  change Nonempty (RelA n ≅
    ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ))
  rcases eq_or_ne n 4 with rfl | h4
  · rw [show (if (4 : ℕ) = 4 then 1 else 0) + (if (4 : ℕ) = 7 then 1 else 0) = 1 from by norm_num]
    obtain ⟨e⟩ := RelA_four_iso_int
    exact ⟨e ≪≫ nonempty_int_fin_one.some⟩
  rcases eq_or_ne n 7 with rfl | h7
  · rw [show (if (7 : ℕ) = 4 then 1 else 0) + (if (7 : ℕ) = 7 then 1 else 0) = 1 from by norm_num]
    obtain ⟨e⟩ := RelA_seven_iso_int
    exact ⟨e ≪≫ nonempty_int_fin_one.some⟩
  · rcases eq_or_ne n 0 with rfl | h0
    · rw [index_eq_zero 0 (by norm_num) (by norm_num)]
      exact nonempty_iso_of_isZero RelA_zero isZero_fin_zero
    rcases eq_or_ne n 1 with rfl | h1
    · rw [index_eq_zero 1 (by norm_num) (by norm_num)]
      exact nonempty_iso_of_isZero RelA_one_isZero isZero_fin_zero
    rcases eq_or_ne n 3 with rfl | h3
    · rw [index_eq_zero 3 (by norm_num) (by norm_num)]
      exact nonempty_iso_of_isZero RelA_three_isZero isZero_fin_zero
    · rw [index_eq_zero n h4 h7]
      exact nonempty_iso_of_isZero (RelA_isZero_of_ne n h0 h1 h3 h4 h7) isZero_fin_zero

end

end Work.Cohomology


