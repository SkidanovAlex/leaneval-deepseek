import Mathlib
import Submission.Work.Projective.CP2Homology
import Submission.Work.Projective.HomologyPieces
import Submission.Work.Cohomology.mvLeft_zero_injective
import Submission.Work.Projective.pathConnectedSpace_CP
import Submission.Work.Projective.pathConnectedSpace_cpUV

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The integral homology of `ℂP²` is degreewise free

`Work.Projective.cp2_homology_free` : for every `n`, the `n`-th singular homology of `ℂP²` with
coefficients in `ℤ` is a free `ℤ`-module.  The homology of `ℂP²` is `ℤ` in degrees `0`, `2`, `4`
and vanishes elsewhere, so every degree is free; the two `ℤ`'s in the middle degrees are the ones
already computed in `Submission/Work/Projective/CP2Homology.lean` (degree `4`) and here (degree
`2`), while the vanishing in degrees `1`, `3` and `≥ 5` is read off the Mayer–Vietoris long exact
sequence of the standard cover `ℂP² = U ∪ V` (`Work.Cohomology.mv_H_exact₁/₂/₃`).

## The cover

Throughout, `U = cp2U = chartSet 0` is contractible and `V = cp2V = chartSet 1 ∪ chartSet 2` is
homotopy equivalent to `S²`, with `U ∩ V ≃ S³`; the three constituent homologies are computed in
`Work.Projective.HomologyPieces`:

* `Hₙ(U) = 0` for `n > 0`;
* `Hₙ(V) = 0` for `n > 0`, `n ≠ 2`, and `H₂(V) ≅ ℤ`;
* `Hₙ(U ∩ V) = 0` for `n > 0`, `n ≠ 3`, and `H₃(U ∩ V) ≅ ℤ`.

## The two general shapes of the argument

Writing `HInter`, `HBiprod`, `HSmall` for the three homology terms of the Mayer–Vietoris sequence
(`Work.Cohomology.HSmall`, `HInter`, `HBiprod`), the exactness statements give two patterns:

* `cp2hf_isZero_HSmall_succ` — if `HBiprod (n+1)` vanishes and the connecting map `mvδ n` is zero,
  then `HSmall (n+1)` vanishes;
* `cp2hf_isIso_homologyMap_mvRight_succ` — if `HInter (n+1)` vanishes and `mvδ n = 0`, then the map
  `HBiprod (n+1) → HSmall (n+1)` is an isomorphism.

The second is used in degree `2`, where it identifies `H₂(ℂP²)` with `H₂(V)`; the first gives the
vanishing in degrees `3` and `≥ 5`.  Degree `1` is the only case that needs the fact that
`H₀(U ∩ V) → H₀(U) ⊞ H₀(V)` is injective (`Work.Cohomology.mvLeft_zero_injective`), which turns
`mvδ 0` into a zero map.
-/

set_option maxHeartbeats 800000

namespace Work.Projective

open CategoryTheory AlgebraicTopology Limits Work.Cohomology

noncomputable section

/-! ## A chain-complex version of the biproduct-homology isomorphism

`Work.Cohomology.homology_biprod_iso` is stated for cochain complexes; the Mayer–Vietoris
computation of `ℂP²` uses chain complexes, so we record the same fact here. -/

/-- The homology of a biproduct of chain complexes of `ℤ`-modules is the biproduct of the
homologies. -/
theorem cp2hf_homology_biprod_iso_chain (C D : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    Nonempty ((C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  exact ⟨F.mapBiprod C D⟩

/-! ## The two patterns extracted from the Mayer–Vietoris exact sequences -/

/-- **Squeeze.**  If `HBiprod (n+1)` vanishes and the connecting map `mvδ n` is zero, then
`HSmall (n+1)` vanishes: exactness at `HSmall (n+1)` exhibits it both as the image of a zero map
and as the kernel of a zero map. -/
lemma cp2hf_isZero_HSmall_succ {X : TopCat} (U V : Set X) (n : ℕ)
    (hB : IsZero (HBiprod U V (n+1))) (hδ : mvδ U V n = 0) : IsZero (HSmall U V (n+1)) := by
  have hex : LinearMap.range (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom =
      LinearMap.ker (mvδ U V n).hom := (mv_H_exact₃ U V n).moduleCat_range_eq_ker
  have hf : HomologicalComplex.homologyMap (mvRight U V) (n+1) = 0 := hB.eq_zero_of_src _
  have hrange : LinearMap.range (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom = ⊥ := by
    rw [hf]; exact LinearMap.range_zero
  have hker : LinearMap.ker (mvδ U V n).hom = ⊤ := by rw [hδ]; exact LinearMap.ker_zero
  have hbot : (⊥ : Submodule ℤ ↥(HSmall U V (n+1))) = ⊤ := by rw [← hrange, hex, hker]
  haveI : Subsingleton ↥(HSmall U V (n+1)) := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Submodule ℤ ↥(HSmall U V (n+1))) := by rw [hbot]; exact Submodule.mem_top
    have hb : b ∈ (⊥ : Submodule ℤ ↥(HSmall U V (n+1))) := by rw [hbot]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  exact ModuleCat.isZero_of_subsingleton _

/-- **Isomorphism at the small chains.**  If `HInter (n+1)` vanishes and `mvδ n = 0`, then the
second Mayer–Vietoris map `HBiprod (n+1) → HSmall (n+1)` is an isomorphism: it is injective because
its kernel is the range of `mvLeft (n+1)`, whose source vanishes, and surjective because its range
is the kernel of `mvδ n`, which is zero. -/
lemma cp2hf_isIso_homologyMap_mvRight_succ {X : TopCat} (U V : Set X) (n : ℕ)
    (hI : IsZero (HInter U V (n+1))) (hδ : mvδ U V n = 0) :
    IsIso (HomologicalComplex.homologyMap (mvRight U V) (n+1)) := by
  have hex2 : LinearMap.range (HomologicalComplex.homologyMap (mvLeft U V) (n+1)).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom :=
    (mv_H_exact₂ U V (n+1)).moduleCat_range_eq_ker
  have hle : HomologicalComplex.homologyMap (mvLeft U V) (n+1) = 0 := hI.eq_zero_of_src _
  have hker : LinearMap.ker (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom = ⊥ := by
    rw [← hex2, hle]; exact LinearMap.range_zero
  have hinj : Function.Injective (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom :=
    LinearMap.ker_eq_bot.mp hker
  have hex3 : LinearMap.range (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom =
      LinearMap.ker (mvδ U V n).hom := (mv_H_exact₃ U V n).moduleCat_range_eq_ker
  have hkerδ : LinearMap.ker (mvδ U V n).hom = ⊤ := by rw [hδ]; exact LinearMap.ker_zero
  have hrange : LinearMap.range (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom = ⊤ := by
    rw [hex3, hkerδ]
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap (mvRight U V) (n+1)).hom :=
    LinearMap.range_eq_top.mp hrange
  haveI : Mono (HomologicalComplex.homologyMap (mvRight U V) (n+1)) :=
    (ModuleCat.mono_iff_injective _).mpr hinj
  haveI : Epi (HomologicalComplex.homologyMap (mvRight U V) (n+1)) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  exact isIso_of_mono_of_epi _

/-! ## The three constituent homologies of the cover -/

/-- `Hₙ(U) = 0` for `n > 0`, `U = chartSet 0` being contractible. -/
lemma cp2hf_hU_zero (n : ℕ) (hn : 0 < n) :
    IsZero ((singularChains ℤ (TopCat.of ↥cp2U)).homology n) := by
  haveI : ContractibleSpace ↥cp2U := contractibleSpace_chartSet 2 0
  exact homologyContractible n hn

/-- `Hₙ(V) = 0` for `n > 0`, `n ≠ 2`. -/
lemma cp2hf_hV_zero (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) :
    IsZero ((singularChains ℤ (TopCat.of ↥cp2V)).homology n) :=
  isZero_cochainV_homology_cp2 hn h2

/-- `Hₙ(U ∩ V) = 0` for `n > 0`, `n ≠ 3`. -/
lemma cp2hf_hUV_zero (n : ℕ) (hn : 0 < n) (h3 : n ≠ 3) :
    IsZero ((singularChains ℤ (TopCat.of ↥(cp2U ∩ cp2V))).homology n) :=
  isZero_cochainUV_homology_cp2 hn h3

/-- `Hₙ(U) ⊞ Hₙ(V) = 0` for `n > 0`, `n ≠ 2`. -/
lemma cp2hf_hBiprod_zero (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) : IsZero (HBiprod cp2U cp2V n) :=
  isZero_homology_biprod n (cp2hf_hU_zero n hn) (cp2hf_hV_zero n hn h2)

/-- `Hₙ(U ∩ V) = 0` for `n > 0`, `n ≠ 3`. -/
lemma cp2hf_hInter_zero (n : ℕ) (hn : 0 < n) (h3 : n ≠ 3) : IsZero (HInter cp2U cp2V n) :=
  cp2hf_hUV_zero n hn h3

/-! ## Freeness of zero modules and of modules isomorphic to `ℤ` -/

/-- A vanishing `ℤ`-module is free. -/
lemma cp2hf_free_of_isZero {M : ModuleCat ℤ} (h : IsZero M) : Module.Free ℤ ↥M := by
  haveI : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp h
  exact Module.Free.of_subsingleton ℤ ↥M

/-- A `ℤ`-module isomorphic to `ℤ` is free. -/
lemma cp2hf_free_of_iso_int {M : ModuleCat ℤ} (e : M ≅ ModuleCat.of ℤ ℤ) :
    Module.Free ℤ ↥M :=
  Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ) e.symm.toLinearEquiv

/-! ## Degree `0`: free because `ℂP²` is path connected -/

lemma cp2hf_free_H_zero :
    Module.Free ℤ ↥((singularChains ℤ (CPSpace 2)).homology 0) := by
  haveI : PathConnectedSpace ↥(CPSpace 2) := pathConnectedSpace_CP 2
  haveI : IsIso (TopCat.singularHomology₀ε (CPSpace 2) (ModuleCat.of ℤ ℤ)) := inferInstance
  exact Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ)
    (asIso (TopCat.singularHomology₀ε (CPSpace 2) (ModuleCat.of ℤ ℤ))).toLinearEquiv.symm

/-! ## Degree `1`: the intersection `U ∩ V` is path connected -/

/-- `U ∩ V = cp2U ∩ cp2V` is path connected (it is homeomorphic to `ℂ² ∖ {0}`). -/
lemma cp2hf_pathConnected_cp2UV : PathConnectedSpace ↥(cp2U ∩ cp2V) := by
  haveI : PathConnectedSpace {z : Fin 2 → ℂ // z ≠ 0} := by
    have hrank : 1 < Module.rank ℝ (Fin 2 → ℂ) := by
      rw [← Module.finrank_eq_rank, finrank_real_fin_complex]
      norm_num
    exact (isPathConnected_iff_pathConnectedSpace (F := ({0} : Set (Fin 2 → ℂ))ᶜ)).mp
      (by simpa using isPathConnected_compl_singleton_of_one_lt_rank hrank 0)
  rw [pathConnectedSpace_iff_univ]
  have h : IsPathConnected (Set.univ : Set {z : Fin 2 → ℂ // z ≠ 0}) :=
    pathConnectedSpace_iff_univ.mp inferInstance
  have h2 := (cp2UV_homeo.symm.isPathConnected_image (s := Set.univ)).mpr h
  rwa [Set.image_univ_of_surjective cp2UV_homeo.symm.surjective] at h2

/-- **`H₁(ℂP²) = 0`.**  In the Mayer–Vietoris sequence the term `H₀(U) ⊞ H₀(V)` receives an
injective map from `H₀(U ∩ V)`, so `mvδ 0 = 0`; then `H₁(ℂP²)` is squeezed between the vanishing
`H₁(U) ⊞ H₁(V)` and zero. -/
lemma cp2hf_isZero_H_one :
    IsZero ((singularChains ℤ (CPSpace 2)).homology 1) := by
  haveI : PathConnectedSpace ↥(cp2U ∩ cp2V) := cp2hf_pathConnected_cp2UV
  have hex1 : LinearMap.range (mvδ cp2U cp2V 0).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mvLeft cp2U cp2V) 0).hom :=
    (mv_H_exact₁ cp2U cp2V 0).moduleCat_range_eq_ker
  have hinj : Function.Injective (HomologicalComplex.homologyMap (mvLeft cp2U cp2V) 0).hom :=
    Work.Cohomology.mvLeft_zero_injective cp2U cp2V
  have hker : LinearMap.ker (HomologicalComplex.homologyMap (mvLeft cp2U cp2V) 0).hom = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hr : LinearMap.range (mvδ cp2U cp2V 0).hom = ⊥ := by rw [hex1, hker]
  have hδ : mvδ cp2U cp2V 0 = 0 := ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hr)
  have hB : IsZero (HBiprod cp2U cp2V 1) := cp2hf_hBiprod_zero 1 (by norm_num) (by norm_num)
  exact IsZero.of_iso (cp2hf_isZero_HSmall_succ cp2U cp2V 0 hB hδ)
    (smallIso cp2U cp2V isOpen_cp2U isOpen_cp2V cp2U_union_cp2V 1).symm

/-! ## Degree `2`: `H₂(ℂP²) ≅ H₂(V) ≅ ℤ` -/

lemma cp2hf_iso_H_two :
    Nonempty ((singularChains ℤ (CPSpace 2)).homology 2 ≅ ModuleCat.of ℤ ℤ) := by
  have hI : IsZero (HInter cp2U cp2V 2) := cp2hf_hInter_zero 2 (by norm_num) (by norm_num)
  have hδ : mvδ cp2U cp2V 1 = 0 :=
    (cp2hf_hInter_zero 1 (by norm_num) (by norm_num)).eq_zero_of_tgt _
  haveI : IsIso (HomologicalComplex.homologyMap (mvRight cp2U cp2V) 2) :=
    cp2hf_isIso_homologyMap_mvRight_succ cp2U cp2V 1 hI hδ
  obtain ⟨ebip⟩ := cp2hf_homology_biprod_iso_chain
    (singularChains ℤ (TopCat.of ↥cp2U)) (singularChains ℤ (TopCat.of ↥cp2V)) 2
  have hU2 : IsZero ((singularChains ℤ (TopCat.of ↥cp2U)).homology 2) :=
    cp2hf_hU_zero 2 (by norm_num)
  obtain ⟨eV⟩ := cp2V_homology 2 (by norm_num)
  refine ⟨(smallIso cp2U cp2V isOpen_cp2U isOpen_cp2V cp2U_union_cp2V 2).symm ≪≫
    (asIso (HomologicalComplex.homologyMap (mvRight cp2U cp2V) 2)).symm ≪≫
    ebip ≪≫ (CategoryTheory.Limits.isoZeroBiprod hU2).symm ≪≫ eV ≪≫ ?_⟩
  rw [if_pos rfl]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-! ## Degree `3`: `H₃(ℂP²) = 0` -/

lemma cp2hf_isZero_H_three :
    IsZero ((singularChains ℤ (CPSpace 2)).homology 3) := by
  have hB : IsZero (HBiprod cp2U cp2V 3) := cp2hf_hBiprod_zero 3 (by norm_num) (by norm_num)
  have hI : IsZero (HInter cp2U cp2V 2) := cp2hf_hInter_zero 2 (by norm_num) (by norm_num)
  have hδ : mvδ cp2U cp2V 2 = 0 := hI.eq_zero_of_tgt _
  exact IsZero.of_iso (cp2hf_isZero_HSmall_succ cp2U cp2V 2 hB hδ)
    (smallIso cp2U cp2V isOpen_cp2U isOpen_cp2V cp2U_union_cp2V 3).symm

/-! ## Degrees `≥ 5`: `Hₙ(ℂP²) = 0` -/

lemma cp2hf_isZero_H_ge_five (n : ℕ) (hn : 5 ≤ n) :
    IsZero ((singularChains ℤ (CPSpace 2)).homology n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hB : IsZero (HBiprod cp2U cp2V (k+1)) :=
    cp2hf_hBiprod_zero (k+1) (by omega) (by omega)
  have hI : IsZero (HInter cp2U cp2V k) := cp2hf_hInter_zero k (by omega) (by omega)
  have hδ : mvδ cp2U cp2V k = 0 := hI.eq_zero_of_tgt _
  exact IsZero.of_iso (cp2hf_isZero_HSmall_succ cp2U cp2V k hB hδ)
    (smallIso cp2U cp2V isOpen_cp2U isOpen_cp2V cp2U_union_cp2V (k+1)).symm

/-! ## The theorem -/

theorem cp2_homology_free (n : ℕ) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ (Work.Projective.CPSpace 2)).homology n) := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact cp2hf_free_H_zero
    · exact cp2hf_free_of_isZero cp2hf_isZero_H_one
    · exact cp2hf_free_of_iso_int cp2hf_iso_H_two.some
    · exact cp2hf_free_of_isZero cp2hf_isZero_H_three
    · exact cp2hf_free_of_iso_int singularHomology_four_cp2.some
  · exact cp2hf_free_of_isZero (cp2hf_isZero_H_ge_five n h5)

end

end Work.Projective
