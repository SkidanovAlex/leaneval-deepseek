import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs
import Submission.Work.Cohomology.CompatTrans.prodSphereAux
import Submission.Work.Cohomology.CompatTrans.prodSphereStep1
import Submission.Work.Cohomology.CompatTrans.contractible_Vset
import Submission.Work.Cohomology.CompatTrans.contractible_A1set_inter_B1set
import Submission.Work.Cohomology.CompatTrans.homotopyEquiv_A1set
import Submission.Work.Cohomology.CompatTrans.homotopyEquiv_B1set
import Submission.Work.Cohomology.mvLeft_zero_injective
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.excisionAux
import Submission.Work.Cohomology.CompatTrans.punctured_cap_prod_sphere
import Submission.Work.Cohomology.CompatTrans.pathConnected_Wset

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Step 2 of the computation of `Hₙ(Sᵖ × Sᵍ)`: the cover `{Sᵖ × Sᵍ \ {pt}, capA p × capA q}`
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
open CategoryTheory AlgebraicTopology Limits
open scoped Topology
namespace Work.Cohomology
noncomputable section


set_option linter.style.haveILetI false
open CategoryTheory AlgebraicTopology Limits
open scoped Topology
namespace Work.Cohomology
noncomputable section

/-- The homology of the punctured product of caps, in the degrees where it vanishes. -/
lemma isZero_HInter_YV (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hn' : n ≠ p + q - 1) :
    IsZero ((singularChains ℤ (TopCat.of ↥(Yset p q ∩ Vset p q))).homology n) := by
  have hzero : IsZero ((singularChains ℤ (TopCat.of ↥(Wset p q))).homology n) := by
    obtain ⟨e⟩ := punctured_cap_prod_sphere p q hp hq
    obtain ⟨e'⟩ := homologyIso_of_homotopyEquiv e n
    refine IsZero.of_iso ?_ e'
    have h := sphereVanishing (p + q - 1) n (by omega) (by omega) hn'
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p + q)] at h
    exact h
  rw [← Wset_eq_inter p q]
  exact hzero

/-- The composite `Vset ∩ Yset ⟶ Yset ⟶ Sᵖ` induces zero on `Hₙ` (`n ≥ 1`). -/
lemma inclUVU_YV_proj₁_eq_zero (p q n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q)) (sphTop (p+1))
      (inclUVU (Yset p q) (Vset p q) ≫ proj₁Y p q)) n = 0 := by
  let g : TopCat.of ↥(Yset p q ∩ Vset p q) ⟶ TopCat.of ↥(capA p) :=
    TopCat.ofHom ⟨fun z => ⟨(((z : ↥(Yset p q ∩ Vset p q)) : ↥(PSph p q)).1), (z.2.2).1⟩,
      by fun_prop⟩
  let h : TopCat.of ↥(capA p) ⟶ sphTop (p+1) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hfac : g ≫ h = inclUVU (Yset p q) (Vset p q) ≫ proj₁Y p q := by
    apply TopCat.hom_ext
    ext z
    rfl
  haveI : ContractibleSpace ↥(capA p) := contractibleSpace_capA p
  exact homologyMap_eq_zero_of_factor _ g h hfac n (homologyContractible n (by omega))

lemma inclUVU_YV_proj₂_eq_zero (p q n : ℕ) (hn : 1 ≤ n) :
    HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q)) (sphTop (q+1))
      (inclUVU (Yset p q) (Vset p q) ≫ proj₂Y p q)) n = 0 := by
  let g : TopCat.of ↥(Yset p q ∩ Vset p q) ⟶ TopCat.of ↥(capA q) :=
    TopCat.ofHom ⟨fun z => ⟨(((z : ↥(Yset p q ∩ Vset p q)) : ↥(PSph p q)).2), (z.2.2).2⟩,
      by fun_prop⟩
  let h : TopCat.of ↥(capA q) ⟶ sphTop (q+1) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hfac : g ≫ h = inclUVU (Yset p q) (Vset p q) ≫ proj₂Y p q := by
    apply TopCat.hom_ext
    ext z
    rfl
  haveI : ContractibleSpace ↥(capA q) := contractibleSpace_capA q
  exact homologyMap_eq_zero_of_factor _ g h hfac n (homologyContractible n (by omega))

/-- The pair of the two projections. -/
def projPair (p q n : ℕ) :
    (singularChains ℤ (TopCat.of ↥(Yset p q))).homology n ⟶
      (singularChains ℤ (sphTop (p+1))).homology n ⊞
        (singularChains ℤ (sphTop (q+1))).homology n :=
  biprod.lift
    (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q)) (sphTop (p+1))
      (proj₁Y p q)) n)
    (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q)) (sphTop (q+1))
      (proj₂Y p q)) n)

/-- `w = 0`, assuming the injectivity of the projection pair. -/
lemma inclUVU_YV_eq_zero (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hproj : Function.Injective (projPair p q n).hom) :
    HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q))
      (TopCat.of ↥(Yset p q)) (inclUVU (Yset p q) (Vset p q))) n = 0 := by
  by_cases hcase : n = p + q - 1
  · have hΨ : HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q))
          (TopCat.of ↥(Yset p q)) (inclUVU (Yset p q) (Vset p q))) n ≫ projPair p q n = 0 := by
      apply biprod.hom_ext
      · rw [Category.assoc, show projPair p q n ≫ biprod.fst
            = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q)) (sphTop (p+1))
              (proj₁Y p q)) n from biprod.lift_fst _ _]
        rw [← HomologicalComplex.homologyMap_comp, chainMap_compCompat', zero_comp]
        exact inclUVU_YV_proj₁_eq_zero p q n hn
      · rw [Category.assoc, show projPair p q n ≫ biprod.snd
            = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q)) (sphTop (q+1))
              (proj₂Y p q)) n from biprod.lift_snd _ _]
        rw [← HomologicalComplex.homologyMap_comp, chainMap_compCompat', zero_comp]
        exact inclUVU_YV_proj₂_eq_zero p q n hn
    apply ModuleCat.hom_ext
    ext x
    change (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q))
      (TopCat.of ↥(Yset p q)) (inclUVU (Yset p q) (Vset p q))) n).hom x = 0
    have h := congrArg (fun (f : (singularChains ℤ (TopCat.of ↥(Yset p q ∩ Vset p q))).homology n
        ⟶ (singularChains ℤ (sphTop (p+1))).homology n ⊞
          (singularChains ℤ (sphTop (q+1))).homology n) => (f : _ → _) x) hΨ
    have hx : (projPair p q n)
        ((HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q))
          (TopCat.of ↥(Yset p q)) (inclUVU (Yset p q) (Vset p q))) n).hom x) = 0 := by
      simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
        ModuleCat.hom_ofHom] using h
    exact hproj (by rw [hx, map_zero])
  · exact IsZero.eq_zero_of_src (isZero_HInter_YV p q n hp hq hn hcase) _

/-- The map `f` of the Mayer–Vietoris sequence of the cover `{Yset, Vset}` vanishes in every
positive degree (assuming the injectivity of the projection pair). -/
lemma mvLeft_YV_eq_zero (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hproj : Function.Injective (projPair p q n).hom) :
    HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q)) n = 0 := by
  have hw := inclUVU_YV_eq_zero p q n hp hq hn hproj
  have hidx : n ≠ 0 := by omega
  let F := homologyBiprodIso (singularChains ℤ (TopCat.of ↥(Yset p q)))
    (singularChains ℤ (TopCat.of ↥(Vset p q))) n
  suffices hfF : HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q)) n
      ≫ F.hom = 0 by
    calc HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q)) n
        = HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q)) n ≫ 𝟙 _ :=
          (Category.comp_id _).symm
      _ = HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q)) n
            ≫ (F.hom ≫ F.inv) := by
          rw [F.hom_inv_id]
      _ = (HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q)) n
            ≫ F.hom) ≫ F.inv := by
          rw [Category.assoc]
      _ = 0 := by rw [hfF, zero_comp]
  rw [show HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q)) n
      = HomologicalComplex.homologyMap (biprod.lift
          (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q)) (TopCat.of ↥(Yset p q))
            (inclUVU (Yset p q) (Vset p q)))
          (chainMap ℤ (TopCat.of ↥(Yset p q ∩ Vset p q)) (TopCat.of ↥(Vset p q))
            (inclUVV (Yset p q) (Vset p q)))) n from rfl]
  rw [homologyMap_biprod_lift]
  apply biprod.hom_ext
  · rw [biprod.lift_fst, zero_comp]
    exact hw
  · rw [biprod.lift_snd, zero_comp]
    haveI : ContractibleSpace ↥(Vset p q) := contractible_Vset p q
    exact IsZero.eq_zero_of_tgt (homologyContractible n (by omega)) _


/-- `Hₙ(Sᵐ) = 0` for `n ≠ 0, m` (`m ≥ 1`), in the `sphTop` model of the sphere. -/
lemma isZero_homology_sphTop (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnm : n ≠ m) :
    IsZero ((singularChains ℤ (sphTop (m+1))).homology n) := by
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (sphereSet_eq' (m+1))).toHomotopyEquiv n
  exact IsZero.of_iso (sphereVanishing m n hm (by omega) hnm) e.symm

/-- `Hₙ(Sᵖ × Sᵍ \ {pt}) = 0` for `n ≠ p, q` (`n ≥ 1`). -/
lemma isZero_homology_Yset (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hnp : n ≠ p) (hnq : n ≠ q) :
    IsZero ((singularChains ℤ (TopCat.of ↥(Yset p q))).homology n) := by
  obtain ⟨e⟩ := nonempty_homology_Yset p q n hp hq hn
  haveI : IsZero ((singularChains ℤ (sphTop (p+1))).homology n) :=
    isZero_homology_sphTop p n hp hn hnp
  haveI : IsZero ((singularChains ℤ (sphTop (q+1))).homology n) :=
    isZero_homology_sphTop q n hq hn hnq
  exact IsZero.of_iso (isZero_biprod_of ‹IsZero _› ‹IsZero _›) e

/-- `HBiprod` vanishes in the degrees different from `p` and `q`. -/
lemma isZero_HBiprod_YV_high (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hnp : n ≠ p) (hnq : n ≠ q) :
    IsZero (HBiprod (Yset p q) (Vset p q) n) := by
  haveI := isZero_homology_Yset p q n hp hq hn hnp hnq
  haveI : ContractibleSpace ↥(Vset p q) := contractible_Vset p q
  haveI : IsZero ((singularChains ℤ (TopCat.of ↥(Vset p q))).homology n) :=
    homologyContractible n (by omega)
  exact isZero_homology_biprod _ _ n ‹IsZero _› ‹IsZero _›

/-- **Step 2, top degree**: for `n = p + q` the connecting map of the cover `{Yset, Vset}`
`H_{p+q}(X) ⟶ H_{p+q-1}(Y ∩ V)` is an isomorphism (assuming the injectivity of the projection
pair). -/
theorem isIso_mvδX_YV_top (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hproj : Function.Injective (projPair p q (p + q - 1)).hom) :
    IsIso (mvδX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
      (isOpen_Vset p q) (Yset_union_Vset p q) (p + q - 1)) := by
  haveI hcontr : ContractibleSpace ↥(Vset p q) := contractible_Vset p q
  have hf' : HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q))
      (p + q - 1) = 0 :=
    mvLeft_YV_eq_zero p q (p + q - 1) hp hq (by omega) hproj
  have hg : HomologicalComplex.homologyMap (mvRight (X := PSph p q) (Yset p q) (Vset p q))
      (p + q - 1 + 1) = 0 :=
    IsZero.eq_zero_of_src (isZero_HBiprod_YV_high p q (p + q - 1 + 1) hp hq (by omega)
      (by omega) (by omega)) _
  have h1 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₁ (X := PSph p q) (Yset p q) (Vset p q) (p + q - 1))
  have h2 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₂ (X := PSph p q) (Yset p q) (Vset p q) (p + q - 1 + 1))
  have h3 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₃ (X := PSph p q) (Yset p q) (Vset p q) (p + q - 1))
  haveI : IsIso (mvδ (X := PSph p q) (Yset p q) (Vset p q) (p + q - 1)) :=
    isIso_delta_of_exact_of_zero_zero _ _ _ _ h1 h2 h3 hg hf'
  rw [mvδX]
  infer_instance

/-- **Step 2, high degrees**: for `k+1 ≥ p+q+1` the map `H_{k+1}(X) ⟶ H_{k+1}(Y) ⊞ H_{k+1}(V)` is
an isomorphism. -/
theorem isIso_mvRightX_YV_high (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hk : p + q + 1 ≤ k + 1) :
    IsIso (mvRightX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
      (isOpen_Vset p q) (Yset_union_Vset p q) (k + 1)) := by
  have hf : HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q))
      (k + 1) = 0 :=
    IsZero.eq_zero_of_src (isZero_HInter_YV p q (k + 1) hp hq (by omega) (by omega)) _
  have h1 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₁ (X := PSph p q) (Yset p q) (Vset p q) k)
  have h2 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₂ (X := PSph p q) (Yset p q) (Vset p q) (k + 1))
  have h3 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₃ (X := PSph p q) (Yset p q) (Vset p q) k)
  have hf' : Function.Injective (HomologicalComplex.homologyMap (mvLeft
      (X := PSph p q) (Yset p q) (Vset p q)) k).hom :=
    injective_of_isZero_src (HomologicalComplex.homologyMap (mvLeft
      (X := PSph p q) (Yset p q) (Vset p q)) k)
      (isZero_HInter_YV p q k hp hq (by omega) (by omega))
  haveI : IsIso (HomologicalComplex.homologyMap (mvRight (X := PSph p q) (Yset p q) (Vset p q))
      (k + 1)) :=
    isIso_of_exact_of_zero_of_inj _ _ _ _ h1 h2 h3 hf hf'
  rw [mvRightX]
  infer_instance

end

end Work.Cohomology
