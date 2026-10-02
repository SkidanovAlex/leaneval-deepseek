import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereDefs
import Submission.Work.Cohomology.CompatTrans.prodSphereAux
import Submission.Work.Cohomology.CompatTrans.prodSphereStep1
import Submission.Work.Cohomology.CompatTrans.prodSphereStep2
import Submission.Work.Cohomology.CompatTrans.proj_pair_injective
import Submission.Work.Cohomology.CompatTrans.punctured_cap_prod_sphere
import Submission.Work.Cohomology.CompatTrans.pathConnected_Wset
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.homologyContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The singular homology of a product of two spheres

`Hₙ(Sᵖ × Sᵍ; ℤ) ≅ ℤ^{[n=0]+[n=p]+[n=q]+[n=p+q]}` for `p, q ≥ 1`.

The proof uses the two Mayer–Vietoris covers

* `Sᵖ × Sᵍ \ {pt} = ((Sᵖ \ {N}) × Sᵍ) ∪ (Sᵖ × (Sᵍ \ {N}))`, whose intersection is contractible
  (`isIso_mvRightX_A1B1`, `nonempty_homology_Yset`), giving `Hₙ(Sᵖ × Sᵍ \ {pt}) ≅ Hₙ(Sᵖ) ⊞ Hₙ(Sᵍ)`;
* `Sᵖ × Sᵍ = (Sᵖ × Sᵍ \ {pt}) ∪ (capA p × capA q)`, where `capA p × capA q` is a contractible open
  set and its punctured form is homotopy equivalent to `Sᵖ⁺ᵍ⁻¹` (`punctured_cap_prod_sphere`).

The second cover reduces the computation to the first (`prodSphereStep2`), the key input being the
vanishing of the connecting map `Hₙ(Sᵖ⁺ᵍ⁻¹) ⟶ Hₙ(Sᵖ × Sᵍ \ {pt})`, which follows from the
injectivity of the pair of the two projections (`proj_pair_injective`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-! ## 1. The exponent and the elementary module isomorphisms -/

/-- The number of cells of `Sᵖ × Sᵍ` in degree `n`. -/
def expo (p q n : ℕ) : ℕ :=
  (if n = 0 then 1 else 0) + (if n = p then 1 else 0) + (if n = q then 1 else 0) +
    (if n = p + q then 1 else 0)

lemma expo_zero (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) : expo p q 0 = 1 := by
  simp only [expo, zero_ne_one, ↓reduceIte]
  have h1 : (0 : ℕ) ≠ p := by omega
  have h2 : (0 : ℕ) ≠ q := by omega
  have h3 : (0 : ℕ) ≠ p + q := by omega
  simp [h1, h2, h3]

lemma expo_low (p q k : ℕ) (hk : k + 1 ≤ p + q - 1) :
    expo p q (k + 1) = (if k + 1 = p then 1 else 0) + (if k + 1 = q then 1 else 0) := by
  have h0 : k + 1 ≠ 0 := by omega
  have hpq : k + 1 ≠ p + q := by omega
  simp only [expo, h0, hpq, ↓reduceIte, add_zero, zero_add]

lemma expo_top (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) : expo p q (p + q) = 1 := by
  have h0 : p + q ≠ 0 := by omega
  have h1 : p + q ≠ p := by omega
  have h2 : p + q ≠ q := by omega
  simp only [expo, h0, h1, h2, ↓reduceIte, add_zero, zero_add]

/-- The exponent in the degree just below the top one, written in the form in which it arises. -/
lemma expo_shift (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    expo p q ((p + q - 1) + 1) = 1 := by
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p + q)]
  exact expo_top p q hp hq

lemma expo_high (p q k : ℕ) (hk : p + q + 1 ≤ k + 1) : expo p q (k + 1) = 0 := by
  have h0 : k + 1 ≠ 0 := by omega
  have h1 : k + 1 ≠ p := by omega
  have h2 : k + 1 ≠ q := by omega
  have h3 : k + 1 ≠ p + q := by omega
  simp [expo, h0, h1, h2, h3]

/-- `ℤ ≅ (Fin 1 → ℤ)`. -/
lemma nonempty_int_fin_one : Nonempty (ModuleCat.of ℤ ℤ ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) :=
  ⟨LinearEquiv.toModuleIso (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm⟩

/-- `(Fin 0 → ℤ)` is the zero module. -/
lemma isZero_fin_zero : IsZero (ModuleCat.of ℤ (Fin 0 → ℤ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- Any two zero objects of `ModuleCat ℤ` are isomorphic. -/
lemma nonempty_iso_of_isZero {M N : ModuleCat ℤ} (hM : IsZero M) (hN : IsZero N) :
    Nonempty (M ≅ N) :=
  ⟨hM.isoZero ≪≫ hN.isoZero.symm⟩

/-- `ℤ^a ⊞ ℤ^b ≅ ℤ^{a+b}`. -/
theorem nonempty_finArrow_biprod (a b : ℕ) :
    Nonempty ((ModuleCat.of ℤ (Fin a → ℤ)) ⊞ (ModuleCat.of ℤ (Fin b → ℤ)) ≅
      ModuleCat.of ℤ (Fin (a + b) → ℤ)) := by
  have e1 : ((Fin a → ℤ) × (Fin b → ℤ)) ≃ₗ[ℤ] ((Fin a ⊕ Fin b) → ℤ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℤ ℤ).symm
  have e2 : ((Fin a ⊕ Fin b) → ℤ) ≃ₗ[ℤ] (Fin (a + b) → ℤ) :=
    (LinearEquiv.piCongrLeft (R := ℤ) (φ := fun _ : Fin (a + b) => ℤ)
      (e := (finSumFinEquiv (m := a) (n := b))))
  exact ⟨ModuleCat.biprodIsoProd (ModuleCat.of ℤ (Fin a → ℤ)) (ModuleCat.of ℤ (Fin b → ℤ))
    ≪≫ LinearEquiv.toModuleIso (e1.trans e2)⟩

/-- `Hₙ(Sᵐ) ≅ ℤ^{[n=m]}` for `n ≥ 1`, `m ≥ 1`, in the `sphTop` model. -/
theorem nonempty_homology_sphere_pos (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Nonempty ((singularChains ℤ (sphTop (m+1))).homology n ≅
      ModuleCat.of ℤ (Fin (if n = m then 1 else 0) → ℤ)) := by
  by_cases hnm : n = m
  · rw [if_pos hnm, hnm]
    obtain ⟨e⟩ := sphereHomology_aux m hm
    exact ⟨e.trans (nonempty_int_fin_one).some⟩
  · have hz : IsZero ((singularChains ℤ (sphTop (m+1))).homology n) := by
      obtain ⟨e⟩ := homologyIso_of_homotopyEquiv
        (Homeomorph.setCongr (sphereSet_eq' (m+1))).toHomotopyEquiv n
      exact IsZero.of_iso (sphereVanishing m n hm (by omega) hnm) e.symm
    have hz' : IsZero (ModuleCat.of ℤ (Fin (if n = m then 1 else 0) → ℤ)) := by
      rw [if_neg hnm]
      exact isZero_fin_zero
    exact nonempty_iso_of_isZero hz hz'

/-! ## 2. Transporting the sphere model along an equality of dimensions -/

/-- `Hₙ(S^{a-1}) ≅ Hₙ(S^{b-1})` when `a = b`. -/
lemma nonempty_homology_sphTop_cast {a b : ℕ} (h : a = b) (n : ℕ) :
    Nonempty ((singularChains ℤ (sphTop a)).homology n ≅
      (singularChains ℤ (sphTop b)).homology n) := by
  subst h
  exact ⟨Iso.refl _⟩

/-! ## 3. The low degrees of the second Mayer–Vietoris sequence -/

/-- **Step 2, low degrees**: for `k+1 ≤ p+q-1` the map `H_{k+1}(X) ⟶ H_{k+1}(Y) ⊞ H_{k+1}(V)` of
the cover `{Yset, Vset}` of `Sᵖ × Sᵍ` is an isomorphism.  (`Yset` is the complement of the base
point, `Vset` the product of the two caps, a contractible open set.) -/
private theorem isIso_mvRightX_YV_low (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hk : k + 1 ≤ p + q - 1) :
    IsIso (mvRightX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
      (isOpen_Vset p q) (Yset_union_Vset p q) (k + 1)) := by
  have hproj : Function.Injective (Work.Cohomology.projPair p q (k + 1)).hom :=
    proj_pair_injective p q (k + 1) hp hq (by omega)
  have hf : HomologicalComplex.homologyMap (mvLeft (X := PSph p q) (Yset p q) (Vset p q))
      (k + 1) = 0 :=
    Work.Cohomology.mvLeft_YV_eq_zero p q (k + 1) hp hq (by omega) hproj
  have h1 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₁ (X := PSph p q) (Yset p q) (Vset p q) k)
  have h2 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₂ (X := PSph p q) (Yset p q) (Vset p q) (k + 1))
  have h3 := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (mv_H_exact₃ (X := PSph p q) (Yset p q) (Vset p q) k)
  have hf' : Function.Injective (HomologicalComplex.homologyMap (mvLeft
      (X := PSph p q) (Yset p q) (Vset p q)) k).hom := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      haveI hpc : PathConnectedSpace ↥(Yset p q ∩ Vset p q) :=
        Set.inter_comm (Yset p q) (Vset p q) ▸ (pathConnected_Wset p q hp hq)
      exact @mvLeft_zero_injective (PSph p q) (Yset p q) (Vset p q) hpc
    · exact injective_of_isZero_src (HomologicalComplex.homologyMap (mvLeft
        (X := PSph p q) (Yset p q) (Vset p q)) k)
        (Work.Cohomology.isZero_HInter_YV p q k hp hq (by omega) (by omega))
  haveI : IsIso (HomologicalComplex.homologyMap (mvRight (X := PSph p q) (Yset p q) (Vset p q))
      (k + 1)) :=
    isIso_of_exact_of_zero_of_inj _ _ _ _ h1 h2 h3 hf hf'
  rw [mvRightX]
  infer_instance

/-- **The low degrees of `Hₙ(Sᵖ × Sᵍ)`**: for `1 ≤ n = k+1 ≤ p+q-1` we have
`Hₙ(Sᵖ × Sᵍ) ≅ ℤ^{[n=p]+[n=q]}`. -/
theorem nonempty_homology_PSph_low (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hk : k + 1 ≤ p + q - 1) :
    Nonempty ((singularChains ℤ (PSph p q)).homology (k + 1) ≅
      ModuleCat.of ℤ (Fin ((if k + 1 = p then 1 else 0) + (if k + 1 = q then 1 else 0)) → ℤ)) := by
  haveI hi : IsIso (mvRightX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
      (isOpen_Vset p q) (Yset_union_Vset p q) (k + 1)) :=
    isIso_mvRightX_YV_low p q k hp hq hk
  let eB := homologyBiprodIso (singularChains ℤ (TopCat.of ↥(Yset p q)))
    (singularChains ℤ (TopCat.of ↥(Vset p q))) (k + 1)
  obtain ⟨eY⟩ := nonempty_homology_Yset p q (k + 1) hp hq (by omega)
  obtain ⟨eSp⟩ := nonempty_homology_sphere_pos p (k + 1) hp (by omega)
  obtain ⟨eSq⟩ := nonempty_homology_sphere_pos q (k + 1) hq (by omega)
  haveI hVc : ContractibleSpace ↥(Vset p q) := contractible_Vset p q
  have hV : IsZero ((singularChains ℤ (TopCat.of ↥(Vset p q))).homology (k + 1)) :=
    homologyContractible (k + 1) (by omega)
  obtain ⟨eV⟩ := nonempty_iso_of_isZero hV isZero_fin_zero
  exact ⟨(asIso (mvRightX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
        (isOpen_Vset p q) (Yset_union_Vset p q) (k + 1))).symm
      ≪≫ eB ≪≫ biprod.mapIso eY (Iso.refl _)
      ≪≫ biprod.mapIso (biprod.mapIso eSp eSq) eV
      ≪≫ biprod.mapIso (nonempty_finArrow_biprod (if k + 1 = p then 1 else 0)
            (if k + 1 = q then 1 else 0)).some (Iso.refl _)
      ≪≫ (nonempty_finArrow_biprod ((if k + 1 = p then 1 else 0) +
            (if k + 1 = q then 1 else 0)) 0).some⟩

/-! ## 4. The top degree: the punctured product of the two caps -/

/-- **The top degree**: `H_{p+q-1}(V ∩ Y) ≅ ℤ`, the homology of the punctured product of the two
caps, which is homotopy equivalent to `S^{p+q-1}`. -/
theorem nonempty_HInter_YV_top (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Nonempty (HInter (Yset p q) (Vset p q) (p + q - 1) ≅ ModuleCat.of ℤ (Fin 1 → ℤ)) := by
  obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (Yset_inter_Vset p q)).toHomotopyEquiv (p + q - 1)
  obtain ⟨e2⟩ := homologyIso_of_homotopyEquiv (punctured_cap_prod_sphere p q hp hq).some
    (p + q - 1)
  obtain ⟨e3⟩ := homologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (sphereSet_eq' (p + q))).toHomotopyEquiv (p + q - 1)
  obtain ⟨e4⟩ := nonempty_homology_sphTop_cast (by omega : p + q = (p + q - 1) + 1) (p + q - 1)
  obtain ⟨e5⟩ := sphereHomology_aux (p + q - 1) (by omega)
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5 ≪≫ (nonempty_int_fin_one).some⟩

/-! ## 5. The high degrees -/

/-- `Hₙ(Sᵖ × Sᵍ) = 0` for `n > p+q`. -/
theorem isZero_homology_PSph_high (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hk : p + q + 1 ≤ k + 1) :
    IsZero ((singularChains ℤ (PSph p q)).homology (k + 1)) := by
  haveI hi : IsIso (mvRightX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
      (isOpen_Vset p q) (Yset_union_Vset p q) (k + 1)) :=
    Work.Cohomology.isIso_mvRightX_YV_high p q k hp hq hk
  have hb : IsZero (HBiprod (Yset p q) (Vset p q) (k + 1)) :=
    Work.Cohomology.isZero_HBiprod_YV_high p q (k + 1) hp hq (by omega) (by omega) (by omega)
  have eXY : HBiprod (Yset p q) (Vset p q) (k + 1) ≅
      (singularChains ℤ (PSph p q)).homology (k + 1) :=
    asIso (mvRightX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
      (isOpen_Vset p q) (Yset_union_Vset p q) (k + 1))
  exact IsZero.of_iso hb eXY.symm

/-! ## 6. The homology of `Sᵖ × Sᵍ` in every degree -/

/-- **The singular homology of a product of two spheres**: `Hₙ(Sᵖ × Sᵍ; ℤ) ≅ ℤ^{expo p q n}`. -/
theorem nonempty_homology_PSph (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Nonempty ((singularChains ℤ (PSph p q)).homology n ≅
      ModuleCat.of ℤ (Fin (expo p q n) → ℤ)) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [expo_zero p q hp hq]
    haveI h1 : PathConnectedSpace ↥(sphSet (p + 1)) := pathConnected_sphSet (p + 1) (by omega)
    haveI h2 : PathConnectedSpace ↥(sphSet (q + 1)) := pathConnected_sphSet (q + 1) (by omega)
    haveI h3 : PathConnectedSpace ↥(PSph p q) := inferInstance
    have hε : ((singularHomologyFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj (PSph p q)
        ≅ ModuleCat.of ℤ ℤ := asIso (TopCat.singularHomology₀ε (PSph p q) (ModuleCat.of ℤ ℤ))
    exact ⟨hε ≪≫ (nonempty_int_fin_one).some⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rcases lt_trichotomy k (p + q - 1) with hlt | heq | hgt
    · rw [expo_low p q k (by omega)]
      exact nonempty_homology_PSph_low p q k hp hq (by omega)
    · subst heq
      rw [expo_shift p q hp hq]
      haveI hδ : IsIso (mvδX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
          (isOpen_Vset p q) (Yset_union_Vset p q) (p + q - 1)) :=
        Work.Cohomology.isIso_mvδX_YV_top p q hp hq (proj_pair_injective p q (p + q - 1) hp hq (by omega))
      exact ⟨asIso (mvδX (X := PSph p q) (Yset p q) (Vset p q) (isOpen_Yset p q)
          (isOpen_Vset p q) (Yset_union_Vset p q) (p + q - 1))
        ≪≫ (nonempty_HInter_YV_top p q hp hq).some⟩
    · rw [expo_high p q k (by omega)]
      exact nonempty_iso_of_isZero (isZero_homology_PSph_high p q k hp hq (by omega))
        isZero_fin_zero

/-! ## 7. The theorem -/

/-- **The singular homology of a product of two spheres**, stated for the model
`Metric.sphere (0 : ℝ^{p+1}) 1 × Metric.sphere (0 : ℝ^{q+1}) 1` of `Sᵖ × Sᵍ`. -/
theorem homology_prod_sphere (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Nonempty ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (p + 1))) 1 ×
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1))).homology n ≅
      ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = p then 1 else 0) +
        (if n = q then 1 else 0) + (if n = p + q then 1 else 0)) → ℤ)) := by
  obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv
    (Homeomorph.prodCongr (Homeomorph.setCongr (sphereSet_eq' (p + 1)))
      (Homeomorph.setCongr (sphereSet_eq' (q + 1)))).toHomotopyEquiv n
  obtain ⟨e2⟩ := nonempty_homology_PSph p q n hp hq
  exact ⟨e1 ≪≫ e2⟩

end

end Work.Cohomology
