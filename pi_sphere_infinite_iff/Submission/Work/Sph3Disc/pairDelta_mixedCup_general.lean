import Mathlib
import Submission.Work.Cohomology.sph3DiscMixedDefs
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.relCochain_shortExact

/-!
# The connecting map of a pair and the mixed cup product, in general degrees

For a space `X`, a subspace `A ⊆ X`, an absolute class `x ∈ H^m(X)` and a class `y ∈ H^n(A)`, the
connecting map `δ : H^n(A) ⟶ H^{n+1}(X,A)` of the long exact sequence of the pair satisfies

`δ(x|_A ⌣ y) = (-1)^m · x ⌣ δy`   (`m = deg x`),

where on the right `x ⌣ -` is the mixed cup product `H^m(X) × H^{n+1}(X,A) ⟶ H^{m+n+1}(X,A)`
(of an absolute class with a relative one) and `δy ∈ H^{n+1}(X,A)`.

The file first records the two ingredients, in the generality needed here:

* `pdmc_pairδ_lift` — the computation rule for the connecting map: on the class of a cocycle `b` of
  `A`, `δ[b] = [d b̃]` for any lift `b̃` of `b` to `X`;
* `pdmc_cochainDiff_cup_left` — the Leibniz rule for the Alexander–Whitney product `α ⌣ β` with
  the left factor `α` a cocycle: `d(α ⌣ β) = (-1)^{deg α} · α ⌣ dβ`.

Together with the bookkeeping lemmas for `relClassOf` and the computation rule `cupH'_apply'` of
the cup product on cohomology, these give the target theorem
`Work.Sph3Disc.pairDelta_mixedCup_general`.

This is the general-degree version of `Work.Cohomology.sph3Disc_pairDelta_restr_cup`, the case
`m = n = 3` used for the pair `(S³ × D⁴, S³ × S³)` in the proof of the exoticness of Milnor's
sphere.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Sph3Disc

open Work.Cohomology

noncomputable section

/-! ## A computation rule for `cocycleOfK` -/

/-- The cycle associated with a `toSpanSingleton` cocycle is `cocycleOfK`. -/
lemma pdmc_liftCycles (K : CochainComplex (ModuleCat ℤ) ℕ) {n : ℕ} (α : ↑(K.X n))
    (j : ℕ) (hj : (ComplexShape.up ℕ).next n = j) (hj' : j = n + 1)
    (hk : ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) α) ≫ K.d n j = 0)
    (h : (ModuleCat.Hom.hom (K.d n (n + 1))) α = 0) :
    (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (K.X n) α)) j hj hk).hom 1
      = cocycleOfK K α h := by
  subst hj'
  unfold cocycleOfK
  rfl

/-! ## Scalar multiplication in a `ℤ`-module of cycles -/

lemma pdmc_iCycles_smul (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (c : ℤ) (z : K.cycles n) :
    (ModuleCat.Hom.hom (HomologicalComplex.iCycles K n)) (c • z)
      = c • (ModuleCat.Hom.hom (HomologicalComplex.iCycles K n)) z := by
  rw [← Int.cast_smul_eq_zsmul ℤ c z, LinearMap.map_smul, Int.cast_smul_eq_zsmul]

lemma pdmc_homologyπ_smul (K : CochainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (c : ℤ) (z : K.cycles n) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) (c • z)
      = c • (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n)) z := by
  rw [← Int.cast_smul_eq_zsmul ℤ c z, LinearMap.map_smul, Int.cast_smul_eq_zsmul]

/-! ## Elementary properties of `relClassOf` -/

lemma pdmc_relClassOf_congr (X : TopCat) (A : Set X) {n : ℕ}
    {a a' : relKern ℤ X A n} (h : a = a')
    (ha : relDiffLM ℤ X A n a = 0) (ha' : relDiffLM ℤ X A n a' = 0) :
    relClassOf ℤ X A a ha = relClassOf ℤ X A a' ha' := by
  subst h
  exact congrArg (fun h => relClassOf ℤ X A a h) (Subsingleton.elim _ _)

lemma pdmc_relClassOf_smul (X : TopCat) (A : Set X) (n : ℕ) (c : ℤ) (a : relKern ℤ X A n)
    (h : relDiffLM ℤ X A n (c • a) = 0) (h' : relDiffLM ℤ X A n a = 0) :
    relClassOf ℤ X A (c • a) h = c • relClassOf ℤ X A a h' := by
  rw [relClassOf, relClassOf]
  rw [← pdmc_homologyπ_smul (relComplex ℤ X A) n c (relCocycleOf ℤ X A a h')]
  congr 1
  apply iCycles_injective_K (relComplex ℤ X A) n
  calc (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex ℤ X A) n))
        (relCocycleOf ℤ X A (c • a) h)
      = c • a := iCycles_relCocycleOf ℤ X A (c • a) h
    _ = c • (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex ℤ X A) n))
          (relCocycleOf ℤ X A a h') := by
          rw [iCycles_relCocycleOf]
    _ = (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex ℤ X A) n))
          (c • relCocycleOf ℤ X A a h') := by
          rw [← Int.cast_smul_eq_zsmul ℤ c (relCocycleOf ℤ X A a h')]
          rw [LinearMap.map_smul]
          rw [Int.cast_smul_eq_zsmul]

/-- Scalar multiplication, with the representative written as the explicit element `c • a.1`. -/
lemma pdmc_relClassOf_smul_coe (X : TopCat) (A : Set X) (n : ℕ) (c : ℤ) (a : relKern ℤ X A n)
    (hmem : c • a.1 ∈ relKern ℤ X A n)
    (h : relDiffLM ℤ X A n ⟨c • a.1, hmem⟩ = 0) (h' : relDiffLM ℤ X A n a = 0) :
    relClassOf ℤ X A ⟨c • a.1, hmem⟩ h = c • relClassOf ℤ X A a h' := by
  rw [← pdmc_relClassOf_smul X A n c a (by rw [map_smul, h', smul_zero]) h']
  exact pdmc_relClassOf_congr X A (Subtype.ext (by simp)) h _

/-! ## Naturality of the cup product -/

/-- The Leibniz rule when the left factor is a cocycle. -/
lemma pdmc_cochainDiff_cup_left (X : SSet) {n m : ℕ}
    (α : Cochain ℤ X n) (hα : cochainDiff ℤ X α = 0) (β : Cochain ℤ X m) :
    cochainDiff ℤ X (cup ℤ X α β) = ((-1 : ℤ) ^ n) • cup ℤ X α (cochainDiff ℤ X β) := by
  rw [cupLeibniz ℤ X α β, hα, cup_zero_left' ℤ X, eqRec_zero ℤ X, zero_add]

lemma pdmc_cyclesMap_cocycleOfK (K L : CochainComplex (ModuleCat ℤ) ℕ)
    (φ : K ⟶ L) {n : ℕ} (α : ↑(K.X n))
    (hα : (ModuleCat.Hom.hom (K.d n (n + 1))) α = 0)
    (h : (ModuleCat.Hom.hom (L.d n (n + 1))) ((ModuleCat.Hom.hom (φ.f n)) α) = 0) :
    HomologicalComplex.cyclesMap φ n (cocycleOfK K α hα) =
      cocycleOfK L ((ModuleCat.Hom.hom (φ.f n)) α) h := by
  apply iCycles_injective_K L n
  have h1 := congrArg (fun (g : K.cycles n ⟶ L.X n) => g.hom (cocycleOfK K α hα))
    (HomologicalComplex.cyclesMap_i φ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [iCycles_cocycleOfK K α hα] at h1
  rw [h1, iCycles_cocycleOfK L ((ModuleCat.Hom.hom (φ.f n)) α) h]

lemma pdmc_homologyMap_restr (X : TopCat) (A : Set X) {n : ℕ}
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : cochainDiff ℤ (TopCat.toSSet.obj X) α = 0)
    (h : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of A)) (((restr ℤ X A).f n).hom α) = 0) :
    (HomologicalComplex.homologyMap (restr ℤ X A) n)
        (cohomologyClassOf ℤ (TopCat.toSSet.obj X) α hα)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of A))
          (((restr ℤ X A).f n).hom α) h := by
  have hα' : (ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1))) α = 0 := by
    rw [singularCochain_d_apply]; exact hα
  have h' : (ModuleCat.Hom.hom ((singularCochainComplex ℤ (TopCat.of A)).d n (n+1)))
      (((restr ℤ X A).f n).hom α) = 0 := by
    rw [singularCochain_d_apply]; exact h
  change (HomologicalComplex.homologyMap (restr ℤ X A) n)
      (((singularCochainComplex ℤ X).homologyπ n).hom
        (cocycleOfK (singularCochainComplex ℤ X) α hα'))
    = ((singularCochainComplex ℤ (TopCat.of A)).homologyπ n).hom
        (cocycleOfK (singularCochainComplex ℤ (TopCat.of A)) (((restr ℤ X A).f n).hom α) h')
  have hnat := congrArg (fun (g : (singularCochainComplex ℤ X).cycles n ⟶
        (singularCochainComplex ℤ (TopCat.of A)).homology n) => g.hom
      (cocycleOfK (singularCochainComplex ℤ X) α hα'))
    (HomologicalComplex.homologyπ_naturality (restr ℤ X A) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat, pdmc_cyclesMap_cocycleOfK]

/-! ## The connecting map on the class of a cocycle -/

theorem pdmc_pairδ_lift (X : TopCat) (A : Set X) (n : ℕ)
    (b : Cochain ℤ (TopCat.toSSet.obj (TopCat.of A)) n)
    (hb : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of A)) b = 0)
    (bt : Cochain ℤ (TopCat.toSSet.obj X) n)
    (hbt : ((restr ℤ X A).f n).hom bt = b) :
    ∃ (hmem : ((singularCochainComplex ℤ X).d n (n + 1)).hom bt ∈ relKern ℤ X A (n + 1)),
      ∃ (hcoc : relDiffLM ℤ X A (n + 1)
          ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ = 0),
        pairδ ℤ X A n (cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of A)) b hb)
          = relClassOf ℤ X A
              ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ hcoc := by
  have hmem : ((singularCochainComplex ℤ X).d n (n + 1)).hom bt ∈ relKern ℤ X A (n + 1) := by
    rw [relKern, LinearMap.mem_ker]
    have h := congrArg ModuleCat.Hom.hom ((restr ℤ X A).comm n (n + 1))
    simp only [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h bt
    simp only [LinearMap.comp_apply] at h2
    rw [singularCochain_d_apply ℤ (TopCat.of A), hbt, hb] at h2
    exact h2.symm
  have hcoc : relDiffLM ℤ X A (n + 1)
      ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero]
    have h := HomologicalComplex.d_comp_d (singularCochainComplex ℤ X) n (n+1) (n+2)
    have h2 := congrArg ModuleCat.Hom.hom h
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    exact LinearMap.congr_fun h2 bt
  refine ⟨hmem, hcoc, ?_⟩
  have hx₃ : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₃).X n) b))
      ≫ ((pairShort ℤ X A).X₃.d n (n+1)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    change r • ((singularCochainComplex ℤ (TopCat.of A)).d n (n + 1)).hom b = 0
    rw [singularCochain_d_apply ℤ (TopCat.of A), hb, smul_zero]
  have hx₂ : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₂).X n) bt))
      ≫ ((pairShort ℤ X A).g.f n)
      = (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₃).X n) b)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul]
    change r • ((restr ℤ X A).f n).hom bt = r • b
    rw [hbt]
  have hx₁ : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₁).X (n+1))
        ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩))
      ≫ ((pairShort ℤ X A).f.f (n+1))
      = (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₂).X n) bt))
        ≫ ((pairShort ℤ X A).X₂.d n (n+1)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul]
    change r • (⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ :
        relKern ℤ X A (n+1)) = r • ((singularCochainComplex ℤ X).d n (n+1)).hom bt
    simp
  have hb' : (ModuleCat.Hom.hom (((pairShort ℤ X A).X₃).d n (n + 1))) b = 0 := by
    change (ModuleCat.Hom.hom ((singularCochainComplex ℤ (TopCat.of A)).d n (n + 1))) b = 0
    rw [singularCochain_d_apply ℤ (TopCat.of A)]; exact hb
  have hcoc' : (ModuleCat.Hom.hom (((pairShort ℤ X A).X₁).d (n + 1) (n + 2)))
      ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ = 0 := by
    change (ModuleCat.Hom.hom ((relComplex ℤ X A).d (n + 1) (n + 2)))
      ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ = 0
    rw [relComplex_d_apply]; exact hcoc
  have hpk : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₁).X (n+1))
        ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩))
      ≫ ((pairShort ℤ X A).X₁.d (n+1) (n+2)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hcoc', smul_zero]
  have key : ∀ (hij : (ComplexShape.up ℕ).Rel n (n+1)),
      (pairShort_shortExact ℤ X A).δ n (n+1) hij
        (cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of A)) b hb)
      = relClassOf ℤ X A ⟨((singularCochainComplex ℤ X).d n (n+1)).hom bt, hmem⟩ hcoc := by
    intro hij
    have hδ := CategoryTheory.ShortComplex.ShortExact.δ_eq (hS := pairShort_shortExact ℤ X A)
      n (n+1) hij
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₃).X n) b)) hx₃
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₂).X n) bt)) hx₂
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₁).X (n+1))
        ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩)) hx₁
      (n+2) (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl))
    have hδ' := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
        (((pairShort ℤ X A).X₁).homology (n+1))) => g.hom 1) hδ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hδ'
    have h₃ : (((pairShort ℤ X A).X₃.liftCycles
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₃).X n) b)) (n+1)
          ((ComplexShape.up ℕ).next_eq' hij) hx₃).hom 1)
        = cocycleOfK ((pairShort ℤ X A).X₃) b hb' :=
      pdmc_liftCycles ((pairShort ℤ X A).X₃) b (n+1)
        ((ComplexShape.up ℕ).next_eq' hij) rfl hx₃ hb'
    have h₁ : (((pairShort ℤ X A).X₁.liftCycles
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (((pairShort ℤ X A).X₁).X (n+1))
            ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩)) (n+2)
          (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl)) hpk).hom 1)
        = cocycleOfK ((pairShort ℤ X A).X₁)
            ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ hcoc' :=
      pdmc_liftCycles ((pairShort ℤ X A).X₁)
        ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ (n+2)
        (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl)) rfl hpk hcoc'
    rw [h₃, h₁] at hδ'
    change (ModuleCat.Hom.hom ((pairShort_shortExact ℤ X A).δ n (n + 1) hij))
        ((ModuleCat.Hom.hom ((singularCochainComplex ℤ (TopCat.of A)).homologyπ n))
          (cocycleOfK (singularCochainComplex ℤ (TopCat.of A)) b hb')) =
        (ModuleCat.Hom.hom ((relComplex ℤ X A).homologyπ (n + 1)))
          (cocycleOfK (relComplex ℤ X A)
            ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ hcoc')
    exact hδ'
  exact key _

/-! ## The main theorem -/

theorem pairDelta_mixedCup_general (X : TopCat) (A : Set X) (m n : ℕ) (x : Work.Cohomology.singularCohomology ℤ m X) (y : (Work.Cohomology.singularCochainComplex ℤ (TopCat.of A)).homology n) : Work.Cohomology.pairδ ℤ X A (m + n) (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of A)) m n ((HomologicalComplex.homologyMap (Work.Cohomology.restr ℤ X A) m).hom x) y) = ((-1 : ℤ) ^ m) • (Work.Cohomology.mixedCup X A m (n + 1) x (Work.Cohomology.pairδ ℤ X A n y)) := by
  obtain ⟨α, hα, hx⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj X) m x
  obtain ⟨b, hb, hβ⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of A)) n y
  obtain ⟨bt, hbt⟩ := surjective_restr ℤ X A n b
  have hrestrα : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of A))
      (((restr ℤ X A).f m).hom α) = 0 := by
    have h := congrArg ModuleCat.Hom.hom ((restr ℤ X A).comm m (m+1))
    simp only [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h α
    simp only [LinearMap.comp_apply] at h2
    rw [singularCochain_d_apply ℤ (TopCat.of A), singularCochain_d_apply ℤ X, hα,
      map_zero] at h2
    exact h2
  have hbc : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of A))
      (cup ℤ (TopCat.toSSet.obj (TopCat.of A)) (((restr ℤ X A).f m).hom α) b) = 0 :=
    cochainDiff_cup_of_cocycles ℤ (TopCat.toSSet.obj (TopCat.of A)) _ _ hrestrα hb
  have hbtcup : ((restr ℤ X A).f (m+n)).hom (cup ℤ (TopCat.toSSet.obj X) α bt)
      = cup ℤ (TopCat.toSSet.obj (TopCat.of A)) (((restr ℤ X A).f m).hom α) b := by
    have h := (cupNatural ℤ (TopCat.toSSet.map (subtypeIncl X A)) α bt).symm
    rw [show (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f n).hom.dualMap) bt = b from hbt] at h
    exact h
  obtain ⟨hmem7, hcoc7, hδ7⟩ := pdmc_pairδ_lift X A (m+n)
    (cup ℤ (TopCat.toSSet.obj (TopCat.of A)) (((restr ℤ X A).f m).hom α) b) hbc
    (cup ℤ (TopCat.toSSet.obj X) α bt) hbtcup
  obtain ⟨hmem4, hcoc4, hδ3⟩ := pdmc_pairδ_lift X A n b hb bt hbt
  obtain ⟨hmemM, hM, hMmix⟩ := mixedCup_apply X A m (n+1) α
    ⟨(ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1))) bt, hmem4⟩ hα hcoc4
  have hleib : (ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d (m+n) (m+n+1)))
      (cup ℤ (TopCat.toSSet.obj X) α bt)
      = ((-1 : ℤ) ^ m) • cup ℤ (TopCat.toSSet.obj X) α
          ((ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1))) bt) := by
    rw [singularCochain_d_apply ℤ X,
        pdmc_cochainDiff_cup_left (TopCat.toSSet.obj X) α hα bt,
        ← singularCochain_d_apply ℤ X bt]
  have hL : pairδ ℤ X A (m+n)
        (cupH' ℤ (TopCat.toSSet.obj (TopCat.of A)) m n
          ((HomologicalComplex.homologyMap (restr ℤ X A) m) x) y)
      = ((-1 : ℤ) ^ m) • relClassOf ℤ X A
          ⟨cup ℤ (TopCat.toSSet.obj X) α
            ((ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1))) bt), hmemM⟩ hM := by
    rw [← hx, ← hβ, pdmc_homologyMap_restr X A α hα hrestrα,
        cupH'_apply' ℤ (TopCat.toSSet.obj (TopCat.of A)) (((restr ℤ X A).f m).hom α) b
          hrestrα hb, hδ7]
    have ha : (⟨(ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d (m+n) (m+n+1)))
          (cup ℤ (TopCat.toSSet.obj X) α bt), hmem7⟩ : relKern ℤ X A (m+n+1))
        = ⟨((-1 : ℤ) ^ m) • cup ℤ (TopCat.toSSet.obj X) α
            ((ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1))) bt),
            hleib ▸ hmem7⟩ :=
      Subtype.ext hleib
    refine (pdmc_relClassOf_congr X A ha hcoc7 (ha ▸ hcoc7)).trans ?_
    exact pdmc_relClassOf_smul_coe X A (m+(n+1)) ((-1 : ℤ) ^ m)
      ⟨_, hmemM⟩ (hleib ▸ hmem7) (ha ▸ hcoc7) hM
  have hR : ((-1 : ℤ) ^ m) • (mixedCup X A m (n+1) x (pairδ ℤ X A n y))
      = ((-1 : ℤ) ^ m) • relClassOf ℤ X A
          ⟨cup ℤ (TopCat.toSSet.obj X) α
            ((ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n+1))) bt), hmemM⟩ hM := by
    rw [← hx, ← hβ, hδ3, hMmix]
  rw [hL, hR]

end

end Work.Sph3Disc
