import Mathlib
import Submission.Work.StemsB.MixedCupR
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.CupRing

/-!
# The connecting map of a pair and the mixed cup product over an arbitrary ring

For a space `X`, a subspace `A ⊆ X`, an absolute class `x ∈ H^m(X;R)` and a class `y ∈ H^n(A;R)`,
the connecting map `δ : H^n(A;R) ⟶ H^{n+1}(X,A;R)` of the long exact sequence of the pair satisfies

`δ(x|_A ⌣ y) = (-1)^m · x ⌣ δy`   (`m = deg x`),

where on the right `x ⌣ -` is the mixed cup product `H^m(X;R) × H^{n+1}(X,A;R) ⟶ H^{m+n+1}(X,A;R)`
of an absolute with a relative class, chosen in `Submission/Work/StemsB/MixedCupR.lean`
(`Work.Cohomology.mixedCupR`).

This is the coefficient-general form of `Work.Sph3Disc.pairDelta_mixedCup_general` (which is over
`ℤ`): the whole derivation is formal in the coefficient ring, so the same proof goes through with
`ℤ` replaced by `R`.  The `ℤ`-specific ingredient of the older proof — `Int.cast_smul_eq_zsmul`,
used to identify `ℤ`-scalar multiplication with the module structure — is simply absent here: over
a general `R` the relevant statements are `LinearMap.map_smul` for `R`-scalars, which is what
`Work.Cohomology.iCycles_smul_K` and `Work.Cohomology.homologyπ_smul_K` already record.

The ingredients are

* `liftCycles_ofHom_hom_one_R` — `cocycleOfK` is `liftCycles` of the singleton map;
* `relClassOf_congr_R`, `relClassOf_smul_R`, `relClassOf_smul_coe_R` — elementary bookkeeping for
  the class of a relative cocycle;
* `cochainDiff_cup_left_R` — the Leibniz rule for the Alexander–Whitney product with the left
  factor a cocycle: `d(α ⌣ β) = (-1)^{deg α} · α ⌣ dβ`;
* `cyclesMap_cocycleOfK_R`, `homologyMap_restr_cohomologyClassOf_R` — the restriction on cohomology
  of the class of a cocycle;
* `pairδ_cohomologyClassOf_lift_R` — the computation rule for the connecting map: on the class of a
  cocycle `b` of `A`, `δ[b] = [d b̃]` for any lift `b̃` of `b` to `X`;
* together with `cupH'_apply'` and the computation rule `mixedCupR_apply` of the mixed product,
  these give `pairDelta_mixedCup_general_R`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.StemsB

open Work.Cohomology

noncomputable section

/-! ## A computation rule for `cocycleOfK` -/

/-- The cycle associated with a `toSpanSingleton` cocycle is `cocycleOfK`. -/
lemma liftCycles_ofHom_hom_one_R (R : Type) [CommRing R]
    (K : CochainComplex (ModuleCat R) ℕ) {n : ℕ} (α : ↑(K.X n))
    (j : ℕ) (hj : (ComplexShape.up ℕ).next n = j) (hj' : j = n + 1)
    (hk : ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) α) ≫ K.d n j = 0)
    (h : (ModuleCat.Hom.hom (K.d n (n + 1))) α = 0) :
    (K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) α)) j hj hk).hom 1
      = cocycleOfK K α h := by
  subst hj'
  unfold cocycleOfK
  rfl

/-! ## Elementary properties of `relClassOf` -/

lemma relClassOf_congr_R (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n : ℕ}
    {a a' : relKern R X A n} (h : a = a')
    (ha : relDiffLM R X A n a = 0) (ha' : relDiffLM R X A n a' = 0) :
    relClassOf R X A a ha = relClassOf R X A a' ha' := by
  subst h
  exact congrArg (fun hh => relClassOf R X A a hh) (Subsingleton.elim _ _)

lemma relClassOf_smul_R (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ) (c : R)
    (a : relKern R X A n)
    (h : relDiffLM R X A n (c • a) = 0) (h' : relDiffLM R X A n a = 0) :
    relClassOf R X A (c • a) h = c • relClassOf R X A a h' := by
  rw [relClassOf, relClassOf]
  rw [← homologyπ_smul_K (relComplex R X A) n c (relCocycleOf R X A a h')]
  congr 1
  apply iCycles_injective_K (relComplex R X A) n
  calc (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex R X A) n))
        (relCocycleOf R X A (c • a) h)
      = c • a := iCycles_relCocycleOf R X A (c • a) h
    _ = c • (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex R X A) n))
          (relCocycleOf R X A a h') := by
          rw [iCycles_relCocycleOf]
    _ = (ModuleCat.Hom.hom (HomologicalComplex.iCycles (relComplex R X A) n))
          (c • relCocycleOf R X A a h') := by
          rw [LinearMap.map_smul]

/-- Scalar multiplication, with the representative written as the explicit element `c • a.1`. -/
lemma relClassOf_smul_coe_R (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ) (c : R)
    (a : relKern R X A n)
    (hmem : c • a.1 ∈ relKern R X A n)
    (h : relDiffLM R X A n ⟨c • a.1, hmem⟩ = 0) (h' : relDiffLM R X A n a = 0) :
    relClassOf R X A ⟨c • a.1, hmem⟩ h = c • relClassOf R X A a h' := by
  rw [← relClassOf_smul_R R X A n c a (by rw [map_smul, h', smul_zero]) h']
  exact relClassOf_congr_R R X A (Subtype.ext (by simp)) h _

/-! ## The Leibniz rule with a cocycle on the left -/

/-- The Leibniz rule when the left factor is a cocycle. -/
lemma cochainDiff_cup_left_R (R : Type) [CommRing R] (X : SSet) {n m : ℕ}
    (α : Cochain R X n) (hα : cochainDiff R X α = 0) (β : Cochain R X m) :
    cochainDiff R X (cup R X α β) = ((-1 : R) ^ n) • cup R X α (cochainDiff R X β) := by
  rw [cupLeibniz R X α β, hα, cup_zero_left' R X, eqRec_zero R X, zero_add]

section Naturality

variable {R : Type} [CommRing R]

lemma cyclesMap_cocycleOfK_R (K L : CochainComplex (ModuleCat R) ℕ)
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

lemma homologyMap_restr_cohomologyClassOf_R (X : TopCat) (A : Set X) {n : ℕ}
    (α : Cochain R (TopCat.toSSet.obj X) n) (hα : cochainDiff R (TopCat.toSSet.obj X) α = 0)
    (h : cochainDiff R (TopCat.toSSet.obj (TopCat.of A)) (((restr R X A).f n).hom α) = 0) :
    (HomologicalComplex.homologyMap (restr R X A) n)
        (cohomologyClassOf R (TopCat.toSSet.obj X) α hα)
      = cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of A))
          (((restr R X A).f n).hom α) h := by
  have hα' : (ModuleCat.Hom.hom ((singularCochainComplex R X).d n (n+1))) α = 0 := by
    rw [singularCochain_d_apply R X]; exact hα
  have h' : (ModuleCat.Hom.hom ((singularCochainComplex R (TopCat.of A)).d n (n+1)))
      (((restr R X A).f n).hom α) = 0 := by
    rw [singularCochain_d_apply R (TopCat.of A)]; exact h
  change (HomologicalComplex.homologyMap (restr R X A) n)
      (((singularCochainComplex R X).homologyπ n).hom
        (cocycleOfK (singularCochainComplex R X) α hα'))
    = ((singularCochainComplex R (TopCat.of A)).homologyπ n).hom
        (cocycleOfK (singularCochainComplex R (TopCat.of A))
          (((restr R X A).f n).hom α) h')
  have hnat := congrArg (fun (g : (singularCochainComplex R X).cycles n ⟶
        (singularCochainComplex R (TopCat.of A)).homology n) => g.hom
      (cocycleOfK (singularCochainComplex R X) α hα'))
    (HomologicalComplex.homologyπ_naturality (restr R X A) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat, cyclesMap_cocycleOfK_R]

end Naturality

/-! ## The connecting map on the class of a cocycle -/

theorem pairδ_cohomologyClassOf_lift_R (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ)
    (b : Cochain R (TopCat.toSSet.obj (TopCat.of A)) n)
    (hb : cochainDiff R (TopCat.toSSet.obj (TopCat.of A)) b = 0)
    (bt : Cochain R (TopCat.toSSet.obj X) n)
    (hbt : ((restr R X A).f n).hom bt = b) :
    ∃ (hmem : ((singularCochainComplex R X).d n (n + 1)).hom bt ∈ relKern R X A (n + 1)),
      ∃ (hcoc : relDiffLM R X A (n + 1)
          ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ = 0),
        pairδ R X A n (cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of A)) b hb)
          = relClassOf R X A
              ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ hcoc := by
  have hmem : ((singularCochainComplex R X).d n (n + 1)).hom bt ∈ relKern R X A (n + 1) := by
    rw [relKern, LinearMap.mem_ker]
    have h := congrArg ModuleCat.Hom.hom ((restr R X A).comm n (n + 1))
    simp only [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h bt
    simp only [LinearMap.comp_apply] at h2
    rw [singularCochain_d_apply R (TopCat.of A), hbt, hb] at h2
    exact h2.symm
  have hcoc : relDiffLM R X A (n + 1)
      ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero]
    have h := HomologicalComplex.d_comp_d (singularCochainComplex R X) n (n+1) (n+2)
    have h2 := congrArg ModuleCat.Hom.hom h
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    exact LinearMap.congr_fun h2 bt
  refine ⟨hmem, hcoc, ?_⟩
  have hx₃ : (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₃).X n) b))
      ≫ ((pairShort R X A).X₃.d n (n+1)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    change r • ((singularCochainComplex R (TopCat.of A)).d n (n + 1)).hom b = 0
    rw [singularCochain_d_apply R (TopCat.of A), hb, smul_zero]
  have hx₂ : (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₂).X n) bt))
      ≫ ((pairShort R X A).g.f n)
      = (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₃).X n) b)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul]
    change r • ((restr R X A).f n).hom bt = r • b
    rw [hbt]
  have hx₁ : (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₁).X (n+1))
        ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩))
      ≫ ((pairShort R X A).f.f (n+1))
      = (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₂).X n) bt))
        ≫ ((pairShort R X A).X₂.d n (n+1)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul]
    change r • (⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ :
        relKern R X A (n+1)) = r • ((singularCochainComplex R X).d n (n+1)).hom bt
    simp
  have hb' : (ModuleCat.Hom.hom (((pairShort R X A).X₃).d n (n + 1))) b = 0 := by
    change (ModuleCat.Hom.hom ((singularCochainComplex R (TopCat.of A)).d n (n + 1))) b = 0
    rw [singularCochain_d_apply R (TopCat.of A)]; exact hb
  have hcoc' : (ModuleCat.Hom.hom (((pairShort R X A).X₁).d (n + 1) (n + 2)))
      ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ = 0 := by
    change (ModuleCat.Hom.hom ((relComplex R X A).d (n + 1) (n + 2)))
      ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ = 0
    rw [relComplex_d_apply]; exact hcoc
  have hpk : (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₁).X (n+1))
        ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩))
      ≫ ((pairShort R X A).X₁.d (n+1) (n+2)) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, map_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hcoc', smul_zero]
  have key : ∀ (hij : (ComplexShape.up ℕ).Rel n (n+1)),
      (pairShort_shortExact R X A).δ n (n+1) hij
        (cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of A)) b hb)
      = relClassOf R X A ⟨((singularCochainComplex R X).d n (n+1)).hom bt, hmem⟩ hcoc := by
    intro hij
    have hδ := CategoryTheory.ShortComplex.ShortExact.δ_eq (hS := pairShort_shortExact R X A)
      n (n+1) hij
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₃).X n) b)) hx₃
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₂).X n) bt)) hx₂
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₁).X (n+1))
        ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩)) hx₁
      (n+2) (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl))
    have hδ' := congrArg (fun (g : ModuleCat.of R R ⟶
        (((pairShort R X A).X₁).homology (n+1))) => g.hom 1) hδ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hδ'
    have h₃ : (((pairShort R X A).X₃.liftCycles
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₃).X n) b)) (n+1)
          ((ComplexShape.up ℕ).next_eq' hij) hx₃).hom 1)
        = cocycleOfK ((pairShort R X A).X₃) b hb' :=
      liftCycles_ofHom_hom_one_R R ((pairShort R X A).X₃) b (n+1)
        ((ComplexShape.up ℕ).next_eq' hij) rfl hx₃ hb'
    have h₁ : (((pairShort R X A).X₁.liftCycles
          (ModuleCat.ofHom (LinearMap.toSpanSingleton R (((pairShort R X A).X₁).X (n+1))
            ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩)) (n+2)
          (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl)) hpk).hom 1)
        = cocycleOfK ((pairShort R X A).X₁)
            ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ hcoc' :=
      liftCycles_ofHom_hom_one_R R ((pairShort R X A).X₁)
        ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ (n+2)
        (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (n+1) (n+2) from rfl)) rfl hpk hcoc'
    rw [h₃, h₁] at hδ'
    change (ModuleCat.Hom.hom ((pairShort_shortExact R X A).δ n (n + 1) hij))
        ((ModuleCat.Hom.hom ((singularCochainComplex R (TopCat.of A)).homologyπ n))
          (cocycleOfK (singularCochainComplex R (TopCat.of A)) b hb')) =
        (ModuleCat.Hom.hom ((relComplex R X A).homologyπ (n + 1)))
          (cocycleOfK (relComplex R X A)
            ⟨((singularCochainComplex R X).d n (n + 1)).hom bt, hmem⟩ hcoc')
    exact hδ'
  exact key _

/-! ## The main theorem -/

theorem pairDelta_mixedCup_general_R (R : Type) [CommRing R] (X : TopCat) (A : Set X) (m n : ℕ)
    (x : Work.Cohomology.singularCohomology R m X)
    (y : (Work.Cohomology.singularCochainComplex R (TopCat.of A)).homology n) :
    Work.Cohomology.pairδ R X A (m + n)
        (Work.Cohomology.cupH' R (TopCat.toSSet.obj (TopCat.of A)) m n
          ((HomologicalComplex.homologyMap (Work.Cohomology.restr R X A) m).hom x) y)
      = ((-1 : R) ^ m) • (Work.Cohomology.mixedCupR R X A m (n + 1) x
          (Work.Cohomology.pairδ R X A n y)) := by
  obtain ⟨α, hα, hx⟩ := exists_cohomologyClassOf R (TopCat.toSSet.obj X) m x
  obtain ⟨b, hb, hβ⟩ := exists_cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of A)) n y
  obtain ⟨bt, hbt⟩ := surjective_restr R X A n b
  have hrestrα : cochainDiff R (TopCat.toSSet.obj (TopCat.of A))
      (((restr R X A).f m).hom α) = 0 := by
    have h := congrArg ModuleCat.Hom.hom ((restr R X A).comm m (m+1))
    simp only [ModuleCat.hom_comp] at h
    have h2 := LinearMap.congr_fun h α
    simp only [LinearMap.comp_apply] at h2
    rw [singularCochain_d_apply R (TopCat.of A), singularCochain_d_apply R X, hα,
      map_zero] at h2
    exact h2
  have hbc : cochainDiff R (TopCat.toSSet.obj (TopCat.of A))
      (cup R (TopCat.toSSet.obj (TopCat.of A)) (((restr R X A).f m).hom α) b) = 0 :=
    cochainDiff_cup_of_cocycles R (TopCat.toSSet.obj (TopCat.of A)) _ _ hrestrα hb
  have hbtcup : ((restr R X A).f (m+n)).hom (cup R (TopCat.toSSet.obj X) α bt)
      = cup R (TopCat.toSSet.obj (TopCat.of A)) (((restr R X A).f m).hom α) b := by
    have h := (cupNatural R (TopCat.toSSet.map (subtypeIncl X A)) α bt).symm
    rw [show (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of R R)).f n).hom.dualMap) bt = b from hbt] at h
    exact h
  obtain ⟨hmem7, hcoc7, hδ7⟩ := pairδ_cohomologyClassOf_lift_R R X A (m+n)
    (cup R (TopCat.toSSet.obj (TopCat.of A)) (((restr R X A).f m).hom α) b) hbc
    (cup R (TopCat.toSSet.obj X) α bt) hbtcup
  obtain ⟨hmem4, hcoc4, hδ3⟩ := pairδ_cohomologyClassOf_lift_R R X A n b hb bt hbt
  obtain ⟨hmemM, hM, hMmix⟩ := mixedCupR_apply R X A m (n+1) α
    ⟨(ModuleCat.Hom.hom ((singularCochainComplex R X).d n (n+1))) bt, hmem4⟩ hα hcoc4
  have hleib : (ModuleCat.Hom.hom ((singularCochainComplex R X).d (m+n) (m+n+1)))
      (cup R (TopCat.toSSet.obj X) α bt)
      = ((-1 : R) ^ m) • cup R (TopCat.toSSet.obj X) α
          ((ModuleCat.Hom.hom ((singularCochainComplex R X).d n (n+1))) bt) := by
    rw [singularCochain_d_apply R X,
        cochainDiff_cup_left_R R (TopCat.toSSet.obj X) α hα bt,
        ← singularCochain_d_apply R X bt]
  have hL : pairδ R X A (m+n)
        (cupH' R (TopCat.toSSet.obj (TopCat.of A)) m n
          ((HomologicalComplex.homologyMap (restr R X A) m) x) y)
      = ((-1 : R) ^ m) • relClassOf R X A
          ⟨cup R (TopCat.toSSet.obj X) α
            ((ModuleCat.Hom.hom ((singularCochainComplex R X).d n (n+1))) bt), hmemM⟩ hM := by
    rw [← hx, ← hβ, homologyMap_restr_cohomologyClassOf_R X A α hα hrestrα,
        cupH'_apply' R (TopCat.toSSet.obj (TopCat.of A)) (((restr R X A).f m).hom α) b
          hrestrα hb, hδ7]
    have ha : (⟨(ModuleCat.Hom.hom ((singularCochainComplex R X).d (m+n) (m+n+1)))
          (cup R (TopCat.toSSet.obj X) α bt), hmem7⟩ : relKern R X A (m+n+1))
        = ⟨((-1 : R) ^ m) • cup R (TopCat.toSSet.obj X) α
            ((ModuleCat.Hom.hom ((singularCochainComplex R X).d n (n+1))) bt),
            hleib ▸ hmem7⟩ :=
      Subtype.ext hleib
    refine (relClassOf_congr_R R X A ha hcoc7 (ha ▸ hcoc7)).trans ?_
    exact relClassOf_smul_coe_R R X A (m+(n+1)) ((-1 : R) ^ m)
      ⟨_, hmemM⟩ (hleib ▸ hmem7) (ha ▸ hcoc7) hM
  have hR : ((-1 : R) ^ m) • (mixedCupR R X A m (n+1) x (pairδ R X A n y))
      = ((-1 : R) ^ m) • relClassOf R X A
          ⟨cup R (TopCat.toSSet.obj X) α
            ((ModuleCat.Hom.hom ((singularCochainComplex R X).d n (n+1))) bt), hmemM⟩ hM := by
    rw [← hx, ← hβ, hδ3, hMmix]
  rw [hL, hR]

end

end Work.StemsB
