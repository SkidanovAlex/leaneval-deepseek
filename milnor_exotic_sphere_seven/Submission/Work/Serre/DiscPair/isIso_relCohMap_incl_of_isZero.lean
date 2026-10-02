
import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.DiscPair.tripleInclIso
import Submission.Work.Cohomology.Endgame.tripleLES

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The triple long exact sequence, and the isomorphism `H^k(X,A) ≅ H^k(B,A∩B)`

For subsets `A ⊆ B ⊆ X` of a topological space, the relative cochain complexes fit into the short
exact sequence of the triple

`0 ⟶ C^*(X,B) ⟶ C^*(X,A) ⟶ C^*(B, A∩B) ⟶ 0`

(the first map the inclusion of the smaller relative complex, the second the pullback along the
inclusion `B ⊆ X`).  Passing to cohomology gives the long exact sequence of the triple,

`H^k(X,B) → H^k(X,A) → H^k(B,A∩B) → H^{k+1}(X,B) → …`,

whose exactness at `H^k(X,A)` and at `H^k(B,A∩B)` shows that the restriction map
`H^k(X,A) → H^k(B,A∩B)` is an isomorphism as soon as the relative groups of the pair `(X,B)`
vanish in degrees `k` and `k+1` — both injectivity and surjectivity are of the form "an exact map
next to a zero map is a mono/epi".

This is the "shrinking the second member of a pair" step used in the cell-by-cell construction of
relative Thom classes (the same statement that `Work.Serre.isIso_triple_f_of_isZero` provides for
the homology of the rational relative *chains*, here for the relative *cochains* and with the
middle map rather than the first one).

The coefficients here are `ℚ` (`RelCoh ℚ`), so the triple sequence is established over `ℚ`; the
development is the exact analogue over `ℚ` of `Work.Cohomology.Endgame.tripleLES` (which is over
`ℤ`) and reuses its ring-independent auxiliary lemmas (`A₁'`, `subIncl`, `kappa`, `kappa_spec`,
`subIncl_spec`, `chainMap_comp`, `ker_dualMap_le_ker_dualMap_comp`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

/-! ## The triple short exact sequence over `ℚ` -/

/-- The inclusion `A ⊆ B` factors through the identification `A → A ∩ B`, hence the chain map it
induces factors accordingly (the input of `qKey_aux`). -/
lemma qChainMap_subIncl_eq (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B)
        (Work.Cohomology.Endgame.subIncl X A B h)
      = Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of (Work.Cohomology.Endgame.A₁' X A B))
          (Work.Cohomology.Endgame.kappa X A B h)
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of (Work.Cohomology.Endgame.A₁' X A B)) (TopCat.of B)
            (Work.Cohomology.subtypeIncl (TopCat.of B) (Work.Cohomology.Endgame.A₁' X A B)) := by
  rw [← Work.Cohomology.Endgame.chainMap_comp, Work.Cohomology.Endgame.kappa_spec]

/-- A cochain on `B` vanishing on `A ∩ B` restricts to zero on `A`. -/
lemma qKey_aux (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ)
    (β : ↑((Work.Cohomology.singularCochainComplex ℚ (TopCat.of B)).X n))
    (hβ : β ∈ Work.Cohomology.relKern ℚ (TopCat.of B) (Work.Cohomology.Endgame.A₁' X A B) n) :
    ((Work.Cohomology.dualChainMap ℚ (TopCat.of A) (TopCat.of B)
      (Work.Cohomology.Endgame.subIncl X A B h)).f n).hom β = 0 := by
  have h1 : ((Work.Cohomology.chainMap ℚ (TopCat.of (Work.Cohomology.Endgame.A₁' X A B)) (TopCat.of B)
      (Work.Cohomology.subtypeIncl (TopCat.of B) (Work.Cohomology.Endgame.A₁' X A B))).f n).hom.dualMap β = 0 := by
    rw [Work.Cohomology.relKern, Work.Cohomology.restr, LinearMap.mem_ker] at hβ
    rw [Work.Cohomology.dualChainMap_f_hom] at hβ
    exact hβ
  have hWu : ((Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B)
        (Work.Cohomology.Endgame.subIncl X A B h)).f n).hom
      = ((Work.Cohomology.chainMap ℚ (TopCat.of (Work.Cohomology.Endgame.A₁' X A B)) (TopCat.of B)
            (Work.Cohomology.subtypeIncl (TopCat.of B) (Work.Cohomology.Endgame.A₁' X A B))).f n).hom.comp
        ((Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of (Work.Cohomology.Endgame.A₁' X A B))
            (Work.Cohomology.Endgame.kappa X A B h)).f n).hom := by
    rw [qChainMap_subIncl_eq, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  have h2 : (((Work.Cohomology.chainMap ℚ (TopCat.of (Work.Cohomology.Endgame.A₁' X A B)) (TopCat.of B)
            (Work.Cohomology.subtypeIncl (TopCat.of B) (Work.Cohomology.Endgame.A₁' X A B))).f n).hom.comp
        ((Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of (Work.Cohomology.Endgame.A₁' X A B))
            (Work.Cohomology.Endgame.kappa X A B h)).f n).hom).dualMap β = 0 :=
    LinearMap.mem_ker.mp (Work.Cohomology.Endgame.ker_dualMap_le_ker_dualMap_comp _ _
      (LinearMap.mem_ker.mpr h1))
  rw [Work.Cohomology.dualChainMap_f_hom, hWu]
  exact h2

/-- The first map of the triple sequence. -/
def qTripleF (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    Work.Cohomology.relComplex ℚ X B ⟶ Work.Cohomology.relComplex ℚ X A :=
  Work.Cohomology.relComplexMap ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h

/-- The second map of the triple sequence. -/
def qTripleG (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    Work.Cohomology.relComplex ℚ X A
      ⟶ Work.Cohomology.relComplex ℚ (TopCat.of B) (Work.Cohomology.Endgame.A₁' X A B) :=
  Work.Cohomology.relComplexMap ℚ (X₁ := TopCat.of B) (X₂ := X) (Work.Cohomology.Endgame.A₁' X A B) A
    (Work.Cohomology.subtypeIncl X B) (fun x hx => hx)

/-- The triple sequence is a complex. -/
lemma qTriple_comp_zero (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    qTripleF X A B h ≫ qTripleG X A B h = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show ((Work.Cohomology.relMapLM ℚ (X₁ := TopCat.of B) (X₂ := X) (Work.Cohomology.Endgame.A₁' X A B) A
        (Work.Cohomology.subtypeIncl X B) (fun x hx => hx) n)
      ((Work.Cohomology.relMapLM ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h n) x)).1 = 0
  simp only [Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  exact x.2

/-- The triple short complex `0 ⟶ C^*(X,B) ⟶ C^*(X,A) ⟶ C^*(B,A∩B) ⟶ 0`. -/
def qTripleShort (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk (qTripleF X A B h) (qTripleG X A B h) (qTriple_comp_zero X A B h)

@[simp] lemma qTripleShort_f (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    (qTripleShort X A B h).f = qTripleF X A B h := rfl

@[simp] lemma qTripleShort_g (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    (qTripleShort X A B h).g = qTripleG X A B h := rfl

@[simp] lemma qTripleF_f (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    (qTripleF X A B h).f n
      = ModuleCat.ofHom (Work.Cohomology.relMapLM ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h n) :=
  Work.Cohomology.relComplexMap_f ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h n

@[simp] lemma qTripleG_f (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    (qTripleG X A B h).f n
      = ModuleCat.ofHom (Work.Cohomology.relMapLM ℚ (X₁ := TopCat.of B) (X₂ := X)
          (Work.Cohomology.Endgame.A₁' X A B) A (Work.Cohomology.subtypeIncl X B) (fun x hx => hx) n) :=
  Work.Cohomology.relComplexMap_f ℚ (X₁ := TopCat.of B) (X₂ := X) (Work.Cohomology.Endgame.A₁' X A B) A
    (Work.Cohomology.subtypeIncl X B) (fun x hx => hx) n

lemma qRelMapLM_id_coe (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ)
    (x : ↥(Work.Cohomology.relKern ℚ X B n)) :
    ((Work.Cohomology.relMapLM ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h n) x).1 = x.1 := by
  rw [Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]

lemma qRelMapLM_id_injective (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    Function.Injective (Work.Cohomology.relMapLM ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h n) := by
  intro a b hab
  have hh := congrArg (fun z => z.1) hab
  rw [qRelMapLM_id_coe, qRelMapLM_id_coe] at hh
  exact Subtype.ext hh

lemma qRelMapLM_g_surjective (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    Function.Surjective (Work.Cohomology.relMapLM ℚ (X₁ := TopCat.of B) (X₂ := X)
      (Work.Cohomology.Endgame.A₁' X A B) A (Work.Cohomology.subtypeIncl X B) (fun x hx => hx) n) := by
  intro β
  obtain ⟨x₁, hx₁⟩ := Work.Cohomology.surjective_restr ℚ X B n β.1
  rw [Work.Cohomology.restr] at hx₁
  have hsq : Work.Cohomology.restr ℚ X A
      = Work.Cohomology.dualChainMap ℚ (TopCat.of B) X (Work.Cohomology.subtypeIncl X B)
        ≫ Work.Cohomology.dualChainMap ℚ (TopCat.of A) (TopCat.of B)
            (Work.Cohomology.Endgame.subIncl X A B h) := by
    rw [Work.Cohomology.restr, ← Work.Cohomology.dualChainMap_comp,
      Work.Cohomology.Endgame.subIncl_spec]
  have hβA : (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of A) (TopCat.of B)
      (Work.Cohomology.Endgame.subIncl X A B h)).f n)) β.1 = 0 := qKey_aux X A B h n β.1 β.2
  have hzero : (ModuleCat.Hom.hom ((Work.Cohomology.restr ℚ X A).f n)) x₁ = 0 := by
    have h2 : (ModuleCat.Hom.hom ((Work.Cohomology.restr ℚ X A).f n)) x₁
        = (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of A) (TopCat.of B)
            (Work.Cohomology.Endgame.subIncl X A B h)).f n))
          ((ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℚ (TopCat.of B) X
            (Work.Cohomology.subtypeIncl X B)).f n)) x₁) := by
      rw [hsq, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [h2, hx₁]
    exact hβA
  exact ⟨⟨x₁, hzero⟩, by
    apply Subtype.ext
    rw [Work.Cohomology.relMapLM_coe]
    exact hx₁⟩

lemma qRelMapLM_range_eq_ker (X : TopCat) (A B : Set X) (h : A ⊆ B) (n : ℕ) :
    LinearMap.range (Work.Cohomology.relMapLM ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h n)
      = LinearMap.ker (Work.Cohomology.relMapLM ℚ (X₁ := TopCat.of B) (X₂ := X)
          (Work.Cohomology.Endgame.A₁' X A B) A (Work.Cohomology.subtypeIncl X B) (fun x hx => hx) n) := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker]
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    apply Subtype.ext
    show ((Work.Cohomology.relMapLM ℚ (X₁ := TopCat.of B) (X₂ := X) (Work.Cohomology.Endgame.A₁' X A B) A
        (Work.Cohomology.subtypeIncl X B) (fun x hx => hx) n)
      ((Work.Cohomology.relMapLM ℚ (X₁ := X) (X₂ := X) A B (𝟙 X) h n) x)).1 = 0
    simp only [Work.Cohomology.relMapLM_coe, Work.Cohomology.dualChainMap_id,
      HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
    exact x.2
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy1 : (ModuleCat.Hom.hom ((Work.Cohomology.restr ℚ X B).f n)) y.1 = 0 := by
      have hcon := congrArg (fun z => z.1) hy
      rw [Work.Cohomology.relMapLM_coe] at hcon
      simpa [Work.Cohomology.restr] using hcon
    refine LinearMap.mem_range.mpr ⟨⟨y.1, ?_⟩, ?_⟩
    · rw [Work.Cohomology.relKern, LinearMap.mem_ker]
      exact hy1
    · apply Subtype.ext
      rw [qRelMapLM_id_coe]

/-- **The short complex of the triple `A ⊆ B ⊆ X` is short exact** (proved degreewise): at each
degree the sequence of `ℚ`-modules
`0 → C^n(X,B) → C^n(X,A) → C^n(B,A∩B) → 0` is short exact. -/
lemma qTripleShort_shortExact (X : TopCat) (A B : Set X) (h : A ⊆ B) :
    (qTripleShort X A B h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, ShortComplex.map_f, ShortComplex.map_g,
      HomologicalComplex.eval_map, HomologicalComplex.eval_map]
    simp only [qTripleShort_f, qTripleShort_g, qTripleF_f, qTripleG_f, ModuleCat.hom_ofHom]
    exact qRelMapLM_range_eq_ker X A B h n
  · rw [ShortComplex.map_f, HomologicalComplex.eval_map, ModuleCat.mono_iff_injective]
    simp only [qTripleShort_f, qTripleF_f, ModuleCat.hom_ofHom]
    exact qRelMapLM_id_injective X A B h n
  · rw [ShortComplex.map_g, HomologicalComplex.eval_map, ModuleCat.epi_iff_surjective]
    simp only [qTripleShort_g, qTripleG_f, ModuleCat.hom_ofHom]
    exact qRelMapLM_g_surjective X A B h n

/-- **The restriction `H^k(X,A) → H^k(B,A∩B)` is an isomorphism** as soon as the relative
cohomology of the larger pair `(X,B)` vanishes in degrees `k` and `k+1`.

This is the exact fragment `H^k(X,B) → H^k(X,A) → H^k(B,A∩B) → H^{k+1}(X,B)` of the long exact
sequence of the triple `A ⊆ B ⊆ X`: the first map is zero (its source is zero), so the second is a
monomorphism, and the third (the connecting map, whose target is zero) is zero, so the second is an
epimorphism. -/
theorem isIso_relCohMap_incl_of_isZero (X : TopCat) (A B : Set X) (hAB : A ⊆ B) (k : ℕ)
    (h₁ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k X B))
    (h₂ : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (k + 1) X B)) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥B, X))
      {x : ↥B | (x : X) ∈ A} A (fun x hx => hx) ℚ k) := by
  have hS : (qTripleShort X A B hAB).ShortExact := qTripleShort_shortExact X A B hAB
  have hrel : (ComplexShape.up ℕ).Rel k (k + 1) := by simp [ComplexShape.up]
  have hmap : HomologicalComplex.homologyMap (qTripleShort X A B hAB).g k
      = Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥B, X))
          {x : ↥B | (x : X) ∈ A} A (fun x hx => hx) ℚ k := by
    show HomologicalComplex.homologyMap (qTripleG X A B hAB) k
      = HomologicalComplex.homologyMap
          (Work.Cohomology.relComplexMap (X₁ := TopCat.of ↥B) (X₂ := TopCat.of X) ℚ
            ((Subtype.val : ↥B → X) ⁻¹' A) A
            (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(↥B, X)))
            (fun x hx => hx)) k
    congr 1
  rw [← hmap]
  have hmono : Mono (HomologicalComplex.homologyMap (qTripleShort X A B hAB).g k) := by
    have hex := hS.homology_exact₂ k
    exact (ShortComplex.exact_iff_mono _ (IsZero.eq_zero_of_src h₁ _)).mp hex
  have hepi : Epi (HomologicalComplex.homologyMap (qTripleShort X A B hAB).g k) := by
    have hex := hS.homology_exact₃ k (k + 1) hrel
    exact (ShortComplex.exact_iff_epi _ (IsZero.eq_zero_of_tgt h₂ _)).mp hex
  exact isIso_of_mono_of_epi _

end
end Work.Serre.DiscPair
