import Mathlib
import Submission.Work.Whitney.TripleRel
import Submission.Work.Whitney.relABZ
import Submission.Work.Cohomology.isIso_homologyMap_tau1
import Submission.Work.Cohomology.rcResLM_surjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-!
# The three-fold small-cochains quasi-isomorphism

For open `A, B, C ⊆ X` the inclusion `pd3InclRelR : C^*(X, A∪B∪C) ⟶ C^*(X,A+B+C)` is a
quasi-isomorphism (the three-fold analogue of `pdABInclRelR_quasiIso`).
-/

/-- The trace of `A` inside the subspace `C`. -/
abbrev traceC (X : TopCat) (A C : Set X) : Set (TopCat.of C) := relSubset A C

/-- The union of the two traces `C ∩ A ∪ C ∩ B` inside the subspace `C`. -/
abbrev traceU (X : TopCat) (A B C : Set X) : Set (TopCat.of C) := traceC X A C ∪ traceC X B C

/-- The union of the traces is contained in the trace of the union. -/
lemma traceU_subset_traceC_union (X : TopCat) (A B C : Set X) :
    traceU X A B C ⊆ traceC X (A ∪ B) C := by
  intro x hx
  rw [Set.mem_union] at hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

/-- The trace of the union is contained in the union of the traces. -/
lemma traceC_union_subset_traceU (X : TopCat) (A B C : Set X) :
    traceC X (A ∪ B) C ⊆ traceU X A B C := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

theorem traceC_union (X : TopCat) (A B C : Set X) :
    traceC X (A ∪ B) C = traceC X A C ∪ traceC X B C := by
  ext x
  show ((x : X) ∈ A ∪ B) ↔ ((x : X) ∈ A ∨ (x : X) ∈ B)
  rw [Set.mem_union]

theorem isOpen_traceC (X : TopCat) {A C : Set X} (hA : IsOpen A) : IsOpen (traceC X A C) := by
  rw [traceC, relSubset]
  exact hA.preimage continuous_subtype_val

/-! ## Membership criteria for relative cochains -/

/-- A cochain vanishing on all chains lying in `A` is a relative cochain for `A`. -/
lemma mem_relKern_of_vanishes (X : TopCat) {A : Set X} {n : ℕ}
    (α : (singularChains ℤ X).X n →ₗ[ℤ] ℤ)
    (h : ∀ c, c ∈ LinearMap.range ((inclChains X A).f n).hom → α c = 0) :
    α ∈ relKern ℤ X A n := by
  rw [relKern, LinearMap.mem_ker]
  rw [restr, dualChainMap_f_hom, chainMap_f_eq]
  apply LinearMap.ext
  intro c
  simp only [LinearMap.dualMap_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  exact h _ ⟨c, rfl⟩

/-- Restriction of a relative cochain for `A` to the subspace `C`, at the cochain-map level:
`restr X C ≫ restr C (C∩A)` is `restr X A` followed by the pullback along `C∩A ⊆ A`. -/
lemma restr_comp_restr (X : TopCat) (A C : Set X) :
    restr ℤ X C ≫ restr ℤ (TopCat.of C) (traceC X A C)
      = restr ℤ X A ≫ dualChainMap ℤ (TopCat.of (traceC X A C)) (TopCat.of A)
          (overlapIncl A C) := by
  rw [restr, restr, restr, ← dualChainMap_comp, ← dualChainMap_comp,
    ← overlapIncl_comp_subtypeIncl (X := X) A C]

/-- The restriction of a relative cochain for `A` to the subspace `C` is a relative cochain for the
trace of `A` in `C`. -/
lemma restr_relKern_mem (X : TopCat) (A C : Set X) (n : ℕ) (φ : relKern ℤ X A n) :
    ((restr ℤ X C).f n).hom φ.1 ∈ relKern ℤ (TopCat.of C) (traceC X A C) n := by
  rw [relKern, LinearMap.mem_ker]
  have h := congrArg (fun (g : singularCochainComplex ℤ X ⟶
      singularCochainComplex ℤ (TopCat.of (traceC X A C))) => (g.f n).hom φ.1)
    (restr_comp_restr X A C)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  have hφ : ((restr ℤ X A).f n).hom φ.1 = 0 := φ.2
  rw [hφ, map_zero]

/-- The restriction of a relative cochain for `A ∪ B` to the subspace `C` is a relative cochain for
the trace of `A ∪ B` in `C`. -/
lemma restr_relKern_mem_trace (X : TopCat) (A B C : Set X) (n : ℕ)
    (φ : relKern ℤ X (A ∪ B) n) :
    ((restr ℤ X C).f n).hom φ.1 ∈ relKern ℤ (TopCat.of C) (traceC X (A ∪ B) C) n := by
  rw [relKern, LinearMap.mem_ker]
  have h := congrArg (fun (g : singularCochainComplex ℤ X ⟶
      singularCochainComplex ℤ (TopCat.of (traceC X (A ∪ B) C))) => (g.f n).hom φ.1)
    (restr_comp_restr X (A ∪ B) C)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  have hφ : ((restr ℤ X (A ∪ B)).f n).hom φ.1 = 0 := φ.2
  rw [hφ, map_zero]

/-- The restriction of a relative cochain for `A ∪ B` to the subspace `C` is a relative cochain for
`C∩A ∪ C∩B`. -/
lemma restr_relKern_mem_union (X : TopCat) (A B C : Set X) (n : ℕ)
    (φ : relKern ℤ X (A ∪ B) n) :
    ((restr ℤ X C).f n).hom φ.1 ∈ relKern ℤ (TopCat.of C) (traceU X A B C) n :=
  relKern_mono (X := TopCat.of C) (traceU_subset_traceC_union X A B C)
    (restr_relKern_mem_trace X A B C n φ)

/-! ## The comparison maps -/

/-- The projection of the `A+B+C` complex onto the `A+B` complex. -/
def pd3ToPdAB (X : TopCat) (A B C : Set X) : pd3CohR X A B C ⟶ pdABCohR (R := ℤ) X A B :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (inf_le_left : pd3KernR X A B C n ≤ pdABKernR (R := ℤ) X A B n)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        pd3CohR_d, pdABCohR_d]
      rfl)

lemma pd3ToPdAB_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (pd3CohR X A B C).X n) : ((pd3ToPdAB X A B C).f n x).1 = x.1 := rfl

/-- The projection of the `(A∪B)+C` complex onto the relative complex of `A ∪ B`. -/
def pdABTraceToRel (X : TopCat) (A B C : Set X) :
    pdABCohR (R := ℤ) X (A ∪ B) C ⟶ relComplex ℤ X (A ∪ B) :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (inf_le_left : pdABKernR (R := ℤ) X (A ∪ B) C n ≤ relKern ℤ X (A ∪ B) n)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        pdABCohR_d, relComplex_d]
      rfl)

lemma pdABTraceToRel_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (pdABCohR (R := ℤ) X (A ∪ B) C).X n) :
    ((pdABTraceToRel X A B C).f n x).1 = x.1 := rfl

lemma pdABTraceToRel_injective (X : TopCat) (A B C : Set X) (n : ℕ) :
    Function.Injective ((pdABTraceToRel X A B C).f n).hom := by
  intro x y h
  have h' := congrArg Subtype.val h
  refine Subtype.ext ?_
  simpa only [pdABTraceToRel_coe] using h'

lemma pd3ToPdAB_injective (X : TopCat) (A B C : Set X) (n : ℕ) :
    Function.Injective ((pd3ToPdAB X A B C).f n).hom := by
  intro x y h
  have h' := congrArg Subtype.val h
  refine Subtype.ext ?_
  simpa only [pd3ToPdAB_coe] using h'

/-- The underlying linear map of the restriction of the relative complex of `A ∪ B` to `C`. -/
def pdABTraceRestrictLM (X : TopCat) (A B C : Set X) (n : ℕ) :
    (relComplex ℤ X (A ∪ B)).X n →ₗ[ℤ]
      (relComplex ℤ (TopCat.of C) (traceU X A B C)).X n :=
  LinearMap.codRestrict
    (relKern ℤ (TopCat.of C) (traceU X A B C) n)
    (((restr ℤ X C).f n).hom.comp (Submodule.subtype (relKern ℤ X (A ∪ B) n)))
    (fun x => restr_relKern_mem_union X A B C n ⟨x.1, x.2⟩)

lemma pdABTraceRestrictLM_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (relComplex ℤ X (A ∪ B)).X n) :
    (pdABTraceRestrictLM X A B C n x).1 = ((restr ℤ X C).f n).hom x.1 :=
  LinearMap.codRestrict_apply _ _ _

/-- Surjectivity of the restriction of the relative complex of `A ∪ B` to the subspace `C`,
in value form. -/
lemma pdABTraceRestrictLM_surj (X : TopCat) (A B C : Set X) (n : ℕ)
    (ψ : (relComplex ℤ (TopCat.of C) (traceU X A B C)).X n) :
    ∃ φ : (relComplex ℤ X (A ∪ B)).X n,
      (pdABTraceRestrictLM X A B C n φ).1 = (ψ.1 : (singularCochainComplex ℤ (TopCat.of C)).X n) := by
  refine ⟨⟨(ψ.1).comp ((chainRetract ℤ X C n).hom), ?_⟩, ?_⟩
  · apply mem_relKern_of_vanishes (X := X) (A := A ∪ B) (n := n)
    intro c hc
    obtain ⟨y, rfl⟩ := hc
    rw [LinearMap.comp_apply]
    have h1 := chainRetract_comp_inclChains_mem_range (X := X) (A ∪ B) C n y
    have h2 := mem_range_inclChains_of_subset (traceC_union_subset_traceU X A B C) h1
    have hker : LinearMap.range ((inclChains (TopCat.of C) (traceU X A B C)).f n).hom ≤
        LinearMap.ker ψ.1 := by
      rintro _ ⟨z, rfl⟩
      exact relKern_apply_inclChains (traceU X A B C) ψ.1 ψ.2 z
    exact hker h2
  · rw [pdABTraceRestrictLM_coe, restr_f_apply]
    have h := congrArg ModuleCat.Hom.hom (chainRetract_spec ℤ X C n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id, ← chainMap_f_eq] at h
    rw [LinearMap.comp_assoc, h, LinearMap.comp_id]

/-- Surjectivity of the restriction of the relative complex of `A ∪ B` to the subspace `C`. -/
lemma pdABTraceRestrictLM_surjective (X : TopCat) (A B C : Set X) (n : ℕ) :
    Function.Surjective (pdABTraceRestrictLM X A B C n) := by
  intro ψ
  obtain ⟨φ, hφ⟩ := pdABTraceRestrictLM_surj X A B C n ψ
  exact ⟨φ, Subtype.ext hφ⟩

/-- The restriction of the relative complex of `A ∪ B` to the subspace `C`, as a cochain map. -/
def pdABTraceRestrict (X : TopCat) (A B C : Set X) :
    relComplex ℤ X (A ∪ B) ⟶ relComplex ℤ (TopCat.of C) (traceU X A B C) :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (pdABTraceRestrictLM X A B C n)) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, relComplex_d,
      relDiff, relDiffLM, relDiffLM_coe, pdABTraceRestrictLM_coe]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((restr ℤ X C).comm n (n+1))) x.1)

lemma pdABTraceRestrict_f (X : TopCat) (A B C : Set X) (n : ℕ) :
    (pdABTraceRestrict X A B C).f n = ModuleCat.ofHom (pdABTraceRestrictLM X A B C n) := rfl

lemma pdABTraceRestrict_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (relComplex ℤ X (A ∪ B)).X n) :
    ((pdABTraceRestrict X A B C).f n x).1 = ((restr ℤ X C).f n).hom x.1 := by
  rw [pdABTraceRestrict_f]
  exact pdABTraceRestrictLM_coe X A B C n x

/-- The underlying linear map of the restriction of the `A+B` complex to the subspace `C`. -/
def pdABRestrictLM (X : TopCat) (A B C : Set X) (n : ℕ) :
    (pdABCohR (R := ℤ) X A B).X n →ₗ[ℤ]
      (pdABCohR (R := ℤ) (TopCat.of C) (traceC X A C) (traceC X B C)).X n :=
  LinearMap.codRestrict
    (pdABKernR (R := ℤ) (TopCat.of C) (traceC X A C) (traceC X B C) n)
    (((restr ℤ X C).f n).hom.comp (Submodule.subtype (pdABKernR (R := ℤ) X A B n)))
    (fun x => Submodule.mem_inf.mpr
      ⟨restr_relKern_mem X A C n ⟨x.1, (Submodule.mem_inf.mp x.2).1⟩,
       restr_relKern_mem X B C n ⟨x.1, (Submodule.mem_inf.mp x.2).2⟩⟩)

lemma pdABRestrictLM_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (pdABCohR (R := ℤ) X A B).X n) :
    (pdABRestrictLM X A B C n x).1 = ((restr ℤ X C).f n).hom x.1 :=
  LinearMap.codRestrict_apply _ _ _

/-- Surjectivity of the restriction of the `A+B` complex to the subspace `C`, in value form. -/
lemma pdABRestrictLM_surj (X : TopCat) (A B C : Set X) (n : ℕ)
    (ψ : (pdABCohR (R := ℤ) (TopCat.of C) (traceC X A C) (traceC X B C)).X n) :
    ∃ φ : (pdABCohR (R := ℤ) X A B).X n,
      (pdABRestrictLM X A B C n φ).1 =
        (ψ.1 : (singularCochainComplex ℤ (TopCat.of C)).X n) := by
  refine ⟨⟨(ψ.1).comp ((chainRetract ℤ X C n).hom), ?_⟩, ?_⟩
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · apply mem_relKern_of_vanishes (X := X) (A := A) (n := n)
      intro c hc
      obtain ⟨y, rfl⟩ := hc
      rw [LinearMap.comp_apply]
      have h1 := chainRetract_comp_inclChains_mem_range (X := X) A C n y
      have hker : LinearMap.range ((inclChains (TopCat.of C) (traceC X A C)).f n).hom ≤
          LinearMap.ker ψ.1 := by
        rintro _ ⟨z, rfl⟩
        exact relKern_apply_inclChains (traceC X A C) ψ.1 (Submodule.mem_inf.mp ψ.2).1 z
      exact hker h1
    · apply mem_relKern_of_vanishes (X := X) (A := B) (n := n)
      intro c hc
      obtain ⟨y, rfl⟩ := hc
      rw [LinearMap.comp_apply]
      have h1 := chainRetract_comp_inclChains_mem_range (X := X) B C n y
      have hker : LinearMap.range ((inclChains (TopCat.of C) (traceC X B C)).f n).hom ≤
          LinearMap.ker ψ.1 := by
        rintro _ ⟨z, rfl⟩
        exact relKern_apply_inclChains (traceC X B C) ψ.1 (Submodule.mem_inf.mp ψ.2).2 z
      exact hker h1
  · rw [pdABRestrictLM_coe, restr_f_apply]
    have h := congrArg ModuleCat.Hom.hom (chainRetract_spec ℤ X C n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id, ← chainMap_f_eq] at h
    rw [LinearMap.comp_assoc, h, LinearMap.comp_id]

/-- Surjectivity of the restriction of the `A+B` complex to the subspace `C`. -/
lemma pdABRestrictLM_surjective (X : TopCat) (A B C : Set X) (n : ℕ) :
    Function.Surjective (pdABRestrictLM X A B C n) := by
  intro ψ
  obtain ⟨φ, hφ⟩ := pdABRestrictLM_surj X A B C n ψ
  exact ⟨φ, Subtype.ext hφ⟩

/-- The restriction of the `A+B` complex to the subspace `C`, as a cochain map. -/
def pdABRestrict (X : TopCat) (A B C : Set X) :
    pdABCohR (R := ℤ) X A B
      ⟶ pdABCohR (R := ℤ) (TopCat.of C) (traceC X A C) (traceC X B C) :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (pdABRestrictLM X A B C n)) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, pdABCohR_d,
      pdABDiffR, pdABDiffLMR, pdABDiffLMR_coe, pdABRestrictLM_coe]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((restr ℤ X C).comm n (n+1))) x.1)

lemma pdABRestrict_f (X : TopCat) (A B C : Set X) (n : ℕ) :
    (pdABRestrict X A B C).f n = ModuleCat.ofHom (pdABRestrictLM X A B C n) := rfl

lemma pdABRestrict_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : (pdABCohR (R := ℤ) X A B).X n) :
    ((pdABRestrict X A B C).f n x).1 = ((restr ℤ X C).f n).hom x.1 := by
  rw [pdABRestrict_f]
  exact pdABRestrictLM_coe X A B C n x

/-! ## The two short exact sequences -/

/-- The first short exact sequence: `0 → C^*(X,(A∪B)+C) → C^*(X,A∪B) → C^*(C, C∩A ∪ C∩B) → 0`. -/
def rowA (X : TopCat) (A B C : Set X) : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (pdABTraceToRel X A B C) (pdABTraceRestrict X A B C)
    (by
      apply HomologicalComplex.hom_ext
      intro n
      rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hc : ((restr ℤ X C).f n).hom x.1 = 0 := (Submodule.mem_inf.mp x.2).2
      exact hc)

/-- The second short exact sequence: `0 → C^*(X,A+B+C) → C^*(X,A+B) → C^*(C, C∩A + C∩B) → 0`. -/
def rowB (X : TopCat) (A B C : Set X) : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (pd3ToPdAB X A B C) (pdABRestrict X A B C)
    (by
      apply HomologicalComplex.hom_ext
      intro n
      rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hc : ((restr ℤ X C).f n).hom x.1 = 0 := (Submodule.mem_inf.mp x.2).2
      exact hc)

/-! ## Exactness -/

lemma rowA_exact (X : TopCat) (A B C : Set X) (n : ℕ) :
    LinearMap.range ((pdABTraceToRel X A B C).f n).hom
      = LinearMap.ker ((pdABTraceRestrict X A B C).f n).hom := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    have hc : ((restr ℤ X C).f n).hom z.1 = 0 := (Submodule.mem_inf.mp z.2).2
    exact hc
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : ((restr ℤ X C).f n).hom y.1 = 0 := by
      have h := congrArg Subtype.val hy
      simpa only [pdABTraceRestrict_coe, Submodule.coe_zero] using h
    refine ⟨⟨y.1, ⟨y.2, hy'⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

lemma rowB_exact (X : TopCat) (A B C : Set X) (n : ℕ) :
    LinearMap.range ((pd3ToPdAB X A B C).f n).hom
      = LinearMap.ker ((pdABRestrict X A B C).f n).hom := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    have hc : ((restr ℤ X C).f n).hom z.1 = 0 := (Submodule.mem_inf.mp z.2).2
    exact hc
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : ((restr ℤ X C).f n).hom y.1 = 0 := by
      have h := congrArg Subtype.val hy
      simpa only [pdABRestrict_coe, Submodule.coe_zero] using h
    refine ⟨⟨y.1, ⟨⟨(Submodule.mem_inf.mp y.2).1, (Submodule.mem_inf.mp y.2).2⟩,
      LinearMap.mem_ker.mpr hy'⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem rowA_shortExact (X : TopCat) (A B C : Set X) : (rowA X A B C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, ShortComplex.map_f, ShortComplex.map_g,
      HomologicalComplex.eval_map, HomologicalComplex.eval_map]
    simp only [rowA]
    exact rowA_exact X A B C n
  · rw [ModuleCat.mono_iff_injective, ShortComplex.map_f, HomologicalComplex.eval_map]
    simp only [rowA]
    exact pdABTraceToRel_injective X A B C n
  · rw [ModuleCat.epi_iff_surjective, ShortComplex.map_g, HomologicalComplex.eval_map]
    simp only [rowA]
    exact pdABTraceRestrictLM_surjective X A B C n

theorem rowB_shortExact (X : TopCat) (A B C : Set X) : (rowB X A B C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, ShortComplex.map_f, ShortComplex.map_g,
      HomologicalComplex.eval_map, HomologicalComplex.eval_map]
    simp only [rowB]
    exact rowB_exact X A B C n
  · rw [ModuleCat.mono_iff_injective, ShortComplex.map_f, HomologicalComplex.eval_map]
    simp only [rowB]
    exact pd3ToPdAB_injective X A B C n
  · rw [ModuleCat.epi_iff_surjective, ShortComplex.map_g, HomologicalComplex.eval_map]
    simp only [rowB]
    exact pdABRestrictLM_surjective X A B C n

/-! ## The morphism of short exact sequences and the five lemma -/

/-- The first square of the comparison. -/
lemma row_sq₁ (X : TopCat) (A B C : Set X) :
    pdABCOhR_to_pd3CohR_left X A B C ≫ (rowB X A B C).f
      = (rowA X A B C).f ≫ pdABInclRelR (R := ℤ) X A B := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The second square of the comparison. -/
lemma row_sq₂ (X : TopCat) (A B C : Set X) :
    pdABInclRelR (R := ℤ) X A B ≫ (rowB X A B C).g
      = (rowA X A B C).g ≫ pdABInclRelR (R := ℤ) (TopCat.of C) (traceC X A C) (traceC X B C) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The comparison morphism of short exact sequences. -/
noncomputable def rowHom (X : TopCat) (A B C : Set X) : rowA X A B C ⟶ rowB X A B C :=
  ShortComplex.homMk (pdABCOhR_to_pd3CohR_left X A B C) (pdABInclRelR (R := ℤ) X A B)
    (pdABInclRelR (R := ℤ) (TopCat.of C) (traceC X A C) (traceC X B C))
    (row_sq₁ X A B C) (row_sq₂ X A B C)

/-- `pd3InclRelR` is the composite of the two-fold inclusion for the cover `(A∪B, C)` with the
comparison map. -/
lemma pd3InclRelR_eq (X : TopCat) (A B C : Set X) :
    pd3InclRelR X A B C
      = pdABInclRelR (R := ℤ) X (A ∪ B) C ≫ pdABCOhR_to_pd3CohR_left X A B C := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

theorem pd3InclRelR_quasiIso (X : TopCat) (A B C : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hC : IsOpen C) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (pd3InclRelR X A B C) n) := by
  have h₂ : ∀ m, IsIso (HomologicalComplex.homologyMap (rowHom X A B C).τ₂ m) :=
    fun m => pdABInclRelR_quasiIso (R := ℤ) (M := X) (A := A) (B := B) hA hB m
  have h₃ : ∀ m, IsIso (HomologicalComplex.homologyMap (rowHom X A B C).τ₃ m) :=
    fun m => pdABInclRelR_quasiIso (R := ℤ) (M := TopCat.of C) (A := traceC X A C)
      (B := traceC X B C) (isOpen_traceC X hA) (isOpen_traceC X hB) m
  have h₁ : IsIso (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_left X A B C) n) :=
    isIso_homologyMap_tau1 ℤ (rowHom X A B C) (rowA_shortExact X A B C)
      (rowB_shortExact X A B C) h₂ h₃ n
  haveI : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := ℤ) X (A ∪ B) C) n) :=
    pdABInclRelR_quasiIso (R := ℤ) (M := X) (A := A ∪ B) (B := C) (hA.union hB) hC n
  haveI : IsIso (HomologicalComplex.homologyMap (pdABCOhR_to_pd3CohR_left X A B C) n) := h₁
  rw [pd3InclRelR_eq X A B C, HomologicalComplex.homologyMap_comp]
  infer_instance
