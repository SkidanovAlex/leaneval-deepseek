import Mathlib
import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.surj_cohomology
import Submission.Work.DSM5b.HCF.htcD_exact_above
import Submission.Work.DSM5b.HCF.level_ker_injective
import Submission.Work.DSM5b.HCF.level_ker_surjective

namespace Work.DSM5b.HCF

universe u

open CategoryTheory Work.DSM5b

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]

/-! ## Elementary facts about the graded piece `exactlyCoeff 𝒜 k`

The coefficient system `ℰ = exactlyCoeff 𝒜 k` is supported on the subsets of size exactly `k`:
its coefficient module `ℰ.M S` is a subsingleton (i.e. `0`) whenever `S.card ≠ k`.  Consequently
the honest complex `Htc ℰ` vanishes in degrees `m` that are too small and the sorted complex
`Stc ℰ` vanishes in every degree `m ≠ k - 1`, so that both complexes are concentrated in degree
`k - 1`, where the comparison `toStc` is the bijection `level_ker_injective`/`level_ker_surjective`. -/

/-- The coefficient module of `exactlyCoeff 𝒜 k` at a subset of size `≠ k` is a subsingleton
(so the zero module). -/
lemma subsingleton_exactlyCoeff_M (𝒜 : CoeffSys R ι) (k : ℕ) {S : Finset ι}
    (h : S.card ≠ k) : Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).M S) := by
  by_cases hlt : S.card < k
  · haveI : Subsingleton ↥((CoeffSys.sizeSubSys 𝒜 k).N S) := by
      rw [show (CoeffSys.sizeSubSys 𝒜 k).N S = ⊥ from if_neg (by omega)]
      infer_instance
    exact Function.Surjective.subsingleton (Submodule.mkQ_surjective _)
  · have hNk1 : (CoeffSys.sizeSubSys 𝒜 (k+1)).N S = ⊤ := if_pos (by omega)
    change Subsingleton (↥((CoeffSys.sizeSubSys 𝒜 k).N S) ⧸
      (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 k S)).range)
    rw [Submodule.Quotient.subsingleton_iff]
    apply Submodule.eq_top_iff'.mpr
    intro y
    refine ⟨⟨y.1, by rw [hNk1]; exact Submodule.mem_top⟩, ?_⟩
    exact Subtype.ext rfl

/-- The honest complex of `exactlyCoeff 𝒜 k` vanishes in the degrees below `k - 1`
(and in every degree when `k = 0`, where no finite subset has size `0`). -/
lemma subsingleton_htc (𝒜 : CoeffSys R ι) (k m : ℕ) (hm : m + 1 < k ∨ k = 0) :
    Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).Htc m) := by
  haveI : ∀ τ : Fin (m+1) → ι,
      Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).M (tupRng τ)) := by
    intro τ
    refine subsingleton_exactlyCoeff_M 𝒜 k (S := tupRng τ) ?_
    rcases hm with hlt | hk0
    · have hc : (tupRng τ).card ≤ m + 1 := by
        rw [tupRng]
        simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin (m+1)))) (f := τ))
      omega
    · subst hk0
      have hpos : 0 < (tupRng τ).card :=
        Finset.card_pos.mpr ⟨τ 0, by rw [tupRng]; exact Finset.mem_image_of_mem τ (Finset.mem_univ 0)⟩
      omega
  infer_instance

/-- The sorted complex of `exactlyCoeff 𝒜 k` vanishes in every degree `m ≠ k - 1`: an increasing
tuple of length `m + 1` has range of size `m + 1 ≠ k`. -/
lemma subsingleton_stc (𝒜 : CoeffSys R ι) (k m : ℕ) (hm : m + 1 ≠ k) :
    Subsingleton (Stc (CoeffSys.exactlyCoeff 𝒜 k) m) := by
  haveI : ∀ τ : IncrTuple (ι := ι) m,
      Subsingleton ((CoeffSys.exactlyCoeff 𝒜 k).M (tupRng τ.1)) := by
    intro τ
    refine subsingleton_exactlyCoeff_M 𝒜 k (S := tupRng τ.1) ?_
    have hinj : Function.Injective τ.1 := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (ne_of_lt (τ.2 a b h)) hab
      · exact (ne_of_lt (τ.2 b a h)) hab.symm
    have hc : (tupRng τ.1).card = m + 1 := by
      rw [tupRng, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    omega
  infer_instance

/-- The sorted differential of `exactlyCoeff 𝒜 k` is the zero map (its source or its target is
always a degree different from `k - 1`). -/
lemma stcD_exactlyCoeff_eq_zero (𝒜 : CoeffSys R ι) (k m : ℕ) :
    stcD (CoeffSys.exactlyCoeff 𝒜 k) m = 0 := by
  apply LinearMap.ext
  intro x
  by_cases h : m + 1 = k - 1
  · have h' : m + 1 ≠ k := by omega
    haveI : Subsingleton (Stc (CoeffSys.exactlyCoeff 𝒜 k) m) :=
      subsingleton_stc 𝒜 k m h'
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx]
    exact map_zero _
  · have h' : (m + 1) + 1 ≠ k := by omega
    haveI : Subsingleton (Stc (CoeffSys.exactlyCoeff 𝒜 k) (m + 1)) :=
      subsingleton_stc 𝒜 k (m + 1) h'
    exact Subsingleton.elim _ _

lemma htcX_subsingleton (𝒜 : CoeffSys R ι) (k m : ℕ) (hm : m + 1 < k ∨ k = 0) :
    Subsingleton ((htcComplex (CoeffSys.exactlyCoeff 𝒜 k)).X m) := by
  rw [htcComplex_X]
  exact subsingleton_htc 𝒜 k m hm

lemma stcX_subsingleton (𝒜 : CoeffSys R ι) (k m : ℕ) (hm : m + 1 ≠ k) :
    Subsingleton ((stcComplex (CoeffSys.exactlyCoeff 𝒜 k)).X m) := by
  rw [stcComplex_X]
  exact subsingleton_stc 𝒜 k m hm

/-! ## General homological helpers -/

/-- The `prev` of `ComplexShape.up ℕ`. -/
lemma prev_up_nat (j : ℕ) : (ComplexShape.up ℕ).prev j = j - 1 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    exact ComplexShape.prev_eq_self' _ _ (fun k hk => by simp [ComplexShape.up] at hk)
  · exact ComplexShape.prev_eq' _ (ComplexShape.up_mk (j-1) j (by omega))

/-- The `next` of `ComplexShape.up ℕ`. -/
lemma next_up_nat (j : ℕ) : (ComplexShape.up ℕ).next j = j + 1 := CochainComplex.next ℕ j

/-- A morphism of `R`-modules whose source is a subsingleton is zero. -/
lemma hom_eq_zero_of_subsingleton {X Y : ModuleCat R} (h : Subsingleton X) (f : X ⟶ Y) :
    f = 0 :=
  CategoryTheory.Limits.IsZero.eq_of_src ((ModuleCat.isZero_iff_subsingleton).mpr h) f 0

/-- A short complex of `R`-modules whose middle term is a subsingleton is exact. -/
lemma shortComplex_exact_of_subsingleton (S : ShortComplex (ModuleCat R))
    (h : Subsingleton S.X₂) : S.Exact := by
  haveI := h
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  apply le_antisymm
  · intro x _
    rw [LinearMap.mem_ker, Subsingleton.elim x 0, map_zero]
  · intro x _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _

/-- A morphism of short complexes of `R`-modules between two exact short complexes is a
quasi-isomorphism. -/
lemma shortComplex_quasiIso_of_exact {S₁ S₂ : ShortComplex (ModuleCat R)} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) : ShortComplex.QuasiIso φ := by
  rw [ShortComplex.quasiIso_iff]
  exact CategoryTheory.Limits.IsZero.isIso ((ShortComplex.exact_iff_isZero_homology S₁).mp h₁)
    ((ShortComplex.exact_iff_isZero_homology S₂).mp h₂) _

/-- **A quasi-isomorphism criterion in the top degree.**  If `S₁.f = 0`, `S₂.f = 0` and
`S₂.g = 0`, then a morphism `φ : S₁ ⟶ S₂` of short complexes of `R`-modules is a quasi-isomorphism
iff the induced map from the cycles `ker S₁.g` of `S₁` to `S₂.X₂` is bijective.  This is the
linear-algebra form of the identification of the source homology with the cycles and of the target
homology with `S₂.X₂`. -/
lemma shortComplex_quasiIso_iff_ker_bijective (S₁ S₂ : ShortComplex (ModuleCat R)) (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    ShortComplex.QuasiIso φ ↔
      Function.Bijective (fun z : ↥(LinearMap.ker (S₁.g.hom)) => (φ.τ₂).hom z.1) := by
  let h₁ : S₁.LeftHomologyData :=
    ShortComplex.LeftHomologyData.ofIsLimitKernelFork S₁ hf₁ _ S₁.cyclesIsKernel
  let h₂ : S₂.LeftHomologyData := ShortComplex.LeftHomologyData.ofZeros S₂ hf₂ hg₂
  let γ : ShortComplex.LeftHomologyMapData φ h₁ h₂ :=
    { φK := S₁.iCycles ≫ φ.τ₂
      φH := S₁.iCycles ≫ φ.τ₂ }
  have h2 : S₁.moduleCatCyclesIso.inv ≫ γ.φH =
      S₁.moduleCatLeftHomologyData.i ≫ φ.τ₂ := by
    show S₁.moduleCatCyclesIso.inv ≫ (S₁.iCycles ≫ φ.τ₂) = _
    rw [← Category.assoc, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  have hfun2 : ⇑(S₁.moduleCatLeftHomologyData.i ≫ φ.τ₂).hom =
      (fun z : ↥(LinearMap.ker (S₁.g.hom)) => (φ.τ₂).hom z.1) := by
    funext z
    show (ModuleCat.Hom.hom (S₁.moduleCatLeftHomologyData.i ≫ φ.τ₂)) z = (φ.τ₂).hom z.1
    rw [ModuleCat.hom_comp]
    show (φ.τ₂).hom ((ModuleCat.Hom.hom S₁.moduleCatLeftHomologyData.i) z) = (φ.τ₂).hom z.1
    rw [ShortComplex.moduleCatLeftHomologyData_i_hom]
    rfl
  rw [γ.quasiIso_iff]
  conv_rhs => rw [← hfun2, ← ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro h
    haveI := h
    rw [← h2]
    infer_instance
  · intro h
    haveI := h
    have h' : IsIso (S₁.moduleCatCyclesIso.inv ≫ γ.φH) := by rw [h2]; exact h
    exact IsIso.of_isIso_comp_left S₁.moduleCatCyclesIso.inv γ.φH

/-! ## Exactness of the two complexes away from the top degree -/

/-- Exactness of the honest complex of `exactlyCoeff 𝒜 k` in degree `m + 1` for `m + 1 ≠ k - 1`,
expressed on the short complex `sc' m (m+1) (m+2)` (so that no `prev`/`next` rewriting is needed).
Below the top degree the middle term is a subsingleton, above it the exactness
`Work.DSM5b.HCF.htcD_exact_above` applies. -/
lemma htcSc'_exact_succ (𝒜 : CoeffSys R ι) (k m : ℕ) (hne : (m + 1) ≠ k - 1) :
    ((htcComplex (CoeffSys.exactlyCoeff 𝒜 k)).sc' m (m+1) (m+2)).Exact := by
  by_cases hlt : m + 1 < k
  · exact shortComplex_exact_of_subsingleton _ (htcX_subsingleton 𝒜 k (m+1) (Or.inl (by omega)))
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker,
      HomologicalComplex.shortComplexFunctor'_obj_f,
      HomologicalComplex.shortComplexFunctor'_obj_g,
      htcComplex_d, htcComplex_d, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    exact htcD_exact_above 𝒜 k m (by omega)

/-- Exactness of the sorted complex of `exactlyCoeff 𝒜 k` in degree `m + 1 ≠ k - 1`: every term
there is a subsingleton. -/
lemma stcSc'_exact_succ (𝒜 : CoeffSys R ι) (k m : ℕ) (hne : (m + 1) ≠ k - 1) :
    ((stcComplex (CoeffSys.exactlyCoeff 𝒜 k)).sc' m (m+1) (m+2)).Exact :=
  shortComplex_exact_of_subsingleton _ (stcX_subsingleton 𝒜 k (m+1) (by omega))

/-- Exactness of the honest complex of `exactlyCoeff 𝒜 k` in degree `0` (with `k ≥ 2`, so the
degree is different from the top degree `k - 1`). -/
lemma htcSc'_exact_zero (𝒜 : CoeffSys R ι) (k : ℕ) (hk : 2 ≤ k) :
    ((htcComplex (CoeffSys.exactlyCoeff 𝒜 k)).sc' 0 0 1).Exact :=
  shortComplex_exact_of_subsingleton _ (htcX_subsingleton 𝒜 k 0 (Or.inl (by omega)))

/-- Exactness of the sorted complex of `exactlyCoeff 𝒜 k` in degree `0` (with `k ≥ 2`). -/
lemma stcSc'_exact_zero (𝒜 : CoeffSys R ι) (k : ℕ) (hk : 2 ≤ k) :
    ((stcComplex (CoeffSys.exactlyCoeff 𝒜 k)).sc' 0 0 1).Exact :=
  shortComplex_exact_of_subsingleton _ (stcX_subsingleton 𝒜 k 0 (by omega))

/-! ## The two remaining equations of the top-degree short complex -/

/-- The differential of the honest complex into the top degree from degree `k - 2` is zero. -/
lemma htc_top_f_eq_zero (𝒜 : CoeffSys R ι) (k : ℕ) :
    ((htcComplex (CoeffSys.exactlyCoeff 𝒜 k)).sc' ((k-1)-1) (k-1) ((k-1)+1)).f = 0 := by
  rw [HomologicalComplex.shortComplexFunctor'_obj_f]
  rcases k with _ | _ | k
  · exact HomologicalComplex.shape _ 0 0 (by simp [ComplexShape.up])
  · exact HomologicalComplex.shape _ 0 0 (by simp [ComplexShape.up])
  · exact hom_eq_zero_of_subsingleton
      (htcX_subsingleton 𝒜 (k+2) ((k+2-1)-1) (Or.inl (by omega))) _

/-- The differential of the sorted complex into the top degree from degree `k - 2` is zero. -/
lemma stc_top_f_eq_zero (𝒜 : CoeffSys R ι) (k : ℕ) :
    ((stcComplex (CoeffSys.exactlyCoeff 𝒜 k)).sc' ((k-1)-1) (k-1) ((k-1)+1)).f = 0 := by
  rw [HomologicalComplex.shortComplexFunctor'_obj_f]
  rcases k with _ | _ | k
  · exact HomologicalComplex.shape _ 0 0 (by simp [ComplexShape.up])
  · exact HomologicalComplex.shape _ 0 0 (by simp [ComplexShape.up])
  · exact hom_eq_zero_of_subsingleton
      (stcX_subsingleton 𝒜 (k+2) ((k+2-1)-1) (by omega)) _

/-- The differential of the sorted complex out of the top degree is zero. -/
lemma stc_top_g_eq_zero (𝒜 : CoeffSys R ι) (k : ℕ) :
    ((stcComplex (CoeffSys.exactlyCoeff 𝒜 k)).sc' ((k-1)-1) (k-1) ((k-1)+1)).g = 0 := by
  rw [HomologicalComplex.shortComplexFunctor'_obj_g, stcComplex_d,
    stcD_exactlyCoeff_eq_zero, ModuleCat.ofHom_zero]

/-- **The comparison map is a quasi-isomorphism on the graded pieces of the size filtration.**
For the coefficient system `ℰ = exactlyCoeff 𝒜 k` (supported on the subsets of size exactly `k`),
the map `toStcHom ℰ : Htc ℰ ⟶ Stc ℰ` is a quasi-isomorphism: both complexes have cohomology
concentrated in degree `k - 1`, where the map is the isomorphism given by evaluation at the
increasing enumerations (the content of `Work.DSM5b.HCF.surj_cohomology`).
Route: `Htc ℰ` is the direct sum, over the `k`-element subsets `S₀`, of the surjection complex
`Work.DSM5b.SurjTerm S₀ (𝒜.M S₀)` with differential `Work.DSM5b.surjD` (in a fibre, the
restriction maps are `res_self`, and a deletion landing on a proper subset meets the zero
coefficient module), whose vanishing in degrees `≠ k-1` and whose explicit top-degree cocycles are
given by `Work.DSM5b.HCF.surj_cohomology` (the `k = 1` and `k = 0` cases are immediate from the
vanishing clause / from both complexes being zero).  `Stc ℰ` is concentrated in degree `k-1` (an
increasing tuple with range of size `k` has length `k`) with zero differential.  Conclude with
`QuasiIso` (root-level class) or the root-level `quasiIsoAt_iff_isIso_homologyMap`. -/
theorem level_quasiIso {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (k : ℕ) :
    QuasiIso (Work.DSM5b.toStcHom (Work.DSM5b.CoeffSys.exactlyCoeff 𝒜 k)) := by
  set ℰ := CoeffSys.exactlyCoeff 𝒜 k with hℰ
  rw [quasiIso_iff]
  intro i
  rcases eq_or_ne i (k - 1) with hi | hi
  · -- the top degree `k - 1`: the comparison is the bijection on the top-degree cocycles
    subst hi
    rw [quasiIsoAt_iff' (f := toStcHom ℰ) (i := (k-1)-1) (j := k-1) (k := (k-1)+1)
      (prev_up_nat (k-1)) (next_up_nat (k-1))]
    refine (shortComplex_quasiIso_iff_ker_bijective _ _ _
      (htc_top_f_eq_zero 𝒜 k) (stc_top_f_eq_zero 𝒜 k) (stc_top_g_eq_zero 𝒜 k)).mpr ?_
    have hg : ((htcComplex ℰ).sc' ((k-1)-1) (k-1) ((k-1)+1)).g.hom =
        CoeffSys.htcD (𝒜 := ℰ) (k-1) := by
      rw [HomologicalComplex.shortComplexFunctor'_obj_g, htcComplex_d, ModuleCat.hom_ofHom]
    have htau : (((HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ)
        ((k-1)-1) (k-1) ((k-1)+1)).map (toStcHom ℰ)).τ₂).hom = toStc ℰ (k-1) := by
      rw [HomologicalComplex.shortComplexFunctor'_map_τ₂, toStcHom_f, ModuleCat.hom_ofHom]
    rw [hg, htau]
    exact ⟨level_ker_injective 𝒜 k, level_ker_surjective 𝒜 k⟩
  · rcases eq_or_ne i 0 with hi0 | hi0
    · -- degree `0 ≠ k - 1` (so `k ≥ 2`): both complexes are exact there
      subst hi0
      have hk2 : 2 ≤ k := by omega
      rw [quasiIsoAt_iff' (f := toStcHom ℰ) (i := 0) (j := 0) (k := 1)
        (prev_up_nat 0) (next_up_nat 0)]
      exact shortComplex_quasiIso_of_exact _
        (htcSc'_exact_zero 𝒜 k hk2) (stcSc'_exact_zero 𝒜 k hk2)
    · -- degree `i ≥ 1`, `i ≠ k - 1`: both complexes are exact there
      have hi1 : 1 ≤ i := by omega
      have hne : (i-1) + 1 ≠ k - 1 := by omega
      rw [show i = (i-1)+1 from (Nat.sub_add_cancel hi1).symm]
      rw [quasiIsoAt_iff' (f := toStcHom ℰ) (i := i-1) (j := (i-1)+1) (k := (i-1)+2)
        (by rw [prev_up_nat]; omega) (by rw [next_up_nat])]
      exact shortComplex_quasiIso_of_exact _
        (htcSc'_exact_succ 𝒜 k (i-1) hne) (stcSc'_exact_succ 𝒜 k (i-1) hne)

end Work.DSM5b.HCF
