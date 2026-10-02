import Mathlib
import Submission.Work.Cohomology.SingularTopFreeDefs
import Submission.Work.Cohomology.homology_iUnion_colim_surjective
import Submission.Work.Cohomology.homology_iUnion_colim_kernel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped CategoryTheory


/-!
# Freeness of the homology of an increasing union

This file proves `Work.Cohomology.free_homology_iUnion_of_split`.

The mathematical content splits in three parts.

* A module-theoretic part: a submodule of a free `ℤ`-module is free, proved by the classical
  well-ordering argument (`free_submodule_of_free`).
* An abstract part: the colimit of a sequence of free `ℤ`-modules along split injective transition
  maps is free (`fsm_colim_free`).
* A topological part: the homology of an increasing union of open sets is the colimit of the
  homologies of the members, which is `homology_iUnion_colim_surjective` together with
  `homology_iUnion_colim_kernel`.
-/

namespace Work.Cohomology

noncomputable section

section InstScoped

attribute [-instance] AddCommGroup.toIntModule

open scoped Classical

set_option linter.unusedSectionVars false

/-! ## Submodules of a free `ℤ`-module are free

Writing `M = ⨁_{x ∈ ι} ℤ`, well-order `ι` and filter `M` by the initial segments
`fsmFle x = ⨁_{y ≤ x} ℤ`.  The `x`-th graded piece of a subgroup `G ≤ M` is a subgroup of `ℤ`,
hence is `0` or cyclic; choosing one generator per nontrivial graded piece gives a basis of `G`. -/

section WellOrdered

variable {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]

/-- The `y`-th basis vector of `ι →₀ ℤ`. -/
def fsmBv (y : ι) : ι →₀ ℤ := Finsupp.single y 1

/-- The submodule of `ι →₀ ℤ` spanned by the basis vectors with index `> x`. -/
def fsmFle (x : ι) : Submodule ℤ (ι →₀ ℤ) :=
  ⨅ z : {y : ι // x < y}, LinearMap.ker (Finsupp.lapply z.1)

/-- The submodule of `ι →₀ ℤ` spanned by the basis vectors with index `≥ x`. -/
def fsmFlt (x : ι) : Submodule ℤ (ι →₀ ℤ) :=
  ⨅ z : {y : ι // x ≤ y}, LinearMap.ker (Finsupp.lapply z.1)

lemma fsm_mem_Fle {x : ι} {f : ι →₀ ℤ} : f ∈ fsmFle x ↔ ∀ y, x < y → f y = 0 := by
  rw [fsmFle, Submodule.mem_iInf]
  constructor
  · intro h y hy
    have := h ⟨y, hy⟩
    rwa [LinearMap.mem_ker, Finsupp.lapply_apply] at this
  · intro h z
    rw [LinearMap.mem_ker, Finsupp.lapply_apply]
    exact h z.1 z.2

lemma fsm_mem_Flt {x : ι} {f : ι →₀ ℤ} : f ∈ fsmFlt x ↔ ∀ y, x ≤ y → f y = 0 := by
  rw [fsmFlt, Submodule.mem_iInf]
  constructor
  · intro h y hy
    have := h ⟨y, hy⟩
    rwa [LinearMap.mem_ker, Finsupp.lapply_apply] at this
  · intro h z
    rw [LinearMap.mem_ker, Finsupp.lapply_apply]
    exact h z.1 z.2

lemma fsmFlt_le_Fle (x : ι) : fsmFlt x ≤ fsmFle x := by
  intro f hf
  rw [fsm_mem_Fle]
  intro y hy
  rw [fsm_mem_Flt] at hf
  exact hf y (le_of_lt hy)

lemma fsmFle_mono {x y : ι} (h : x ≤ y) : fsmFle x ≤ fsmFle y := by
  intro f hf
  rw [fsm_mem_Fle] at hf ⊢
  intro z hz
  exact hf z (lt_of_le_of_lt h hz)

lemma fsmFlt_mono {x y : ι} (h : x ≤ y) : fsmFlt x ≤ fsmFlt y := by
  intro f hf
  rw [fsm_mem_Flt] at hf ⊢
  intro z hz
  exact hf z (le_trans h hz)

lemma fsmFle_le_Flt_of_lt {x y : ι} (h : x < y) : fsmFle x ≤ fsmFlt y := by
  intro f hf
  rw [fsm_mem_Flt]
  intro z hz
  rw [fsm_mem_Fle] at hf
  exact hf z (lt_of_lt_of_le h hz)

lemma fsmBv_mem_Fle (x : ι) : fsmBv x ∈ fsmFle x := by
  rw [fsm_mem_Fle]
  intro y hy
  rw [fsmBv, Finsupp.single_eq_of_ne (ne_of_gt hy)]

lemma fsmBv_notMem_Flt (x : ι) : fsmBv x ∉ fsmFlt x := by
  rw [fsm_mem_Flt]
  intro h
  have hx := h x le_rfl
  rw [fsmBv, Finsupp.single_eq_same] at hx
  exact one_ne_zero hx

lemma fsmFle_eq (x : ι) : fsmFle x = fsmFlt x ⊔ ℤ ∙ fsmBv x := by
  apply le_antisymm
  · intro f hf
    rw [fsm_mem_Fle] at hf
    rw [Submodule.mem_sup]
    refine ⟨f - f x • fsmBv x, ?_, f x • fsmBv x, ?_, sub_add_cancel _ _⟩
    · rw [fsm_mem_Flt]
      intro y hy
      rw [Finsupp.sub_apply, Finsupp.smul_apply, fsmBv]
      rcases eq_or_lt_of_le hy with h' | h'
      · subst h'
        rw [Finsupp.single_eq_same, smul_eq_mul]
        ring
      · rw [hf y h', Finsupp.single_eq_of_ne (ne_of_gt h'), smul_zero, sub_zero]
    · rw [Submodule.mem_span_singleton]
      exact ⟨f x, rfl⟩
  · refine sup_le (fsmFlt_le_Fle x) ?_
    intro f hf
    rw [Submodule.mem_span_singleton] at hf
    obtain ⟨c, rfl⟩ := hf
    rw [fsm_mem_Fle]
    intro y hy
    rw [Finsupp.smul_apply, fsmBv, Finsupp.single_eq_of_ne (ne_of_gt hy), smul_zero]

lemma fsmFlt_inf_bv_eq_bot (x : ι) : fsmFlt x ⊓ ℤ ∙ fsmBv x = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro f hf
  rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hf
  obtain ⟨hf1, c, rfl⟩ := hf
  rw [fsm_mem_Flt] at hf1
  have hx := hf1 x le_rfl
  rw [Finsupp.smul_apply, fsmBv, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hx
  rw [hx, zero_smul]

section Subgroup

variable (G : Submodule ℤ (ι →₀ ℤ))

/-- The part of `G` supported on the initial segment `≤ x`. -/
def fsmGle (x : ι) : Submodule ℤ (ι →₀ ℤ) := G ⊓ fsmFle x

/-- The part of `G` supported on the initial segment `< x`. -/
def fsmGlt (x : ι) : Submodule ℤ (ι →₀ ℤ) := G ⊓ fsmFlt x

lemma fsm_mem_Gle {x : ι} {g : ι →₀ ℤ} : g ∈ fsmGle G x ↔ g ∈ G ∧ ∀ y, x < y → g y = 0 := by
  rw [fsmGle, Submodule.mem_inf, fsm_mem_Fle]

lemma fsm_mem_Glt {x : ι} {g : ι →₀ ℤ} : g ∈ fsmGlt G x ↔ g ∈ G ∧ ∀ y, x ≤ y → g y = 0 := by
  rw [fsmGlt, Submodule.mem_inf, fsm_mem_Flt]

lemma fsmGlt_le_Gle (x : ι) : fsmGlt G x ≤ fsmGle G x :=
  inf_le_inf_left G (fsmFlt_le_Fle x)

lemma fsmGle_le_Glt {x y : ι} (h : x < y) : fsmGle G x ≤ fsmGlt G y :=
  inf_le_inf_left G (fsmFle_le_Flt_of_lt h)

lemma fsmGle_le_G (x : ι) : fsmGle G x ≤ G := inf_le_left

lemma fsmGlt_le_G (x : ι) : fsmGlt G x ≤ G := inf_le_left

lemma fsmGle_le_Fle (x : ι) : fsmGle G x ≤ fsmFle x := inf_le_right

/-- The `x`-th graded piece of `G`, as a submodule of `ℤ`. -/
def fsmJ (x : ι) : Submodule ℤ ℤ :=
  LinearMap.range ((Finsupp.lapply x).comp (fsmGle G x).subtype)

/-- A generator of the `x`-th graded piece. -/
def fsmGen (x : ι) : ℤ := Submodule.IsPrincipal.generator (fsmJ G x)

/-- An element of `fsmGle G x` whose `x`-th coordinate generates the `x`-th graded piece. -/
def fsmHsel (x : ι) : fsmGle G x :=
  Classical.choose
    (LinearMap.mem_range.mp (Submodule.IsPrincipal.generator_mem (fsmJ G x)))

/-- The chosen element as a vector of `ι →₀ ℤ`. -/
def fsmHvec (x : ι) : ι →₀ ℤ := (fsmHsel G x : ι →₀ ℤ)

lemma fsmHsel_spec (x : ι) : (fsmHvec G x) x = fsmGen G x := by
  have h := Classical.choose_spec
    (LinearMap.mem_range.mp (Submodule.IsPrincipal.generator_mem (fsmJ G x)))
  show (fsmHsel G x : ι →₀ ℤ) x = Submodule.IsPrincipal.generator (fsmJ G x)
  simpa [fsmHsel, fsmJ, LinearMap.comp_apply, Finsupp.lapply_apply] using h

lemma fsmHvec_mem_Gle (x : ι) : fsmHvec G x ∈ fsmGle G x := (fsmHsel G x).2

lemma fsmHvec_mem_G (x : ι) : fsmHvec G x ∈ G := fsmGle_le_G G x (fsmHvec_mem_Gle G x)

/-- **The graded decomposition at level `x`.**  The elements of `G` supported on `≤ x` are exactly
those supported on `< x` together with the multiples of the chosen generator `fsmHvec G x`. -/
lemma fsmGle_eq (x : ι) : fsmGle G x = fsmGlt G x ⊔ ℤ ∙ fsmHvec G x := by
  apply le_antisymm
  · intro g hg
    have hgG : g ∈ G := fsmGle_le_G G x hg
    have hgF : ∀ y, x < y → g y = 0 := fsm_mem_Fle.mp (fsmGle_le_Fle G x hg)
    have hgJ : g x ∈ fsmJ G x := by
      rw [fsmJ, LinearMap.mem_range]
      exact ⟨⟨g, hg⟩, by rw [LinearMap.comp_apply, Finsupp.lapply_apply]; rfl⟩
    rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hgJ
    obtain ⟨c, hc⟩ := hgJ
    rw [Submodule.mem_sup]
    refine ⟨g - c • fsmHvec G x, ?_, c • fsmHvec G x, ?_, sub_add_cancel _ _⟩
    · rw [fsm_mem_Glt]
      refine ⟨Submodule.sub_mem _ hgG (Submodule.smul_mem _ _ (fsmHvec_mem_G G x)), ?_⟩
      intro y hy
      rw [Finsupp.sub_apply, Finsupp.smul_apply]
      rcases eq_or_lt_of_le hy with h' | h'
      · subst h'
        simp only [hc, fsmHsel_spec, fsmGen, smul_eq_mul]
        ring
      · rw [hgF y h', (fsm_mem_Fle.mp (fsmGle_le_Fle G x (fsmHvec_mem_Gle G x))) y h',
          smul_zero, sub_zero]
    · rw [Submodule.mem_span_singleton]
      exact ⟨c, rfl⟩
  · refine sup_le (fsmGlt_le_Gle G x) ?_
    intro g hg
    rw [Submodule.mem_span_singleton] at hg
    obtain ⟨c, rfl⟩ := hg
    rw [fsm_mem_Gle]
    refine ⟨Submodule.smul_mem _ _ (fsmHvec_mem_G G x), fun y hy => ?_⟩
    rw [Finsupp.smul_apply, (fsm_mem_Fle.mp (fsmGle_le_Fle G x (fsmHvec_mem_Gle G x))) y hy,
        smul_zero]

lemma fsmHvec_notMem_Glt (x : ι) (h : fsmGen G x ≠ 0) : fsmHvec G x ∉ fsmGlt G x := by
  intro hg
  rw [fsm_mem_Glt] at hg
  have hx : (fsmHvec G x) x = 0 := hg.2 x le_rfl
  rw [fsmHsel_spec] at hx
  exact h hx

lemma fsm_mem_Gle_max' (g : ι →₀ ℤ) (hg : g ∈ G) (hne : g.support.Nonempty) :
    g ∈ fsmGle G (g.support.max' hne) := by
  rw [fsm_mem_Gle]
  refine ⟨hg, fun y hy => ?_⟩
  by_contra hfy
  have hymem : y ∈ g.support := Finsupp.mem_support_iff.mpr hfy
  exact absurd hy (not_lt.mpr (Finset.le_max' g.support y hymem))

lemma fsm_max'_lt_of_mem_Glt {x : ι} (g : ι →₀ ℤ) (hg : g ∈ fsmGlt G x)
    (hne : g.support.Nonempty) : g.support.max' hne < x := by
  rw [Finset.max'_lt_iff]
  intro y hy
  rw [fsm_mem_Glt] at hg
  by_contra h
  exact Finsupp.mem_support_iff.mp hy (hg.2 y (not_lt.mp h))

/-- The candidate basis of `G`. -/
def fsmS : Set (ι →₀ ℤ) := Set.range (fun x : {x : ι // fsmGen G x ≠ 0} => fsmHvec G x.1)

lemma fsmHvec_mem_S {x : ι} (h : fsmGen G x ≠ 0) : fsmHvec G x ∈ fsmS G := ⟨⟨x, h⟩, rfl⟩

/-- The coordinate functional `G → ℤ` at `y`. -/
def fsmPsi (y : ι) : ↥G →ₗ[ℤ] ℤ := (Finsupp.lapply y).comp (Submodule.subtype G)

lemma fsmPsi_apply (y : ι) (g : ↥G) : fsmPsi G y g = (g : ι →₀ ℤ) y := by
  rw [fsmPsi, LinearMap.comp_apply, Finsupp.lapply_apply]; rfl

/-- **Linearity of the candidate basis.** -/
lemma fsm_linearIndependent :
    LinearIndependent ℤ
      (fun x : {x : ι // fsmGen G x ≠ 0} => (⟨fsmHvec G x.1, fsmHvec_mem_G G x.1⟩ : ↥G)) := by
  rw [linearIndependent_iff]
  intro l hl
  by_contra hne
  have hsupp : l.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (Finsupp.support_eq_empty.mp h)
  have him : (l.support.image (Subtype.val : {x : ι // fsmGen G x ≠ 0} → ι)).Nonempty :=
    hsupp.image (Subtype.val : {x : ι // fsmGen G x ≠ 0} → ι)
  let x₀ : ι := (l.support.image (Subtype.val : {x : ι // fsmGen G x ≠ 0} → ι)).max' him
  have hx₀mem : x₀ ∈ l.support.image (Subtype.val : {x : ι // fsmGen G x ≠ 0} → ι) :=
    Finset.max'_mem _ _
  obtain ⟨i₀, hi₀, hi₀val⟩ := Finset.mem_image.mp hx₀mem
  have hl' : l.support.sum (fun i => l i • (⟨fsmHvec G i.1, fsmHvec_mem_G G i.1⟩ : ↥G)) = 0 := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using hl
  have hcoord : l.support.sum (fun i => l i * ((fsmHvec G i.1) x₀)) = 0 := by
    have h := congrArg (fsmPsi G x₀) hl'
    rw [map_sum, map_zero] at h
    simpa [fsmPsi_apply, Finsupp.smul_apply, smul_eq_mul] using h
  have hsingle : l.support.sum (fun i => l i * ((fsmHvec G i.1) x₀))
      = l i₀ * ((fsmHvec G i₀.1) x₀) := by
    refine Finset.sum_eq_single i₀ ?_ ?_
    · intro i hi hii
      have hle : i.1 ≤ x₀ := Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have hlt : i.1 < x₀ := by
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (Subtype.ext (h.trans hi₀val.symm)) hii
      rw [(fsm_mem_Fle.mp (fsmGle_le_Fle G i.1 (fsmHvec_mem_Gle G i.1))) x₀ hlt, mul_zero]
    · intro hnot
      rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]
  rw [hsingle, ← hi₀val, fsmHsel_spec] at hcoord
  have hl0 : l i₀ = 0 := by
    rcases mul_eq_zero.mp hcoord with h | h
    · exact h
    · exact absurd h i₀.2
  exact (Finsupp.mem_support_iff.mp hi₀) hl0

/-- **Spanning of the candidate basis.** -/
lemma fsm_G_le_span : G ≤ Submodule.span ℤ (fsmS G) := by
  have key : ∀ x : ι, fsmGle G x ≤ Submodule.span ℤ (fsmS G) := by
    intro x
    refine WellFounded.induction (C := fun y => fsmGle G y ≤ Submodule.span ℤ (fsmS G))
      (wellFounded_lt (α := ι)) x ?_
    intro x ih
    intro g hg
    rw [fsmGle_eq G x] at hg
    rw [Submodule.mem_sup] at hg
    obtain ⟨g1, hg1, g2, hg2, h12⟩ := hg
    have h1 : g1 ∈ Submodule.span ℤ (fsmS G) := by
      by_cases hg1z : g1 = 0
      · rw [hg1z]; exact Submodule.zero_mem _
      · have hne1 : g1.support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          exact hg1z (Finsupp.support_eq_empty.mp h)
        exact ih _ (fsm_max'_lt_of_mem_Glt G g1 hg1 hne1)
          (fsm_mem_Gle_max' G g1 (fsmGlt_le_G G x hg1) hne1)
    have h2 : g2 ∈ Submodule.span ℤ (fsmS G) := by
      rw [Submodule.mem_span_singleton] at hg2
      obtain ⟨c, rfl⟩ := hg2
      by_cases hgen : fsmGen G x = 0
      · by_cases hz : fsmHvec G x = 0
        · rw [hz, smul_zero]; exact Submodule.zero_mem _
        · have hmem : fsmHvec G x ∈ fsmGlt G x := by
            rw [fsm_mem_Glt]
            refine ⟨fsmHvec_mem_G G x, fun y hy => ?_⟩
            rcases eq_or_lt_of_le hy with h' | h'
            · subst h'; rw [fsmHsel_spec, hgen]
            · exact (fsm_mem_Fle.mp (fsmGle_le_Fle G x (fsmHvec_mem_Gle G x))) y h'
          have hne' : (fsmHvec G x).support.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro h
            exact hz (Finsupp.support_eq_empty.mp h)
          exact Submodule.smul_mem _ c
            (ih _ (fsm_max'_lt_of_mem_Glt G _ hmem hne')
              (fsm_mem_Gle_max' G _ (fsmGlt_le_G G x hmem) hne'))
      · exact Submodule.smul_mem _ c (Submodule.subset_span (fsmHvec_mem_S G hgen))
    rw [← h12]
    exact Submodule.add_mem _ h1 h2
  intro g hg
  by_cases h0 : g = 0
  · rw [h0]; exact Submodule.zero_mem _
  · have hne : g.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact h0 (Finsupp.support_eq_empty.mp h)
    exact key _ (fsm_mem_Gle_max' G g hg hne)

end Subgroup

end WellOrdered

/-- **A submodule of a free `ℤ`-module is free.** -/
theorem free_submodule_of_free_finsupp {ι : Type*} (N : Submodule ℤ (ι →₀ ℤ)) :
    Module.Free ℤ ↥N := by
  obtain ⟨lo, hlo⟩ := exists_wellFoundedLT ι
  letI := lo
  haveI := hlo
  let v : {x : ι // fsmGen N x ≠ 0} → ↥N :=
    fun x => ⟨fsmHvec N x.1, fsmHvec_mem_G N x.1⟩
  have hli : LinearIndependent ℤ v := fsm_linearIndependent N
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro y _
    have hy : ((y : ↥N) : ι →₀ ℤ) ∈ Submodule.span ℤ (fsmS N) := fsm_G_le_span N y.2
    have hmap : Submodule.map (Submodule.subtype N) (Submodule.span ℤ (Set.range v))
        = Submodule.span ℤ (fsmS N) := by
      rw [Submodule.map_span]
      congr 1
      ext z
      constructor
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨v x, ⟨x, rfl⟩, rfl⟩
    rw [← hmap, Submodule.mem_map] at hy
    obtain ⟨w, hw, hwz⟩ := hy
    rw [← Subtype.ext hwz]
    exact hw
  exact Module.Free.of_basis (Module.Basis.mk hli hsp)

/-- **Every subgroup of a free abelian group is free.** -/
theorem free_submodule_of_free {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M]
    (N : Submodule ℤ M) : Module.Free ℤ ↥N := by
  let e : M ≃ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M →₀ ℤ) := (Module.Free.chooseBasis ℤ M).repr
  let e' : M →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M →₀ ℤ) := e
  have hfree : Module.Free ℤ ↥(N.map e') := free_submodule_of_free_finsupp _
  exact Module.Free.of_equiv' hfree (e.submoduleMap N).symm


section Colim

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module ℤ (A n)]
variable {B : Type*} [AddCommGroup B] [Module ℤ B]

/-- **Freeness of a colimit of free modules along split injections.**

Given modules `A n`, transition maps `F n k : A n ⟶ A k` for `n ≤ k` compatible with composition,
compatibly split injections `F n (n+1)`, a module `B` with compatible maps `φ n : A n ⟶ B` that
are jointly surjective and whose "kernel is eventually killed" (`hker`), the module `B` is free
whenever the `A n` are. -/
theorem fsm_colim_free
    (F : ∀ n k, n ≤ k → A n →ₗ[ℤ] A k)
    (hF_self : ∀ n (h : n ≤ n), F n n h = LinearMap.id)
    (hF_comp : ∀ n k l (hnk : n ≤ k) (hkl : k ≤ l),
      F n l (le_trans hnk hkl) = (F k l hkl).comp (F n k hnk))
    (φ : ∀ n, A n →ₗ[ℤ] B)
    (hφ : ∀ n k (hnk : n ≤ k), (φ k).comp (F n k hnk) = φ n)
    (hsplit : ∀ n, ∃ σ : (A (n+1) →ₗ[ℤ] A n), σ.comp (F n (n+1) (Nat.le_succ n)) = LinearMap.id)
    (hfree : ∀ n, Module.Free ℤ (A n))
    (hsurj : ∀ b : B, ∃ (n : ℕ) (x : A n), φ n x = b)
    (hker : ∀ (n : ℕ) (x : A n), φ n x = 0 → ∃ (k : ℕ) (hk : n ≤ k), F n k hk x = 0) :
    Module.Free ℤ B := by
  classical
  choose σ hσ using hsplit
  -- the step maps are injective
  have step_inj : ∀ n, Function.Injective (F n (n+1) (Nat.le_succ n)) := by
    intro n a b hab
    have h1 := LinearMap.congr_fun (hσ n) a
    have h2 := LinearMap.congr_fun (hσ n) b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    exact h1.symm.trans ((congrArg (σ n) hab).trans h2)
  -- all transition maps are injective
  have Finj : ∀ n k (hk : n ≤ k), Function.Injective (F n k hk) := by
    intro n k hk
    refine Nat.le_induction (P := fun k hk => Function.Injective (F n k hk)) ?_ ?_ k hk
    · intro a b hab
      simpa [hF_self n] using hab
    · intro m hnm ih a b hab
      have hc := hF_comp n m (m+1) hnm (Nat.le_succ m)
      rw [hc] at hab
      simp only [LinearMap.comp_apply] at hab
      exact ih (step_inj m hab)
  -- the new part at level n
  let C := fun n : ℕ => ↥(LinearMap.ker (σ n))
  letI hCac : ∀ n, AddCommMonoid (C n) := fun n => (LinearMap.ker (σ n)).addCommMonoid
  letI hCmod : ∀ n, Module ℤ (C n) := fun n => (LinearMap.ker (σ n)).module
  letI hDSmod : Module ℤ (DirectSum ℕ (fun n => ↥(LinearMap.ker (σ n)))) := DirectSum.instModule
  let incl := fun n => (LinearMap.ker (σ n)).subtype
  have hσC : ∀ n (c : C n), σ n (incl n c) = 0 := by
    intro n c
    have h := c.2
    simpa [incl] using (LinearMap.mem_ker.mp h)
  have incl_inj : ∀ n, Function.Injective (incl n) := by
    intro n a b hab
    exact Subtype.ext (by simpa [incl] using hab)
  -- the direct sum map
  let Ψ' := DirectSum.toModule ℤ ℕ B (M := fun n => ↥(LinearMap.ker (σ n)))
    (fun n => (φ (n+1)).comp (incl n))
  let Ψ := (φ 0).coprod Ψ'
  have hΨ_apply : ∀ (a : A 0) (c : Π₀ n, C n), Ψ (a, c) = φ 0 a + Ψ' c :=
    fun a c => LinearMap.coprod_apply _ _ _
  have hΨ'_single : ∀ (n : ℕ) (c : C n),
      Ψ' (DFinsupp.single n c) = φ (n+1) (incl n c) := by
    intro n c
    exact DirectSum.toModule_lof (M := fun n => ↥(LinearMap.ker (σ n))) ℤ n c
  -- surjectivity
  have hsurj' : ∀ n (x : A n), ∃ y : A 0 × (Π₀ n, C n), Ψ y = φ n x := by
    intro n
    induction n with
    | zero =>
      intro x
      exact ⟨(x, 0), by rw [hΨ_apply, map_zero, add_zero]⟩
    | succ n ih =>
      intro x
      have hmem : x - F n (n+1) (Nat.le_succ n) (σ n x) ∈ LinearMap.ker (σ n) := by
        rw [LinearMap.mem_ker, map_sub]
        have h1 := LinearMap.congr_fun (hσ n) (σ n x)
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
        rw [h1, sub_self]
      obtain ⟨y, hy⟩ := ih (σ n x)
      refine ⟨(y.1, y.2 + DFinsupp.single n ⟨x - F n (n+1) (Nat.le_succ n) (σ n x), hmem⟩), ?_⟩
      have h2 : incl n ⟨x - F n (n+1) (Nat.le_succ n) (σ n x), hmem⟩
          = x - F n (n+1) (Nat.le_succ n) (σ n x) := rfl
      have h3 := LinearMap.congr_fun (hφ n (n+1) (Nat.le_succ n)) (σ n x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h3
      have hy' : φ 0 y.1 + Ψ' y.2 = φ n (σ n x) := by rw [← hΨ_apply]; exact hy
      have hx : x = F n (n+1) (Nat.le_succ n) (σ n x)
          + (x - F n (n+1) (Nat.le_succ n) (σ n x)) := by abel
      have hr : φ (n+1) x = φ n (σ n x)
          + φ (n+1) (incl n ⟨x - F n (n+1) (Nat.le_succ n) (σ n x), hmem⟩) := by
        rw [congrArg (φ (n+1)) hx, map_add, h3, h2]
      rw [hΨ_apply, map_add, hΨ'_single, ← add_assoc, hy', hr]
  -- reconstruction of an element of the colimit from its coordinates
  let xN : A 0 × (Π₀ n, C n) → ∀ m, A m := fun y m =>
    Nat.rec (motive := fun m => A m) y.1
      (fun m ih => F m (m+1) (Nat.le_succ m) ih + incl m (y.2 m)) m
  have xN_zero : ∀ y, xN y 0 = y.1 := fun y => rfl
  have xN_succ : ∀ y m, xN y (m+1) = F m (m+1) (Nat.le_succ m) (xN y m) + incl m (y.2 m) :=
    fun y m => rfl
  have xN_sigma : ∀ y m, σ m (xN y (m+1)) = xN y m := by
    intro y m
    have h1 := LinearMap.congr_fun (hσ m) (xN y m)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [xN_succ, map_add, h1, hσC, add_zero]
  have xN_agree : ∀ (N : ℕ) (y y' : A 0 × (Π₀ n, C n)), y.1 = y'.1 →
      (∀ n, n < N → y.2 n = y'.2 n) → xN y N = xN y' N := by
    intro N
    induction N with
    | zero => intro y y' h0 h; rw [xN_zero, xN_zero, h0]
    | succ N ih =>
      intro y y' h0 h
      rw [xN_succ, xN_succ, ih y y' h0 (fun n hn => h n (Nat.lt_succ_of_lt hn)),
        h N (Nat.lt_succ_self N)]
  -- an element of `Π₀` supported in `< N` is evaluated by the sum over `range N`
  have hΨ'_eq : ∀ (N : ℕ) (c : Π₀ n, C n), (∀ n, N ≤ n → c n = 0) →
      Ψ' c = ∑ n ∈ Finset.range N, φ (n+1) (incl n (c n)) := by
    intro N
    induction N with
    | zero =>
      intro c h
      have hc : c = 0 := DFinsupp.ext fun n => h n (Nat.zero_le n)
      rw [hc, map_zero, Finset.range_zero, Finset.sum_empty]
    | succ N ih =>
      intro c h
      have hsub : ∀ n, N ≤ n → (c - DFinsupp.single N (c N)) n = 0 := by
        intro n hn
        rw [DFinsupp.sub_apply]
        rcases eq_or_lt_of_le hn with h' | h'
        · subst h'; rw [DFinsupp.single_eq_same, sub_self]
        · rw [DFinsupp.single_eq_of_ne (ne_of_gt h'), h n h', sub_zero]
      have hsplitc : c = (c - DFinsupp.single N (c N)) + DFinsupp.single N (c N) := by abel
      conv_lhs => rw [hsplitc]
      rw [map_add, ih (c - DFinsupp.single N (c N)) hsub, hΨ'_single, Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [DFinsupp.sub_apply,
        DFinsupp.single_eq_of_ne (ne_of_lt (Finset.mem_range.mp hn)), sub_zero]
  have hΨ_eq : ∀ (N : ℕ) (y : A 0 × (Π₀ n, C n)), (∀ n, N ≤ n → y.2 n = 0) →
      Ψ y = φ N (xN y N) := by
    intro N
    induction N with
    | zero =>
      rintro ⟨a, c⟩ h
      have hy : c = 0 := DFinsupp.ext fun n => h n (Nat.zero_le n)
      rw [hΨ_apply, hy, map_zero, add_zero, xN_zero]
    | succ N ih =>
      rintro ⟨a, c⟩ h
      have hdrop : ∀ n, N ≤ n → (c - DFinsupp.single N (c N)) n = 0 := by
        intro n hn
        rw [DFinsupp.sub_apply]
        rcases eq_or_lt_of_le hn with h' | h'
        · subst h'; rw [DFinsupp.single_eq_same, sub_self]
        · rw [DFinsupp.single_eq_of_ne (ne_of_gt h'), h n h', sub_zero]
      have h1 := ih (a, c - DFinsupp.single N (c N)) hdrop
      have h2 : xN (a, c - DFinsupp.single N (c N)) N = xN (a, c) N :=
        (xN_agree N (a, c) (a, c - DFinsupp.single N (c N)) rfl
          (fun n hn => by simp [DFinsupp.sub_apply, DFinsupp.single_eq_of_ne (ne_of_lt hn)])).symm
      have h3 : (a, c) = (a, c - DFinsupp.single N (c N)) + (0, DFinsupp.single N (c N)) := by
        ext <;> simp [DFinsupp.sub_apply]
      have h4 := LinearMap.congr_fun (hφ N (N+1) (Nat.le_succ N)) (xN (a, c) N)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h4
      have hL : Ψ (a, c) = φ N (xN (a, c) N) + φ (N+1) (incl N (c N)) := by
        conv_lhs => rw [h3]
        rw [map_add, h1, h2, hΨ_apply, map_zero, zero_add, hΨ'_single]
      have hR : φ (N+1) (xN (a, c) (N+1)) = φ N (xN (a, c) N) + φ (N+1) (incl N (c N)) := by
        rw [xN_succ, map_add, h4]
      rw [hL, hR]
  have hkerΨ : ∀ y : A 0 × (Π₀ n, C n), Ψ y = 0 → y = 0 := by
    rintro ⟨a, c⟩ hy
    obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → c n = 0 := by
      refine ⟨c.support.sup id + 1, fun n hn => ?_⟩
      by_contra hc
      have hmem : n ∈ c.support := DFinsupp.mem_support_iff.mpr hc
      have hle : n ≤ c.support.sup id := Finset.le_sup (f := id) hmem
      omega
    have hxN : xN (a, c) N = 0 := by
      have h1 : φ N (xN (a, c) N) = 0 := by
        have hh := hΨ_eq N (a, c) hN
        rw [hy] at hh
        exact hh.symm
      obtain ⟨k, hk, hk0⟩ := hker N (xN (a, c) N) h1
      exact Finj N k hk (by rw [hk0, map_zero])
    have hdown : ∀ m, m ≤ N → xN (a, c) m = 0 := by
      intro m hm
      have key : ∀ d, N - m = d → xN (a, c) m = 0 := by
        intro d
        induction d generalizing m with
        | zero =>
          intro he
          have : m = N := by omega
          rw [this]; exact hxN
        | succ d ih =>
          intro he
          have h1 : xN (a, c) (m+1) = 0 := ih (m+1) (by omega) (by omega)
          rw [← xN_sigma (a, c) m, h1, map_zero]
      exact key (N - m) rfl
    have hc0 : c = 0 := by
      refine DFinsupp.ext fun m => ?_
      by_cases hm : m < N
      · have h1 : xN (a, c) (m+1) = 0 := hdown (m+1) (by omega)
        have h2 : xN (a, c) m = 0 := hdown m (by omega)
        have h5 := xN_succ (a, c) m
        rw [h1, h2, map_zero, zero_add] at h5
        exact incl_inj m (h5.symm.trans (map_zero (incl m)).symm)
      · exact hN m (not_lt.mp hm)
    have ha0 : a = 0 := by
      have hh := hdown 0 (Nat.zero_le N)
      rwa [xN_zero] at hh
    exact Prod.ext ha0 hc0
  have hinj : Function.Injective Ψ := fun y y' h => by
    have hzero : y - y' = 0 := hkerΨ (y - y') (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp hzero
  haveI hfreeC : ∀ n, Module.Free ℤ (C n) := fun n =>
    free_submodule_of_free (LinearMap.ker (σ n))
  haveI hfreeD : Module.Free ℤ (Π₀ n, C n) := Module.Free.dfinsupp ℤ (fun n => C n)
  haveI hfreeP : Module.Free ℤ (A 0 × (Π₀ n, C n)) := Module.Free.prod ℤ (A 0) (Π₀ n, C n)
  exact Module.Free.of_equiv' hfreeP
    (LinearEquiv.ofBijective Ψ ⟨hinj, fun b => by
      obtain ⟨n, x, hx⟩ := hsurj b
      obtain ⟨y, hy⟩ := hsurj' n x
      exact ⟨y, by rw [hy, hx]⟩⟩)

end Colim

end InstScoped

/-- **Freeness of the homology of an increasing union of open sets with split transition
maps.**  If `V : ℕ → Set X` is an increasing sequence of open subsets, the `m`-th homology of each
`V n` is free, and each transition map `H_m(V n) → H_m(V (n+1))` is split injective, then the
`m`-th homology of the union `⋃ n, V n` is free. -/
theorem free_homology_iUnion_of_split {X : TopCat} (V : ℕ → Set X)
    (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V) (m : ℕ)
    (hfree : ∀ n, Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of (V n))).homology m))
    (hsplit : ∀ n, ∃ σ : ↥((Work.Cohomology.singularChains ℤ (TopCat.of (V (n+1)))).homology m) →ₗ[ℤ]
        ↥((Work.Cohomology.singularChains ℤ (TopCat.of (V n))).homology m),
      σ.comp (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
        (TopCat.of (V (n+1))) (Work.Cohomology.inclSet (hmono (Nat.le_succ n)))) m).hom = LinearMap.id) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of (⋃ n, V n))).homology m) := by
  classical
  let A : ℕ → Type := fun n => ↥((Work.Cohomology.singularChains ℤ (TopCat.of (V n))).homology m)
  let B : Type := ↥((Work.Cohomology.singularChains ℤ (TopCat.of (⋃ n, V n))).homology m)
  let F : ∀ n k, n ≤ k → A n →ₗ[ℤ] A k := fun n k hk =>
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
      (TopCat.of (V k)) (Work.Cohomology.inclSet (hmono hk))) m).hom
  let φ : ∀ n, A n →ₗ[ℤ] B := fun n =>
    (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
      (TopCat.of (⋃ k, V k)) (Work.Cohomology.toUnion V n)) m).hom
  have hF_self : ∀ n (h : n ≤ n), F n n h = LinearMap.id := by
    intro n h
    show (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
      (TopCat.of (V n)) (Work.Cohomology.inclSet (hmono h))) m).hom = LinearMap.id
    have h1 : Work.Cohomology.inclSet (hmono h) = 𝟙 (TopCat.of (V n)) := by
      ext x; rfl
    rw [h1]
    simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id,
      HomologicalComplex.homologyMap_id, ModuleCat.hom_id]
  have hF_comp : ∀ n k l (hnk : n ≤ k) (hkl : k ≤ l),
      F n l (le_trans hnk hkl) = (F k l hkl).comp (F n k hnk) := by
    intro n k l hnk hkl
    show (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
        (TopCat.of (V l)) (Work.Cohomology.inclSet (hmono (le_trans hnk hkl)))) m).hom
      = ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V k))
          (TopCat.of (V l)) (Work.Cohomology.inclSet (hmono hkl))) m).hom).comp
        ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
          (TopCat.of (V k)) (Work.Cohomology.inclSet (hmono hnk))) m).hom)
    have h1 : Work.Cohomology.inclSet (hmono (le_trans hnk hkl))
        = Work.Cohomology.inclSet (hmono hnk) ≫ Work.Cohomology.inclSet (hmono hkl) := by
      ext x; rfl
    rw [h1, Work.Cohomology.chainMap_comp', HomologicalComplex.homologyMap_comp,
      ModuleCat.hom_comp]
  have hφ : ∀ n k (hnk : n ≤ k), (φ k).comp (F n k hnk) = φ n := by
    intro n k hnk
    show ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V k))
        (TopCat.of (⋃ j, V j)) (Work.Cohomology.toUnion V k)) m).hom).comp
      ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
        (TopCat.of (V k)) (Work.Cohomology.inclSet (hmono hnk))) m).hom)
      = (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
        (TopCat.of (⋃ j, V j)) (Work.Cohomology.toUnion V n)) m).hom
    have h1 : Work.Cohomology.inclSet (hmono hnk) ≫ Work.Cohomology.toUnion V k
        = Work.Cohomology.toUnion V n := by
      ext x; rfl
    rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
      ← Work.Cohomology.chainMap_comp', h1]
  have hsurj : ∀ b : B, ∃ (n : ℕ) (x : A n), φ n x = b := by
    intro b
    obtain ⟨n, y, hy⟩ := Work.Cohomology.homology_iUnion_colim_surjective V hopen hmono m b
    exact ⟨n, y, hy⟩
  have hker : ∀ (n : ℕ) (x : A n), φ n x = 0 →
      ∃ (k : ℕ) (hk : n ≤ k), F n k hk x = 0 := by
    intro n x hx
    obtain ⟨k, hk, h⟩ := Work.Cohomology.homology_iUnion_colim_kernel V hopen hmono m n x hx
    exact ⟨k, hk, h⟩
  exact Work.Cohomology.fsm_colim_free (A := A) (B := B) F hF_self hF_comp φ hφ hsplit hfree
    hsurj hker

end

end Work.Cohomology
