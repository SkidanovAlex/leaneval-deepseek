import Mathlib

/-!
# Submodules of a free `ℤ`-module are free

Every subgroup of a free abelian group is free, of arbitrary rank.  Mathlib has only the
finite-rank case (`Submodule.exists_basis_of_pid`); here we run the classical well-ordering
argument: write `M ≃ ⨁_{x ∈ ι} ℤ`, well-order `ι`, filter by initial segments, and observe
that each graded piece of the subgroup is a subgroup of `ℤ`, hence a principal ideal whose
generator we choose.

The `fsi*` definitions below are a (renamed) copy of the development in
`Submission/Work/Cohomology/free_homology_iUnion_of_split.lean`.
-/

namespace Work.Cohomology

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

/-! ## Submodules of a free `ℤ`-module are free

Writing `M = ⨁_{x ∈ ι} ℤ`, well-order `ι` and filter `M` by the initial segments
`fsiFle x = ⨁_{y ≤ x} ℤ`.  The `x`-th graded piece of a subgroup `G ≤ M` is a subgroup of `ℤ`,
hence is `0` or cyclic; choosing one generator per nontrivial graded piece gives a basis of `G`. -/

section WellOrdered

variable {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]

/-- The `y`-th basis vector of `ι →₀ ℤ`. -/
def fsiBv (y : ι) : ι →₀ ℤ := Finsupp.single y 1

/-- The submodule of `ι →₀ ℤ` spanned by the basis vectors with index `> x`. -/
def fsiFle (x : ι) : Submodule ℤ (ι →₀ ℤ) :=
  ⨅ z : {y : ι // x < y}, LinearMap.ker (Finsupp.lapply z.1)

/-- The submodule of `ι →₀ ℤ` spanned by the basis vectors with index `≥ x`. -/
def fsiFlt (x : ι) : Submodule ℤ (ι →₀ ℤ) :=
  ⨅ z : {y : ι // x ≤ y}, LinearMap.ker (Finsupp.lapply z.1)

lemma fsi_mem_Fle {x : ι} {f : ι →₀ ℤ} : f ∈ fsiFle x ↔ ∀ y, x < y → f y = 0 := by
  rw [fsiFle, Submodule.mem_iInf]
  constructor
  · intro h y hy
    have := h ⟨y, hy⟩
    rwa [LinearMap.mem_ker, Finsupp.lapply_apply] at this
  · intro h z
    rw [LinearMap.mem_ker, Finsupp.lapply_apply]
    exact h z.1 z.2

lemma fsi_mem_Flt {x : ι} {f : ι →₀ ℤ} : f ∈ fsiFlt x ↔ ∀ y, x ≤ y → f y = 0 := by
  rw [fsiFlt, Submodule.mem_iInf]
  constructor
  · intro h y hy
    have := h ⟨y, hy⟩
    rwa [LinearMap.mem_ker, Finsupp.lapply_apply] at this
  · intro h z
    rw [LinearMap.mem_ker, Finsupp.lapply_apply]
    exact h z.1 z.2

lemma fsiFlt_le_Fle (x : ι) : fsiFlt x ≤ fsiFle x := by
  intro f hf
  rw [fsi_mem_Fle]
  intro y hy
  rw [fsi_mem_Flt] at hf
  exact hf y (le_of_lt hy)

lemma fsiFle_mono {x y : ι} (h : x ≤ y) : fsiFle x ≤ fsiFle y := by
  intro f hf
  rw [fsi_mem_Fle] at hf ⊢
  intro z hz
  exact hf z (lt_of_le_of_lt h hz)

lemma fsiFlt_mono {x y : ι} (h : x ≤ y) : fsiFlt x ≤ fsiFlt y := by
  intro f hf
  rw [fsi_mem_Flt] at hf ⊢
  intro z hz
  exact hf z (le_trans h hz)

lemma fsiFle_le_Flt_of_lt {x y : ι} (h : x < y) : fsiFle x ≤ fsiFlt y := by
  intro f hf
  rw [fsi_mem_Flt]
  intro z hz
  rw [fsi_mem_Fle] at hf
  exact hf z (lt_of_lt_of_le h hz)

lemma fsiBv_mem_Fle (x : ι) : fsiBv x ∈ fsiFle x := by
  rw [fsi_mem_Fle]
  intro y hy
  rw [fsiBv, Finsupp.single_eq_of_ne (ne_of_gt hy)]

lemma fsiBv_notMem_Flt (x : ι) : fsiBv x ∉ fsiFlt x := by
  rw [fsi_mem_Flt]
  intro h
  have hx := h x le_rfl
  rw [fsiBv, Finsupp.single_eq_same] at hx
  exact one_ne_zero hx

lemma fsiFle_eq (x : ι) : fsiFle x = fsiFlt x ⊔ ℤ ∙ fsiBv x := by
  apply le_antisymm
  · intro f hf
    rw [fsi_mem_Fle] at hf
    rw [Submodule.mem_sup]
    refine ⟨f - f x • fsiBv x, ?_, f x • fsiBv x, ?_, sub_add_cancel _ _⟩
    · rw [fsi_mem_Flt]
      intro y hy
      rw [Finsupp.sub_apply, Finsupp.smul_apply, fsiBv]
      rcases eq_or_lt_of_le hy with h' | h'
      · subst h'
        rw [Finsupp.single_eq_same, smul_eq_mul]
        ring
      · rw [hf y h', Finsupp.single_eq_of_ne (ne_of_gt h'), smul_zero, sub_zero]
    · rw [Submodule.mem_span_singleton]
      exact ⟨f x, rfl⟩
  · refine sup_le (fsiFlt_le_Fle x) ?_
    intro f hf
    rw [Submodule.mem_span_singleton] at hf
    obtain ⟨c, rfl⟩ := hf
    rw [fsi_mem_Fle]
    intro y hy
    rw [Finsupp.smul_apply, fsiBv, Finsupp.single_eq_of_ne (ne_of_gt hy), smul_zero]

lemma fsiFlt_inf_bv_eq_bot (x : ι) : fsiFlt x ⊓ ℤ ∙ fsiBv x = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro f hf
  rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hf
  obtain ⟨hf1, c, rfl⟩ := hf
  rw [fsi_mem_Flt] at hf1
  have hx := hf1 x le_rfl
  rw [Finsupp.smul_apply, fsiBv, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hx
  rw [hx, zero_smul]

section Subgroup

variable (G : Submodule ℤ (ι →₀ ℤ))

/-- The part of `G` supported on the initial segment `≤ x`. -/
def fsiGle (x : ι) : Submodule ℤ (ι →₀ ℤ) := G ⊓ fsiFle x

/-- The part of `G` supported on the initial segment `< x`. -/
def fsiGlt (x : ι) : Submodule ℤ (ι →₀ ℤ) := G ⊓ fsiFlt x

lemma fsi_mem_Gle {x : ι} {g : ι →₀ ℤ} : g ∈ fsiGle G x ↔ g ∈ G ∧ ∀ y, x < y → g y = 0 := by
  rw [fsiGle, Submodule.mem_inf, fsi_mem_Fle]

lemma fsi_mem_Glt {x : ι} {g : ι →₀ ℤ} : g ∈ fsiGlt G x ↔ g ∈ G ∧ ∀ y, x ≤ y → g y = 0 := by
  rw [fsiGlt, Submodule.mem_inf, fsi_mem_Flt]

lemma fsiGlt_le_Gle (x : ι) : fsiGlt G x ≤ fsiGle G x :=
  inf_le_inf_left G (fsiFlt_le_Fle x)

lemma fsiGle_le_Glt {x y : ι} (h : x < y) : fsiGle G x ≤ fsiGlt G y :=
  inf_le_inf_left G (fsiFle_le_Flt_of_lt h)

lemma fsiGle_le_G (x : ι) : fsiGle G x ≤ G := inf_le_left

lemma fsiGlt_le_G (x : ι) : fsiGlt G x ≤ G := inf_le_left

lemma fsiGle_le_Fle (x : ι) : fsiGle G x ≤ fsiFle x := inf_le_right

/-- The `x`-th graded piece of `G`, as a submodule of `ℤ`. -/
def fsiJ (x : ι) : Submodule ℤ ℤ :=
  LinearMap.range ((Finsupp.lapply x).comp (fsiGle G x).subtype)

/-- A generator of the `x`-th graded piece. -/
def fsiGen (x : ι) : ℤ := Submodule.IsPrincipal.generator (fsiJ G x)

/-- An element of `fsiGle G x` whose `x`-th coordinate generates the `x`-th graded piece. -/
def fsiHsel (x : ι) : fsiGle G x :=
  Classical.choose
    (LinearMap.mem_range.mp (Submodule.IsPrincipal.generator_mem (fsiJ G x)))

/-- The chosen element as a vector of `ι →₀ ℤ`. -/
def fsiHvec (x : ι) : ι →₀ ℤ := (fsiHsel G x : ι →₀ ℤ)

lemma fsiHsel_spec (x : ι) : (fsiHvec G x) x = fsiGen G x := by
  have h := Classical.choose_spec
    (LinearMap.mem_range.mp (Submodule.IsPrincipal.generator_mem (fsiJ G x)))
  show (fsiHsel G x : ι →₀ ℤ) x = Submodule.IsPrincipal.generator (fsiJ G x)
  simpa [fsiHsel, fsiJ, LinearMap.comp_apply, Finsupp.lapply_apply] using h

lemma fsiHvec_mem_Gle (x : ι) : fsiHvec G x ∈ fsiGle G x := (fsiHsel G x).2

lemma fsiHvec_mem_G (x : ι) : fsiHvec G x ∈ G := fsiGle_le_G G x (fsiHvec_mem_Gle G x)

/-- **The graded decomposition at level `x`.**  The elements of `G` supported on `≤ x` are exactly
those supported on `< x` together with the multiples of the chosen generator `fsiHvec G x`. -/
lemma fsiGle_eq (x : ι) : fsiGle G x = fsiGlt G x ⊔ ℤ ∙ fsiHvec G x := by
  apply le_antisymm
  · intro g hg
    have hgG : g ∈ G := fsiGle_le_G G x hg
    have hgF : ∀ y, x < y → g y = 0 := fsi_mem_Fle.mp (fsiGle_le_Fle G x hg)
    have hgJ : g x ∈ fsiJ G x := by
      rw [fsiJ, LinearMap.mem_range]
      exact ⟨⟨g, hg⟩, by rw [LinearMap.comp_apply, Finsupp.lapply_apply]; rfl⟩
    rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hgJ
    obtain ⟨c, hc⟩ := hgJ
    rw [Submodule.mem_sup]
    refine ⟨g - c • fsiHvec G x, ?_, c • fsiHvec G x, ?_, sub_add_cancel _ _⟩
    · rw [fsi_mem_Glt]
      refine ⟨Submodule.sub_mem _ hgG (Submodule.smul_mem _ _ (fsiHvec_mem_G G x)), ?_⟩
      intro y hy
      rw [Finsupp.sub_apply, Finsupp.smul_apply]
      rcases eq_or_lt_of_le hy with h' | h'
      · subst h'
        simp only [hc, fsiHsel_spec, fsiGen, smul_eq_mul]
        ring
      · rw [hgF y h', (fsi_mem_Fle.mp (fsiGle_le_Fle G x (fsiHvec_mem_Gle G x))) y h',
          smul_zero, sub_zero]
    · rw [Submodule.mem_span_singleton]
      exact ⟨c, rfl⟩
  · refine sup_le (fsiGlt_le_Gle G x) ?_
    intro g hg
    rw [Submodule.mem_span_singleton] at hg
    obtain ⟨c, rfl⟩ := hg
    rw [fsi_mem_Gle]
    refine ⟨Submodule.smul_mem _ _ (fsiHvec_mem_G G x), fun y hy => ?_⟩
    rw [Finsupp.smul_apply, (fsi_mem_Fle.mp (fsiGle_le_Fle G x (fsiHvec_mem_Gle G x))) y hy,
        smul_zero]

lemma fsiHvec_notMem_Glt (x : ι) (h : fsiGen G x ≠ 0) : fsiHvec G x ∉ fsiGlt G x := by
  intro hg
  rw [fsi_mem_Glt] at hg
  have hx : (fsiHvec G x) x = 0 := hg.2 x le_rfl
  rw [fsiHsel_spec] at hx
  exact h hx

lemma fsi_mem_Gle_max' (g : ι →₀ ℤ) (hg : g ∈ G) (hne : g.support.Nonempty) :
    g ∈ fsiGle G (g.support.max' hne) := by
  rw [fsi_mem_Gle]
  refine ⟨hg, fun y hy => ?_⟩
  by_contra hfy
  have hymem : y ∈ g.support := Finsupp.mem_support_iff.mpr hfy
  exact absurd hy (not_lt.mpr (Finset.le_max' g.support y hymem))

lemma fsi_max'_lt_of_mem_Glt {x : ι} (g : ι →₀ ℤ) (hg : g ∈ fsiGlt G x)
    (hne : g.support.Nonempty) : g.support.max' hne < x := by
  rw [Finset.max'_lt_iff]
  intro y hy
  rw [fsi_mem_Glt] at hg
  by_contra h
  exact Finsupp.mem_support_iff.mp hy (hg.2 y (not_lt.mp h))

/-- The candidate basis of `G`. -/
def fsiS : Set (ι →₀ ℤ) := Set.range (fun x : {x : ι // fsiGen G x ≠ 0} => fsiHvec G x.1)

lemma fsiHvec_mem_S {x : ι} (h : fsiGen G x ≠ 0) : fsiHvec G x ∈ fsiS G := ⟨⟨x, h⟩, rfl⟩

/-- The coordinate functional `G → ℤ` at `y`. -/
def fsiPsi (y : ι) : ↥G →ₗ[ℤ] ℤ := (Finsupp.lapply y).comp (Submodule.subtype G)

lemma fsiPsi_apply (y : ι) (g : ↥G) : fsiPsi G y g = (g : ι →₀ ℤ) y := by
  rw [fsiPsi, LinearMap.comp_apply, Finsupp.lapply_apply]; rfl

/-- **Linearity of the candidate basis.** -/
lemma fsi_linearIndependent :
    LinearIndependent ℤ
      (fun x : {x : ι // fsiGen G x ≠ 0} => (⟨fsiHvec G x.1, fsiHvec_mem_G G x.1⟩ : ↥G)) := by
  rw [linearIndependent_iff]
  intro l hl
  by_contra hne
  have hsupp : l.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (Finsupp.support_eq_empty.mp h)
  have him : (l.support.image (Subtype.val : {x : ι // fsiGen G x ≠ 0} → ι)).Nonempty :=
    hsupp.image (Subtype.val : {x : ι // fsiGen G x ≠ 0} → ι)
  let x₀ : ι := (l.support.image (Subtype.val : {x : ι // fsiGen G x ≠ 0} → ι)).max' him
  have hx₀mem : x₀ ∈ l.support.image (Subtype.val : {x : ι // fsiGen G x ≠ 0} → ι) :=
    Finset.max'_mem _ _
  obtain ⟨i₀, hi₀, hi₀val⟩ := Finset.mem_image.mp hx₀mem
  have hl' : l.support.sum (fun i => l i • (⟨fsiHvec G i.1, fsiHvec_mem_G G i.1⟩ : ↥G)) = 0 := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using hl
  have hcoord : l.support.sum (fun i => l i * ((fsiHvec G i.1) x₀)) = 0 := by
    have h := congrArg (fsiPsi G x₀) hl'
    rw [map_sum, map_zero] at h
    simpa [fsiPsi_apply, Finsupp.smul_apply, smul_eq_mul] using h
  have hsingle : l.support.sum (fun i => l i * ((fsiHvec G i.1) x₀))
      = l i₀ * ((fsiHvec G i₀.1) x₀) := by
    refine Finset.sum_eq_single i₀ ?_ ?_
    · intro i hi hii
      have hle : i.1 ≤ x₀ := Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      have hlt : i.1 < x₀ := by
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (Subtype.ext (h.trans hi₀val.symm)) hii
      rw [(fsi_mem_Fle.mp (fsiGle_le_Fle G i.1 (fsiHvec_mem_Gle G i.1))) x₀ hlt, mul_zero]
    · intro hnot
      rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]
  rw [hsingle, ← hi₀val, fsiHsel_spec] at hcoord
  have hl0 : l i₀ = 0 := by
    rcases mul_eq_zero.mp hcoord with h | h
    · exact h
    · exact absurd h i₀.2
  exact (Finsupp.mem_support_iff.mp hi₀) hl0

/-- **Spanning of the candidate basis.** -/
lemma fsi_G_le_span : G ≤ Submodule.span ℤ (fsiS G) := by
  have key : ∀ x : ι, fsiGle G x ≤ Submodule.span ℤ (fsiS G) := by
    intro x
    refine WellFounded.induction (C := fun y => fsiGle G y ≤ Submodule.span ℤ (fsiS G))
      (wellFounded_lt (α := ι)) x ?_
    intro x ih
    intro g hg
    rw [fsiGle_eq G x] at hg
    rw [Submodule.mem_sup] at hg
    obtain ⟨g1, hg1, g2, hg2, h12⟩ := hg
    have h1 : g1 ∈ Submodule.span ℤ (fsiS G) := by
      by_cases hg1z : g1 = 0
      · rw [hg1z]; exact Submodule.zero_mem _
      · have hne1 : g1.support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          exact hg1z (Finsupp.support_eq_empty.mp h)
        exact ih _ (fsi_max'_lt_of_mem_Glt G g1 hg1 hne1)
          (fsi_mem_Gle_max' G g1 (fsiGlt_le_G G x hg1) hne1)
    have h2 : g2 ∈ Submodule.span ℤ (fsiS G) := by
      rw [Submodule.mem_span_singleton] at hg2
      obtain ⟨c, rfl⟩ := hg2
      by_cases hgen : fsiGen G x = 0
      · by_cases hz : fsiHvec G x = 0
        · rw [hz, smul_zero]; exact Submodule.zero_mem _
        · have hmem : fsiHvec G x ∈ fsiGlt G x := by
            rw [fsi_mem_Glt]
            refine ⟨fsiHvec_mem_G G x, fun y hy => ?_⟩
            rcases eq_or_lt_of_le hy with h' | h'
            · subst h'; rw [fsiHsel_spec, hgen]
            · exact (fsi_mem_Fle.mp (fsiGle_le_Fle G x (fsiHvec_mem_Gle G x))) y h'
          have hne' : (fsiHvec G x).support.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro h
            exact hz (Finsupp.support_eq_empty.mp h)
          exact Submodule.smul_mem _ c
            (ih _ (fsi_max'_lt_of_mem_Glt G _ hmem hne')
              (fsi_mem_Gle_max' G _ (fsiGlt_le_G G x hmem) hne'))
      · exact Submodule.smul_mem _ c (Submodule.subset_span (fsiHvec_mem_S G hgen))
    rw [← h12]
    exact Submodule.add_mem _ h1 h2
  intro g hg
  by_cases h0 : g = 0
  · rw [h0]; exact Submodule.zero_mem _
  · have hne : g.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact h0 (Finsupp.support_eq_empty.mp h)
    exact key _ (fsi_mem_Gle_max' G g hg hne)

end Subgroup

end WellOrdered

/-- **A submodule of a free `ℤ`-module is free.** -/
theorem free_submodule_of_free_finsupp_aux {ι : Type*} (N : Submodule ℤ (ι →₀ ℤ)) :
    Module.Free ℤ ↥N := by
  obtain ⟨lo, hlo⟩ := exists_wellFoundedLT ι
  letI := lo
  haveI := hlo
  let v : {x : ι // fsiGen N x ≠ 0} → ↥N :=
    fun x => ⟨fsiHvec N x.1, fsiHvec_mem_G N x.1⟩
  have hli : LinearIndependent ℤ v := fsi_linearIndependent N
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro y _
    have hy : ((y : ↥N) : ι →₀ ℤ) ∈ Submodule.span ℤ (fsiS N) := fsi_G_le_span N y.2
    have hmap : Submodule.map (Submodule.subtype N) (Submodule.span ℤ (Set.range v))
        = Submodule.span ℤ (fsiS N) := by
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
theorem free_submodule_of_free_int {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Free ℤ M]
    (N : Submodule ℤ M) : Module.Free ℤ ↥N := by
  let e : M ≃ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M →₀ ℤ) := (Module.Free.chooseBasis ℤ M).repr
  let e' : M →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ M →₀ ℤ) := e
  have hfree : Module.Free ℤ ↥(N.map e') := free_submodule_of_free_finsupp_aux _
  let φ : ↥(N.map e') ≃ₗ[ℤ] ↥N :=
    { toFun := fun y => ⟨e.symm (y : _), by
        obtain ⟨x, hx, hxy⟩ := y.2
        have hx' : x = e.symm (y : _) := by
          rw [← hxy]
          exact (e.symm_apply_apply x).symm
        rwa [← hx']⟩
      map_add' := fun a b => by ext1; simp
      map_smul' := fun c a => by ext1; simp
      invFun := fun x => ⟨e (x : M), ⟨(x : M), x.2, rfl⟩⟩
      left_inv := fun y => by ext1; simp
      right_inv := fun x => by ext1; simp }
  exact Module.Free.of_equiv' hfree φ

end

end Work.Cohomology
