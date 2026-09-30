import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.prod_pow_mult_comap_fiber
import Submission.Work.BW.finprod_liesOver_pow_fiber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# logHeight_intermediate — heights under field extension; 1–2k lines, low-medium risk

**Claim.** For `F ⊆ K` and `x : ι → F`, `h_K(x) = [K:F]·h_F(x)` (relative projective heights).

**Why it is needed.** `siegel_numberField` must be applied over `F = ℚ(α'₁,…,α'_r)`, not
over `K`:
* `K` may be much larger than `ℚ(α)`;
* `discr K` is uncontrolled;
* BW apply Lemma 1 to `K'`.

The resulting `p` must then be measured in `K`, which is what `aux_poly` states.

**Proof.** Split into infinite and finite places.
* **Infinite places.** The places of `K` above `w` have multiplicities summing to
  `[K:F]·mult(w)`. Mathlib has `InfinitePlace.comap` and `InfinitePlace.sum_mult_eq`.
* **Finite places.** `∑_{P|𝔭} e_P f_P = [K:F]`. Mathlib has `Ideal.sum_ramification_inertia`.
  The local absolute values `|x|_P = |x|_𝔭^{e_P f_P}` in Mathlib's normalisation.
-/

set_option linter.style.haveILetI false

namespace Work.BW

open NumberField IsDedekindDomain

open Classical

variable {K : Type*} [Field K] [NumberField K]

/-! ## Local comparison of places -/

/-- **Local comparison, finite places.** If a finite place `v` of `K` lies above the finite
place `w` of `F ⊆ K`, then on `F` the absolute values are related by
`|a|_v = |a|_w ^ (e_v * f_v)`. -/
lemma finitePlace_apply_of_liesOver (F : IntermediateField ℚ K) (v : FinitePlace K)
    (w : FinitePlace F) (h : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal) (a : F) :
    v (algebraMap F K a) =
      w a ^ (v.maximalIdeal.asIdeal.ramificationIdx (𝓞 F) *
        v.maximalIdeal.asIdeal.inertiaDeg (𝓞 F)) := by
  haveI := h
  have hh := FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap (K := F) (L := K)
    (v := w.maximalIdeal) (w := v.maximalIdeal) a
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply] at hh
  rw [FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding_eq] at hh
  exact hh

/-- **Local comparison, infinite places.** If `v` is an infinite place of `K` restricting to
`w` on `F ⊆ K`, then `v` and `w` agree on `F`. -/
lemma infinitePlace_apply_of_comap_eq (F : IntermediateField ℚ K) {v : InfinitePlace K}
    {w : InfinitePlace F} (h : v.comap (algebraMap F K) = w) (a : F) :
    v (algebraMap F K a) = w a := by
  rw [← h, InfinitePlace.comap_apply]

/-! ## Restricting finite places -/

/-- The finite place of `F` below a finite place of `K`, for `ℚ ⊆ F ⊆ K`. -/
noncomputable def finitePlaceRestrict (F : IntermediateField ℚ K) (v : FinitePlace K) :
    FinitePlace F :=
  FinitePlace.mk (IsDedekindDomain.HeightOneSpectrum.under (𝓞 F) v.maximalIdeal)

lemma maximalIdeal_finitePlaceRestrict (F : IntermediateField ℚ K) (v : FinitePlace K) :
    (finitePlaceRestrict F v).maximalIdeal =
      IsDedekindDomain.HeightOneSpectrum.under (𝓞 F) v.maximalIdeal := by
  rw [finitePlaceRestrict, FinitePlace.maximalIdeal_mk]

lemma liesOver_finitePlaceRestrict (F : IntermediateField ℚ K) (v : FinitePlace K) :
    v.maximalIdeal.asIdeal.LiesOver (finitePlaceRestrict F v).maximalIdeal.asIdeal := by
  rw [maximalIdeal_finitePlaceRestrict]
  exact Ideal.over_under v.maximalIdeal.asIdeal

lemma finitePlaceRestrict_eq_iff (F : IntermediateField ℚ K) (v : FinitePlace K)
    (w : FinitePlace F) :
    finitePlaceRestrict F v = w ↔
      v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := by
  have h : finitePlaceRestrict F v = w ↔
      IsDedekindDomain.HeightOneSpectrum.under (𝓞 F) v.maximalIdeal = w.maximalIdeal := by
    constructor
    · rintro rfl; simp [maximalIdeal_finitePlaceRestrict]
    · intro hh; rw [finitePlaceRestrict, hh, FinitePlace.mk_maximalIdeal]
  rw [h]
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · rw [Ideal.liesOver_iff, ← hh, HeightOneSpectrum.under_asIdeal]
  · rw [Ideal.liesOver_iff, ← HeightOneSpectrum.under_asIdeal] at hh
    exact HeightOneSpectrum.ext_iff.mpr hh.symm

/-! ## Finiteness of the relevant fibres -/

/-- The finite places of `K` above a given finite place of `F` are finite in number. -/
lemma finite_setOf_liesOver_finitePlace (F : IntermediateField ℚ K) (w : FinitePlace F) :
    {v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal}.Finite := by
  haveI : (w.maximalIdeal.asIdeal).IsMaximal :=
    Ideal.IsPrime.isMaximal w.maximalIdeal.isPrime w.maximalIdeal.ne_bot
  have h : ((w.maximalIdeal.asIdeal).primesOver (𝓞 K)).Finite :=
    IsDedekindDomain.primesOver_finite (w.maximalIdeal.asIdeal) (𝓞 K)
  have hpre : {v : FinitePlace K |
      v.maximalIdeal.asIdeal ∈ (w.maximalIdeal.asIdeal).primesOver (𝓞 K)}.Finite :=
    Set.Finite.preimage (fun a _ b _ hab =>
      FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext_iff.mpr hab)) h
  refine hpre.subset fun v hv => ?_
  exact ⟨v.maximalIdeal.isPrime, hv⟩

/-- The support of `w ↦ ⨆ i, w (x i)` on the finite places of a number field is finite. -/
lemma finite_mulSupport_iSup_finitePlace {ι : Type*} [Finite ι] (F : IntermediateField ℚ K)
    {x : ι → F} (hx : x ≠ 0) :
    (Function.mulSupport fun w : FinitePlace F => ⨆ i, w (x i)).Finite := by
  classical
  have hne : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    exact not_not.mp (not_exists.mp h i)
  haveI : Nonempty ι := ⟨hne.choose⟩
  have hsub : Function.mulSupport (fun w : FinitePlace F => ⨆ i, w (x i)) ⊆
      ⋃ i ∈ {i : ι | x i ≠ 0}, Function.mulSupport fun w : FinitePlace F => w (x i) := by
    intro w hw
    simp only [Function.mem_mulSupport] at hw
    obtain ⟨i, hi, hwi⟩ : ∃ i, x i ≠ 0 ∧ w (x i) ≠ 1 := by
      by_contra h
      apply hw
      obtain ⟨i₀, hi₀⟩ := hne
      have hw1 : w (x i₀) = 1 := by
        by_contra hw'
        exact (not_exists.mp h i₀) ⟨hi₀, hw'⟩
      refine le_antisymm (ciSup_le fun j => ?_) ?_
      · by_cases hj : x j = 0
        · rw [hj, map_zero]; norm_num
        · by_contra hwj
          exact (not_exists.mp h j) ⟨hj, (not_le.mp hwj).ne'⟩
      · rw [← hw1]
        exact le_ciSup (f := fun j => w (x j)) (Set.finite_range _).bddAbove i₀
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, by simpa using hwi⟩⟩
  exact (Set.Finite.biUnion (Set.toFinite _) fun i hi =>
    FinitePlace.hasFiniteMulSupport hi).subset hsub

/-! ## Assembly -/

/-- A product over a set containing the support is the product over everything. -/
lemma finprod_mem_eq_finprod_of_mulSupport_subset {α : Type*} {M : Type*} [CommMonoid M]
    {f : α → M} {s : Set α} (h : Function.mulSupport f ⊆ s) :
    ∏ᶠ a ∈ s, f a = ∏ᶠ a, f a := by
  rw [← finprod_mem_mulSupport f, ← finprod_mem_inter_mulSupport f s,
    Set.inter_eq_right.mpr h]

/-- The `iSup` of the values of `v` over the tuple `x` in terms of the restriction `w`. -/
lemma finitePlace_iSup_eq {ι : Type*} [Nonempty ι] (F : IntermediateField ℚ K)
    (v : FinitePlace K) (w : FinitePlace F)
    (h : v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal) (x : ι → F) :
    (⨆ i, v (x i : K)) =
      (⨆ i, w (x i)) ^ (v.maximalIdeal.asIdeal.ramificationIdx (𝓞 F) *
        v.maximalIdeal.asIdeal.inertiaDeg (𝓞 F)) := by
  rw [Real.iSup_pow (f := fun i => w (x i)) (fun i => w.1.nonneg (x i))]
  exact iSup_congr fun i => finitePlace_apply_of_liesOver F v w h (x i)

/-- **The archimedean factor.** -/
lemma arch_factor {ι : Type*} [Finite ι] (F : IntermediateField ℚ K) (x : ι → F)
    (hx : x ≠ 0) :
    (∏ v : InfinitePlace K, (⨆ i, v (x i : K)) ^ v.mult) =
      (∏ w : InfinitePlace F, (⨆ i, w (x i)) ^ w.mult) ^ (Module.finrank F K : ℝ) := by
  classical
  obtain ⟨i₀, _⟩ := Function.ne_iff.mp hx
  haveI : Nonempty ι := ⟨i₀⟩
  have hmain : (∏ v : InfinitePlace K, (⨆ i, v (x i : K)) ^ v.mult) =
      (∏ w : InfinitePlace F, (⨆ i, w (x i)) ^ w.mult) ^ Module.finrank F K := by
    have hdisj : (Set.univ : Set (InfinitePlace F)).PairwiseDisjoint
        fun w => {v : InfinitePlace K | v.comap (algebraMap F K) = w} := by
      intro w _ w' _ hww'
      change Disjoint {v : InfinitePlace K | v.comap (algebraMap F K) = w}
        {v : InfinitePlace K | v.comap (algebraMap F K) = w'}
      rw [Set.disjoint_iff]
      rintro v ⟨hv, hv'⟩
      exact hww' (hv.symm.trans hv')
    have hunion : (⋃ w ∈ (Set.univ : Set (InfinitePlace F)),
        {v : InfinitePlace K | v.comap (algebraMap F K) = w}) = Set.univ := by
      ext v
      exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨v.comap (algebraMap F K),
        Set.mem_iUnion.mpr ⟨trivial, rfl⟩⟩⟩
    have hper : ∀ w ∈ (Set.univ : Set (InfinitePlace F)),
        (∏ᶠ v ∈ {v : InfinitePlace K | v.comap (algebraMap F K) = w},
          (⨆ i, v (x i : K)) ^ v.mult) =
          ((⨆ i, w (x i)) ^ w.mult) ^ Module.finrank F K := by
      intro w _
      refine (finprod_mem_congr rfl fun v hv => ?_).trans
        (prod_pow_mult_comap_fiber F w _)
      congr 1
      exact iSup_congr fun i => infinitePlace_apply_of_comap_eq F hv (x i)
    rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ, ← hunion,
      finprod_mem_biUnion hdisj Set.finite_univ (fun w _ => Set.toFinite _),
      finprod_mem_congr rfl hper, finprod_mem_univ, finprod_eq_prod_of_fintype,
      Finset.prod_pow]
  rw [hmain, Real.rpow_natCast]

/-- **The non-archimedean factor.** -/
lemma nonarch_factor {ι : Type*} [Finite ι] (F : IntermediateField ℚ K) (x : ι → F)
    (hx : x ≠ 0) :
    (∏ᶠ v : FinitePlace K, ⨆ i, v (x i : K)) =
      (∏ᶠ w : FinitePlace F, ⨆ i, w (x i)) ^ (Module.finrank F K : ℝ) := by
  classical
  obtain ⟨i₀, _⟩ := Function.ne_iff.mp hx
  haveI : Nonempty ι := ⟨i₀⟩
  have hBfin : (Function.mulSupport fun w : FinitePlace F => ⨆ i, w (x i)).Finite :=
    finite_mulSupport_iSup_finitePlace F hx
  have hGsub : Function.mulSupport (fun v : FinitePlace K => ⨆ i, v (x i : K)) ⊆
      ⋃ w ∈ (hBfin.toFinset : Set (FinitePlace F)),
        {v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal} := by
    intro v hv
    have hv1 : (⨆ i, v (x i : K)) ≠ 1 := hv
    have hne1 : (⨆ i, (finitePlaceRestrict F v) (x i)) ≠ 1 := by
      intro h
      apply hv1
      rw [finitePlace_iSup_eq F v (finitePlaceRestrict F v)
        (liesOver_finitePlaceRestrict F v) x, h, one_pow]
    exact Set.mem_iUnion.mpr ⟨finitePlaceRestrict F v, Set.mem_iUnion.mpr
      ⟨(Set.Finite.mem_toFinset hBfin).mpr hne1, liesOver_finitePlaceRestrict F v⟩⟩
  have hper : ∀ w ∈ (hBfin.toFinset : Set (FinitePlace F)),
      (∏ᶠ v ∈ {v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal},
        (⨆ i, v (x i : K))) = ((⨆ i, w (x i)) ^ Module.finrank F K) := by
    intro w _
    refine (finprod_mem_congr rfl fun v hv => ?_).trans (finprod_liesOver_pow_fiber F w _)
    exact finitePlace_iSup_eq F v w hv x
  have hB'sub : Function.mulSupport
      (fun w : FinitePlace F => (⨆ i, w (x i)) ^ Module.finrank F K) ⊆
      (hBfin.toFinset : Set (FinitePlace F)) := by
    intro w hw
    simp only [Function.mem_mulSupport] at hw
    rw [Finset.mem_coe, Set.Finite.mem_toFinset hBfin]
    by_contra hw1
    rw [Function.mem_mulSupport] at hw1
    exact hw (by rw [not_not.mp hw1, one_pow])
  have hstep : (∏ᶠ v : FinitePlace K, ⨆ i, v (x i : K)) =
      ∏ᶠ w : FinitePlace F, (⨆ i, w (x i)) ^ Module.finrank F K := by
    have hdisj : (hBfin.toFinset : Set (FinitePlace F)).PairwiseDisjoint
        (fun w => {v : FinitePlace K |
          v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal}) := by
      intro w _ w' _ hww'
      change Disjoint {v : FinitePlace K |
          v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal}
        {v : FinitePlace K | v.maximalIdeal.asIdeal.LiesOver w'.maximalIdeal.asIdeal}
      rw [Set.disjoint_iff]
      rintro v ⟨hv, hv'⟩
      exact hww' (by
        have h1 : w.maximalIdeal.asIdeal = v.maximalIdeal.asIdeal.under (𝓞 F) := hv.over
        have h2 : w'.maximalIdeal.asIdeal = v.maximalIdeal.asIdeal.under (𝓞 F) := hv'.over
        exact FinitePlace.maximalIdeal_injective
          (HeightOneSpectrum.ext_iff.mpr (h1.trans h2.symm)))
    have hbiUnion := finprod_mem_biUnion (f := fun v : FinitePlace K => ⨆ i, v (x i : K))
      (I := (hBfin.toFinset : Set (FinitePlace F)))
      (t := fun w => {v : FinitePlace K |
        v.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal})
      hdisj (hBfin.subset fun x hx => (Set.Finite.mem_toFinset hBfin).mp hx)
      (fun w _ => finite_setOf_liesOver_finitePlace F w)
    rw [← finprod_mem_eq_finprod_of_mulSupport_subset hGsub, hbiUnion,
      finprod_mem_congr rfl hper, finprod_mem_eq_finprod_of_mulSupport_subset hB'sub]
  rw [hstep, Real.rpow_natCast, ← finprod_pow hBfin]

/-! ## The main theorem -/

/-- Relative projective heights scale by the degree under field extension:
`h_K(x) = [K:F] · h_F(x)` for `x ∈ Fⁿ`, `F ⊆ K` an intermediate field. -/
theorem logHeight_intermediate {K : Type*} [Field K] [NumberField K]
    (F : IntermediateField ℚ K) {ι : Type*} [Finite ι] (x : ι → F) :
    Height.logHeight (fun i => (x i : K)) = (Module.finrank F K : ℝ) * Height.logHeight x := by
  classical
  suffices hmul : Height.mulHeight (fun i => (x i : K)) =
      Height.mulHeight x ^ (Module.finrank F K : ℝ) by
    rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight, hmul,
      Real.log_rpow (Height.mulHeight_pos x)]
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp
  · have hy : (fun i => (x i : K)) ≠ 0 := by
      intro h
      apply hx
      funext i
      have hi : algebraMap F K (x i) = 0 := congrFun h i
      rwa [FaithfulSMul.algebraMap_eq_zero_iff] at hi
    have hA : 0 ≤ ∏ w : InfinitePlace F, (⨆ i, w (x i)) ^ w.mult :=
      Finset.prod_nonneg fun w _ =>
        pow_nonneg (Real.iSup_nonneg fun i => w.1.nonneg (x i)) _
    have hB : 0 ≤ ∏ᶠ w : FinitePlace F, ⨆ i, w (x i) :=
      finprod_nonneg fun w => Real.iSup_nonneg fun i => w.1.nonneg (x i)
    rw [NumberField.mulHeight_eq hy, NumberField.mulHeight_eq hx, arch_factor F x hx,
      nonarch_factor F x hx, ← Real.mul_rpow hA hB]

end Work.BW
