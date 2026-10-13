import Mathlib
import Submission.Work.DSNORM.Defs

/-!
# The chosen parameters of a regular local ring form a regular sequence

The main result of this file is `Work.DSNORM.params_regularSequence`: for a regular local ring `A`,
the family `Work.DSNORM.params A` — a family generating the maximal ideal with exactly
`(maximalIdeal A).spanFinrank = ringKrullDim A` elements — is a (weakly) regular sequence.

The proof is by induction on `(maximalIdeal A).spanFinrank`, using the classical fact that the
quotient of a regular local ring by a minimal generator of its maximal ideal is again regular local,
of dimension (and embedding dimension) one less. The auxiliary statements (all in the namespace
`Work.DSNORM.ParamsRS`) are:

* `notMem_mul_of_minimal_generators`: no element of a minimal generating family of an ideal `I`
  lies in `𝔪 * I` (Nakayama).
* `quotient_span_isRegularLocalRing`: the quotient by a minimal generator of `𝔪` is regular local
  and its embedding dimension drops by one.
* `span_range_succ_eq_maximalIdeal_quotient`: the images of the remaining generators generate the
  maximal ideal of the quotient.
* `isWeaklyRegular_of_span_eq_maximalIdeal`: the general induction statement.
-/

noncomputable section

set_option linter.style.haveILetI false

open RingTheory

namespace Work.DSNORM

universe u

/-! Auxiliary lemmas for the proof of `Work.DSNORM.params_regularSequence`.  They are placed in a
dedicated namespace so that they cannot collide with the (independently developed) lemmas of the
area DSNORM that carry similar names. -/

namespace ParamsRS

/-! ## A minimal generator is not in `𝔪 ^ 2` -/

/-- **Nakayama.** Let `f : Fin n → R` be a family of `n` elements generating an ideal `I` of a local
ring `R`, where `n` is the minimal number `μ(I) = I.spanFinrank` of generators of `I`. Then no
`f i` lies in `𝔪 * I`. (Here `I = 𝔪`, which is the only case used below.) -/
theorem notMem_mul_of_minimal_generators {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (f : Fin n → R) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal R)
    (hn : (IsLocalRing.maximalIdeal R).spanFinrank = n) (i : Fin n) :
    f i ∉ IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R := by
  intro hin
  classical
  set s : Finset R := Finset.univ.image f with hs
  have hspan_s : Ideal.span ((s : Finset R) : Set R) = IsLocalRing.maximalIdeal R := by
    rw [hs, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hf
  have hmem : f i ∈ s := by
    rw [hs]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hfi_mem : f i ∈ IsLocalRing.maximalIdeal R :=
    hf ▸ Submodule.subset_span (Set.mem_range_self i)
  have hspan_le : Ideal.span {f i} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr hfi_mem
  set J : Ideal R := Ideal.span (((s.erase (f i)) : Finset R) : Set R) with hJ
  -- `𝔪` is spanned by `J` together with `f i`
  have h𝔪 : IsLocalRing.maximalIdeal R = J ⊔ Ideal.span {f i} := by
    refine le_antisymm ?_ ?_
    · rw [← hspan_s]
      refine Submodule.span_le.mpr ?_
      rintro y hy
      rw [Finset.mem_coe] at hy
      rcases eq_or_ne y (f i) with rfl | hne
      · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
      · refine Submodule.mem_sup_left ?_
        rw [hJ]
        refine Submodule.subset_span ?_
        rw [Finset.mem_coe, Finset.mem_erase]
        exact ⟨hne, hy⟩
    · refine sup_le ?_ ?_
      · rw [hJ]
        refine Submodule.span_le.mpr ?_
        rintro y hy
        rw [Finset.mem_coe] at hy
        rw [← hspan_s]
        exact Submodule.subset_span (Finset.mem_of_mem_erase hy)
      · rw [Ideal.span_singleton_le_iff_mem]; exact hfi_mem
  -- `𝔪 * 𝔪 ≤ J ⊔ (f i) * 𝔪`
  have hle : IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R ≤
      J ⊔ Ideal.span {f i} * IsLocalRing.maximalIdeal R := by
    refine Submodule.mul_le.mpr ?_
    intro a ha b hb
    rw [h𝔪] at ha hb
    obtain ⟨ja, hja, sa, hsa, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨jb, hjb, sb, hsb, rfl⟩ := Submodule.mem_sup.mp hb
    rw [add_mul, mul_add, mul_add]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.add_mem _ ?_ ?_)
    · exact Submodule.mem_sup_left (Ideal.mul_mem_left J ja hjb)
    · exact Submodule.mem_sup_left (Ideal.mul_mem_right sb J hja)
    · exact Submodule.mem_sup_left (Ideal.mul_mem_left J sa hjb)
    · exact Submodule.mem_sup_right
        (Ideal.mul_mem_mul hsa (hspan_le hsb))
  obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp (hle hin)
  obtain ⟨d, hd, hd_eq⟩ := Ideal.mem_span_singleton_mul.mp hz
  rw [← hd_eq] at hjz
  -- `(1 - d) * f i = j`
  have hunit : IsUnit (1 - d) := by
    refine IsLocalRing.notMem_maximalIdeal.mp ?_
    intro hmem1
    have h1not : (1 : R) ∉ IsLocalRing.maximalIdeal R :=
      IsLocalRing.notMem_maximalIdeal.mpr isUnit_one
    exact h1not (by simpa using Ideal.add_mem _ hmem1 hd)
  have h2 : (1 - d) * f i = j := by
    rw [sub_mul, one_mul, mul_comm d (f i)]
    exact sub_eq_iff_eq_add.mpr hjz.symm
  obtain ⟨u, hu⟩ := hunit
  have h2' : (u : R) * f i = j := by rwa [← hu] at h2
  have hfi_J : f i ∈ J := by
    have h4 : f i = (↑u⁻¹ : R) * j := by
      rw [← h2', ← mul_assoc, Units.inv_mul, one_mul]
    rw [h4]
    exact Ideal.mul_mem_left J _ hj
  -- hence `J = 𝔪`, contradicting the minimality of `f`
  have hJ_eq : J = IsLocalRing.maximalIdeal R := by
    rw [h𝔪]
    exact le_antisymm le_sup_left
      (sup_le le_rfl (Ideal.span_singleton_le_iff_mem _ |>.mpr hfi_J))
  have hfin : (IsLocalRing.maximalIdeal R).spanFinrank ≤ (s.erase (f i)).card := by
    rw [← hJ_eq, hJ]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
      (s := (((s.erase (f i)) : Finset R) : Set R)) (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    exact h
  have hcard : (s.erase (f i)).card ≤ n - 1 := by
    have h1 : s.card ≤ n := by
      rw [hs]
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := f)
    rw [Finset.card_erase_of_mem hmem]
    omega
  have hi : (i : ℕ) < n := i.isLt
  omega

/-! ## The quotient by a minimal generator is regular local -/

/-- **Quotient of a regular local ring by a minimal generator.** If `x ∈ 𝔪 \ 𝔪²`, then
`A ⧸ (x)` is again a regular local ring, and its embedding dimension is one less than that of
`A`. -/
theorem quotient_span_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A) (hx2 : x ∉ IsLocalRing.maximalIdeal A ^ 2)
    [Nontrivial (A ⧸ Ideal.span {x})] :
    IsRegularLocalRing (A ⧸ Ideal.span {x}) ∧
      (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank + 1
        = (IsLocalRing.maximalIdeal A).spanFinrank := by
  have hm : IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})
      = (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x})) :=
    Work.DSREG.maximalIdeal_quotient_span_singleton A x
  -- the maximal ideal needs one fewer generator
  have hdrop : (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank
      ≤ (IsLocalRing.maximalIdeal A).spanFinrank - 1 := by
    rw [hm]
    exact Work.DSREG.SpanFinrankQuotient.spanFinrank_maximalIdeal_quotient_span_le
      A x hx hx2 _ (by omega)
  -- `𝔪 ≠ ⊥`
  have ha_pos : 1 ≤ (IsLocalRing.maximalIdeal A).spanFinrank := by
    rcases Nat.eq_zero_or_pos (IsLocalRing.maximalIdeal A).spanFinrank with h | h
    · exfalso
      have hbot : IsLocalRing.maximalIdeal A = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (Ideal.fg_of_isNoetherianRing _)).mp h
      have hx0 : x = 0 := by simpa [hbot] using hx
      exact hx2 (hx0.symm ▸ Submodule.zero_mem _)
    · exact h
  -- the dimension drops by at most one
  have hA : (((IsLocalRing.maximalIdeal A).spanFinrank : ℕ) : WithBot ℕ∞)
      ≤ ringKrullDim (A ⧸ Ideal.span {x}) + 1 := by
    have h := Work.DSREG.ringKrullDim_le_quotient_span_add_one A x hx
    rwa [Work.DSREG.ringKrullDim_eq_spanFinrank_maximalIdeal_of_isRegularLocalRing A] at h
  have hle_sub : (((IsLocalRing.maximalIdeal A).spanFinrank - 1 : ℕ) : WithBot ℕ∞)
      ≤ ringKrullDim (A ⧸ Ideal.span {x}) := by
    refine Work.DSREG.natCast_le_of_succ_le_add_one (n := _ - 1) ?_
    simpa [Nat.sub_add_cancel ha_pos] using hA
  have hdim_le : ringKrullDim (A ⧸ Ideal.span {x})
      ≤ ((IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ Ideal.span {x})
  have hdim_ge : ((IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
      ≤ ringKrullDim (A ⧸ Ideal.span {x}) :=
    le_trans (by exact_mod_cast hdrop) hle_sub
  have hdim : ringKrullDim (A ⧸ Ideal.span {x})
      = ((IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    le_antisymm hdim_le hdim_ge
  refine ⟨?_, ?_⟩
  · exact (isRegularLocalRing_iff (A ⧸ Ideal.span {x})).mpr hdim.symm
  · have hb_ge : (IsLocalRing.maximalIdeal A).spanFinrank - 1
        ≤ (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank := by
      have h := hle_sub
      rw [hdim] at h
      exact_mod_cast h
    have hb_eq : (IsLocalRing.maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank
        = (IsLocalRing.maximalIdeal A).spanFinrank - 1 := le_antisymm hdrop hb_ge
    omega

/-! ## The remaining generators generate the maximal ideal of the quotient -/

/-- If `f : Fin (n+1) → R` generates `𝔪`, then the images of `f 1, …, f n` in `R ⧸ (f 0)` generate
the maximal ideal of the quotient. -/
theorem span_range_succ_eq_maximalIdeal_quotient {R : Type*} [CommRing R] [IsLocalRing R]
    {n : ℕ} (f : Fin (n + 1) → R) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal R)
    [Nontrivial (R ⧸ Ideal.span {f 0})] :
    Ideal.span (Set.range (fun i : Fin n => Ideal.Quotient.mk (Ideal.span {f 0}) (f i.succ)))
      = IsLocalRing.maximalIdeal (R ⧸ Ideal.span {f 0}) := by
  rw [Work.DSREG.maximalIdeal_quotient_span_singleton R (f 0), ← hf, Ideal.map_span]
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨l, rfl⟩
    exact Submodule.subset_span ⟨f l.succ, ⟨l.succ, rfl⟩, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨x, ⟨j, rfl⟩, rfl⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
    · rw [show Ideal.Quotient.mk (Ideal.span {f 0}) (f 0) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.subset_span (Set.mem_singleton _))]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨l, rfl⟩

/-! ## The induction -/

/-- **Any minimal generating family of the maximal ideal of a regular local ring is a regular
sequence.** -/
theorem isWeaklyRegular_of_span_eq_maximalIdeal :
    ∀ (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = d →
      ∀ (f : Fin d → R), Ideal.span (Set.range f) = IsLocalRing.maximalIdeal R →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  intro d
  induction d with
  | zero =>
    intro R _ _ _ f _
    rw [List.ofFn_zero]
    exact RingTheory.Sequence.IsWeaklyRegular.nil R R
  | succ k ih =>
    intro R _ _ hcard f hf
    haveI : IsDomain R := Work.DSREG.isDomain_of_isRegularLocalRing R
    have hmem : f 0 ∈ IsLocalRing.maximalIdeal R :=
      hf ▸ Submodule.subset_span (Set.mem_range_self 0)
    have hx2 : f 0 ∉ IsLocalRing.maximalIdeal R ^ 2 := by
      rw [pow_two]
      exact notMem_mul_of_minimal_generators f hf hcard 0
    have hne : f 0 ≠ 0 := fun h => hx2 (h.symm ▸ Submodule.zero_mem _)
    haveI : Nontrivial (R ⧸ Ideal.span {f 0}) :=
      Work.DSREG.nontrivial_quotient_span_singleton hmem
    obtain ⟨hregS, hspanS⟩ := quotient_span_isRegularLocalRing R hmem hx2
    haveI : IsRegularLocalRing (R ⧸ Ideal.span {f 0}) := hregS
    have hcardS : (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {f 0})).spanFinrank = k := by
      omega
    set g : Fin k → (R ⧸ Ideal.span {f 0}) :=
      fun i => Ideal.Quotient.mk (Ideal.span {f 0}) (f i.succ) with hg
    have hgspan : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal (R ⧸ Ideal.span {f 0}) := by
      rw [hg]
      exact span_range_succ_eq_maximalIdeal_quotient f hf
    have hIH : RingTheory.Sequence.IsWeaklyRegular (R ⧸ Ideal.span {f 0}) (List.ofFn g) :=
      ih _ hcardS g hgspan
    rw [List.ofFn_succ, RingTheory.Sequence.isWeaklyRegular_cons_iff]
    refine ⟨?_, ?_⟩
    · -- `f 0` is a nonzerodivisor
      intro y z hyz
      have hyz' : f 0 * y = f 0 * z := hyz
      have hy : f 0 * (y - z) = 0 := by rw [mul_sub, hyz', sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hne)
    · -- the tail is weakly regular on the quotient
      have h_list : List.ofFn g
          = (List.ofFn (fun i : Fin k => f i.succ)).map
              (algebraMap R (R ⧸ Ideal.span {f 0})) := by
        rw [List.map_ofFn, Ideal.Quotient.algebraMap_eq]
        rfl
      have hmap : RingTheory.Sequence.IsWeaklyRegular (R ⧸ Ideal.span {f 0})
            (List.ofFn (fun i : Fin k => f i.succ)) ↔
          RingTheory.Sequence.IsWeaklyRegular (R ⧸ Ideal.span {f 0}) (List.ofFn g) := by
        rw [h_list]
        exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {f 0})
          (R ⧸ Ideal.span {f 0}) (List.ofFn (fun i : Fin k => f i.succ))).symm
      have hiso : RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop (f 0) R)
            (List.ofFn (fun i : Fin k => f i.succ)) ↔
          RingTheory.Sequence.IsWeaklyRegular (R ⧸ Ideal.span {f 0})
            (List.ofFn (fun i : Fin k => f i.succ)) :=
        ((QuotSMulTop.equivQuotTensor (f 0) R).trans
          (TensorProduct.rid R (R ⧸ Ideal.span {f 0}))).isWeaklyRegular_congr _
      rw [hiso, hmap]
      exact hIH

end ParamsRS

/-- **The parameters of a regular local ring form a regular sequence.** -/
theorem params_regularSequence (A : Type*) [CommRing A] [IsRegularLocalRing A] :
    RingTheory.Sequence.IsWeaklyRegular A (List.ofFn (Work.DSNORM.params A)) :=
  ParamsRS.isWeaklyRegular_of_span_eq_maximalIdeal (nParams A) A rfl (params A) (params_span A)

end Work.DSNORM
