import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.GradedHilbDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions and linear-algebra lemmas for the multigraded Hilbert–Serre theorem

This file collects the general (definition-independent) linear algebra used by the induction in
`Submission/Work/BW/hilb_serre_poly.lean`, together with the definitions of the pieces appearing
in the inductive step: the quotient by `X x • ⊤` and the kernel of multiplication by `X x`.
-/

namespace Work.BW

open MvPolynomial
open scoped Pointwise

/-- If `A` is an internal direct sum decomposition of `M` and `B i ≤ A i` for all `i`, then the
images of the `A i` in the quotient by `⨆ i, B i` form an internal direct sum decomposition. -/
theorem isInternal_map_mkQ {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [DecidableEq ι] (A B : ι → Submodule R M) (hBA : ∀ i, B i ≤ A i)
    (hA : DirectSum.IsInternal A) :
    DirectSum.IsInternal (fun i => (A i).map (Submodule.mkQ (⨆ j, B j))) := by
  classical
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hv0
    have hchoice : ∀ i : ι, ∃ a : M, i ∈ s → (a ∈ A i ∧ Submodule.mkQ (⨆ j, B j) a = v i) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨a, ha, hae⟩ := Submodule.mem_map.mp (hv i hi)
        exact ⟨a, fun _ => ⟨ha, hae⟩⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose a ha using hchoice
    have hsum : Submodule.mkQ (⨆ j, B j) (∑ i ∈ s, a i) = 0 := by
      rw [map_sum]
      rw [Finset.sum_congr rfl (fun i hi => (ha i hi).2), hv0]
    have hmem : ∑ i ∈ s, a i ∈ (⨆ j, B j) := by
      have h := LinearMap.mem_ker.mpr hsum
      rwa [Submodule.ker_mkQ] at h
    obtain ⟨f, hfmem, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp B (∑ i ∈ s, a i)).mp hmem
    have hfs : f.sum (fun _ x => x) = ∑ z ∈ f.support, f z := rfl
    have hzero : ∑ z ∈ s ∪ f.support, ((if z ∈ s then a z else 0) - f z) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_mem]
      have h1 : ∑ z ∈ (s ∪ f.support) ∩ s, a z = ∑ z ∈ s, a z := by
        congr 1
        exact Finset.inter_eq_right.mpr Finset.subset_union_left
      have h2 : ∑ z ∈ s ∪ f.support, f z = ∑ z ∈ f.support, f z := by
        refine (Finset.sum_subset (s₁ := f.support) (s₂ := s ∪ f.support)
          Finset.subset_union_right (fun z hz hzn => ?_)).symm
        rwa [Finsupp.notMem_support_iff] at hzn
      rw [h1, h2, ← hfs, hfsum, sub_self]
    have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A).mp hA.submodule_iSupIndep
    have hmemA : ∀ z ∈ s ∪ f.support, ((if z ∈ s then a z else 0) - f z) ∈ A z := by
      intro z _
      by_cases hzs : z ∈ s
      · rw [if_pos hzs]
        exact (A z).sub_mem (ha z hzs).1 (hBA z (hfmem z))
      · rw [if_neg hzs]
        simpa using (A z).neg_mem (hBA z (hfmem z))
    have hkey := hind (s ∪ f.support) (fun z => (if z ∈ s then a z else 0) - f z) hmemA hzero
    intro i hi
    have hzi := hkey i (Finset.mem_union_left _ hi)
    rw [if_pos hi, sub_eq_zero] at hzi
    rw [← (ha i hi).2, hzi]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact Submodule.mem_iSup_of_mem i (hfmem i)
  · rw [← Submodule.map_iSup, hA.submodule_iSup_eq_top, Submodule.map_top, Submodule.range_mkQ]

/-- The kernel of a degree-shifting endomorphism of an internally decomposed module is again
internally decomposed, after shifting the index by a bijection `τ`. -/
theorem isInternal_ker {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [DecidableEq ι] (A : ι → Submodule R M) (hA : DirectSum.IsInternal A)
    (φ : M →ₗ[R] M) (τ : ι ≃ ι) (hφ : ∀ i, A (τ i) ≤ Submodule.comap φ (A i)) :
    DirectSum.IsInternal (fun i => (A (τ i)).comap φ.ker.subtype) := by
  classical
  have hAi : iSupIndep (fun i => A (τ i)) := hA.submodule_iSupIndep.comp τ.injective
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hv0
    rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hAi
    have hvM : ∑ i ∈ s, (v i : M) = 0 := by
      have h := congrArg (fun k : φ.ker => (k : M)) hv0
      simpa [Submodule.coe_sum] using h
    have hmem : ∀ i ∈ s, (v i : M) ∈ A (τ i) := by
      intro i hi
      have hi' := hv i hi
      rw [Submodule.mem_comap] at hi'
      simpa using hi'
    have hzero := hAi s (fun i => (v i : M)) hmem hvM
    intro i hi
    exact Subtype.ext (by simpa using hzero i hi)
  · rw [eq_top_iff]
    intro k _
    have hk : (k : M) ∈ (⨆ i, A (τ i)) := by
      rw [Equiv.iSup_comp (e := τ) (g := A), hA.submodule_iSup_eq_top]
      trivial
    obtain ⟨f, hfmem, hfsum⟩ :=
      (Submodule.mem_iSup_iff_exists_finsupp (fun i => A (τ i)) (k : M)).mp hk
    have hfs : f.sum (fun _ x => x) = ∑ i ∈ f.support, f i := rfl
    have hksum : ∑ i ∈ f.support, f i = (k : M) := by
      rw [← hfs]; exact hfsum
    have hφk : φ (k : M) = 0 := LinearMap.mem_ker.mp k.2
    have hsumφ : ∑ i ∈ f.support, φ (f i) = 0 := by
      rw [← map_sum, hksum, hφk]
    have hkerf : ∀ i ∈ f.support, φ (f i) = 0 :=
      ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A).mp hA.submodule_iSupIndep)
        f.support (fun i => φ (f i)) (fun i hi => hφ i (hfmem i)) hsumφ
    let g : ι → φ.ker := fun i => if h : i ∈ f.support then ⟨f i, hkerf i h⟩ else 0
    have hg_mem : ∀ i ∈ f.support, g i ∈ (⨆ i, (A (τ i)).comap φ.ker.subtype) := by
      intro i hi
      simp only [g, dif_pos hi]
      exact Submodule.mem_iSup_of_mem i (by rw [Submodule.mem_comap]; exact hfmem i)
    have hsum_mem := Submodule.sum_mem (⨆ i, (A (τ i)).comap φ.ker.subtype) hg_mem
    have hk_eq : k = ∑ i ∈ f.support, g i := by
      refine Subtype.ext ?_
      rw [Submodule.coe_sum]
      rw [show (∑ i ∈ f.support, (g i : M)) = ∑ i ∈ f.support, f i from
        Finset.sum_congr rfl (fun i hi => by simp only [g, dif_pos hi])]
      exact hksum.symm
    rw [hk_eq]
    exact hsum_mem

/-- If `B i ≤ A i` for all `i` and the `A i` are independent, then the `i`-th piece is exactly the
part of `A i` lying in the span of all the `B j`. -/
theorem iSupIndep_inf_iSup_eq {ι R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [DecidableEq ι] (A B : ι → Submodule R M) (hB : ∀ i, B i ≤ A i)
    (hA : iSupIndep A) (i : ι) : A i ⊓ (⨆ j, B j) = B i := by
  classical
  refine le_antisymm ?_ (le_inf (hB i) (le_iSup B i))
  intro x hx
  obtain ⟨hxA, hxB⟩ := Submodule.mem_inf.mp hx
  obtain ⟨f, hfmem, hfsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp B x).mp hxB
  have hfs : f.sum (fun _ y => y) = ∑ j ∈ f.support, f j := rfl
  have hsumx : ∑ j ∈ f.support, f j = x := by rw [← hfs]; exact hfsum
  have hsum_f : ∑ j ∈ insert i f.support, f j = x := by
    by_cases hi : i ∈ f.support
    · rw [Finset.insert_eq_of_mem hi]; exact hsumx
    · rw [Finset.sum_insert hi, Finsupp.notMem_support_iff.mp hi, zero_add]; exact hsumx
  have hzero : ∑ j ∈ insert i f.support, ((if j = i then x else 0) - f j) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_insert_self i f.support),
      hsum_f, sub_self]
  have hmemA : ∀ j ∈ insert i f.support, ((if j = i then x else 0) - f j) ∈ A j := by
    intro j _
    by_cases hji : j = i
    · rw [if_pos hji, hji]
      exact (A i).sub_mem hxA (hB i (hfmem i))
    · rw [if_neg hji]
      simpa using (A j).neg_mem (hB j (hfmem j))
  have hkey := ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero A).mp hA) (insert i f.support)
    (fun j => (if j = i then x else 0) - f j) hmemA hzero
  have hi := hkey i (Finset.mem_insert_self i f.support)
  rw [if_pos rfl, sub_eq_zero] at hi
  rw [hi]
  exact hfmem i

/-- In a finite-dimensional module, an internal direct sum decomposition has only finitely many
non-zero pieces. -/
theorem setOf_ne_bot_finite {ι K V : Type*} [DecidableEq ι] [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : ι → Submodule K V) (hA : DirectSum.IsInternal A) :
    {i | A i ≠ ⊥}.Finite := by
  classical
  let b := Module.finBasis K V
  have hb : ∀ v : Fin (Module.finrank K V), (b v) ∈ (⨆ i, A i) := by
    intro v
    rw [hA.submodule_iSup_eq_top]; trivial
  choose s hs using fun v => (Submodule.mem_iSup_iff_exists_finset).mp (hb v)
  let T : Finset ι := Finset.univ.biUnion s
  have hT : ∀ v, s v ⊆ T := fun v =>
    Finset.subset_biUnion_of_mem (s := Finset.univ) (u := s) (Finset.mem_univ v)
  have hspanT : (⨆ i ∈ T, A i) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro v ⟨j, rfl⟩
    exact (SetLike.le_def.mp (biSup_mono (fun i hi => hT j hi))) (hs j)
  have hTbot : ∀ i, i ∉ T → A i = ⊥ := by
    intro i hi
    have h1 : A i ≤ ⨆ j ∈ T, A j := by rw [hspanT]; exact le_top
    have h2 : Disjoint (A i) (⨆ j, ⨆ (_ : j ≠ i), A j) :=
      iSupIndep_def.mp hA.submodule_iSupIndep i
    have h3 : ⨆ j ∈ T, A j ≤ ⨆ j, ⨆ (_ : j ≠ i), A j :=
      biSup_mono (fun j hj hji => hi (hji ▸ hj))
    have h4 : A i ≤ ⊥ := le_trans (le_inf le_rfl (le_trans h1 h3))
      (disjoint_iff_inf_le.mp h2)
    exact bot_unique h4
  exact Set.Finite.subset T.finite_toSet (fun i hi => by
    by_contra hmem
    exact hi (hTbot i hmem))

namespace HilbSerre

/-- The `ℕ`-valued version of a multidegree. -/
noncomputable def toNatF {N : ℕ} (u : Fin (N + 1) →₀ ℤ) : Fin (N + 1) →₀ ℕ :=
  u.mapRange Int.toNat (by simp)

@[simp]
theorem toNatF_apply {N : ℕ} (u : Fin (N + 1) →₀ ℤ) (i : Fin (N + 1)) :
    toNatF u i = (u i).toNat := rfl

/-- `toNatF` is a left inverse to `castF` on non-negative multidegrees. -/
theorem castF_toNatF {N : ℕ} (u : Fin (N + 1) →₀ ℤ) (h : ∀ i, 0 ≤ u i) :
    castF (toNatF u) = u := by
  ext i
  rw [castF_apply, toNatF_apply, Int.toNat_of_nonneg (h i)]

theorem toNatF_castF {N : ℕ} (D : Fin (N + 1) →₀ ℕ) : toNatF (castF D) = D := by
  ext i
  rw [toNatF_apply, castF_apply, Int.toNat_natCast]

/-- The submodule `X x • ⊤` of `M`. -/
noncomputable def Xsub (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
    (x : Fin (N + 1) × Fin 2) : Submodule (MR N) M := (MvPolynomial.X x : MR N) • ⊤

/-- The pieces of the quotient `M ⧸ (X x • ⊤)`. -/
noncomputable def quoPiece (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
    [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
    (x : Fin (N + 1) × Fin 2) (u : Fin (N + 1) →₀ ℤ) : Submodule ℂ (M ⧸ Xsub N M x) :=
  (piece u).map (Submodule.mkQ (Xsub N M x) : M →ₗ[ℂ] (M ⧸ Xsub N M x))

/-- Multiplication by `X x` as an `MR N`-linear endomorphism of `M`. -/
noncomputable def mulX (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
    (x : Fin (N + 1) × Fin 2) : M →ₗ[MR N] M := LinearMap.lsmul (MR N) M (MvPolynomial.X x)

/-- The pieces of the kernel of multiplication by `X x`. -/
noncomputable def kerPiece (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
    [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
    (x : Fin (N + 1) × Fin 2) (u : Fin (N + 1) →₀ ℤ) :
    Submodule ℂ (LinearMap.ker (mulX N M x)) :=
  (piece (u - wZ N x)).comap ((LinearMap.ker (mulX N M x)).subtype : LinearMap.ker (mulX N M x) →ₗ[ℂ] M)

end HilbSerre

end Work.BW
