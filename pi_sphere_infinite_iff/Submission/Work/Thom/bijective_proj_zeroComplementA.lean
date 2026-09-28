import Mathlib
import Submission.Work.Thom.subsingleton_PieceCoh_genFibre
import Submission.Work.Cohomology.subsingleton_pdCohSub_union_clean
import Submission.Work.Cohomology.pdCohSub_iUnion_of_wf
import Submission.Work.Thom.Gysin

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The Gysin descent `pi^* : H^k(B;Z) = H^k(E \ 0;Z)`, island-clean copy

`Work.Thom.bijective_proj_zeroComplement_gen` proves the bijectivity of
`pi^* : H^k(B;Z) -> H^k(E \ 0;Z)` for `k + 2 <= n` and an arbitrary finite-dimensional real fibre,
but its module lies in the import island of `Submission.Work.Cohomology.subsingleton_pdCohSub_union`
(via `subsingleton_PieceCohA`), which cannot be imported together with the island of
`Submission.Work.Thom.thomClass_of_finite_cover` (the duplicate `Work.Cohomology.Yt`).  The
Chern-class recursion needs **both** the descent and the finite-cover Thom class, so this module
re-proves the descent against the island-clean union step
`Work.Cohomology.subsingleton_pdCohSub_union_clean`.

* `Work.Thom.subsingleton_pdCoh_of_subsingleton_pdCohSub_univA` — transport of vanishing from the
  piece over all of `X` to the pair `(X,A)`;
* `Work.Thom.subsingleton_OpenThom_genFibreA` — `H^m(E,E∖0;Z) = 0` for `m < finrank ℝ F` for an
  arbitrary finite-dimensional fibre and an arbitrary cover (transfinite induction);
* `Work.Thom.bijective_proj_zeroComplementA` — the descent.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The relative cohomology of the pair `(X,A)` from the piece over all of `X`.** -/
theorem subsingleton_pdCoh_of_subsingleton_pdCohSub_univA {X : Type} [TopologicalSpace X]
    (A : Set X) (k : ℕ)
    (h : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A Set.univ k)) :
    Subsingleton (Work.Cohomology.pdCoh (TopCat.of X) A k) := by
  let e : ↥(Set.univ : Set X) ≃ₜ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Set.mem_univ x⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun x => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  obtain ⟨iso⟩ := Work.Cohomology.relCohomology_homeomorph_pairs
    {y : ↥(Set.univ : Set X) | (y : X) ∈ A} A e (fun _ => Iff.rfl) k
  exact Work.Cohomology.subsingleton_of_iso iso h

/-- Global low-degree vanishing of the Thom pair of a real bundle with an arbitrary
finite-dimensional fibre: `H^m(E, E∖0; ℤ) = 0` for `m < finrank ℝ F`.  (Island-clean copy of
`Work.Thom.subsingleton_OpenThom_genFibre`.) -/
theorem subsingleton_OpenThom_genFibreA {B : Type} [TopologicalSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} (Z : RealBundle B F ι) (m : ℕ)
    (hm : m < Module.finrank ℝ F) :
    Subsingleton (OpenThom Z m) := by
  classical
  obtain ⟨inst, hwf⟩ := exists_wellFoundedLT ι
  letI : LinearOrder ι := inst
  haveI : WellFoundedLT ι := hwf
  let Q : ι → Set B := fun i => ⋃ β ≤ i, Z.baseSet β
  let P : ι → Set B := fun i => ⋃ β < i, Z.baseSet β
  let Cov : ι → Set Z.TotalSpace := fun i => Z.proj ⁻¹' (Q i)
  have hQP : ∀ i, Q i = P i ∪ Z.baseSet i := by
    intro i
    ext x
    simp only [Q, P, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hx⟩
      rcases lt_or_eq_of_le hβ with h | h
      · exact Or.inl ⟨β, h, hx⟩
      · exact Or.inr (h ▸ hx)
    · rintro (⟨β, hβ, hx⟩ | hx)
      · exact ⟨β, le_of_lt hβ, hx⟩
      · exact ⟨i, le_rfl, hx⟩
  have hPQ : ∀ i, P i = ⋃ β < i, Q β := by
    intro i
    ext x
    simp only [P, Q, Set.mem_iUnion]
    constructor
    · rintro ⟨β, hβ, hx⟩
      exact ⟨β, hβ, β, le_rfl, hx⟩
    · rintro ⟨β, hβ, γ, hγ, hx⟩
      exact ⟨γ, lt_of_le_of_lt hγ hβ, hx⟩
  have hCovopen : ∀ i, IsOpen (Cov i) := by
    intro i
    exact (isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≤ i => Z.isOpen_baseSet β).preimage
      Z.continuous_proj
  have hCovmono : Monotone Cov := by
    intro i j hij x hx
    simp only [Cov, Q, Set.mem_preimage, Set.mem_iUnion] at hx ⊢
    obtain ⟨β, hβ, hx⟩ := hx
    exact ⟨β, le_trans hβ hij, hx⟩
  have key : ∀ i : ι, ∀ j ≤ m,
      Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Cov i) j) := by
    intro i
    refine WellFoundedLT.induction (motive := fun i : ι => ∀ j ≤ m,
      Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace) (zeroComplement Z)
        (Cov i) j)) i ?_
    intro i ih j hj
    have hPQ2 : (⋃ k : ↥(Set.Iio i), Q k.1) = P i := by
      ext x
      simp only [P, Q, Set.mem_iUnion]
      constructor
      · rintro ⟨k, β, hβ, hx⟩
        exact ⟨β, lt_of_le_of_lt hβ k.2, hx⟩
      · rintro ⟨β, hβ, hx⟩
        exact ⟨⟨β, hβ⟩, β, le_rfl, hx⟩
    have hprev_eq : (⋃ k : ↥(Set.Iio i), Cov k.1) = Z.proj ⁻¹' (P i) := by
      have h1 : (⋃ k : ↥(Set.Iio i), Cov k.1)
          = ⋃ k : ↥(Set.Iio i), Z.proj ⁻¹' (Q k.1) := rfl
      rw [h1, ← Set.preimage_iUnion, hPQ2]
    have hlim := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf (zeroComplement Z)
      (fun k : ↥(Set.Iio i) => Cov k.1) (fun k => hCovopen k.1)
      (fun a b hab => hCovmono hab) m (fun k j hj => ih k.1 k.2 j hj)
    have hUj : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
        (zeroComplement Z) (Z.proj ⁻¹' (P i)) j) := hprev_eq ▸ hlim j hj
    refine Work.Cohomology.subsingleton_pdCohSub_union_clean (zeroComplement Z)
      (W := Cov i) (U := Z.proj ⁻¹' (P i)) (V := Z.proj ⁻¹' (Z.baseSet i))
      (hCovopen i) ?_ ?_ ?_ ?_ ?_ j hUj ?_ ?_
    · exact (isOpen_iUnion fun β => isOpen_iUnion fun _ : β < i => Z.isOpen_baseSet β).preimage
        Z.continuous_proj
    · exact (Z.isOpen_baseSet i).preimage Z.continuous_proj
    · refine Set.preimage_mono fun x hx => ?_
      simp only [P, Q, Set.mem_iUnion] at hx ⊢
      obtain ⟨β, hβ, hx⟩ := hx
      exact ⟨β, le_of_lt hβ, hx⟩
    · refine Set.preimage_mono fun x hx => ?_
      simp only [Q, Set.mem_iUnion]
      exact ⟨i, le_rfl, hx⟩
    · rw [← Set.preimage_union, ← hQP i]
    · haveI : Inhabited ι := ⟨i⟩
      exact subsingleton_PieceCoh_genFibre Z i (fun _ hx => hx) (by omega)
    · intro e he
      haveI : Inhabited ι := ⟨i⟩
      have hen : e < Module.finrank ℝ F := by omega
      have h1 : Subsingleton (PieceCoh Z (P i ∩ Z.baseSet i) e) :=
        subsingleton_PieceCoh_genFibre Z i (fun x hx => hx.2) hen
      simpa only [Set.preimage_inter, PieceCoh] using h1
  have huniv : (⋃ i : ι, Cov i) = Set.univ := by
    have hQB : (⋃ i : ι, Q i) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      refine Set.mem_iUnion.mpr ⟨Z.indexAt x, ?_⟩
      simp only [Q, Set.mem_iUnion] at *
      exact ⟨Z.indexAt x, le_rfl, Z.mem_baseSet_at x⟩
    have h1 : (⋃ i : ι, Cov i) = Z.proj ⁻¹' (⋃ i : ι, Q i) := (Set.preimage_iUnion).symm
    rw [h1, hQB, Set.preimage_univ]
  have hfin := Work.Cohomology.subsingleton_pdCohSub_iUnion_of_wf (zeroComplement Z) Cov
    hCovopen hCovmono m (fun i j hj => key i j hj)
  have hsub : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
      (zeroComplement Z) Set.univ m) := huniv ▸ hfin m le_rfl
  exact subsingleton_pdCoh_of_subsingleton_pdCohSub_univA (zeroComplement Z) m hsub

/-- **The Gysin descent**, island-clean copy of `Work.Thom.bijective_proj_zeroComplement_gen`:
for a real bundle `Z` of rank `n` with an arbitrary finite-dimensional fibre and a Thom class `T`,
the pullback `pi^* : H^k(B;Z) -> H^k(E∖0;Z)` along the projection of the sphere bundle is bijective
whenever `k + 2 ≤ n`. -/
theorem bijective_proj_zeroComplementA
    {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {ι : Type} {n k : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (hF : Module.finrank ℝ F = n)
    (T : Work.Thom.ThomClass Z n) (hk : k + 2 ≤ n) :
    Function.Bijective
      ((Work.Thom.CohMap ((Work.Thom.bundleProj Z).comp
        (Work.Thom.subtypeMap (Work.Thom.zeroComplement Z))) ℤ k).hom) := by
  have hcomp : (CohMap ((bundleProj Z).comp (subtypeMap (zeroComplement Z))) ℤ k).hom
      = gysinπ Z k := by
    rw [CohMap_comp (subtypeMap (zeroComplement Z)) (bundleProj Z) ℤ k]
    rfl
  rw [hcomp]
  have hπ := bijective_CohMap_bundleProj Z k
  have hrel : (relToAbs ℤ (zeroComplement Z) k).hom = 0 := by
    haveI : Subsingleton (OpenThom Z k) :=
      subsingleton_OpenThom_genFibreA Z k (by omega)
    refine LinearMap.ext fun x => ?_
    have hx : x = 0 := Subsingleton.elim x 0
    show (relToAbs ℤ (zeroComplement Z) k).hom x = 0
    rw [hx]
    exact map_zero _
  have hδ : (pairδC (zeroComplement Z) k).hom = 0 := by
    haveI : Subsingleton (OpenThom Z (k + 1)) :=
      subsingleton_OpenThom_genFibreA Z (k + 1) (by omega)
    refine LinearMap.ext fun x => ?_
    exact Subsingleton.elim _ _
  constructor
  · intro x y hxy
    have h1 : gysinπ Z k (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1' : (restrCoh (zeroComplement Z) ℤ k).hom
        ((CohMap (bundleProj Z) ℤ k).hom (x - y)) = 0 := h1
    have h3 : (CohMap (bundleProj Z) ℤ k).hom (x - y) ∈
        (relToAbs ℤ (zeroComplement Z) k).hom.range := by
      rw [pairRange_eq_ker₂ (zeroComplement Z) k]
      exact h1'
    rw [hrel, LinearMap.range_zero] at h3
    have h4 : (CohMap (bundleProj Z) ℤ k).hom (x - y) = 0 := by simpa using h3
    exact sub_eq_zero.mp (hπ.1 (by rw [h4, map_zero]))
  · intro y
    have hy : y ∈ (restrCoh (zeroComplement Z) ℤ k).hom.range := by
      rw [pairRange_eq_ker₃ (zeroComplement Z) k, hδ, LinearMap.ker_zero]
      exact Submodule.mem_top
    obtain ⟨w, hw⟩ := hy
    obtain ⟨z, hz⟩ := hπ.2 w
    exact ⟨z, by
      show (restrCoh (zeroComplement Z) ℤ k).hom
        ((CohMap (bundleProj Z) ℤ k).hom z) = y
      rw [hz, hw]⟩

end

end Work.Thom
