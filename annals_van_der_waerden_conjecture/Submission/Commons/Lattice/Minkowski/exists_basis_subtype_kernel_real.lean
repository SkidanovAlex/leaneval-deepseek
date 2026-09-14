import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Lattice.Module.basis_extension_pure_rank
import Submission.Commons.Lattice.Module.exists_basis_subtype_kernel

open Module Submodule
open scoped BigOperators

noncomputable section

set_option linter.style.haveILetI false

namespace Commons.Lattice.Minkowski

/-- The `ℝ`-linear map `x ↦ (l ↦ ∑ i, A l i * x i)`, viewed as a map into `EuclideanSpace ℝ ι`. -/
def AhatMap {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ) :
    (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp A.mulVecLin

@[simp]
lemma AhatMap_ofLp {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ)
    (x : Fin N → ℝ) :
    (AhatMap A x).ofLp = A.mulVec x := by
  simp [AhatMap, WithLp.coe_symm_linearEquiv]

lemma AhatMap_apply {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ)
    (x : Fin N → ℝ) (l : ι) :
    (AhatMap A x) l = ∑ i, A l i * x i := by
  simp [Matrix.mulVec, dotProduct, AhatMap_ofLp]

/-- The `ℤ`-linear map `x ↦ (l ↦ ∑ i, A l i * (x i : ℝ))`. -/
def AhatZMap {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ) :
    (Fin N → ℤ) →ₗ[ℤ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun l => ∑ i, A l i * (x i : ℝ))
  map_add' x y := by
    rw [WithLp.ext_iff]
    funext l
    simp only [WithLp.ofLp_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  map_smul' c x := by
    rw [WithLp.ext_iff]
    funext l
    simp only [WithLp.ofLp_smul, Pi.smul_apply]
    rw [zsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RingHom.id_apply, zsmul_eq_mul]
    push_cast
    ring

@[simp]
lemma AhatZMap_ofLp {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ)
    (x : Fin N → ℤ) :
    (AhatZMap A x).ofLp = fun l => ∑ i, A l i * (x i : ℝ) := rfl

lemma AhatZMap_apply {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ)
    (x : Fin N → ℤ) (l : ι) :
    (AhatZMap A x) l = ∑ i, A l i * (x i : ℝ) := rfl

/-- The `ℝ`-linear map `AhatMap A` is surjective when the rows of `A` are `ℝ`-linearly
independent. -/
theorem AhatMap_range_eq_top {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ)
    (hA : LinearIndependent ℝ (fun l : ι => fun i : Fin N => A l i)) :
    (AhatMap A).range = ⊤ := by
  have hrank : A.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_row A]
    exact finrank_span_eq_card hA
  have hfin : Module.finrank ℝ (AhatMap A).range = Fintype.card ι := by
    let e := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
    have h1 : (AhatMap A).range = (A.mulVecLin).range.map e.toLinearMap := by
      rw [AhatMap, LinearMap.range_comp]
    have h2 : Module.finrank ℝ ((A.mulVecLin).range.map e.toLinearMap) =
        Module.finrank ℝ (A.mulVecLin).range :=
      LinearEquiv.finrank_map_eq e (A.mulVecLin).range
    rw [h1, h2]
    exact hrank
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hfin, finrank_euclideanSpace]

/-- The standard unit vector `Pi.single i 1` of `ℤ^N` maps to the `i`-th column of `A`. -/
lemma AhatZMap_single {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ) (i : Fin N) :
    AhatZMap A (Pi.single i (1 : ℤ)) =
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm (A.col i) := by
  rw [WithLp.ext_iff]
  funext l
  simp only [AhatZMap_ofLp, WithLp.coe_symm_linearEquiv, WithLp.ofLp_toLp, Matrix.col_apply,
    Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- If the rows of `A` are `ℝ`-linearly independent then the range of `AhatZMap A` spans
`EuclideanSpace ℝ ι` over `ℝ`. -/
theorem span_range_AhatZMap_eq_top {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ)
    (hA : LinearIndependent ℝ (fun l : ι => fun i : Fin N => A l i)) :
    Submodule.span ℝ (Set.range (AhatZMap A)) = ⊤ := by
  refine le_antisymm le_top ?_
  have hle : (AhatMap A).range ≤ Submodule.span ℝ (Set.range (AhatZMap A)) := by
    have h1 : (AhatMap A).range =
        Submodule.span ℝ (Set.range (fun i : Fin N => AhatZMap A (Pi.single i (1 : ℤ)))) := by
      rw [AhatMap, LinearMap.range_comp, Matrix.range_mulVecLin, Submodule.map_span]
      congr 1
      rw [← Set.range_comp]
      congr 1
      funext i
      exact (AhatZMap_single A i).symm
    rw [h1]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i (1 : ℤ), rfl⟩
  rw [← AhatMap_range_eq_top A hA]
  exact hle

/-- Membership in the kernel of `AhatZMap A`, elementwise. -/
lemma mem_ker_AhatZMap_iff {N : ℕ} {ι : Type*} [Fintype ι] (A : Matrix ι (Fin N) ℝ)
    (x : Fin N → ℤ) :
    x ∈ LinearMap.ker (AhatZMap A) ↔ ∀ l, ∑ i, A l i * (x i : ℝ) = 0 := by
  rw [LinearMap.mem_ker]
  have hiff : AhatZMap A x = 0 ↔ (fun l => ∑ i, A l i * (x i : ℝ)) = 0 := by
    rw [← (WithLp.ofLp_injective 2).eq_iff]
    simp
  rw [hiff, funext_iff]
  simp

end Commons.Lattice.Minkowski

namespace Commons.Lattice.Minkowski

/-- **Adapted `ℤ`-basis for the integer kernel of a real matrix with independent rows.**

Let `A : Matrix ι (Fin N) ℝ` have `ℝ`-linearly independent rows, and let `L` be a full `ℤ`-lattice
of `EuclideanSpace ℝ ι` containing the image lattice `A ℤ^N`. Then there is a `ℤ`-basis `e` of
`ℤ^N` whose first `N - card ι` vectors are exactly a `ℤ`-basis of the integer kernel
`Λ = {x : Fin N → ℤ | ∀ l, ∑ i, A l i * x i = 0}`:

`(∀ l, ∑ i, A l i * (x i : ℝ) = 0) ↔ ∃ a : Fin (N - card ι) → ℤ, x = ∑ j, a j • e (Fin.castLE _ j)`.

This is the real-matrix analogue of `Commons.Lattice.Module.exists_basis_subtype_kernel` (which
treats an integer matrix). -/
theorem exists_basis_subtype_kernel_real {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι (Fin N) ℝ) (hA : LinearIndependent ℝ (fun l : ι => fun i : Fin N => A l i))
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : ∀ x : Fin N → ℤ, (WithLp.equiv 2 (ι → ℝ)).symm (fun l => ∑ i, A l i * (x i : ℝ)) ∈ L) :
    ∃ e : Module.Basis (Fin N) ℤ (Fin N → ℤ), ∀ x : Fin N → ℤ,
      (∀ l, ∑ i, A l i * (x i : ℝ) = 0) ↔
        ∃ a : Fin (N - Fintype.card ι) → ℤ,
          x = ∑ j, a j • e (Fin.castLE (Nat.sub_le N (Fintype.card ι)) j) := by
  classical
  set Λ : Submodule ℤ (Fin N → ℤ) := LinearMap.ker (AhatZMap A) with hΛ
  have hker : ∀ x : Fin N → ℤ, x ∈ Λ ↔ ∀ l, ∑ i, A l i * (x i : ℝ) = 0 := by
    intro x; rw [hΛ]; exact mem_ker_AhatZMap_iff A x
  -- The range of `AhatZMap A` lies in `L`, hence is discrete.
  have hle : (AhatZMap A).range ≤ L := by
    rintro y ⟨x, rfl⟩
    exact hL x
  haveI : DiscreteTopology (AhatZMap A).range := by
    have hDs : DiscreteTopology (L : Set (EuclideanSpace ℝ ι)) := ‹DiscreteTopology L›
    exact DiscreteTopology.of_subset hDs hle
  haveI : IsZLattice ℝ (AhatZMap A).range := ⟨span_range_AhatZMap_eq_top A hA⟩
  -- Rank of the range.
  have hfinrange : Module.finrank ℤ (AhatZMap A).range = Fintype.card ι := by
    rw [ZLattice.rank ℝ (AhatZMap A).range, finrank_euclideanSpace]
  -- Rank-nullity.
  have hfinΛ : Module.finrank ℤ Λ = N - Fintype.card ι := by
    have hquot : Module.finrank ℤ ((Fin N → ℤ) ⧸ Λ) =
        Module.finrank ℤ (AhatZMap A).range := by
      rw [hΛ]
      exact LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (AhatZMap A))
    have hrn := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := Fin N → ℤ) Λ
    rw [hquot, hfinrange, Module.finrank_fin_fun ℤ] at hrn
    omega
  -- Purity.
  have hpure : ∀ x : Fin N → ℤ, (∃ a : ℤ, a ≠ 0 ∧ a • x ∈ Λ) → x ∈ Λ := by
    rintro x ⟨a, ha, hax⟩
    rw [hker] at hax ⊢
    intro l
    have h0 := hax l
    have hthis : ∑ i, A l i * ((a • x) i : ℝ) =
        (a : ℝ) * ∑ i, A l i * (x i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, zsmul_eq_mul]
      push_cast
      ring
    rw [hthis] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast ha)
  -- Choose a basis of `Λ` and extend it.
  let bN : Module.Basis (Fin (N - Fintype.card ι)) ℤ Λ :=
    Module.finBasisOfFinrankEq ℤ Λ hfinΛ
  obtain ⟨e, he⟩ := Commons.Lattice.Module.basis_extension_pure_rank (M := Fin N → ℤ)
    (m := N) (d := N - Fintype.card ι) (Nat.sub_le N (Fintype.card ι)) Λ
    (Pi.basisFun ℤ (Fin N)) bN hpure
  have hspanΛ : Submodule.span ℤ
      (Set.range (fun j : Fin (N - Fintype.card ι) => ((bN j : Λ) : Fin N → ℤ))) = Λ := by
    have hrange : Set.range (fun j : Fin (N - Fintype.card ι) => ((bN j : Λ) : Fin N → ℤ)) =
        Λ.subtype '' Set.range bN := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨bN j, ⟨j, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
    rw [hrange, ← Submodule.map_span, bN.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : Submodule.span ℤ
      (Set.range (fun j : Fin (N - Fintype.card ι) =>
        e (Fin.castLE (Nat.sub_le N (Fintype.card ι)) j))) = Λ := by
    have hfun : (fun j : Fin (N - Fintype.card ι) =>
          e (Fin.castLE (Nat.sub_le N (Fintype.card ι)) j)) =
        (fun j : Fin (N - Fintype.card ι) => ((bN j : Λ) : Fin N → ℤ)) := funext he
    rw [hfun, hspanΛ]
  refine ⟨e, fun x => ?_⟩
  rw [← hker x]
  constructor
  · intro hx
    have hxspan : x ∈ Submodule.span ℤ
        (Set.range (fun j : Fin (N - Fintype.card ι) =>
          e (Fin.castLE (Nat.sub_le N (Fintype.card ι)) j))) := by
      rw [hspan]
      exact hx
    rcases (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxspan with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨a, rfl⟩
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun ℤ]
    exact ⟨a, rfl⟩

end Commons.Lattice.Minkowski