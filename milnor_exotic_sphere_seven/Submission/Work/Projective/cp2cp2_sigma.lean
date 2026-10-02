import Mathlib
import Submission.Work.Projective.CP2CP2Ring
import Submission.Work.Projective.signature_of_orthogonal_spanning

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The signature of `ℂP² × ℂP²`

This module computes the *signature* `σ(ℂP² × ℂP²) = 1` from the Künneth ring data recorded in
`Work.Projective.CP2CP2Model` (`Submission/Work/Projective/CP2CP2Ring.lean`), i.e. from the two
hyperplane classes `a, b ∈ H²`, the fundamental class `c ∈ H₈` and the nine intersection numbers
of `a², ab, b²`.

The route is the one advertised in `Submission/Work/SignatureBordism/Rationalisation.lean`: the
middle intersection form on `H⁴(X;ℤ) ⊗[ℤ] ℚ` is diagonalised by the basis

`a² + b²,  a² - b²,  ab`

with diagonal values `(2, -2, 1)`, so it is equivalent to `QuadraticMap.weightedSumSquares ℚ
![2,-2,1]` and has signature `2 - 1 = 1`.  Concretely:

* `Work.Projective.span_tmul_one_image` — base change to `ℚ` carries a `ℤ`-spanning set to a
  `ℚ`-spanning set (`1 ⊗ -` is a `ℤ`-linear map, and every element of the tensor product is a
  finite sum of pure tensors);
* `Work.Projective.span_cp2cp2Vec` — **`H⁴ ⊗ ℚ` is spanned by the three vectors**: over `ℚ` the
  change of basis `{a², b²} ↦ {a²+b², a²-b²}` is invertible (with inverse the half-sum/half-
  difference), so the three vectors span as soon as the rationalisations of `a², ab, b²` do, which
  is `CP2CP2Model.span_middle`;
* `Work.Projective.cp2cp2Vec_pair_*` — the nine values `⟨vᵢ ⌣ vⱼ, c⟩` of the diagonalising basis,
  obtained by expanding the rationalised intersection form on pure tensors
  (`Work.SignatureBordism.ratInterForm_tmul`) and using the nine intersection-number fields of the
  model;
* `Work.Projective.cp2cp2Vec_diagonal` — consequently the middle intersection form *is* diagonal in
  that spanning family, with weights `cp2cp2Diag = (2, -2, 1)`;
* `Work.Projective.cp2cp2_sigma` — the signature is therefore `2 - 1 = 1`, by
  `Work.Projective.signature_of_orthogonal_spanning` (Sylvester's law of inertia).

## Main results

* `Work.Projective.cp2cp2_sigma` — **`σ(ℂP² × ℂP²) = 1`**, the `σ`-coordinate of
  `Work.SignatureBordism.cp2cp2Tuple`.

The other coordinates of the tuple are computed in
`Submission/Work/Projective/Product.lean` (`Work.Projective.p1SqNumberProd_eq`,
`Work.Projective.p2NumberProd_eq`) in the abstract Künneth ring; the present module works in the
cochain model of an actual `SSet`, where only the `CP2CP2Model` interface is available.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Work.Projective

open TensorProduct
open Work.Cohomology Work.SignatureBordism

noncomputable section

/-! ## Base change of a `ℤ`-spanning set to `ℚ`

The rationalisation of a spanning set spans.  This is the *set* version of
`Work.SignatureBordism.span_tmul_one` (which treats the case of a single generator), and it is
what turns `CP2CP2Model.span_middle`, a statement over `ℤ`, into a spanning statement over `ℚ`. -/

/-- **Base change to `ℚ` preserves spanning.**  If `s` spans a `ℤ`-module `M`, then the image of
`s` under `y ↦ 1 ⊗ₜ[ℤ] y` spans the rationalisation `ℚ ⊗[ℤ] M` over `ℚ`.

Indeed `f = TensorProduct.mk ℤ ℚ M 1` is `ℤ`-linear, so the image of a `ℤ`-spanning set spans the
range of `f` over `ℤ`; and every pure tensor `q ⊗ m = q • (1 ⊗ m)` is a `ℚ`-multiple of an element
of that range, while every element of the tensor product is a sum of pure tensors. -/
theorem span_tmul_one_image {M : Type*} [AddCommGroup M] [Module ℤ M] (s : Set M)
    (hs : Submodule.span ℤ s = ⊤) :
    Submodule.span ℚ ((fun y : M => ((1 : ℚ) ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M)) '' s) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro z
  set T : Submodule ℚ (ℚ ⊗[ℤ] M) :=
    Submodule.span ℚ ((fun y : M => ((1 : ℚ) ⊗ₜ[ℤ] y : ℚ ⊗[ℤ] M)) '' s) with hT
  have hle : Submodule.span ℤ s ≤
      Submodule.comap (TensorProduct.mk ℤ ℚ M (1 : ℚ)) (T.restrictScalars ℤ) := by
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have key : ∀ m : M, ((1 : ℚ) ⊗ₜ[ℤ] m : ℚ ⊗[ℤ] M) ∈ T := by
    intro m
    exact hle (by rw [hs]; exact Submodule.mem_top)
  show z ∈ T
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact T.zero_mem
  · intro q m
    rw [TensorProduct.tmul_eq_smul_one_tmul]
    exact T.smul_mem q (key m)
  · intro x y hx hy
    exact T.add_mem hx hy

/-! ## The three diagonalising vectors -/

/-- **`v₀ = a² + b²`**, the first vector of the diagonalising basis. -/
@[simp] theorem cp2cp2Vec_zero {X : SSet} (a b : (cochainC ℤ X).homology 2) :
    cp2cp2Vec X a b 0 =
      ((1 : ℚ) ⊗ₜ[ℤ] kSq X a + (1 : ℚ) ⊗ₜ[ℤ] kSq X b : ratCohomology 4 X) := by
  simp [cp2cp2Vec]

/-- **`v₁ = a² - b²`**, the second vector of the diagonalising basis. -/
@[simp] theorem cp2cp2Vec_one {X : SSet} (a b : (cochainC ℤ X).homology 2) :
    cp2cp2Vec X a b 1 =
      ((1 : ℚ) ⊗ₜ[ℤ] kSq X a - (1 : ℚ) ⊗ₜ[ℤ] kSq X b : ratCohomology 4 X) := by
  simp [cp2cp2Vec]

/-- **`v₂ = ab`**, the third vector of the diagonalising basis. -/
@[simp] theorem cp2cp2Vec_two {X : SSet} (a b : (cochainC ℤ X).homology 2) :
    cp2cp2Vec X a b 2 = ((1 : ℚ) ⊗ₜ[ℤ] kMul X a b : ratCohomology 4 X) := by
  simp [cp2cp2Vec]

/-- The diagonal values of `Work.Projective.cp2cp2Diag`, spelled out. -/
@[simp] theorem cp2cp2Diag_zero : cp2cp2Diag 0 = 2 := by simp [cp2cp2Diag]

/-- The diagonal values of `Work.Projective.cp2cp2Diag`, spelled out. -/
@[simp] theorem cp2cp2Diag_one : cp2cp2Diag 1 = -2 := by simp [cp2cp2Diag]

/-- The diagonal values of `Work.Projective.cp2cp2Diag`, spelled out. -/
@[simp] theorem cp2cp2Diag_two : cp2cp2Diag 2 = 1 := by simp [cp2cp2Diag]

/-! ## The rationalised intersection form on pure tensors -/

/-- **The rationalised intersection form on pure tensors with coefficient `1`** is the integral
intersection form, cast to `ℚ` (the computation rule
`Work.SignatureBordism.ratInterForm_tmul` with `a = b = 1`). -/
theorem ratInterForm_one_tmul {X : SSet} (c : (chainC ℤ X).homology 8)
    (y z : (cochainC ℤ X).homology 4) :
    ratInterForm 4 X c ((1 : ℚ) ⊗ₜ[ℤ] y) ((1 : ℚ) ⊗ₜ[ℤ] z)
      = ((interForm ℤ X 4 4 c y z : ℤ) : ℚ) := by
  rw [ratInterForm_tmul]
  ring

/-! ## The nine intersection numbers of the diagonalising basis

Each of these is the expansion of `⟨vᵢ ⌣ vⱼ, c⟩` in the classes `a², ab, b²`
(`ratInterForm_one_tmul`), followed by the corresponding fields of the model. -/

/-- `⟨v₀ ⌣ v₀, c⟩ = ⟨(a²+b²)², c⟩ = 2`. -/
theorem cp2cp2Vec_pair_00 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 0) (cp2cp2Vec X M.a M.b 0) = 2 := by
  rw [cp2cp2Vec_zero]
  simp only [map_add, LinearMap.add_apply, ratInterForm_one_tmul]
  rw [M.int_a2a2, M.int_a2b2, M.int_b2a2, M.int_b2b2]
  norm_num

/-- `⟨v₀ ⌣ v₁, c⟩ = ⟨(a²+b²)(a²-b²), c⟩ = 0`. -/
theorem cp2cp2Vec_pair_01 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 0) (cp2cp2Vec X M.a M.b 1) = 0 := by
  rw [cp2cp2Vec_zero, cp2cp2Vec_one]
  simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply, ratInterForm_one_tmul]
  rw [M.int_a2a2, M.int_a2b2, M.int_b2a2, M.int_b2b2]
  norm_num

/-- `⟨v₀ ⌣ v₂, c⟩ = ⟨(a²+b²)ab, c⟩ = 0`. -/
theorem cp2cp2Vec_pair_02 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 0) (cp2cp2Vec X M.a M.b 2) = 0 := by
  rw [cp2cp2Vec_zero, cp2cp2Vec_two]
  simp only [map_add, LinearMap.add_apply, ratInterForm_one_tmul]
  rw [M.int_a2ab, M.int_b2ab]
  norm_num

/-- `⟨v₁ ⌣ v₀, c⟩ = ⟨(a²-b²)(a²+b²), c⟩ = 0`. -/
theorem cp2cp2Vec_pair_10 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 1) (cp2cp2Vec X M.a M.b 0) = 0 := by
  rw [cp2cp2Vec_zero, cp2cp2Vec_one]
  simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply, ratInterForm_one_tmul]
  rw [M.int_a2a2, M.int_a2b2, M.int_b2a2, M.int_b2b2]
  norm_num

/-- `⟨v₁ ⌣ v₁, c⟩ = ⟨(a²-b²)², c⟩ = -2`. -/
theorem cp2cp2Vec_pair_11 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 1) (cp2cp2Vec X M.a M.b 1) = -2 := by
  rw [cp2cp2Vec_one]
  simp only [map_sub, LinearMap.sub_apply, ratInterForm_one_tmul]
  rw [M.int_a2a2, M.int_a2b2, M.int_b2a2, M.int_b2b2]
  norm_num

/-- `⟨v₁ ⌣ v₂, c⟩ = ⟨(a²-b²)ab, c⟩ = 0`. -/
theorem cp2cp2Vec_pair_12 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 1) (cp2cp2Vec X M.a M.b 2) = 0 := by
  rw [cp2cp2Vec_one, cp2cp2Vec_two]
  simp only [map_sub, LinearMap.sub_apply, ratInterForm_one_tmul]
  rw [M.int_a2ab, M.int_b2ab]
  norm_num

/-- `⟨v₂ ⌣ v₀, c⟩ = ⟨ab(a²+b²), c⟩ = 0`. -/
theorem cp2cp2Vec_pair_20 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 2) (cp2cp2Vec X M.a M.b 0) = 0 := by
  rw [cp2cp2Vec_zero, cp2cp2Vec_two]
  simp only [map_add, LinearMap.add_apply, ratInterForm_one_tmul]
  rw [M.int_aba2, M.int_abb2]
  norm_num

/-- `⟨v₂ ⌣ v₁, c⟩ = ⟨ab(a²-b²), c⟩ = 0`. -/
theorem cp2cp2Vec_pair_21 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 2) (cp2cp2Vec X M.a M.b 1) = 0 := by
  rw [cp2cp2Vec_two, cp2cp2Vec_one]
  simp only [map_sub, LinearMap.sub_apply, ratInterForm_one_tmul]
  rw [M.int_aba2, M.int_abb2]
  norm_num

/-- `⟨v₂ ⌣ v₂, c⟩ = ⟨(ab)², c⟩ = 1`. -/
theorem cp2cp2Vec_pair_22 {X : SSet} (M : CP2CP2Model X) :
    ratInterForm 4 X M.c (cp2cp2Vec X M.a M.b 2) (cp2cp2Vec X M.a M.b 2) = 1 := by
  rw [cp2cp2Vec_two, ratInterForm_one_tmul, M.int_abab]
  norm_num

/-! ## The three vectors span `H⁴ ⊗ ℚ` -/

/-- **The middle cohomology `H⁴(X;ℤ) ⊗[ℤ] ℚ` is spanned by `a² + b²`, `a² - b²`, `ab`.**

Over `ℚ` the change of basis `{a², b²} ↦ {a²+b², a²-b²}` is invertible:
`a² = ½((a²+b²) + (a²-b²))` and `b² = ½((a²+b²) - (a²-b²))`.  Since
`CP2CP2Model.span_middle` says that `a², ab, b²` span `H⁴(X;ℤ)` over `ℤ`, their rationalisations
span `H⁴(X;ℤ) ⊗ ℚ` over `ℚ` (`span_tmul_one_image`), and the latter span is contained in the span
of the three vectors `cp2cp2Vec`. -/
theorem span_cp2cp2Vec {X : SSet} (M : CP2CP2Model X) :
    Submodule.span ℚ (Set.range (cp2cp2Vec X M.a M.b)) = ⊤ := by
  have htop : Submodule.span ℚ
      ((fun y : (cochainC ℤ X).homology 4 => ((1 : ℚ) ⊗ₜ[ℤ] y : ratCohomology 4 X)) ''
        ({kSq X M.a, kMul X M.a M.b, kSq X M.b} : Set ((cochainC ℤ X).homology 4))) = ⊤ :=
    span_tmul_one_image _ M.span_middle
  have hle : Submodule.span ℚ
      ((fun y : (cochainC ℤ X).homology 4 => ((1 : ℚ) ⊗ₜ[ℤ] y : ratCohomology 4 X)) ''
        ({kSq X M.a, kMul X M.a M.b, kSq X M.b} : Set ((cochainC ℤ X).homology 4)))
      ≤ Submodule.span ℚ (Set.range (cp2cp2Vec X M.a M.b)) := by
    rw [Submodule.span_le]
    rintro z ⟨y, hy, rfl⟩
    change ((1 : ℚ) ⊗ₜ[ℤ] y : ratCohomology 4 X) ∈
      Submodule.span ℚ (Set.range (cp2cp2Vec X M.a M.b))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · -- the rationalisation of `a²` is `½(v₀ + v₁)`
      have h : (1 / 2 : ℚ) • (cp2cp2Vec X M.a M.b 0 + cp2cp2Vec X M.a M.b 1)
          = ((1 : ℚ) ⊗ₜ[ℤ] kSq X M.a : ratCohomology 4 X) := by
        rw [cp2cp2Vec_zero, cp2cp2Vec_one]
        module
      rw [← h]
      exact Submodule.smul_mem _ _
        (Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self 0))
          (Submodule.subset_span (Set.mem_range_self 1)))
    · -- the rationalisation of `ab` is `v₂`
      rw [← cp2cp2Vec_two]
      exact Submodule.subset_span (Set.mem_range_self 2)
    · -- the rationalisation of `b²` is `½(v₀ - v₁)`
      have h : (1 / 2 : ℚ) • (cp2cp2Vec X M.a M.b 0 - cp2cp2Vec X M.a M.b 1)
          = ((1 : ℚ) ⊗ₜ[ℤ] kSq X M.b : ratCohomology 4 X) := by
        rw [cp2cp2Vec_zero, cp2cp2Vec_one]
        module
      rw [← h]
      exact Submodule.smul_mem _ _
        (Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self 0))
          (Submodule.subset_span (Set.mem_range_self 1)))
  have := hle
  rw [htop] at this
  exact eq_top_iff.mpr this

/-! ## The intersection form is diagonal in that spanning family -/

/-- **The middle intersection form of `ℂP² × ℂP²` is diagonal in `a²+b², a²-b², ab`** with the
weights `cp2cp2Diag = (2, -2, 1)`:

`Q (x₀ v₀ + x₁ v₁ + x₂ v₂) = 2 x₀² - 2 x₁² + x₂²`.

This is the expansion of `Q y = ⟨y ⌣ y, c⟩` as a double sum
`∑ᵢⱼ xᵢ xⱼ ⟨vᵢ ⌣ vⱼ, c⟩` followed by the nine intersection numbers `cp2cp2Vec_pair_*`. -/
theorem cp2cp2Vec_diagonal {X : SSet} (M : CP2CP2Model X) (x : Fin 3 → ℚ) :
    quadOfBilin (ratInterForm 4 X M.c) (∑ i, x i • cp2cp2Vec X M.a M.b i)
      = ∑ i, (x i) ^ 2 * cp2cp2Diag i := by
  have hv : (∑ i : Fin 3, x i • cp2cp2Vec X M.a M.b i)
      = x 0 • cp2cp2Vec X M.a M.b 0 + x 1 • cp2cp2Vec X M.a M.b 1
        + x 2 • cp2cp2Vec X M.a M.b 2 := by
    rw [Fin.sum_univ_three]
  rw [hv, quadOfBilin_apply]
  simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  rw [cp2cp2Vec_pair_00 M, cp2cp2Vec_pair_01 M, cp2cp2Vec_pair_02 M, cp2cp2Vec_pair_10 M,
    cp2cp2Vec_pair_11 M, cp2cp2Vec_pair_12 M, cp2cp2Vec_pair_20 M, cp2cp2Vec_pair_21 M,
    cp2cp2Vec_pair_22 M]
  rw [Fin.sum_univ_three, cp2cp2Diag_zero, cp2cp2Diag_one, cp2cp2Diag_two]
  ring

/-! ## The signature -/

/-- **The signature of `ℂP² × ℂP²` is `1`**, from the Künneth ring data of
`Work.Projective.CP2CP2Model` (`Submission/Work/Projective/CP2CP2Ring.lean`): the middle
intersection form on `H⁴(ℂP² × ℂP²;ℚ) ⊗ ℚ` has the orthogonal basis `a² + b²`, `a² - b²`, `ab`
with values `2, -2, 1` (`Work.Projective.cp2cp2Vec`, `Work.Projective.cp2cp2Diag`), so it is
equivalent to `QuadraticMap.weightedSumSquares ℚ ![2,-2,1]` and has signature `2 - 1 = 1`.

The intended route: from `M.span_middle` show the three vectors span `H⁴ ⊗ ℚ` (over `ℚ` the change
of basis `{a², b²} ↦ {a²+b², a²-b²}` is invertible), then show the form is diagonal in them by
expanding `ratInterForm` on pure tensors (`Work.SignatureBordism.ratInterForm_tmul`) and using the
nine intersection-number fields, then apply
`Work.Projective.signature_of_orthogonal_spanning`
(`Submission.Work.Projective.signature_of_orthogonal_spanning`). -/
theorem cp2cp2_sigma {X : SSet} (M : Work.Projective.CP2CP2Model X) :
    Work.SignatureBordism.sigma 4 X M.c = 1 := by
  have hne : ∀ i : Fin 3, cp2cp2Diag i ≠ 0 := by
    intro i
    fin_cases i <;> decide
  have hsig := signature_of_orthogonal_spanning (quadOfBilin (ratInterForm 4 X M.c))
    (cp2cp2Vec X M.a M.b) cp2cp2Diag (span_cp2cp2Vec M)
    (cp2cp2Vec_diagonal M) hne
  show signature (quadOfBilin (ratInterForm 4 X M.c)) = 1
  rw [hsig]
  have hpos : (Finset.univ.filter (fun i : Fin 3 => 0 < cp2cp2Diag i)).card = 2 := by decide
  have hneg : (Finset.univ.filter (fun i : Fin 3 => cp2cp2Diag i < 0)).card = 1 := by decide
  rw [hpos, hneg]
  norm_num

end

end Work.Projective
