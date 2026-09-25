import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_graded_part_one_finrank

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra
open scoped TensorProduct

def golodShafarevich_words (ι : Type*) (d : ℕ) := {w : FreeMonoid ι // (FreeMonoid.toList w).length = d}

noncomputable def golodShafarevich_gradedPartBasis (K ι : Type*) [Field K] (d : ℕ) :
    Module.Basis (golodShafarevich_words ι d) K (golodShafarevich_gradedPart K ι d) := by
  let v : golodShafarevich_words ι d → FreeAlgebra K ι := fun w => FreeAlgebra.basisFreeMonoid K ι w.1
  have hli : LinearIndependent K v := by
    dsimp [v]
    exact (FreeAlgebra.basisFreeMonoid K ι).linearIndependent.comp (fun w : golodShafarevich_words ι d => w.1) (by intro a b h; exact Subtype.ext h)
  have hspan : Submodule.span K (Set.range v) = golodShafarevich_gradedPart K ι d := by
    unfold golodShafarevich_gradedPart
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with ⟨w, hxw⟩
      rw [← hxw]
      apply Submodule.subset_span
      refine ⟨w.1, w.2, rfl⟩
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with ⟨w, hwlen, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨w, hwlen⟩, rfl⟩
  exact (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)

@[simp] lemma golodShafarevich_gradedPartBasis_apply (K ι : Type*) [Field K] (d : ℕ)
    (w : golodShafarevich_words ι d) :
    ((golodShafarevich_gradedPartBasis K ι d w : golodShafarevich_gradedPart K ι d) : FreeAlgebra K ι) =
      FreeAlgebra.basisFreeMonoid K ι w.1 := by
  unfold golodShafarevich_gradedPartBasis
  simp [Module.Basis.span_apply]

noncomputable def golodShafarevich_gradedMulMap (K ι : Type*) [Field K] (d e : ℕ) :
    golodShafarevich_gradedPart K ι d ⊗[K] golodShafarevich_gradedPart K ι e →ₗ[K]
      golodShafarevich_gradedPart K ι (d + e) := by
  refine LinearMap.codRestrict _ (Submodule.mulMap (golodShafarevich_gradedPart K ι d) (golodShafarevich_gradedPart K ι e)) ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul a b => exact golodShafarevich_gradedPart_mul_mem a.2 b.2

@[simp] lemma golodShafarevich_gradedMulMap_tmul (K ι : Type*) [Field K] (d e : ℕ)
    (a : golodShafarevich_gradedPart K ι d) (b : golodShafarevich_gradedPart K ι e) :
    ((golodShafarevich_gradedMulMap K ι d e) (a ⊗ₜ[K] b) : FreeAlgebra K ι) = (a : FreeAlgebra K ι) * b := by
  simp [golodShafarevich_gradedMulMap]

noncomputable def golodShafarevich_gradedMulMapRight (K ι : Type*) [Field K] {n : ℕ} (hn : 0 < n) :
    golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1 →ₗ[K]
      golodShafarevich_gradedPart K ι n := by
  refine LinearMap.codRestrict _ (Submodule.mulMap (golodShafarevich_gradedPart K ι (n - 1)) (golodShafarevich_gradedPart K ι 1)) ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul a b =>
      have h := golodShafarevich_gradedPart_mul_mem a.2 b.2
      simpa [Nat.sub_one_add_one_eq_of_pos hn] using h

@[simp] lemma golodShafarevich_gradedMulMapRight_tmul (K ι : Type*) [Field K] {n : ℕ} (hn : 0 < n)
    (a : golodShafarevich_gradedPart K ι (n - 1)) (b : golodShafarevich_gradedPart K ι 1) :
    ((golodShafarevich_gradedMulMapRight K ι hn) (a ⊗ₜ[K] b) : FreeAlgebra K ι) = (a : FreeAlgebra K ι) * b := by
  simp [golodShafarevich_gradedMulMapRight]

noncomputable def golodShafarevich_word_split (ι : Type*) {n : ℕ} (hn : 0 < n)
    (w : golodShafarevich_words ι n) :
    golodShafarevich_words ι (n - 1) × golodShafarevich_words ι 1 := by
  let l : List ι := FreeMonoid.toList w.1
  have hlne : l ≠ [] := by
    intro h
    have hlen : l.length = 0 := by simp [h]
    have hwlen : l.length = n := by simpa [l] using w.2
    omega
  let i : ι := l.getLast hlne
  let u : FreeMonoid ι := FreeMonoid.ofList l.dropLast
  have hulen : (FreeMonoid.toList u).length = n - 1 := by
    dsimp [u]
    have hlen : l.length = n := by simpa [l] using w.2
    rw [List.length_dropLast]
    omega
  have hilen : (FreeMonoid.toList (FreeMonoid.of i)).length = 1 := by
    simp [FreeMonoid.toList_of]
  exact (⟨u, hulen⟩, ⟨FreeMonoid.of i, hilen⟩)

lemma golodShafarevich_word_split_spec (ι : Type*) {n : ℕ} (hn : 0 < n)
    (w : golodShafarevich_words ι n) :
    w.1 = (golodShafarevich_word_split ι hn w).1.1 * (golodShafarevich_word_split ι hn w).2.1 := by
  unfold golodShafarevich_word_split
  dsimp
  let l : List ι := FreeMonoid.toList w.1
  have hlne : l ≠ [] := by
    intro h
    have hlen : l.length = 0 := by simp [h]
    have hwlen : l.length = n := by simpa [l] using w.2
    omega
  have hsplit : l.dropLast ++ [l.getLast hlne] = l := List.dropLast_concat_getLast hlne
  apply FreeMonoid.toList.injective
  rw [FreeMonoid.toList_mul, FreeMonoid.toList_ofList, FreeMonoid.toList_of]
  simpa [l] using hsplit.symm

noncomputable def golodShafarevich_word_concat (ι : Type*) {n : ℕ} (hn : 0 < n)
    (p : golodShafarevich_words ι (n - 1) × golodShafarevich_words ι 1) :
    golodShafarevich_words ι n := by
  refine ⟨p.1.1 * p.2.1, ?_⟩
  rw [FreeMonoid.toList_mul, List.length_append, p.1.2, p.2.2]
  exact Nat.sub_one_add_one_eq_of_pos hn

lemma golodShafarevich_word_split_concat (ι : Type*) {n : ℕ} (hn : 0 < n)
    (p : golodShafarevich_words ι (n - 1) × golodShafarevich_words ι 1) :
    golodShafarevich_word_split ι hn (golodShafarevich_word_concat ι hn p) = p := by
  rcases freeMonoid_eq_of_of_length_one p.2.2 with ⟨i, hi⟩
  apply Prod.ext
  · apply Subtype.ext
    unfold golodShafarevich_word_split golodShafarevich_word_concat
    dsimp
    apply FreeMonoid.toList.injective
    rw [FreeMonoid.toList_ofList]
    simp [hi]
  · apply Subtype.ext
    unfold golodShafarevich_word_split golodShafarevich_word_concat
    dsimp
    apply FreeMonoid.toList.injective
    rw [FreeMonoid.toList_of]
    simp [hi]

noncomputable def golodShafarevich_wordsEquiv (ι : Type*) {n : ℕ} (hn : 0 < n) :
    golodShafarevich_words ι (n - 1) × golodShafarevich_words ι 1 ≃ golodShafarevich_words ι n where
  toFun := golodShafarevich_word_concat ι hn
  invFun := golodShafarevich_word_split ι hn
  left_inv := golodShafarevich_word_split_concat ι hn
  right_inv := by
    intro w
    apply Subtype.ext
    exact (golodShafarevich_word_split_spec ι hn w).symm

noncomputable def golodShafarevich_gradedMulPreimage (K ι : Type*) [Field K] {n : ℕ} (hn : 0 < n)
    (w : golodShafarevich_words ι n) :
    golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1 :=
  (golodShafarevich_gradedPartBasis K ι (n - 1)) (golodShafarevich_word_split ι hn w).1 ⊗ₜ[K]
    (golodShafarevich_gradedPartBasis K ι 1) (golodShafarevich_word_split ι hn w).2

lemma golodShafarevich_gradedMulPreimage_apply (K ι : Type*) [Field K] {n : ℕ} (hn : 0 < n)
    (w : golodShafarevich_words ι n) :
    golodShafarevich_gradedMulMapRight K ι hn (golodShafarevich_gradedMulPreimage K ι hn w) =
      golodShafarevich_gradedPartBasis K ι n w := by
  apply Subtype.ext
  simp only [golodShafarevich_gradedMulPreimage, golodShafarevich_gradedMulMapRight_tmul,
    golodShafarevich_gradedPartBasis_apply]
  rw [← golodShafarevich_basisFreeMonoid_mul]
  rw [← golodShafarevich_word_split_spec]

lemma golodShafarevich_gradedMulMapRight_surjective (K ι : Type*) [Field K] {n : ℕ} (hn : 0 < n) :
    Function.Surjective (golodShafarevich_gradedMulMapRight K ι hn) := by
  intro y
  let bn := golodShafarevich_gradedPartBasis K ι n
  let f := golodShafarevich_gradedMulMapRight K ι hn
  let c := bn.repr y
  let pre : golodShafarevich_words ι n → golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1 :=
    fun w => golodShafarevich_gradedMulPreimage K ι hn w
  let x : golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1 :=
    Finsupp.linearCombination K pre c
  refine ⟨x, ?_⟩
  have hy : Finsupp.linearCombination K bn c = y := by
    simpa [c] using Module.Basis.linearCombination_repr bn y
  rw [← hy]
  dsimp [x]
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_smul]
  congr 1
  exact golodShafarevich_gradedMulPreimage_apply K ι hn w

lemma golodShafarevich_mem_span_mul_right {K ι : Type*} [Field K]
    {a : FreeAlgebra K ι} {T : Submodule K (FreeAlgebra K ι)}
    (h : ∀ i : ι, a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) ∈ T)
    {u : golodShafarevich_gradedPart K ι 1} :
    a * (u : FreeAlgebra K ι) ∈ T := by
  have hu : (u : FreeAlgebra K ι) ∈ Submodule.span K (Set.range (fun i : ι => FreeAlgebra.ι K i)) := by
    simpa [golodShafarevich_gradedPart_one_eq_span_ι] using u.2
  refine Submodule.span_induction (p := fun y (_ : y ∈ Submodule.span K (Set.range (fun i : ι => FreeAlgebra.ι K i))) =>
    a * y ∈ T) ?_ ?_ ?_ ?_ hu
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    simpa [golodShafarevich_basisFreeMonoid_of] using h i
  · simp
  · intro y z hy hz iy iz
    rw [mul_add]
    exact Submodule.add_mem _ iy iz
  · intro c y hy iy
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ _ iy

lemma golodShafarevich_gradedMulMapRight_image_subset
    {K ι : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (A : Submodule K (golodShafarevich_gradedPart K ι (n - 1))) :
    let T := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
      x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    (LinearMap.range (TensorProduct.map A.subtype LinearMap.id)).map
      (golodShafarevich_gradedMulMapRight K ι hn) ≤
      Submodule.comap (golodShafarevich_gradedPart K ι n).subtype T := by
  intro T x hx
  rw [Submodule.mem_comap]
  rw [TensorProduct.range_map_eq_span_tmul A.subtype LinearMap.id] at hx
  rw [Submodule.map_span] at hx
  refine Submodule.span_induction (p := fun y (_ : y ∈ Submodule.span K
      (golodShafarevich_gradedMulMapRight K ι hn '' {t | ∃ (m : A) (n : golodShafarevich_gradedPart K ι 1),
        A.subtype m ⊗ₜ[K] LinearMap.id n = t})) =>
      (y : FreeAlgebra K ι) ∈ T) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    rcases ht with ⟨a, u, rfl⟩
    simp only [golodShafarevich_gradedMulMapRight_tmul, LinearMap.id_coe, id_eq]
    apply golodShafarevich_mem_span_mul_right
    intro i
    apply Submodule.subset_span
    refine ⟨a, a.2, i, rfl⟩
  · simp
  · intro y z hy hz iy iz
    exact Submodule.add_mem _ iy iz
  · intro c y hy iy
    exact Submodule.smul_mem _ _ iy

lemma golodShafarevich_gradedMulMapRight_image_superset
    {K ι : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (A : Submodule K (golodShafarevich_gradedPart K ι (n - 1))) :
    let T := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
      x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    Submodule.comap (golodShafarevich_gradedPart K ι n).subtype T ≤
      (LinearMap.range (TensorProduct.map A.subtype LinearMap.id)).map
        (golodShafarevich_gradedMulMapRight K ι hn) := by
  intro T x hx
  rw [Submodule.mem_comap] at hx
  rw [Submodule.mem_map]
  have hp : ∃ hC : (x : FreeAlgebra K ι) ∈ golodShafarevich_gradedPart K ι n,
      ∃ z ∈ LinearMap.range (TensorProduct.map A.subtype LinearMap.id),
        golodShafarevich_gradedMulMapRight K ι hn z =
          (⟨(x : FreeAlgebra K ι), hC⟩ : golodShafarevich_gradedPart K ι n) := by
    refine Submodule.span_induction (p := fun y (_ : y ∈ T) =>
        ∃ hC : y ∈ golodShafarevich_gradedPart K ι n,
          ∃ z ∈ LinearMap.range (TensorProduct.map A.subtype LinearMap.id),
            golodShafarevich_gradedMulMapRight K ι hn z =
              (⟨y, hC⟩ : golodShafarevich_gradedPart K ι n)) ?_ ?_ ?_ ?_ hx
    · intro y hyT
      rcases hyT with ⟨a, haA, i, rfl⟩
      have hbasis : FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) ∈ golodShafarevich_gradedPart K ι 1 := by
        simpa using (golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) (FreeMonoid.of i))
      have hC : (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) ∈
          golodShafarevich_gradedPart K ι n := by
        have h := golodShafarevich_gradedPart_mul_mem a.2 hbasis
        simpa [Nat.sub_one_add_one_eq_of_pos hn] using h
      refine ⟨hC, (a : golodShafarevich_gradedPart K ι (n - 1)) ⊗ₜ[K]
          (⟨FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i), hbasis⟩ : golodShafarevich_gradedPart K ι 1),
          ?_, ?_⟩
      · rw [LinearMap.mem_range]
        refine ⟨(⟨a, haA⟩ : A) ⊗ₜ[K] (⟨FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i), hbasis⟩ :
          golodShafarevich_gradedPart K ι 1), ?_⟩
        rw [TensorProduct.map_tmul]
        rfl
      · apply Subtype.ext
        simp only [golodShafarevich_gradedMulMapRight_tmul]
    · refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, ?_⟩
      apply Subtype.ext
      simp
    · intro y z hyT hzT iy iz
      rcases iy with ⟨hyC, zy, hyP, hzy⟩
      rcases iz with ⟨hzC, zz, hzP, hzz⟩
      refine ⟨Submodule.add_mem _ hyC hzC, zy + zz, Submodule.add_mem _ hyP hzP, ?_⟩
      rw [map_add, hzy, hzz]
      rfl
    · intro c y hyT iy
      rcases iy with ⟨hyC, zy, hyP, hzy⟩
      refine ⟨Submodule.smul_mem _ c hyC, c • zy, Submodule.smul_mem _ c hyP, ?_⟩
      rw [map_smul, hzy]
      rfl
  rcases hp with ⟨hC, z, hzP, hz⟩
  exact ⟨z, hzP, by simpa using hz⟩

lemma golodShafarevich_gradedMulMapRight_image_eq
    {K ι : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (A : Submodule K (golodShafarevich_gradedPart K ι (n - 1))) :
    let T := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
      x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    (LinearMap.range (TensorProduct.map A.subtype LinearMap.id)).map
      (golodShafarevich_gradedMulMapRight K ι hn) =
      Submodule.comap (golodShafarevich_gradedPart K ι n).subtype T := by
  intro T
  exact le_antisymm
    (golodShafarevich_gradedMulMapRight_image_subset (K := K) (ι := ι) hn A)
    (golodShafarevich_gradedMulMapRight_image_superset (K := K) (ι := ι) hn A)

noncomputable def golodShafarevich_gradedMulEquiv (K ι : Type*) [Field K] {n : ℕ} (hn : 0 < n) :
    golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1 ≃ₗ[K]
      golodShafarevich_gradedPart K ι n := by
  let bn := golodShafarevich_gradedPartBasis K ι n
  let bnm1 := golodShafarevich_gradedPartBasis K ι (n - 1)
  let b1 := golodShafarevich_gradedPartBasis K ι 1
  let bt : Module.Basis (golodShafarevich_words ι (n - 1) × golodShafarevich_words ι 1) K
      (golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1) :=
    bnm1.tensorProduct b1
  exact bt.equiv bn (golodShafarevich_wordsEquiv ι hn)

lemma golodShafarevich_gradedMulEquiv_toLinearMap (K ι : Type*) [Field K] {n : ℕ} (hn : 0 < n) :
    (golodShafarevich_gradedMulEquiv K ι hn :
      golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1 →ₗ[K]
        golodShafarevich_gradedPart K ι n) =
      golodShafarevich_gradedMulMapRight K ι hn := by
  let bn := golodShafarevich_gradedPartBasis K ι n
  let bnm1 := golodShafarevich_gradedPartBasis K ι (n - 1)
  let b1 := golodShafarevich_gradedPartBasis K ι 1
  let bt : Module.Basis (golodShafarevich_words ι (n - 1) × golodShafarevich_words ι 1) K
      (golodShafarevich_gradedPart K ι (n - 1) ⊗[K] golodShafarevich_gradedPart K ι 1) :=
    bnm1.tensorProduct b1
  apply Module.Basis.ext bt
  intro p
  dsimp [golodShafarevich_gradedMulEquiv, bt]
  rw [Module.Basis.equiv_apply]
  rw [Module.Basis.tensorProduct_apply]
  change bn (golodShafarevich_word_concat ι hn p) =
    golodShafarevich_gradedMulMapRight K ι hn (bnm1 p.1 ⊗ₜ[K] b1 p.2)
  apply Subtype.ext
  dsimp [bn, bnm1, b1]
  simp only [golodShafarevich_gradedMulMapRight_tmul,
    golodShafarevich_gradedPartBasis_apply]
  unfold golodShafarevich_word_concat
  rw [golodShafarevich_basisFreeMonoid_mul]

theorem golod_shafarevich_graded_mul_quotient_equiv
    {K ι : Type*} [Field K] [DecidableEq ι] (n : ℕ) (hn : 0 < n)
    (A : Submodule K (golodShafarevich_gradedPart K ι (n - 1))) :
    let V := golodShafarevich_gradedPart K ι
    let T := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
      x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    Nonempty ((TensorProduct K ((golodShafarevich_gradedPart K ι (n - 1)) ⧸ A)
        (golodShafarevich_gradedPart K ι 1)) ≃ₗ[K]
      (V n ⧸ Submodule.comap (V n).subtype T)) := by
  classical
  dsimp only
  let Ws := golodShafarevich_gradedPart K ι (n - 1)
  let Us := golodShafarevich_gradedPart K ι 1
  let Cs := golodShafarevich_gradedPart K ι n
  let W : Type _ := Ws
  let U : Type _ := Us
  let C : Type _ := Cs
  letI : AddCommGroup C := inferInstance
  letI : Module K C := inferInstance
  let A' : Submodule K W := A
  letI : AddCommGroup (W ⊗[K] U) := inferInstance
  letI : Module K (W ⊗[K] U) := inferInstance
  let T := Submodule.span K {x | ∃ a ∈ A, ∃ i : ι,
    x = (a : FreeAlgebra K ι) * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let P : Submodule K (W ⊗[K] U) := LinearMap.range (TensorProduct.map A'.subtype LinearMap.id)
  let e_mul : W ⊗[K] U ≃ₗ[K] C := golodShafarevich_gradedMulEquiv K ι hn
  let Q : Submodule K C := Submodule.map (e_mul : W ⊗[K] U →ₗ[K] C) P
  let e1 : (W ⧸ A') ⊗[K] U ≃ₗ[K] (W ⊗[K] U) ⧸ P := by
    dsimp [P]
    exact TensorProduct.quotientTensorEquiv (R := K) (M := W) (N := U) A'
  let e2 := Submodule.Quotient.equiv P Q e_mul rfl
  have himage : Q = Submodule.comap Cs.subtype T := by
    dsimp [Q, P, e_mul]
    rw [golodShafarevich_gradedMulEquiv_toLinearMap]
    simpa [W, U, C, Ws, Us, Cs, A', T] using golodShafarevich_gradedMulMapRight_image_eq (K := K) (ι := ι) hn A
  let R : Submodule K C := Submodule.comap Cs.subtype T
  let e3 := Submodule.quotEquivOfEq (p := Q) (p' := R) himage
  exact ⟨e1.trans (e2.trans e3)⟩

end Commons.Algebra.FreeAlgebra
