import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Matrix

open _root_.Matrix

noncomputable section

variable {n : ℕ}

/-- The submodule of antisymmetric matrices whose columns all lie in `S`. -/
def antisymColumnsSubmodule (S : Submodule ℂ (Fin n → ℂ)) :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | A.transpose = -A ∧ ∀ q : Fin n, (fun p => A p q) ∈ S}
  zero_mem' := by
    refine ⟨?_, fun q => S.zero_mem⟩
    ext i j; simp
  add_mem' := by
    intro A B hA hB
    refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_add, hA.1, hB.1]; abel
    · intro q
      have h : (fun p => (A + B) p q) = (fun p => A p q) + (fun p => B p q) := by ext p; rfl
      rw [h]; exact S.add_mem (hA.2 q) (hB.2 q)
  smul_mem' := by
    intro c A hA
    refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_smul, hA.1]
      exact smul_neg c A
    · intro q
      have h : (fun p => (c • A) p q) = c • (fun p => A p q) := by ext p; rfl
      rw [h]; exact S.smul_mem c (hA.2 q)

lemma mem_antisymColumnsSubmodule {S : Submodule ℂ (Fin n → ℂ)}
    {A : Matrix (Fin n) (Fin n) ℂ} :
    A ∈ antisymColumnsSubmodule S ↔ A.transpose = -A ∧ ∀ q : Fin n, (fun p => A p q) ∈ S :=
  Iff.rfl

lemma col_mem_iff_range (S : Submodule ℂ (Fin n → ℂ)) (A : Matrix (Fin n) (Fin n) ℂ) :
    (∀ q : Fin n, (fun p => A p q) ∈ S) ↔ LinearMap.range A.mulVecLin ≤ S := by
  rw [Matrix.range_mulVecLin]
  constructor
  · intro h
    rw [Submodule.span_le]
    rintro x ⟨q, rfl⟩
    exact h q
  · intro h q
    exact h (Submodule.subset_span ⟨q, rfl⟩)

/-! ### The standard coordinate subspace of dimension `r`. -/

/-- Vectors supported in the first `r` coordinates. -/
def coordSubmodule (n r : ℕ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∀ i : Fin n, r ≤ i.val → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by intro x y hx hy i hi; simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' := by intro c x hx i hi; simp only [Pi.smul_apply, hx i hi, smul_zero]

/-- Extend a function on the first `r` coordinates by zero. -/
def liftFun (n r : ℕ) (y : Fin r → ℂ) : Fin n → ℂ :=
  fun i => if hi : i.val < r then y ⟨i.val, hi⟩ else 0

def coordEquiv (n r : ℕ) (h : r ≤ n) : ↥(coordSubmodule n r) ≃ₗ[ℂ] (Fin r → ℂ) where
  toFun x := fun i => x.1 (Fin.castLE h i)
  map_add' := by intro x y; ext i; rfl
  map_smul' := by intro c x; ext i; rfl
  invFun y := ⟨liftFun n r y, by
    intro j hj
    have hnot : ¬ j.val < r := by omega
    simp only [liftFun]
    exact dif_neg hnot⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext j
    simp only [liftFun]
    split_ifs with hj
    · exact congrArg x.1 (Fin.ext (by rw [Fin.val_castLE]))
    · exact (x.2 j (by omega)).symm
  right_inv := by
    intro y
    funext i
    have hi : (Fin.castLE h i).val < r := by rw [Fin.val_castLE]; exact i.2
    simp only [liftFun, dif_pos hi]
    exact congrArg y (Fin.ext (by rw [Fin.val_castLE]))

lemma finrank_coordSubmodule (n r : ℕ) (h : r ≤ n) :
    Module.finrank ℂ ↥(coordSubmodule n r) = r := by
  rw [LinearEquiv.finrank_eq (coordEquiv n r h), Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-! ### Extending a linear equivalence between subspaces. -/

theorem exists_linearEquiv_map_eq {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S T : Submodule K V)
    (h : Module.finrank K ↥S = Module.finrank K ↥T) :
    ∃ e : V ≃ₗ[K] V, Submodule.map (e : V →ₗ[K] V) S = T := by
  let f : ↥S ≃ₗ[K] ↥T := LinearEquiv.ofFinrankEq _ _ h
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e, ?_⟩
  have hcomp : (e : V →ₗ[K] V).comp S.subtype = T.subtype.comp (f : ↥S →ₗ[K] ↥T) := by
    ext x
    exact (he x).symm
  rw [← Submodule.map_subtype_top S, ← Submodule.map_comp, hcomp, Submodule.map_comp,
      Submodule.map_top, LinearMap.range_eq_top.mpr f.surjective, Submodule.map_top,
      Submodule.range_subtype]


/-! ### Antisymmetric square matrices and their dimension. -/

/-- The submodule of antisymmetric matrices `Aᵀ = -A`. -/
def skewMatrixSubmodule (k : ℕ) : Submodule ℂ (Matrix (Fin k) (Fin k) ℂ) where
  carrier := {A | A.transpose = -A}
  zero_mem' := by ext i j; simp
  add_mem' := by
    intro A B hA hB
    change (A + B).transpose = -(A + B)
    rw [Matrix.transpose_add, hA, hB]
    abel
  smul_mem' := by
    intro c A hA
    change (c • A).transpose = -(c • A)
    rw [Matrix.transpose_smul, hA]
    exact smul_neg c A

lemma skew_apply_swap {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A ∈ skewMatrixSubmodule k) (i j : Fin k) : A j i = - A i j := by
  have h := congrFun (congrFun hA i) j
  simpa using h

lemma skew_diag_zero {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A ∈ skewMatrixSubmodule k) (i : Fin k) : A i i = 0 := by
  have h := skew_apply_swap hA i i
  have h2 : (2 : ℂ) * A i i = 0 := by
    rw [two_mul, ← neg_eq_iff_add_eq_zero]
    exact h.symm
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Restriction to the strictly upper triangle. -/
def skewUpper (k : ℕ) :
    ↥(skewMatrixSubmodule k) →ₗ[ℂ] ({p : Fin k × Fin k // p.1 < p.2} → ℂ) where
  toFun A := fun p => A.1 p.1.1 p.1.2
  map_add' := by intro A B; funext p; rfl
  map_smul' := by intro c A; funext p; rfl

/-- The antisymmetric matrix determined by its strict upper triangle. -/
def invSkew (k : ℕ) (c : {p : Fin k × Fin k // p.1 < p.2} → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => if hij : i.val < j.val then c ⟨(i, j), hij⟩
    else if hji : j.val < i.val then - c ⟨(j, i), hji⟩ else 0

lemma invSkew_skew (k : ℕ) (c : {p : Fin k × Fin k // p.1 < p.2} → ℂ) :
    (invSkew k c).transpose = -(invSkew k c) := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  rcases lt_trichotomy i.val j.val with h | h | h
  · have h1 : ¬ j.val < i.val := by omega
    simp only [invSkew, dif_pos h, dif_neg h1]
  · have hij : i = j := Fin.ext h
    subst hij
    simp only [invSkew, dif_neg (lt_irrefl i.val), neg_zero]
  · have h1 : ¬ i.val < j.val := by omega
    simp only [invSkew, dif_pos h, dif_neg h1, neg_neg]

lemma skewUpper_invSkew (k : ℕ) (c : {p : Fin k × Fin k // p.1 < p.2} → ℂ) :
    skewUpper k ⟨invSkew k c, invSkew_skew k c⟩ = c := by
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  change invSkew k c i j = c ⟨(i, j), hij⟩
  have hij' : i.val < j.val := hij
  simp only [invSkew]
  rw [dif_pos hij']

lemma skewUpper_ker (k : ℕ) : LinearMap.ker (skewUpper k) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro A B hAB
  apply Subtype.ext
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hh := congrFun hAB ⟨(i, j), h⟩
    change A.1 i j = B.1 i j at hh
    exact hh
  · have hij : i = j := Fin.ext h
    subst hij
    rw [skew_diag_zero A.2 i, skew_diag_zero B.2 i]
  · have hh := congrFun hAB ⟨(j, i), h⟩
    change A.1 j i = B.1 j i at hh
    rw [skew_apply_swap A.2 i j, skew_apply_swap B.2 i j] at hh
    exact neg_injective hh

lemma skewUpper_range (k : ℕ) : LinearMap.range (skewUpper k) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro c
  exact ⟨⟨invSkew k c, invSkew_skew k c⟩, skewUpper_invSkew k c⟩

theorem finrank_skewMatrixSubmodule (k : ℕ) :
    Module.finrank ℂ ↥(skewMatrixSubmodule k) = k * (k - 1) / 2 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (skewUpper k)
  rw [skewUpper_range, skewUpper_ker, finrank_top, finrank_bot ℂ _, add_zero] at hrank
  rw [← hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
  have h1 : (Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)) =
      {x ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)) | x.1 < x.2} := by
    rw [Finset.univ_product_univ]
  rw [h1, Finset.card_product_filter_lt, Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]



/-! ### Identifying `antisymColumnsSubmodule (coordSubmodule n r)` with antisymmetric `r × r` matrices. -/

def extractMat (n r : ℕ) (h : r ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

def embedMat (n r : ℕ) (_h : r ≤ n) (C : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if hi : i.val < r then (if hj : j.val < r then C ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0) else 0

lemma extractMat_transpose (n r : ℕ) (h : r ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    (extractMat n r h A).transpose = extractMat n r h A.transpose := by
  ext i j; rfl

lemma extractMat_neg (n r : ℕ) (h : r ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    extractMat n r h (-A) = -(extractMat n r h A) := by
  ext i j; rfl

lemma extractMat_add (n r : ℕ) (h : r ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) :
    extractMat n r h (A + B) = extractMat n r h A + extractMat n r h B := by
  ext i j; rfl

lemma extractMat_smul (n r : ℕ) (h : r ≤ n) (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    extractMat n r h (c • A) = c • extractMat n r h A := by
  ext i j; rfl

lemma extractMat_skew (n r : ℕ) (h : r ≤ n) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.transpose = -A) : extractMat n r h A ∈ skewMatrixSubmodule r := by
  change (extractMat n r h A).transpose = -(extractMat n r h A)
  rw [extractMat_transpose, hA, extractMat_neg]

lemma extractMat_embedMat (n r : ℕ) (h : r ≤ n) (C : Matrix (Fin r) (Fin r) ℂ) :
    extractMat n r h (embedMat n r h C) = C := by
  ext i j
  have hi : (Fin.castLE h i).val < r := by rw [Fin.val_castLE]; exact i.2
  have hj : (Fin.castLE h j).val < r := by rw [Fin.val_castLE]; exact j.2
  simp only [extractMat, Matrix.submatrix_apply, embedMat, dif_pos hi, dif_pos hj]
  exact congrArg₂ C (Fin.ext (by rw [Fin.val_castLE])) (Fin.ext (by rw [Fin.val_castLE]))

lemma embedMat_neg (n r : ℕ) (h : r ≤ n) (C : Matrix (Fin r) (Fin r) ℂ) :
    embedMat n r h (-C) = -(embedMat n r h C) := by
  ext i j
  simp only [embedMat, Matrix.neg_apply]
  split_ifs <;> simp

lemma embedMat_transpose (n r : ℕ) (h : r ≤ n) (C : Matrix (Fin r) (Fin r) ℂ) :
    (embedMat n r h C).transpose = embedMat n r h C.transpose := by
  ext i j
  simp only [Matrix.transpose_apply, embedMat]
  split_ifs <;> simp

lemma embedMat_mem (n r : ℕ) (h : r ≤ n) {C : Matrix (Fin r) (Fin r) ℂ}
    (hC : C.transpose = -C) : embedMat n r h C ∈ antisymColumnsSubmodule (coordSubmodule n r) := by
  refine ⟨?_, ?_⟩
  · rw [embedMat_transpose, hC, embedMat_neg]
  · intro q i hi
    have hnot : ¬ i.val < r := by omega
    show (embedMat n r h C) i q = 0
    simp only [embedMat, dif_neg hnot]

lemma embedMat_extractMat (n r : ℕ) (h : r ≤ n) {A : Matrix (Fin n) (Fin n) ℂ}
    (hsk : A.transpose = -A) (hcol : ∀ i j : Fin n, r ≤ i.val → A i j = 0) :
    embedMat n r h (extractMat n r h A) = A := by
  ext i j
  simp only [embedMat]
  by_cases hi : i.val < r
  · by_cases hj : j.val < r
    · rw [dif_pos hi, dif_pos hj]
      change A (Fin.castLE h ⟨i.val, hi⟩) (Fin.castLE h ⟨j.val, hj⟩) = A i j
      exact congrArg₂ A (Fin.ext (by rw [Fin.val_castLE])) (Fin.ext (by rw [Fin.val_castLE]))
    · rw [dif_pos hi, dif_neg hj]
      have h1 : A j i = 0 := hcol j i (by omega)
      have h2 : A j i = -A i j := skew_apply_swap hsk i j
      rw [h1] at h2
      exact (neg_eq_zero.mp h2.symm).symm
  · rw [dif_neg hi]
    exact (hcol i j (by omega)).symm

/-- The isomorphism between skew matrices concentrated in the top-left `r × r` block and
antisymmetric `r × r` matrices. -/
def blockEquiv (n r : ℕ) (h : r ≤ n) :
    ↥(antisymColumnsSubmodule (coordSubmodule n r)) ≃ₗ[ℂ] ↥(skewMatrixSubmodule r) where
  toFun A := ⟨extractMat n r h A.1, extractMat_skew n r h (mem_antisymColumnsSubmodule.mp A.2).1⟩
  map_add' := by intro A B; apply Subtype.ext; exact extractMat_add n r h A.1 B.1
  map_smul' := by intro c A; apply Subtype.ext; exact extractMat_smul n r h c A.1
  invFun C := ⟨embedMat n r h C.1, embedMat_mem n r h C.2⟩
  left_inv := by
    intro A
    apply Subtype.ext
    exact embedMat_extractMat n r h (mem_antisymColumnsSubmodule.mp A.2).1
      (fun i j hij => by simpa using (mem_antisymColumnsSubmodule.mp A.2).2 j i hij)
  right_inv := by
    intro C
    apply Subtype.ext
    exact extractMat_embedMat n r h C.1

theorem finrank_antisymColumnsSubmodule_coord (n r : ℕ) (h : r ≤ n) :
    Module.finrank ℂ ↥(antisymColumnsSubmodule (coordSubmodule n r)) = r * (r - 1) / 2 := by
  rw [LinearEquiv.finrank_eq (blockEquiv n r h), finrank_skewMatrixSubmodule r]


/-! ### The main dimension computation. -/

theorem finrank_antisymColumnsSubmodule (S : Submodule ℂ (Fin n → ℂ)) (r : ℕ)
    (hr : Module.finrank ℂ ↥S = r) :
    Module.finrank ℂ ↥(antisymColumnsSubmodule S) = r * (r - 1) / 2 := by
  have hn : r ≤ n := by
    have h1 : Module.finrank ℂ ↥S ≤ Module.finrank ℂ (Fin n → ℂ) := Submodule.finrank_le S
    rw [hr, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    exact h1
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_eq S (coordSubmodule n r)
    (by rw [hr, finrank_coordSubmodule n r hn])
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℂ,
      Q.mulVecLin = (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :=
    ⟨(Matrix.toLin').symm (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)),
      LinearEquiv.apply_symm_apply (Matrix.toLin') (g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Matrix (Fin n) (Fin n) ℂ,
      Q'.mulVecLin = (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :=
    ⟨(Matrix.toLin').symm (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)),
      LinearEquiv.apply_symm_apply (Matrix.toLin') (g.symm : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))⟩
  have hQinj : Function.Injective Q.mulVecLin := by rw [hQ]; exact g.injective
  have hgQ : Submodule.map Q.mulVecLin S = coordSubmodule n r := by rw [hQ]; exact hg
  have hQQ' : Q * Q' = 1 := by
    have key : (Q * Q').mulVecLin = (1 : Matrix (Fin n) (Fin n) ℂ).mulVecLin := by
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one, hQ, hQ']
      ext x; simp
    have h2 : Matrix.toLin' (Q * Q') = Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply']; exact key
    exact Matrix.toLin'.injective h2
  have hQ'Q : Q' * Q = 1 := by
    have key : (Q' * Q).mulVecLin = (1 : Matrix (Fin n) (Fin n) ℂ).mulVecLin := by
      rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_one, hQ', hQ]
      ext x; simp
    have h2 : Matrix.toLin' (Q' * Q) = Matrix.toLin' (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply']; exact key
    exact Matrix.toLin'.injective h2
  have hTT : Qᵀ * (Q')ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hQ'Q, Matrix.transpose_one]
  have hsurj : LinearMap.range (Qᵀ).mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨((Q')ᵀ).mulVecLin y, ?_⟩
    have hcomp : (Qᵀ).mulVecLin (((Q')ᵀ).mulVecLin y) = ((Qᵀ * (Q')ᵀ).mulVecLin) y := by
      rw [Matrix.mulVecLin_mul]; rfl
    rw [hcomp, hTT, Matrix.mulVecLin_one]
    rfl
  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => Q * A * Qᵀ
      map_add' := by intro A B; rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c A; rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hleft : ∀ A : Matrix (Fin n) (Fin n) ℂ, Q' * (Φ A) * (Q')ᵀ = A := by
    intro A
    change Q' * (Q * A * Qᵀ) * (Q')ᵀ = A
    calc Q' * (Q * A * Qᵀ) * (Q')ᵀ = (Q' * Q) * A * (Qᵀ * (Q')ᵀ) := by noncomm_ring
      _ = A := by rw [hQ'Q, hTT, one_mul, mul_one]
  have hright : ∀ B : Matrix (Fin n) (Fin n) ℂ, Q * (Q' * B * (Q')ᵀ) * Qᵀ = B := by
    intro B
    calc Q * (Q' * B * (Q')ᵀ) * Qᵀ = (Q * Q') * B * ((Q')ᵀ * Qᵀ) := by noncomm_ring
      _ = B := by rw [hQQ', ← Matrix.transpose_mul, hQQ', Matrix.transpose_one, one_mul, mul_one]
  have hrng : ∀ A : Matrix (Fin n) (Fin n) ℂ, LinearMap.range (Φ A).mulVecLin =
      Submodule.map Q.mulVecLin (LinearMap.range A.mulVecLin) := by
    intro A
    change LinearMap.range (Q * A * Qᵀ).mulVecLin =
      Submodule.map Q.mulVecLin (LinearMap.range A.mulVecLin)
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, hsurj,
      Submodule.map_top, LinearMap.range_comp]
  have hskew : ∀ A : Matrix (Fin n) (Fin n) ℂ, (Φ A).transpose = Q * A.transpose * Qᵀ := by
    intro A
    change (Q * A * Qᵀ).transpose = Q * A.transpose * Qᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
  have hmem : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      A ∈ antisymColumnsSubmodule S ↔ Φ A ∈ antisymColumnsSubmodule (coordSubmodule n r) := by
    intro A
    have h1 : A ∈ antisymColumnsSubmodule S ↔
        (A.transpose = -A ∧ LinearMap.range A.mulVecLin ≤ S) := by
      rw [mem_antisymColumnsSubmodule, col_mem_iff_range]
    have h2 : Φ A ∈ antisymColumnsSubmodule (coordSubmodule n r) ↔
        ((Φ A).transpose = -(Φ A) ∧ LinearMap.range (Φ A).mulVecLin ≤ coordSubmodule n r) := by
      rw [mem_antisymColumnsSubmodule, col_mem_iff_range]
    rw [h1, h2]
    constructor
    · rintro ⟨hA, hrange⟩
      refine ⟨?_, ?_⟩
      · rw [hskew, hA]
        change Q * (-A) * Qᵀ = -(Q * A * Qᵀ)
        rw [Matrix.mul_neg, Matrix.neg_mul]
      · rw [hrng, ← hgQ]
        exact Submodule.map_mono hrange
    · rintro ⟨hB1, hrange⟩
      refine ⟨?_, ?_⟩
      · have h2 : Q * A.transpose * Qᵀ = -(Q * A * Qᵀ) := by rw [← hskew]; exact hB1
        have e1 : Q' * (Q * A.transpose * Qᵀ) * (Q')ᵀ = A.transpose := hleft A.transpose
        have e2 : Q' * (Q * A * Qᵀ) * (Q')ᵀ = A := hleft A
        rw [h2, Matrix.mul_neg, Matrix.neg_mul, e2] at e1
        exact e1.symm
      · rw [hrng, ← hgQ] at hrange
        exact (Submodule.map_le_map_iff_of_injective hQinj _ _).mp hrange
  have hbij : Function.Bijective Φ := by
    refine ⟨?_, fun B => ⟨Q' * B * (Q')ᵀ, hright B⟩⟩
    intro A B h
    have h1 : Q' * (Φ A) * (Q')ᵀ = Q' * (Φ B) * (Q')ᵀ := by rw [h]
    rw [hleft A, hleft B] at h1
    exact h1
  let eΦ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearEquiv.ofBijective Φ hbij
  have hmap : (antisymColumnsSubmodule S).map
        (eΦ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) =
      antisymColumnsSubmodule (coordSubmodule n r) := by
    ext B
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨A, hA, rfl⟩
      change Φ A ∈ antisymColumnsSubmodule (coordSubmodule n r)
      exact (hmem A).mp hA
    · intro hB
      refine ⟨eΦ.symm B, ?_, eΦ.apply_symm_apply B⟩
      have h1 : Φ (eΦ.symm B) = B := eΦ.apply_symm_apply B
      have h2 : Φ (eΦ.symm B) ∈ antisymColumnsSubmodule (coordSubmodule n r) := by
        rw [h1]; exact hB
      exact (hmem (eΦ.symm B)).mpr h2
  calc Module.finrank ℂ ↥(antisymColumnsSubmodule S)
      = Module.finrank ℂ ↥((antisymColumnsSubmodule S).map
          (eΦ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)) :=
        LinearEquiv.finrank_eq (eΦ.submoduleMap (antisymColumnsSubmodule S))
    _ = Module.finrank ℂ ↥(antisymColumnsSubmodule (coordSubmodule n r)) := by rw [hmap]
    _ = r * (r - 1) / 2 := finrank_antisymColumnsSubmodule_coord n r hn

theorem finrank_antisym_columns_le {n : ℕ} (S : Submodule ℂ (Fin n → ℂ)) (r : ℕ)
    (hr : Module.finrank ℂ ↥S = r) :
    Module.finrank ℂ ↥(Submodule.span ℂ {A : Matrix (Fin n) (Fin n) ℂ |
      A.transpose = -A ∧ ∀ q : Fin n, (fun p => A p q) ∈ S}) = r * (r - 1) / 2 := by
  have hspan : (Submodule.span ℂ {A : Matrix (Fin n) (Fin n) ℂ |
      A.transpose = -A ∧ ∀ q : Fin n, (fun p => A p q) ∈ S}) = antisymColumnsSubmodule S :=
    Submodule.span_eq (antisymColumnsSubmodule S)
  rw [hspan]
  exact finrank_antisymColumnsSubmodule S r hr

end

end Commons.LinearAlgebra.Matrix