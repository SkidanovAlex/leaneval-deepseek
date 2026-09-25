import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.FunLike.Fintype
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Matrix MvPolynomial

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Alternating

/-- The generic alternating matrix of size `n` over a field `K`. -/
noncomputable def genAlt (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial {p : Fin n × Fin n // p.1 < p.2} K) :=
  fun i j => if h : i < j then X ⟨(i, j), h⟩ else if h' : j < i then -X ⟨(j, i), h'⟩ else 0

lemma genAlt_apply_lt (K : Type*) [Field K] {n : ℕ} {i j : Fin n} (h : i < j) :
    genAlt K n i j = X ⟨(i, j), h⟩ := by
  rw [genAlt]; exact dif_pos h

lemma genAlt_apply_gt (K : Type*) [Field K] {n : ℕ} {i j : Fin n} (h : j < i) :
    genAlt K n i j = -X ⟨(j, i), h⟩ := by
  rw [genAlt, dif_neg (not_lt_of_gt h)]; exact dif_pos h

lemma genAlt_apply_eq (K : Type*) [Field K] {n : ℕ} (i : Fin n) : genAlt K n i i = 0 := by
  rw [genAlt, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

lemma genAlt_transpose (K : Type*) [Field K] (n : ℕ) : (genAlt K n)ᵀ = -genAlt K n := by
  apply Matrix.ext
  intro i j
  rw [Matrix.transpose_apply, Matrix.neg_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [genAlt_apply_gt K h, genAlt_apply_lt K h]
  · subst h; simp [genAlt_apply_eq]
  · rw [genAlt_apply_lt K h, genAlt_apply_gt K h, neg_neg]

lemma genAlt_map {K R : Type*} [Field K] [CommRing R] (f : K →+* R) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hskew : Mᵀ = -M) (hdiag : ∀ i, M i i = 0) :
    (genAlt K n).map (MvPolynomial.eval₂Hom f (fun p => M p.val.1 p.val.2)) = M := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [genAlt_apply_lt K h, MvPolynomial.eval₂Hom_X']
  · subst h; rw [genAlt_apply_eq, map_zero, hdiag]
  · rw [genAlt_apply_gt K h, map_neg, MvPolynomial.eval₂Hom_X']
    have h1 : M j i = -M i j := by
      have := congrFun (congrFun hskew i) j
      simpa [Matrix.transpose_apply, Matrix.neg_apply] using this
    rw [h1, neg_neg]

lemma genAlt_skew_entry (K : Type*) [Field K] {n : ℕ} (i j : Fin n) :
    genAlt K n j i = -genAlt K n i j := by
  have := congrFun (congrFun (genAlt_transpose K n) i) j
  simpa [Matrix.transpose_apply, Matrix.neg_apply] using this
/-- The Schur complement of an alternating block matrix whose top-left block is `!![0,c;-c,0]`
is again alternating. -/
lemma schur_isAlt {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (c : R) [Invertible c] (B : Matrix (Fin 2) ι R) (C : Matrix ι (Fin 2) R) (D : Matrix ι ι R)
    (hB0 : ∀ i, B 0 i = -C i 0) (hB1 : ∀ i, B 1 i = -C i 1)
    (hD : ∀ i j, D j i = -D i j) (hD0 : ∀ i, D i i = 0) :
    (D - C * !![0, -⅟c; ⅟c, 0] * B)ᵀ = -(D - C * !![0, -⅟c; ⅟c, 0] * B) ∧
      ∀ i, (D - C * !![0, -⅟c; ⅟c, 0] * B) i i = 0 := by
  have hX10 : (!![0, -⅟c; ⅟c, 0] : Matrix (Fin 2) (Fin 2) R) 1 0 = ⅟c := rfl
  have hX01 : (!![0, -⅟c; ⅟c, 0] : Matrix (Fin 2) (Fin 2) R) 0 1 = -⅟c := rfl
  have hX00 : (!![0, -⅟c; ⅟c, 0] : Matrix (Fin 2) (Fin 2) R) 0 0 = 0 := rfl
  have hX11 : (!![0, -⅟c; ⅟c, 0] : Matrix (Fin 2) (Fin 2) R) 1 1 = 0 := rfl
  constructor
  · ext i j
    have hDji : D j i = -D i j := hD i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
      Fin.sum_univ_two, hX10, hX01, hX00, hX11, hB0, hB1, hDji]
    ring
  · intro i
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hX10, hX01, hX00, hX11,
      hB0 i, hB1 i, hD0]
    ring
/-- If an element of an integrally closed domain is a square in a fraction field, it is a square
in the ring. -/
lemma isSquare_of_isSquare_algebraMap {R K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing K] [Algebra R K] [IsFractionRing R K] {f : R}
    (h : IsSquare (algebraMap R K f)) : IsSquare f := by
  obtain ⟨y, hy⟩ := h
  have hy2 : y ^ 2 = algebraMap R K f := by rw [pow_two]; exact hy.symm
  have hint : IsIntegral R (y ^ 2) := by rw [hy2]; exact isIntegral_algebraMap
  obtain ⟨g, hg⟩ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (x := y) (n := 2)
      (by norm_num) hint
  exact ⟨g, by
    apply IsFractionRing.injective R K
    rw [map_mul, hg]; exact hy⟩


lemma finSumFinEquiv_symm_zero (m : ℕ) : finSumFinEquiv.symm (0 : Fin (2 + m)) = Sum.inl 0 := by
  rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
  exact Fin.ext (by simp)

lemma finSumFinEquiv_symm_one (m : ℕ) : finSumFinEquiv.symm (1 : Fin (2 + m)) = Sum.inl 1 := by
  rw [Equiv.symm_apply_eq, finSumFinEquiv_apply_left]
  exact Fin.ext (by simp [Nat.mod_eq_of_lt (show 1 < 2 + m by omega)])

lemma finCongr_zero (m : ℕ) (h : m + 2 = 2 + m) :
    finCongr h (0 : Fin (m + 2)) = (0 : Fin (2 + m)) := by
  apply Fin.ext; rw [finCongr_apply, Fin.val_cast]; simp

lemma finCongr_one (m : ℕ) (h : m + 2 = 2 + m) :
    finCongr h (1 : Fin (m + 2)) = (1 : Fin (2 + m)) := by
  apply Fin.ext; rw [finCongr_apply, Fin.val_cast]
  simp [Nat.mod_eq_of_lt (show 1 < 2 + m by omega)]

/-- The variables of the generic alternating matrix of size `n`. -/
abbrev GenVar (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

theorem genAlt_isSquare (K : Type*) [Field K] : ∀ n, IsSquare (genAlt K n).det := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · refine ⟨1, ?_⟩
        rw [show genAlt K 0 = 1 from Subsingleton.elim _ _, Matrix.det_one, one_mul]
      · have h0 : genAlt K 1 = 0 := by
          apply Matrix.ext
          intro i j
          fin_cases i; fin_cases j
          exact genAlt_apply_eq K 0
        refine ⟨0, ?_⟩
        rw [h0, Matrix.det_zero, mul_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩

      -- main step: n = m + 2
      have hnm : m + 2 = 2 + m := by omega
      let e : Fin (m + 2) ≃ Fin 2 ⊕ Fin m := (finCongr hnm).trans finSumFinEquiv.symm
      let R := MvPolynomial (GenVar (m + 2)) K
      let F := FractionRing R
      let G : Matrix (Fin (m + 2)) (Fin (m + 2)) F :=
        (algebraMap R F : R →+* F).mapMatrix (genAlt K (m + 2))
      let M : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) F := Matrix.reindex e e G
      let Ab : Matrix (Fin 2) (Fin 2) F := fun a b => M (Sum.inl a) (Sum.inl b)
      let Bb : Matrix (Fin 2) (Fin m) F := fun a j => M (Sum.inl a) (Sum.inr j)
      let Cb : Matrix (Fin m) (Fin 2) F := fun i a => M (Sum.inr i) (Sum.inl a)
      let Db : Matrix (Fin m) (Fin m) F := fun i j => M (Sum.inr i) (Sum.inr j)
      have hM : M = Matrix.fromBlocks Ab Bb Cb Db := by
        ext i j
        rcases i with a | i <;> rcases j with b | j <;> rfl
      have hG : ∀ i j : Fin (m + 2), G i j = -G j i := by
        intro i j
        simp only [G, RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [genAlt_skew_entry K j i, map_neg]
      have hMs : ∀ a b, M a b = -M b a := by
        intro a b
        simp only [M, Matrix.reindex_apply, Matrix.submatrix_apply]
        exact hG _ _
      have hB0 : ∀ i, Bb 0 i = -Cb i 0 := fun i => hMs (Sum.inl 0) (Sum.inr i)
      have hB1 : ∀ i, Bb 1 i = -Cb i 1 := fun i => hMs (Sum.inl 1) (Sum.inr i)
      have hD : ∀ i j, Db j i = -Db i j := fun i j => hMs (Sum.inr j) (Sum.inr i)
      have hD0 : ∀ i, Db i i = 0 := by
        intro i
        simp only [Db, M, Matrix.reindex_apply, Matrix.submatrix_apply, G, RingHom.mapMatrix_apply,
          Matrix.map_apply]
        rw [genAlt_apply_eq, map_zero]
      have he0 : e 0 = Sum.inl 0 := by
        simp only [e, Equiv.trans_apply, finCongr_zero m hnm]
        exact finSumFinEquiv_symm_zero m
      have he1 : e 1 = Sum.inl 1 := by
        simp only [e, Equiv.trans_apply, finCongr_one m hnm]
        exact finSumFinEquiv_symm_one m
      have hes0 : e.symm (Sum.inl 0) = 0 := by rw [Equiv.symm_apply_eq, he0]
      have hes1 : e.symm (Sum.inl 1) = 1 := by rw [Equiv.symm_apply_eq, he1]
      set x : F := G 0 1 with hxdef
      have hx0 : x ≠ 0 := by
        rw [hxdef]
        simp only [G, RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [genAlt_apply_lt K (by norm_num : (0 : Fin (m + 2)) < 1)]
        intro h
        exact MvPolynomial.X_ne_zero _ (IsFractionRing.injective R F (by rw [h, map_zero]))
      have hAb00 : Ab 0 0 = 0 := by
        simp only [Ab, M, Matrix.reindex_apply, Matrix.submatrix_apply, hes0, G,
          RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [genAlt_apply_eq, map_zero]
      have hAb11 : Ab 1 1 = 0 := by
        simp only [Ab, M, Matrix.reindex_apply, Matrix.submatrix_apply, hes1, G,
          RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [genAlt_apply_eq, map_zero]
      have hAb01 : Ab 0 1 = x := by
        rw [hxdef]
        simp only [Ab, M, Matrix.reindex_apply, Matrix.submatrix_apply, hes0, hes1, G,
          RingHom.mapMatrix_apply, Matrix.map_apply]
      have hAb10 : Ab 1 0 = -x := by
        rw [hxdef]
        simp only [Ab, M, Matrix.reindex_apply, Matrix.submatrix_apply, hes0, hes1, G,
          RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [genAlt_apply_lt K (by norm_num : (0 : Fin (m + 2)) < 1),
          genAlt_apply_gt K (by norm_num : (1 : Fin (m + 2)) > 0), map_neg]
      have hAb : Ab = !![0, x; -x, 0] := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [hAb00, hAb01, hAb10, hAb11]
      have hAbdet : Ab.det = x * x := by
        rw [hAb, Matrix.det_fin_two]
        simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
        ring
      have hxunit : IsUnit x := isUnit_iff_ne_zero.mpr hx0
      letI : Invertible x := hxunit.invertible
      have hneg : -x * -⅟x = 1 := by rw [neg_mul_neg, mul_invOf_self]
      have hAbmul : Ab * !![0, -⅟x; ⅟x, 0] = 1 := by
        rw [hAb, Matrix.mul_fin_two, Matrix.one_fin_two]
        ext a b <;> fin_cases a <;> fin_cases b <;>
        · simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
            mul_zero, zero_mul, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero,
            mul_invOf_self, hneg]
      have hAbunit : IsUnit Ab := isUnit_iff_exists_inv.mpr ⟨_, hAbmul⟩
      letI : Invertible Ab := hAbunit.invertible
      have hAbinv : ⅟Ab = !![0, -⅟x; ⅟x, 0] := invOf_eq_right_inv hAbmul
      set Sc : Matrix (Fin m) (Fin m) F := Db - Cb * !![0, -⅟x; ⅟x, 0] * Bb with hScdef
      have hScS : Scᵀ = -Sc := (schur_isAlt x Bb Cb Db hB0 hB1 hD hD0).1
      have hSc0 : ∀ i, Sc i i = 0 := (schur_isAlt x Bb Cb Db hB0 hB1 hD hD0).2
      have hIHdet : IsSquare Sc.det := by
        have hih := ih m (by omega)
        have hspec := hih.map (MvPolynomial.eval₂Hom
          ((algebraMap R F : R →+* F).comp MvPolynomial.C)
          (fun p : GenVar m => Sc p.val.1 p.val.2))
        rw [RingHom.map_det] at hspec
        rw [RingHom.mapMatrix_apply] at hspec
        rwa [genAlt_map ((algebraMap R F : R →+* F).comp MvPolynomial.C) Sc hScS hSc0] at hspec
      have hkey : (algebraMap R F) ((genAlt K (m + 2)).det) = x * x * Sc.det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply]
        rw [show (genAlt K (m + 2)).map (algebraMap R F) = G from rfl]
        rw [show G.det = M.det from (Matrix.det_reindex_self e G).symm]
        rw [hM, Matrix.det_fromBlocks₁₁, hAbinv, hAb, Matrix.det_fin_two]
        simp only [Sc, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
        ring
      have hsq : IsSquare (algebraMap R F ((genAlt K (m + 2)).det)) := by
        obtain ⟨s, hs⟩ := hIHdet
        refine ⟨x * s, ?_⟩
        rw [hkey, hs]
        ring
      exact isSquare_of_isSquare_algebraMap hsq

/-- Any alternating matrix over a polynomial ring (over a field) has a square determinant. -/
theorem exists_sq_det_of_alt {K : Type*} [Field K] {τ : Type*} [Fintype τ] [DecidableEq τ]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial τ K))
    (hskew : Mᵀ = -M) (hdiag : ∀ i, M i i = 0) :
    ∃ g : MvPolynomial τ K, g * g = M.det := by
  obtain ⟨g, hg⟩ := genAlt_isSquare K n
  refine ⟨MvPolynomial.eval₂Hom MvPolynomial.C (fun p : GenVar n => M p.val.1 p.val.2) g, ?_⟩
  rw [← map_mul, ← hg, RingHom.map_det, RingHom.mapMatrix_apply,
    genAlt_map MvPolynomial.C M hskew hdiag]

/-- If a bilinear form is left-nondegenerate, then the determinant of its matrix in any basis
is nonzero. -/
lemma det_toMatrix_ne_zero_of_nondegenerate {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) {B : V →ₗ[K] V →ₗ[K] K}
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0) :
    (LinearMap.BilinForm.toMatrix b B).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hx : b.equivFun.symm v = 0 := hnd _ (by
    intro w
    have hb := LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B (b.equivFun.symm v) w
    rw [hb]
    have h1 : ⇑(b.repr (b.equivFun.symm v)) = v := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [h1, Matrix.dotProduct_mulVec, hv, zero_dotProduct])
  have h2 : v = 0 := by
    have h3 : b.equivFun (b.equivFun.symm v) = b.equivFun (0 : V) := congrArg b.equivFun hx
    rw [LinearEquiv.apply_symm_apply, map_zero] at h3
    exact h3
  exact hv0 h2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
open scoped Classical in
/-- Core counting argument, matrix form: if `A_1,…,A_t` are alternating matrices spanning a space
of nondegenerate forms, then `2t ≤ n`. -/
theorem core_matrix {p : ℕ} [Fact p.Prime] {n t : ℕ}
    (A : Fin t → Matrix (Fin n) (Fin n) (ZMod p))
    (hli : ∀ x : Fin t → ZMod p, (∑ k, x k • A k) = 0 → x = 0)
    (hskew : ∀ k, (A k)ᵀ = -(A k)) (hdiag : ∀ k i, A k i i = 0)
    (hnd : ∀ x : Fin t → ZMod p, x ≠ 0 → ∀ v : Fin n → ZMod p,
      (∑ k, x k • A k) *ᵥ v = 0 → v = 0) :
    2 * t ≤ n := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have ht0 : t = 0 := by
      by_contra ht0
      obtain ⟨k⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero ht0)
      have h0 : (Pi.single k 1 : Fin t → ZMod p) = 0 := by
        apply hli
        have hsum : (∑ k', (Pi.single k 1 : Fin t → ZMod p) k' • A k') = A k := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro b _ hb; simp [Pi.single_eq_of_ne hb]
          · intro hk; exact absurd (Finset.mem_univ k) hk
        rw [hsum]
        exact Subsingleton.elim _ _
      have h1 := congrFun h0 k
      simp at h1
    omega
  · haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
    by_contra hcon
    have hlt : n < 2 * t := not_le.mp hcon
    let Mp : Matrix (Fin n) (Fin n) (MvPolynomial (Fin t) (ZMod p)) :=
      Matrix.of fun i j => ∑ k, MvPolynomial.C ((A k) i j) *
        (MvPolynomial.X k : MvPolynomial (Fin t) (ZMod p))
    have hMp_skew : Mpᵀ = -Mp := by
      apply Matrix.ext
      intro i j
      simp only [Matrix.transpose_apply, Mp, Matrix.of_apply, Matrix.neg_apply]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : (A k) j i = -((A k) i j) := by
        have := congrFun (congrFun (hskew k) i) j
        simpa [Matrix.transpose_apply, Matrix.neg_apply] using this
      rw [h1, map_neg]
      ring
    have hMp_diag : ∀ i, Mp i i = 0 := by
      intro i
      simp only [Mp, Matrix.of_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hdiag k i, map_zero, zero_mul]
    obtain ⟨g, hg⟩ := exists_sq_det_of_alt Mp hMp_skew hMp_diag
    have hDdeg : Mp.det.totalDegree ≤ n := by
      rw [Matrix.det_apply]
      refine MvPolynomial.totalDegree_finsetSum_le fun σ _ => ?_
      have h1 : (∏ i, Mp (σ i) i).totalDegree ≤ ∑ i, (Mp (σ i) i).totalDegree :=
        MvPolynomial.totalDegree_finsetProd _ _
      have h2 : ∀ i, (Mp (σ i) i).totalDegree ≤ 1 := by
        intro i
        simp only [Mp, Matrix.of_apply]
        refine MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_X]
        simp
      calc ((((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • (∏ i, Mp (σ i) i) :
            MvPolynomial (Fin t) (ZMod p)).totalDegree
          ≤ (∏ i, Mp (σ i) i).totalDegree :=
            MvPolynomial.totalDegree_smul_le (((Equiv.Perm.sign σ : ℤˣ) : ℤ))
              (∏ i, Mp (σ i) i)
        _ ≤ ∑ i, (Mp (σ i) i).totalDegree := h1
        _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => h2 i
        _ = n := by simp
    have hgdeg : g.totalDegree ≤ n / 2 := by
      rcases eq_or_ne g 0 with hg0 | hg0
      · rw [hg0]; exact Nat.zero_le _
      · have h := MvPolynomial.totalDegree_mul_of_isDomain hg0 hg0
        rw [hg] at h
        have := hDdeg
        omega
    have hgt : g.totalDegree < Fintype.card (Fin t) := by
      have h1 : n / 2 < t := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
        omega
      simp only [Fintype.card_fin]
      omega
    have hMp_eval : ∀ x : Fin t → ZMod p, Mp.map (MvPolynomial.eval x) = ∑ k, x k • A k := by
      intro x
      apply Matrix.ext
      intro i j
      simp only [Matrix.map_apply, Mp, Matrix.of_apply, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X, map_sum]
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hzero : ∀ x : Fin t → ZMod p, MvPolynomial.eval x g = 0 ↔ x = 0 := by
      intro x
      constructor
      · intro hx
        by_contra hx0
        have hdet : (∑ k, x k • A k).det ≠ 0 := by
          intro hdet0
          obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
          exact hv0 (hnd x hx0 v hv)
        exact hdet (by
          have h2 : MvPolynomial.eval x g * MvPolynomial.eval x g
              = MvPolynomial.eval x Mp.det := by rw [← map_mul, hg]
          rw [hx, mul_zero] at h2
          calc (∑ k, x k • A k).det = MvPolynomial.eval x Mp.det := by
                rw [RingHom.map_det, RingHom.mapMatrix_apply, hMp_eval x]
            _ = 0 := h2.symm)
      · intro hx
        subst hx
        have h2 : MvPolynomial.eval (0 : Fin t → ZMod p) g * MvPolynomial.eval 0 g
            = MvPolynomial.eval (0 : Fin t → ZMod p) Mp.det := by
          rw [← map_mul, hg]
        have h5 : MvPolynomial.eval (0 : Fin t → ZMod p) Mp.det = 0 := by
          rw [RingHom.map_det, RingHom.mapMatrix_apply, hMp_eval 0]
          simp
        rw [h5, mul_eq_zero] at h2
        exact h2.elim id id
    have hCW := char_dvd_card_solutions p (K := ZMod p) (σ := Fin t) (f := g) hgt
    have hcard : Fintype.card {x : Fin t → ZMod p // MvPolynomial.eval x g = 0} = 1 := by
      refine Fintype.card_eq_one_iff.mpr ⟨⟨0, (hzero 0).mpr rfl⟩, fun y => ?_⟩
      exact Subtype.ext ((hzero y.val).mp y.2)
    rw [hcard] at hCW
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hCW)

/-- For a nondegenerate form, the matrix `M i j = B (bV j) (bV i)` annihilates no nonzero vector. -/
lemma mulVec_eq_zero_of_nondegenerate {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (bV : Module.Basis (Fin n) K V) {B : V →ₗ[K] V →ₗ[K] K}
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0)
    {v : Fin n → K} (hv : Matrix.of (fun i j => B (bV j) (bV i)) *ᵥ v = 0) : v = 0 := by
  have h1 : ∀ i, B (∑ k, (v k) • (bV k) : V) (bV i) =
      (Matrix.of (fun i j => B (bV j) (bV i)) *ᵥ v) i := by
    intro i
    rw [Matrix.mulVec, dotProduct, map_sum]
    simp only [Matrix.of_apply, Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have h2 : ∀ i, (Matrix.of (fun i j => B (bV j) (bV i)) *ᵥ v) i = 0 := by
    intro i
    have := congrFun hv i
    simpa using this
  have hx : (∑ i, v i • bV i : V) = 0 := by
    apply hnd
    intro w
    have hw : w = ∑ i, (bV.repr w) i • bV i := (Module.Basis.sum_repr bV w).symm
    rw [hw, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, smul_eq_mul, h1 i, h2 i, mul_zero]
  exact funext ((Fintype.linearIndependent_iff.mp bV.linearIndependent) v hx)

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **A subspace of alternating forms, all of whose nonzero elements are nondegenerate, has
cardinality at most `√|V|`.**  (Equivalently: its `𝔽_p`-dimension is at most `dim V / 2`.)

Proof route: if `dim L > dim V/2`, pick a basis `b_1,…,b_t` of `L` and consider the polynomial
`F(x) = Pf(∑ x_i · M(b_i))`, where `M(b)` is the matrix of `b` in a basis of `V` and `Pf` is the
Pfaffian, a polynomial of degree `n/2 = dim V / 2` in the entries with `Pf(A)^2 = det A` and
`Pf(A) = 0 ↔ A` singular.  Since every nonzero element of `L` is nondegenerate, `F` has no
nonzero zero (`F(0) = 0`), so Chevalley–Warning
(`MvPolynomial.char_dvd_card_solutions`, in Mathlib) gives `p ∣ 1`, a contradiction. -/
theorem nonsingular_subspace_card_sq_le {p : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (L : Submodule (ZMod p) (V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p))
    (halt : ∀ b ∈ L, ∀ v : V, b v v = 0)
    (hnd : ∀ b ∈ L, b ≠ 0 → ∀ v : V, (∀ w : V, b v w = 0) → v = 0) :
    Nat.card L ^ 2 ≤ Nat.card V := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : Fintype V := Fintype.ofFinite V
  have hVfree : Module.Free (ZMod p) V := Module.Free.of_divisionRing (ZMod p) V
  have hVfin : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let bV := @Module.finBasis (ZMod p) V _ _ _ hVfree _ hVfin
  obtain ⟨s, hsL, hsspan, hsli⟩ :=
    exists_linearIndependent (ZMod p) (↑L : Set (V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p))
  have hsspanL : Submodule.span (ZMod p) s = L := by rw [hsspan, Submodule.span_eq]
  haveI : Finite L := Finite.of_injective
    (fun x : L => fun v w => (x : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) v w)
    (fun a b h => Subtype.ext (LinearMap.ext fun v => LinearMap.ext fun w => congrFun (congrFun h v) w))
  have hLfin : (↑L : Set (V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p)).Finite := by
    rw [← Subtype.range_val (s := (↑L : Set (V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p)))]
    exact Set.finite_range _
  have hsf : s.Finite := hLfin.subset hsL
  haveI : Finite s := hsf.to_subtype
  haveI : Fintype s := Fintype.ofFinite s
  set t := Nat.card s with ht
  let e : s ≃ Fin t := (Fintype.equivFin s).trans (finCongr (by rw [ht, Nat.card_eq_fintype_card]))
  let Ψ : (V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) ≃ₗ[ZMod p]
      Matrix (Fin (Module.finrank (ZMod p) V)) (Fin (Module.finrank (ZMod p) V)) (ZMod p) :=
    { toFun := fun B => ((LinearMap.toMatrix₂ bV bV) B)ᵀ
      invFun := fun M => (LinearMap.toMatrix₂ bV bV).symm Mᵀ
      left_inv := by intro B; simp [Matrix.transpose_transpose]
      right_inv := by intro M; simp [Matrix.transpose_transpose]
      map_add' := by intro B C; simp [Matrix.transpose_add]
      map_smul' := by intro c B; simp [Matrix.transpose_smul] }
  have hΨ : ∀ (B : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) (i j : Fin (Module.finrank (ZMod p) V)),
      Ψ B i j = B (bV j) (bV i) := by
    intro B i j
    show ((LinearMap.toMatrix₂ bV bV) B)ᵀ i j = B (bV j) (bV i)
    rw [Matrix.transpose_apply, LinearMap.toMatrix₂_apply]
  have hΨeq : ∀ B : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p,
      Ψ B = Matrix.of (fun i j => B (bV j) (bV i)) := by
    intro B
    apply Matrix.ext
    intro i j
    rw [hΨ]
    rfl
  let A : Fin t → Matrix (Fin (Module.finrank (ZMod p) V)) (Fin (Module.finrank (ZMod p) V)) (ZMod p) :=
    fun k => Ψ ((e.symm k : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p)
  have hsum : ∀ x : Fin t → ZMod p, (∑ k, x k • A k) =
      Ψ (∑ k, x k • ((e.symm k : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p)) := by
    intro x
    simp only [A, map_sum, map_smul]
  have hli : ∀ x : Fin t → ZMod p, (∑ k, x k • A k) = 0 → x = 0 := by
    intro x hx
    have h0 : (∑ k, x k • ((e.symm k : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p)) = 0 := by
      rw [hsum x] at hx
      exact Ψ.injective (by simpa using hx)
    have h1 : ∀ i : s, x (e i) = 0 := by
      refine (Fintype.linearIndependent_iff.mp hsli) (fun i : s => x (e i)) ?_
      have h4 : (∑ i : s, x (e i) • ((i : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p)) =
          ∑ k : Fin t, x k • ((e.symm k : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) := by
        rw [← Equiv.sum_comp e (fun k => x k • ((e.symm k : s) :
          V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p))]
        simp
      rw [h4, h0]
    funext k
    have := h1 (e.symm k)
    simpa using this
  have hskew : ∀ k, (A k)ᵀ = -(A k) := by
    intro k
    apply Matrix.ext
    intro i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, A, hΨ]
    have h1 := LinearMap.IsAlt.neg
      (B := ((e.symm k : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p))
      (fun v => halt _ (hsL ((e.symm k : s).2)) v) (bV i) (bV j)
    rw [h1.symm]
    simp
  have hdiag : ∀ k i, A k i i = 0 := by
    intro k i
    show Ψ ((e.symm k : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) i i = 0
    rw [hΨ]
    exact halt _ (hsL ((e.symm k : s).2)) (bV i)
  have hnd' : ∀ x : Fin t → ZMod p, x ≠ 0 →
      ∀ v : Fin (Module.finrank (ZMod p) V) → ZMod p, (∑ k, x k • A k) *ᵥ v = 0 → v = 0 := by
    intro x hx0 v hv
    set B : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p :=
      ∑ k, x k • ((e.symm k : s) : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) with hB
    have hBne : B ≠ 0 := fun h => hx0 (hli x (by rw [hsum x, ← hB]; simp [h]))
    have hBmem : B ∈ L := by
      rw [hB, ← hsspanL]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ((e.symm k : s).2))
    have hv' : Matrix.of (fun i j => B (bV j) (bV i)) *ᵥ v = 0 := by
      rw [show Matrix.of (fun i j => B (bV j) (bV i)) = ∑ k, x k • A k from by
        rw [hsum x, ← hB, hΨeq]]
      exact hv
    exact mulVec_eq_zero_of_nondegenerate bV (fun v hv => hnd B hBmem hBne v hv) hv'
  have h2t : 2 * t ≤ Module.finrank (ZMod p) V := core_matrix A hli hskew hdiag hnd'
  have hcardL : Nat.card L ≤ p ^ t := by
    have hsurj : Function.Surjective (fun l : s →₀ ZMod p =>
        (⟨Finsupp.linearCombination (ZMod p)
            (Subtype.val : s → V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) l,
          by rw [Finsupp.span_eq_range_linearCombination (R := ZMod p)
            (M := V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) (s := s)]
             exact LinearMap.mem_range_self _ l⟩ :
          ↥(Submodule.span (ZMod p) s))) := by
      intro y
      obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination (R := ZMod p)
        (M := V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) s
        (y : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p)).mp y.2
      exact ⟨l, Subtype.ext hl⟩
    have h1 : Nat.card ↥(Submodule.span (ZMod p) s) ≤ Nat.card (s →₀ ZMod p) :=
      Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card (s →₀ ZMod p) = p ^ t := by
      rw [Nat.card_congr Finsupp.equivFunOnFinite, Nat.card_eq_fintype_card, Fintype.card_fun]
      simp [ht, ZMod.card p]
    have h3 : Nat.card ↥(Submodule.span (ZMod p) s) = Nat.card L := by rw [hsspanL]
    omega
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := V), ZMod.card p]
  calc Nat.card L ^ 2 ≤ (p ^ t) ^ 2 := Nat.pow_le_pow_left hcardL 2
    _ = p ^ (2 * t) := by rw [← pow_mul, mul_comm]
    _ ≤ p ^ Module.finrank (ZMod p) V := Nat.pow_le_pow_right (le_of_lt hp) h2t
    _ = Nat.card V := hcardV.symm

end Commons.LinearAlgebra.Alternating