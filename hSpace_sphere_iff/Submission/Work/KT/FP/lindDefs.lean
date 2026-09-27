import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Fund.Laurent

/-!
# `Work.KT.FP.lindDefs` — auxiliary lemmas for `lindAt_admissible`

* `penQ n D c z = ∑_j z^j • c_j` — the polynomial matrix carried by a coefficient sequence
  `c : Fin (D+1) → Mₙ(C(X, ℂ))`;
* `polyOf_map_eval_eq_penQ` — evaluating the `W`-polynomial `polyOf` at a point is the same as
  evaluating `penQ` pointwise;
* `isUnit_matrix_iff_forall_eval` — a matrix over `C(X, ℂ)` is a unit as soon as all its pointwise
  evaluations are units;
* `laurentMap_apply_eq_sum` — the value of `laurentMap` at a point is the sum of the coefficients
  weighted by the powers of `z`.
-/

namespace Work.KT.FP

open Matrix
open scoped BigOperators

noncomputable section

/-- The polynomial matrix `∑_j z^j • c_j` carried by a coefficient sequence `c`. -/
def penQ (X : Type) [TopologicalSpace X] (n D : ℕ)
    (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) :
    Matrix (Fin n) (Fin n) C(X, ℂ) :=
  ∑ j : Fin (D + 1), (z ^ (j : ℕ)) • c j

lemma penQ_apply (X : Type) [TopologicalSpace X] (n D : ℕ)
    (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) (a b : Fin n) :
    penQ X n D c z a b = ∑ j : Fin (D + 1), (z ^ (j : ℕ)) • (c j a b : C(X, ℂ)) := by
  simp only [penQ, Matrix.sum_apply, Matrix.smul_apply]

lemma penQ_map_eval (X : Type) [TopologicalSpace X] (n D : ℕ)
    (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) (x : X) (a b : Fin n) :
    (penQ X n D c z).map (fun f => f x) a b = ∑ j : Fin (D + 1), z ^ (j : ℕ) * (c j a b) x := by
  rw [Matrix.map_apply]
  change (penQ X n D c z a b) x = _
  rw [penQ_apply]
  change (ContinuousMap.evalAlgHom ℂ ℂ x)
      (∑ j : Fin (D + 1), (z ^ (j : ℕ)) • (c j a b : C(X, ℂ))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

/-- Evaluating the `W`-polynomial `polyOf` at a point of `X × S¹` is the same as evaluating the
polynomial matrix `penQ` at the corresponding point of `X`. -/
lemma polyOf_map_eval_eq_penQ (X : Type) [TopologicalSpace X] (n D : ℕ)
    (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) (z : Sph ℂ) :
    (polyOf X n D c).map (fun f => f (x, z))
      = (penQ X n D c (z : ℂ)).map (fun f => f x) := by
  ext a b
  rw [penQ_map_eval, Matrix.map_apply]
  change (polyOf X n D c a b) (x, z) = ∑ j : Fin (D + 1), (z : ℂ) ^ (j : ℕ) * (c j a b) x
  rw [polyOf]
  change (ContinuousMap.evalAlgHom ℂ ℂ (x, z))
      (∑ j : Fin (D + 1),
        pullFun X (c j a b) * (↑(Work.KT.zUnit X) : C(X × Sph ℂ, ℂ)) ^ (j : ℕ)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, ContinuousMap.evalAlgHom_apply, Work.KT.zUnit_apply,
    pullFun_apply]
  ring

/-! ## Units of matrices over `C(X, ℂ)` -/

/-- A matrix over `C(X, ℂ)` is a unit iff all its pointwise evaluations are units. -/
theorem isUnit_matrix_iff_forall_eval {X : Type} [TopologicalSpace X] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    IsUnit M ↔ ∀ x : X, IsUnit (M.map (fun f => f x)) := by
  have hdet : ∀ x : X, M.det x = (M.map (fun f => f x)).det := by
    intro x
    have h := RingHom.map_det (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom M
    have h2 : ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix M)
        = M.map (fun f => f x) := by
      rw [RingHom.mapMatrix_apply]; rfl
    have h1 : (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom M.det = M.det x :=
      ContinuousMap.evalAlgHom_apply ℂ ℂ x M.det
    rw [h1, h2] at h
    exact h
  rw [Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h x
    rw [Matrix.isUnit_iff_isUnit_det, ← hdet x]
    exact (ContinuousMap.isUnit_iff_forall_isUnit M.det).mp h x
  · intro h
    rw [ContinuousMap.isUnit_iff_forall_isUnit]
    intro x
    rw [hdet x]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (h x)

/-! ## The expansion of `laurentMap` in the coefficients -/

/-- `LaurentPolynomial.eval₂` evaluated on the coefficient decomposition. -/
theorem laurent_eval₂_eq_sum {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (u : Sˣ) (p : LaurentPolynomial R) :
    LaurentPolynomial.eval₂ f u p = p.coeff.sum (fun k r => f r * (u ^ k).val) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      have h1 : ∀ k : ℤ, f (0 : R) * (u ^ k).val = 0 := fun k => by simp
      have h2 : ∀ k : ℤ, ∀ b₁ b₂ : R, f (b₁ + b₂) * (u ^ k).val
          = f b₁ * (u ^ k).val + f b₂ * (u ^ k).val := by
        intro k b₁ b₂; rw [map_add, add_mul]
      rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index' (h := fun k r => f r * (u ^ k).val) h1 h2]
  | C_mul_T k r =>
      rw [LaurentPolynomial.eval₂_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
        AddMonoidAlgebra.coeff_single]
      exact (Finsupp.sum_single_index (h := fun k r => f r * (u ^ k).val)
        (by simp : f (0 : R) * (u ^ k).val = 0)).symm

/-- Naturality of `LaurentPolynomial.eval₂` under a ring homomorphism. -/
theorem laurent_eval₂_natural {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (u : Sˣ) (φ : S →+* T) (p : LaurentPolynomial R) :
    φ (LaurentPolynomial.eval₂ f u p)
      = LaurentPolynomial.eval₂ (φ.comp f) (Units.map φ.toMonoidHom u) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T k r =>
      rw [LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C_mul_T, map_mul,
        RingHom.comp_apply]
      congr 1
      rw [← map_zpow (Units.map φ.toMonoidHom) u k]
      rfl

/-- **Expansion of `laurentMap`**: the value of `laurentMap Y p` at `(y, w)` is the sum of the
coefficients of `p` weighted by the powers of `w`. -/
theorem laurentMap_apply_eq_sum {Y : Type} [TopologicalSpace Y]
    (p : LaurentPolynomial C(Y, ℂ)) (y : Y) (w : Sph ℂ) :
    (laurentMap Y p) (y, w) = ∑ k ∈ p.coeff.support, (p.coeff k) y * (w : ℂ) ^ k := by
  have hnat := laurent_eval₂_natural
    (pullAlg (ContinuousMap.fst : C(Y × Sph ℂ, Y))).toRingHom
    (Work.KT.zUnit Y) (ContinuousMap.evalAlgHom ℂ ℂ (y, w)).toRingHom p
  have h1 : (laurentMap Y p) (y, w)
      = (ContinuousMap.evalAlgHom ℂ ℂ (y, w)).toRingHom
          (LaurentPolynomial.eval₂ (pullAlg (ContinuousMap.fst : C(Y × Sph ℂ, Y))).toRingHom
            (Work.KT.zUnit Y) p) := rfl
  have huval : (Units.map (ContinuousMap.evalAlgHom ℂ ℂ (y, w)).toRingHom.toMonoidHom
      (Work.KT.zUnit Y)).val = (w : ℂ) := by
    change (ContinuousMap.evalAlgHom ℂ ℂ (y, w)) (Work.KT.zUnit Y : C(Y × Sph ℂ, ℂ)) = (w : ℂ)
    rw [ContinuousMap.evalAlgHom_apply, Work.KT.zUnit_apply]
  have hfac : ∀ k : ℤ, (ContinuousMap.evalAlgHom ℂ ℂ (y, w)).toRingHom
      ((pullAlg (ContinuousMap.fst : C(Y × Sph ℂ, Y))).toRingHom (p.coeff k)) = (p.coeff k) y :=
    fun k => rfl
  rw [h1, hnat, laurent_eval₂_eq_sum]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RingHom.comp_apply, hfac k, Units.val_zpow_eq_zpow_val, huval]


/-! ## The degree-`m` Laurent coefficient identity -/

/-- For a Laurent polynomial whose coefficients vanish outside `[-m, m]`, the value of
`laurentMap` at `(x, z)` multiplied by `z^m` is the sum of the coefficients over `Fin (2m+1)`. -/
lemma laurentMap_zpow_mul_eq_coeff_sum (X : Type) [TopologicalSpace X] (m : ℕ)
    (p : LaurentPolynomial C(X, ℂ))
    (hm : ∀ k : ℤ, (m : ℤ) < k ∨ k < -(m : ℤ) → p.coeff k = 0)
    (x : X) (z : Sph ℂ) :
    ((z : ℂ) ^ m) * (laurentMap X p) (x, z)
      = ∑ j : Fin (2 * m + 1), (p.coeff ((j : ℤ) - (m : ℤ))) x * (z : ℂ) ^ (j : ℕ) := by
  have hZ : (z : ℂ) ≠ 0 := by
    intro h
    have h' := Metric.mem_sphere.mp z.2
    rw [dist_eq_norm, sub_zero, h, norm_zero] at h'
    exact zero_ne_one h'
  have hstep : ∀ k : ℤ, (z : ℂ) ^ m * ((p.coeff k) x * (z : ℂ) ^ k)
      = (p.coeff k) x * (z : ℂ) ^ ((m : ℤ) + k) := by
    intro k
    rw [← zpow_natCast (a := (z : ℂ)) (n := m), ← mul_assoc,
      mul_comm ((z : ℂ) ^ (m : ℤ)) ((p.coeff k) x), mul_assoc, ← zpow_add₀ hZ]
  have hsub : p.coeff.support ⊆ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    intro k hk
    rw [Finset.mem_Icc]
    by_contra hcon
    rw [not_and_or, not_le, not_le] at hcon
    exact Finsupp.mem_support_iff.mp hk (hm k (by tauto))
  rw [laurentMap_apply_eq_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [Finset.sum_subset hsub (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.mp hk]; simp)]
  have hemb : Function.Injective (fun n : ℕ => (n : ℤ) - (m : ℤ)) := by
    intro a b h
    dsimp only at h
    have h' : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast h'
  have hIcc : (Finset.range (2 * m + 1)).map ⟨fun n : ℕ => (n : ℤ) - (m : ℤ), hemb⟩
      = Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨n, hn, rfl⟩
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨(k + (m : ℤ)).toNat, ?_, ?_⟩
      · have h3 : ((k + (m : ℤ)).toNat : ℤ) = k + (m : ℤ) :=
          Int.toNat_of_nonneg (by omega)
        omega
      · rw [Int.toNat_of_nonneg (by omega)]
        ring
  rw [← hIcc, Finset.sum_map, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [show (m : ℤ) + ((j : ℤ) - (m : ℤ)) = (j : ℤ) from by ring, zpow_natCast]

/-- **The evaluation bridge**: the `W`-polynomial of a bounded-degree Laurent matrix, evaluated at
a point of `X × S¹`, is `z^m` times the value of the Laurent matrix. -/
lemma polyOf_coeffSeq_map_eq (X : Type) [TopologicalSpace X] (n m : ℕ)
    (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0)
    (x : X) (z : Sph ℂ) :
    (polyOf X n (2 * m) (coeffSeq X n m P)).map (fun f => f (x, z))
      = ((z : ℂ) ^ m) • ((P.map (Work.KT.laurentMap X)).map (fun f => f (x, z))) := by
  ext a b
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, smul_eq_mul]
  have h1 : (polyOf X n (2 * m) (coeffSeq X n m P) a b) (x, z)
      = (penQ X n (2 * m) (coeffSeq X n m P) (z : ℂ)).map (fun f => f x) a b := by
    have h := congrFun (congrFun (polyOf_map_eval_eq_penQ X n (2 * m) (coeffSeq X n m P) x z) a) b
    simpa only [Matrix.map_apply] using h
  rw [h1, penQ_map_eval, Matrix.map_apply,
    laurentMap_zpow_mul_eq_coeff_sum X m (P a b) (fun k => hb a b k) x z]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [coeffSeq]
  ring


/-- A nonzero scalar multiple of a complex matrix is a unit iff the matrix is. -/
lemma isUnit_smul_of_ne_zero {n : ℕ} {c : ℂ} (hc : c ≠ 0) {M : Matrix (Fin n) (Fin n) ℂ} :
    IsUnit (c • M) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul,
    (Commute.all _ _).isUnit_mul_iff]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by rw [isUnit_iff_ne_zero]; exact pow_ne_zero _ hc, h⟩

end

end Work.KT.FP
