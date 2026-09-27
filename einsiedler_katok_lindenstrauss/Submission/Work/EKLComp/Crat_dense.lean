import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.exists_eta_adj
import Submission.Work.EKLComp.exists_eta_inv_close
import Submission.Work.EKLComp.exists_rat_matrix

/-!
# Rational matrices dense in the centraliser `Csub t`

`Csub t = C_{SL3(R)}(aDiag t)` is the centraliser of `aDiag t`; by `mem_Csub_iff` its elements are
the matrices whose entries vanish at every pair `(i,j)` with `t i != t j`.  The lemma `Crat_dense`
says that, for every `c in Csub t` and every `eps > 0`, there is `g in Csub t` with rational matrix
entries and with `g^{-1} c in V eps`.

The proof is the standard "rational points of a linear group are dense" argument, made effective
for a single matrix: approximate `M = toMat c` entrywise by a rational matrix `Rq` with the same
zero pattern, then change one entry of `Rq` (the determinant is affine in that entry, with the
`(q,p)`-cofactor as slope) so that the determinant becomes exactly `1`.  The modified entry lies
inside a block (`t p = t q`), so the zero pattern is preserved.  Continuity of `G |-> adjugate G * M`
at `M` turns entrywise closeness of `G` to `M` into `g^{-1} c in V eps`.
-/

namespace Work.EKLComp

open Matrix

/-- The determinant of a matrix in which the entry `(p,q)` has been perturbed by `s`, expressed
through the `(q,p)`-cofactor. -/
lemma det_updateRow_add_single {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (A : Matrix n n R) (p q : n) (s : R) :
    (A.updateRow p (A p + Pi.single q s)).det = A.det + s * A.adjugate q p := by
  rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self]
  have hs : (Pi.single q s : n → R) = s • (Pi.single q 1 : n → R) := by
    ext k; rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
    by_cases h : q = k <;> simp [h]
  rw [hs, Matrix.det_updateRow_smul, Matrix.adjugate_apply]

/-- Entry formula for the perturbation of a single entry. -/
lemma updateRow_add_single_apply {n : Type*} [DecidableEq n] {R : Type*} [AddCommMonoid R]
    (A : Matrix n n R) (p q : n) (s : R) (i j : n) :
    (A.updateRow p (A p + Pi.single q s)) i j = A i j + (if i = p ∧ q = j then s else 0) := by
  rw [Matrix.updateRow_apply, Pi.add_apply, Pi.single_apply]
  by_cases hip : i = p
  · subst hip
    by_cases hqj : q = j
    · simp [hqj]
    · simp [hqj, Ne.symm hqj]
  · rw [if_neg hip, if_neg (fun h => hip h.1), add_zero]

/-- Perturbing an entry `(p,q)` with `t p = t q` preserves the zero pattern of `Csub t`. -/
lemma updateRow_zero_pattern {R : Type*} [AddMonoid R] {t : Fin 3 → ℝ}
    {A : Matrix (Fin 3) (Fin 3) R}
    (hA : ∀ i j, t i ≠ t j → A i j = 0) {p q : Fin 3} (hpq : t p = t q) (s : R) :
    ∀ i j, t i ≠ t j → (A.updateRow p (A p + Pi.single q s)) i j = 0 := by
  intro i j hij
  rw [Matrix.updateRow_apply]
  by_cases hip : i = p
  · obtain rfl := hip
    rw [if_pos rfl]
    have hqj : q ≠ j := by intro h; rw [h] at hpq; exact hij hpq
    simp only [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hqj), hA i j hij, add_zero]
  · rw [if_neg hip]
    exact hA i j hij

/-- For every `eta > 0` and every `M` with `det M = 1` and a nonzero `(q,p)`-cofactor, there is a
rational matrix `G` with `det G = 1`, the `Csub t`-zero-pattern, and entries within `eta` of those
of `M`. -/
lemma exists_rat_approx (M : Matrix (Fin 3) (Fin 3) ℝ) (hMdet : M.det = 1) (t : Fin 3 → ℝ)
    (hMzero : ∀ i j, t i ≠ t j → M i j = 0)
    {q p : Fin 3} (htpq : t p = t q) (hMadj : M.adjugate q p ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.det = 1 ∧ (∀ i j, t i ≠ t j → G i j = 0) ∧
      (∀ i j, ∃ r : ℚ, G i j = r) ∧ (∀ i j, |G i j - M i j| < η) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := exists_eta_adj M hMdet hMadj η hη
  have hδmpos : 0 < min δ₀ (η / 2) := lt_min hδ₀pos (by linarith)
  have hδmle : min δ₀ (η / 2) ≤ δ₀ := min_le_left _ _
  have hδmη : min δ₀ (η / 2) ≤ η / 2 := min_le_right _ _
  obtain ⟨Rq, hRq_close, hRq_zero⟩ := exists_rat_matrix M t hMzero hδmpos
  set R : Matrix (Fin 3) (Fin 3) ℝ := (Rat.castHom ℝ).mapMatrix Rq with hR_def
  have hRij : ∀ i j, R i j = (Rq i j : ℝ) := fun i j => by rw [hR_def]; rfl
  have hRdet_eq : R.det = (Rq.det : ℝ) := by
    rw [hR_def, ← RingHom.map_det (Rat.castHom ℝ) Rq]; rfl
  have hRadj_eq : R.adjugate q p = (Rq.adjugate q p : ℝ) := by
    rw [hR_def, ← RingHom.map_adjugate (Rat.castHom ℝ) Rq]; rfl
  have hR_close' : ∀ i j, |R i j - M i j| < min δ₀ (η / 2) := fun i j => by
    rw [hRij i j]; exact hRq_close i j
  have hR_close : ∀ i j, |R i j - M i j| < δ₀ := fun i j => lt_of_lt_of_le (hR_close' i j) hδmle
  have hRadj : R.adjugate q p ≠ 0 := (hδ₀ R hR_close).1
  have hRfrac : |(1 - R.det) / (R.adjugate q p)| ≤ η / 2 := (hδ₀ R hR_close).2
  have hRadjq : Rq.adjugate q p ≠ 0 := by
    intro h; apply hRadj; rw [hRadj_eq, h]; norm_num
  set s : ℚ := (1 - Rq.det) / (Rq.adjugate q p) with hs_def
  have hs_eq : (s : ℝ) = (1 - R.det) / (R.adjugate q p) := by
    rw [hs_def, Rat.cast_div, Rat.cast_sub, Rat.cast_one, hRdet_eq, ← hRadj_eq]
  have hssmall : |(s : ℝ)| ≤ η / 2 := by rw [hs_eq]; exact hRfrac
  set Gq : Matrix (Fin 3) (Fin 3) ℚ := Rq.updateRow p (Rq p + Pi.single q s) with hGq_def
  have hGqdet : Gq.det = 1 := by
    rw [hGq_def, det_updateRow_add_single, hs_def, div_mul_cancel₀ _ hRadjq]; ring
  have hGqzero : ∀ i j, t i ≠ t j → Gq i j = 0 := fun i j hij => by
    rw [hGq_def]; exact updateRow_zero_pattern (A := Rq) hRq_zero htpq s i j hij
  set G : Matrix (Fin 3) (Fin 3) ℝ := (Rat.castHom ℝ).mapMatrix Gq with hG_def
  have hGij : ∀ i j, G i j = (Gq i j : ℝ) := fun i j => by rw [hG_def]; rfl
  have hGdet : G.det = 1 := by
    rw [hG_def, ← RingHom.map_det (Rat.castHom ℝ) Gq, hGqdet]; simp
  have hGzero : ∀ i j, t i ≠ t j → G i j = 0 := fun i j hij => by
    rw [hGij i j, hGqzero i j hij]; norm_num
  have hGrat : ∀ i j, ∃ r : ℚ, G i j = r := fun i j => ⟨Gq i j, hGij i j⟩
  have hGclose : ∀ i j, |G i j - M i j| < η := by
    intro i j
    have hGqij : Gq i j = Rq i j + (if i = p ∧ q = j then s else 0) := by
      rw [hGq_def]; exact updateRow_add_single_apply Rq p q s i j
    have hdiff : G i j - R i j = (((if i = p ∧ q = j then s else 0 : ℚ)) : ℝ) := by
      rw [hGij i j, hRij i j, hGqij, Rat.cast_add]; ring
    have hb2 : |R i j - M i j| < η / 2 := lt_of_lt_of_le (hR_close' i j) hδmη
    have hb1 : |(((if i = p ∧ q = j then s else 0 : ℚ)) : ℝ)| ≤ |(s : ℝ)| := by
      by_cases hc : i = p ∧ q = j
      · rw [if_pos hc]
      · rw [if_neg hc]; simp
    calc |G i j - M i j| = |(G i j - R i j) + (R i j - M i j)| := by
          rw [show G i j - R i j + (R i j - M i j) = G i j - M i j by ring]
      _ ≤ |G i j - R i j| + |R i j - M i j| := abs_add_le _ _
      _ = |(((if i = p ∧ q = j then s else 0 : ℚ)) : ℝ)| + |R i j - M i j| := by rw [hdiff]
      _ ≤ |(s : ℝ)| + |R i j - M i j| := by linarith
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring
  exact ⟨G, hGdet, hGzero, hGrat, hGclose⟩

theorem Crat_dense {t : Fin 3 → ℝ} (c : Work.EKLContract.SL3) (hc : c ∈ Work.EKLComp.Csub t) {ε : ℝ} (hε : 0 < ε) : ∃ g : Work.EKLContract.SL3, g ∈ Work.EKLComp.Csub t ∧ (∀ i j, ∃ q : ℚ, (g : Matrix (Fin 3) (Fin 3) ℝ) i j = q) ∧ g⁻¹ * c ∈ Work.EKLContract.V ε := by
  have hMdet : (Work.EKLContract.toMat c).det = 1 := c.2
  have hMzero : ∀ i j, t i ≠ t j → Work.EKLContract.toMat c i j = 0 :=
    fun i j hij => (Work.EKLComp.mem_Csub_iff t c).mp hc i j hij
  have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := one_ne_zero
  have hMadj_ne : (Work.EKLContract.toMat c).adjugate ≠ 0 := by
    intro h
    have hmul := Matrix.mul_adjugate (Work.EKLContract.toMat c)
    rw [h, Matrix.mul_zero, hMdet, one_smul] at hmul
    exact hone hmul.symm
  obtain ⟨q, p, hqp⟩ : ∃ q p, (Work.EKLContract.toMat c).adjugate q p ≠ 0 := by
    by_contra h
    push Not at h
    exact hMadj_ne (funext fun i => funext fun j => h i j)
  have hcoevinv : (Work.EKLContract.toMat c).adjugate = Work.EKLContract.toMat (c⁻¹) := by
    rw [← Matrix.SpecialLinearGroup.coe_inv c]
  have hcinv : c⁻¹ ∈ Work.EKLComp.Csub t := (Work.EKLComp.Csub t).inv_mem hc
  have hzeroinv : ∀ i j, t i ≠ t j → Work.EKLContract.toMat (c⁻¹) i j = 0 :=
    (Work.EKLComp.mem_Csub_iff t (c⁻¹)).mp hcinv
  have htpq : t p = t q := by
    by_contra hne
    exact hqp (by rw [hcoevinv]; exact hzeroinv q p (Ne.symm hne))
  obtain ⟨η₀, hη₀pos, hη₀⟩ := exists_eta_inv_close (Work.EKLContract.toMat c) hMdet hε
  obtain ⟨G, hGdet, hGzero, hGrat, hGclose⟩ :=
    exists_rat_approx (Work.EKLContract.toMat c) hMdet t hMzero htpq hqp hη₀pos
  refine ⟨(⟨G, hGdet⟩ : Work.EKLContract.SL3), ?_, ?_, ?_⟩
  · exact (Work.EKLComp.mem_Csub_iff t _).mpr hGzero
  · intro i j
    exact hGrat i j
  · exact hη₀ G hGclose

end Work.EKLComp
