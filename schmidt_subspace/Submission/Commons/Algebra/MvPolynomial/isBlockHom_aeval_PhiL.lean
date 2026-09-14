import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Defs

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators
open _root_.MvPolynomial

noncomputable section

variable {R : Type*} [CommSemiring R] {m N : ℕ}

/-- The block degree of a monomial: the `h`-th entry is the total degree of `v` in the
variables `(h, ·)`. -/
private def blockDeg (v : Fin m × Fin N →₀ ℕ) : Fin m → ℕ :=
  fun h => ∑ j : Fin N, v (h, j)

/-- The block weight of a variable index `x`: `1` at the block `x.1`, `0` elsewhere. -/
private def wdeg (x : Fin m × Fin N) : Fin m → ℕ :=
  fun h => if x.1 = h then 1 else 0

private lemma blockDeg_add (a b : Fin m × Fin N →₀ ℕ) :
    blockDeg (a + b) = blockDeg a + blockDeg b := by
  funext h
  simp only [blockDeg, Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]

/-- Summing `v` over the indices whose first coordinate equals `h`. -/
private lemma sum_fiber_eq (v : Fin m × Fin N →₀ ℕ) (h : Fin m) :
    (∑ x ∈ v.support, (if x.1 = h then v x else 0)) = ∑ j : Fin N, v (h, j) := by
  classical
  have h1 : (∑ x ∈ v.support, (if x.1 = h then v x else 0))
      = ∑ x : Fin m × Fin N, (if x.1 = h then v x else 0) := by
    apply Finset.sum_subset (Finset.subset_univ v.support)
    intro x _ hx
    rw [Finsupp.notMem_support_iff] at hx
    simp [hx]
  rw [h1, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single h]
  · apply Finset.sum_congr rfl
    intro j _
    simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro j _
    simp [hb]
  · intro hh; exact absurd (Finset.mem_univ h) hh

/-- The value of `Finsupp.mapDomain Prod.fst` at `h` is the sum over the `j`-fiber. -/
private lemma mapDomain_prodFst_apply {N' : ℕ} (v : Fin m × Fin N' →₀ ℕ) (h : Fin m) :
    Finsupp.mapDomain Prod.fst v h = ∑ j : Fin N', v (h, j) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.single_apply, Finsupp.sum]
  exact sum_fiber_eq v h

private lemma blockDeg_single (y : Fin m × Fin N) :
    blockDeg (Finsupp.single y 1) = wdeg y := by
  funext h
  show (∑ j : Fin N, (Finsupp.single y 1 : Fin m × Fin N →₀ ℕ) (h, j)) = wdeg y h
  rw [← mapDomain_prodFst_apply (Finsupp.single y 1) h, Finsupp.mapDomain_single]
  simp only [wdeg, Finsupp.single_apply]

private lemma wdeg_fst (x : Fin m × Fin N) (k : Fin N) : wdeg (x.1, k) = wdeg x := by
  funext h
  simp only [wdeg]

/-- The `R`-submodule of polynomials all of whose monomials have block degree exactly
`e`.  This is a submodule (for fixed `e`) because block degrees add under multiplication,
and a sum of block-homogeneous polynomials of the same degree is again block-homogeneous. -/
private def blockHomog (e : Fin m → ℕ) : Submodule R (MvPolynomial (Fin m × Fin N) R) where
  carrier := {p | ∀ v ∈ p.support, blockDeg v = e}
  zero_mem' := by intro v hv; simp at hv
  add_mem' := by
    intro p q hp hq v hv
    rcases Finset.mem_union.mp (MvPolynomial.support_add (p := p) (q := q) hv) with h | h
    · exact hp v h
    · exact hq v h
  smul_mem' := by
    intro a p hp v hv
    exact hp v (MvPolynomial.support_smul hv)

private lemma monomial_mem_blockHomog {e : Fin m → ℕ} {w : Fin m × Fin N →₀ ℕ} (a : R)
    (hw : blockDeg w = e) : MvPolynomial.monomial w a ∈ blockHomog e := by
  intro v hv
  have hvs := MvPolynomial.support_monomial_subset (s := w) (a := a) hv
  rw [Finset.mem_singleton] at hvs
  rw [hvs, hw]

private lemma one_mem_blockHomog :
    (1 : MvPolynomial (Fin m × Fin N) R) ∈ blockHomog (0 : Fin m → ℕ) := by
  have h : (1 : MvPolynomial (Fin m × Fin N) R) = MvPolynomial.monomial 0 1 := by
    rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]
  rw [h]
  apply monomial_mem_blockHomog
  funext h; simp [blockDeg]

/-- The linear form `∑_k Λ k b • X (a,k)` lies in the block-homogeneous piece of degree
`wdeg (a,b)`. -/
private lemma linForm_mem_blockHomog (Λ : Matrix (Fin N) (Fin N) R) (x : Fin m × Fin N) :
    (∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k))
      ∈ blockHomog (wdeg x) := by
  apply Submodule.sum_mem
  intro k _
  rw [MvPolynomial.C_mul_X_eq_monomial]
  apply monomial_mem_blockHomog
  rw [blockDeg_single, wdeg_fst]

private lemma blockHomog_mul_mem {e e' : Fin m → ℕ} {p q : MvPolynomial (Fin m × Fin N) R}
    (hp : p ∈ blockHomog e) (hq : q ∈ blockHomog e') :
    p * q ∈ blockHomog (e + e') := by
  intro v hv
  rcases Finset.mem_add.mp (MvPolynomial.support_mul p q hv) with ⟨a, ha, b, hb, rfl⟩
  rw [blockDeg_add, hp a ha, hq b hb]

private lemma blockHomog_pow_mem {e : Fin m → ℕ} {p : MvPolynomial (Fin m × Fin N) R}
    (hp : p ∈ blockHomog e) (n : ℕ) : p ^ n ∈ blockHomog (n • e) := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact one_mem_blockHomog
  | succ n ih => rw [pow_succ, succ_nsmul]; exact blockHomog_mul_mem ih hp

private lemma blockHomog_prod_mem {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (g : ι → MvPolynomial (Fin m × Fin N) R) (e : ι → Fin m → ℕ)
    (hg : ∀ x ∈ t, g x ∈ blockHomog (e x)) :
    (∏ x ∈ t, g x) ∈ blockHomog (fun h => ∑ x ∈ t, e x h) := by
  classical
  induction t using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact one_mem_blockHomog
  | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      have hga : g a ∈ blockHomog (e a) := hg a (Finset.mem_insert_self a t)
      have hgt : (∏ x ∈ t, g x) ∈ blockHomog (fun h => ∑ x ∈ t, e x h) :=
        ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      have hmem := blockHomog_mul_mem hga hgt
      have heq : (e a + fun h => ∑ x ∈ t, e x h) = (fun h => ∑ x ∈ insert a t, e x h) := by
        ext h; simp only [Pi.add_apply, Finset.sum_insert ha]
      rwa [heq] at hmem

/-- `aeval` of a monomial is block-homogeneous of its block degree. -/
private lemma aeval_monomial_mem (Λ : Matrix (Fin N) (Fin N) R)
    (u : Fin m × Fin N →₀ ℕ) (c : R) :
    MvPolynomial.aeval
        (fun x : Fin m × Fin N =>
          ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k))
        (MvPolynomial.monomial u c) ∈ blockHomog (blockDeg u) := by
  set f : Fin m × Fin N → MvPolynomial (Fin m × Fin N) R :=
    fun x => ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k) with hf
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod]
  have hprod : (∏ i ∈ u.support, (f i) ^ (u i))
      ∈ blockHomog (fun h => ∑ i ∈ u.support, (u i • wdeg i) h) := by
    apply blockHomog_prod_mem
    intro i _
    apply blockHomog_pow_mem
    simpa only [hf] using linForm_mem_blockHomog Λ i
  have heq : (fun h => ∑ i ∈ u.support, (u i • wdeg i) h) = blockDeg u := by
    funext h
    simp only [blockDeg]
    have hstep : (∑ i ∈ u.support, (u i • wdeg i) h)
        = ∑ i ∈ u.support, (if i.1 = h then u i else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hih : i.1 = h
      · simp [Pi.smul_apply, wdeg, hih]
      · simp [Pi.smul_apply, wdeg, hih]
    rw [hstep, sum_fiber_eq u h]
  rw [heq] at hprod
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hprod

theorem isBlockHom_aeval_PhiL {R : Type*} [CommSemiring R] {m N : ℕ}
    (Λ : Matrix (Fin N) (Fin N) R)
    {F : MvPolynomial (Fin m × Fin N) R} {d : Fin m → ℕ}
    (hF : ∀ u ∈ F.support, ∀ h : Fin m, ∑ k : Fin N, u (h, k) = d h) :
    ∀ J ∈ (MvPolynomial.aeval
        (fun x : Fin m × Fin N =>
          ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)) F).support,
      ∀ h : Fin m, ∑ k : Fin N, J (h, k) = d h := by
  have hsum : MvPolynomial.aeval
        (fun x : Fin m × Fin N =>
          ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)) F
      = ∑ u ∈ F.support, MvPolynomial.aeval
          (fun x : Fin m × Fin N =>
            ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k))
          (MvPolynomial.monomial u (F.coeff u)) := by
    conv_lhs => rw [MvPolynomial.as_sum F]
    rw [MvPolynomial.aeval_sum]
  have hmem : MvPolynomial.aeval
        (fun x : Fin m × Fin N =>
          ∑ k : Fin N, MvPolynomial.C (Λ k x.2) * MvPolynomial.X (x.1, k)) F
      ∈ blockHomog d := by
    rw [hsum]
    apply Submodule.sum_mem
    intro u hu
    have hu_eq : blockDeg u = d := by funext h; exact hF u hu h
    have h1 := aeval_monomial_mem Λ u (F.coeff u)
    rwa [hu_eq] at h1
  intro J hJ h
  exact congrFun (hmem J hJ) h

end

end Commons.Algebra.MvPolynomial