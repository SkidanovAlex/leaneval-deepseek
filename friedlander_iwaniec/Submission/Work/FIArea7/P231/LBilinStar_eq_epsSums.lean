import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231.quadEigen_triple
import Submission.Work.FIArea7.quadEigen_decomp
import Submission.Work.FIArea7.jksym_mul_rule_primary
import Submission.Work.FIArea7.dirichletSym_mul
import Submission.Work.FIArea7.JKSym_mul_eq_zero
import Submission.Work.FIArea7.primarySet_card_le_tau
import Submission.Work.FIArea7.P231.sum_primaryDisc_two
import Submission.Work.FIArea7.P231.sum_primaryPrimSet_eq_sum_primarySet
import Submission.Work.FIArea7.P231.epsSummand_sum_eq_zero_of_not_coprime
import Submission.Work.FIArea7.P231.JKSym_mul_assoc_eq

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. TEMPORARY development placeholders

These are the five independent pieces of the proof that are being proved in parallel by
colleagues; each has been requested as a separate module.  They are replaced by imports of the
corresponding modules before the final `declare_proven()`. -/

lemma epsSummand_sum_eq_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (e : GaussianInt)
    (α β : ℕ → ℂ) (ψ : GaussianInt → ℂ) :
    ∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
        epsSummand e
          (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
          (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z
      = α m * β n * ∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          ψ w * ψ z * ((DirichletSym e w : ℤ) : ℂ)
            * ((DirichletSym e z : ℤ) : ℂ)
            * ((MultEps e (w * z) : ℂ) * JKSym (w * z)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  have hcop : Work.FIPlan.GaussCoprime w z := by
    rw [Work.FIPlan.GaussCoprime]
    refine isCoprime_of_coprime_gnorm ?_
    rw [gnorm_of_mem_primarySet hw, gnorm_of_mem_primarySet hz]
    exact hmn
  rw [epsSummand, if_pos hcop]
  simp only [gnorm_of_mem_primarySet hw, gnorm_of_mem_primarySet hz]
  ring

/-! ## 1. Vocabulary -/

/-- The coefficient of the pair `(m,n)` in the eigenvalue sums: `α m β n` when `(m,n) = 1`,
`0` otherwise. -/
def LG (α β : ℕ → ℂ) (m n : ℕ) : ℂ := if Nat.Coprime m n then α m * β n else 0

/-- The triple sum over the primary fibres of `c`, `m`, `n`: the common form of `L∗(M,N)` reached
both from the definition (via `quadEigen_triple`) and from the `ε`-form. -/
def TripleSum (ψ : GaussianInt → ℂ) (c : ℕ) (m n : ℕ) : ℂ :=
  ∑ e ∈ primarySet c, ∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
    ψ e * ψ w * ψ z * JKSym (e * w * z)

/-- The inner double sum of the `ε`-form, with the Jacobi–Kubota factor `[e·w·z]`. -/
def Ssum (ψ : GaussianInt → ℂ) (m n : ℕ) (e : GaussianInt) : ℂ :=
  ∑ w ∈ primarySet m, ∑ z ∈ primarySet n, ψ w * ψ z * JKSym (e * w * z)

/-- The inner double sum of the `ε`-form, in its expanded (multiplier-rule) form. -/
def Tsum (ψ : GaussianInt → ℂ) (m n : ℕ) (e : GaussianInt) : ℂ :=
  ∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
    ψ w * ψ z * ((DirichletSym e w : ℤ) : ℂ) * ((DirichletSym e z : ℤ) : ℂ)
      * ((MultEps e (w * z) : ℂ) * JKSym (w * z))

/-! ## 2. Elementary facts -/

/-- If `e` is primary but not primitive and `x` is primary then `[e·x] = 0`. -/
lemma JKSym_mul_eq_zero_of_not_isCoprime_primary' {e x : GaussianInt}
    (he : Work.FIPlan.IsPrimary e) (hx : Work.FIPlan.IsPrimary x)
    (hnc : ¬ IsCoprime e.re e.im) : JKSym (e * x) = 0 := by
  rw [mul_comm]
  exact JKSym_mul_eq_zero_of_not_isCoprime_primary hx he hnc

/-- Swapping a sum in `e` of constant multiples of a double sum with the double sum. -/
lemma sum_swap_const_mul {ι κ θ : Type*}
    (s : Finset ι) (t : Finset κ) (u : Finset θ) (c : ι → ℂ) (F : ι → κ → θ → ℂ) :
    (∑ e ∈ s, c e * (∑ m ∈ t, ∑ n ∈ u, F e m n))
      = ∑ m ∈ t, ∑ n ∈ u, ∑ e ∈ s, c e * F e m n := by
  have h1 : (∑ e ∈ s, c e * (∑ m ∈ t, ∑ n ∈ u, F e m n))
      = ∑ e ∈ s, ∑ m ∈ t, ∑ n ∈ u, c e * F e m n := by
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
  rw [h1, Finset.sum_comm (s := s) (t := t)]
  exact Finset.sum_congr rfl (fun m _ => Finset.sum_comm)

/-- `TripleSum` written as a sum of `ψ e · Ssum`. -/
lemma TripleSum_eq (ψ : GaussianInt → ℂ) (c m n : ℕ) :
    TripleSum ψ c m n = ∑ e ∈ primarySet c, ψ e * Ssum ψ m n e := by
  show (∑ e ∈ primarySet c, ∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          ψ e * ψ w * ψ z * JKSym (e * w * z))
      = ∑ e ∈ primarySet c, ψ e * Ssum ψ m n e
  refine Finset.sum_congr rfl (fun e _ => ?_)
  show (∑ w ∈ primarySet m, ∑ z ∈ primarySet n, ψ e * ψ w * ψ z * JKSym (e * w * z))
      = ψ e * Ssum ψ m n e
  rw [show Ssum ψ m n e
        = (∑ w ∈ primarySet m, ∑ z ∈ primarySet n, ψ w * ψ z * JKSym (e * w * z)) from rfl]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

/-! ## 3. The definition side -/

/-- **The definition side.**  Using `quadEigen_triple` at every pair `(m,n)` with `(m,n) = 1`,
`(c,m) = 1` and `(c,n) = 1` (the last two coming from the support hypotheses `hαc`, `hβc`),
`L∗(M,N)` is the `(m,n)`-sum of `LG α β m n · TripleSum ψ c m n`. -/
lemma LBilinStar_eq_sum_LG_TripleSum {M N c : ℕ} (hc : 1 ≤ c) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (k : ℤ) (χ : GaussianInt → ℂ)
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → χ (z1 * z2) = χ z1 * χ z2)
    (α β : ℕ → ℂ)
    (hαc : ∀ m, m ∈ Finset.Icc 1 M → α m ≠ 0 → Nat.Coprime m c)
    (hβc : ∀ n, n ∈ Finset.Icc 1 N → β n ≠ 0 → Nat.Coprime n c) :
    LBilinStar M N c (grossenChar χ k) α β
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          LG α β m n * TripleSum (grossenChar χ k) c m n := by
  rw [LBilinStar]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  rw [LG]
  by_cases hmn : Nat.Coprime m n
  · rw [if_pos hmn, if_pos hmn]
    by_cases hab : α m * β n = 0
    · rw [hab, zero_mul, zero_mul]
    · have hα : α m ≠ 0 := fun h => hab (by rw [h, zero_mul])
      have hβ : β n ≠ 0 := fun h => hab (by rw [h, mul_zero])
      have hcm : Nat.Coprime c m := (hαc m hm hα).symm
      have hcn : Nat.Coprime c n := (hβc n hn hβ).symm
      rw [quadEigen_triple hc (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1 hcm hcn hmn
        k χ hmul]
      rfl
  · rw [if_neg hmn, if_neg hmn, zero_mul]

/-! ## 4. The `ε`-form side, pair by pair -/

/-- **The pair `(m,n)` with `(m,n) = 1`.**  Expanding `ε(e, wz)[e][wz](w/e)(z/e) = [e·w·z]` by the
multiplier rule and using that `(w,z) = 1` is automatic for `w ∈ primarySet m`, `z ∈ primarySet n`,
the `e`-sum of the `ε`-form collapses to `α m β n · TripleSum ψ c m n` (the non-primitive `e`
contributing `[e·w·z] = 0`). -/
lemma sum_epsSummand_ppSet_coprime {c m n : ℕ} (hmn : Nat.Coprime m n)
    (α β : ℕ → ℂ) (ψ : GaussianInt → ℂ) :
    ∑ e ∈ primaryPrimSet c, ψ e * JKSym e *
        (∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          epsSummand e
            (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
            (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
      = α m * β n * TripleSum ψ c m n := by
  have hzero : ∀ e ∈ primarySet c, ¬ IsCoprime e.re e.im → ψ e * Ssum ψ m n e = 0 := by
    intro e he hnc
    have heP : Work.FIPlan.IsPrimary e := isPrimary_of_mem_primarySet he
    have hS : Ssum ψ m n e = 0 := by
      rw [show Ssum ψ m n e
            = (∑ w ∈ primarySet m, ∑ z ∈ primarySet n, ψ w * ψ z * JKSym (e * w * z)) from rfl]
      refine Finset.sum_eq_zero (fun w hw => Finset.sum_eq_zero (fun z hz => ?_))
      have h0 : JKSym (e * (w * z)) = 0 :=
        JKSym_mul_eq_zero_of_not_isCoprime_primary' heP
          (Work.FITop3.Witness.isPrimary_mul (isPrimary_of_mem_primarySet hw)
            (isPrimary_of_mem_primarySet hz)) hnc
      rw [mul_assoc e w z, h0, mul_zero]
    rw [hS, mul_zero]
  have hper : ∀ e ∈ primaryPrimSet c,
      ψ e * JKSym e *
        (∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          epsSummand e
            (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
            (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
        = α m * β n * (ψ e * Ssum ψ m n e) := by
    intro e he
    obtain ⟨heP, _hegn, hec⟩ := mem_primaryPrimSet.mp he
    have hX : (∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          epsSummand e
            (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
            (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
        = α m * β n * Tsum ψ m n e := epsSummand_sum_eq_of_coprime hmn e α β ψ
    rw [hX]
    have hT : JKSym e * Tsum ψ m n e = Ssum ψ m n e := by
      rw [show Tsum ψ m n e
            = (∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
                ψ w * ψ z * ((DirichletSym e w : ℤ) : ℂ) * ((DirichletSym e z : ℤ) : ℂ)
                  * ((MultEps e (w * z) : ℂ) * JKSym (w * z))) from rfl]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [JKSym_mul_assoc_eq heP hec (isPrimary_of_mem_primarySet hw)
        (isPrimary_of_mem_primarySet hz)]
      ring
    calc ψ e * JKSym e * (α m * β n * Tsum ψ m n e)
        = α m * β n * (ψ e * (JKSym e * Tsum ψ m n e)) := by ring
      _ = α m * β n * (ψ e * Ssum ψ m n e) := by rw [hT]
  calc ∑ e ∈ primaryPrimSet c, ψ e * JKSym e *
        (∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          epsSummand e
            (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
            (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
      = ∑ e ∈ primaryPrimSet c, α m * β n * (ψ e * Ssum ψ m n e) := Finset.sum_congr rfl hper
    _ = α m * β n * ∑ e ∈ primaryPrimSet c, ψ e * Ssum ψ m n e := by rw [Finset.mul_sum]
    _ = α m * β n * ∑ e ∈ primarySet c, ψ e * Ssum ψ m n e := by
          rw [sum_primaryPrimSet_eq_sum_primarySet c (fun e => ψ e * Ssum ψ m n e) hzero]
    _ = α m * β n * TripleSum ψ c m n := by rw [TripleSum_eq]

/-- **The pair `(m,n)` with `(m,n) ≠ 1`.**  Every admissible `(w,z)` then has
`gcd(|w|²,|z|²) > 1`, so `[wz] = 0` and the whole double sum vanishes. -/
lemma sum_epsSummand_ppSet_not_coprime {c m n : ℕ} (hmn : ¬ Nat.Coprime m n)
    (α β : ℕ → ℂ) (ψ : GaussianInt → ℂ) :
    ∑ e ∈ primaryPrimSet c, ψ e * JKSym e *
        (∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
          epsSummand e
            (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
            (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
      = 0 := by
  refine Finset.sum_eq_zero (fun e _ => ?_)
  have hX : (∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
        epsSummand e
          (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
          (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
      = 0 := epsSummand_sum_eq_zero_of_not_coprime hmn e _ _
  rw [hX, mul_zero]

/-! ## 5. The `ε`-form side -/

/-- **The `ε`-form side.**  Reindexing the two discs by the exact norm (`sum_primaryDisc_two`),
swapping the `e`-sum with the `(m,n)`-sums and applying the pair lemmas. -/
lemma epsSums_eq_sum_LG_TripleSum {M N c : ℕ} (α β : ℕ → ℂ) (ψ : GaussianInt → ℂ) :
    (∑ e ∈ primaryPrimSet c, ψ e * JKSym e *
        (∑ w ∈ primaryDisc M, ∑ z ∈ primaryDisc N,
          epsSummand e
            (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
            (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z))
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          LG α β m n * TripleSum ψ c m n := by
  have hstep : ∀ e : GaussianInt,
      (∑ w ∈ primaryDisc M, ∑ z ∈ primaryDisc N,
          epsSummand e
            (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
            (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
        = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ∑ w ∈ primarySet m, ∑ z ∈ primarySet n,
              epsSummand e
                (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
                (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z :=
    fun e => sum_primaryDisc_two M N (fun w z => epsSummand e
      (fun w => α (Work.FIPlan.gnorm w) * ψ w * ((DirichletSym e w : ℤ) : ℂ))
      (fun z => β (Work.FIPlan.gnorm z) * ψ z * ((DirichletSym e z : ℤ) : ℂ)) w z)
  rw [Finset.sum_congr rfl (fun e _ => by rw [hstep e])]
  rw [sum_swap_const_mul (s := primaryPrimSet c) (t := Finset.Icc 1 M) (u := Finset.Icc 1 N)]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  rw [LG]
  by_cases hmn : Nat.Coprime m n
  · rw [if_pos hmn]
    exact sum_epsSummand_ppSet_coprime hmn α β ψ
  · rw [if_neg hmn, zero_mul]
    exact sum_epsSummand_ppSet_not_coprime hmn α β ψ

/-! ## 6. The theorem -/

theorem LBilinStar_eq_epsSums {M N c : ℕ} (hc : 1 ≤ c) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (k : ℤ) (χ : GaussianInt → ℂ)
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → χ (z1 * z2) = χ z1 * χ z2)
    (α β : ℕ → ℂ)
    (hαc : ∀ m, m ∈ Finset.Icc 1 M → α m ≠ 0 → Nat.Coprime m c)
    (hβc : ∀ n, n ∈ Finset.Icc 1 N → β n ≠ 0 → Nat.Coprime n c) :
    LBilinStar M N c (grossenChar χ k) α β
      = ∑ e ∈ primaryPrimSet c,
          grossenChar χ k e * JKSym e *
            (∑ w ∈ primaryDisc M, ∑ z ∈ primaryDisc N,
              epsSummand e
                (fun w => (α (Work.FIPlan.gnorm w)) * grossenChar χ k w
                  * ((DirichletSym e w : ℤ) : ℂ))
                (fun z => (β (Work.FIPlan.gnorm z)) * grossenChar χ k z
                  * ((DirichletSym e z : ℤ) : ℂ))
                w z) := by
  rw [LBilinStar_eq_sum_LG_TripleSum hc hM hN k χ hmul α β hαc hβc]
  rw [epsSums_eq_sum_LG_TripleSum α β (grossenChar χ k)]

end

end Work.FIArea7.P231
