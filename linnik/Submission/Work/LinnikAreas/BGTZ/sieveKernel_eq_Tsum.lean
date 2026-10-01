import Mathlib
import Submission.Work.LinnikAreas.BGTZ.SelbergLocal
import Submission.Work.LinnikAreas.BGTZ.SelbergReindex

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-!
## Rewriting the Selberg sieve kernel as a sum over admissible indices

The double sum `Σ_{d,e ≤ R} θ_d θ_e ∏_{p | [d,e]} Re (sieveLocal χ₁ χ₀ 1 p)` of the sieve
kernel collapses to a sum over the *squarefree* `d, e ≤ R` that are coprime to `q`: the weights
`θ_d` vanish off the squarefree numbers (`IsSieveWeight`), and the local factor at any prime
`p | q` vanishes, so a common prime of `[d,e]` and `q` kills the term.  For the surviving
indices the local product is `1/h([d,e])` (`sieveLocal_re_prod`), which is exactly the
right-hand side.
-/

/-- The admissible set of indices: squarefree and coprime to `q`. -/
private def sieveSupport (q R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q)

/-- The summand of the sieve kernel. -/
private noncomputable def kern (χ₁ : DirichletCharacter ℂ q) (θw : ℕ → ℝ) (d e : ℕ) : ℝ :=
  θw d * θw e * ∏ p ∈ (Nat.lcm d e).primeFactors,
    (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) (1 : ℂ) p).re

omit [NeZero q] in
private lemma kern_not_squarefree_left (χ₁ : DirichletCharacter ℂ q) {R : ℕ}
    {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {d e : ℕ} (hd : ¬ Squarefree d) :
    kern χ₁ θw d e = 0 := by
  unfold kern; simp [hθ.2.1 d (Or.inl hd)]

omit [NeZero q] in
private lemma kern_not_squarefree_right (χ₁ : DirichletCharacter ℂ q) {R : ℕ}
    {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {d e : ℕ} (he : ¬ Squarefree e) :
    kern χ₁ θw d e = 0 := by
  unfold kern; simp [hθ.2.1 e (Or.inl he)]

private lemma kern_not_coprime_left (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {θw : ℕ → ℝ} {d e : ℕ} (hd0 : d ≠ 0) (he0 : e ≠ 0) (hcop : ¬ Nat.Coprime d q) :
    kern χ₁ θw d e = 0 := by
  unfold kern
  have hg : Nat.gcd d q ≠ 1 := fun h => hcop h
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left d q)
  have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right d q)
  have hpml : p ∈ (Nat.lcm d e).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpd.trans (Nat.dvd_lcm_left d e), Nat.lcm_ne_zero hd0 he0⟩
  have hzero : (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) (1 : ℂ) p).re = 0 := by
    rw [sieveLocal_prime_re χ₁ hχ₁ p hp, if_pos hpq]
  rw [Finset.prod_eq_zero hpml hzero, mul_zero]

private lemma kern_not_coprime_right (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {θw : ℕ → ℝ} {d e : ℕ} (hd0 : d ≠ 0) (he0 : e ≠ 0) (hcop : ¬ Nat.Coprime e q) :
    kern χ₁ θw d e = 0 := by
  unfold kern
  have hg : Nat.gcd e q ≠ 1 := fun h => hcop h
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpe : p ∣ e := hpg.trans (Nat.gcd_dvd_left e q)
  have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right e q)
  have hpml : p ∈ (Nat.lcm d e).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpe.trans (Nat.dvd_lcm_right d e), Nat.lcm_ne_zero hd0 he0⟩
  have hzero : (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) (1 : ℂ) p).re = 0 := by
    rw [sieveLocal_prime_re χ₁ hχ₁ p hp, if_pos hpq]
  rw [Finset.prod_eq_zero hpml hzero, mul_zero]

/-- For admissible `d, e` the local product is `1/h([d,e])`. -/
private lemma kern_eq_div (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {θw : ℕ → ℝ} {d e : ℕ} (hdsf : Squarefree d) (hesf : Squarefree e)
    (hdc : Nat.Coprime d q) (hec : Nat.Coprime e q) :
    kern χ₁ θw d e = θw d * θw e / Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e) := by
  unfold kern
  have hsf : Squarefree (Nat.lcm d e) := squarefree_lcm' hdsf hesf
  have hcop : Nat.Coprime (Nat.lcm d e) q :=
    (Nat.Coprime.mul_left hdc hec).coprime_dvd_left (Nat.lcm_dvd_mul d e)
  rw [sieveLocal_re_prod χ₁ hχ₁ (Nat.lcm d e) hsf, if_pos hcop, div_eq_mul_inv]

theorem sieveKernel_eq_Tsum {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (hχ₁ : χ₁ ^ 2 = 1) (R : ℕ) {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) :
    (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, θw d * θw e *
        ∏ p ∈ (Nat.lcm d e).primeFactors,
          (sieveLocal χ₁ (1 : DirichletCharacter ℂ q) (1 : ℂ) p).re)
      = ∑ d ∈ (Finset.Icc 1 R).filter (fun d => Squarefree d ∧ Nat.Coprime d q),
          ∑ e ∈ (Finset.Icc 1 R).filter (fun e => Squarefree e ∧ Nat.Coprime e q),
            θw d * θw e / Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e) := by
  classical
  show (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, kern χ₁ θw d e)
      = ∑ d ∈ sieveSupport q R, ∑ e ∈ sieveSupport q R,
          θw d * θw e / Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e)
  have hST : sieveSupport q R ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
  have hinner : ∀ d ∈ Finset.Icc 1 R,
      (∑ e ∈ sieveSupport q R, kern χ₁ θw d e)
        = ∑ e ∈ Finset.Icc 1 R, kern χ₁ θw d e := by
    intro d hd
    refine Finset.sum_subset hST (fun e heT heS => ?_)
    have hc : ¬ (Squarefree e ∧ Nat.Coprime e q) := by
      intro hce
      exact heS (Finset.mem_filter.mpr ⟨heT, hce⟩)
    rcases not_and_or.mp hc with hsf | hcop
    · exact kern_not_squarefree_right χ₁ hθ hsf
    · exact kern_not_coprime_right χ₁ hχ₁
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hd).1)
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp heT).1) hcop
  have houter : (∑ d ∈ sieveSupport q R, ∑ e ∈ sieveSupport q R, kern χ₁ θw d e)
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ sieveSupport q R, kern χ₁ θw d e := by
    refine Finset.sum_subset hST (fun d hdT hdS => ?_)
    refine Finset.sum_eq_zero (fun e heS => ?_)
    have hc : ¬ (Squarefree d ∧ Nat.Coprime d q) := by
      intro hcd
      exact hdS (Finset.mem_filter.mpr ⟨hdT, hcd⟩)
    rcases not_and_or.mp hc with hsf | hcop
    · exact kern_not_squarefree_left χ₁ hθ hsf
    · exact kern_not_coprime_left χ₁ hχ₁
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hdT).1)
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp (Finset.mem_filter.mp heS).1).1) hcop
  calc (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, kern χ₁ θw d e)
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ sieveSupport q R, kern χ₁ θw d e :=
        Finset.sum_congr rfl (fun d hd => (hinner d hd).symm)
    _ = ∑ d ∈ sieveSupport q R, ∑ e ∈ sieveSupport q R, kern χ₁ θw d e := houter.symm
    _ = ∑ d ∈ sieveSupport q R, ∑ e ∈ sieveSupport q R,
          θw d * θw e / Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e) := by
        refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => ?_))
        obtain ⟨-, hdsf, hdc⟩ := Finset.mem_filter.mp hd
        obtain ⟨-, hesf, hec⟩ := Finset.mem_filter.mp he
        exact kern_eq_div χ₁ hχ₁ hdsf hesf hdc hec

end Work.LinnikAreas.BGTZ
