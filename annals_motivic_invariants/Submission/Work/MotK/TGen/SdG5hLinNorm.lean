import Mathlib
import Submission.Work.MotK.TGen.CruxAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

open MvPolynomial

/-- A monomial `v : Fin 3 →₀ ℕ` of total degree `1` is one of the three variables. -/
private lemma degree_one_eq_single {v : Fin 3 →₀ ℕ} (hv : v.degree = 1) :
    v = Finsupp.single 0 1 ∨ v = Finsupp.single 1 1 ∨ v = Finsupp.single 2 1 := by
  have hsum : v 0 + v 1 + v 2 = 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hv
    exact hv
  have h : v 0 = 1 ∧ v 1 = 0 ∧ v 2 = 0 ∨ v 0 = 0 ∧ v 1 = 1 ∧ v 2 = 0 ∨
      v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1 := by omega
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · left; ext i; fin_cases i <;> simp_all [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  · right; left; ext i; fin_cases i <;> simp_all [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]
  · right; right; ext i; fin_cases i <;> simp_all [Finsupp.single_eq_same, Finsupp.single_eq_of_ne]

theorem SdG5hLinNorm {K : Type} [Field K] (F : MvPolynomial (Fin 3) K)
    (hF : F.IsHomogeneous 1) (hc : F.coeff (Finsupp.single (0 : Fin 3) 1) ≠ 0) :
    ∃ c b d : K, c ≠ 0 ∧ F = MvPolynomial.C c *
      (MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
        + MvPolynomial.C d * MvPolynomial.X 2) := by
  have h01 : (Finsupp.single (0 : Fin 3) 1) ∉
      ({Finsupp.single (1 : Fin 3) 1, Finsupp.single (2 : Fin 3) 1} :
        Finset (Fin 3 →₀ ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h
      have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h
      simp only [Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0 : Fin 3) ≠ 1 by decide)] at h0
      exact one_ne_zero h0
    · intro h
      have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) h
      simp only [Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0 : Fin 3) ≠ 2 by decide)] at h0
      exact one_ne_zero h0
  have h12 : (Finsupp.single (1 : Fin 3) 1) ∉
      ({Finsupp.single (2 : Fin 3) 1} : Finset (Fin 3 →₀ ℕ)) := by
    simp only [Finset.mem_singleton]
    intro h
    have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
    simp only [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 : Fin 3) ≠ 2 by decide)] at h0
    exact one_ne_zero h0
  have hsub : F.support ⊆ ({Finsupp.single (0 : Fin 3) 1, Finsupp.single 1 1,
      Finsupp.single 2 1} : Finset (Fin 3 →₀ ℕ)) := by
    intro v hv
    rw [mem_support_iff] at hv
    have hdeg : v.degree = 1 := by
      by_contra hd
      exact hv (by apply hF.coeff_eq_zero;
                      simpa only [Finsupp.degree_eq_weight_one] using hd)
    have := degree_one_eq_single hdeg
    rcases this with h | h | h <;> subst h <;> simp
  have hmain : F = C (F.coeff (Finsupp.single (0 : Fin 3) 1)) * X 0
      + C (F.coeff (Finsupp.single (1 : Fin 3) 1)) * X 1
      + C (F.coeff (Finsupp.single (2 : Fin 3) 1)) * X 2 := by
    have h1 : ∑ v ∈ F.support, monomial v (F.coeff v)
        = ∑ v ∈ ({Finsupp.single (0 : Fin 3) 1, Finsupp.single 1 1,
            Finsupp.single 2 1} : Finset (Fin 3 →₀ ℕ)), monomial v (F.coeff v) :=
      Finset.sum_subset hsub (fun v _ hvsup => by
        rw [mem_support_iff, not_not] at hvsup
        simp [hvsup])
    conv_lhs => rw [as_sum F]
    rw [h1, Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_singleton]
    rw [← C_mul_X_eq_monomial, ← C_mul_X_eq_monomial, ← C_mul_X_eq_monomial]
    first | refl_ring1 | ring
  refine ⟨F.coeff (Finsupp.single (0 : Fin 3) 1),
    F.coeff (Finsupp.single (1 : Fin 3) 1) / F.coeff (Finsupp.single (0 : Fin 3) 1),
    F.coeff (Finsupp.single (2 : Fin 3) 1) / F.coeff (Finsupp.single (0 : Fin 3) 1),
    hc, ?_⟩
  conv_lhs => rw [hmain]
  have hb1 : F.coeff (Finsupp.single (1 : Fin 3) 1)
      = F.coeff (Finsupp.single (0 : Fin 3) 1) *
        (F.coeff (Finsupp.single (1 : Fin 3) 1) /
          F.coeff (Finsupp.single (0 : Fin 3) 1)) :=
    (mul_div_cancel₀ _ hc).symm
  have hb2 : F.coeff (Finsupp.single (2 : Fin 3) 1)
      = F.coeff (Finsupp.single (0 : Fin 3) 1) *
        (F.coeff (Finsupp.single (2 : Fin 3) 1) /
          F.coeff (Finsupp.single (0 : Fin 3) 1)) :=
    (mul_div_cancel₀ _ hc).symm
  conv_lhs => rw [hb1, hb2]
  simp only [map_mul]
  first | refl_ring1 | ring

end Work.MotK.TGen
