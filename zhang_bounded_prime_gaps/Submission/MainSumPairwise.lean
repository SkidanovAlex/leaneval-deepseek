import Mathlib
import Submission.SieveExpansion
import Submission.PairwiseLemma41
import Submission.PairwiseFourier

open scoped BigOperators

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# The main sum of Theorem 3.6(i) as a pairwise divisor sum

Polymath8a Theorem 3.6(i) evaluates the residue-window product of the Maynard
divisor sums `λ_{Fᵢ}·λ_{Gᵢ}`.  `Submission/SieveExpansion.lean` writes that
product as `goodMainSum + goodErrSum`; this module performs the algebraic
identification of the main part with the pairwise divisor sum of
`Submission/PairwiseLemma41.lean`:

    goodMainSum (μF_i(log_R ·)) (μG_i(log_R ·))
      = (N/W) · Σ_{d,e good} ∏_i μ(d_i)μ(e_i)F_i(log_R d_i)G_i(log_R e_i)/[d_i,e_i] .

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The main term of a divisor pair is `(N/W)·∏ᵢ 1/mᵢ`. -/
lemma mainTerm_eq_mul_prod_inv (N W : ℕ) (hW : W ≠ 0) {k : ℕ} (m : Fin k → ℕ) :
    mainTerm N W m = ((N : ℝ) / (W : ℝ)) * ∏ i : Fin k, (1 / ((m i : ℕ) : ℝ)) := by
  rw [mainTerm]
  have hcast : ((W * ∏ i : Fin k, m i : ℕ) : ℝ) = (W : ℝ) * ∏ i : Fin k, ((m i : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_prod]
  rw [hcast]
  rw [show (∏ i : Fin k, (1 / ((m i : ℕ) : ℝ))) = 1 / ∏ i : Fin k, ((m i : ℕ) : ℝ) from ?_]
  · rw [div_mul_div_comm]; ring
  · simp only [one_div]
    exact Finset.prod_inv_distrib (s := Finset.univ) (f := fun i : Fin k => ((m i : ℕ) : ℝ))

/-- **The main summand as `(N/W)` times the pairwise weight.** -/
lemma coefProd_mul_mainTerm_lcm (N W : ℕ) (hW : W ≠ 0) {k : ℕ}
    (α β : Fin k → ℕ → ℝ) (d e : Fin k → ℕ) :
    coefProd α β d e * mainTerm N W (fun i => Nat.lcm (d i) (e i)) =
      ((N : ℝ) / (W : ℝ)) *
        ∏ i : Fin k,
          (α i (d i) * β i (e i) / ((Nat.lcm (d i) (e i) : ℕ) : ℝ)) := by
  rw [mainTerm_eq_mul_prod_inv N W hW, coefProd]
  rw [show (∏ i : Fin k, α i (d i) * β i (e i)) *
        (((N : ℝ) / (W : ℝ)) * ∏ i : Fin k, (1 / ((Nat.lcm (d i) (e i) : ℕ) : ℝ))) =
      ((N : ℝ) / (W : ℝ)) * ((∏ i : Fin k, α i (d i) * β i (e i)) *
        ∏ i : Fin k, (1 / ((Nat.lcm (d i) (e i) : ℕ) : ℝ))) from by ring]
  rw [← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring

/-- **The `goodMainSum` with Maynard weights is `(N/W)` times the pairwise
divisor sum.** -/
theorem goodMainSum_lamDiv_eq_mul_pairwiseSum {k D N W : ℕ} (hW : W ≠ 0)
    (F G : Fin k → ℝ → ℝ) (R : ℕ) :
    goodMainSum (k := k) (D := D) (N := N) (W := W)
        (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d) =
      ((N : ℝ) / (W : ℝ)) *
        ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          goodInd W d e * ∏ i : Fin k,
            (lamDivWeight (F i) R (d i : ℕ) * lamDivWeight (G i) R (e i : ℕ) /
              ((Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ)) := by
  classical
  rw [goodMainSum]
  rw [show (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        goodInd W d e *
          (coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))) =
      ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        ((N : ℝ) / (W : ℝ)) * (goodInd W d e * ∏ i : Fin k,
            (lamDivWeight (F i) R (d i : ℕ) * lamDivWeight (G i) R (e i : ℕ) /
              ((Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ))) from by
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
    rw [coefProd_mul_mainTerm_lcm N W hW]
    ring]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]

/-- The pairwise divisor-sum weight, as a **real** number. -/
noncomputable def pairWeightDivR {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (t : Fin k → ℕ × ℕ) : ℝ :=
  if (∀ j : Fin k, ((t j).1.lcm (t j).2).Coprime q) ∧ PairwiseCoprimeK t then
    ∏ j : Fin k, (lamDivWeight (F j) R (t j).1 * lamDivWeight (G j) R (t j).2 /
      ((Nat.lcm (t j).1 (t j).2 : ℕ) : ℝ))
  else 0

lemma pairWeightDivR_cast {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (t : Fin k → ℕ × ℕ) :
    ((pairWeightDivR F G q R t : ℝ) : ℂ) = pairWeightDiv F G q R t := by
  rw [pairWeightDivR, pairWeightDiv]
  split_ifs with h
  · rw [Complex.ofReal_prod (s := Finset.univ)
      (f := fun j : Fin k => lamDivWeight (F j) R (t j).1 * lamDivWeight (G j) R (t j).2 /
        ((Nat.lcm (t j).1 (t j).2 : ℕ) : ℝ))]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [mobiusLcmWeight, if_pos (h.1 j)]
    simp only [lamDivWeight, moebiusReal, logR, div_eq_mul_inv]
    push_cast
    ring
  · rw [Complex.ofReal_zero]

/-- The good-pair indicator times the product form is the real pairwise weight. -/
lemma goodInd_mul_prod_eq_pairWeightDivR {k D W R : ℕ} (F G : Fin k → ℝ → ℝ)
    (d e : Fin k → Fin (D + 1)) :
    goodInd W d e * ∏ i : Fin k,
        (lamDivWeight (F i) R (d i : ℕ) * lamDivWeight (G i) R (e i : ℕ) /
          ((Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ)) =
      pairWeightDivR F G W R (fun i => (((d i : Fin (D + 1)) : ℕ), ((e i : Fin (D + 1)) : ℕ))) := by
  rw [pairWeightDivR, goodInd]
  have hiff : ((∀ j : Fin k, ((Nat.lcm (d j : ℕ) (e j : ℕ)).Coprime W)) ∧
      PairwiseCoprimeK (fun i => (((d i : Fin (D + 1)) : ℕ), ((e i : Fin (D + 1)) : ℕ)))) ↔
      lcmGood W d e := Iff.rfl
  by_cases h : lcmGood W d e
  · rw [if_pos h, if_pos (hiff.mpr h), one_mul]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
    ring

/-- **The finite divisor sum equals the pairwise `tsum`.** -/
theorem sum_fin_eq_tsum {k D W R : ℕ} (F G : Fin k → ℝ → ℝ)
    (hzero : ∀ t : Fin k → ℕ × ℕ, (∃ i : Fin k, D < (t i).1 ∨ D < (t i).2) →
      pairWeightDiv F G W R t = 0) :
    ((∑ d : Fin k → Fin (D + 1), ∑ e : Fin k → Fin (D + 1),
        goodInd W d e * ∏ i : Fin k,
          (lamDivWeight (F i) R (d i : ℕ) * lamDivWeight (G i) R (e i : ℕ) /
            ((Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ))) : ℂ)
      = ∑' t : Fin k → ℕ × ℕ, pairWeightDiv F G W R t := by
  classical
  set g : ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))) → (Fin k → ℕ × ℕ) :=
    fun p i => (((p.1 i : Fin (D + 1)) : ℕ), ((p.2 i : Fin (D + 1)) : ℕ)) with hg
  set s : Finset (Fin k → ℕ × ℕ) := Finset.univ.image g with hs
  have hinj : Set.InjOn g (Finset.univ : Finset
      ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))) := by
    intro p _ p' _ hpp
    have h1 : p.1 = p'.1 := by
      funext i
      exact Fin.ext (by simpa using congrArg Prod.fst (congrFun hpp i))
    have h2 : p.2 = p'.2 := by
      funext i
      exact Fin.ext (by simpa using congrArg Prod.snd (congrFun hpp i))
    exact Prod.ext h1 h2
  have hzero' : ∀ t ∉ s, pairWeightDiv F G W R t = 0 := by
    intro t ht
    refine hzero t ?_
    by_contra hcon
    push_neg at hcon
    apply ht
    rw [hs]
    refine Finset.mem_image.mpr ⟨(fun i => ⟨(t i).1, by have := hcon i; omega⟩,
      fun i => ⟨(t i).2, by have := hcon i; omega⟩), Finset.mem_univ _, ?_⟩
    funext i
    simp [hg]
  rw [tsum_eq_sum (s := s) hzero', hs, Finset.sum_image hinj]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun e _ => ?_))
  rw [← Complex.ofReal_mul, goodInd_mul_prod_eq_pairWeightDivR, pairWeightDivR_cast]

end Commons.NumberTheory.MaynardSieve
