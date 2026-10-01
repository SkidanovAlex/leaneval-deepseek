import Mathlib
import Submission.Commons.NumberTheory.ArtinSchreier.point_count
import Submission.Commons.NumberTheory.ExponentialSums.additive_weil_from_point_count

open Polynomial

namespace Commons.NumberTheory.ExponentialSums

/-- The standard additive character of `ZMod p` is non-trivial for a prime `p`. -/
theorem stdAddChar_ne_one (p : ℕ) [Fact p.Prime] :
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
  intro h
  have h1 : (ZMod.stdAddChar (1 : ZMod p) : ℂ) = 1 := by
    have := congrFun (congrArg DFunLike.coe h) 1
    simpa using this
  have h2 : (ZMod.stdAddChar (1 : ZMod p) : ℂ) = ZMod.stdAddChar (0 : ZMod p) := by
    rw [h1]; simp
  have h3 : (1 : ZMod p) = 0 := ZMod.injective_stdAddChar h2
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  exact one_ne_zero h3

/-- **Additive Weil bound for polynomials over a prime field** (Weil, elementary proof via
Stepanov's method): there is an absolute constant `C > 0` such that for every prime `p` and
every polynomial `f` over `ZMod p` of degree `d` with `2 ≤ d < p`,
`‖∑ x, stdAddChar (f x)‖ ≤ C · d · √p`.

Assembled from the shared commons:
* `Commons.NumberTheory.ArtinSchreier.point_count` — the Stepanov point count for the
  Artin–Schreier cover `y ^ p - y = g x` over even-degree extensions of `ZMod p`;
* `Commons.NumberTheory.ExponentialSums.addchar_char_sum_power_sums` — the additive
  `L`-function over `F_p[X]` (the even Artin–Schreier sums are power sums of at most `d - 1`
  complex numbers);
* `Commons.NumberTheory.ExponentialSums.addchar_char_sum_extension_bound` — the resulting
  `O(√(#E))` bound for the Artin–Schreier sums over every extension;
* `Commons.NumberTheory.ExponentialSums.addchar_pow_sum_transference` — the eigenvalue step
  (each Weil number has modulus `≤ √p`).

The resulting constant is `2`, independent of `p` and `d`. -/
theorem additive_weil_bound_poly :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)),
      2 ≤ f.natDegree → f.natDegree < p →
      ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤ C * (f.natDegree : ℝ) * Real.sqrt (p : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro p hp f hf2 hfp
  haveI := hp
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rcases eq_or_lt_of_le hp2 with hp_eq | hp_gt
  · -- p = 2 : incompatible with `2 ≤ f.natDegree < p`
    omega
  · -- p ≥ 3
    have hψ : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := stdAddChar_ne_one p
    obtain ⟨C₀, hC₀pos, hC₀⟩ :=
      Commons.NumberTheory.ExponentialSums.addchar_char_sum_extension_bound.{0} p (p-1)
        (by omega) (by omega)
        (fun d hd => Commons.NumberTheory.ArtinSchreier.point_count.{0} p d hd)
    obtain ⟨t, ht, γ, hγ⟩ :=
      Commons.NumberTheory.ExponentialSums.addchar_char_sum_power_sums p ZMod.stdAddChar hψ f
        (by omega) hfp
    have hbdd' : ∀ k : ℕ, 0 < k → ¬ p ∣ k → ‖∑ j : Fin t, (γ j ^ 2) ^ k‖ ≤ C₀ * (p:ℝ) ^ k := by
      intro k hk hkop
      have h2k : 0 < 2*k := by omega
      letI hF : Fintype (GaloisField p (2*k)) := Fintype.ofFinite _
      letI hD : DecidableEq (GaloisField p (2*k)) := Classical.decEq _
      have hcard : (Fintype.card (GaloisField p (2*k)) : ℝ) = ((p:ℝ)^k)^2 := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card p (2*k) (by omega), Nat.cast_pow]
        ring
      have hfin : Module.finrank (ZMod p) (GaloisField p (2*k)) = 2*k :=
        GaloisField.finrank p (by omega : 2*k ≠ 0)
      have hpk : ¬ p ∣ 2*k := by
        intro hdvd
        rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hdvd with h | h
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact hkop h
      have hineq := hC₀ ZMod.stdAddChar hψ f (by omega) (by omega) (2*k) h2k hpk
        (GaloisField p (2*k)) hfin
      have hsum : (∑ a : GaloisField p (2*k),
            ZMod.stdAddChar (Algebra.trace (ZMod p) (GaloisField p (2*k))
              ((f.map (algebraMap (ZMod p) (GaloisField p (2*k)))).eval a)))
          = - ∑ j : Fin t, γ j ^ (2*k) := by
        have := hγ (2*k) (by omega) (GaloisField p (2*k)) hfin
        simpa using this
      have h3 : (∑ j : Fin t, (γ j ^ 2) ^ k) = ∑ j : Fin t, γ j ^ (2*k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [← pow_mul, mul_comm]
      rw [h3, show (∑ j : Fin t, γ j ^ (2*k)) = -(- ∑ j : Fin t, γ j ^ (2*k)) by ring,
        ← hsum, norm_neg]
      refine hineq.trans_eq ?_
      rw [hcard, Real.sqrt_sq (by positivity)]
    have hroot := Commons.NumberTheory.ExponentialSums.addchar_pow_sum_transference (p := p)
      (by have := hfp; omega : t < p) γ hC₀pos hbdd'
    have hnorm : ∀ j : Fin t, ‖γ j‖ ≤ Real.sqrt p := by
      intro j
      have hj := hroot j
      rw [norm_pow] at hj
      calc ‖γ j‖ = Real.sqrt (‖γ j‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt p := Real.sqrt_le_sqrt hj
    have hT1 : (∑ x : ZMod p, ZMod.stdAddChar (f.eval x)) = - ∑ j : Fin t, γ j := by
      have h1 := hγ 1 le_rfl (ZMod p) (Module.finrank_self (ZMod p))
      simpa only [pow_one, Algebra.trace_self, LinearMap.id_coe, id_eq,
        Algebra.algebraMap_self (R := ZMod p), Polynomial.map_id] using h1
    calc ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖
        = ‖∑ j : Fin t, γ j‖ := by rw [hT1, norm_neg]
      _ ≤ ∑ j : Fin t, ‖γ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin t, Real.sqrt p := Finset.sum_le_sum fun j _ => hnorm j
      _ = (t:ℝ) * Real.sqrt p := by simp
      _ ≤ (f.natDegree : ℝ) * Real.sqrt p := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          have ht' : t ≤ f.natDegree := le_trans ht (Nat.sub_le _ _)
          exact_mod_cast ht'
      _ ≤ 2 * (f.natDegree : ℝ) * Real.sqrt p := by
          have h1 : (1:ℝ) ≤ 2 := by norm_num
          nlinarith [Real.sqrt_nonneg (p:ℝ), Nat.cast_nonneg (α := ℝ) f.natDegree]

end Commons.NumberTheory.ExponentialSums
