import Mathlib
import Submission.PhiLemma41
import Submission.MainSumPairwise
import Submission.SieveSupport

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# The `φ`-denominator divisor sum at the ℕ level

The main term of Polymath8a Theorem 3.5 is the `φ`-denominator divisor sum

    `(1/φ(W)) · Σ_{good (d,e)} ∏_i μ(d_i)μ(e_i)/φ([d_i,e_i])·F_i(log_x d_i)G_i(log_x e_i)`,

which `Submission.PhiLemma41` (`phiPairwiseLemma41`) evaluates as
`(1+o(1))·B^{1-k}·∏∫F_i′G_i′`.  Here we connect the *finite* box sum appearing in
the sieve expansion to the ℕ-level `tsum` `pairWeightDivPhi` of the `φ`-Fubini
identity, exactly as `Submission.MainSumPairwise` does for the plain case.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The real-valued `φ`-denominator pairwise weight (the `ℝ`-shadow of
`pairWeightDivPhi`). -/
noncomputable def pairWeightDivRPhi {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (t : Fin k → ℕ × ℕ) : ℝ :=
  if (∀ j : Fin k, ((t j).1.lcm (t j).2).Coprime q) ∧ PairwiseCoprimeK t then
    ∏ j : Fin k, (lamDivWeight (F j) R (t j).1 * lamDivWeight (G j) R (t j).2 /
      (((Nat.lcm (t j).1 (t j).2).totient : ℕ) : ℝ))
  else 0

/-- The cast agreement of the real and complex `φ`-weights. -/
lemma pairWeightDivRPhi_cast {k : ℕ} (F G : Fin k → ℝ → ℝ) (q R : ℕ)
    (t : Fin k → ℕ × ℕ) :
    ((pairWeightDivRPhi F G q R t : ℝ) : ℂ) = pairWeightDivPhi F G q R t := by
  rw [pairWeightDivRPhi, pairWeightDivPhi]
  split_ifs with h
  · rw [Complex.ofReal_prod (s := Finset.univ)
      (f := fun j : Fin k => lamDivWeight (F j) R (t j).1 * lamDivWeight (G j) R (t j).2 /
        (((Nat.lcm (t j).1 (t j).2).totient : ℕ) : ℝ))]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [mobiusTotientWeight, if_pos (h.1 j)]
    simp only [lamDivWeight, moebiusReal, logR, div_eq_mul_inv]
    push_cast
    ring
  · rw [Complex.ofReal_zero]

/-- The good-pair indicator times the product form is the real `φ`-weight. -/
lemma goodInd_mul_prod_eq_pairWeightDivRPhi {k D W R : ℕ} (F G : Fin k → ℝ → ℝ)
    (d e : Fin k → Fin (D + 1)) :
    goodInd W d e * ∏ i : Fin k,
        (lamDivWeight (F i) R (d i : ℕ) * lamDivWeight (G i) R (e i : ℕ) /
          (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) =
      pairWeightDivRPhi F G W R
        (fun i => (((d i : Fin (D + 1)) : ℕ), ((e i : Fin (D + 1)) : ℕ))) := by
  rw [pairWeightDivRPhi, goodInd]
  have hiff : ((∀ j : Fin k, ((Nat.lcm (d j : ℕ) (e j : ℕ)).Coprime W)) ∧
      PairwiseCoprimeK (fun i => (((d i : Fin (D + 1)) : ℕ), ((e i : Fin (D + 1)) : ℕ)))) ↔
      lcmGood W d e := Iff.rfl
  by_cases h : lcmGood W d e
  · rw [if_pos h, if_pos (hiff.mpr h), one_mul]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
    ring

/-- **The finite `φ`-divisor sum equals the `φ`-pairwise `tsum`.** -/
theorem sum_fin_eq_tsum_phi {k D W R : ℕ} (F G : Fin k → ℝ → ℝ)
    (hzero : ∀ t : Fin k → ℕ × ℕ, (∃ i : Fin k, D < (t i).1 ∨ D < (t i).2) →
      pairWeightDivPhi F G W R t = 0) :
    ((∑ d : Fin k → Fin (D + 1), ∑ e : Fin k → Fin (D + 1),
        goodInd W d e * ∏ i : Fin k,
          (lamDivWeight (F i) R (d i : ℕ) * lamDivWeight (G i) R (e i : ℕ) /
            (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))) : ℂ)
      = ∑' t : Fin k → ℕ × ℕ, pairWeightDivPhi F G W R t := by
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
  have hzero' : ∀ t ∉ s, pairWeightDivPhi F G W R t = 0 := by
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
  rw [← Complex.ofReal_mul, goodInd_mul_prod_eq_pairWeightDivRPhi, pairWeightDivRPhi_cast]


/-- The `φ`-pairwise weight vanishes once a coordinate leaves the support of the
cutoffs. -/
theorem pairWeightDivPhi_eq_zero_of_gt {k : ℕ} (F G : Fin k → ℝ → ℝ) (R W : ℕ)
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    (hR : 1 < R) {D : ℕ} (hD : (R : ℝ) ^ M ≤ (D : ℝ)) (t : Fin k → ℕ × ℕ)
    (h : ∃ i : Fin k, D < (t i).1 ∨ D < (t i).2) : pairWeightDivPhi F G W R t = 0 := by
  rw [pairWeightDivPhi]
  by_cases hg : (∀ j : Fin k, ((t j).1.lcm (t j).2).Coprime W) ∧ PairwiseCoprimeK t
  · rw [if_pos hg]
    obtain ⟨i, hi | hi⟩ := h
    · have hd0 : (t i).1 ≠ 0 := by omega
      have hlog : M < logR (t i).1 R := by
        by_contra hcon
        push_neg at hcon
        have h2 : ((t i).1 : ℝ) ≤ (R : ℝ) ^ M := le_rpow_of_logR_le hR hd0 hcon
        have h3 : ((t i).1 : ℝ) ≤ (D : ℝ) := le_trans h2 hD
        have h4 : (t i).1 ≤ D := by exact_mod_cast h3
        omega
      have hF0 : F i (logR (t i).1 R) = 0 :=
        (hM i _ (lt_of_lt_of_le hlog (le_abs_self _))).1
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hF0])
    · have hd0 : (t i).2 ≠ 0 := by omega
      have hlog : M < logR (t i).2 R := by
        by_contra hcon
        push_neg at hcon
        have h2 : ((t i).2 : ℝ) ≤ (R : ℝ) ^ M := le_rpow_of_logR_le hR hd0 hcon
        have h3 : ((t i).2 : ℝ) ≤ (D : ℝ) := le_trans h2 hD
        have h4 : (t i).2 ≤ D := by exact_mod_cast h3
        omega
      have hG0 : G i (logR (t i).2 R) = 0 :=
        (hM i _ (lt_of_lt_of_le hlog (le_abs_self _))).2
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hG0])
  · rw [if_neg hg]

/-- **The main term of the `φ`-denominator divisor sum** (the object appearing in
Polymath8a Theorem 3.5): the good-restricted finite box sum of
`∏_i μμ/φ([d_i,e_i])·F_i(log_x d_i)G_i(log_x e_i)` equals
`(1+o(1))·(prefactor)^k·∏∫₀^∞ F_i′G_i′`, uniformly in `D ≥ x^M`. -/
theorem phiGoodMainSum_asymptotic {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (Wf : ℕ → ℕ) (hW : ∀ x, Wf x ≠ 0)
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ Wf x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log ((Wf x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ M ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖((∑ d : Fin k → Fin (D x + 1), ∑ e : Fin k → Fin (D x + 1),
              goodInd (Wf x) d e * ∏ i : Fin k,
                lamDivWeight (F i) x (d i : ℕ) * lamDivWeight (G i) x (e i : ℕ) /
                  (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) : ℂ) -
            (((prefactor Wf (fun _ => 1) x : ℝ) : ℂ) ^ k *
                ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
                  ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))‖ ≤
          ε x * prefactor Wf (fun _ => 1) x ^ k := by
  classical
  obtain ⟨x₀s, εs, hεs, hbd⟩ :=
    phiPairwiseLemma41 hk F G hcsF hsmF hcsG hsmG Wf (fun _ => 1) hW
      (fun _ => one_ne_zero) (fun x => by simp) w hw
      (fun x p hp hle => by simpa using hsmall x p hp hle) (by simpa using hlq)
  obtain ⟨x₀D, hx₀D⟩ := Filter.eventually_atTop.mp hD
  refine ⟨max (max x₀s x₀D) 2, εs, hεs, fun x hx => ?_⟩
  have hxs : x₀s ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxD : x₀D ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 < x := by omega
  have hsum := sum_fin_eq_tsum_phi (D := D x) (W := Wf x) (R := x) F G
    (fun t ht => pairWeightDivPhi_eq_zero_of_gt F G x (Wf x) hM hx1 (hx₀D x hxD) t ht)
  have hbd' : ‖(∑' t : Fin k → ℕ × ℕ, pairWeightDivPhi F G (Wf x) x t) -
      (((prefactor Wf (fun _ => 1) x : ℝ) : ℂ) ^ k *
        ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))‖ ≤
      εs x * prefactor Wf (fun _ => 1) x ^ k := by
    simpa only [mul_one] using hbd x hxs
  calc ‖((∑ d : Fin k → Fin (D x + 1), ∑ e : Fin k → Fin (D x + 1),
          goodInd (Wf x) d e * ∏ i : Fin k,
            lamDivWeight (F i) x (d i : ℕ) * lamDivWeight (G i) x (e i : ℕ) /
              (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) : ℂ) -
        (((prefactor Wf (fun _ => 1) x : ℝ) : ℂ) ^ k *
          ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
            ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))‖
      = ‖(∑' t : Fin k → ℕ × ℕ, pairWeightDivPhi F G (Wf x) x t) -
          (((prefactor Wf (fun _ => 1) x : ℝ) : ℂ) ^ k *
            ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))‖ := by
        rw [hsum]
    _ ≤ εs x * prefactor Wf (fun _ => 1) x ^ k := hbd'

end Commons.NumberTheory.MaynardSieve
