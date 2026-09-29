import Mathlib
import Submission.Work.TMC7Core.Fourier.ldt_setup

namespace Work.TMC7Core.Fourier

/-- `fracDist` is even. -/
private lemma fracDist_neg_own (x : ℝ) : fracDist (-x) = fracDist x := by
  apply le_antisymm
  · have h := round_le (-x) (-round x)
    rw [fracDist, fracDist]
    refine h.trans (le_of_eq ?_)
    rw [show (-x - ((-round x : ℤ) : ℝ)) = -(x - (round x : ℝ)) by push_cast; ring, abs_neg]
  · have h := round_le x (-round (-x))
    rw [fracDist, fracDist]
    refine h.trans (le_of_eq ?_)
    rw [show (x - ((-round (-x) : ℤ) : ℝ)) = -(-x - (round (-x) : ℝ)) by push_cast; ring, abs_neg]

/-- Pointwise bound on the truncated Fourier sum, given the arithmetic bound `harith`
(the Bourgain--Goldstein Fejér/Diophantine estimate). -/
theorem trig_bound_of_arith (α : ℝ) (a : ℤ) (q s K : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s) (hK : 0 < K)
    (u : ℤ → ℂ) (hu : ∀ k : ℤ, k ≠ 0 → ‖u k‖ ≤ 1 / |(k:ℝ)|)
    (hfej : ∀ R' : ℕ, 1 ≤ R' → ∀ θ : ℝ,
      fejerKer R' θ ≤ 2 / (1 + ((R':ℝ) * fracDist θ) ^ 2))
    (hcop : Nat.Coprime (Int.natAbs a) q) (hα : |α - (a:ℝ)/(q:ℝ)| < 1/((q:ℝ)^2))
    (harith : (∑ k ∈ Finset.Icc 1 K,
        (1 / (k : ℝ)) * (1 + ((s : ℝ) * (q : ℝ) * fracDist ((k : ℝ) * α)) ^ 2)⁻¹)
      ≤ 50 / ((s : ℝ) ^ 2) + (1 + 50 / (s : ℝ)) * (1 / (q : ℝ)) * Real.log (1 + (K : ℝ) / (q : ℝ))
        + 100 / (q : ℝ)) :
    ∀ x : ℝ, ‖∑ k ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun k => k ≠ 0),
        u k * (fejerKer (q*s) ((k:ℝ)*α) : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x)‖
      ≤ 4 * (50/((s:ℝ)^2) + (1 + 50/(s:ℝ)) * (1/(q:ℝ)) * Real.log (1 + (K:ℝ)/(q:ℝ))
          + 100/(q:ℝ)) := by
  intro x
  set T : Finset ℤ := (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun k => k ≠ 0) with hT
  set G : ℤ → ℝ := fun k => (1 / |(k:ℝ)|) * (2 / (1 + (((q*s:ℕ):ℝ) * fracDist ((k:ℝ)*α))^2)) with hG
  have hqs : 1 ≤ q*s := by
    have : 0 < q*s := Nat.mul_pos (by omega) (by omega)
    omega
  have hterm : ∀ k ∈ T, ‖u k * (fejerKer (q*s) ((k:ℝ)*α) : ℂ)
      * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x)‖ ≤ G k := by
    intro k hk
    have hkne : k ≠ 0 := (Finset.mem_filter.mp hk).2
    have hexp : ‖Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x)‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (2*Real.pi*Complex.I*(k:ℝ)*x).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    have hfejC : ‖((fejerKer (q*s) ((k:ℝ)*α) : ℝ) : ℂ)‖ = fejerKer (q*s) ((k:ℝ)*α) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (fejerKer_nonneg _ _)]
    simp only [hG]
    rw [norm_mul, norm_mul, hfejC, hexp, mul_one]
    exact mul_le_mul (hu k hkne) (hfej (q*s) hqs ((k:ℝ)*α)) (fejerKer_nonneg _ _)
      (div_nonneg zero_le_one (abs_nonneg _))
  have hGsym : ∀ k : ℤ, G (-k) = G k := by
    intro k
    have h1 : ((-k:ℤ):ℝ) = -(k:ℝ) := by push_cast; ring
    have h2 : fracDist ((-(k:ℝ))*α) = fracDist ((k:ℝ)*α) := by
      rw [show (-(k:ℝ))*α = -((k:ℝ)*α) by ring, fracDist_neg_own]
    simp only [hG, h1, h2, abs_neg]
  have hTp : T.filter (fun k => 0 < k) = Finset.Icc (1:ℤ) (K:ℤ) := by
    ext k
    simp only [hT, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hk1, hk2⟩, hk3⟩, hk4⟩
      exact ⟨by omega, hk2⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega
  have hTn : T.filter (fun k => ¬ 0 < k) = Finset.Icc (-(K:ℤ)) (-1:ℤ) := by
    ext k
    simp only [hT, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hk1, hk2⟩, hk3⟩, hk4⟩
      exact ⟨hk1, by omega⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega
  have hsplit : ∑ k ∈ T, G k
      = ∑ k ∈ Finset.Icc (1:ℤ) (K:ℤ), G k + ∑ k ∈ Finset.Icc (-(K:ℤ)) (-1:ℤ), G k := by
    rw [← hTp, ← hTn, ← Finset.sum_filter_add_sum_filter_not T (fun k => 0 < k) G]
  have hneg : ∑ k ∈ Finset.Icc (-(K:ℤ)) (-1:ℤ), G k = ∑ k ∈ Finset.Icc (1:ℤ) (K:ℤ), G k := by
    refine Finset.sum_bij (fun k _ => -k) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k1 hk1 k2 hk2 h; omega
    · intro b hb; simp only [Finset.mem_Icc] at hb
      refine ⟨-b, ?_, by simp⟩
      simp only [Finset.mem_Icc]; omega
    · intro k hk; exact (hGsym k).symm
  have hTsplit : ∑ k ∈ T, G k = 2 * ∑ k ∈ Finset.Icc (1:ℤ) (K:ℤ), G k := by
    rw [hsplit, hneg]; ring
  have hcast1 : ∑ k ∈ Finset.Icc 1 K, G (k:ℤ) = ∑ k ∈ Finset.Icc (1:ℤ) (K:ℤ), G k := by
    refine Finset.sum_bij (fun a _ => ((a:ℤ))) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
    · intro a1 ha1 a2 ha2 h
      exact_mod_cast h
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨b.toNat, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        exact ⟨by omega, by omega⟩
      · simp only [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ b)]
    · intro a ha; rfl
  have hcast2 : ∑ k ∈ Finset.Icc 1 K, G (k:ℤ)
      = 2 * ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ))*(1+((s:ℝ)*(q:ℝ)*fracDist ((k:ℝ)*α))^2)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    simp only [hG]
    push_cast
    rw [abs_of_pos hkpos, mul_comm (q:ℝ) (s:ℝ), div_eq_mul_inv]
    ring
  have htotal : ∑ k ∈ T, G k
      = 4 * ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ))*(1+((s:ℝ)*(q:ℝ)*fracDist ((k:ℝ)*α))^2)⁻¹ := by
    rw [hTsplit, ← hcast1, hcast2]; ring
  calc ‖∑ k ∈ T, u k * (fejerKer (q*s) ((k:ℝ)*α) : ℂ)
        * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x)‖
      ≤ ∑ k ∈ T, ‖u k * (fejerKer (q*s) ((k:ℝ)*α) : ℂ)
          * Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ T, G k := Finset.sum_le_sum hterm
    _ = 4 * ∑ k ∈ Finset.Icc 1 K,
          (1/(k:ℝ))*(1+((s:ℝ)*(q:ℝ)*fracDist ((k:ℝ)*α))^2)⁻¹ := htotal
    _ ≤ 4 * (50/((s:ℝ)^2) + (1 + 50/(s:ℝ)) * (1/(q:ℝ)) * Real.log (1 + (K:ℝ)/(q:ℝ))
          + 100/(q:ℝ)) :=
        mul_le_mul_of_nonneg_left (harith) (by norm_num)



end Work.TMC7Core.Fourier
