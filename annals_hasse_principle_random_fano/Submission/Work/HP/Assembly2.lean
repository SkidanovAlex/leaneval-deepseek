import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.IntForm

/-!
# Assembling Proposition 2 (node N13) from the product-factors bound and the sibling nodes

`prop2_of_pf` proves the statement of `Work.HP.prop2` from

* the product-factors bound `sigmaLoc a W * tauArch a (log B) ≤ C * NVloc a B / φ + C / B^(1/n)`
  for `B = A φ` (the paper's Lemma product factors), and
* the two sibling nodes N11 (`Work.HP.nonarch`) and N12 (`Work.HP.arch`), whose statements are
  taken here as hypotheses with the parameter `C` universally quantified.

The proof is the paper's: `N_V^loc ≤ φ^{2/3}` and the product bound force
`min (σ, τ) ≤ φ^{-1/6}`, and then the union bound over the two sibling nodes gives the result.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators

namespace Work.HP

/-- Height balls are finite: `primSet` is contained in a finite box. -/
theorem pf_primSet_finite (d n : ℕ) (A : ℝ) (P : (Mon d n → ℤ) → Prop) :
    (primSet d n A P).Finite := by
  have hsub : primSet d n A P ⊆
      {a : Mon d n → ℤ | ∀ m, a m ∈ Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)} := by
    intro a ha m
    obtain ⟨hprim, hnorm, hP⟩ := ha
    rw [Finset.mem_Icc]
    have hsquare : ((a m : ℝ)) ^ 2 ≤ ∑ m' : Mon d n, ((a m' : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun m' => ((a m' : ℝ)) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ m)
    have h1 : |((a m : ℤ) : ℝ)| ≤ A := by
      calc |((a m : ℤ) : ℝ)| = Real.sqrt (((a m : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (∑ m' : Mon d n, ((a m' : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsquare
        _ = eNorm a := rfl
        _ ≤ A := hnorm
    have hceil : A ≤ (((⌈A⌉₊ : ℤ)) : ℝ) := by
      have := Nat.le_ceil A; push_cast; exact this
    have hle := abs_le.mp h1
    refine ⟨?_, ?_⟩
    · exact_mod_cast (show -(((⌈A⌉₊ : ℤ)) : ℝ) ≤ ((a m : ℤ) : ℝ) from by linarith [hle.1, hceil])
    · exact_mod_cast (show ((a m : ℤ) : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) from by linarith [hle.2, hceil])
  have hpi : ({a : Mon d n → ℤ | ∀ m, a m ∈ Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)}).Finite := by
    have h := Set.Finite.pi (t := fun _m : Mon d n =>
      (Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ) : Set ℤ)) (fun _ => Finset.finite_toSet _)
    simpa [Set.pi] using h
  exact hpi.subset hsub

section assembly

variable {d n : ℕ}

/-- The assembly of Proposition 2: from the product-factors bound `hPF` and the two sibling nodes
N11 (`hN11`) and N12 (`hN12`), both with the constant `C` universally quantified, the conclusion
of `Work.HP.prop2` follows. -/
theorem prop2_of_pf (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (hPF : ∃ C A₀ : ℝ, 0 < C ∧ ∀ A φ : ℝ, A₀ ≤ A → 1 < φ → ∀ a : Mon d n → ℤ,
      IsPrim a → eNorm a ≤ A → RealSol d n a →
      sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ))
        ≤ C * NVloc d n a (A * φ) / φ + C / (A * φ) ^ ((1 : ℝ) / (n : ℝ)))
    (hN11 : ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧ ∀ φ : ℝ, 1 < φ → ∀ᶠ A in atTop,
      primCount d n A (fun a => LocSet d n (wOf (A * φ)) a ∧
          sigmaLoc d n a (bigW (wOf (A * φ))) < C / φ ^ ((1 : ℝ) / 6))
        ≤ K * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ))))
    (hN12 : ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧ ∀ φ : ℝ, 1 < φ → ∀ᶠ A in atTop,
      primCount d n A (fun a => RealSol d n a ∧
          tauArch d n (toR a) (Real.log (A * φ)) < C / φ ^ ((1 : ℝ) / 6))
        ≤ K * A ^ NN d n / φ ^ (1 / (6 * (n : ℝ)))) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ : ℝ, 1 < φ → ∀ᶠ A in atTop,
      primCount d n A (fun a => LocSet d n (wOf (A * φ)) a ∧ NVloc d n a (A * φ) ≤ φ ^ ((2 : ℝ) / 3))
        ≤ K * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ))) := by

  obtain ⟨C, A₀, hCpos, hPF'⟩ := hPF
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n ≤ 2 := by omega
    have hd2 : d = 2 := by omega
    have hn2' : n = 2 := by omega
    exact h22 (by simp [hd2, hn2'])
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  set C₂ : ℝ := Real.sqrt (8 * C) with hC₂def
  have hC₂pos : 0 < C₂ := by
    rw [hC₂def]; exact Real.sqrt_pos.mpr (by linarith)
  have hC₂sq : C₂ ^ 2 = 8 * C := by
    rw [hC₂def]; exact Real.sq_sqrt (by linarith)
  obtain ⟨K₁, hK₁pos, hb₁⟩ := hN11 C₂ hC₂pos
  obtain ⟨K₂, hK₂pos, hb₂⟩ := hN12 C₂ hC₂pos
  refine ⟨K₁ + K₂, by linarith, ?_⟩
  intro φ hφ
  have hφ1 : (1 : ℝ) < φ := hφ
  have hφpos : 0 < φ := lt_trans zero_lt_one hφ
  filter_upwards [hb₁ φ hφ, hb₂ φ hφ,
      eventually_ge_atTop (max A₀ (φ ^ ((n : ℝ) / 3)))] with A hA₁ hA₂ hAge
  have hAge₀ : A₀ ≤ A := le_trans (le_max_left _ _) hAge
  have hAgeφ : φ ^ ((n : ℝ) / 3) ≤ A := le_trans (le_max_right _ _) hAge
  have hApos : 0 < A :=
    lt_of_lt_of_le (by norm_num) (le_trans (Real.one_le_rpow hφ1.le (by positivity)) hAgeφ)
  -- rpow bookkeeping
  set Q : ℝ := φ ^ (-(1 / 3 : ℝ)) with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; exact Real.rpow_pos_of_pos hφpos _
  have hQinv : Q = (φ ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [hQdef]; exact Real.rpow_neg hφpos.le (1 / 3)
  have hp1 : φ ^ ((2 : ℝ) / 3) / φ = Q := by
    have h := Real.rpow_sub hφpos ((2 : ℝ) / 3) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [← h, hQdef]
    rw [show (2 : ℝ) / 3 - 1 = -(1 / 3 : ℝ) by norm_num]
  have hp2 : (φ ^ ((1 : ℝ) / 6) : ℝ) ^ 2 = φ ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (φ ^ ((1 : ℝ) / 6)) 2, ← Real.rpow_mul hφpos.le]
    rw [show (1 : ℝ) / 6 * ((2 : ℕ) : ℝ) = 1 / 3 by norm_num]
  have hthr2 : (C₂ / φ ^ ((1 : ℝ) / 6)) ^ 2 = C₂ ^ 2 / φ ^ ((1 : ℝ) / 3) := by
    rw [div_pow, hp2]
  have hdivQ : C / φ ^ ((1 : ℝ) / 3) = C * Q := by
    rw [hQinv, div_eq_mul_inv]
  -- `(A φ)^{1/n} ≥ φ^{1/3}`
  have hbnd : φ ^ ((1 : ℝ) / 3) ≤ (A * φ) ^ ((1 : ℝ) / (n : ℝ)) := by
    have hexp : (1 : ℝ) / 3 ≤ 1 / 3 + 1 / (n : ℝ) := by
      have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
      linarith
    have h1 : φ ^ ((1 : ℝ) / 3) ≤ φ ^ ((1 : ℝ) / 3 + 1 / (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hφ1.le hexp
    have h2 : φ ^ ((1 : ℝ) / 3 + 1 / (n : ℝ))
        = (φ ^ ((n : ℝ) / 3 + 1)) ^ ((1 : ℝ) / (n : ℝ)) := by
      rw [← Real.rpow_mul hφpos.le]
      congr 1
      field_simp
    have h3 : φ ^ ((n : ℝ) / 3 + 1) ≤ A * φ := by
      have hmul : φ ^ ((n : ℝ) / 3) * φ ≤ A * φ :=
        mul_le_mul_of_nonneg_right hAgeφ hφpos.le
      have heq : φ ^ ((n : ℝ) / 3) * φ = φ ^ ((n : ℝ) / 3 + 1) := by
        have h := Real.rpow_add hφpos ((n : ℝ) / 3) 1
        rw [Real.rpow_one] at h
        exact h.symm
      rw [← heq]
      exact hmul
    have h4 : (φ ^ ((n : ℝ) / 3 + 1)) ^ ((1 : ℝ) / (n : ℝ))
        ≤ (A * φ) ^ ((1 : ℝ) / (n : ℝ)) :=
      Real.rpow_le_rpow (by positivity) h3 (by positivity)
    linarith [h1, h2.le, h2.ge, h4]
  set Pbig : (Mon d n → ℤ) → Prop := fun a =>
    LocSet d n (wOf (A * φ)) a ∧ NVloc d n a (A * φ) ≤ φ ^ ((2 : ℝ) / 3) with hPbig
  set P₁ : (Mon d n → ℤ) → Prop := fun a =>
    LocSet d n (wOf (A * φ)) a ∧
      sigmaLoc d n a (bigW (wOf (A * φ))) < C₂ / φ ^ ((1 : ℝ) / 6) with hP₁
  set P₂ : (Mon d n → ℤ) → Prop := fun a =>
    RealSol d n a ∧ tauArch d n (toR a) (Real.log (A * φ)) < C₂ / φ ^ ((1 : ℝ) / 6) with hP₂
  have hsub : primSet d n A Pbig ⊆ primSet d n A P₁ ∪ primSet d n A P₂ := by
    intro a ha
    simp only [primSet, Set.mem_ofPred_eq, hPbig] at ha
    obtain ⟨hprim, hnorm, hLoc, hNV⟩ := ha
    have hPFa := hPF' A φ hAge₀ hφ1 a hprim hnorm hLoc.1
    have h1 : C * NVloc d n a (A * φ) / φ ≤ C * Q := by
      calc C * NVloc d n a (A * φ) / φ ≤ C * φ ^ ((2 : ℝ) / 3) / φ :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNV hCpos.le) hφpos.le
        _ = C * (φ ^ ((2 : ℝ) / 3) / φ) := mul_div_assoc _ _ _
        _ = C * Q := by rw [hp1]
    have h2 : C / (A * φ) ^ ((1 : ℝ) / (n : ℝ)) ≤ C * Q := by
      calc C / (A * φ) ^ ((1 : ℝ) / (n : ℝ)) ≤ C / φ ^ ((1 : ℝ) / 3) :=
            div_le_div_of_nonneg_left hCpos.le (Real.rpow_pos_of_pos hφpos _) hbnd
        _ = C * Q := hdivQ
    have hkey : sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ))
        ≤ 2 * C * Q := by
      calc sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ))
          ≤ C * NVloc d n a (A * φ) / φ + C / (A * φ) ^ ((1 : ℝ) / (n : ℝ)) := hPFa
        _ ≤ C * Q + C * Q := add_le_add h1 h2
        _ = 2 * C * Q := by ring
    have hdich : sigmaLoc d n a (bigW (wOf (A * φ))) < C₂ / φ ^ ((1 : ℝ) / 6) ∨
        tauArch d n (toR a) (Real.log (A * φ)) < C₂ / φ ^ ((1 : ℝ) / 6) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hσ, hτ⟩ := hcon
      have hσpos : 0 < C₂ / φ ^ ((1 : ℝ) / 6) :=
        div_pos hC₂pos (Real.rpow_pos_of_pos hφpos _)
      have hστnn : 0 ≤ sigmaLoc d n a (bigW (wOf (A * φ))) := le_trans hσpos.le hσ
      have hmul : (C₂ / φ ^ ((1 : ℝ) / 6)) * (C₂ / φ ^ ((1 : ℝ) / 6))
          ≤ sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ)) := by
        calc (C₂ / φ ^ ((1 : ℝ) / 6)) * (C₂ / φ ^ ((1 : ℝ) / 6))
            ≤ sigmaLoc d n a (bigW (wOf (A * φ))) * (C₂ / φ ^ ((1 : ℝ) / 6)) :=
              mul_le_mul_of_nonneg_right hσ hσpos.le
          _ ≤ sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ)) :=
              mul_le_mul_of_nonneg_left hτ hστnn
      have hchain : C₂ ^ 2 / φ ^ ((1 : ℝ) / 3) ≤ 2 * C * Q := by
        calc C₂ ^ 2 / φ ^ ((1 : ℝ) / 3)
            = (C₂ / φ ^ ((1 : ℝ) / 6)) * (C₂ / φ ^ ((1 : ℝ) / 6)) := by
              rw [← hthr2, pow_two]
          _ ≤ sigmaLoc d n a (bigW (wOf (A * φ))) * tauArch d n (toR a) (Real.log (A * φ)) := hmul
          _ ≤ 2 * C * Q := hkey
      rw [hC₂sq] at hchain
      have hchainQ : 8 * C * Q ≤ 2 * C * Q := by
        rw [hQinv] at hchain ⊢
        rwa [div_eq_mul_inv] at hchain
      have hCQ : 0 < C * Q := mul_pos hCpos hQpos
      nlinarith [hchainQ, hCQ]
    rw [Set.mem_union]
    rcases hdich with hσ | hτ
    · left
      simp only [primSet, Set.mem_ofPred_eq, hP₁]
      exact ⟨hprim, hnorm, hLoc, hσ⟩
    · right
      simp only [primSet, Set.mem_ofPred_eq, hP₂]
      exact ⟨hprim, hnorm, hLoc.1, hτ⟩
  have hle : primCount d n A Pbig ≤ primCount d n A P₁ + primCount d n A P₂ := by
    have hfinu : (primSet d n A P₁ ∪ primSet d n A P₂).Finite :=
      (pf_primSet_finite d n A P₁).union (pf_primSet_finite d n A P₂)
    have hcard : (primSet d n A Pbig).ncard ≤ (primSet d n A P₁ ∪ primSet d n A P₂).ncard :=
      Set.ncard_le_ncard hsub hfinu
    have hcast : ((primSet d n A Pbig).ncard : ℝ)
        ≤ ((primSet d n A P₁).ncard : ℝ) + ((primSet d n A P₂).ncard : ℝ) := by
      have h := (Nat.cast_le (α := ℝ)).mpr (le_trans hcard (Set.ncard_union_le _ _))
      push_cast at h
      linarith [h]
    simpa only [primCount] using hcast
  have h24 : (1 : ℝ) / (24 * (n : ℝ)) ≤ 1 / (6 * (n : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by nlinarith [hn0] : (6 : ℝ) * (n : ℝ) ≤ 24 * (n : ℝ))
  have hexp24 : φ ^ (1 / (24 * (n : ℝ))) ≤ φ ^ (1 / (6 * (n : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hφ1.le h24
  calc primCount d n A Pbig ≤ primCount d n A P₁ + primCount d n A P₂ := hle
    _ ≤ K₁ * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ)))
          + K₂ * A ^ NN d n / φ ^ (1 / (6 * (n : ℝ))) := add_le_add hA₁ hA₂
    _ ≤ (K₁ + K₂) * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ))) := by
        have hstep : K₂ * A ^ NN d n / φ ^ (1 / (6 * (n : ℝ)))
            ≤ K₂ * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ))) :=
          div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hφpos _) hexp24
        have heq : K₁ * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ)))
            + K₂ * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ)))
            = (K₁ + K₂) * A ^ NN d n / φ ^ (1 / (24 * (n : ℝ))) := by ring
        linarith [hstep, heq.le, heq.ge]

end assembly

end Work.HP

