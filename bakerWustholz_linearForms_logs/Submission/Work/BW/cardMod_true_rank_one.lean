import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.ratSpan_saturation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- **From `PrimSys` to an integral multiple.**  If `M : Fin 1 → Fin N → ℤ` is a primitive system
(the single row is non-zero and its `ℤ`-span is saturated in `ℤ^N`) and the integral vector `B`
lies in the rational span of that row, then `B` is an integral multiple of the row. -/
private theorem cmtrue_prim_row_int_multiple {N : ℕ} (M : Fin 1 → Fin N → ℤ) (hM : PrimSys M)
    (B : Fin N → ℤ) (hB : B ≠ 0)
    (hBM : (fun i => (B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ))) :
    ∃ k : ℤ, k ≠ 0 ∧ ∀ i, B i = k * M 0 i := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 1 → ℤ, ∀ i, B i = ∑ j, c j * M j i := by
    by_contra hc
    exact ratSpan_saturation M hM B hc hBM
  refine ⟨c 0, ?_, ?_⟩
  · intro h0
    apply hB
    funext i
    have h := hc i
    rw [Fin.sum_univ_one, h0] at h
    simpa using h
  · intro i
    have h := hc i
    rwa [Fin.sum_univ_one] at h

/-- **Non-vanishing of an integer combination.**  A non-trivial integral combination of
`ℚ`-linearly independent complex numbers is non-zero. -/
private lemma cmtrue_linIndep_sum_ne_zero {N : ℕ} (ℓ : Fin N → ℂ) (hℓ : LinearIndependent ℚ ℓ)
    (x : Fin N → ℤ) (hx : x ≠ 0) : ∑ i, (x i : ℂ) * ℓ i ≠ 0 := by
  intro h
  rw [Fintype.linearIndependent_iff] at hℓ
  have hsum : ∑ i : Fin N, ((x i : ℚ) • ℓ i) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [Rat.smul_def, Rat.cast_intCast]
  have hall := hℓ (fun i => (x i : ℚ)) hsum
  exact hx (funext fun i => by exact_mod_cast hall i)

/-- **Products of exponentials.**  For integer exponents, a product of powers of `exp (ℓ i)`
collapses into a single exponential whose argument is the corresponding integral combination. -/
private lemma cmtrue_prod_exp_zpow {N : ℕ} (ℓ : Fin N → ℂ) (c : ℤ) (x : Fin N → ℤ) :
    ∏ i, (Complex.exp (ℓ i)) ^ (c * x i) = Complex.exp ((c : ℂ) * ∑ i, (x i : ℂ) * ℓ i) := by
  have h1 : ∀ i, (Complex.exp (ℓ i)) ^ (c * x i) = Complex.exp (((c * x i : ℤ) : ℂ) * ℓ i) :=
    fun i => (Complex.exp_int_mul (ℓ i) (c * x i)).symm
  rw [Finset.prod_congr rfl (fun i _ => h1 i), ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by push_cast; ring)

/-- Norm computation: `‖n · 2πi‖ = 2π · |n|`. -/
private lemma cmtrue_norm_int_mul_two_pi (n : ℤ) :
    ‖(n : ℂ) * (2 * ↑Real.pi * Complex.I)‖ = 2 * Real.pi * |(n : ℝ)| := by
  rw [Complex.norm_mul, Complex.norm_intCast]
  have h2 : ‖(((2 : ℂ) * ↑Real.pi) * Complex.I)‖ = 2 * Real.pi := by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_two,
      Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  rw [h2]
  ring

/-- Collision-free case `ε = true` with `ρ = 1`: if `θ i = exp (ℓ i)` with `ℓ` `ℚ`-linearly
independent, `B` is a non-zero integral vector whose `ℚ`-span contains the single row of `M`,
`PrimSys M` holds (so the row is primitive and `B` is an integral multiple of it), and
`‖∑ Bᵢℓᵢ‖ < π/𝒮` with `S ≤ 𝒮`, then no two of `0,…,S` are congruent modulo `G' = G_a × ker 𝒵`,
so `cardMod true M θ S = S + 1`. -/
theorem cardMod_true_rank_one {N S : ℕ} (M : Fin 1 → Fin N → ℤ) (hM : PrimSys M)
    (B : Fin N → ℤ) (hB : B ≠ 0)
    (hBM : (fun i => (B i : ℚ)) ∈
      Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)))
    (ℓ : Fin N → ℂ) (hℓ : LinearIndependent ℚ ℓ) (𝒮 : ℝ) (hSpos : 0 < 𝒮)
    (hS : (S : ℝ) ≤ 𝒮) (hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮) :
    cardMod true M (fun i => Complex.exp (ℓ i)) S = S + 1 := by
  classical
  -- `B = k · (row 0)` with `k ≠ 0`, so `‖Λ'‖ ≤ ‖Λ‖` where `Λ' = ∑ M₀ᵢℓᵢ`.
  obtain ⟨k, hk0, hkB⟩ := cmtrue_prim_row_int_multiple M hM B hB hBM
  have hM0 : M 0 ≠ 0 := by
    intro h
    exact hB (by funext i; rw [hkB i, congrFun h i]; simp)
  -- `Λ' ≠ 0`: otherwise `∑ M₀ᵢℓᵢ = 0` is a non-trivial rational relation among the `ℓᵢ`.
  have hΛne : (∑ i, (M 0 i : ℂ) * ℓ i) ≠ 0 :=
    cmtrue_linIndep_sum_ne_zero ℓ hℓ (M 0) hM0
  have hsum : (∑ i, (B i : ℂ) * ℓ i) = (k : ℂ) * ∑ i, (M 0 i : ℂ) * ℓ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hkB i]
    push_cast
    ring
  have hkn : (1 : ℝ) ≤ ‖(k : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hk0
  have hΛbound : ‖∑ i, (M 0 i : ℂ) * ℓ i‖ < Real.pi / 𝒮 := by
    have h1 : ‖∑ i, (M 0 i : ℂ) * ℓ i‖ ≤ ‖∑ i, (B i : ℂ) * ℓ i‖ := by
      rw [hsum, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hkn
    linarith [hΛ]
  -- The classes of `0,…,S` are pairwise distinct.
  have hinj : Set.InjOn
      (fun s : ℕ => ((0 : ℂ), fun j : Fin 1 => ∏ i, (Complex.exp (ℓ i)) ^ ((s : ℤ) * M j i)))
      (Finset.range (S + 1)) := by
    intro s hs t ht hst
    by_contra hne
    have h2 : ∏ i, (Complex.exp (ℓ i)) ^ ((s : ℤ) * M 0 i)
        = ∏ i, (Complex.exp (ℓ i)) ^ ((t : ℤ) * M 0 i) := by
      have h := congrFun (congrArg Prod.snd hst) 0
      simpa using h
    rw [cmtrue_prod_exp_zpow ℓ (s : ℤ) (M 0), cmtrue_prod_exp_zpow ℓ (t : ℤ) (M 0)] at h2
    -- `exp (s Λ') = exp (t Λ')`, so `(s - t) Λ' ∈ 2πiℤ`.
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h2
    have hct : ((((s : ℤ) - (t : ℤ) : ℤ)) : ℂ) = ((s : ℤ) : ℂ) - ((t : ℤ) : ℂ) := by
      push_cast; ring
    have hcne : ((((s : ℤ) - (t : ℤ) : ℤ)) : ℂ) ≠ 0 := by
      intro h
      rw [hct, sub_eq_zero] at h
      have h3 : (s : ℤ) = (t : ℤ) := by exact_mod_cast h
      exact hne (Nat.cast_injective h3)
    have hkey : ((((s : ℤ) - (t : ℤ) : ℤ)) : ℂ) * (∑ i, (M 0 i : ℂ) * ℓ i) =
        (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      have h1 : (((s : ℤ) : ℂ) - ((t : ℤ) : ℂ)) * (∑ i, (M 0 i : ℂ) * ℓ i)
          = ((s : ℤ) : ℂ) * (∑ i, (M 0 i : ℂ) * ℓ i)
            - ((t : ℤ) : ℂ) * (∑ i, (M 0 i : ℂ) * ℓ i) := by ring
      rw [hct, h1, hn]
      ring
    by_cases hn0 : n = 0
    · -- the integral multiple vanishes, forcing `Λ' = 0`
      apply hΛne
      rw [hn0, Int.cast_zero, zero_mul] at hkey
      exact (mul_eq_zero.mp hkey).resolve_left hcne
    · -- otherwise `‖(s-t)Λ'‖ ≥ 2π > π ≥ ‖(s-t)Λ'‖`
      have hge : (2 * Real.pi) ≤
          ‖((((s : ℤ) - (t : ℤ) : ℤ)) : ℂ) * (∑ i, (M 0 i : ℂ) * ℓ i)‖ := by
        rw [hkey, cmtrue_norm_int_mul_two_pi n]
        have h1 : (1 : ℝ) ≤ |((n : ℝ))| := by exact_mod_cast Int.one_le_abs hn0
        nlinarith [Real.pi_pos]
      have hle : ‖((((s : ℤ) - (t : ℤ) : ℤ)) : ℂ) * (∑ i, (M 0 i : ℂ) * ℓ i)‖ ≤ Real.pi := by
        rw [norm_mul, Complex.norm_intCast]
        have hsle : (s : ℝ) ≤ (S : ℝ) := by
          have h := Finset.mem_range.mp hs
          exact_mod_cast Nat.lt_succ_iff.mp h
        have htle : (t : ℝ) ≤ (S : ℝ) := by
          have h := Finset.mem_range.mp ht
          exact_mod_cast Nat.lt_succ_iff.mp h
        have hcle : |((((s : ℤ) - (t : ℤ) : ℤ)) : ℝ)| ≤ (S : ℝ) := by
          have hcr : ((((s : ℤ) - (t : ℤ) : ℤ)) : ℝ) = (s : ℝ) - (t : ℝ) := by
            push_cast; ring
          rw [hcr, abs_sub_le_iff]
          have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
          have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
          exact ⟨by linarith, by linarith⟩
        calc |((((s : ℤ) - (t : ℤ) : ℤ)) : ℝ)| * ‖∑ i, (M 0 i : ℂ) * ℓ i‖
            ≤ (S : ℝ) * ‖∑ i, (M 0 i : ℂ) * ℓ i‖ :=
              mul_le_mul_of_nonneg_right hcle (norm_nonneg _)
          _ ≤ (S : ℝ) * (Real.pi / 𝒮) :=
              mul_le_mul_of_nonneg_left hΛbound.le (Nat.cast_nonneg S)
          _ ≤ Real.pi := by
              have h1 : (S : ℝ) / 𝒮 ≤ 1 := (div_le_one hSpos).mpr hS
              have h2 : (S : ℝ) * (Real.pi / 𝒮) = Real.pi * ((S : ℝ) / 𝒮) := by ring
              rw [h2]
              calc Real.pi * ((S : ℝ) / 𝒮) ≤ Real.pi * 1 :=
                    mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
                _ = Real.pi := by ring
      linarith [hge, hle, Real.pi_pos]
  rw [cardMod]
  simp only [ite_true]
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

end Work.BW
