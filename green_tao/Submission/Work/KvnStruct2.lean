import Submission.Work.KvnStruct
import Submission.Work.KvnTower2
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0
import Submission.Commons.Combinatorics.Transference.exists_bohr_sigma_atom_bound_deg_K0

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Green–Tao Proposition 8.1 (generalised Koopman–von Neumann structure theorem), unconditionally

`exists_kvn_structure` discharges the last hypothesis of the Furstenberg tower
(`Submission/Work/KvnTower2.lean`): for every `k ≥ 3`, every level-set resolution `ε > 0` and
every Gowers-uniformity threshold `gr > 0` with `9 (2C)^{2^{k-1}-1} ε ≤ gr/4`, and every uniform
bound `CmB` on the correlation moments, there are *uniform* smallness parameters
`η, η', εp₀` and a threshold `N₀` such that: for every prime `p ≥ N₀` and every data
`(ν, f, τ, εp)` (with `ν ≥ 0`, `0 ≤ f ≤ ν`, `τ ≥ 0`, moments of `τ` bounded by `CmB`, the
finset-form correlation condition, mean `1 + O(εp)`, the cube linear forms condition at scale
`k-1`, and `‖ν - 1‖_{U^{k-1}} ≤ 2 εp^{1/2^{k-1}}`), the tower terminates with an invariant state.
-/

open Finset
open scoped BigOperators
open Commons.Combinatorics.Transference
open FinSigma

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-- **Green–Tao Proposition 8.1, unconditional form.** -/
theorem exists_kvn_structure {k : ℕ} (hk : 3 ≤ k) {C : ℝ} (hC : 5 ≤ C)
    {ε : ℝ} (hε : 0 < ε) {gr : ℝ} (hgr : 0 < gr)
    (hεgr : 9 * (2 * C) ^ (2 ^ (k - 1) - 1) * ε ≤ gr / 4)
    (CmB : ℕ → ℝ) (ρtgt : ℝ) (hρtgt : 0 < ρtgt) :
    ∃ (η η' εp₀ : ℝ) (N₀ : ℕ), 0 < η ∧ η ≤ 1 / 4 ∧ 0 < η' ∧ 0 < εp₀ ∧ εp₀ ≤ 1 ∧
      ∀ (p : ℕ) [Fact p.Prime], N₀ ≤ p → k ≤ p →
      ∀ (ν f τ : ZMod p → ℝ) (εp : ℝ),
        (∀ x, 0 ≤ ν x) → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ ν x) → (∀ x, 0 ≤ τ x) →
        (∀ q : ℕ, 1 ≤ q →
          ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ CmB q) →
        (∀ (A : Finset (Fin (k - 1) → Bool)), 2 ≤ A.card → ∀ h : Fin (k - 1) → ZMod p,
          ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
              ∏ ω ∈ A, ν (y + ∑ i, (if ω i then h i else 0))
            ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
                τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) →
        |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ εp →
        (∀ A : Finset (Fin (k - 1) → Bool),
          A ⊆ Finset.univ.erase (0 : Fin (k - 1) → Bool) → A.Nonempty → ∀ b : ZMod p,
          |((Fintype.card (Fin (k - 1) → ZMod p) : ℝ))⁻¹ *
            (∑ h : Fin (k - 1) → ZMod p,
              ∏ ω ∈ A, ν (b + ∑ j : Fin (k - 1), (if ω j then (1 : ZMod p) else 0) * h j)) - 1|
            ≤ εp) →
        Unorm (k - 1) (fun x => ν x - 1) ≤ 2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) →
        0 ≤ εp → εp ≤ εp₀ →
        ∃ (ρs c : ℝ) (K₀ : ℕ), 0 < ρs ∧ 0 < c ∧
          ((K₀ : ℝ) + 1) * ρs ≤ ρtgt * (Fintype.card (ZMod p) : ℝ) ∧
          (∀ s : KvnSt p, KvnSt.Inv (k - 1) C ε 2 η ρs ν s → s.n < K₀ →
            ¬ KvnSt.term f (k - 1) C ε gr s → KvnSt.small (k - 1) C ε η 2 c ρs ν f s) ∧
          ∃ s : KvnSt p,
            KvnSt.Inv (k - 1) C ε 2 η ρs ν s ∧ s.n ≤ K₀ ∧ KvnSt.term f (k - 1) C ε gr s := by
  classical
  have hd : 1 ≤ k - 1 := by omega
  have hC1 : (1 : ℝ) ≤ C := by linarith
  set Msb : ℝ := (2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 with hMsb
  set Mrawb1 : ℝ := (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2) with hMrawb1
  set Abnd : ℕ := KvnAbndU k ε with hAbnd
  have hMsb0 : (0 : ℝ) ≤ Msb := by rw [hMsb]; positivity
  have hP2pos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (k - 1) - 1) := pow_pos (by norm_num) _
  have hQWpos : (0 : ℝ) < (2 * C) ^ (2 ^ (k - 1) - 1) := pow_pos (by linarith) _
  have hMrawb1pos : (0 : ℝ) < Mrawb1 := by rw [hMrawb1]; positivity
  have hAbnd1 : (1 : ℕ) ≤ Abnd := by
    rw [hAbnd, KvnAbndU]
    have hc0 : (0 : ℤ) ≤ ⌈(2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 / ε⌉ :=
      Int.ceil_nonneg (by positivity)
    rw [Int.le_toNat (by omega : (0 : ℤ) ≤ 2 *
      (⌈(2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 / ε⌉ + 2) + 1)]
    omega
  have hAbnd1R : (1 : ℝ) ≤ (Abnd : ℝ) := by exact_mod_cast hAbnd1
  have hAbndpos : (0 : ℝ) < (Abnd : ℝ) := by linarith
  set K₀ : ℕ := ⌈72 * Mrawb1 ^ 2 / gr ^ 2⌉.toNat + 1 with hK₀def
  have hK₀pos : (0 : ℕ) < K₀ := by rw [hK₀def]; omega
  have hK₀1 : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀pos
  have hK₀pos' : (0 : ℝ) < (K₀ : ℝ) := by linarith
  have hK₀big : (9 : ℝ) < (K₀ : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2) := by
    have hgr2 : (0 : ℝ) < gr ^ 2 := by positivity
    have h0 : (0 : ℝ) ≤ 72 * Mrawb1 ^ 2 / gr ^ 2 := by positivity
    have hceil : 72 * Mrawb1 ^ 2 / gr ^ 2 ≤ ((⌈72 * Mrawb1 ^ 2 / gr ^ 2⌉.toNat : ℕ) : ℝ) := by
      have h1 : 72 * Mrawb1 ^ 2 / gr ^ 2 ≤ (⌈72 * Mrawb1 ^ 2 / gr ^ 2⌉ : ℤ) := Int.le_ceil _
      have h2 : ((⌈72 * Mrawb1 ^ 2 / gr ^ 2⌉.toNat : ℕ) : ℝ)
          = ((⌈72 * Mrawb1 ^ 2 / gr ^ 2⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (Int.ceil_nonneg h0)
      linarith [h1, h2]
    have hK₀ge : 72 * Mrawb1 ^ 2 / gr ^ 2 + 1 ≤ (K₀ : ℝ) := by
      have : (K₀ : ℝ) = ((⌈72 * Mrawb1 ^ 2 / gr ^ 2⌉.toNat : ℕ) : ℝ) + 1 := by
        rw [hK₀def]; push_cast; ring
      rw [this]; linarith
    have hstep : (72 * Mrawb1 ^ 2 / gr ^ 2 + 1) * gr ^ 2 / (8 * Mrawb1 ^ 2)
        = 9 + gr ^ 2 / (8 * Mrawb1 ^ 2) := by
      field_simp; ring
    have hpos : (0 : ℝ) < gr ^ 2 / (8 * Mrawb1 ^ 2) := div_pos hgr2 (by positivity)
    calc (9 : ℝ) < 9 + gr ^ 2 / (8 * Mrawb1 ^ 2) := by linarith
      _ = (72 * Mrawb1 ^ 2 / gr ^ 2 + 1) * gr ^ 2 / (8 * Mrawb1 ^ 2) := hstep.symm
      _ ≤ (K₀ : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hK₀ge hgr2.le
  -- the smallness parameter `t`
  set Cst1 : ℝ := 32 * Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ with hCst1
  set Cst2 : ℝ := 264 * Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ with hCst2
  have hCst1pos : 0 < Cst1 := by rw [hCst1]; positivity
  have hCst2pos : 0 < Cst2 := by rw [hCst2]; positivity
  set Cst5 : ℝ := ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ with hCst5
  have hCst5pos : 0 < Cst5 := by rw [hCst5]; positivity
  set t : ℝ := min (1 / 4) (min (min (gr / (16 * max Cst1 1)) (gr ^ 2 / (32 * max Cst2 1)))
      (ρtgt / (32 * max Cst5 1))) with ht
  have htpos : 0 < t := by
    rw [ht]
    refine lt_min (by norm_num) (lt_min (lt_min (div_pos hgr (by positivity))
      (div_pos (by positivity) (by positivity))) ?_)
    exact div_pos hρtgt (by positivity)
  have htle : t ≤ 1 / 4 := by rw [ht]; exact min_le_left _ _
  have ht3 : 8 * Cst5 * t ≤ ρtgt / 4 := by
    have hle : t ≤ ρtgt / (32 * max Cst5 1) := by
      rw [ht]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : 8 * Cst5 * (ρtgt / (32 * max Cst5 1)) ≤ ρtgt / 4 := by
      rw [mul_div_assoc']
      have h3 : Cst5 / max Cst5 1 ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) (by positivity)
      calc 8 * Cst5 * ρtgt / (32 * max Cst5 1) = (Cst5 / max Cst5 1) * (ρtgt / 4) := by ring
        _ ≤ 1 * (ρtgt / 4) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = ρtgt / 4 := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) h2
  have ht1 : Cst1 * t ≤ gr / 16 := by
    have hle : t ≤ gr / (16 * max Cst1 1) := by
      rw [ht]; exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (min_le_left _ _)
    have h2 : Cst1 * (gr / (16 * max Cst1 1)) ≤ gr / 16 := by
      rw [mul_div_assoc']
      have h3 : Cst1 / max Cst1 1 ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) (by positivity)
      calc Cst1 * gr / (16 * max Cst1 1) = (Cst1 / max Cst1 1) * (gr / 16) := by ring
        _ ≤ 1 * (gr / 16) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = gr / 16 := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hle hCst1pos.le) h2
  have ht2 : Cst2 * t ≤ gr ^ 2 / 32 := by
    have hle : t ≤ gr ^ 2 / (32 * max Cst2 1) := by
      rw [ht]; exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (min_le_right _ _)
    have h2 : Cst2 * (gr ^ 2 / (32 * max Cst2 1)) ≤ gr ^ 2 / 32 := by
      rw [mul_div_assoc']
      have h3 : Cst2 / max Cst2 1 ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) (by positivity)
      calc Cst2 * gr ^ 2 / (32 * max Cst2 1) = (Cst2 / max Cst2 1) * (gr ^ 2 / 32) := by ring
        _ ≤ 1 * (gr ^ 2 / 32) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = gr ^ 2 / 32 := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hle hCst2pos.le) h2
  set η : ℝ := t / (27 * (K₀ : ℝ) ^ 2 + 1) with hηdef
  set η' : ℝ := t with hη'def
  have hdenη : (0 : ℝ) < 27 * (K₀ : ℝ) ^ 2 + 1 := by positivity
  have hηpos : 0 < η := by rw [hηdef]; exact div_pos htpos hdenη
  have hη1 : η ≤ 1 / 4 := by
    rw [hηdef]
    have h1 : t / (27 * (K₀ : ℝ) ^ 2 + 1) ≤ t := by
      rw [div_le_iff₀ hdenη]; nlinarith [htpos.le]
    linarith [htle]
  have hη'pos : 0 < η' := by rw [hη'def]; exact htpos
  have hT4 : 3 * η' + 27 * (K₀ : ℝ) ^ 2 * η ≤ 4 * t := by
    rw [hηdef, hη'def]
    have h1 : 27 * (K₀ : ℝ) ^ 2 * (t / (27 * (K₀ : ℝ) ^ 2 + 1)) ≤ t := by
      rw [mul_div_assoc', div_le_iff₀ hdenη]; nlinarith [htpos.le]
    linarith
  -- the Weierstrass data (chosen once, uniformly in the state)
  obtain ⟨E, D, hE0, hEspec⟩ :=
    Commons.Analysis.Approximation.exists_poly_weight_family_deg_K0 (K₀ := K₀) (M := Msb)
      (ε := ε) (C := Msb + ε) (η' := η') hMsb0 hε (by linarith) hη'pos
      (continuous_levelJoinPsi η).continuousOn
      (fun u _ => ⟨levelJoinPsi_nonneg η u, levelJoinPsi_le_one η u⟩) (levelJoinPsi_zero hηpos)
  set S : ℝ := ∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (CmB j) 0) with hSdef
  set E₀max : ℝ := E * (1 + (((2 ^ (k - 1) * 2 ^ (k - 1) : ℕ)) : ℝ) ^ D *
      ((6 : ℝ) ^ D * S)) with hE₀maxdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun j _ => by by_cases hj : j = 0 <;> simp [hj])
  have hE₀max0 : 0 ≤ E₀max := by
    rw [hE₀maxdef]
    refine mul_nonneg hE0 (add_nonneg zero_le_one ?_)
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (pow_nonneg (by norm_num) _) hS0)
  -- choose `εp₀`
  set Cst3 : ℝ := 16 * Mrawb1 * ((K₀ : ℝ) + 1) * E₀max * (Abnd : ℝ) ^ K₀ with hCst3
  set Cst4 : ℝ := 132 * Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * E₀max * (Abnd : ℝ) ^ K₀ with hCst4
  set Cst6 : ℝ := 16 * ((K₀ : ℝ) + 1) * E₀max * (Abnd : ℝ) ^ K₀ with hCst6
  set s : ℝ := min (min (gr / (16 * max Cst3 1)) (gr ^ 2 / (32 * max Cst4 1)))
      (ρtgt / max Cst6 1) with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    exact lt_min (lt_min (div_pos hgr (by positivity)) (div_pos (by positivity) (by positivity)))
      (div_pos hρtgt (by positivity))
  set εp₀ : ℝ := min 1 (s ^ (2 ^ (k - 1))) with hεp₀def
  have hεp₀0 : 0 < εp₀ := by
    rw [hεp₀def]; exact lt_min (by norm_num) (pow_pos hspos _)
  have hεp₀1 : εp₀ ≤ 1 := by rw [hεp₀def]; exact min_le_left _ _
  have hεp₀rpow : εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ s := by
    have h1 : εp₀ ≤ s ^ (2 ^ (k - 1)) := by rw [hεp₀def]; exact min_le_right _ _
    calc εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹)
        ≤ (s ^ (2 ^ (k - 1))) ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (le_of_lt hεp₀0) h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = s := by
          rw [← Real.rpow_natCast s (2 ^ (k - 1))]
          rw [← Real.rpow_mul hspos.le]
          rw [mul_inv_cancel₀ (by positivity : (((2 ^ (k - 1) : ℕ) : ℝ)) ≠ 0), Real.rpow_one]
  have hεC3 : Cst3 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ gr / 16 := by
    have hle : εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ gr / (16 * max Cst3 1) := by
      refine le_trans hεp₀rpow ?_
      rw [hsdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : Cst3 * (gr / (16 * max Cst3 1)) ≤ gr / 16 := by
      rw [mul_div_assoc']
      have h3 : Cst3 / max Cst3 1 ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) (by positivity)
      calc Cst3 * gr / (16 * max Cst3 1) = (Cst3 / max Cst3 1) * (gr / 16) := by ring
        _ ≤ 1 * (gr / 16) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = gr / 16 := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hle (by
      rw [hCst3]; positivity)) h2
  have hεC4 : Cst4 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ gr ^ 2 / 32 := by
    have hle : εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ gr ^ 2 / (32 * max Cst4 1) := by
      refine le_trans hεp₀rpow ?_
      rw [hsdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 : Cst4 * (gr ^ 2 / (32 * max Cst4 1)) ≤ gr ^ 2 / 32 := by
      rw [mul_div_assoc']
      have h3 : Cst4 / max Cst4 1 ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) (by positivity)
      calc Cst4 * gr ^ 2 / (32 * max Cst4 1) = (Cst4 / max Cst4 1) * (gr ^ 2 / 32) := by ring
        _ ≤ 1 * (gr ^ 2 / 32) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = gr ^ 2 / 32 := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hle (by
      rw [hCst4]; positivity)) h2
  have hεC6 : Cst6 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ ρtgt := by
    have hle : εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) ≤ ρtgt / max Cst6 1 := by
      refine le_trans hεp₀rpow ?_
      rw [hsdef]; exact min_le_right _ _
    have h2 : Cst6 * (ρtgt / max Cst6 1) ≤ ρtgt := by
      rw [mul_div_assoc']
      have h3 : Cst6 / max Cst6 1 ≤ 1 := div_le_one_of_le₀ (le_max_left _ _) (by positivity)
      calc Cst6 * ρtgt / max Cst6 1 = (Cst6 / max Cst6 1) * ρtgt := by ring
        _ ≤ 1 * ρtgt := mul_le_mul_of_nonneg_right h3 hρtgt.le
        _ = ρtgt := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hle (by rw [hCst6]; positivity)) h2
  -- choose `N₀`
  set NA : ℝ := 32 * Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ / gr with hNA
  set NB : ℝ := 528 * Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ / gr ^ 2 with hNB
  set NC : ℝ := 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ / ρtgt with hNC
  have hNA0 : (0 : ℝ) ≤ NA := by rw [hNA]; positivity
  have hNB0 : (0 : ℝ) ≤ NB := by rw [hNB]; positivity
  have hNC0 : (0 : ℝ) ≤ NC := by rw [hNC]; positivity
  refine ⟨η, η', εp₀, ⌈NA⌉.toNat + ⌈NB⌉.toNat + ⌈NC⌉.toNat + k + 1, hηpos, hη1, hη'pos,
    hεp₀0, hεp₀1, ?_⟩
  intro p _ hpN hpk ν f τ εp hν hf0 hfν hτ0 hmom hcorr hmean hLFC hUnorm hεp0 hεple
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by
    have h : 0 < Fintype.card (ZMod p) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast h
  have hNnn : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) := le_of_lt hNpos
  have hcardp : (Fintype.card (ZMod p) : ℝ) = (p : ℝ) := by rw [ZMod.card]
  have hpleNA : NA ≤ (Fintype.card (ZMod p) : ℝ) := by
    have h1 : ⌈NA⌉.toNat ≤ p := by
      have : ⌈NA⌉.toNat ≤ ⌈NA⌉.toNat + ⌈NB⌉.toNat + ⌈NC⌉.toNat + k + 1 := by omega
      exact le_trans this hpN
    have ha : ((⌈NA⌉.toNat : ℕ) : ℝ) = ((⌈NA⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.ceil_nonneg hNA0)
    have h2 : ((⌈NA⌉ : ℤ) : ℝ) ≤ (p : ℝ) := by
      rw [← ha]; exact_mod_cast h1
    have h3 : NA ≤ ((⌈NA⌉ : ℤ) : ℝ) := Int.le_ceil NA
    rw [hcardp]; linarith
  have hpNNB : NB ≤ (Fintype.card (ZMod p) : ℝ) := by
    have h1 : ⌈NB⌉.toNat ≤ p := by
      have : ⌈NB⌉.toNat ≤ ⌈NA⌉.toNat + ⌈NB⌉.toNat + ⌈NC⌉.toNat + k + 1 := by omega
      exact le_trans this hpN
    have ha : ((⌈NB⌉.toNat : ℕ) : ℝ) = ((⌈NB⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.ceil_nonneg hNB0)
    have h2 : ((⌈NB⌉ : ℤ) : ℝ) ≤ (p : ℝ) := by
      rw [← ha]; exact_mod_cast h1
    have h3 : NB ≤ ((⌈NB⌉ : ℤ) : ℝ) := Int.le_ceil NB
    rw [hcardp]; linarith
  have hpNNC : NC ≤ (Fintype.card (ZMod p) : ℝ) := by
    have h1 : ⌈NC⌉.toNat ≤ p := by
      have : ⌈NC⌉.toNat ≤ ⌈NA⌉.toNat + ⌈NB⌉.toNat + ⌈NC⌉.toNat + k + 1 := by omega
      exact le_trans this hpN
    have ha : ((⌈NC⌉.toNat : ℕ) : ℝ) = ((⌈NC⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.ceil_nonneg hNC0)
    have h2 : ((⌈NC⌉ : ℤ) : ℝ) ≤ (p : ℝ) := by
      rw [← ha]; exact_mod_cast h1
    have h3 : NC ≤ ((⌈NC⌉ : ℤ) : ℝ) := Int.le_ceil NC
    rw [hcardp]; linarith
  -- the state-dependent constants
  set B₀ : ℝ := 2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 3 * η'
    + 27 * (K₀ : ℝ) ^ 2 * η with hB₀
  set ρs : ℝ := (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀
    with hρs
  set c : ℝ := (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2) with hc
  have hB₀0 : 0 ≤ B₀ := by
    rw [hB₀]
    refine add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (le_of_lt hεp₀0) _)) hE₀max0) (by linarith)) (by positivity)
  have hB₀bound : B₀ ≤ 2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 4 * t := by
    rw [hB₀]; linarith [hT4]
  have hB₀bound2 : 2 * B₀ ≤ 4 * (εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max) + 8 * t := by
    nlinarith [hB₀bound]
  have hAbndK0pos : (0 : ℝ) < (Abnd : ℝ) ^ K₀ := pow_pos hAbndpos _
  have hρs0 : (0 : ℝ) < ρs := by
    rw [hρs]
    have h1 : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ :=
      mul_nonneg (mul_nonneg hNnn (by linarith)) hAbndK0pos.le
    linarith [h1, hAbndK0pos]
  have hc0 : (0 : ℝ) < c := by
    rw [hc]; exact div_pos (mul_pos hNpos (by positivity)) (by positivity)
  -- the numeric bounds needed for `kvn_small_of_ED`
  have hX1 : 8 * Mrawb1 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀ ≤ gr / 8 := by
    have h1 : Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ * (2 * (εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹)
        * E₀max)) = Cst3 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) / 8 := by
      rw [hCst3]; ring
    have h2 : Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ * (4 * t) = Cst1 * t / 8 := by
      rw [hCst1]; ring
    have h3 : 8 * Mrawb1 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀
        = 8 * (Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀) * B₀ := by ring
    rw [h3]
    have h4 : 8 * (Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀)
        * B₀ ≤ 8 * (Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀)
          * (2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 4 * t) :=
      mul_le_mul_of_nonneg_left hB₀bound (by positivity)
    have h5 : 8 * (Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀)
        * (2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 4 * t)
        = 8 * (Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀
            * (2 * (εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max)))
          + 8 * (Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ * (4 * t)) := by ring
    rw [h5, h1, h2] at h4
    linarith [h4, hεC3, ht1]
  have hX2 : 4 * Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ ≤ (Fintype.card (ZMod p) : ℝ) * gr / 8 := by
    have h1 : 32 * Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ ≤ (Fintype.card (ZMod p) : ℝ) * gr := by
      have := hpleNA
      rw [hNA, div_le_iff₀ hgr] at this
      linarith [this]
    linarith [h1]
  have hX3 : 66 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀ * Mrawb1 ^ 2 ≤ gr ^ 2 / 16 := by
    have h1 : Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ * (2 * (εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹)
        * E₀max)) = Cst4 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) / 66 := by
      rw [hCst4]; ring
    have h2 : Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ * (4 * t) = Cst2 * t / 66 := by
      rw [hCst2]; ring
    have h3 : 66 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀ * Mrawb1 ^ 2
        = 66 * (Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀) * B₀ := by ring
    rw [h3]
    have h4 : 66 * (Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀) * B₀
        ≤ 66 * (Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀)
          * (2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 4 * t) :=
      mul_le_mul_of_nonneg_left hB₀bound (by positivity)
    have h5 : 66 * (Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀)
        * (2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 4 * t)
        = 66 * (Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀
            * (2 * (εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max)))
          + 66 * (Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ * (4 * t)) := by ring
    rw [h5, h1, h2] at h4
    linarith [h4, hεC4, ht2]
  have hX4 : 33 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀
      ≤ (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (16 * Mrawb1 ^ 2) := by
    have h1 : 528 * Mrawb1 ^ 2 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀
        ≤ (Fintype.card (ZMod p) : ℝ) * gr ^ 2 := by
      have := hpNNB
      rw [hNB, div_le_iff₀ (by positivity : (0:ℝ) < gr ^ 2)] at this
      linarith [this]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 16 * Mrawb1 ^ 2)]
    nlinarith [h1]
  -- `ρs` bounds via `B₀`
  have hρs_le : ρs ≤ (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀
      + (Abnd : ℝ) ^ K₀ := le_rfl
  -- the four conditions
  have hεCp : 9 * (2 * C) ^ (2 ^ (k - 1) - 1) * ε ≤ gr / 4 := hεgr
  have hρsCp : (Fintype.card (ZMod p) : ℝ) *
        (2 * (2 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 3 * η'
          + 27 * (K₀ : ℝ) ^ 2 * η))
        * (KvnAbndU k ε : ℝ) ^ K₀ + (KvnAbndU k ε : ℝ) ^ K₀ ≤ ρs := by
    rw [hρs, hB₀, hAbnd]
  have hγCp : (2 * C) ^ (2 ^ (k - 1) - 1) * (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) *
        (4 * ((K₀ : ℝ) + 1)) * ρs ≤ (Fintype.card (ZMod p) : ℝ) * gr / 4 := by
    have hMrawA : (2 * C) ^ (2 ^ (k - 1) - 1) * (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀)
        ≤ Mrawb1 := by
      have h1 : (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 : (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀))
          ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      calc (2 * C) ^ (2 ^ (k - 1) - 1) * (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀)
          = (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀)) := by ring
        _ ≤ _ := h2
        _ = Mrawb1 := by rw [hMrawb1]
    have hρsval : ρs = (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀
        + (Abnd : ℝ) ^ K₀ := by rw [hρs]
    have hstep : (2 * C) ^ (2 ^ (k - 1) - 1) * (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) *
          (4 * ((K₀ : ℝ) + 1)) * ρs
        ≤ Mrawb1 * (4 * ((K₀ : ℝ) + 1))
          * ((Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀) := by
      rw [hρsval]
      have hnn : (0 : ℝ) ≤ 4 * ((K₀ : ℝ) + 1) * ((Fintype.card (ZMod p) : ℝ) * (2 * B₀)
          * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀) := by
        have h1 : (0:ℝ) ≤ (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ :=
          mul_nonneg (mul_nonneg hNnn (by linarith [hB₀0])) (le_of_lt hAbndK0pos)
        exact mul_nonneg (by positivity) (add_nonneg h1 (le_of_lt hAbndK0pos))
      calc (2 * C) ^ (2 ^ (k - 1) - 1) * (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀)
            * (4 * ((K₀ : ℝ) + 1)) * ρs
          = ((2 * C) ^ (2 ^ (k - 1) - 1) * (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀))
            * (4 * ((K₀ : ℝ) + 1) * ρs) := by ring
        _ ≤ Mrawb1 * (4 * ((K₀ : ℝ) + 1) * ρs) :=
            mul_le_mul_of_nonneg_right hMrawA (by positivity)
        _ = Mrawb1 * (4 * ((K₀ : ℝ) + 1))
            * ((Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀) := by
            rw [hρsval]; ring
    have hsplit : Mrawb1 * (4 * ((K₀ : ℝ) + 1))
          * ((Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀)
        = (Fintype.card (ZMod p) : ℝ) * (8 * Mrawb1 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀)
          + 4 * Mrawb1 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ := by ring
    rw [hsplit] at hstep
    have h7 : (Fintype.card (ZMod p) : ℝ) * (8 * Mrawb1 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀)
        ≤ (Fintype.card (ZMod p) : ℝ) * (gr / 8) :=
      mul_le_mul_of_nonneg_left hX1 hNnn
    linarith [hstep, h7, hX2]
  have hsCp : (3 * 3 ^ 2 + 2 * 3) * ((K₀ : ℝ) + 1) * ρs + c ≤
      ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2 /
        ((Fintype.card (ZMod p) : ℝ)
          * ((2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ^ 2) := by
    have hMraw_eq : (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))
        ≤ Mrawb1 := by
      rw [hMrawb1]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        (by positivity)
    have hM2 : ((2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ^ 2
        ≤ Mrawb1 ^ 2 := by
      have h0 : (0 : ℝ) ≤ (2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp)) :=
        mul_nonneg (le_of_lt hQWpos) (by positivity)
      exact pow_le_pow_left₀ h0 hMraw_eq 2
    have hden : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ)
        * ((2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ^ 2 :=
      mul_pos hNpos (pow_pos (mul_pos hQWpos (by positivity)) _)
    have hdenle : (Fintype.card (ZMod p) : ℝ)
          * ((2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ^ 2
        ≤ (Fintype.card (ZMod p) : ℝ) * Mrawb1 ^ 2 :=
      mul_le_mul_of_nonneg_left hM2 hNnn
    have hfrac : ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2
          / ((Fintype.card (ZMod p) : ℝ) * Mrawb1 ^ 2)
        ≤ ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2
          / ((Fintype.card (ZMod p) : ℝ)
            * ((2 * C) ^ (2 ^ (k - 1) - 1) * ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp))) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) hden hdenle
    have hmain : (3 * 3 ^ 2 + 2 * 3) * ((K₀ : ℝ) + 1) * ρs + c
        ≤ ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2
          / ((Fintype.card (ZMod p) : ℝ) * Mrawb1 ^ 2) := by
      have hρsval : ρs = (Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀
          + (Abnd : ℝ) ^ K₀ := by rw [hρs]
      rw [hρsval, hc]
      have hsplit : (3 * 3 ^ 2 + 2 * 3) * ((K₀ : ℝ) + 1)
            * ((Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀)
          = (Fintype.card (ZMod p) : ℝ) * (66 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀)
            + 33 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀ := by ring
      rw [hsplit]
      have htarget : ((Fintype.card (ZMod p) : ℝ) * gr / 2) ^ 2
            / ((Fintype.card (ZMod p) : ℝ) * Mrawb1 ^ 2)
          = (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (4 * Mrawb1 ^ 2) := by
        field_simp; ring
      rw [htarget]
      have hA : (Fintype.card (ZMod p) : ℝ) * (66 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀)
          ≤ (Fintype.card (ZMod p) : ℝ) * (gr ^ 2 / (16 * Mrawb1 ^ 2)) := by
        have h2 : 66 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀ ≤ gr ^ 2 / (16 * Mrawb1 ^ 2) := by
          have h3 : 66 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀
              = (66 * ((K₀ : ℝ) + 1) * B₀ * (Abnd : ℝ) ^ K₀ * Mrawb1 ^ 2) / Mrawb1 ^ 2 := by
            field_simp
          rw [h3, show gr ^ 2 / (16 * Mrawb1 ^ 2) = (gr ^ 2 / 16) / Mrawb1 ^ 2 from by
            field_simp]
          exact div_le_div_of_nonneg_right hX3 (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hNnn
      have hsum : (Fintype.card (ZMod p) : ℝ) * (gr ^ 2 / (16 * Mrawb1 ^ 2))
            + 33 * ((K₀ : ℝ) + 1) * (Abnd : ℝ) ^ K₀
            + (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2)
          ≤ (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (4 * Mrawb1 ^ 2) := by
        have heq : (Fintype.card (ZMod p) : ℝ) * (gr ^ 2 / (16 * Mrawb1 ^ 2))
              + (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (16 * Mrawb1 ^ 2)
              + (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2)
            = (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (4 * Mrawb1 ^ 2) := by
          rw [show (Fintype.card (ZMod p) : ℝ) * (gr ^ 2 / (16 * Mrawb1 ^ 2))
              = (Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (16 * Mrawb1 ^ 2) from by ring]
          field_simp; ring
        linarith [hX4, heq]
      linarith [hA, hsum]
    linarith [hmain, hfrac]
  -- the `hpoly` hypothesis
  have hA_le_Msb : (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) ≤ Msb := by
    rw [hMsb]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpoly : ∀ (K' : ℕ) (hK' : K' ≤ K₀) (c' : Fin K' → ℝ),
      (∀ j, |c' j| ≤ (2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀) + ε) →
      ∃ P : MvPolynomial (Fin K') ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K' => Set.Icc (-((2 : ℝ) ^ (2 ^ (k - 1) - 1)
            * (1 + εp₀))) ((2 : ℝ) ^ (2 ^ (k - 1) - 1) * (1 + εp₀))),
          |∏ j, levelJoinPsi η ((t j - c' j) / ε) - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E ∧
        P.totalDegree ≤ D := by
    intro K' hK' c' hc'
    obtain ⟨P, hP1, hP2, hP3⟩ := hEspec K' hK' c' (fun j => by
      have := hc' j
      linarith [hA_le_Msb])
    exact ⟨P, fun t ht => hP1 t (by
      intro i _
      have := ht i (Set.mem_univ i)
      exact ⟨by linarith [(Set.mem_Icc.mp this).1, hA_le_Msb],
        by linarith [(Set.mem_Icc.mp this).2, hA_le_Msb]⟩), hP2, hP3⟩
  have hE₀le : E * (1 + (((2 ^ (k - 1) * 2 ^ (k - 1) : ℕ)) : ℝ) ^ D *
        ((6 : ℝ) ^ D * (∑ j ∈ Finset.range (D + 1), (if j = 0 then 1 else max (CmB j) 0))))
      ≤ E₀max := by
    rw [hE₀maxdef, hSdef]
  refine ⟨ρs, c, K₀, hρs0, hc0, ?_, ?_, ?_⟩
  · have hρs_goal : ((K₀ : ℝ) + 1) * ρs ≤ ρtgt * (Fintype.card (ZMod p) : ℝ) := by
      rw [hρs]
      have hsplit : ((K₀ : ℝ) + 1)
            * ((Fintype.card (ZMod p) : ℝ) * (2 * B₀) * (Abnd : ℝ) ^ K₀ + (Abnd : ℝ) ^ K₀)
          = (Fintype.card (ZMod p) : ℝ) * (((K₀ : ℝ) + 1) * (2 * B₀) * (Abnd : ℝ) ^ K₀)
            + Cst5 := by
        rw [hCst5]; ring
      rw [hsplit]
      have h1 : ((K₀ : ℝ) + 1) * (2 * B₀) * (Abnd : ℝ) ^ K₀ ≤ ρtgt / 2 := by
        have hb : (2 * B₀) * (Abnd : ℝ) ^ K₀
            ≤ (4 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 8 * t) * (Abnd : ℝ) ^ K₀ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [hB₀bound]
        have hstep : ((K₀ : ℝ) + 1) * (2 * B₀) * (Abnd : ℝ) ^ K₀
            ≤ ((K₀ : ℝ) + 1)
              * ((4 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 8 * t) * (Abnd : ℝ) ^ K₀) := by
          rw [show ((K₀ : ℝ) + 1) * (2 * B₀) * (Abnd : ℝ) ^ K₀
              = ((K₀ : ℝ) + 1) * ((2 * B₀) * (Abnd : ℝ) ^ K₀) from by ring]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
        have hterm : 4 * ((K₀ : ℝ) + 1) * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max
              * (Abnd : ℝ) ^ K₀ = Cst6 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) / 4 := by
          rw [hCst6]; ring
        have hterm2 : 8 * ((K₀ : ℝ) + 1) * t * (Abnd : ℝ) ^ K₀ = 8 * Cst5 * t := by
          rw [hCst5]; ring
        have hexp : ((K₀ : ℝ) + 1) * ((4 * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max + 8 * t)
              * (Abnd : ℝ) ^ K₀)
            = 4 * ((K₀ : ℝ) + 1) * εp₀ ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) * E₀max * (Abnd : ℝ) ^ K₀
              + 8 * ((K₀ : ℝ) + 1) * t * (Abnd : ℝ) ^ K₀ := by ring
        rw [hexp, hterm, hterm2] at hstep
        linarith [hstep, hεC6, ht3]
      have h2 : Cst5 ≤ (Fintype.card (ZMod p) : ℝ) * (ρtgt / 2) := by
        have hNCle : NC ≤ (Fintype.card (ZMod p) : ℝ) := hpNNC
        rw [hNC, div_le_iff₀ hρtgt] at hNCle
        linarith [hNCle]
      have hX : (Fintype.card (ZMod p) : ℝ) * (((K₀ : ℝ) + 1) * (2 * B₀) * (Abnd : ℝ) ^ K₀)
          ≤ (Fintype.card (ZMod p) : ℝ) * (ρtgt / 2) :=
        mul_le_mul_of_nonneg_left h1 hNnn
      linarith [hX, h2]
    exact hρs_goal
  · intro s hInv hsK hnt
    exact kvn_small_of_ED (p := p) (k := k) (C := C) (ε := ε) (η := η) (ν := ν) (f := f)
      (εp := εp) (εp₀ := εp₀) (τ := τ) (Cm := CmB) (η' := η') (ρs := ρs) (c := c) (gr := gr)
      (K₀ := K₀) (E := E) (D := D) (E₀max := E₀max)
      hk hC hε hηpos hη1 hν hf0 hfν hεp0 hεple hεp₀1 hτ0 hmom hcorr hmean hLFC hη'pos hgr hE0
      hpoly hUnorm hE₀max0 hE₀le hεCp hρsCp hγCp hsCp s hInv hsK hnt
  · have henergy : ∀ s : KvnSt p, KvnSt.Inv (k - 1) C ε 2 η ρs ν s →
        KvnSt.energy f (k - 1) C ε s ≤ 9 * (Fintype.card (ZMod p) : ℝ) := by
      intro s hInv
      have hbound : ∀ x ∈ Finset.univ \ s.Ω, (cE (KvnSt.B (k - 1) C ε s) f x) ^ 2 ≤ 9 := by
        intro x hx
        have hxΩ : x ∉ s.Ω := (Finset.mem_sdiff.mp hx).2
        have h := cE_abs_le_one_add_tau (d := k - 1) (τ := 2) (by norm_num) s hInv hf0 hfν x hxΩ
        have h2 : |cE (KvnSt.B (k - 1) C ε s) f x| ≤ 3 := by linarith
        calc (cE (KvnSt.B (k - 1) C ε s) f x) ^ 2
            = |cE (KvnSt.B (k - 1) C ε s) f x| ^ 2 := (sq_abs _).symm
          _ ≤ 3 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
          _ = 9 := by norm_num
      calc KvnSt.energy f (k - 1) C ε s
          = ∑ x ∈ Finset.univ \ s.Ω, (cE (KvnSt.B (k - 1) C ε s) f x) ^ 2 := rfl
        _ ≤ ∑ _x ∈ Finset.univ \ s.Ω, (9 : ℝ) := Finset.sum_le_sum hbound
        _ = 9 * ((Finset.univ \ s.Ω).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 9 * (Fintype.card (ZMod p) : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
    have hmean2 : |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ 2 := by
      have h1 : εp ≤ 1 := le_trans hεple hεp₀1
      linarith [hmean]
    exact kvn_decomp (d := k - 1) hd C ε η 2 c gr (9 * (Fintype.card (ZMod p) : ℝ)) hε ν f
      hν hf0 hfν (KvnSt.triv p) (KvnSt.inv_triv (k := k) hε (le_of_lt hρs0) hmean2) rfl hc0
      (by
        rw [hc]
        have h1 := mul_lt_mul_of_pos_right hK₀big hNpos
        have h2 : (9:ℝ) * (Fintype.card (ZMod p) : ℝ)
            < ((K₀ : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2)) * (Fintype.card (ZMod p) : ℝ) := by
          linarith [h1]
        calc (9:ℝ) * (Fintype.card (ZMod p) : ℝ)
            < ((K₀ : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2)) * (Fintype.card (ZMod p) : ℝ) := h2
          _ = (K₀ : ℝ) * ((Fintype.card (ZMod p) : ℝ) * gr ^ 2 / (8 * Mrawb1 ^ 2)) := by ring)
      henergy
      (fun s hInv hsK hnt =>
        kvn_small_of_ED (p := p) (k := k) (C := C) (ε := ε) (η := η) (ν := ν) (f := f)
          (εp := εp) (εp₀ := εp₀) (τ := τ) (Cm := CmB) (η' := η') (ρs := ρs) (c := c) (gr := gr)
          (K₀ := K₀) (E := E) (D := D) (E₀max := E₀max)
          hk hC hε hηpos hη1 hν hf0 hfν hεp0 hεple hεp₀1 hτ0 hmom hcorr hmean hLFC hη'pos hgr
          hE0 hpoly hUnorm hE₀max0 hE₀le hεCp hρsCp hγCp hsCp s hInv hsK hnt)

end GTTrans
