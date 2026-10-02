import Submission.Work.Deep.Nibble.AsmMargins
import Submission.Work.Deep.Nibble.asmHelp

/-!
# The assembly data: partition, colour blocks and their degree estimates

`nibbleConclusion_of_assembly` (proved) runs the §7 assembly from

* the numeric bundle `AssemblyParams` at *explicit* constants,
* the absorption margins `InternalMargins`/`CrossingMargins` at those constants,
* a `K`-fold partition `P` of `𝓗'` and the colour blocks `I : Fin K → Finset (Fin D)`,
* and the per-part degree/seed/interaction estimates
  `hpartdeg`, `hseed`, `hint'`, `hKslide`.

This module produces all of them from the cone's margin bundle
`NibbleMarginsStrong` and the hypotheses of the Nibble Lemma about the seeds
`M c`, at the *pinned* constants

`κ = γ²/3200`, `γp = γ/4`, `δ = γ²/256000`, `βp = γ²/32000`, `K = ⌈3200/γ²⌉`,

so that the caller can feed the parameter-sensitive
`PseudorandomMatchingAtObj n r (γ²/32000) (γ²/3200) (γ/4)` (obtained from
`EmbedAtR r` and `SparseMatchingAbove N₁ (r+1) (γ²/16000) (γ/4)`) to the assembly.

Everything here is elementary arithmetic and finite-block bookkeeping; the
non-trivial inputs are the random-partition step `exists_edgePartition` and the
numeric bundle `assemblyParams_selected` (both proved).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

/-- **Block-size arithmetic for the per-part degree estimate.**  If a part degree
`p` approximates `d/K` to relative accuracy `δ`, `d` approximates `D` to relative
accuracy `β`, and the block size `m` is `D/K` up to `1` (as `D/K ≤ m+1` and
`D/K - 1 ≤ m`, with `m ≥ 1`), then `p` approximates `m` to relative accuracy
`βp`, provided `4(δ+β+K/D) ≤ βp` and `β ≤ 1`. -/
lemma blockdeg_arith {m p d D K δ β βp : ℝ} (hD0 : 0 < D) (hK0 : 0 < K)
    (hacc : |p - d / K| ≤ δ * (d / K)) (hd : |d - D| ≤ β * D)
    (hm1 : D / K - 1 ≤ m) (hm2 : m ≤ D / K + 1) (hm3 : 1 ≤ m)
    (hβp : 4 * (δ + β + K / D) ≤ βp) (hβ1 : β ≤ 1) (hδ0 : 0 ≤ δ) :
    |p - m| ≤ βp * m := by
  have hβ0 : 0 ≤ β := by
    have h : 0 ≤ D * β := by
      rw [mul_comm]
      exact le_trans (abs_nonneg (d - D)) hd
    exact nonneg_of_mul_nonneg_right h hD0
  have hDnn : 0 ≤ D := le_of_lt hD0
  have hKnn : 0 ≤ K := le_of_lt hK0
  have hdD : d ≤ (1 + β) * D := by
    have h := (abs_le.mp hd).2
    linarith
  have hT1 : |p - d / K| ≤ δ * (d / K) := hacc
  have hT2 : |d / K - D / K| ≤ β * D / K := by
    have h1 : d / K - D / K = (d - D) / K := by ring
    rw [h1, abs_div, abs_of_pos hK0]
    exact div_le_div_of_nonneg_right hd hKnn
  have hT3 : |D / K - m| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have htri0 : |p - m| ≤ |p - d / K| + |d / K - D / K| + |D / K - m| := by
    have h1 : |p - m| ≤ |p - d / K| + |d / K - m| := abs_sub_le _ _ _
    have h2 : |d / K - m| ≤ |d / K - D / K| + |D / K - m| := abs_sub_le _ _ _
    linarith
  have htri : |p - m| ≤ δ * (d / K) + β * D / K + 1 := by linarith
  have hm2m : m + 1 ≤ 2 * m := by linarith
  have hβ1p : 0 ≤ 1 + β := by linarith
  have hA2 : D / K ≤ m + 1 := by linarith
  have hA0 : d / K ≤ (1 + β) * (D / K) := by
    calc d / K = (1 / K) * d := by ring
      _ ≤ (1 / K) * ((1 + β) * D) :=
          mul_le_mul_of_nonneg_left hdD (by positivity)
      _ = (1 + β) * (D / K) := by ring
  have hA1 : δ * (d / K) ≤ δ * ((1 + β) * (D / K)) :=
    mul_le_mul_of_nonneg_left hA0 hδ0
  have hA3 : δ * ((1 + β) * (D / K)) = δ * (1 + β) * (D / K) := by ring
  have hδβ0 : 0 ≤ δ * (1 + β) := mul_nonneg hδ0 hβ1p
  have hA4 : δ * (1 + β) * (D / K) ≤ δ * (1 + β) * (m + 1) :=
    mul_le_mul_of_nonneg_left hA2 hδβ0
  have hA5 : δ * (1 + β) * (m + 1) ≤ 2 * m * δ * (1 + β) := by
    have h := mul_le_mul_of_nonneg_left hm2m hδβ0
    linarith
  have hA : δ * (d / K) ≤ 2 * m * δ * (1 + β) := by linarith
  have hB : β * D / K ≤ 2 * m * β := by
    have h1 : β * D / K = β * (D / K) := by ring
    have h2 : β * (D / K) ≤ β * (m + 1) := mul_le_mul_of_nonneg_left hA2 hβ0
    have h3 : β * (m + 1) ≤ β * (2 * m) := mul_le_mul_of_nonneg_left hm2m hβ0
    linarith
  have hKDpos : 0 ≤ K / D := by positivity
  have hC : (1 : ℝ) ≤ 2 * (K / D) * m := by
    have h1 : (K / D) * (D / K) = 1 := by field_simp
    have h2 : (K / D) * (D / K) ≤ (K / D) * (m + 1) :=
      mul_le_mul_of_nonneg_left hA2 hKDpos
    have h3 : (K / D) * (m + 1) ≤ (K / D) * (2 * m) :=
      mul_le_mul_of_nonneg_left hm2m hKDpos
    linarith
  have hcoef : 2 * δ * (1 + β) + 2 * β + 2 * (K / D) ≤ βp := by
    have h1 : 2 * δ * (1 + β) ≤ 4 * δ := by nlinarith
    linarith
  have hm0 : 0 ≤ m := by linarith
  calc |p - m| ≤ δ * (d / K) + β * D / K + 1 := htri
    _ ≤ 2 * m * δ * (1 + β) + 2 * m * β + 2 * (K / D) * m := by linarith
    _ = m * (2 * δ * (1 + β) + 2 * β + 2 * (K / D)) := by ring
    _ ≤ m * βp := mul_le_mul_of_nonneg_left hcoef hm0
    _ = βp * m := by ring

/-- **The block-size lower bound `√n + 1 ≤ D/K`.**  From the `n`-domination
`10^{400} (γ²)^{-8} ≤ n` (a consequence of `NibbleMarginsStrong.hnbig`), `γ ≤ 1`
and `n ≤ 2D`, the block size `D/⌈3200/γ²⌉` dominates `√n + 1` — the `+1` being
the integrality slack of the equipartition of `D` colours into `K` blocks. -/
lemma sqrt_add_one_le_DK {n : ℕ} {D γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hbig : 10 ^ 400 * ((γ ^ 2)⁻¹) ^ 8 ≤ (n : ℝ)) (hDlin : (n : ℝ) / 2 ≤ D) :
    (n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ D / ((Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) := by
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hγ2le : γ ^ 2 ≤ 1 := by nlinarith
  have hu1 : 1 ≤ (γ ^ 2)⁻¹ := by
    rw [one_le_inv₀ hγ2]
    exact hγ2le
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hD0 : 0 ≤ D := by linarith
  -- `12804 ^ 2 ≤ n * γ ^ 4`
  have hsq : (12804 : ℝ) ^ 2 ≤ (n : ℝ) * γ ^ 4 := by
    have h2 : 10 ^ 400 * ((γ ^ 2)⁻¹) ^ 8 * γ ^ 4 ≤ (n : ℝ) * γ ^ 4 :=
      mul_le_mul_of_nonneg_right hbig (by positivity)
    have hu2 : ((γ ^ 2)⁻¹) ^ 2 * (γ ^ 2) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hγ2), one_pow]
    have h3 : ((γ ^ 2)⁻¹) ^ 8 * γ ^ 4 = ((γ ^ 2)⁻¹) ^ 6 := by
      rw [show γ ^ 4 = (γ ^ 2) ^ 2 by ring,
        show ((γ ^ 2)⁻¹) ^ 8 = ((γ ^ 2)⁻¹) ^ 6 * ((γ ^ 2)⁻¹) ^ 2 by ring,
        mul_assoc, hu2, mul_one]
    have h2' : 10 ^ 400 * (((γ ^ 2)⁻¹) ^ 8 * γ ^ 4) ≤ (n : ℝ) * γ ^ 4 := by
      rw [← mul_assoc]; exact h2
    rw [h3] at h2'
    have h4 : (1 : ℝ) ≤ ((γ ^ 2)⁻¹) ^ 6 := one_le_pow₀ hu1
    have h5 : (12804 : ℝ) ^ 2 ≤ 10 ^ 400 := by
      have h6 : (12804 : ℝ) ^ 2 ≤ (10 : ℝ) ^ 9 := by norm_num
      have h7 : (10 : ℝ) ^ 9 ≤ (10 : ℝ) ^ 400 :=
        pow_le_pow_right₀ (by norm_num) (by norm_num)
      exact le_trans h6 h7
    have h4' : (10 : ℝ) ^ 400 ≤ 10 ^ 400 * ((γ ^ 2)⁻¹) ^ 6 := by
      have h4b := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (10:ℝ) ^ 400)
      simpa [mul_comm] using h4b
    exact le_trans (le_trans h5 h4') h2'
  have hsqrtrpow : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (n : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
  -- `12804 √n ≤ n γ²`
  have h1 : 12804 * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) * γ ^ 2 := by
    have hL : 0 ≤ 12804 * (n : ℝ) ^ ((1 : ℝ) / 2) := by positivity
    have hR : 0 ≤ (n : ℝ) * γ ^ 2 := by positivity
    refine (mul_self_le_mul_self_iff hL hR).mpr ?_
    have e1' : (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) = (n : ℝ) := by
      rw [← sq, hsqrtrpow]
    have e1 : (12804 * (n : ℝ) ^ ((1 : ℝ) / 2)) * (12804 * (n : ℝ) ^ ((1 : ℝ) / 2))
        = 12804 ^ 2 * (n : ℝ) := by
      rw [mul_mul_mul_comm, e1']
      ring
    have e2 : ((n : ℝ) * γ ^ 2) * ((n : ℝ) * γ ^ 2) = (n : ℝ) ^ 2 * γ ^ 4 := by ring
    rw [e1, e2]
    nlinarith [hsq, hnn]
  have h3 : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) * γ ^ 2 / 12804 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12804)]
    linarith
  have h4 : (1 : ℝ) ≤ (n : ℝ) * γ ^ 2 / 12804 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12804)]
    have h7 : (n : ℝ) * γ ^ 4 ≤ (n : ℝ) * γ ^ 2 := by
      have h8 : γ ^ 4 ≤ γ ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h8 hnn
    nlinarith [hsq, h7]
  have h6 : (n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ (n : ℝ) * γ ^ 2 / 6402 := by
    have h19 : (n : ℝ) * γ ^ 2 / 12804 + (n : ℝ) * γ ^ 2 / 12804
        = (n : ℝ) * γ ^ 2 / 6402 := by ring
    linarith
  have h20 : (n : ℝ) * γ ^ 2 / 6402 ≤ D * γ ^ 2 / 3201 := by
    have h10 : 3201 * (n : ℝ) ≤ 6402 * D := by linarith
    have h11 : 3201 * (n : ℝ) * γ ^ 2 ≤ 6402 * D * γ ^ 2 :=
      mul_le_mul_of_nonneg_right h10 (by positivity)
    nlinarith
  have h21 : D * γ ^ 2 / 3201 ≤ D / ((Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) := by
    have hKpos : (0 : ℝ) < (Nat.ceil (3200 / γ ^ 2) : ℕ) := by
      have h12 : 1 ≤ Nat.ceil (3200 / γ ^ 2) := Nat.one_le_ceil_iff.mpr (by positivity)
      exact_mod_cast h12
    have hKle : (Nat.ceil (3200 / γ ^ 2) : ℝ) ≤ (3200 + γ ^ 2) / γ ^ 2 := by
      have h13 : (Nat.ceil (3200 / γ ^ 2) : ℝ) ≤ 3200 / γ ^ 2 + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3200 / γ ^ 2 by positivity))
      have h13' : (3200 + γ ^ 2) / γ ^ 2 = 3200 / γ ^ 2 + 1 := by
        rw [add_div, div_self (ne_of_gt hγ2)]
      linarith
    have h14 : γ ^ 2 / (3200 + γ ^ 2) ≤ 1 / (Nat.ceil (3200 / γ ^ 2) : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      have h15 : γ ^ 2 * (Nat.ceil (3200 / γ ^ 2) : ℝ) ≤ γ ^ 2 * ((3200 + γ ^ 2) / γ ^ 2) :=
        mul_le_mul_of_nonneg_left hKle (by positivity)
      have h16 : γ ^ 2 * ((3200 + γ ^ 2) / γ ^ 2) = 3200 + γ ^ 2 := by
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hγ2)]
      linarith
    have h17 : γ ^ 2 / 3201 ≤ γ ^ 2 / (3200 + γ ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have h18 : γ ^ 2 / 3201 ≤ 1 / (Nat.ceil (3200 / γ ^ 2) : ℝ) := le_trans h17 h14
    calc D * γ ^ 2 / 3201 = D * (γ ^ 2 / 3201) := by ring
      _ ≤ D * (1 / (Nat.ceil (3200 / γ ^ 2) : ℝ)) := mul_le_mul_of_nonneg_left h18 hD0
      _ = D / ((Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) := by ring
  linarith [h6, h20, h21]

/-- **The assembly data at the pinned constants.**  From the cone's margin bundle
and the hypotheses of the Nibble Lemma about the seeds `M c`, this produces a
`⌈3200/γ²⌉`-fold partition of `𝓗'`, the colour blocks, the absorption margins at
`γp = γ/4`, `κ = γ²/3200`, and the per-part degree, seed-size and interaction
estimates that `nibbleConclusion_of_assembly` consumes. -/
theorem exists_assemblyAll {n D : ℕ} (𝓗' : MultiHypergraph n) {r : ℕ} {β γ ε ρ ξ : ℝ}
    (M : Fin D → Set (Set (Fin n)))
    (hm : NibbleMarginsStrong n (D : ℝ) r β γ ε ρ ξ)
    (hD8 : 4000 * ξ ≤ γ * ρ ^ 2)
    (hdeg : ∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ))
    (hMsz : ∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ))
    (hMint : ∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) :
    ∃ (P : EdgePartition 𝓗' (Nat.ceil (3200 / γ ^ 2)))
      (I : Fin (Nat.ceil (3200 / γ ^ 2)) → Finset (Fin D)),
      AssemblyParams n (D : ℝ) β γ ε ρ ξ (γ ^ 2 / 3200) (γ / 4) (γ ^ 2 / 256000) (γ ^ 2 / 32000)
        (Nat.ceil (3200 / γ ^ 2)) ∧
      InternalMargins n ρ ε (γ / 4) (γ ^ 2 / 3200) ξ ∧
      CrossingMargins n ρ ε (γ / 4) (γ ^ 2 / 3200) ξ ∧
      (∀ i, D / Nat.ceil (3200 / γ ^ 2) ≤ (I i).card ∧
        (I i).card ≤ D / Nat.ceil (3200 / γ ^ 2) + 1) ∧
      (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧
      (Finset.univ.biUnion I = Finset.univ) ∧
      ((n : ℝ) ^ ((1 : ℝ) / 2) + 1 ≤ (D : ℝ) / ((Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ)) ∧
      (∀ i w, |(((P.part i).deg w : ℝ)) - ((I i).card : ℝ)|
        ≤ (γ ^ 2 / 32000) * ((I i).card : ℝ)) ∧
      (∀ i c, c ∈ I i → ((famVert (M c)).ncard : ℝ) ≤ (γ ^ 2 / 32000) * ((I i).card : ℝ)) ∧
      (∀ i e, e ∈ (P.part i).edgeSet →
        (({c : Fin D | c ∈ I i ∧ (e ∩ famVert (M c)).Nonempty}).ncard : ℝ)
          ≤ (γ ^ 2 / 32000) * ((I i).card : ℝ)) := by
  classical
  have hγ0 : 0 < γ := hm.base.hγ0
  have hγ1 : γ ≤ 1 := by
    have h1 := hm.hγρ
    have h2 := hm.base.hρ1
    linarith
  have hρ0 : 0 < ρ := hm.base.hρ0
  have hε0 : 0 < ε := hm.base.hε0
  have hρ1 : ρ ≤ 1 := hm.base.hρ1
  have hε4 : 4000 * ε ≤ 1 := hm.hε
  have hξ0 : 0 < ξ := hm.base.hξ0
  have hn8 : 8 ≤ n := hm.base.hn
  have hnR : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
  have hDlin : (n : ℝ) / 2 ≤ (D : ℝ) := hm.hDlin
  have hDhigh : (D : ℝ) ≤ (n : ℝ) := hm.base.hDhigh
  have hD0 : (0 : ℝ) < (D : ℝ) := by linarith
  have hβhalf : β ≤ 1 / 2 := by
    have h1 := hm.hβ4
    have h2 : γ ^ 4 ≤ 1 := by
      have h3 : γ ^ 4 ≤ γ ^ 1 := pow_le_pow_of_le_one (le_of_lt hγ0) hγ1 (by norm_num)
      linarith
    linarith
  -- the numeric bundle at the pinned constants
  have hpar : AssemblyParams n (D : ℝ) β γ ε ρ ξ (γ ^ 2 / 3200) (γ / 4) (γ ^ 2 / 256000)
      (γ ^ 2 / 32000) (Nat.ceil (3200 / γ ^ 2)) := assemblyParams_selected hm hD0
  -- the random partition
  have hCher : 2 * ((n : ℝ) * (Nat.ceil (3200 / γ ^ 2) : ℕ)) *
      Real.exp (-(3 * (γ ^ 2 / 256000) ^ 2 * ((1 - β) * (D : ℝ)))
        / (8 * (Nat.ceil (3200 / γ ^ 2) : ℕ))) < 1 := by
    have h := hpar.hCher
    convert h using 2
    ring
  obtain ⟨P, hPacc⟩ := exists_edgePartition 𝓗' hpar.hK hpar.hδ0 hpar.hδ1 hβhalf hdeg hCher
  -- the colour blocks
  have hKpos : 0 < Nat.ceil (3200 / γ ^ 2) := Nat.lt_of_lt_of_le (by norm_num) hpar.hK
  have hKposR : (0 : ℝ) < (Nat.ceil (3200 / γ ^ 2) : ℕ) := by exact_mod_cast hKpos
  have hKD : Nat.ceil (3200 / γ ^ 2) ≤ D := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) / ((Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) :=
      hpar.hKlow
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by linarith) (by norm_num)
    have h4 : (Nat.ceil (3200 / γ ^ 2) : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (D : ℝ) := by
      rw [le_div_iff₀ hKposR] at h1
      simpa [mul_comm] using h1
    have h5 : (Nat.ceil (3200 / γ ^ 2) : ℝ) ≤ (D : ℝ) := by
      have h6 : (Nat.ceil (3200 / γ ^ 2) : ℝ) ≤
          (Nat.ceil (3200 / γ ^ 2) : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        nlinarith [h2, hKposR]
      linarith
    exact_mod_cast h5
  obtain ⟨I, hIcard, hIdisj, hIuniv, hIsum⟩ :=
    exists_colourBlocks D (Nat.ceil (3200 / γ ^ 2)) hKpos hKD
  -- the block-size floor, used three times
  have hfloor : ∀ i : Fin (Nat.ceil (3200 / γ ^ 2)),
      (D : ℝ) / (Nat.ceil (3200 / γ ^ 2) : ℝ) - 1 ≤ ((I i).card : ℝ) := by
    intro i
    have hlt : D < (D / Nat.ceil (3200 / γ ^ 2) + 1) * Nat.ceil (3200 / γ ^ 2) :=
      (Nat.div_lt_iff_lt_mul hKpos).mp (Nat.lt_succ_self _)
    have hcast : (D : ℝ) / ((Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ)
        < ((D / Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hKposR]
      have h2 : ((D : ℕ) : ℝ) < (((D / Nat.ceil (3200 / γ ^ 2) + 1)
          * Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast at h2
      linarith
    have h3 : ((D / Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) ≤ ((I i).card : ℝ) := by
      exact_mod_cast (hIcard i).1
    linarith
  have hceil : ∀ i : Fin (Nat.ceil (3200 / γ ^ 2)),
      ((I i).card : ℝ) ≤ (D : ℝ) / (Nat.ceil (3200 / γ ^ 2) : ℝ) + 1 := by
    intro i
    have h4 : ((I i).card : ℝ) ≤ ((D / Nat.ceil (3200 / γ ^ 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (hIcard i).2
    have h5 : ((D / Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) ≤
        (D : ℝ) / (Nat.ceil (3200 / γ ^ 2) : ℝ) := Nat.cast_div_le
    push_cast at h4
    linarith
  have hone : ∀ i : Fin (Nat.ceil (3200 / γ ^ 2)), (1 : ℝ) ≤ ((I i).card : ℝ) := by
    intro i
    have h6 : 1 ≤ D / Nat.ceil (3200 / γ ^ 2) :=
      (Nat.one_le_div_iff hKpos).mpr hKD
    have h7 : (1 : ℝ) ≤ ((D / Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) := by exact_mod_cast h6
    have h8 : ((D / Nat.ceil (3200 / γ ^ 2) : ℕ) : ℝ) ≤ ((I i).card : ℝ) := by
      exact_mod_cast (hIcard i).1
    linarith
  -- the `n`-domination, used for `hKslide`
  have hbig : 10 ^ 400 * ((γ ^ 2)⁻¹) ^ 8 ≤ (n : ℝ) := by
    have h1 := hm.hnbig
    have h2 : (γ⁻¹) ^ 16 ≤ (ρ⁻¹) ^ 6 + (γ⁻¹) ^ 16 + (γ * ρ * ε)⁻¹
        + ((γ * ρ * ε)⁻¹) ^ 2 + (r : ℝ) := by
      have h3 : 0 ≤ (ρ⁻¹) ^ 6 := by positivity
      have h4 : 0 ≤ (γ * ρ * ε)⁻¹ := by positivity
      have h5 : 0 ≤ ((γ * ρ * ε)⁻¹) ^ 2 := by positivity
      have h6 : 0 ≤ (r : ℝ) := by positivity
      linarith
    have h7 : 10 ^ 400 * (γ⁻¹) ^ 16 ≤ (n : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1
    have h8 : (γ⁻¹) ^ 16 = ((γ ^ 2)⁻¹) ^ 8 := by
      rw [inv_pow γ 16, inv_pow (γ ^ 2) 8]
      congr 1
      rw [show (γ ^ 2) ^ 8 = γ ^ (2 * 8) by rw [pow_mul]]
    rwa [h8] at h7
  refine ⟨P, I, hpar,
    internalMargins_of_assemblyParams hpar hρ1 hε4 hξ0,
    crossingMargins_of_assemblyParams hpar hρ1 hε4 hξ0 hD8,
    hIcard, hIdisj, hIuniv, sqrt_add_one_le_DK hγ0 hγ1 hbig hDlin, ?_, ?_, ?_⟩
  · -- `hpartdeg`
    intro i w
    have hmm : |(((P.part i).deg w : ℝ)) - (𝓗'.deg w : ℝ) / (Nat.ceil (3200 / γ ^ 2) : ℝ)|
        ≤ (γ ^ 2 / 256000) * ((𝓗'.deg w : ℝ) / (Nat.ceil (3200 / γ ^ 2) : ℝ)) :=
      hPacc i w
    exact blockdeg_arith (m := ((I i).card : ℝ)) (p := ((P.part i).deg w : ℝ))
      (d := (𝓗'.deg w : ℝ)) (D := (D : ℝ)) (K := (Nat.ceil (3200 / γ ^ 2) : ℝ))
      (δ := γ ^ 2 / 256000) (β := β) (βp := γ ^ 2 / 32000)
      hD0 hKposR hmm (hdeg w) (hfloor i) (hceil i) (hone i) hpar.hβp
      (by linarith [hβhalf]) (by positivity)
  · -- `hseed`
    intro i c hc
    have h1 : β * (D : ℝ) ≤ (γ ^ 2 / 32000) * ((I i).card : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (hfloor i) (le_of_lt hpar.hβp0)
      linarith [h, hpar.hβpfloor]
    linarith [hMsz c, h1]
  · -- `hint'`
    intro i e he
    have he' : e ∈ 𝓗'.edgeSet := EdgePartition.part_edgeSet_subset i he
    have hsub : ({c : Fin D | c ∈ I i ∧ (e ∩ famVert (M c)).Nonempty} : Set (Fin D)) ⊆
        ({c : Fin D | (e ∩ famVert (M c)).Nonempty} : Set (Fin D)) := by
      intro c hc
      exact hc.2
    have hle : (({c : Fin D | c ∈ I i ∧ (e ∩ famVert (M c)).Nonempty} : Set (Fin D)).ncard : ℝ)
        ≤ (({c : Fin D | (e ∩ famVert (M c)).Nonempty} : Set (Fin D)).ncard : ℝ) := by
      have h := Set.ncard_le_ncard hsub (Set.toFinite _)
      exact_mod_cast h
    have h1 : β * (D : ℝ) ≤ (γ ^ 2 / 32000) * ((I i).card : ℝ) := by
      have h := mul_le_mul_of_nonneg_left (hfloor i) (le_of_lt hpar.hβp0)
      linarith [h, hpar.hβpfloor]
    linarith [hMint e he', hle, h1]

end

end Work.Deep.Nibble
