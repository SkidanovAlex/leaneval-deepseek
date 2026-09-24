import Submission.Work.NumberTheory.Chen.BTermCount.Basic
import Submission.Work.NumberTheory.Chen.BTermCount.SieveInterface

open Finset Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The sharp reduction of the `B`-term count to the sieve

Every prime counted by `Submission.bTermCount x M Y` satisfies `p + 2 = q q₂ q₃ ≥ M Y²`, hence
`p ≥ Y` as soon as `M ≥ 1` and `Y ≥ 2`.  Consequently *all* counted primes give sieve survivors,
with no exceptional small primes:

`bTermCount x M Y ≤ survivorCount x M Y`  for `1 ≤ M`, `2 ≤ Y`.

Combining this with `BTermSieveInput C` (`survivorCount ≤ C x/(log x)^2` eventually) yields
`bTermCount ≤ C x/(log x)^2` eventually, so the requested constant `3` follows from the sieve
input with `C = 3`.  Heuristically the survivor count is `≈ 2.4 x/(log x)^2` (the primes-only
part is `≈ 1.9 x/(log x)^2` and the composite survivors `≈ 0.5 x/(log x)^2`), while the classical
linear sieve bounds it by `3.52 x/(log x)^2`; see `notes/BTERM_COUNT_ANALYSIS.md`.
-/

/-- **Sharp reduction.**  For `1 ≤ M` and `2 ≤ Y`, every `B`-term prime is a sieve survivor, so
`bTermCount x M Y ≤ survivorCount x M Y`. -/
theorem bTermCount_le_survivorCount (x M Y : ℕ) (hM : 1 ≤ M) (hY : 2 ≤ Y) :
    Submission.bTermCount x M Y ≤ survivorCount x M Y := by
  rw [bTermCount_eq_card_bTermSet x M Y, survivorCount_eq_card]
  refine Finset.card_le_card_of_injOn (fun p => p + 2) ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe] at hp ⊢
    rw [mem_survivorSet]
    refine ⟨bTermSet_prod_mem hp, ?_⟩
    obtain ⟨hs0, q, q₂, q₃, hq, hq₂, hq₃, hMq, hqY, hYq₂, hq₂q₃, heq⟩ := mem_bTermSet.mp hp
    have hMY : M * (Y * Y) ≤ q * q₂ * q₃ := by
      calc M * (Y * Y) ≤ q * (q₂ * q₃) :=
            Nat.mul_le_mul hMq (Nat.mul_le_mul hYq₂ (le_trans hYq₂ hq₂q₃))
        _ = q * q₂ * q₃ := by ring
    have hY2le : Y * Y ≤ p + 2 := by
      calc Y * Y = 1 * (Y * Y) := (one_mul _).symm
        _ ≤ M * (Y * Y) := Nat.mul_le_mul_right _ hM
        _ ≤ q * q₂ * q₃ := hMY
        _ = p + 2 := heq.symm
    have hpge : Y ≤ p := by nlinarith [hY2le, hY]
    have hp' : p.Prime := (mem_s0Set'.mp (mem_bTermSet.mp hp).1).2.1
    intro r hr hdvd
    obtain ⟨hr', hr3, hrY⟩ := mem_oddLt'.mp hr
    have hsub : (p + 2) - 2 = p := by omega
    rw [hsub] at hdvd
    have hpr : p = r := (hp'.dvd_iff_eq hr'.ne_one).mp hdvd
    omega
  · intro p _ p' _ h
    simp only at h
    omega

/-- **The requested `B`-term bound from the sieve input.**  If the survivors of the ternary
sequence number at most `C x/(log x)^2` eventually, with `C ≤ 3`, then the `B`-term count is at
most `3 x/(log x)^2` eventually.

The classical linear sieve proves this input with `C = 3.52` (see
`notes/BTERM_COUNT_ANALYSIS.md`), which is `1.17` times too large.  The input with `C = 3` is
delicate: the count of survivors is `≈ 1.5 - 1.7` times the count of the primes `p` themselves
(numerically `1.53` at `x = 10^6`, `1.60` at `x = 10^7`), and the prime count is `≈ 1.9 x/log²x`,
so the survivor count is expected to be right around `3x/log²x`.  Proving the input therefore
needs a sieve refinement beyond the classical linear sieve, say a two-dimensional treatment of
the pair `(q₃, q q₂ q₃ - 2)`, i.e. the parity-breaking step which is the heart of Chen's
argument. -/
theorem chen_bterm_count_upper_of_sieveInput_three (C : ℝ) (hC : C ≤ 3)
    (h : BTermSieveInput C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Submission.bTermCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
        ≤ 3 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 h
  filter_upwards [eventually_ge_atTop (max x₀ 2), eventually_ge_atTop 5] with x hx hx5
  have hx₀' : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0:ℝ) < (x:ℝ) := by positivity
  have hM1 : 1 ≤ Submission.chenSiftLimit x := by
    rw [Submission.chenSiftLimit]
    have : (0:ℕ) ≤ ⌊cut (Real.rpow (x:ℝ) ((1:ℝ)/8)) 1⌋₊ := Nat.zero_le _
    omega
  have hY2 : 2 ≤ Submission.chenWindowTop x := by
    rw [Submission.chenWindowTop]
    have h : (0:ℕ) ≤ ⌊Real.rpow (x:ℝ) ((1:ℝ)/3)⌋₊ := Nat.zero_le _
    omega
  have hred : (Submission.bTermCount x (Submission.chenSiftLimit x)
      (Submission.chenWindowTop x) : ℝ)
      ≤ (survivorCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ) := by
    exact_mod_cast bTermCount_le_survivorCount x _ _ hM1 hY2
  have hsurv := hx₀ x hx₀'
  have hCx : C * (x:ℝ) / (Real.log (x:ℝ))^2 ≤ 3 * (x:ℝ) / (Real.log (x:ℝ))^2 := by
    have h1 : C * (x:ℝ) ≤ 3 * (x:ℝ) := by nlinarith
    exact div_le_div_of_nonneg_right h1 (by positivity)
  linarith

end Work.NumberTheory.Chen.BTermCount
