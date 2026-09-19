import Mathlib
import Submission.S2Expansion
import Submission.SieveExpansion
import Submission.Commons.NumberTheory.CongruenceWindows.filter_shift_system_class
import Submission.LamDivSum

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 1000000

/-!
# The `S₂` reduction: good/bad split and CRT collapse of the θ-weighted sum

Polymath8a §4.2 (Theorem 3.5(i)).  The prime (θ-weighted) window sum expands
(step 1, `Submission.S2Expansion`) into a sum over divisor tuples of the
coefficient `∏ᵢ αᵢ(dᵢ)βᵢ(eᵢ)` times the θ-weighted `S`-set sum `S̃` with moduli
`[dᵢ,eᵢ]`.  Here we finish steps 2–3:

* `classResidue`: the CRT class of the `S`-set — for *good* tuples (all
  `[dᵢ,eᵢ]` coprime to `W` and pairwise coprime) the system `n ≡ b (W)`,
  `[dᵢ,eᵢ] ∣ n + Hᵢ` collapses to the single class `n + h ≡ c (q)`,
  `q = W·∏ᵢ[dᵢ,eᵢ]` (`classResidue_spec`, from the fleet lemma
  `filter_shift_system_class`);
* `thetaExpansion_eq_good_part`: the non-good tuples contribute `0` to the
  θ-sum (the `S`-set is empty);
* `thetaSset_eq_expected_add_disc_of_good`: for a good tuple the discrepancy
  decomposition of `Submission.LevelOfDistribution` applies:
  `S̃ = (1/φ(q))·Σ_{(n+h,q)=1} θ(n+h) + Δ(θ; c (q))`;
* `thetaWindowProduct_decomposition`: the assembled Theorem 3.5 structure.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The CRT class residue (P8 (44)–(45)) attached to a divisor pair: for a
*good* tuple of moduli `m` (coprime to `W` and pairwise coprime) the `S`-set is
the single class `(n+h) ≡ classResidue (mod W·∏ᵢ mᵢ)`; for bad tuples the value
is irrelevant (the good-indicator kills it). -/
noncomputable def classResidue {k : ℕ} (N W b h : ℕ) (H : Fin k → ℕ) (m : Fin k → ℕ) : ℕ :=
  if hgood : W ≠ 0 ∧ (∀ i : Fin k, m i ≠ 0) ∧ (∀ i : Fin k, (m i).Coprime W) ∧
      (∀ i j : Fin k, i ≠ j → (m i).Coprime (m j)) then
    Classical.choose (Commons.NumberTheory.CongruenceWindows.filter_shift_system_class
      (k := k) (N := N) (W := W) (b := b) (h := h) H m hgood.1 hgood.2.1
      hgood.2.2.1 hgood.2.2.2)
  else 0

/-- Specification of `classResidue` on good tuples. -/
theorem classResidue_spec {k : ℕ} (N W b h : ℕ) (H : Fin k → ℕ) (m : Fin k → ℕ)
    (hW : W ≠ 0) (hm : ∀ i : Fin k, m i ≠ 0) (hcop : ∀ i : Fin k, (m i).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j → (m i).Coprime (m j)) :
    Sset N W b H m = (Finset.Icc N (2 * N)).filter
        (fun n => (n + h) % (W * ∏ i, m i) =
          classResidue N W b h H m % (W * ∏ i, m i)) := by
  have hgood : W ≠ 0 ∧ (∀ i : Fin k, m i ≠ 0) ∧ (∀ i : Fin k, (m i).Coprime W) ∧
      (∀ i j : Fin k, i ≠ j → (m i).Coprime (m j)) := ⟨hW, hm, hcop, hcopm⟩
  have hspec := Classical.choose_spec
    (Commons.NumberTheory.CongruenceWindows.filter_shift_system_class
      (k := k) (N := N) (W := W) (b := b) (h := h) H m hW hm hcop hcopm)
  simp only [classResidue, dif_pos hgood]
  rw [Sset]
  exact hspec

/-- **Discrepancy decomposition of the θ-weighted `S`-set sum** for a good
tuple: `S̃ = (1/φ(q))·Σ_{(n+h,q)=1}θ(n+h) + Δ(θ; c (q))`, `q = W·∏ᵢ mᵢ`. -/
theorem thetaSset_eq_expected_add_disc_of_good {k N W b : ℕ} {H : Fin k → ℕ}
    {m : Fin k → ℕ} {h : ℕ}
    (hW : W ≠ 0) (hm : ∀ i : Fin k, m i ≠ 0) (hcop : ∀ i : Fin k, (m i).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j → (m i).Coprime (m j)) :
    thetaSset N W b H m h =
      (1 / (((W * ∏ i, m i).totient : ℕ) : ℝ)) *
          (∑ n ∈ (Finset.Icc N (2 * N)).filter
            (fun n => (n + h).Coprime (W * ∏ i, m i)), thetaNat (n + h)) +
        discShift (fun n => thetaNat n) N (W * ∏ i, m i) (classResidue N W b h H m) h := by
  exact thetaSset_eq_expected_add_disc (q := W * ∏ i, m i)
    (c := classResidue N W b h H m) (classResidue_spec N W b h H m hW hm hcop hcopm)

/-! ## The non-good tuples contribute nothing -/

/-- Non-good divisor pairs give zero contribution to the θ-weighted expansion. -/
theorem thetaExpansion_bad_sum_zero {k D N W b wd : ℕ} {H : Fin k → ℕ} (h : ℕ)
    {α β : Fin k → ℕ → ℝ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      (1 - goodInd W d e) *
        (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  by_cases hG : lcmGood W d e
  · simp [goodInd, hG]
  · have hnot : ¬ lcmGood W d e := hG
    by_cases hWgood : ∀ i : Fin k, (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W
    · have hMbad : ¬ (∀ i j : Fin k, i ≠ j →
          (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ))) := by
        intro hM
        exact hnot (by simpa [lcmGood] using ⟨hWgood, hM⟩)
      have hex : ∃ i : Fin k, ∃ j : Fin k, i ≠ j ∧
          ¬ (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ)) := by
        push Not at hMbad
        exact hMbad
      obtain ⟨i, j, hij, hbad⟩ := hex
      have hs : Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) = ∅ :=
        Sset_card_eq_zero_of_not_pairwise_coprime (k := k) (N := N) (W := W) (b := b)
          (wd := wd) (H := H) (m := fun i => Nat.lcm (d i : ℕ) (e i : ℕ))
          (i := i) (j := j) hWdiv hHinj hbW hsep hij hbad
      have hz : thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h = 0 := by
        simp [thetaSset, hs]
      simp [goodInd, hG, hz]
    · obtain ⟨i, hi⟩ := not_forall.mp hWgood
      have hs : Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) = ∅ :=
        Sset_card_eq_zero_of_not_coprime_W (k := k) (N := N) (W := W) (b := b)
          (H := H) (m := fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) (i := i) (hbW i) hi
      have hz : thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h = 0 := by
        simp [thetaSset, hs]
      simp [goodInd, hG, hz]

/-- **Split-and-kill for the θ-weighted expansion.**  The full divisor-tuple sum
equals its `lcmGood`-restricted part. -/
theorem thetaExpansion_eq_good_part {k D N W b wd : ℕ} {H : Fin k → ℕ} (h : ℕ)
    {α β : Fin k → ℕ → ℝ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h) =
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      goodInd W d e *
        (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h)) := by
  classical
  let f : (Fin k → Fin (D + 1)) → (Fin k → Fin (D + 1)) → ℝ := fun d e =>
    coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
      thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h
  have hsplit := expansion_sum_split_good (k := k) (D := D) (W := W) (f := f)
  have hbad := thetaExpansion_bad_sum_zero (k := k) (D := D) (N := N) (W := W) (b := b)
    (wd := wd) (H := H) h (α := α) (β := β) hWdiv hHinj hbW hsep
  dsimp [f] at hsplit hbad
  rw [hsplit, hbad]
  ring

/-! ## The assembled Theorem 3.5 structure -/

/-- **Theorem 3.5 structure (θ-weighted window sum).**  The prime window sum of
Polymath8a (26) equals, up to the vanishing of non-good tuples, the sum over
good divisor pairs of the coefficient times the CRT class sum, decomposed as
`(1/φ(q))·Σ_{(n+h,q)=1}θ(n+h) + Δ(θ; c (q))` with `q = W·∏ᵢ[dᵢ,eᵢ]`. -/
theorem thetaWindowProduct_decomposition {k D N W b wd : ℕ} {H : Fin k → ℕ} (h : ℕ)
    (α β : Fin k → ℕ → ℝ) (hW2 : 2 ≤ W)
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
        thetaNat (n + h) * ∏ i : Fin k,
          (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
    ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      goodInd W d e *
        (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          ((1 / (((W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) *
              (∑ n ∈ (Finset.Icc N (2 * N)).filter
                (fun n => (n + h).Coprime (W * ∏ i : Fin k,
                  Nat.lcm (d i : ℕ) (e i : ℕ))), thetaNat (n + h)) +
            discShift (fun n => thetaNat n) N
              (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ))
              (classResidue N W b h H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) h)) := by
  classical
  rw [thetaResidueWindowProduct_eq_weighted_thetaSset (h := h) (α := α) (β := β)]
  have hfold : (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
          thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h) =
      (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          thetaSset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) h) := by
    simp only [coefProd]
  rw [hfold, thetaExpansion_eq_good_part (k := k) (D := D) (N := N) (W := W) (b := b)
    (wd := wd) (H := H) h (α := α) (β := β) hWdiv hHinj hbW hsep]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
  have hWpos : W ≠ 0 := by omega
  by_cases hg : lcmGood W d e
  · have hg' : (∀ i : Fin k, (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W) ∧
        (∀ i j : Fin k, i ≠ j →
          (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ))) := by
      simpa [lcmGood] using hg
    have hm0 : ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ≠ 0 := fun i =>
      Nat.lcm_ne_zero
        (coprime_lcm_ne_zero_left (d := (d i : ℕ)) (e := (e i : ℕ)) (W := W) hW2 (hg'.1 i))
        (coprime_lcm_ne_zero_right (d := (d i : ℕ)) (e := (e i : ℕ)) (W := W) hW2 (hg'.1 i))
    have hid := thetaSset_eq_expected_add_disc_of_good (k := k) (N := N) (W := W) (b := b)
      (H := H) (m := fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) (h := h) hWpos hm0
      hg'.1 hg'.2
    have hgi : goodInd W d e = 1 := by simp [goodInd, hg]
    rw [hgi, hid, one_mul]
  · simp [goodInd, hg]

end Commons.NumberTheory.MaynardSieve
