import Mathlib
import Submission.Work.Analysis.InverseTheory.Basic

/-!
# The sliding-window identity for the `ρ`-transform

Given a summable `w : ℤ → ℂ` and a step `L ≥ 1`, let

`ρ r = ∑' j, (w (r - j L) - w (r - j L - 1))`

be the "sliding sum" of `w` along the arithmetic progression `r - L ℕ`.  Summing `ρ`
against a window of `L` consecutive integers `[n - L + 1, n]` recovers `w n`:

`∑' k, ρ k · 1_{k ≤ n ≤ k + L - 1} = w n`.

The point is that a window of `L` consecutive integers is exactly one representative of
every residue class mod `L`, so for fixed `j` the window sum of
`w (· - j L) - w (· - j L - 1)` telescopes along the window to
`w (n - j L) - w (n - j L - L)`; summing over `j` then telescopes on the whole
arithmetic progression `n - L ℕ`, and summability of `w` supplies the limit `w n`.

## Main statement

* `Work.KMTAreas.A4.slideSum_eq`
-/

set_option autoImplicit false

namespace Work.KMTAreas.A4

open scoped BigOperators

/-- `winFun n L t = n - L + 1 + t`, the enumeration of the `L` consecutive integers
`n - L + 1, …, n` by `t ∈ {0, …, L - 1}`. -/
def winFun (n : ℤ) (L : ℕ) (t : ℕ) : ℤ := n - (L : ℤ) + 1 + (t : ℤ)

lemma winFun_injOn (n : ℤ) (L : ℕ) :
    Set.InjOn (winFun n L) (↑(Finset.range L) : Set ℕ) := by
  intro x hx y hy h
  rw [Finset.mem_coe, Finset.mem_range] at hx hy
  simp only [winFun] at h
  exact_mod_cast (show (x : ℤ) = (y : ℤ) by omega)

/-- Membership in the window `{n - L + 1, …, n}` enumerated by `winFun`. -/
lemma mem_winFun_range (n : ℤ) (L : ℕ) (hL : 1 ≤ L) (k : ℤ) :
    k ∈ (Finset.range L).image (winFun n L) ↔ n - (L : ℤ) + 1 ≤ k ∧ k ≤ n := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, hk⟩
    rw [Finset.mem_range] at ht
    rw [← hk]
    have ht0 : (0 : ℤ) ≤ (t : ℤ) := by exact_mod_cast Nat.zero_le t
    have htL : (t : ℤ) < (L : ℤ) := by exact_mod_cast ht
    simp only [winFun]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(k - (n - (L : ℤ) + 1)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hnn : 0 ≤ k - (n - (L : ℤ) + 1) := by omega
      have hLz : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
      have hcast : (((k - (n - (L : ℤ) + 1)).toNat : ℤ)) = k - (n - (L : ℤ) + 1) :=
        Int.toNat_of_nonneg hnn
      have hlt : (((k - (n - (L : ℤ) + 1)).toNat : ℤ)) < (L : ℤ) := by
        rw [hcast]; omega
      exact_mod_cast hlt
    · have hnn : 0 ≤ k - (n - (L : ℤ) + 1) := by
        omega
      simp only [winFun]
      rw [Int.toNat_of_nonneg hnn]
      ring

/-- Telescoping a difference along `L` consecutive integers. -/
lemma sum_range_winFun_sub (w : ℤ → ℂ) (L : ℕ) (a : ℤ) :
    ∑ t ∈ Finset.range L, (w (a + (t : ℤ)) - w (a + (t : ℤ) - 1))
      = w (a + (L : ℤ) - 1) - w (a - 1) := by
  let F : ℕ → ℂ := fun u => w (a + (u : ℤ) - 1)
  calc ∑ t ∈ Finset.range L, (w (a + (t : ℤ)) - w (a + (t : ℤ) - 1))
      = ∑ t ∈ Finset.range L, (F (t + 1) - F t) := by
        refine Finset.sum_congr rfl ?_
        intro t _
        simp only [F]
        have harg : a + ((t + 1 : ℕ) : ℤ) - 1 = a + (t : ℤ) := by push_cast; ring
        rw [harg]
    _ = F L - F 0 := Finset.sum_range_sub F L
    _ = w (a + (L : ℤ) - 1) - w (a - 1) := by
        simp only [F]
        norm_num

theorem slideSum_eq (w : ℤ → ℂ) (L : ℕ) (hL : 1 ≤ L) (hw : Summable w) (ρ : ℤ → ℂ)
    (hρ : ∀ r : ℤ, ρ r = ∑' j : ℕ, (w (r - (j : ℤ) * (L : ℤ)) - w ((r - (j : ℤ) * (L : ℤ)) - 1)))
    (n : ℤ) :
    (∑' k : ℤ, ρ k * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) = w n := by
  classical
  have hLne : (L : ℤ) ≠ 0 := by
    have : L ≠ 0 := by omega
    exact_mod_cast this
  -- ### summability of the inner `j`-series, for every base point
  have hinj₁ : ∀ r : ℤ, Function.Injective (fun j : ℕ => r - (j : ℤ) * (L : ℤ)) := by
    intro r j j' h
    have h2 : (j : ℤ) * (L : ℤ) = (j' : ℤ) * (L : ℤ) := by linarith
    have h3 : (j : ℤ) = (j' : ℤ) := mul_right_cancel₀ hLne h2
    exact_mod_cast h3
  have hinj₂ : ∀ r : ℤ, Function.Injective (fun j : ℕ => r - (j : ℤ) * (L : ℤ) - 1) := by
    intro r j j' h
    have h2 : (j : ℤ) * (L : ℤ) = (j' : ℤ) * (L : ℤ) := by linarith
    have h3 : (j : ℤ) = (j' : ℤ) := mul_right_cancel₀ hLne h2
    exact_mod_cast h3
  have hsm : ∀ r : ℤ, Summable (fun j : ℕ =>
      w (r - (j : ℤ) * (L : ℤ)) - w ((r - (j : ℤ) * (L : ℤ)) - 1)) := by
    intro r
    exact (hw.comp_injective (hinj₁ r)).sub (hw.comp_injective (hinj₂ r))
  -- ### the window
  set s : Finset ℤ := (Finset.range L).image (winFun n L) with hs
  have hmem : ∀ k : ℤ, k ∈ s ↔ n - (L : ℤ) + 1 ≤ k ∧ k ≤ n := by
    intro k
    rw [hs]
    exact mem_winFun_range n L hL k
  -- ### step 1 : the sum over `ℤ` is a sum over the window
  have step1 : (∑' k : ℤ, ρ k * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
      = ∑ k ∈ s, ρ k := by
    have hsupp : ∀ k ∉ s,
        ρ k * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0) = 0 := by
      intro k hk
      have hk' : ¬ (n - (L : ℤ) + 1 ≤ k ∧ k ≤ n) := fun h => hk ((hmem k).mpr h)
      have hcond : ¬ (k ≤ n ∧ n ≤ k + (L : ℤ) - 1) := by
        rintro ⟨h1, h2⟩
        exact hk' ⟨by omega, h1⟩
      rw [if_neg hcond, mul_zero]
    rw [tsum_eq_sum hsupp]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk2 := (hmem k).mp hk
    rw [if_pos ⟨hk2.2, by omega⟩, mul_one]
  -- ### step 2 : expand `ρ`
  have step2 : ∑ k ∈ s, ρ k
      = ∑ k ∈ s, ∑' j : ℕ, (w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1)) := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hρ k]
  -- ### step 3 : exchange the order of summation
  have step3 : ∑ k ∈ s, ∑' j : ℕ, (w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1))
      = ∑' j : ℕ, ∑ k ∈ s, (w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1)) :=
    (Summable.tsum_finsetSum (f := fun (k : ℤ) (j : ℕ) =>
      w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1)) (fun k _ => hsm k)).symm
  -- ### step 4 : telescoping along the window
  have step4 : ∀ j : ℕ, ∑ k ∈ s, (w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1))
      = w (n - (j : ℤ) * (L : ℤ)) - w (n - (j : ℤ) * (L : ℤ) - (L : ℤ)) := by
    intro j
    set a : ℤ := n - (L : ℤ) + 1 - (j : ℤ) * (L : ℤ) with ha
    have hsum : ∑ k ∈ s, (w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1))
        = ∑ t ∈ Finset.range L, (w (a + (t : ℤ)) - w (a + (t : ℤ) - 1)) := by
      rw [hs, Finset.sum_image (winFun_injOn n L)]
      refine Finset.sum_congr rfl ?_
      intro t _
      have h1 : winFun n L t - (j : ℤ) * (L : ℤ) = a + (t : ℤ) := by
        simp only [winFun]
        rw [ha]
        ring
      rw [h1]
    rw [hsum, sum_range_winFun_sub w L a]
    have e1 : a + (L : ℤ) - 1 = n - (j : ℤ) * (L : ℤ) := by
      simp only [ha]; ring
    have e2 : a - 1 = n - (j : ℤ) * (L : ℤ) - (L : ℤ) := by
      simp only [ha]; ring
    rw [e1, e2]
  -- ### step 5 : the resulting series telescopes to `w n`
  have step5 : (∑' j : ℕ, (w (n - (j : ℤ) * (L : ℤ)) - w (n - (j : ℤ) * (L : ℤ) - (L : ℤ)))) = w n := by
    let F : ℕ → ℂ := fun k => w (n - (k : ℤ) * (L : ℤ))
    have hF : Summable F := hw.comp_injective (hinj₁ n)
    have hF1 : Summable (fun j : ℕ => F (j + 1)) := hF.comp_injective Nat.succ_injective
    have bridge : (∑' j : ℕ, (w (n - (j : ℤ) * (L : ℤ)) - w (n - (j : ℤ) * (L : ℤ) - (L : ℤ))))
        = ∑' j : ℕ, (F j - F (j + 1)) := by
      refine tsum_congr (fun j => ?_)
      change w (n - (j : ℤ) * (L : ℤ)) - w (n - (j : ℤ) * (L : ℤ) - (L : ℤ))
           = w (n - (j : ℤ) * (L : ℤ)) - w (n - ((j + 1 : ℕ) : ℤ) * (L : ℤ))
      have harg : n - ((j + 1 : ℕ) : ℤ) * (L : ℤ) = n - (j : ℤ) * (L : ℤ) - (L : ℤ) := by
        push_cast
        ring
      rw [harg]
    rw [bridge, hF.tsum_sub hF1, hF.tsum_eq_zero_add]
    have h0 : F 0 = w n := by
      change w (n - ((0 : ℕ) : ℤ) * (L : ℤ)) = w n
      norm_num
    rw [h0]
    simp
  calc (∑' k : ℤ, ρ k * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
      = ∑ k ∈ s, ρ k := step1
    _ = ∑ k ∈ s, ∑' j : ℕ, (w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1)) := step2
    _ = ∑' j : ℕ, ∑ k ∈ s, (w (k - (j : ℤ) * (L : ℤ)) - w ((k - (j : ℤ) * (L : ℤ)) - 1)) := step3
    _ = ∑' j : ℕ, (w (n - (j : ℤ) * (L : ℤ)) - w (n - (j : ℤ) * (L : ℤ) - (L : ℤ))) :=
        tsum_congr step4
    _ = w n := step5

end Work.KMTAreas.A4
