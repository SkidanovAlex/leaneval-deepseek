/-
# `Work.FIChain.VfB_le_mul_ratio` — the `VfB` ratio bound at the window floor `max 2 c`

The sieve product `VfB ν y = ∏_{p < y}(1 - ν p)` (`LamPlusBLayerDefs`) decreases with the range,
and the windowed `Ω_κ` norm `LinNormKup ν C κ D` (`LamPlusBLayerDefs`) controls the ratio

    `∏_{w ≤ p < z}(1 - ν p)⁻¹ ≤ C · (log z / log w)^κ`   (`2 ≤ w ≤ z ≤ D`).

The lemma proved here evaluates the ratio between the range `c` (an arbitrary real, where the
product is governed by the primes below `⌈c⌉₊`) and a *natural* upper endpoint `Y ≥ 2`, and it
replaces the lower endpoint `c` by the window floor `max 2 c`: this is exactly the form in which
the Rosser–Iwaniec layer/majorant analysis consumes the norm, because every window used there is
at least `2` (`Work.FIChain.layerU`).

The single substantive ingredient is `VfB_le_VfB_mul_LinNormKup_real` below: the ratio bound for
two arbitrary real endpoints `2 ≤ w ≤ Z ≤ D`, with the density only required to satisfy
`0 ≤ ν p < 1` (in particular `ν p ≤ 4/5`, the standing hypothesis of the `4/5`-density fundamental
lemma).  The passage from a real lower endpoint `w` to the sieve range `VfB ν w` needs the primes
of the non-integral tail `[w, ⌈w⌉₊)`, whose inverse factors `(1 - ν p)⁻¹` are `≥ 1` because
`ν p ≥ 0`.
-/
import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.OddLayersMajorantDefs

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **`VfB` ratio bound with two real endpoints and the windowed norm.**
For `2 ≤ w ≤ Z ≤ D` and a density with `0 ≤ ν p < 1` at primes satisfying `LinNormKup ν C κ D`,

  `VfB ν w ≤ VfB ν Z * (C * (log Z / log w) ^ κ)`. -/
theorem VfB_le_VfB_mul_LinNormKup_real {ν : ℕ → ℝ} {C κ D : ℝ} (h : LinNormKup ν C κ D)
    (hν0 : ∀ p : ℕ, p.Prime → 0 ≤ ν p) (hν1 : ∀ p : ℕ, p.Prime → ν p < 1)
    {w Z : ℝ} (hw : 2 ≤ w) (hwZ : w ≤ Z) (hZD : Z ≤ D) :
    VfB ν w ≤ VfB ν Z * (C * (Real.log Z / Real.log w) ^ κ) := by
  set A : ℕ := ⌈w⌉₊ with hA
  set Bz : ℕ := ⌈Z⌉₊ with hBz
  have hwZA : w ≤ (A : ℝ) := Nat.le_ceil w
  have hAB : A ≤ Bz := by
    rw [hA, hBz]
    exact Nat.ceil_mono hwZ
  have hsub : Nat.primesBelow A ⊆ Nat.primesBelow Bz := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (by exact_mod_cast hAB), hp.2⟩
  have hsmall : Nat.primesBelow Bz \ Nat.primesBelow A
      = (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hz, hp⟩, hnc⟩
      exact ⟨⟨hz, hp⟩, by by_contra h; exact hnc ⟨by omega, hp⟩⟩
    · rintro ⟨⟨hz, hp⟩, hc⟩; exact ⟨⟨hz, hp⟩, by omega⟩
  have hbig : (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p)
      ⊆ (Nat.primesBelow Bz).filter (fun p : ℕ => w ≤ (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, le_trans hwZA (by exact_mod_cast hp.2)⟩
  have hpos : ∀ p ∈ Nat.primesBelow Bz, 0 < 1 - ν p := by
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have := hν1 p hp'; linarith
  have hge1 : ∀ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => w ≤ (p : ℝ)),
      1 ≤ (1 - ν p)⁻¹ := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp.1).2
    have h0 := hν0 p hp'; have h1 := hν1 p hp'
    exact (one_le_inv₀ (by linarith : (0 : ℝ) < 1 - ν p)).mpr (by linarith)
  have hsplit : ∏ p ∈ Nat.primesBelow Bz, (1 - ν p)
      = (∏ p ∈ Nat.primesBelow A, (1 - ν p))
        * ∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p) := by
    rw [← Finset.prod_sdiff hsub, hsmall, mul_comm]
  have hPpos : 0 < ∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p) :=
    Finset.prod_pos (fun p hp => hpos p (Finset.mem_filter.mp hp).1)
  have hlin := h w Z hw hwZ hZD
  rw [← hBz] at hlin
  rw [Finset.prod_inv_distrib] at hlin
  have hmono : (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p))⁻¹
      ≤ (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p))⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib]
    have hsd := Finset.prod_sdiff hbig (f := fun p : ℕ => (1 - ν p)⁻¹)
    have hrest : 1 ≤ ∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => w ≤ (p : ℝ))
        \ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p)⁻¹ :=
      Finset.one_le_prod₀ (fun p hp => hge1 p (Finset.mem_sdiff.mp hp).1)
    calc (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p)⁻¹)
        ≤ (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p)⁻¹)
            * (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => w ≤ (p : ℝ))
                \ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p)⁻¹) :=
          le_mul_of_one_le_right (Finset.prod_nonneg fun p hp => by
            have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
            exact le_of_lt (inv_pos.mpr (by have := hν1 p hp'; linarith))) hrest
      _ = ∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p)⁻¹ := by
          rw [mul_comm]; exact hsd
  have hVZpos : 0 < ∏ p ∈ Nat.primesBelow Bz, (1 - ν p) :=
    Finset.prod_pos (fun p hp => hpos p hp)
  have key : ∏ p ∈ Nat.primesBelow A, (1 - ν p)
      = (∏ p ∈ Nat.primesBelow Bz, (1 - ν p))
        * (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p))⁻¹ := by
    rw [hsplit, mul_assoc, mul_inv_cancel₀ (ne_of_gt hPpos), mul_one]
  rw [show VfB ν w = ∏ p ∈ Nat.primesBelow A, (1 - ν p) from by rw [VfB, ← hA],
      show VfB ν Z = ∏ p ∈ Nat.primesBelow Bz, (1 - ν p) from by rw [VfB, ← hBz], key]
  calc (∏ p ∈ Nat.primesBelow Bz, (1 - ν p))
        * (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => A ≤ p), (1 - ν p))⁻¹
      ≤ (∏ p ∈ Nat.primesBelow Bz, (1 - ν p))
          * (∏ p ∈ (Nat.primesBelow Bz).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - ν p))⁻¹ :=
        mul_le_mul_of_nonneg_left hmono hVZpos.le
    _ ≤ (∏ p ∈ Nat.primesBelow Bz, (1 - ν p)) * (C * (Real.log Z / Real.log w) ^ κ) :=
        mul_le_mul_of_nonneg_left hlin hVZpos.le

/-- **Windowed `VfB` ratio bound at the floor `max 2 c`.**  If `c ≤ Y`, `2 ≤ Y ≤ D` and
`LinNormKup ν C κ D` holds for a density with `0 ≤ ν p ≤ 4/5` at primes, then

  `VfB ν c ≤ VfB ν Y * (C * (log Y / log (max 2 c)) ^ κ)`.

For `c ≤ 2` both sides see the empty sieve range (`VfB ν c = VfB ν 2 = 1`), and for `c > 2` the
lower endpoint is just `c`; in both cases `VfB ν c ≤ VfB ν (max 2 c)` and
`VfB_le_VfB_mul_LinNormKup_real` applies to the window `[max 2 c, Y] ⊆ [2, D]`. -/
lemma VfB_le_mul_ratio {ν : ℕ → ℝ} {C κ D : ℝ} (hLin : LinNormKup ν C κ D) (hC : 0 < C)
    (hκ : 0 ≤ κ) (hν0 : ∀ p : ℕ, p.Prime → 0 ≤ ν p) (hν1 : ∀ p : ℕ, p.Prime → ν p ≤ 4/5)
    {c : ℝ} {Y : ℕ} (hcY : c ≤ (Y : ℝ)) (hYD : (Y : ℝ) ≤ D) (h2Y : 2 ≤ (Y : ℝ)) :
    VfB ν c ≤ VfB ν (Y : ℝ) * (C * (Real.log (Y : ℝ) / Real.log (max 2 c)) ^ κ) := by
  have hν1' : ∀ p : ℕ, p.Prime → ν p < 1 := fun p hp => by
    have := hν1 p hp; linarith
  have hle : VfB ν c ≤ VfB ν (max 2 c) := by
    by_cases hc2 : c ≤ 2
    · rw [max_eq_left hc2, VfB_eq_one_of_le_two ν hc2, VfB_eq_one_of_le_two ν (le_refl 2)]
    · rw [max_eq_right (not_le.mp hc2).le]
  have hw : 2 ≤ max 2 c := le_max_left 2 c
  have hwZ : max 2 c ≤ (Y : ℝ) := max_le h2Y hcY
  exact le_trans hle
    (VfB_le_VfB_mul_LinNormKup_real hLin hν0 hν1' hw hwZ hYD)

end

end Work.FIChain
