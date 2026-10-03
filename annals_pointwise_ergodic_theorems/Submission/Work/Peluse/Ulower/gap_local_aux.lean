/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.

# Auxiliary lemmas for the gap-regime localisation

The elementary lemmas underlying `Submission/Work/Peluse/Ulower/gap_local_block.lean`:

* `reach_natAbs_le`, `iterDelta_ne_zero_reach`, `iterDelta_congr`, `iterDelta_supportIn` — the
  reach `reach k sh` of the iterated difference `iterDelta k sh` (defined in `gap_local_defs`);
* `mem_arithIcc_le` — the entries of the arithmetic-progression set `c[D]` are bounded by `D |c|`;
* `gapGoodSet_conditions`, `dualFn_gapLocalise_eq` — on the interior `gapGoodSet P N Ns` of the
  window, the windowed dual function is the translate of the original one;
* `sum_shift_window_eq`, `exists_shift_window_ge` — the averaging of a window sum over the shifts.
-/
import Mathlib
import Submission.Work.Peluse.PETTwo.eval_abs_le_polySup_abs
import Submission.Work.Peluse.Ulower.gap_localise
import Submission.Work.Peluse.Ulower.gap_local_defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## The reach of the iterated difference -/

/-- **The reach bounds the shifts of `iterDelta`.** -/
theorem reach_natAbs_le (k : ℕ) : ∀ (sh : Fin k → ℤ × ℤ) {M : ℕ},
    (∀ i : Fin k, (sh i).1.natAbs ≤ M ∧ (sh i).2.natAbs ≤ M) →
    ∀ ζ ∈ reach k sh, ζ.natAbs ≤ k * M := by
  induction k with
  | zero =>
      intro sh M _ ζ hζ
      have hζ0 : ζ = 0 := by
        simpa only [reach, Finset.mem_singleton] using hζ
      simp [hζ0]
  | succ k ih =>
      intro sh M hM ζ hζ
      rw [reach] at hζ
      rcases Finset.mem_union.mp hζ with h | h
      · obtain ⟨ζ', hζ', rfl⟩ := Finset.mem_image.mp h
        have h1 := ih (fun i => sh i.succ) (fun i => hM i.succ) ζ' hζ'
        have h2 := (hM 0).1
        calc (ζ' + (sh 0).1).natAbs ≤ ζ'.natAbs + ((sh 0).1).natAbs := Int.natAbs_add_le _ _
          _ ≤ k * M + M := by omega
          _ = (k + 1) * M := by ring
      · obtain ⟨ζ', hζ', rfl⟩ := Finset.mem_image.mp h
        have h1 := ih (fun i => sh i.succ) (fun i => hM i.succ) ζ' hζ'
        have h2 := (hM 0).2
        calc (ζ' + (sh 0).2).natAbs ≤ ζ'.natAbs + ((sh 0).2).natAbs := Int.natAbs_add_le _ _
          _ ≤ k * M + M := by omega
          _ = (k + 1) * M := by ring

/-- **`iterDelta` reads its argument only through the reach.** -/
theorem iterDelta_ne_zero_reach (k : ℕ) : ∀ (sh : Fin k → ℤ × ℤ) (F : ℤ → ℂ) (w : ℤ),
    iterDelta k sh F w ≠ 0 → ∃ ζ ∈ reach k sh, F (w + ζ) ≠ 0 := by
  induction k with
  | zero =>
      intro sh F w h
      exact ⟨0, by simp [reach], by simpa [iterDelta_zero] using h⟩
  | succ k ih =>
      intro sh F w h
      simp only [iterDelta_succ] at h
      have h1 : iterDelta k (fun i => sh i.succ) F (w + (sh 0).1) ≠ 0 :=
        fun hc => h (by rw [hc, zero_mul])
      obtain ⟨ζ, hζ, hF⟩ := ih (fun i => sh i.succ) F (w + (sh 0).1) h1
      refine ⟨ζ + (sh 0).1, ?_, ?_⟩
      · rw [reach]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ζ, hζ, rfl⟩)
      · rwa [show (w + (sh 0).1) + ζ = w + (ζ + (sh 0).1) by ring] at hF

/-- **`iterDelta` commutes with a translation on a set where the two functions agree.** -/
theorem iterDelta_congr (k : ℕ) :
    ∀ (sh : Fin k → ℤ × ℤ) (F F' : ℤ → ℂ) (J : Finset ℤ) (a : ℤ),
      (∀ u ∈ J, F' u = F (u + a)) → ∀ w : ℤ, (∀ ζ ∈ reach k sh, w + ζ ∈ J) →
      iterDelta k sh F' w = iterDelta k sh F (w + a) := by
  induction k with
  | zero =>
      intro sh F F' J a hJ w hw
      rw [iterDelta_zero, iterDelta_zero]
      exact hJ w (by simpa using hw 0 (by simp [reach]))
  | succ k ih =>
      intro sh F F' J a hJ w hw
      have h1 : iterDelta k (fun i => sh i.succ) F' (w + (sh 0).1)
          = iterDelta k (fun i => sh i.succ) F ((w + (sh 0).1) + a) :=
        ih (fun i => sh i.succ) F F' J a hJ (w + (sh 0).1) (fun ζ hζ => by
          rw [show (w + (sh 0).1) + ζ = w + (ζ + (sh 0).1) by ring]
          exact hw _ (by
            rw [reach]
            exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ζ, hζ, rfl⟩)))
      have h2 : iterDelta k (fun i => sh i.succ) F' (w + (sh 0).2)
          = iterDelta k (fun i => sh i.succ) F ((w + (sh 0).2) + a) :=
        ih (fun i => sh i.succ) F F' J a hJ (w + (sh 0).2) (fun ζ hζ => by
          rw [show (w + (sh 0).2) + ζ = w + (ζ + (sh 0).2) by ring]
          exact hw _ (by
            rw [reach]
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ζ, hζ, rfl⟩)))
      simp only [iterDelta_succ]
      rw [h1, h2,
        show (w + (sh 0).1) + a = (w + a) + (sh 0).1 by ring,
        show (w + (sh 0).2) + a = (w + a) + (sh 0).2 by ring]

/-- **`iterDelta` preserves support in `symIcc`, up to the reach.** -/
theorem iterDelta_supportIn {k : ℕ} (sh : Fin k → ℤ × ℤ) {B M : ℕ}
    (hM : ∀ i : Fin k, (sh i).1.natAbs ≤ M ∧ (sh i).2.natAbs ≤ M) {F : ℤ → ℂ}
    (hF : SupportIn F B) : SupportIn (iterDelta k sh F) (B + k * M) := by
  intro w hw
  by_contra hne
  obtain ⟨ζ, hζ, hFne⟩ := iterDelta_ne_zero_reach k sh F w hne
  have h1 : ζ.natAbs ≤ k * M := reach_natAbs_le k sh hM ζ hζ
  have h2 : (w + ζ).natAbs ≤ B := by
    by_contra hc
    exact hFne (hF (w + ζ) (by omega))
  have h3 : w.natAbs ≤ (w + ζ).natAbs + ζ.natAbs := by
    simpa using Int.natAbs_add_le (w + ζ) (-ζ)
  omega

/-- **`polySup` is at most the sum of the absolute values of the coefficients times `N ^ deg P`.**
This is the bound that makes `polySup P N` comparable to `N ^ P.natDegree`. -/
theorem polySup_le (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) :
    polySup P N ≤ ((Finset.range (P.natDegree + 1)).sum (fun i => (P.coeff i).natAbs))
      * N ^ P.natDegree := by
  rw [polySup, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hid : i ≤ P.natDegree := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN hid)

/-! ## The constants of the localisation

`gapNs P s N` is the localisation radius `Ns`, `gapHalf P s N` the radius `ℓ` of the *interior* of
the window (`gapNs P s N = 2 * gapHalf P s N`, and the interior condition is
`gapK0 P N + gapSig P s D ≤ gapHalf P s N`), `gapRho P s N N₀ D` the radius of the support of the
mass function of the original data and `gapR P s N N₀ D` the range of the localisation centres. -/

/-- The sum of the absolute values of the coefficients of `P`. -/
def gapCsum (P : Polynomial ℤ) : ℕ :=
  (Finset.range (P.natDegree + 1)).sum (fun i => (P.coeff i).natAbs)

/-- The constant `C₂` with `Ns = C₂ N ^ deg P` (an even number). -/
def gapC2 (P : Polynomial ℤ) (s : ℕ) : ℕ := 2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4

/-- The localisation radius `Ns = C₂ N ^ deg P`. -/
def gapNs (P : Polynomial ℤ) (s N : ℕ) : ℕ := gapC2 P s * N ^ P.natDegree

/-- The radius `ℓ = Ns / 2` of the interior of the window. -/
def gapHalf (P : Polynomial ℤ) (s N : ℕ) : ℕ :=
  (gapCsum P + 1 + s * P.leadingCoeff.natAbs + 2) * N ^ P.natDegree

/-- The size `K₀ = polySup P N + N` of the window needed by the dual function. -/
def gapK0 (P : Polynomial ℤ) (N : ℕ) : ℕ := polySup P N + N

/-- A bound `σ = s D |lc P|` for the reach of the iterated difference. -/
def gapSig (P : Polynomial ℤ) (s D : ℕ) : ℕ := s * D * P.leadingCoeff.natAbs

/-- The radius of the support of the mass function of the original data. -/
def gapRho (P : Polynomial ℤ) (s N N₀ D : ℕ) : ℕ :=
  dSup P N₀ N + gapSig P s D + 2 * (D * P.leadingCoeff.natAbs)

/-- The range of the localisation centres. -/
def gapR (P : Polynomial ℤ) (s N N₀ D : ℕ) : ℕ := gapRho P s N N₀ D + gapHalf P s N

/-- The constant `A₀` of the conclusion. -/
def gapA0 (P : Polynomial ℤ) (s : ℕ) : ℕ := 1000 * (gapC2 P s + 1) * (s + 1) + 1000

/-- `gapNs = 2 * gapHalf`. -/
theorem gapNs_eq_two_gapHalf (P : Polynomial ℤ) (s N : ℕ) :
    gapNs P s N = 2 * gapHalf P s N := by
  rw [gapNs, gapHalf, gapC2]; ring

/-- **The interior condition.**  The reach `gapK0 P N + gapSig P s D` of the iterated difference
(added to the window needed by the dual function) is at most the interior radius `gapHalf`. -/
theorem gapK0_add_gapSig_le_gapHalf (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (s N D : ℕ)
    (hN : 1 ≤ N) (hD : D ≤ N ^ P.natDegree) :
    gapK0 P N + gapSig P s D ≤ gapHalf P s N := by
  have hp : polySup P N ≤ gapCsum P * N ^ P.natDegree := polySup_le P hN
  have hNd : N ≤ N ^ P.natDegree := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ P.natDegree := Nat.pow_le_pow_right hN hd
  have hs : gapSig P s D ≤ s * P.leadingCoeff.natAbs * N ^ P.natDegree := by
    rw [gapSig]
    calc s * D * P.leadingCoeff.natAbs = (s * P.leadingCoeff.natAbs) * D := by ring
      _ ≤ (s * P.leadingCoeff.natAbs) * N ^ P.natDegree := Nat.mul_le_mul_left _ hD
  have h1 : polySup P N + N ≤ (gapCsum P + 1) * N ^ P.natDegree := by
    calc polySup P N + N ≤ gapCsum P * N ^ P.natDegree + N ^ P.natDegree := add_le_add hp hNd
      _ = (gapCsum P + 1) * N ^ P.natDegree := by ring
  rw [gapK0, gapHalf]
  calc polySup P N + N + gapSig P s D
      ≤ (gapCsum P + 1) * N ^ P.natDegree + s * P.leadingCoeff.natAbs * N ^ P.natDegree :=
        add_le_add h1 hs
    _ ≤ (gapCsum P + 1 + s * P.leadingCoeff.natAbs + 2) * N ^ P.natDegree := by
        have hle : gapCsum P + 1 + s * P.leadingCoeff.natAbs
            ≤ gapCsum P + 1 + s * P.leadingCoeff.natAbs + 2 := by omega
        calc (gapCsum P + 1) * N ^ P.natDegree + s * P.leadingCoeff.natAbs * N ^ P.natDegree
            = (gapCsum P + 1 + s * P.leadingCoeff.natAbs) * N ^ P.natDegree := by ring
          _ ≤ (gapCsum P + 1 + s * P.leadingCoeff.natAbs + 2) * N ^ P.natDegree :=
              Nat.mul_le_mul_right _ hle

/-! ## The arithmetic-progression shift set -/

/-- The entries of `c[D] = arithIcc c D` are bounded by `D |c|`. -/
theorem mem_arithIcc_le {c : ℤ} {D : ℕ} {z : ℤ} (hz : z ∈ arithIcc c D) :
    z.natAbs ≤ D * c.natAbs := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
  have hmD : m ≤ D := (Finset.mem_Icc.mp hm).2
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  rw [← mul_comm c.natAbs D]
  exact Nat.mul_le_mul_left _ hmD

/-- The cardinality of a symmetric interval. -/
theorem symIcc_card' (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc]
  have h : (L : ℤ) + 1 - (-(L : ℤ)) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-! ## The interior of the window -/

/-- **Membership in the interior of the window.** -/
theorem gapGoodSet_conditions {P : Polynomial ℤ} {N Ns : ℕ} (hNs : polySup P N + N ≤ Ns)
    {w : ℤ} (hw : w ∈ gapGoodSet P N Ns) : ∀ y ∈ Finset.Icc 1 N,
    (w - P.eval (y : ℤ)) ∈ symIcc Ns ∧ (w + (y : ℤ) - P.eval (y : ℤ)) ∈ symIcc Ns := by
  have hwabs : w.natAbs ≤ Ns - (polySup P N + N) := by
    rw [gapGoodSet, mem_symIcc_iff] at hw
    exact hw
  intro y hy
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
  have hyZ : |(y : ℤ)| ≤ (N : ℤ) := by
    rw [abs_of_nonneg (by exact_mod_cast (Nat.zero_le y : 0 ≤ y))]
    exact_mod_cast hy2
  have hPabs : |P.eval (y : ℤ)| ≤ ((polySup P N : ℕ) : ℤ) :=
    Work.Peluse.PETTwo.eval_abs_le_polySup_abs hyZ
  have hPnat : (P.eval (y : ℤ)).natAbs ≤ polySup P N := by
    rw [← Int.natCast_natAbs] at hPabs
    exact_mod_cast hPabs
  have hyn : (y : ℤ).natAbs = y := Int.natAbs_natCast y
  constructor
  · rw [mem_symIcc_iff]
    calc (w - P.eval (y : ℤ)).natAbs ≤ w.natAbs + (P.eval (y : ℤ)).natAbs := Int.natAbs_sub_le _ _
      _ ≤ (Ns - (polySup P N + N)) + polySup P N := add_le_add hwabs hPnat
      _ ≤ Ns := by omega
  · rw [mem_symIcc_iff]
    have h1 : (w + (y : ℤ) - P.eval (y : ℤ)).natAbs
        ≤ (w + (y : ℤ)).natAbs + (P.eval (y : ℤ)).natAbs := Int.natAbs_sub_le _ _
    have h2 : (w + (y : ℤ)).natAbs ≤ w.natAbs + y := by
      calc (w + (y : ℤ)).natAbs ≤ w.natAbs + ((y : ℤ)).natAbs := Int.natAbs_add_le _ _
        _ = w.natAbs + y := by rw [hyn]
    have h3 : w.natAbs + y ≤ (Ns - (polySup P N + N)) + N := by omega
    have h4 : (Ns - (polySup P N + N)) + N + polySup P N ≤ Ns := by omega
    omega

/-- **The localised dual function on the interior is the translate of the original one.** -/
theorem dualFn_gapLocalise_eq {P : Polynomial ℤ} {N Ns : ℕ} (hNs : polySup P N + N ≤ Ns)
    (f₀ f₁ : ℤ → ℂ) (a : ℤ) {w : ℤ} (hw : w ∈ gapGoodSet P N Ns) :
    dualFn N P (gapLocalise f₀ a Ns) (gapLocalise f₁ a Ns) w = dualFn N P f₀ f₁ (w + a) := by
  simp only [dualFn]
  congr 1
  refine Finset.sum_congr rfl (fun y hy => ?_)
  obtain ⟨h1, h2⟩ := gapGoodSet_conditions hNs hw y hy
  rw [gapLocalise_apply_of_mem h1, gapLocalise_apply_of_mem h2]
  ring_nf

/-! ## Averaging a window sum over the shifts -/

/-- **Averaging a window sum.** -/
theorem sum_shift_window_eq {g : ℤ → ℝ} (hg : ∀ x : ℤ, 0 ≤ g x) {ρ l R : ℕ} (hlR : l + ρ ≤ R)
    (hsupp : ∀ x : ℤ, ρ < x.natAbs → g x = 0) :
    ∑ a ∈ symIcc R, ∑ x ∈ symIcc l, g (x + a) = ((2 * l + 1 : ℕ) : ℝ) * ∑' v : ℤ, g v := by
  have htotal : ∀ x : ℤ, x ∈ symIcc l → ∑ a ∈ symIcc R, g (x + a) = ∑' v : ℤ, g v := by
    intro x hx
    have hxl : x.natAbs ≤ l := mem_symIcc_iff.mp hx
    have hinj : ∀ a ∈ symIcc R, ∀ b ∈ symIcc R, x + a = x + b → a = b := by
      intro a _ b _ hab
      simpa using hab
    have himg : symIcc ρ ⊆ (symIcc R).image (fun a : ℤ => x + a) := by
      intro v hv
      have hvl : v.natAbs ≤ ρ := mem_symIcc_iff.mp hv
      refine Finset.mem_image.mpr ⟨v - x, ?_, by ring⟩
      rw [mem_symIcc_iff]
      calc (v - x).natAbs ≤ v.natAbs + x.natAbs := Int.natAbs_sub_le _ _
        _ ≤ ρ + l := by omega
        _ ≤ R := by omega
    have hzero : ∀ v ∈ (symIcc R).image (fun a : ℤ => x + a), v ∉ symIcc ρ → g v = 0 := by
      intro v _ hv
      exact hsupp v (by
        by_contra hc
        exact hv (mem_symIcc_iff.mpr (not_lt.mp hc)))
    calc ∑ a ∈ symIcc R, g (x + a)
        = ∑ v ∈ (symIcc R).image (fun a : ℤ => x + a), g v := (Finset.sum_image hinj).symm
      _ = ∑ v ∈ symIcc ρ, g v := (Finset.sum_subset himg hzero).symm
      _ = ∑' v : ℤ, g v := (tsum_eq_sum (s := symIcc ρ) (fun v hv => hsupp v (by
            by_contra hc
            exact hv (mem_symIcc_iff.mpr (not_lt.mp hc))))).symm
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x hx => htotal x hx)]
  rw [Finset.sum_const, nsmul_eq_mul, symIcc_card']

/-- **A shift carrying at least the average of the window sums exists.** -/
theorem exists_shift_window_ge {g : ℤ → ℝ} (hg : ∀ x : ℤ, 0 ≤ g x) {ρ l R : ℕ} (hlR : l + ρ ≤ R)
    (hsupp : ∀ x : ℤ, ρ < x.natAbs → g x = 0) :
    ∃ a ∈ symIcc R, ((2 * l + 1 : ℕ) : ℝ) * (∑' v : ℤ, g v) / ((2 * R + 1 : ℕ) : ℝ)
      ≤ ∑ x ∈ symIcc l, g (x + a) := by
  have h := sum_shift_window_eq hg hlR hsupp
  have hne : (symIcc R).Nonempty := ⟨0, by rw [mem_symIcc_iff]; simp⟩
  have hR : ((2 * R + 1 : ℕ) : ℝ) = ((symIcc R).card : ℝ) := by rw [symIcc_card']
  by_contra hcon
  push_neg at hcon
  have h1 : ∀ a ∈ symIcc R, (∑ x ∈ symIcc l, g (x + a))
      ≤ ((2 * l + 1 : ℕ) : ℝ) * (∑' v : ℤ, g v) / ((2 * R + 1 : ℕ) : ℝ) :=
    fun a ha => le_of_lt (hcon a ha)
  obtain ⟨a₀, ha₀⟩ := hne
  have h2 : ∑ a ∈ symIcc R, (∑ x ∈ symIcc l, g (x + a))
      < ∑ a ∈ symIcc R, ((2 * l + 1 : ℕ) : ℝ) * (∑' v : ℤ, g v) / ((2 * R + 1 : ℕ) : ℝ) :=
    Finset.sum_lt_sum h1 ⟨a₀, ha₀, hcon a₀ ha₀⟩
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  rw [h] at h2
  have hX : ((symIcc R).card : ℝ)
      * (((2 * l + 1 : ℕ) : ℝ) * (∑' v : ℤ, g v) / ((2 * R + 1 : ℕ) : ℝ))
      = ((2 * l + 1 : ℕ) : ℝ) * (∑' v : ℤ, g v) := by
    rw [← hR, mul_comm]
    exact div_mul_cancel₀ _ (by positivity)
  rw [hX] at h2
  exact lt_irrefl _ h2

end

end Work.Peluse.Ulower
