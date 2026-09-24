import Mathlib
import Submission.Work.GM.Trace.Spart_defs

/-!
# Counting the `m` with `nzCount m = 1` and `|rho m| ≤ X` (GM Proposition 5.1, counting step)

`rho m` is the unique non-zero coordinate of `m : ℤ × ℤ × ℤ` on the locus `nzCount m = 1`
(`Submission.Work.GM.Trace.Spart_defs`).  The point of this file is the trivial observation
that such an `m` is *determined* by the pair `(rho m, place of the non-zero coordinate)`, so
that a set of such `m` with `|rho m| ≤ X` injects into `[-X,X] ∩ ℤ` times a three-element
set.  Hence it has at most `3 (2X+1) ≤ 27 X³` elements for `X ≥ 1`.

This is the crude counting input used when the sum over the `nzCount = 1` locus is split
according to the size of `rho m ≈ |m|` (cf. `rho_sum_pow_le`).
-/

namespace Work.GM.Trace

open Submission.GM

/-- The place of the non-zero coordinate of `m`, encoded as `0` (first), `1` (second),
`2` (third); for `m = 0` it is `2`. -/
def rhoPos (m : ℤ × ℤ × ℤ) : Fin 3 :=
  if m.1 ≠ 0 then 0 else if m.2.1 ≠ 0 then 1 else 2

/-- On the locus `nzCount m = 1`, the pair `(rho m, rhoPos m)` determines `m`. -/
theorem rho_injOn_pair :
    Set.InjOn (fun m : ℤ × ℤ × ℤ => (rho m, rhoPos m)) {m | nzCount m = 1} := by
  intro m hm m' hm' heq
  have hrho : rho m = rho m' := congrArg Prod.fst heq
  have hpos : rhoPos m = rhoPos m' := congrArg Prod.snd heq
  rcases nzCount_one_cases m hm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [rho_of_ne_zero h1] at hrho
    rcases nzCount_one_cases m' hm' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
    · rw [rho_of_ne_zero g1] at hrho
      exact eq_of_nzCount_one_of_fst_eq hm hm' hrho h1
    · exfalso
      have hp1 : rhoPos m = 0 := by simp [rhoPos, h1]
      have hp2 : rhoPos m' = 1 := by simp [rhoPos, g1, g2]
      rw [hp1, hp2] at hpos
      exact absurd hpos (by decide)
    · exfalso
      have hp1 : rhoPos m = 0 := by simp [rhoPos, h1]
      have hp2 : rhoPos m' = 2 := by simp [rhoPos, g1, g2]
      rw [hp1, hp2] at hpos
      exact absurd hpos (by decide)
  · rw [rho_of_fst_eq_zero h1 h2] at hrho
    rcases nzCount_one_cases m' hm' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
    · exfalso
      have hp1 : rhoPos m = 1 := by simp [rhoPos, h1, h2]
      have hp2 : rhoPos m' = 0 := by simp [rhoPos, g1]
      rw [hp1, hp2] at hpos
      exact absurd hpos (by decide)
    · rw [rho_of_fst_eq_zero g1 g2] at hrho
      exact eq_of_nzCount_one_of_snd_eq hm hm' h1 hrho h2
    · exfalso
      have hp1 : rhoPos m = 1 := by simp [rhoPos, h1, h2]
      have hp2 : rhoPos m' = 2 := by simp [rhoPos, g1, g2]
      rw [hp1, hp2] at hpos
      exact absurd hpos (by decide)
  · rw [rho_of_fst_snd_eq_zero h1 h2] at hrho
    rcases nzCount_one_cases m' hm' with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
    · exfalso
      have hp1 : rhoPos m = 2 := by simp [rhoPos, h1, h2]
      have hp2 : rhoPos m' = 0 := by simp [rhoPos, g1]
      rw [hp1, hp2] at hpos
      exact absurd hpos (by decide)
    · exfalso
      have hp1 : rhoPos m = 2 := by simp [rhoPos, h1, h2]
      have hp2 : rhoPos m' = 1 := by simp [rhoPos, g1, g2]
      rw [hp1, hp2] at hpos
      exact absurd hpos (by decide)
    · rw [rho_of_fst_snd_eq_zero g1 g2] at hrho
      exact eq_of_nzCount_one_of_thd_eq hm hm' h1 h2 hrho

theorem rho_card_le (X : ℝ) (hX : 1 ≤ X) (s : Finset (ℤ × ℤ × ℤ))
    (hs : ∀ m ∈ s, Submission.GM.nzCount m = 1)
    (hXm : ∀ m ∈ s, |(Work.GM.Trace.rho m : ℝ)| ≤ X) :
    (s.card : ℝ) ≤ 27 * X ^ 3 := by
  -- The pair `(rho m, rhoPos m)` is injective on `s`, so `s` injects into `ℤ × Fin 3`.
  have hinj : Set.InjOn (fun m : ℤ × ℤ × ℤ => (rho m, rhoPos m)) ↑s := by
    intro m hm m' hm' h
    exact rho_injOn_pair (hs m hm) (hs m' hm') h
  have hcard : s.card = (s.image (fun m : ℤ × ℤ × ℤ => (rho m, rhoPos m))).card :=
    (Finset.card_image_of_injOn hinj).symm
  -- The image lies in the box `[-⌊X⌋, ⌊X⌋] × Fin 3`.
  have hsub : s.image (fun m : ℤ × ℤ × ℤ => (rho m, rhoPos m)) ⊆
      Finset.Icc (-⌊X⌋) ⌊X⌋ ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    have hmv := hXm m hm
    rw [Finset.mem_Icc]
    constructor
    · have hb : -X ≤ (rho m : ℝ) := (abs_le.mp hmv).1
      rw [← Int.ceil_neg]
      exact Int.ceil_le.mpr hb
    · have hb : (rho m : ℝ) ≤ X := (abs_le.mp hmv).2
      exact Int.le_floor.mpr hb
  have hcardle : (s.card : ℝ) ≤
      ((Finset.Icc (-⌊X⌋) ⌊X⌋ ×ˢ (Finset.univ : Finset (Fin 3))).card : ℝ) := by
    rw [hcard]
    exact_mod_cast Finset.card_le_card hsub
  have hsimp : ((Finset.Icc (-⌊X⌋) ⌊X⌋ ×ˢ (Finset.univ : Finset (Fin 3))).card : ℝ)
      = ((Finset.Icc (-⌊X⌋) ⌊X⌋).card : ℝ) * 3 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  -- The interval `[-⌊X⌋, ⌊X⌋] ∩ ℤ` has at most `2X+1` elements.
  have hbound : ((Finset.Icc (-⌊X⌋) ⌊X⌋).card : ℝ) ≤ 2 * X + 1 := by
    rw [Int.card_Icc]
    have hd : (0 : ℤ) ≤ ⌊X⌋ := Int.floor_nonneg.mpr (by linarith)
    have hnn : (0 : ℤ) ≤ ⌊X⌋ + 1 - -⌊X⌋ := by omega
    have hcast : (((⌊X⌋ + 1 - -⌊X⌋).toNat : ℕ) : ℝ) = 2 * (⌊X⌋ : ℝ) + 1 := by
      rw [show (((⌊X⌋ + 1 - -⌊X⌋).toNat : ℕ) : ℝ)
            = (((⌊X⌋ + 1 - -⌊X⌋ : ℤ)) : ℝ) from by
        exact_mod_cast (Int.toNat_of_nonneg hnn : ((⌊X⌋ + 1 - -⌊X⌋).toNat : ℤ) = _)]
      push_cast
      ring
    rw [hcast]
    have := Int.floor_le X
    linarith
  have harith : (2 * X + 1) * 3 ≤ 27 * X ^ 3 := by nlinarith [sq_nonneg X, hX]
  linarith [hcardle, hbound, harith]

end Work.GM.Trace
