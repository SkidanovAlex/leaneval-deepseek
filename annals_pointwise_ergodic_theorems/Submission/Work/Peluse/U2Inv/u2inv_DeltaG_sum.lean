/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.U2Inv.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The group sum of the weighted difference operator equals the interval sum

This module proves

`∑_{x ∈ ZMod (Gmod L)} Δ_{a,b} (pF L f) x = ∑_{x ∈ symIcc L} Δ_{a,b} f x`

for `f` supported in `[-L,L]` and `a, b ∈ symIcc (m-1)`, `m ≤ L`.

This is the step that lets the transported (group) object `gW`/`TT` of
`Submission/Work/Peluse/U2Inv/Defs.lean` be evaluated back on the interval `[-L,L]`: the only
nonzero contributions to the group sum come from the residues that have a representative in
`symIcc L`, and on those the zero extension `pF L f` agrees with `f`, the "wrap-around" being
ruled out by `Gmod L = 4L+1` being larger than `3L + L`.

## Main results

* `Work.Peluse.U2Inv.pF_cast_eq` : `pF L f (y : ZMod (Gmod L)) = f y` for `|y| ≤ 3L`;
* `Work.Peluse.U2Inv.DeltaG_pF_eq` : the pointwise identity of the two difference operators;
* `Work.Peluse.U2Inv.u2inv_DeltaG_sum` : the sum identity.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-! ## The arithmetic of `Gmod L = 4L+1` -/

/-- `symIcc L` is the set of integers of modulus at most `L`. -/
lemma u2inv_mem_symIcc_iff_abs {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ |x| ≤ (L : ℤ) :=
  mem_symIcc_iff.trans abs_le.symm

/-- If `c ∈ symIcc L`, `|y| ≤ 3L` and `c ≡ y (mod Gmod L)`, then `c = y`: the residue class mod
`Gmod L = 4L+1` of `y` meets `symIcc L` in at most one point, and only at `y` itself. -/
lemma u2inv_zmod_cast_eq_of_mem {L : ℕ} {c y : ℤ} (hc : c ∈ symIcc L)
    (hy : |y| ≤ 3 * (L : ℤ)) (h : (c : ZMod (Gmod L)) = (y : ZMod (Gmod L))) : c = y := by
  have hmod : c ≡ y [ZMOD (Gmod L)] := (ZMod.intCast_eq_intCast_iff c y (Gmod L)).mp h
  obtain ⟨k, hk⟩ := hmod.dvd
  have hN : (0 : ℤ) < (Gmod L : ℤ) := by simp [Gmod]
  have hc' : |c| ≤ (L : ℤ) := abs_le.mpr (mem_symIcc_iff.mp hc)
  have habs : |y - c| = (Gmod L : ℤ) * |k| := by
    rw [hk, abs_mul, abs_of_pos hN]
  have hle : (Gmod L : ℤ) * |k| < (Gmod L : ℤ) := by
    have h1 : |y - c| ≤ |y| + |c| := by
      rw [sub_eq_add_neg]
      calc |y + -c| ≤ |y| + |-c| := abs_add_le y (-c)
        _ = |y| + |c| := by rw [abs_neg]
    have h2 : (Gmod L : ℤ) = 4 * (L : ℤ) + 1 := by simp [Gmod]
    rw [← habs]
    linarith
  have hk1 : |k| < 1 := by nlinarith [abs_nonneg k]
  have hk0 : k = 0 := by
    rw [abs_lt] at hk1
    omega
  have hyc : y - c = 0 := by rw [hk0, mul_zero] at hk; exact hk
  omega

/-- The zero extension `pF L f` of a function supported in `[-L,L]` agrees with `f` at every
`y` with `|y| ≤ 3L`. -/
lemma pF_cast_eq {L : ℕ} {f : ℤ → ℂ} (hf : SupportIn f L) {y : ℤ}
    (hy : |y| ≤ 3 * (L : ℤ)) : pF L f (y : ZMod (Gmod L)) = f y := by
  have hiff : ∀ c ∈ symIcc L, ((c : ZMod (Gmod L)) = (y : ZMod (Gmod L))) ↔ c = y :=
    fun c hc => ⟨fun h => u2inv_zmod_cast_eq_of_mem hc hy h, fun h => by rw [h]⟩
  have hmain : pF L f (y : ZMod (Gmod L))
      = ∑ c ∈ symIcc L, (if c = y then f c else 0) := by
    simp only [pF]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [show (if (c : ZMod (Gmod L)) = (y : ZMod (Gmod L)) then f c else 0)
        = (if c = y then f c else 0) from if_congr (hiff c hc) rfl rfl]
  rw [hmain, Finset.sum_ite_eq' (symIcc L) y f]
  by_cases hyS : y ∈ symIcc L
  · rw [if_pos hyS]
  · rw [if_neg hyS]
    have hlt : (L : ℤ) < |y| := not_le.mp (fun h => hyS (u2inv_mem_symIcc_iff_abs.mpr h))
    have hnat : L < y.natAbs := by
      have hh := hlt
      rw [← Int.natCast_natAbs] at hh
      exact_mod_cast hh
    rw [hf y hnat]

/-! ## The pointwise identity of the difference operators -/

/-- On `x ∈ symIcc L`, the group difference operator applied to the transported function is the
interval difference operator applied to `f`. -/
lemma DeltaG_pF_eq {L m : ℕ} {f : ℤ → ℂ} (hf : SupportIn f L) (hm : m ≤ L)
    {a b : ℤ} (ha : a ∈ symIcc (m - 1)) (hb : b ∈ symIcc (m - 1)) {x : ℤ} (hx : x ∈ symIcc L) :
    DeltaG (a : ZMod (Gmod L)) (b : ZMod (Gmod L)) (pF L f) (x : ZMod (Gmod L))
      = DeltaZ a b f x := by
  have haL : |a| ≤ (L : ℤ) := by
    have h1 : |a| ≤ ((m - 1 : ℕ) : ℤ) := abs_le.mpr (mem_symIcc_iff.mp ha)
    have h2 : ((m - 1 : ℕ) : ℤ) ≤ (L : ℤ) := by
      have : m - 1 ≤ L := by omega
      exact_mod_cast this
    linarith
  have hbL : |b| ≤ (L : ℤ) := by
    have h1 : |b| ≤ ((m - 1 : ℕ) : ℤ) := abs_le.mpr (mem_symIcc_iff.mp hb)
    have h2 : ((m - 1 : ℕ) : ℤ) ≤ (L : ℤ) := by
      have : m - 1 ≤ L := by omega
      exact_mod_cast this
    linarith
  have hxL : |x| ≤ (L : ℤ) := abs_le.mpr (mem_symIcc_iff.mp hx)
  have h1 : |x + a| ≤ 3 * (L : ℤ) := by
    calc |x + a| ≤ |x| + |a| := abs_add_le x a
      _ ≤ (L : ℤ) + (L : ℤ) := by linarith
      _ ≤ 3 * (L : ℤ) := by linarith [Int.natCast_nonneg L]
  have h2 : |x + b| ≤ 3 * (L : ℤ) := by
    calc |x + b| ≤ |x| + |b| := abs_add_le x b
      _ ≤ (L : ℤ) + (L : ℤ) := by linarith
      _ ≤ 3 * (L : ℤ) := by linarith [Int.natCast_nonneg L]
  have h3 : |x + a + b| ≤ 3 * (L : ℤ) := by
    calc |x + a + b| ≤ |x + a| + |b| := abs_add_le (x + a) b
      _ ≤ (|x| + |a|) + |b| := by linarith [abs_add_le x a]
      _ ≤ 3 * (L : ℤ) := by linarith
  have e1 : (x : ZMod (Gmod L)) + (a : ZMod (Gmod L)) = ((x + a : ℤ) : ZMod (Gmod L)) := by
    push_cast; ring
  have e2 : (x : ZMod (Gmod L)) + (b : ZMod (Gmod L)) = ((x + b : ℤ) : ZMod (Gmod L)) := by
    push_cast; ring
  have e3 : (x : ZMod (Gmod L)) + (a : ZMod (Gmod L)) + (b : ZMod (Gmod L))
      = ((x + a + b : ℤ) : ZMod (Gmod L)) := by push_cast; ring
  have hxL' : |x| ≤ 3 * (L : ℤ) := by linarith [Int.natCast_nonneg L]
  simp only [DeltaG, DeltaZ]
  rw [e3, e1, e2, pF_cast_eq hf h1, pF_cast_eq hf h2, pF_cast_eq hf h3, pF_cast_eq hf hxL']

/-! ## The sum identity -/

theorem u2inv_DeltaG_sum (L m : ℕ) (f : ℤ → ℂ) (hf : Work.Peluse.SupportIn f L) (hm : m ≤ L)
    (a b : ℤ) (ha : a ∈ Work.Peluse.symIcc (m - 1)) (hb : b ∈ Work.Peluse.symIcc (m - 1)) :
    (∑ x : ZMod (Work.Peluse.U2Inv.Gmod L),
        Work.Peluse.U2Inv.DeltaG (a : ZMod (Work.Peluse.U2Inv.Gmod L))
          (b : ZMod (Work.Peluse.U2Inv.Gmod L)) (Work.Peluse.U2Inv.pF L f) x)
      = ∑ x ∈ Work.Peluse.symIcc L, Work.Peluse.U2Inv.DeltaZ a b f x := by
  have hzero : ∀ z : ZMod (Gmod L),
      z ∉ (symIcc L).image (fun y : ℤ => (y : ZMod (Gmod L))) → pF L f z = 0 := by
    intro z hz
    simp only [pF]
    refine Finset.sum_eq_zero (fun c hc => ?_)
    rw [if_neg]
    intro h
    exact hz (Finset.mem_image.mpr ⟨c, hc, h⟩)
  have hgzero : ∀ z : ZMod (Gmod L),
      z ∉ (symIcc L).image (fun y : ℤ => (y : ZMod (Gmod L))) →
      DeltaG (a : ZMod (Gmod L)) (b : ZMod (Gmod L)) (pF L f) z = 0 := by
    intro z hz
    simp only [DeltaG]
    rw [hzero z hz, mul_zero]
  have hpt : ∀ x ∈ symIcc L,
      DeltaG (a : ZMod (Gmod L)) (b : ZMod (Gmod L)) (pF L f) (x : ZMod (Gmod L))
        = DeltaZ a b f x := fun x hx => DeltaG_pF_eq hf hm ha hb hx
  calc (∑ x : ZMod (Gmod L),
          DeltaG (a : ZMod (Gmod L)) (b : ZMod (Gmod L)) (pF L f) x)
      = ∑ x ∈ (symIcc L).image (fun y : ℤ => (y : ZMod (Gmod L))),
          DeltaG (a : ZMod (Gmod L)) (b : ZMod (Gmod L)) (pF L f) x := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro x _ hx
        exact hgzero x hx
    _ = ∑ y ∈ symIcc L,
          DeltaG (a : ZMod (Gmod L)) (b : ZMod (Gmod L)) (pF L f) (y : ZMod (Gmod L)) := by
        refine Finset.sum_image ?_
        intro y hy z hz h
        exact u2inv_zmod_cast_eq_of_mem hy (by
          have : |z| ≤ (L : ℤ) := abs_le.mpr (mem_symIcc_iff.mp hz)
          linarith [Int.natCast_nonneg L]) h
    _ = ∑ x ∈ symIcc L, DeltaZ a b f x := Finset.sum_congr rfl hpt

end

end Work.Peluse.U2Inv
