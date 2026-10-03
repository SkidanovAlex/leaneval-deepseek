import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2.R6

/-- **Fibres of the reduction map `Z -> ZMod c` inside a bounded set are small.**

For `c >= 1`, any finite set `S : Finset ℤ` of integers of absolute value at most `Y`, and any
residue `r : ZMod c`, the elements of `S` congruent to `r` modulo `c` number at most `2Y/c + 1`:

  `(S.filter (fun h => (h : ZMod c) = r)).card <= 2*Y/c + 1`.

This is the elementary spacing fact behind the periodic count of the weighted primitive-pair sum:
two distinct elements of a fibre differ by a nonzero multiple of `c`, hence by at least `c`, and
`S` lies in `[-Y,Y]`.

`[NeZero c]` is the instance needed for `DecidableEq (ZMod c)`; `1 <= c` follows from it.
(Note the binder must be annotated, `fun (h : ℤ) => ...`, since `S : Finset ℤ`.)

PROOF ROUTE.  Let `T = S.filter (fun (h : ℤ) => (h : ZMod c) = r)`.  Prove first that distinct
`a b ∈ T` satisfy `c <= |a - b|`: from the filter, `(a : ZMod c) = (b : ZMod c)`, so
`a ≡ b [ZMOD (c : ℤ)]` by `ZMod.intCast_eq_intCast_iff`, so `(c : ℤ) ∣ a - b`; with `a ≠ b` this
gives `c <= |a - b|` as naturals.  Then, if `T ≠ ∅`, put `m = T.min' _` and `M = T.max' _`: the
elements lie in `[m, M]`, are pairwise at least `c` apart, so `M - m >= (T.card - 1) * c` (order
them increasingly and telescope, or use an injective strictly monotone enumeration into
`Finset.Icc 0 (T.card - 1)`), while `M - m <= 2 * Y` because `m, M ∈ [-Y, Y]` (expand
`Int.natAbs_le`).  Hence `(T.card - 1) * c <= 2 * Y`, i.e. `T.card <= 2 * Y / c + 1`.

An efficient finish is an injective map `T -> ℤ`, `h ↦ (h - m) / c` (integer division), whose
image lies in `Finset.Icc 0 (Nat.floor (2*Y/c))`; `Finset.card_le_card` and the cardinality of
`Finset.Icc` for `ℤ` then give the claim.  The case `c = 1` is sharp: `2*Y/1 + 1 = 2*Y + 1` is
exactly the cardinality of `Finset.Icc (-Y) Y`. -/
theorem fibre_card_le (Y c : ℕ) [NeZero c] (S : Finset ℤ) (hS : ∀ h ∈ S, h.natAbs ≤ Y)
    (r : ZMod c) :
    ((S.filter (fun (h : ℤ) => (h : ZMod c) = r)).card : ℝ) ≤ 2 * (Y : ℝ) / (c : ℝ) + 1 := by
  classical
  set T : Finset ℤ := S.filter (fun (h : ℤ) => (h : ZMod c) = r) with hT
  have hcpos_nat : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hcpos : (0:ℤ) < (c:ℤ) := by exact_mod_cast hcpos_nat
  have hmem : ∀ a : ℤ, a ∈ T ↔ a ∈ S ∧ (a : ZMod c) = r := by
    intro a; rw [hT]; exact Finset.mem_filter
  have hcong : ∀ a ∈ T, ∀ b ∈ T, (c:ℤ) ∣ a - b := by
    intro a ha b hb
    have ha' := (hmem a).mp ha
    have hb' := (hmem b).mp hb
    have h : (a : ZMod c) = (b : ZMod c) := by rw [ha'.2, hb'.2]
    rw [ZMod.intCast_eq_intCast_iff] at h
    have hd : (c:ℤ) ∣ -(a - b) := by
      rw [neg_sub]; exact h.dvd
    exact dvd_neg.mp hd
  have hbdd : ∀ h ∈ T, -(Y:ℤ) ≤ h ∧ h ≤ (Y:ℤ) := by
    intro h hh
    have hhS : h ∈ S := (hmem h).mp hh |>.1
    have h2 : |h| ≤ ((Y:ℤ)) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hS h hhS
    exact abs_le.mp h2
  rcases Finset.eq_empty_or_nonempty T with hemp | hne
  · rw [hemp]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  · set m : ℤ := T.min' hne with hm
    set M : ℤ := T.max' hne with hM
    have hmT : m ∈ T := Finset.min'_mem T hne
    have hMT : M ∈ T := Finset.max'_mem T hne
    have hm_lb : -(Y:ℤ) ≤ m := (hbdd m hmT).1
    have hM_ub : M ≤ (Y:ℤ) := (hbdd M hMT).2
    have hmM : m ≤ M := by rw [hm]; exact Finset.min'_le T M hMT
    have hMm : M - m ≤ 2 * (Y:ℤ) := by linarith
    have hxnonneg : 0 ≤ (M - m) / (c:ℤ) := Int.ediv_nonneg (by linarith) (le_of_lt hcpos)
    have hinj : Set.InjOn (fun h : ℤ => (h - m) / (c:ℤ)) ↑T := by
      intro a ha b hb hab
      have hab' : (a - m) / (c:ℤ) = (b - m) / (c:ℤ) := hab
      have ha' : (c:ℤ) ∣ a - m := hcong a ha m hmT
      have hb' : (c:ℤ) ∣ b - m := hcong b hb m hmT
      have h1 := Int.ediv_mul_cancel ha'
      have h2 := Int.ediv_mul_cancel hb'
      rw [hab'] at h1
      linarith
    have hrange : ∀ h ∈ T, (h - m) / (c:ℤ) ∈ Finset.Icc (0:ℤ) ((M-m)/(c:ℤ)) := by
      intro h hh
      rw [Finset.mem_Icc]
      have hmle : m ≤ h := by
        rw [hm]; exact Finset.min'_le T h hh
      have hleM : h ≤ M := by
        rw [hM]; exact Finset.le_max' T h hh
      exact ⟨Int.ediv_nonneg (by linarith) (le_of_lt hcpos), Int.ediv_le_ediv hcpos (by linarith)⟩
    have himg : T.image (fun h : ℤ => (h - m) / (c:ℤ)) ⊆ Finset.Icc (0:ℤ) ((M-m)/(c:ℤ)) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      exact hrange h hh
    have hcard1 : T.card = (T.image (fun h : ℤ => (h - m) / (c:ℤ))).card :=
      (Finset.card_image_of_injOn hinj).symm
    have hcard2 : (T.image (fun h : ℤ => (h - m) / (c:ℤ))).card
        ≤ (Finset.Icc (0:ℤ) ((M-m)/(c:ℤ))).card :=
      Finset.card_le_card himg
    have hval : (Finset.Icc (0:ℤ) ((M-m)/(c:ℤ))).card = ((M-m)/(c:ℤ)).toNat + 1 := by
      rw [Int.card_Icc, sub_zero, Int.toNat_add hxnonneg (by norm_num)]
      norm_num
    have hstep : ((M-m)/(c:ℤ)).toNat ≤ 2 * Y / c := by
      have h1 : (M - m) / (c:ℤ) ≤ (2 * (Y:ℤ)) / (c:ℤ) := Int.ediv_le_ediv hcpos hMm
      have h2 : (2 * (Y:ℤ)) / (c:ℤ) = ((2 * Y / c : ℕ) : ℤ) := by
        rw [show (2 * (Y:ℤ)) = ((2*Y : ℕ) : ℤ) by push_cast; ring, ← Int.natCast_ediv]
      calc ((M-m)/(c:ℤ)).toNat ≤ ((2 * (Y:ℤ)) / (c:ℤ)).toNat := Int.toNat_le_toNat h1
        _ = (2 * Y / c) := by rw [h2, Int.toNat_natCast]
    have hbound : T.card ≤ 2 * Y / c + 1 := by
      calc T.card = (T.image (fun h : ℤ => (h - m) / (c:ℤ))).card := hcard1
        _ ≤ (Finset.Icc (0:ℤ) ((M-m)/(c:ℤ))).card := hcard2
        _ = ((M-m)/(c:ℤ)).toNat + 1 := hval
        _ ≤ 2 * Y / c + 1 := by omega
    have hcast : ((2 * Y / c + 1 : ℕ) : ℝ) ≤ 2 * (Y:ℝ) / (c:ℝ) + 1 := by
      have h1 : ((2 * Y / c : ℕ) : ℝ) ≤ 2 * (Y:ℝ) / (c:ℝ) := by
        calc ((2 * Y / c : ℕ) : ℝ) ≤ ((2*Y : ℕ) : ℝ) / (c:ℝ) := Nat.cast_div_le
          _ = 2 * (Y:ℝ) / (c:ℝ) := by push_cast; ring
      have h2 : ((2 * Y / c + 1 : ℕ) : ℝ) = ((2*Y/c : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [h2]; linarith
    calc ((T.card : ℕ) : ℝ) ≤ ((2 * Y / c + 1 : ℕ) : ℝ) := by exact_mod_cast hbound
      _ ≤ 2 * (Y:ℝ) / (c:ℝ) + 1 := hcast

end Work.FIArea2.R6
