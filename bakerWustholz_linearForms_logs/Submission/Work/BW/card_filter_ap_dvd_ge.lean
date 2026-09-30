import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Counting lemma: if `q` is coprime to `r > 0`, then among the indices `j < n` the
number of `j` with `r ∣ x - j * q` is at least `n / r`. Indeed those `j` form a single
residue class modulo `r`. -/
lemma card_filter_dvd_ge_aux (r n q : ℕ) (x : ℤ) (hr : 0 < r) (hcop : Nat.Coprime q r) :
    n / r ≤ ((Finset.range n).filter (fun (j : ℕ) => (r : ℤ) ∣ x - (j:ℤ)*(q:ℤ))).card := by
  have hne : NeZero r := ⟨Nat.pos_iff_ne_zero.mp hr⟩
  -- There is a residue `j0 < r` with `r ∣ x - j0 * q`: `q` is invertible mod `r`.
  have hex : ∃ j0 : ℕ, j0 < r ∧ (r:ℤ) ∣ x - (j0:ℤ)*(q:ℤ) := by
    let u : (ZMod r)ˣ := ZMod.unitOfCoprime q hcop
    refine ⟨((x : ZMod r) * ↑(u⁻¹)).val, ZMod.val_lt _, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    have huval : (↑u : ZMod r) = (q : ZMod r) := ZMod.coe_unitOfCoprime q hcop
    rw [← huval]
    rw [mul_assoc, Units.inv_mul, mul_one, sub_self]
  obtain ⟨j0, hj0lt, hj0dvd⟩ := hex
  -- The map `k ↦ k * r + j0` injects `range (n/r)` into the good set.
  let f : ℕ → ℕ := fun k => k * r + j0
  have hfmem : ∀ k ∈ Finset.range (n / r),
      f k ∈ (Finset.range n).filter (fun (j : ℕ) => (r : ℤ) ∣ x - (j:ℤ)*(q:ℤ)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_range, f]
    refine ⟨?_, ?_⟩
    · have hk1 : k + 1 ≤ n / r := Nat.succ_le_of_lt hk
      have hle1 : (k+1) * r ≤ (n / r) * r := Nat.mul_le_mul_right _ hk1
      have hle2 : (n / r) * r ≤ n := by
        rw [mul_comm]
        calc r * (n / r) ≤ r * (n / r) + n % r := Nat.le_add_right _ _
          _ = n := Nat.div_add_mod n r
      calc k * r + j0 < k * r + r := Nat.add_lt_add_left hj0lt _
        _ = (k+1) * r := by ring
        _ ≤ (n/r) * r := hle1
        _ ≤ n := hle2
    · have hB : (r:ℤ) ∣ (k:ℤ)*(r:ℤ)*(q:ℤ) := ⟨(k:ℤ)*(q:ℤ), by ring⟩
      have hcomb := hj0dvd.sub hB
      convert hcomb using 1
      push_cast
      ring
  have hfinj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    exact Nat.mul_right_cancel hr (Nat.add_right_cancel hab)
  calc n / r = (Finset.range (n / r)).card := (Finset.card_range _).symm
    _ = (Finset.image f (Finset.range (n / r))).card := (Finset.card_image_of_injective _ hfinj).symm
    _ ≤ _ := Finset.card_le_card (Finset.image_subset_iff.mpr hfmem)

/-- If `p` is prime, `m ≥ 1`, and `p ∤ q`, then among the indices `j < n` at least `n / p ^ m`
of them satisfy `p ^ m ∣ x - j * q` (they form one residue class mod `p ^ m`). -/
theorem card_filter_ap_dvd_ge (p m n q : ℕ) (x : ℤ) (hp : p.Prime) (hm : 1 ≤ m) (hq : ¬ p ∣ q) :
    n / p ^ m ≤
      ((Finset.range n).filter (fun (j : ℕ) => ((p : ℤ) ^ m) ∣ x - (j : ℤ) * (q : ℤ))).card := by
  have _hm := hm
  have hrpos : 0 < p ^ m := pow_pos hp.pos m
  have hcop : Nat.Coprime q (p ^ m) := (hp.coprime_iff_not_dvd.mpr hq).symm.pow_right m
  rw [show ((p : ℤ) ^ m) = ((p ^ m : ℕ) : ℤ) from (Nat.cast_pow (α := ℤ) p m).symm]
  exact card_filter_dvd_ge_aux (p^m) n q x hrpos hcop

end Work.BW
