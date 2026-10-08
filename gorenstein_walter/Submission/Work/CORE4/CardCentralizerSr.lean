import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.L2F.Dihedral.centralizer_sr_subset

namespace Work.CORE4

/-- For `2 ≤ n`, the residue `n / 2` is a nonzero element of `ZMod n`. -/
lemma half_cast_ne_zero {n : ℕ} (hn : 2 ≤ n) : ((n / 2 : ℕ) : ZMod n) ≠ 0 := by
  intro hzero
  have hdiv : n ∣ n / 2 := (ZMod.natCast_eq_zero_iff (n / 2) n).mp hzero
  have hpos : 0 < n / 2 := by omega
  have hlt : n / 2 < n := by omega
  exact Nat.not_dvd_of_pos_of_lt hpos hlt hdiv

/-- For even `n`, the residue `n / 2` is an element of order (at most) two in `ZMod n`:
it is its own negative. -/
lemma half_cast_add_self {n : ℕ} (hnEven : Even n) :
    ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
  rw [← Nat.cast_add]
  have h : n / 2 + n / 2 = n := by
    have := Nat.two_mul_div_two_of_even hnEven
    omega
  rw [h, ZMod.natCast_self]

/-- **The centralizer of a reflection in a dihedral group of even order is a four-group.**

For `n ≥ 2` even and `i : ZMod n`, the centralizer of the reflection `sr i` in `DihedralGroup n`
is `{1, r (n/2), sr i, sr (i + n/2)}`, hence has `4` elements.

Route: `Work.L2F.Dihedral.centralizer_sr_subset` gives `⊆` the four-element set; the reverse
inclusion is the commutation check `r (n/2) * sr i = sr i * r (n/2)` (which uses
`(n/2) + (n/2) = 0` in `ZMod n`, i.e. `Even n`) together with
`sr i * sr (i + n/2) = sr (i + n/2) * sr i`; then count, e.g. via `Nat.card_coe_set_eq` and
`Set.ncard_insert_of_notMem` (the four elements are distinct because `((n / 2 : ℕ) : ZMod n) ≠ 0`
when `2 ≤ n`).  Note `n = 2` is included (`DihedralGroup 2` is the Klein four group). -/
theorem CardCentralizerSr {n : ℕ} (hn : 2 ≤ n) (hnEven : Even n) (i : ZMod n) :
    Nat.card ↥(Subgroup.centralizer ({DihedralGroup.sr i} : Set (DihedralGroup n))) = 4 := by
  -- Abbreviate the half-rotation `n / 2` as an element of `ZMod n`.
  set h : ZMod n := ((n / 2 : ℕ) : ZMod n) with hh
  have h2 : h + h = 0 := by
    rw [hh]
    exact half_cast_add_self hnEven
  have hne : h ≠ 0 := by
    rw [hh]
    exact half_cast_ne_zero hn
  have hneg : h = -h := (eq_neg_iff_add_eq_zero).mpr h2
  -- The centralizer is exactly the four-element set `{1, r h, sr i, sr (i + h)}`.
  have hset :
      (Subgroup.centralizer ({DihedralGroup.sr i} : Set (DihedralGroup n)) : Set (DihedralGroup n))
        = ({1, DihedralGroup.r h, DihedralGroup.sr i, DihedralGroup.sr (i + h)} :
            Set (DihedralGroup n)) := by
    apply Set.Subset.antisymm
    · -- `⊆`: this is `Work.L2F.Dihedral.centralizer_sr_subset`, rewritten via `← hh`.
      intro x hx
      have hx' := Work.L2F.Dihedral.centralizer_sr_subset (m := n) (i := i) hx
      rw [← hh] at hx'
      exact hx'
    · -- `⊇`: each of the four elements commutes with `sr i`.
      intro x hx
      change x ∈ Subgroup.centralizer ({DihedralGroup.sr i} : Set (DihedralGroup n))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp
      · -- `x = r h`: use `sr i * r h = sr (i + h)` and `r h * sr i = sr (i - h)` together
        -- with `h = -h`.
        rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq, sub_eq_add_neg,
          add_left_cancel_iff]
        exact hneg
      · simp
      · -- `x = sr (i + h)`: `sr i * sr (i + h) = r h` and `sr (i + h) * sr i = r h`.
        simp only [DihedralGroup.sr_mul_sr]
        rw [DihedralGroup.r.injEq, add_sub_cancel_left, sub_add_eq_sub_sub, sub_self, zero_sub]
        exact hneg
  -- Count: the four displayed elements are distinct.
  show Nat.card
      (↥ (Subgroup.centralizer ({DihedralGroup.sr i} : Set (DihedralGroup n)) :
          Set (DihedralGroup n))) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_eq_four]
  refine ⟨1, DihedralGroup.r h, DihedralGroup.sr i, DihedralGroup.sr (i + h),
    ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · -- `1 ≠ r h`
    intro heq
    apply hne
    have h0 : (0 : ZMod n) = h := by
      rw [DihedralGroup.one_def] at heq
      exact DihedralGroup.r.inj heq
    exact h0.symm
  · -- `1 ≠ sr i`
    intro heq
    exact Work.Dihedral.sr_ne_r i 0 (by rw [← heq, DihedralGroup.one_def])
  · -- `1 ≠ sr (i + h)`
    intro heq
    exact Work.Dihedral.sr_ne_r (i + h) 0 (by rw [← heq, DihedralGroup.one_def])
  · -- `r h ≠ sr i`
    exact (Work.Dihedral.sr_ne_r i h).symm
  · -- `r h ≠ sr (i + h)`
    exact (Work.Dihedral.sr_ne_r (i + h) h).symm
  · -- `sr i ≠ sr (i + h)` because `h ≠ 0`
    intro heq
    apply hne
    have h' : i + h = i + (0 : ZMod n) := by
      rw [add_zero]
      exact (DihedralGroup.sr.inj heq).symm
    exact add_left_cancel_iff.mp h'

end Work.CORE4
