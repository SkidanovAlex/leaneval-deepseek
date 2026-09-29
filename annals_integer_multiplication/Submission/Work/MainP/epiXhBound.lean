import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtLabSum
import Submission.Work.MainP.crtMath

/-!
# The accumulator history is small

The CRT label word accumulates its history in the value
`acc ss i = cons (prp (vlab ss (i-1)) (Est ss i)) (ofList (Xh ss i))`: the current pair
`(last label, current state)` consed onto the list `Xh ss i` of all earlier pairs.

For the epilogue of the word (reading the labels off the history) one needs two size facts about
every element of the list `prp (vlab ss (S-1)) (Est ss S) :: Xh ss S`:

* every element is a pair `prp v E`, and the label fits in `S` in the sense `vsz (int v) ≤ S.size + 2`
  (`S = ss.prod` bounds every label `crtIdx ss j`);
* every element has size `≤ (3 · #ss + 4) · (S.size + 2) + 4 · #ss + 6` (each state entry has size
  `≤ 3 · (S.size + 2) + 3`, and a state has `#ss` entries).

Both follow from `Work.MainP.crtLabSum` (`estVszLe`, the label bound) and the membership
characterisation of `Xh` proved below.
-/

namespace Work.MainP

set_option autoImplicit false

open HvdH

/-- Membership in the history list: the entries of `Xh ss S` are the pairs
`prp (vlab ss (i-1)) (Est ss i)` for `i < S`. -/
theorem mem_Xh (ss : List ℕ) (S : ℕ) {x : Val} :
    x ∈ Xh ss S ↔ ∃ i, i < S ∧ x = prp (vlab ss (i - 1)) (Est ss i) := by
  induction S with
  | zero => simp [Xh]
  | succ S ih =>
      rw [Xh_succ, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨i, hi, hx⟩)
        · exact ⟨S, Nat.lt_succ_self S, h⟩
        · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
      · rintro ⟨i, hi, hx⟩
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | rfl
        · exact Or.inr ⟨i, hi, hx⟩
        · exact Or.inl hx

/-- The size of a pair `prp v E`. -/
theorem vsz_prp (v : ℤ) (E : List Val) :
    vsz (prp v E) = isz v + (E.map vsz).sum + E.length + 2 := by
  rw [prp, vsz_cons, vsz_int, vsz_ofList]
  ring

/-- Every label `vlab ss i` fits in `S = ss.prod`, hence has `isz ≤ S.size + 2`. -/
private theorem isz_vlab_le {ss : List ℕ} {S : ℕ} (hS : S = ss.prod)
    (hpos : ∀ s ∈ ss, 1 ≤ s) (i : ℕ) : HvdH.isz (vlab ss i) ≤ S.size + 2 := by
  have hlt : crtIdx ss i < ss.prod :=
    crtIdx_lt (fun s hs => lt_of_lt_of_le Nat.zero_lt_one (hpos s hs)) i
  rw [vlab, isz_natCast, iszN]
  exact Nat.add_le_add_right (Nat.size_le_size (by rw [hS]; exact le_of_lt hlt)) 2

/-- The size bound for an entry of the history. -/
theorem prp_vsz_le {ss : List ℕ} {S : ℕ} (hS : S = ss.prod)
    (hpos : ∀ s ∈ ss, 1 ≤ s) (i : ℕ) :
    vsz (prp (vlab ss (i - 1)) (Est ss i)) ≤
      (3 * ss.length + 4) * (S.size + 2) + 4 * ss.length + 6 := by
  rw [vsz_prp]
  have hisz : HvdH.isz (vlab ss (i - 1)) ≤ S.size + 2 := isz_vlab_le hS hpos (i - 1)
  have hsum : ((Est ss i).map vsz).sum ≤ ss.length * (3 * (S.size + 2) + 3) := by
    have hle := List.sum_le_sum (l := Est ss i) (f := HvdH.vsz)
      (g := fun _ : Val => 3 * (S.size + 2) + 3) (fun x hx => estVszLe hS hpos i x hx)
    rw [List.map_const', List.sum_const_nat] at hle
    simpa [Est_length] using hle
  have hlen : (Est ss i).length = ss.length := Est_length ss i
  nlinarith [hisz, hsum, hlen]

theorem epiXhBound (ss : List ℕ) (S : ℕ) (hpos : ∀ s ∈ ss, 1 ≤ s) (hS : S = ss.prod) :
    ∀ x ∈ Work.MainP.prp (Work.MainP.vlab ss (S-1)) (Work.MainP.Est ss S) :: Work.MainP.Xh ss S,
      (∃ (v : ℤ) (E : List HvdH.Val), x = Work.MainP.prp v E ∧ HvdH.vsz (HvdH.Val.int v) ≤ S.size + 2) ∧
      HvdH.vsz x ≤ (3 * ss.length + 4) * (S.size + 2) + 4 * ss.length + 6 := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · refine ⟨⟨vlab ss (S - 1), Est ss S, h, ?_⟩, ?_⟩
    · rw [vsz_int]; exact isz_vlab_le hS hpos (S - 1)
    · rw [h]; exact prp_vsz_le hS hpos S
  · obtain ⟨i, -, hxi⟩ := (mem_Xh ss S).mp h
    refine ⟨⟨vlab ss (i - 1), Est ss i, hxi, ?_⟩, ?_⟩
    · rw [vsz_int]; exact isz_vlab_le hS hpos (i - 1)
    · rw [hxi]; exact prp_vsz_le hS hpos i

end Work.MainP
