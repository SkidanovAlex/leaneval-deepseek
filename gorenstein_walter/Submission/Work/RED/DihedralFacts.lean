import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.Dihedral.Defs

/-!
# `DihedralGroup` facts needed by RED

This file discharges `Work.RED.GW2.DihedralFactsProp`: the four elementary facts about
`DihedralGroup n` (`n ≠ 0`) that the non-simple step of Gorenstein–Walter (Bender's analysis)
uses.

* `elementary_abelian_card_le_four`: `DihedralGroup n` has 2-rank at most `2`, i.e. a subgroup all
  of whose elements are involutions has at most `4` elements.
* `normal_fourGroup_centralizer`: a normal four-group is self-centralizing.
* `fourGroup_exists_of_even`: for even `n` there is a Klein four-subgroup.
* `involution_ne_of_central`: a central involution is never the only involution (`n ≥ 2`).

The proofs are elementary computations with the normal form `r i` / `sr i` of
`DihedralGroup` (multiplication rules `r i * r j = r (i+j)`, `r i * sr j = sr (j-i)`,
`sr i * r j = sr (i+j)`, `sr i * sr j = r (j-i)`) and with the rotation subgroup
`Work.Dihedral.rot n = ⟨r⟩`, which is cyclic of index two.

The single number-theoretic input is that `2 * a = 0` in `ZMod n` has at most the two solutions
`a = 0` and `a = n/2`; this is Mathlib's `ZMod.neg_eq_self_iff` plus `Nat` arithmetic.
-/

namespace Work.RED

open DihedralGroup

/-! ## The rotation subgroup -/

/-- The involutions of the rotation subgroup `⟨r⟩ ≤ DihedralGroup n` are the identity and the
"central" rotation `r (n/2)` (which is an involution only when `n` is even; the statement is
uniform in `n`). -/
private theorem rot_sq_eq_one (n : ℕ) [NeZero n] {x : DihedralGroup n}
    (hx : x ∈ Work.Dihedral.rot n) (hx2 : x ^ 2 = 1) :
    x = 1 ∨ x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
  obtain ⟨i, rfl⟩ := Work.Dihedral.mem_rot.mp hx
  have h2i : 2 * i = 0 := by
    have h : (DihedralGroup.r i : DihedralGroup n) ^ 2 = DihedralGroup.r (0 : ZMod n) := by
      rw [hx2, DihedralGroup.r_zero]
    rw [DihedralGroup.r_pow] at h
    have h' : i * 2 = 0 := DihedralGroup.r.inj h
    simpa [mul_comm] using h'
  have hsum : i + i = 0 := by simpa [two_mul] using h2i
  have hneg : -i = i := (neg_eq_iff_add_eq_zero).mpr hsum
  rcases (ZMod.neg_eq_self_iff i).mp hneg with h | h
  · exact Or.inl (by rw [h, DihedralGroup.r_zero])
  · refine Or.inr ?_
    have hval : i.val = n / 2 := by omega
    rw [← ZMod.natCast_zmod_val i, hval]

/-- The solutions of `2 * a = 0` in `ZMod n` are among `0` and `n/2`. -/
private theorem zmod_two_mul_eq_zero (n : ℕ) [NeZero n] (a : ZMod n) (ha : 2 * a = 0) :
    a = 0 ∨ a = ((n / 2 : ℕ) : ZMod n) := by
  have ha' : a + a = 0 := by simpa [two_mul] using ha
  have hsq : (DihedralGroup.r a : DihedralGroup n) ^ 2 = 1 := by
    have h : DihedralGroup.r (a + a) = 1 := by rw [ha', DihedralGroup.r_zero]
    simpa [pow_two, DihedralGroup.r_mul_r] using h
  rcases rot_sq_eq_one n (Work.Dihedral.r_mem_rot a) hsq with h | h
  · exact Or.inl (DihedralGroup.r.inj (by simpa using h))
  · exact Or.inr (DihedralGroup.r.inj h)

/-! ## Set-cardinality helpers -/

private theorem ncard_pair_le {α : Type*} (a b : α) : ({a, b} : Set α).ncard ≤ 2 := by
  have h := Set.ncard_insert_le a ({b} : Set α)
  simp only [Set.ncard_singleton] at h
  linarith

private theorem ncard_four_le {α : Type*} (p a b c : α) :
    ({p, a, b, c} : Set α).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le p ({a, b, c} : Set α)
  have h2 := Set.ncard_insert_le a ({b, c} : Set α)
  have h3 := Set.ncard_insert_le b ({(c)} : Set α)
  simp only [Set.ncard_singleton] at h3
  linarith

private theorem ncard_four_eq {α : Type*} (p a b c : α) (hp : p ≠ a) (hp' : p ≠ b)
    (hp'' : p ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({p, a, b, c} : Set α).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hp, hp', hp''⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hab, hac⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_singleton_iff]
        exact hbc),
      Set.ncard_singleton]

/-! ## 2-rank: subgroups of exponent two have at most four elements -/

/-- A subgroup of `DihedralGroup n` all of whose elements are involutions is contained either in
the rotation subgroup `⟨r⟩` (and then in `{1, r (n/2)}`), or in one of the four-groups
`{1, r (n/2), sr i, sr (i - n/2)}`. -/
private theorem sq_one_subset (n : ℕ) [NeZero n] (E : Subgroup (DihedralGroup n))
    (hE : ∀ x ∈ E, x ^ 2 = 1) :
    (E ≤ Work.Dihedral.rot n ∧ ∀ x ∈ E, x = 1 ∨ x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) ∨
      ∃ i : ZMod n, ∀ x ∈ E, x = 1 ∨ x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) ∨
        x = DihedralGroup.sr i ∨ x = DihedralGroup.sr (i - ((n / 2 : ℕ) : ZMod n)) := by
  by_cases hrot : E ≤ Work.Dihedral.rot n
  · exact Or.inl ⟨hrot, fun x hx => rot_sq_eq_one n (hrot hx) (hE x hx)⟩
  · right
    obtain ⟨s, hsE, hsR⟩ : ∃ s ∈ E, s ∉ Work.Dihedral.rot n := by
      by_contra h
      exact hrot fun x hx => by
        by_contra hx'
        exact h ⟨x, hx, hx'⟩
    obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hsR
    refine ⟨i, fun x hx => ?_⟩
    by_cases hxr : x ∈ Work.Dihedral.rot n
    · rcases rot_sq_eq_one n hxr (hE x hx) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · obtain ⟨j, rfl⟩ := Work.Dihedral.notMem_rot.mp hxr
      have hyE : DihedralGroup.sr j * DihedralGroup.sr i ∈ E := E.mul_mem hx hsE
      have hyrot : DihedralGroup.sr j * DihedralGroup.sr i ∈ Work.Dihedral.rot n := by
        rw [DihedralGroup.sr_mul_sr]; exact Work.Dihedral.r_mem_rot _
      have hy2 : (DihedralGroup.sr j * DihedralGroup.sr i) ^ 2 = 1 := hE _ hyE
      rcases rot_sq_eq_one n hyrot hy2 with h | h
      · have h0 : DihedralGroup.r (i - j) = DihedralGroup.r (0 : ZMod n) := by
          simpa [DihedralGroup.sr_mul_sr, DihedralGroup.r_zero] using h
        have hij : i - j = 0 := DihedralGroup.r.inj h0
        have hji : j = i := (sub_eq_zero.mp hij).symm
        right; right; left
        rw [hji]
      · have h0 : DihedralGroup.r (i - j) = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
          simpa [DihedralGroup.sr_mul_sr] using h
        have hij : i - j = ((n / 2 : ℕ) : ZMod n) := DihedralGroup.r.inj h0
        have hji : j = i - ((n / 2 : ℕ) : ZMod n) := by
          rw [← hij]; ring
        right; right; right
        rw [hji]

private theorem card_le_four (n : ℕ) [NeZero n] (E : Subgroup (DihedralGroup n))
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  rcases sq_one_subset n E hE with ⟨hrot, hsub⟩ | ⟨i, hsub⟩
  · have hsub' : (E : Set (DihedralGroup n)) ⊆
        ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n)} : Set (DihedralGroup n)) :=
      fun x hx => hsub x hx
    calc Nat.card E = (E : Set (DihedralGroup n)).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n)} : Set (DihedralGroup n)).ncard :=
          Set.ncard_le_ncard hsub'
      _ ≤ 2 := ncard_pair_le _ _
      _ ≤ 4 := by norm_num
  · have hsub' : (E : Set (DihedralGroup n)) ⊆
        ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n), DihedralGroup.sr i,
          DihedralGroup.sr (i - ((n / 2 : ℕ) : ZMod n))} : Set (DihedralGroup n)) :=
      fun x hx => hsub x hx
    calc Nat.card E = (E : Set (DihedralGroup n)).ncard := Nat.card_coe_set_eq _
      _ ≤ _ := Set.ncard_le_ncard hsub'
      _ ≤ 4 := ncard_four_le _ _ _ _

/-! ## The central involution of a four-group -/

/-- A normal four-subgroup of `DihedralGroup n` contains the "central" rotation `r (n/2)`.

(For `n = 2` the whole group is the four-group, so this is immediate; otherwise conjugate the
chosen reflection `sr i ∈ V` by `r 1`; the product `sr i * (sr i)^{r 1} = r (-2)` lies in `V`,
and since it is a rotation of order `≤ 2` it is either `1` — which forces `n ∣ 2`, i.e. `n = 2` —
or `r (n/2)`.) -/
private theorem centerElem_mem_of_normal_fourGroup (n : ℕ) [NeZero n]
    (V : Subgroup (DihedralGroup n)) (hVn : V.Normal) (hV4 : Work.RED.GW2.IsFourGroup V) :
    DihedralGroup.r ((n / 2 : ℕ) : ZMod n) ∈ V := by
  have hcard : Nat.card V = 4 := hV4.1
  have hcardset : (V : Set (DihedralGroup n)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq (V : Set (DihedralGroup n))]
    exact hcard
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := hV4.2
  have hdvd : 4 ∣ 2 * n := by
    have := Subgroup.card_subgroup_dvd_card V
    rwa [hcard, DihedralGroup.nat_card] at this
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hdvd
    have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  -- `V` contains a reflection
  have hnotrot : ¬ V ≤ Work.Dihedral.rot n := by
    intro hle
    have hsub : (V : Set (DihedralGroup n)) ⊆
        ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n)} : Set (DihedralGroup n)) :=
      fun x hx => rot_sq_eq_one n (hle hx) (hsq x hx)
    have hle2 : (V : Set (DihedralGroup n)).ncard ≤ 2 :=
      le_trans (Set.ncard_le_ncard hsub) (ncard_pair_le _ _)
    omega
  obtain ⟨s, hsV, hsR⟩ : ∃ s ∈ V, s ∉ Work.Dihedral.rot n := by
    by_contra h
    exact hnotrot fun x hx => by
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
  obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hsR
  by_cases hn2' : n = 2
  · have htop : V = ⊤ := by
      refine Subgroup.eq_top_of_card_eq V ?_
      rw [hcard, DihedralGroup.nat_card, hn2']
    rw [htop]
    exact Subgroup.mem_top _
  · have hconj : DihedralGroup.r 1 * DihedralGroup.sr i * (DihedralGroup.r 1)⁻¹ ∈ V :=
      hVn.conj_mem _ hsV (DihedralGroup.r 1)
    have hQ : DihedralGroup.sr i *
        (DihedralGroup.r 1 * DihedralGroup.sr i * (DihedralGroup.r 1)⁻¹) ∈ V :=
      V.mul_mem hsV hconj
    have hconj' : DihedralGroup.r 1 * DihedralGroup.sr i * (DihedralGroup.r 1)⁻¹
        = DihedralGroup.sr (i - 2 * 1) := Work.Dihedral.r_conj_sr 1 i
    rw [hconj', DihedralGroup.sr_mul_sr] at hQ
    have hQ' : DihedralGroup.r (-(2 : ZMod n)) ∈ V := by
      have heq : (i - 2 * 1 : ZMod n) - i = -(2 : ZMod n) := by ring
      rwa [heq] at hQ
    have hsqQ : (DihedralGroup.r (-(2 : ZMod n))) ^ 2 = 1 := hsq _ hQ'
    rcases rot_sq_eq_one n (Work.Dihedral.r_mem_rot _) hsqQ with h | h
    · exfalso
      have h2 : ((2 : ℕ) : ZMod n) = 0 := by
        have hz : -(2 : ZMod n) = 0 := DihedralGroup.r.inj (by simpa using h)
        simpa using neg_eq_zero.mp hz
      have hdvd2 : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp h2
      have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
      exact hn2' (le_antisymm hle hn2)
    · rw [← h]; exact hQ'

/-! ## Normal four-groups are self-centralizing -/

/-- A normal four-subgroup of `DihedralGroup n` is its own centralizer. -/
private theorem centralizer_eq_of_fourGroup (n : ℕ) [NeZero n] (V : Subgroup (DihedralGroup n))
    (hVn : V.Normal) (hV4 : Work.RED.GW2.IsFourGroup V) :
    Subgroup.centralizer (V : Set (DihedralGroup n)) = V := by
  have hcard : Nat.card V = 4 := hV4.1
  have hcardset : (V : Set (DihedralGroup n)).ncard = 4 := by
    rw [← Nat.card_coe_set_eq (V : Set (DihedralGroup n))]
    exact hcard
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := hV4.2
  -- a reflection in `V`
  have hnotrot : ¬ V ≤ Work.Dihedral.rot n := by
    intro hle
    have hsub : (V : Set (DihedralGroup n)) ⊆
        ({1, DihedralGroup.r ((n / 2 : ℕ) : ZMod n)} : Set (DihedralGroup n)) :=
      fun x hx => rot_sq_eq_one n (hle hx) (hsq x hx)
    have hle2 : (V : Set (DihedralGroup n)).ncard ≤ 2 :=
      le_trans (Set.ncard_le_ncard hsub) (ncard_pair_le _ _)
    omega
  obtain ⟨s, hsV, hsR⟩ : ∃ s ∈ V, s ∉ Work.Dihedral.rot n := by
    by_contra h
    exact hnotrot fun x hx => by
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
  obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hsR
  have hzV : DihedralGroup.r ((n / 2 : ℕ) : ZMod n) ∈ V :=
    centerElem_mem_of_normal_fourGroup n V hVn hV4
  have hhz : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    have h1 : (DihedralGroup.r (((n / 2 : ℕ) : ZMod n))) ^ 2 = 1 := hsq _ hzV
    have h2 : DihedralGroup.r (((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n)) = 1 := by
      simpa [pow_two, DihedralGroup.r_mul_r] using h1
    exact DihedralGroup.r.inj h2
  have hneg : -(((n / 2 : ℕ)) : ZMod n) = ((n / 2 : ℕ) : ZMod n) :=
    (neg_eq_iff_add_eq_zero).mpr hhz
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxcomm : ∀ w ∈ V, w * x = x * w := Subgroup.mem_centralizer_iff.mp hx
    rcases Work.Dihedral.eq_r_or_sr x with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · -- `x = r j`: commutation with `sr i` forces `j = -j`, i.e. `(r j)^2 = 1`
      have hcomm := hxcomm (DihedralGroup.sr i) hsV
      have h1 : (i : ZMod n) + j = i - j := by
        have : DihedralGroup.sr (i + j) = DihedralGroup.sr (i - j) := by
          simpa [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] using hcomm
        exact DihedralGroup.sr.inj this
      have hjeq : j = -j := by
        have h1' : i + j = i + -j := by simpa [sub_eq_add_neg] using h1
        exact add_left_cancel h1'
      have h2j : 2 * j = 0 := by
        have := (eq_neg_iff_add_eq_zero (a := j) (b := j)).mp hjeq
        simpa [two_mul] using this
      have hsqx : (DihedralGroup.r j) ^ 2 = 1 := by
        have h : DihedralGroup.r (j + j) = 1 := by
          rw [show j + j = 0 by simpa [two_mul] using h2j, DihedralGroup.r_zero]
        simpa [pow_two, DihedralGroup.r_mul_r] using h
      rcases rot_sq_eq_one n (Work.Dihedral.r_mem_rot j) hsqx with h | h
      · rw [h]; exact V.one_mem
      · rw [h]; exact hzV
    · -- `x = sr j`: commutation with `sr i` forces `j - i = i - j`
      have hcomm := hxcomm (DihedralGroup.sr i) hsV
      have h1 : (j : ZMod n) - i = i - j := by
        have : DihedralGroup.r (j - i) = DihedralGroup.r (i - j) := by
          simpa [DihedralGroup.sr_mul_sr] using hcomm
        exact DihedralGroup.r.inj this
      have hd : 2 * (j - i) = 0 := by
        have hd1 : j - i = -(j - i) := h1.trans (neg_sub j i).symm
        have := (eq_neg_iff_add_eq_zero (a := j - i) (b := j - i)).mp hd1
        simpa [two_mul] using this
      rcases zmod_two_mul_eq_zero n (j - i) hd with hd0 | hdh
      · have hji : j = i := sub_eq_zero.mp hd0
        rw [hji]; exact hsV
      · have hji : j = i + ((n / 2 : ℕ) : ZMod n) := by
          rw [← hdh]; ring
        have hsj : DihedralGroup.sr j =
            DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr i := by
          rw [hji, DihedralGroup.r_mul_sr]
          congr 1
          rw [sub_eq_add_neg, hneg]
        rw [hsj]
        exact V.mul_mem hzV hsV
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hv2 : v * v = 1 := by simpa [sq] using hsq v hv
    have hw2 : w * w = 1 := by simpa [sq] using hsq w hw
    have hwv2 : (w * v) * (w * v) = 1 := by simpa [sq] using hsq (w * v) (V.mul_mem hw hv)
    calc w * v = (w * v)⁻¹ := (inv_eq_of_mul_eq_one_right hwv2).symm
      _ = v⁻¹ * w⁻¹ := mul_inv_rev w v
      _ = v * w := by
          rw [inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hw2]

/-! ## Existence of Klein four-subgroups -/

/-- For even `n` there is a Klein four-subgroup of `DihedralGroup n`, namely
`{1, r m, sr 0, sr m}` for `n = 2 * m`. -/
private theorem exists_fourGroup_of_even (n : ℕ) [NeZero n] (h : Even n) :
    ∃ V : Subgroup (DihedralGroup n), Nat.card V = 4 ∧ ∀ x ∈ V, x ^ 2 = 1 := by
  obtain ⟨m, hm⟩ := h
  have hmpos : 0 < m := by have := Nat.pos_of_ne_zero (NeZero.ne n); omega
  set h2 : ZMod n := (m : ZMod n) with hh2def
  have hh : h2 + h2 = 0 := by
    rw [hh2def, ← Nat.cast_add, ← hm, ZMod.natCast_self]
  have hh0 : h2 ≠ 0 := by
    rw [hh2def]
    intro h0
    have hdvd : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp h0
    have hle : n ≤ m := Nat.le_of_dvd hmpos hdvd
    omega
  have hneg : -h2 = h2 := (neg_eq_iff_add_eq_zero).mpr hh
  set a : DihedralGroup n := DihedralGroup.r h2 with hadef
  set b : DihedralGroup n := DihedralGroup.sr 0 with hbdef
  set c : DihedralGroup n := DihedralGroup.sr h2 with hcdef
  have ha2 : a * a = 1 := by
    rw [hadef, DihedralGroup.r_mul_r, hh, DihedralGroup.r_zero]
  have hb2 : b * b = 1 := by rw [hbdef, DihedralGroup.sr_mul_self]
  have hc2 : c * c = 1 := by rw [hcdef, DihedralGroup.sr_mul_self]
  have hab : a * b = c := by
    rw [hadef, hbdef, hcdef, DihedralGroup.r_mul_sr, zero_sub, hneg]
  have hba : b * a = c := by
    rw [hadef, hbdef, hcdef, DihedralGroup.sr_mul_r, zero_add]
  have hac : a * c = b := by
    rw [hadef, hbdef, hcdef, DihedralGroup.r_mul_sr, sub_self]
  have hca : c * a = b := by
    rw [hadef, hbdef, hcdef, DihedralGroup.sr_mul_r, hh]
  have hbc : b * c = a := by
    rw [hadef, hbdef, hcdef, DihedralGroup.sr_mul_sr, sub_zero]
  have hcb : c * b = a := by
    rw [hadef, hbdef, hcdef, DihedralGroup.sr_mul_sr, zero_sub, hneg]
  have h1a : (1 : DihedralGroup n) ≠ a := by
    rw [hadef]
    intro hh'
    exact hh0 (DihedralGroup.r.inj (by simpa using hh'.symm))
  have h1b : (1 : DihedralGroup n) ≠ b := by
    rw [hbdef]
    intro hh'
    exact (Work.Dihedral.sr_ne_r 0 0) hh'.symm
  have h1c : (1 : DihedralGroup n) ≠ c := by
    rw [hcdef]
    intro hh'
    exact (Work.Dihedral.sr_ne_r h2 0) hh'.symm
  have hab' : a ≠ b := by
    rw [hadef, hbdef]
    intro hh'
    exact (Work.Dihedral.sr_ne_r 0 h2) hh'.symm
  have hac' : a ≠ c := by
    rw [hadef, hcdef]
    intro hh'
    exact (Work.Dihedral.sr_ne_r h2 h2) hh'.symm
  have hbc' : b ≠ c := by
    rw [hbdef, hcdef]
    intro hh'
    exact hh0 (DihedralGroup.sr.inj hh').symm
  set V : Subgroup (DihedralGroup n) :=
    { carrier := ({1, a, b, c} : Set (DihedralGroup n))
      mul_mem' := by
        rintro x y (hx : x = 1 ∨ x = a ∨ x = b ∨ x = c)
          (hy : y = 1 ∨ y = a ∨ y = b ∨ y = c)
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp only [one_mul, mul_one, ha2, hb2, hc2, hab, hba, hac, hca, hbc, hcb] <;> simp
      one_mem' := by simp
      inv_mem' := by
        rintro x (hx : x = 1 ∨ x = a ∨ x = b ∨ x = c)
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · rw [inv_eq_of_mul_eq_one_right ha2]; simp
        · rw [inv_eq_of_mul_eq_one_right hb2]; simp
        · rw [inv_eq_of_mul_eq_one_right hc2]; simp } with hVdef
  refine ⟨V, ?_, ?_⟩
  · have hcoe : Nat.card V = (V : Set (DihedralGroup n)).ncard :=
      Nat.card_coe_set_eq (V : Set (DihedralGroup n))
    have hVs : (V : Set (DihedralGroup n)) = ({1, a, b, c} : Set (DihedralGroup n)) := by
      rw [hVdef]
      ext x
      simp
    rw [hcoe, hVs]
    exact ncard_four_eq 1 a b c h1a h1b h1c hab' hac' hbc'
  · intro x hx
    have hx' : x = 1 ∨ x = a ∨ x = b ∨ x = c := hx
    rcases hx' with h | h | h | h
    · rw [h]; simp
    · rw [h]; simpa [pow_two] using ha2
    · rw [h]; simpa [pow_two] using hb2
    · rw [h]; simpa [pow_two] using hc2

/-! ## A second involution -/

private theorem involution_ne_of_central (n : ℕ) [NeZero n] (hn : 2 ≤ n) (z : DihedralGroup n)
    (_hz : orderOf z = 2) (_hzc : z ∈ Subgroup.center (DihedralGroup n)) :
    ∃ u : DihedralGroup n, orderOf u = 2 ∧ u ≠ z := by
  by_cases h : z = DihedralGroup.sr 0
  · refine ⟨DihedralGroup.sr 1, by simp, ?_⟩
    rw [h]
    intro hh
    have h1 : ((1 : ℕ) : ZMod n) = 0 := by simpa using DihedralGroup.sr.inj hh
    have h2 : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp h1
    have h3 : n ≤ 1 := Nat.le_of_dvd (by norm_num) h2
    omega
  · exact ⟨DihedralGroup.sr 0, by simp, fun hh => h hh.symm⟩

/-! ## The four facts -/

theorem DihedralFacts : Work.RED.GW2.DihedralFactsProp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn E hE
    haveI : NeZero n := hn
    exact card_le_four n E hE
  · intro n hn V hVn hV4
    haveI : NeZero n := hn
    exact centralizer_eq_of_fourGroup n V hVn hV4
  · intro n hn h
    haveI : NeZero n := hn
    exact exists_fourGroup_of_even n h
  · intro n hn h2 z hz hzc
    haveI : NeZero n := hn
    exact involution_ne_of_central n h2 z hz hzc

end Work.RED
