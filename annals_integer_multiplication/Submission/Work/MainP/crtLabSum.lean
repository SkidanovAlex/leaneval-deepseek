import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtMath

/-!
# `crtLabSum`: the sum of the entry labels, and the sizes of the CRT state

`Work.MainP.crtLabWord` produces the label list `sigmaList ss` by running an *odometer*: the state
at time `i` is a list of triples `(r_j·P_j, P_j, s_j·P_j)` (with `(s_j, P_j) = [crtTab ss]_j` and
`r_j = i % s_j`), and the running label is the sum of the first components.

This file collects the *arithmetic* facts about that state, needed to bound the cost of the word:

* `(Est ss i).map entryC).sum = vlab ss i` — the sum of the first components is the label
  `crtIdx ss i` (§5.4 of the paper);
* `0 ≤ vlab ss i ≤ S` where `S = ss.prod`;
* every entry has the shape `triple ((i % s)·P) P (s·P)`;
* each entry has size `≤ 3·(S.size + 2) + 3`, whence the whole state has size
  `≤ (ss.length + 1)·(3·(S.size + 2) + 4) + 1`.

The last two are the bounds that make the per-step cost of the odometer `O(d · size S)`.
-/

set_option autoImplicit false

namespace Work.MainP

open HvdH

/-! ## Elementary value facts -/

/-- Casting a list sum of naturals to `ℤ`. -/
theorem sum_map_ofNat (l : List ℕ) : (l.map Int.ofNat).sum = ((l.sum : ℕ) : ℤ) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Size of an entry `triple c P Q` (two nested `cons`, no terminator). -/
theorem vsz_triple (c P Q : ℤ) : HvdH.vsz (triple c P Q) = HvdH.isz c + HvdH.isz P + HvdH.isz Q + 2 := by
  simp only [triple, vsz_cons]
  rw [vsz_int, vsz_int, vsz_int]
  ring

/-! ## The label sum -/

/-- The first components of `canon ss i` are the mixed-radix digits of `i`. -/
theorem canon_map_entryC (ss : List ℕ) (i : ℕ) :
    (canon ss i).map entryC = (crtTab ss).map (fun sp => (((i % sp.1) * sp.2 : ℕ) : ℤ)) := by
  simp only [canon, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro sp _
  exact entryC_triple _ _ _

/-- The label sum for the canonical state. -/
theorem canon_sum_entryC (ss : List ℕ) (i : ℕ) : ((canon ss i).map entryC).sum = vlab ss i := by
  rw [canon_map_entryC]
  rw [show ((crtTab ss).map (fun sp : ℕ × ℕ => (((i % sp.1) * sp.2 : ℕ) : ℤ)))
      = (((crtTab ss).map (fun sp : ℕ × ℕ => (i % sp.1) * sp.2)).map Int.ofNat) from by
    rw [List.map_map]; rfl]
  rw [sum_map_ofNat, vlab, crtIdx_eq_sum]

/-- Membership in the runtime state `Est ss i` is membership in `canon ss i`. -/
theorem mem_Est {ss : List ℕ} {i : ℕ} {e : Val} : e ∈ Est ss i ↔ e ∈ canon ss i := by
  unfold Est
  split <;> simp [List.mem_reverse]

/-- The label sum for the runtime state. -/
theorem estSumEntryC (ss : List ℕ) (i : ℕ) : ((Est ss i).map entryC).sum = vlab ss i := by
  unfold Est
  split
  · exact canon_sum_entryC ss i
  · rw [List.map_reverse, List.sum_reverse]; exact canon_sum_entryC ss i

/-! ## The entries of the place-value table -/

/-- An entry `(s, P)` of `crtTab ss` is a modulus of `ss` followed by the product of a suffix. -/
theorem mem_crtTab {ss : List ℕ} {sp : ℕ × ℕ} (h : sp ∈ crtTab ss) :
    ∃ pre suf : List ℕ, ss = pre ++ sp.1 :: suf ∧ sp.2 = suf.prod := by
  induction ss generalizing sp with
  | nil => simp [crtTab] at h
  | cons s ss ih =>
      rw [crtTab_cons, List.mem_cons] at h
      rcases h with h | h
      · rw [h]; exact ⟨[], ss, rfl, rfl⟩
      · obtain ⟨pre, suf, heq, hsnd⟩ := ih h
        exact ⟨s :: pre, suf, by rw [heq]; rfl, hsnd⟩

/-- The modulus of an entry of `crtTab ss` is at least `1` when so are the elements of `ss`. -/
theorem crtTab_1le_fst {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) {sp : ℕ × ℕ}
    (h : sp ∈ crtTab ss) : 1 ≤ sp.1 := by
  obtain ⟨pre, suf, heq, _⟩ := mem_crtTab h
  exact hpos sp.1 (by rw [heq]; exact List.mem_append_right _ List.mem_cons_self)

/-- For an entry `(s, P)` of `crtTab ss`, `s * P` is a suffix product of `ss`, hence `≤ ss.prod`. -/
theorem crtTab_mul_le {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) {sp : ℕ × ℕ}
    (h : sp ∈ crtTab ss) : sp.1 * sp.2 ≤ ss.prod := by
  obtain ⟨pre, suf, heq, hsnd⟩ := mem_crtTab h
  have hpre : 1 ≤ pre.prod :=
    List.one_le_prod (fun a ha => hpos a (by rw [heq]; exact List.mem_append_left _ ha))
  have hprod : ss.prod = pre.prod * (sp.1 * sp.2) := by
    rw [heq, List.prod_append, List.prod_cons, hsnd]
  calc sp.1 * sp.2 = 1 * (sp.1 * sp.2) := by ring
    _ ≤ pre.prod * (sp.1 * sp.2) := Nat.mul_le_mul_right _ hpre
    _ = ss.prod := hprod.symm

/-- For an entry `(s, P)` of `crtTab ss`, the place value `P` is `≤ ss.prod`. -/
theorem crtTab_snd_le {ss : List ℕ} (hpos : ∀ s ∈ ss, 1 ≤ s) {sp : ℕ × ℕ}
    (h : sp ∈ crtTab ss) : sp.2 ≤ ss.prod := by
  have h1 : 1 ≤ sp.1 := crtTab_1le_fst hpos h
  calc sp.2 = 1 * sp.2 := by ring
    _ ≤ sp.1 * sp.2 := Nat.mul_le_mul_right _ h1
    _ ≤ ss.prod := crtTab_mul_le hpos h

/-! ## The size bound -/

/-- Every entry of the runtime state has size `≤ 3·(S.size + 2) + 3`. -/
theorem estVszLe {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) (hpos : ∀ s ∈ ss, 1 ≤ s) (i : ℕ) :
    ∀ e ∈ Est ss i, HvdH.vsz e ≤ 3 * (S.size + 2) + 3 := by
  intro e he
  have hc : e ∈ canon ss i := mem_Est.mp he
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.mp hc
  rw [vsz_triple, isz_natCast, isz_natCast, isz_natCast]
  have hQ : sp.1 * sp.2 ≤ S := by rw [hS]; exact crtTab_mul_le hpos hsp
  have hP : sp.2 ≤ S := by rw [hS]; exact crtTab_snd_le hpos hsp
  have hmod : i % sp.1 ≤ sp.1 :=
    le_of_lt (Nat.mod_lt i (lt_of_lt_of_le Nat.zero_lt_one (crtTab_1le_fst hpos hsp)))
  have hc' : (i % sp.1) * sp.2 ≤ S := le_trans (Nat.mul_le_mul_right _ hmod) hQ
  have h1 := Nat.size_le_size hc'
  have h2 := Nat.size_le_size hP
  have h3 := Nat.size_le_size hQ
  simp only [iszN]
  omega

/-! ## The task -/

theorem crtLabSum {ss : List ℕ} {S : ℕ} (hS : S = ss.prod) (hpos : ∀ s ∈ ss, 1 ≤ s) (i : ℕ) :
    ((Work.MainP.Est ss i).map Work.MainP.entryC).sum = Work.MainP.vlab ss i ∧
    0 ≤ Work.MainP.vlab ss i ∧ Work.MainP.vlab ss i ≤ (S : ℤ) ∧
    (∀ e ∈ Work.MainP.Est ss i, ∃ (s P : ℕ),
      e = Work.MainP.triple (((i % s) * P : ℕ) : ℤ) (P : ℤ) ((s * P : ℕ) : ℤ)) ∧
    (∀ e ∈ Work.MainP.Est ss i, HvdH.vsz e ≤ 3 * (S.size + 2) + 3) ∧
    HvdH.vsz (HvdH.ofList (Work.MainP.Est ss i)) ≤ (ss.length + 1) * (3 * (S.size + 2) + 4) + 1 := by
  refine ⟨estSumEntryC ss i, Int.natCast_nonneg _, ?_, ?_, estVszLe hS hpos i, ?_⟩
  · rw [hS, vlab]
    exact Nat.cast_le.mpr
      (le_of_lt (crtIdx_lt (fun s hs => lt_of_lt_of_le Nat.zero_lt_one (hpos s hs)) i))
  · intro e he
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.mp (mem_Est.mp he)
    exact ⟨sp.1, sp.2, rfl⟩
  · rw [vsz_ofList, Est_length]
    have hsum : ((Est ss i).map HvdH.vsz).sum ≤ ss.length * (3 * (S.size + 2) + 3) := by
      have hle := List.sum_le_sum (l := Est ss i) (f := HvdH.vsz)
        (g := fun _ : Val => 3 * (S.size + 2) + 3) (fun x hx => estVszLe hS hpos i x hx)
      rw [List.map_const', List.sum_const_nat] at hle
      simpa [Est_length] using hle
    calc ((Est ss i).map HvdH.vsz).sum + ss.length + 1
        ≤ ss.length * (3 * (S.size + 2) + 3) + ss.length + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right hsum ss.length) 1
      _ = ss.length * (3 * (S.size + 2) + 4) + 1 := by ring
      _ ≤ (ss.length + 1) * (3 * (S.size + 2) + 4) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_succ ss.length)) 1

end Work.MainP
