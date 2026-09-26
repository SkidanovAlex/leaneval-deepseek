import Submission.Work.ConfineTransfer

open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Confined-factor counting and the align-level general-`k` T1 disjunction

`ConfineTransfer.lean` proves the junction mirror theorem: for any two
adjacent blocks, the cancelled pairs crossing their junction are exactly the
mirror slots `s < crossCount Fs t` (`junction_mirror`, forward direction), so
`align L_t L_{t+1} ≥ crossCount Fs t`.  This module adds:

* the **reverse** direction `junction_mirror_rev` — every cross pair is a
  mirror slot (the `crossCount` mirror slots are distinct members of the
  junction list, whose length is `crossCount`, so nothing else fits);
* the **confined-factor counting**: for a confined block `j` every letter is
  cancelled against a partner in the adjacent block `j-1` or `j+1`; letters
  whose partner lies left occupy offsets `< crossCount (j-1)` (by the reverse
  direction at junction `j-1`) and letters whose partner lies right occupy
  offsets `≥ |L_j| - crossCount j` (by the reverse direction at junction
  `j`), giving

      |L_j| = crossCount (j-1) + crossCount j      (interior)

  and the one-sided identities at the ends
  (`|L_0| ≤ crossCount 0`, `|L_{k-1}| ≤ crossCount (k-2)`, from confinement
  alone every letter of the end block pairs inwards);
* the **assembly** `t1_align_general` (PROVEN below): from
  `confined_factor_exists` and the counting, a concatenation of reduced
  factors whose reduction has length ≤ 1 satisfies the align-level T1
  disjunction.  (The absorption-level general-`k` aggregate — translating the
  alignment disjuncts through `FactorAbsorption`'s
  `absorbedRight_of_align_eq_left` / `absorbedLeft_of_align_eq_right` /
  `middleAbsorbed_of_align_ge` — is the next milestone; it needs the
  general-`k` word-to-group reduction-length bridge.)

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## Reverse junction mirror -/

/-- The mirror slots below `crossCount` are members of the junction list. -/
lemma slotPair_mem_junctionPairs {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (ht : t + 1 < Fs.length) {s : ℕ} (hs : s < crossCount Fs t) :
    slotPair Fs t s ∈ junctionPairs Fs t := by
  classical
  have hpair := junction_mirror Fs hred ht s hs
  have hc1 : crossCount Fs t ≤ (Fs[t]).length := crossCount_le_factor_left Fs ht
  have hc2 : crossCount Fs t ≤ (Fs[t + 1]).length := crossCount_le_factor_right Fs ht
  have hs1 : s < (Fs[t]).length := lt_of_lt_of_le hs hc1
  have hs2 : s < (Fs[t + 1]).length := lt_of_lt_of_le hs hc2
  have hsuccL : BlockStart Fs (t + 1) = BlockStart Fs t + Fs[t].length :=
    BlockStart_succ_in Fs (j := t) (by omega)
  have hsuccR : BlockStart Fs (t + 2) = BlockStart Fs (t + 1) + Fs[t + 1].length :=
    BlockStart_succ_in Fs (j := t + 1) ht
  have hoffL : s + 1 ≤ Fs[t].length := by omega
  have hoffR : s + 1 ≤ Fs[t + 1].length := by omega
  have hL : InBlock Fs t (BlockStart Fs (t + 1) - 1 - s) := by
    refine ⟨?_, ?_, ?_⟩
    · omega
    · rw [hsuccL]
      omega
    · rw [hsuccL]
      omega
  have hR : InBlock Fs (t + 1) (BlockStart Fs (t + 1) + s) := by
    refine ⟨ht, ?_, ?_⟩
    · omega
    · rw [hsuccR]
      omega
  exact mem_junctionPairs_of Fs t hpair hL hR

/-- **Reverse junction mirror.**  Every cross pair at a junction is one of
the mirror slots below the cross count: the `crossCount` mirror slots are
distinct members of the junction list (length `crossCount`), so the list
contains no other element. -/
theorem junction_mirror_rev {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {t : ℕ} (ht : t + 1 < Fs.length) :
    ∀ pr : ℕ × ℕ, pr ∈ junctionPairs Fs t →
      ∃ s : ℕ, s < crossCount Fs t ∧ pr = slotPair Fs t s := by
  classical
  intro pr hpr
  let c := crossCount Fs t
  by_contra hnot
  have hnot' : ∀ s : ℕ, s < c → pr ≠ slotPair Fs t s := by
    intro s hs hEq
    apply hnot
    exact ⟨s, hs, hEq⟩
  let M : List (ℕ × ℕ) := (List.range c).map (fun s => slotPair Fs t s)
  have hMnod : M.Nodup := by
    unfold M
    apply List.Nodup.map
    · intro a b h
      have hs := congrArg Prod.snd h
      simp [slotPair] at hs
      omega
    · exact List.nodup_range
  have hnotPr : pr ∉ M := by
    intro hM
    rcases (List.mem_map.mp hM) with ⟨s, hs, hEq⟩
    exact hnot' s (List.mem_range.mp hs) hEq.symm
  have hsub : ∀ x ∈ M ++ [pr], x ∈ junctionPairs Fs t := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · rcases (List.mem_map.mp hx) with ⟨s, hs, rfl⟩
      exact slotPair_mem_junctionPairs Fs hred ht (s := s)
        (by simpa [c] using (List.mem_range.mp hs))
    · have hxpr : x = pr := List.mem_singleton.mp hx
      subst x
      exact hpr
  have hMlen : (M ++ [pr]).length = c + 1 := by
    rw [List.length_append, List.length_singleton]
    simp [M]
  have hnodapp : (M ++ [pr]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hMnod, List.nodup_singleton pr, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst b
    intro hEq
    subst a
    exact hnotPr ha
  have hle := nodup_length_le_of_subset (β := ℕ × ℕ) hnodapp hsub
  rw [hMlen] at hle
  have hc : (junctionPairs Fs t).length = c := rfl
  rw [hc] at hle
  omega


/-! ## Offset of a letter pairing across a junction -/

/-- A letter of block `j` pairing with a letter of block `j-1` sits at an
offset below `crossCount (j-1)`: its pair is a cross pair at junction `j-1`,
hence a mirror slot. -/
lemma pair_left_offset_lt {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j p y : ℕ} (hj : j < Fs.length) (hj0 : 0 < j)
    (hp : InBlock Fs j p) (hy : InBlock Fs (j - 1) y)
    (hpair : (y, p) ∈ cancelledPairs Fs.flatten) :
    p - BlockStart Fs j < crossCount Fs (j - 1) := by
  have hj1 : (j - 1) + 1 = j := by omega
  have ht : (j - 1) + 1 < Fs.length := by rw [hj1]; exact hj
  have hp' : InBlock Fs ((j - 1) + 1) p := by simpa [hj1] using hp
  have hmem : (y, p) ∈ junctionPairs Fs (j - 1) :=
    mem_junctionPairs_of Fs (j - 1) hpair hy hp'
  rcases junction_mirror_rev Fs hred ht (y, p) hmem with ⟨s, hs, hEq⟩
  have hpEq := congrArg Prod.snd hEq
  simp [slotPair] at hpEq
  rw [hj1] at hpEq
  have : p - BlockStart Fs j = s := by omega
  rwa [this]

/-- A letter of block `j` pairing with a letter of block `j+1` sits at an
offset at least `|L_j| - crossCount j`: its pair is a cross pair at junction
`j`, hence a mirror slot. -/
lemma pair_right_offset_ge {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j p y : ℕ} (hj : j + 1 < Fs.length)
    (hp : InBlock Fs j p) (hy : InBlock Fs (j + 1) y)
    (hpair : (p, y) ∈ cancelledPairs Fs.flatten) :
    (Fs[j]).length ≤ crossCount Fs j + (p - BlockStart Fs j) := by
  have hmem : (p, y) ∈ junctionPairs Fs j :=
    mem_junctionPairs_of Fs j hpair hp hy
  rcases junction_mirror_rev Fs hred hj (p, y) hmem with ⟨s, hs, hEq⟩
  have hpEq := congrArg Prod.fst hEq
  simp [slotPair] at hpEq
  have hsuccL : BlockStart Fs (j + 1) = BlockStart Fs j + Fs[j].length :=
    BlockStart_succ_in Fs (j := j) (by omega)
  have hcle : crossCount Fs j ≤ (Fs[j]).length := crossCount_le_factor_left Fs hj
  omega

/-! ## A letter of a confined block pairs left or right -/

/-- A letter of a confined block is cancelled against a letter of block `j-1`
or of block `j+1`. -/
lemma confined_letter_partner {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) {j p : ℕ} (_hj : j < Fs.length) (hconf : Confined Fs j)
    (hp : InBlock Fs j p) :
    (∃ y : ℕ, InBlock Fs (j - 1) y ∧ (y, p) ∈ cancelledPairs Fs.flatten) ∨
    (∃ y : ℕ, InBlock Fs (j + 1) y ∧ (p, y) ∈ cancelledPairs Fs.flatten) := by
  classical
  have hns : p ∉ survivorPos Fs.flatten := hconf.1 p hp
  have hx : p < Fs.flatten.length := InBlock_lt_total hp
  rcases (in_pair_iff_not_survivor (Fs.flatten) hx).mpr hns with ⟨y, hpy⟩
  rcases hconf.2 p hp y hpy with ⟨j', hadj, hy'⟩
  rcases hadj with hright | hleft
  · -- j' = j + 1
    have hyR : InBlock Fs (j + 1) y := by simpa [hright] using hy'
    rcases hpy with hpy | hpy
    · right
      exact ⟨y, hyR, hpy⟩
    · -- (y, p) with y in block j+1: y > p, contradicting y < p
      have hylt := pair_lt (Fs.flatten) hpy
      have hpB : p < BlockStart Fs (j + 1) := hp.2.2
      have hyB : BlockStart Fs (j + 1) ≤ y := hyR.2.1
      omega
  · -- j = j' + 1
    have hyL : InBlock Fs (j - 1) y := by
      have hj' : j' = j - 1 := by omega
      simpa [hj'] using hy'
    rcases hpy with hpy | hpy
    · -- (p, y) with y in block j-1: y < p, contradicting p < y
      have hplt := pair_lt (Fs.flatten) hpy
      have hj1 : (j - 1) + 1 = j := by omega
      have hyB : y < BlockStart Fs j := by simpa [hj1] using hyL.2.2
      have hpB : BlockStart Fs j ≤ p := hp.2.1
      omega
    · left
      exact ⟨y, hyL, hpy⟩


/-! ## Confined-factor counting -/

/-- Interior confined block: `|L_j| ≤ crossCount (j-1) + crossCount j`.  If a
letter lay beyond offset `crossCount (j-1)`, confinement would force it to
pair right at an offset below `|L_j| - crossCount j` — impossible. -/
lemma confined_length_le_cross_sum {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj0 : 0 < j) (hjk : j + 1 < Fs.length)
    (hconf : Confined Fs j) :
    crossCount Fs (j - 1) + crossCount Fs j ≥ (Fs[j]).length := by
  classical
  by_contra hlt
  have hlen : crossCount Fs (j - 1) + crossCount Fs j < (Fs[j]).length := lt_of_not_ge hlt
  have hj : j < Fs.length := by omega
  let p : ℕ := BlockStart Fs j + crossCount Fs (j - 1)
  have hp : InBlock Fs j p := by
    refine ⟨hj, ?_, ?_⟩
    · simp [p]
    · have hsuccL : BlockStart Fs (j + 1) = BlockStart Fs j + Fs[j].length :=
        BlockStart_succ_in Fs (j := j) (by omega)
      omega
  rcases confined_letter_partner Fs hj hconf hp with hL | hR
  · rcases hL with ⟨y, hy, hpair⟩
    have hofflt := pair_left_offset_lt Fs hred (j := j) (p := p) (y := y) hj hj0 hp hy hpair
    have : p - BlockStart Fs j = crossCount Fs (j - 1) := by simp [p]
    omega
  · rcases hR with ⟨y, hy, hpair⟩
    have hoffge := pair_right_offset_ge Fs hred (j := j) (p := p) (y := y) hjk hp hy hpair
    have : p - BlockStart Fs j = crossCount Fs (j - 1) := by simp [p]
    omega

/-- Leading confined block: `|L_0| ≤ crossCount 0`.  Confinement forces every
letter of the first block to pair rightwards. -/
lemma confined_zero_length_le {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    (h1 : 1 < Fs.length) (hconf : Confined Fs 0) :
    crossCount Fs 0 ≥ (Fs[0]).length := by
  classical
  by_cases hz : (Fs[0]).length = 0
  · rw [hz]
    simp
  · have hlen0 : 0 < (Fs[0]).length := Nat.pos_of_ne_zero hz
    let p : ℕ := BlockStart Fs 0
    have hp : InBlock Fs 0 p := by
      refine ⟨by omega, le_rfl, ?_⟩
      have hsuccL : BlockStart Fs 1 = BlockStart Fs 0 + Fs[0].length :=
        BlockStart_succ_in Fs (j := 0) (by omega)
      have h01 : 0 + 1 = 1 := rfl
      rw [h01]
      omega
    have hns : p ∉ survivorPos Fs.flatten := hconf.1 p hp
    have hx : p < Fs.flatten.length := InBlock_lt_total hp
    rcases (in_pair_iff_not_survivor (Fs.flatten) hx).mpr hns with ⟨y, hpy⟩
    rcases hconf.2 p hp y hpy with ⟨j', hadj, hy'⟩
    have hy1 : InBlock Fs 1 y := by
      rcases hadj with h1' | h0
      · simpa [h1'] using hy'
      · have : False := by omega
        exact False.elim this
    have hyRpair : (p, y) ∈ cancelledPairs Fs.flatten := by
      rcases hpy with hpy | hpy
      · exact hpy
      · have hylt := pair_lt (Fs.flatten) hpy
        have hpB : p < BlockStart Fs 1 := hp.2.2
        have hyB : BlockStart Fs 1 ≤ y := hy1.2.1
        omega
    have hoffge := pair_right_offset_ge Fs hred (j := 0) (p := p) (y := y) h1 hp hy1 hyRpair
    have : p - BlockStart Fs 0 = 0 := by simp [p]
    omega

/-- Trailing confined block: `|L_j| ≤ crossCount (j-1)` when `j+1 = Fs.length`.
Confinement forces every letter of the last block to pair leftwards. -/
lemma confined_last_length_le {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j < Fs.length) (h2 : 2 ≤ Fs.length) (hlast : j + 1 = Fs.length)
    (hconf : Confined Fs j) :
    crossCount Fs (j - 1) ≥ (Fs[j]).length := by
  classical
  by_contra hlt
  have hj0 : 0 < j := by omega
  let p : ℕ := BlockStart Fs j + crossCount Fs (j - 1)
  have hp : InBlock Fs j p := by
    refine ⟨hj, ?_, ?_⟩
    · simp [p]
    · have hsuccL : BlockStart Fs (j + 1) = BlockStart Fs j + Fs[j].length :=
        BlockStart_succ_in Fs (j := j) hj
      omega
  rcases confined_letter_partner Fs hj hconf hp with hL | hR
  · rcases hL with ⟨y, hy, hpair⟩
    have hofflt := pair_left_offset_lt Fs hred (j := j) (p := p) (y := y) hj hj0 hp hy hpair
    have : p - BlockStart Fs j = crossCount Fs (j - 1) := by simp [p]
    omega
  · -- no right neighbour exists
    rcases hR with ⟨y, hy, hpair⟩
    have hbad : j + 1 < Fs.length := hy.1
    omega

/-! ## Alignment corollaries in block-index terms -/

/-- Alignment across the left junction of block `j`. -/
lemma align_left_junction {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : 0 < j) (hj2 : j < Fs.length) :
    align (Fs[j - 1]) (Fs[j]) ≥ crossCount Fs (j - 1) := by
  have ht : (j - 1) + 1 < Fs.length := by
    have : (j - 1) + 1 = j := by omega
    rw [this]
    exact hj2
  have htmp := align_ge_crossCount Fs hred (t := j - 1) ht
  have hj1 : (j - 1) + 1 = j := by omega
  simpa [hj1] using htmp

/-- Alignment across the right junction of block `j`. -/
lemma align_right_junction {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    {j : ℕ} (hj : j + 1 < Fs.length) :
    align (Fs[j]) (Fs[j + 1]) ≥ crossCount Fs j :=
  align_ge_crossCount Fs hred (t := j) hj


/-! ## The align-level general-`k` T1 disjunction -/

/-- **T1, alignment level.**  For a concatenation of `k ≥ 2` reduced words
whose reduction has length ≤ 1, some junction alignment equals the length of
one of its factors, or two adjacent junctions together cover the middle
factor:  `align L_j L_{j+1} = |L_j|`, `align L_j L_{j+1} = |L_{j+1}|`, or
`align L_{j-1} L_j + align L_j L_{j+1} ≥ |L_j|`.  (Proof: `Confine` gives a
confined factor; its letters pair into the neighbouring blocks, so the cross
counts bound its length; each junction alignment is at least the cross count
at that junction, and at the ends alignment cannot exceed the block length.) -/
theorem t1_align_general {α : Type*} [DecidableEq α]
    (Fs : List (List (α × Bool))) (hred : ∀ L ∈ Fs, FreeGroup.IsReduced L)
    (hk : 2 ≤ Fs.length) (hshort : (FreeGroup.reduce Fs.flatten).length ≤ 1) :
    (∃ (j : ℕ) (_hj : j < Fs.length) (hj1 : j + 1 < Fs.length),
        align (Fs[j]) (Fs[j + 1]) = (Fs[j]).length) ∨
    (∃ (j : ℕ) (_hj : j < Fs.length) (hj1 : j + 1 < Fs.length),
        align (Fs[j]) (Fs[j + 1]) = (Fs[j + 1]).length) ∨
    (∃ (j : ℕ) (_hj0 : 0 < j) (hj1 : j + 1 < Fs.length)
        (_hj2 : j < Fs.length) (_hm : j - 1 < Fs.length),
        align (Fs[j - 1]) (Fs[j]) + align (Fs[j]) (Fs[j + 1]) ≥ (Fs[j]).length) := by
  classical
  have hsurv : (survivorPos Fs.flatten).length ≤ 1 := by
    rw [survivorPos_length]
    exact hshort
  rcases confined_factor_exists Fs hred hk hsurv with ⟨j, hj, hconf⟩
  by_cases hj0 : j = 0
  · -- confined first block: everything pairs rightwards into block 1
    left
    refine ⟨0, ?_, ?_, ?_⟩
    · omega
    · omega
    · have h01s : 0 + 1 = 1 := rfl
      have hc : crossCount Fs 0 ≥ (Fs[0]).length :=
        confined_zero_length_le Fs hred (by omega) (by simpa [hj0] using hconf)
      have hal : align (Fs[0]) (Fs[1]) ≥ crossCount Fs 0 :=
        align_ge_crossCount Fs hred (t := 0) (by omega)
      have hle : align (Fs[0]) (Fs[1]) ≤ (Fs[0]).length :=
        align_le_length_left (Fs[0]) (Fs[1])
      apply le_antisymm
      · simpa [h01s] using hle
      · simpa [h01s] using le_trans hc hal
  · by_cases hjk : j + 1 = Fs.length
    · -- confined last block: everything pairs leftwards into block j-1
      right; left
      refine ⟨j - 1, ?_, ?_, ?_⟩
      · omega
      · omega
      · have hj1 : (j - 1) + 1 = j := by omega
        have hc : crossCount Fs (j - 1) ≥ (Fs[j]).length :=
          confined_last_length_le Fs hred (j := j) hj hk hjk hconf
        have hal : align (Fs[j - 1]) (Fs[j]) ≥ crossCount Fs (j - 1) :=
          align_left_junction Fs hred (j := j) (by omega) hj
        have hle : align (Fs[j - 1]) (Fs[j]) ≤ (Fs[j]).length :=
          align_le_length_right (Fs[j - 1]) (Fs[j])
        apply le_antisymm
        · simpa [hj1] using hle
        · simpa [hj1] using le_trans hc hal
    · -- interior confined block: two junctions cover it
      right; right
      refine ⟨j, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · exact hj
      · omega
      · have hc : crossCount Fs (j - 1) + crossCount Fs j ≥ (Fs[j]).length :=
          confined_length_le_cross_sum Fs hred (j := j) (by omega) (by omega) hconf
        have halL : align (Fs[j - 1]) (Fs[j]) ≥ crossCount Fs (j - 1) :=
          align_left_junction Fs hred (j := j) (by omega) (by omega : j < Fs.length)
        have halR : align (Fs[j]) (Fs[j + 1]) ≥ crossCount Fs j :=
          align_right_junction Fs hred (j := j) (by omega)
        omega

end Submission.Nielsen
