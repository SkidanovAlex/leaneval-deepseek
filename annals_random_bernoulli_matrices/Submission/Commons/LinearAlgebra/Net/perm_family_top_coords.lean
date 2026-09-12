import Mathlib
import Submission.Commons.LinearAlgebra.Net.top_coords_exists
import Submission.Commons.Combinatorics.Fin.exists_perm_cells
import Submission.Commons.Combinatorics.Fin.exists_perm_prefix_chain
import Submission.Commons.Combinatorics.Fin.sum_choose_pow_four
import Submission.Commons.Combinatorics.Fin.nested_chain_card_bound

set_option autoImplicit false
open scoped BigOperators

namespace Commons.LinearAlgebra.Net

open Finset

/-! We prove `perm_family_top_coords` by an explicit family of permutations.
For a vector `x` and `δ ∈ (0,1/2]` let `t = ⌊δ·n⌋₊`; the dyadic cuts in the
statement are `k_j = ⌊δ·n / 2^j⌋₊ = ⌊t / 2^j⌋`.  The family contains, for
every `t ≤ n/2` and every nested chain `[n] ⊇ I_0 ⊇ I_1 ⊇ ⋯` with
`|I_j| = t/2^j`, one permutation mapping the position-prefix of size `t/2^j`
onto `I_j` for every `j`.  The bound `card ≤ 5^n` is obtained by counting
such chains (`≤ C(n,t)·4^t` for each `t`, then `Σ_t ≤ 5^n`). -/

section Floor

/-- `(t+1)/2^j ≤ t/2^j + 1` -/
lemma nat_div_succ_le_two_pow (t j : ℕ) : (t + 1) / 2 ^ j ≤ t / 2 ^ j + 1 := by
  by_cases hj : j = 0
  · subst j
    simp
  · have h2 : 0 < 2 ^ j := pow_pos (by norm_num : 0 < (2 : ℕ)) j
    have h1 : t + 1 = 2 ^ j * (t / 2 ^ j) + (t % 2 ^ j + 1) := by
      have h1a := Nat.div_add_mod t (2 ^ j)
      omega
    have h2j : (t + 1) / 2 ^ j = t / 2 ^ j + (t % 2 ^ j + 1) / 2 ^ j := by
      rw [h1]
      exact Nat.mul_add_div (m := 2 ^ j) (m_pos := h2) (x := t / 2 ^ j) (y := t % 2 ^ j + 1)
    rw [h2j]
    have hmod : t % 2 ^ j < 2 ^ j := Nat.mod_lt _ h2
    have hle : t % 2 ^ j + 1 ≤ 2 ^ j := by omega
    have hdiv : (t % 2 ^ j + 1) / 2 ^ j ≤ 1 := by
      calc (t % 2 ^ j + 1) / 2 ^ j ≤ (2 ^ j) / 2 ^ j := Nat.div_le_div_right hle
      _ = 1 := Nat.div_self h2
    omega

/-- `⌊a / 2^j⌋₊ = ⌊a⌋₊ / 2^j` for `0 ≤ a` -/
lemma floor_div_pow (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    ⌊a / (2 : ℝ) ^ j⌋₊ = ⌊a⌋₊ / 2 ^ j := by
  have ht : (⌊a⌋₊ : ℝ) ≤ a ∧ a < (⌊a⌋₊ : ℝ) + 1 := by
    exact (Nat.floor_eq_iff ha).1 rfl
  have hnonneg : 0 ≤ a / (2 : ℝ) ^ j :=
    div_nonneg ha (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) j)
  rw [Nat.floor_eq_iff hnonneg]
  have hpow : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num : 0 < (2 : ℝ)) j
  constructor
  · rw [le_div_iff₀ hpow]
    have hm : (⌊a⌋₊ / 2 ^ j) * 2 ^ j ≤ ⌊a⌋₊ := by
      simpa [Nat.mul_comm] using Nat.mul_div_le ⌊a⌋₊ (2 ^ j)
    have hm3 : ((⌊a⌋₊ / 2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
      exact_mod_cast hm
    have hm2 : ((⌊a⌋₊ / 2 ^ j : ℕ) : ℝ) * (2 : ℝ) ^ j ≤ (⌊a⌋₊ : ℝ) := by
      simpa [Nat.cast_pow] using hm3
    exact le_trans hm2 ht.1
  · rw [div_lt_iff₀ hpow]
    let r : ℕ := ⌊a⌋₊ % 2 ^ j
    have hmod : r < 2 ^ j := by
      dsimp [r]
      exact Nat.mod_lt ⌊a⌋₊ (pow_pos (by norm_num : 0 < (2 : ℕ)) j)
    have hmodle : r + 1 ≤ 2 ^ j := by omega
    have hda := Nat.div_add_mod ⌊a⌋₊ (2 ^ j)
    have hdecompR : (⌊a⌋₊ : ℝ) = ((⌊a⌋₊ / 2 ^ j : ℕ) : ℝ) * (2 : ℝ) ^ j + (r : ℝ) := by
      have hda1 : (((2 ^ j : ℕ) : ℝ) * ((⌊a⌋₊ / 2 ^ j : ℕ) : ℝ) + (r : ℝ)) = (⌊a⌋₊ : ℝ) := by
        dsimp [r]
        exact_mod_cast hda
      have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by norm_cast
      rw [hcast, ← mul_comm ((⌊a⌋₊ / 2 ^ j : ℕ) : ℝ) ((2 : ℝ) ^ j)] at hda1
      exact hda1.symm
    have hmodleR : (r : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
      have hc1 : ((r + 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hmodle
      have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by norm_cast
      rw [hcast] at hc1
      norm_num at hc1 ⊢
      exact hc1
    have hgoal : (⌊a⌋₊ : ℝ) + 1 ≤ (((⌊a⌋₊ / 2 ^ j : ℕ) : ℝ) + 1) * (2 : ℝ) ^ j := by
      nlinarith
    nlinarith

/-- When `(2:ℝ)^j ≤ δ·n`, the natural `2^j` is at most `t = ⌊δ·n⌋₊`. -/
lemma pow_two_le_floor (δ : ℝ) (n : ℕ) (hδn : 0 ≤ δ * (n : ℝ)) (j : ℕ)
    (hj : (2 : ℝ) ^ j ≤ δ * (n : ℝ)) : 2 ^ j ≤ ⌊δ * (n : ℝ)⌋₊ := by
  by_contra h
  have hlt : ⌊δ * (n : ℝ)⌋₊ < 2 ^ j := Nat.lt_of_not_ge h
  have hle1 : (⌊δ * (n : ℝ)⌋₊ + 1 : ℕ) ≤ 2 ^ j := Nat.succ_le_of_lt hlt
  have hfloor : (⌊δ * (n : ℝ)⌋₊ : ℝ) ≤ δ * (n : ℝ) ∧ δ * (n : ℝ) < (⌊δ * (n : ℝ)⌋₊ : ℝ) + 1 := by
    exact (Nat.floor_eq_iff (a := δ * (n : ℝ)) hδn).mp rfl
  have hup : δ * (n : ℝ) < (2 : ℝ) ^ j := by
    have hcast : ((⌊δ * (n : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
      exact_mod_cast hle1
    nlinarith
  linarith

end Floor

/-! ## Position prefixes -/

/-- positions `0,1,…,s-1` of `Fin n` (requires nothing of `s`) -/
def posPrefix {n : ℕ} (s : ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℕ) < s)

lemma mem_posPrefix {n s : ℕ} (i : Fin n) : i ∈ posPrefix (n := n) s ↔ (i : ℕ) < s := by
  simp [posPrefix]

lemma posPrefix_card {n s : ℕ} (hs : s ≤ n) : (posPrefix (n := n) s).card = s := by
  have hbij : (posPrefix (n := n) s).card = (Finset.range s).card := by
    refine Finset.card_bij (s := posPrefix (n := n) s) (t := Finset.range s) ?_ ?_ ?_ ?_
    · intro a ha
      exact (a : ℕ)
    · intro a ha
      exact Finset.mem_range.mpr ((mem_posPrefix a).mp ha)
    · intro a₁ ha₁ a₂ ha₂ h
      exact Fin.ext h
    · intro b hb
      have hb' : (b : ℕ) < s := Finset.mem_range.mp hb
      refine ⟨⟨(b : ℕ), lt_of_lt_of_le hb' hs⟩, ?_, rfl⟩
      exact (mem_posPrefix ⟨(b : ℕ), lt_of_lt_of_le hb' hs⟩).mpr hb'
  simpa using hbij.trans (Finset.card_range s)

lemma posPrefix_empty {n : ℕ} : posPrefix (n := n) 0 = ∅ := by
  simp [posPrefix]

lemma posPrefix_subset {n : ℕ} {s r : ℕ} (h : s ≤ r) :
    posPrefix (n := n) s ⊆ posPrefix (n := n) r := by
  intro i hi
  simp [mem_posPrefix] at hi ⊢
  exact le_trans hi h

/-! ## Top-coordinate extensions and halving chains -/

/-- `A` is a set of `top` coordinates: it dominates its complement. -/
def Dominant {n : ℕ} (x : Fin n → ℝ) (A : Finset (Fin n)) : Prop :=
  ∀ i ∈ A, ∀ j : Fin n, j ∉ A → |x j| ≤ |x i|

private lemma nat_div_div (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    (a / b) / c = a / (b * c) := by
  apply le_antisymm
  · rw [Nat.le_div_iff_mul_le (mul_pos hb hc)]
    calc ((a / b) / c) * (b * c) = ((a / b) / c) * c * b := by ac_rfl
      _ ≤ (a / b) * b := Nat.mul_le_mul_right b (Nat.div_mul_le_self (a / b) c)
      _ ≤ a := by simpa [Nat.mul_comm] using Nat.mul_div_le a b
  · rw [Nat.le_div_iff_mul_le hc]
    rw [Nat.le_div_iff_mul_le hb]
    calc (a / (b * c)) * c * b = (a / (b * c)) * (b * c) := by ac_rfl
      _ ≤ a := by simpa [Nat.mul_comm] using Nat.mul_div_le a (b * c)

/-- `top_coords_exists` relative to an ambient finite set `A`. -/
private lemma top_coords_on {n : ℕ} (A : Finset (Fin n)) (x : Fin n → ℝ) (r : ℕ)
    (hr : r ≤ A.card) :
    ∃ B : Finset (Fin n), B ⊆ A ∧ B.card = r ∧
      (∀ i ∈ B, ∀ j ∈ A, j ∉ B → |x j| ≤ |x i|) := by
  classical
  let iso : Fin (A.card) ≃o {a // a ∈ A} := Finset.orderIsoOfFin A rfl
  let emb : Fin (A.card) → Fin n := fun i => (iso i : {a // a ∈ A})
  let xA : Fin (A.card) → ℝ := fun i => x (emb i)
  rcases top_coords_exists xA r hr with ⟨J, hJc, hJdom⟩
  refine ⟨J.image emb, ?_, ?_, ?_⟩
  · -- B ⊆ A
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨i, _hi, rfl⟩
    exact (iso i).2
  · -- card
    have hinj : Function.Injective emb := by
      intro a b h
      apply (OrderIso.injective iso)
      apply Subtype.ext
      exact h
    have : (J.image emb).card = J.card := Finset.card_image_of_injective J hinj
    simpa [this, hJc]
  · -- dominance
    intro i hi j hjA hjnotB
    rcases Finset.mem_image.mp hi with ⟨i0, hi0, rfl⟩
    have hj0 : ((iso.symm ⟨j, hjA⟩ : Fin (A.card))) ∉ J := by
      intro hcontra
      apply hjnotB
      refine Finset.mem_image.mpr ⟨iso.symm ⟨j, hjA⟩, hcontra, ?_⟩
      · -- emb (iso.symm ⟨j,hjA⟩) = j
        exact congrArg (fun u : {a // a ∈ A} => (u : Fin n)) (OrderIso.apply_symm_apply iso ⟨j, hjA⟩)
    have hle := hJdom i0 hi0 (iso.symm ⟨j, hjA⟩) hj0
    have hconv1 : xA (iso.symm ⟨j, hjA⟩) = x j := by
      dsimp [xA, emb]
      congr 1
      exact congrArg (fun u : {a // a ∈ A} => (u : Fin n)) (OrderIso.apply_symm_apply iso ⟨j, hjA⟩)
    have hconv2 : xA i0 = x (emb i0) := by rfl
    simpa [hconv1, hconv2] using hle

/-- Extend a dominant set `A` to a dominant set of size `r ≥ |A|`. -/
private lemma top_extension {n : ℕ} (x : Fin n → ℝ) (A : Finset (Fin n))
    (hdom : ∀ i ∈ A, ∀ j : Fin n, j ∉ A → |x j| ≤ |x i|)
    (r : ℕ) (ha : A.card ≤ r) (hr : r ≤ n) :
    ∃ B : Finset (Fin n), A ⊆ B ∧ B.card = r ∧ Dominant x B := by
  classical
  let C : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ A
  have hCcard : C.card = n - A.card := by
    dsimp [C]
    rw [Finset.card_sdiff]
    simp
  have hC_le : r - A.card ≤ C.card := by
    rw [hCcard]
    omega
  rcases top_coords_on C x (r - A.card) hC_le with ⟨B', hB'sub, hB'c, hB'dom⟩
  refine ⟨A ∪ B', ?_, ?_, ?_⟩
  · exact Finset.subset_union_left
  · -- card A ∪ B' = r
    have hdisj : Disjoint A B' := by
      rw [Finset.disjoint_left]
      intro i hiA hiB'
      exact (Finset.mem_sdiff.mp (hB'sub hiB')).2 hiA
    have hcardu : (A ∪ B').card = A.card + B'.card := Finset.card_union_of_disjoint hdisj
    have hcardu' : A.card + (r - A.card) = r := Nat.add_sub_of_le ha
    omega
  · -- dominance
    intro i hi j hjnot
    rcases Finset.mem_union.mp hi with hiA | hiB'
    · -- i ∈ A
      exact hdom i hiA j (by
        intro hjA
        exact hjnot (Finset.mem_union_left B' hjA))
    · -- i ∈ B' ⊆ C
      have hiC : i ∈ C := hB'sub hiB'
      have hjC : j ∈ C := by
        by_contra h
        have hjA' : j ∈ A := by
          simp [C] at h
          exact h
        exact hjnot (Finset.mem_union_left B' hjA')
      have hjnotB' : j ∉ B' := by
        intro hcontra
        exact hjnot (Finset.mem_union_right A hcontra)
      exact hB'dom i hiB' j hjC hjnotB'

/-- For any `t ≤ n` the dyadic-halving nested chain of dominant sets of sizes
`t/2^j` exists. -/
private lemma exists_top_halving_chain {n : ℕ} (x : Fin n → ℝ) (t : ℕ) (ht : t ≤ n) :
    ∃ C : ℕ → Finset (Fin n),
      (∀ j : ℕ, C (j + 1) ⊆ C j) ∧
      (∀ j : ℕ, (C j).card = t / 2 ^ j) ∧
      (∀ j : ℕ, Dominant x (C j)) := by
  classical
  revert x ht
  refine Nat.strong_induction_on t ?_
  intro u ih x hu
  by_cases hu0 : u = 0
  · -- u = 0: empty chain
    refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
    · intro j
      simp
    · intro j
      simp [hu0]
    · intro j i hi e he
      simp at hi
  · -- u ≥ 1
    have hupos : 1 ≤ u := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hu0)
    let t' : ℕ := u / 2
    have ht'le : t' ≤ n := by
      dsimp [t']
      exact le_trans (Nat.div_le_self u 2) hu
    have htrec : t' < u := by
      dsimp [t']
      by_cases hu1 : u = 1
      · subst u
        norm_num
      · have h1 : 1 < u := by omega
        exact Nat.div_lt_self (n := u) (k := 2) (by omega : 0 < u) (by norm_num : 1 < 2)
    rcases ih t' htrec x ht'le with ⟨C', hC'nav, hC'card, hC'dom⟩
    have hdom0 : Dominant x (C' 0) := hC'dom 0
    have hcardC'0 : (C' 0).card = t' := by
      simpa using (hC'card 0)
    have ha : (C' 0).card ≤ u := by
      rw [hcardC'0]
      dsimp [t']
      exact Nat.div_le_self u 2
    rcases top_extension x (C' 0) hdom0 u ha hu with ⟨B, hBsup, hBcard, hBdom⟩
    let C : ℕ → Finset (Fin n) := fun j => match j with | 0 => B | j + 1 => C' j
    refine ⟨C, ?_, ?_, ?_⟩
    · -- nesting C (j+1) ⊆ C j
      intro j
      cases j with
      | zero =>
          dsimp [C]
          exact hBsup
      | succ j =>
          dsimp [C]
          exact hC'nav j
    · -- card
      intro j
      cases j with
      | zero =>
          dsimp [C]
          have hc : u / 2 ^ 0 = u := by simp
          simpa [hc] using hBcard
      | succ j =>
          dsimp [C]
          have hc0 : (C' j).card = t' / 2 ^ j := hC'card j
          have hmain : u / 2 ^ (j + 1) = t' / 2 ^ j := by
            dsimp [t']
            rw [pow_succ]
            rw [Nat.mul_comm]
            exact (nat_div_div u 2 (2 ^ j) (by norm_num) (pow_pos (by norm_num : 0 < (2:ℕ)) j)).symm
          simpa [hc0, hmain] using hC'card j
    · -- dominance
      intro j i hi e he
      cases j with
      | zero =>
          dsimp [C] at hi he ⊢
          exact hBdom i hi e he
      | succ j =>
          have thisd : Dominant x (C' j) := hC'dom j
          dsimp [C] at hi he ⊢
          exact thisd i hi e he


/-! ## The permutation family -/

/-- A chain datum: levels `0..n` (many are forced empty). -/
abbrev Chain (n : ℕ) := Fin (n + 1) → Finset (Fin n)

/-- dyadic cut size at level `j` for a chain of top size `t` -/
def levelSize (t j : ℕ) : ℕ := t / 2 ^ j

/-- validity: sizes are `t/2^j` and the sets are nested (decreasing in `j`) -/
def ValidChain {n : ℕ} (t : ℕ) (f : Chain n) : Prop :=
  (∀ j : Fin (n + 1), (f j).card = levelSize t (j : ℕ)) ∧
    (∀ j k : Fin (n + 1), (j : ℕ) ≤ (k : ℕ) → f k ⊆ f j)

/-- finite set of valid chains for given `t` -/
noncomputable def chainsFinset (n t : ℕ) : Finset (Chain n) := by
  classical
  exact (Finset.univ : Finset (Chain n)).filter (fun f : Chain n => ValidChain t f)

/-- the chosen permutation realising a valid chain (defaults to identity if
the chain is not valid) -/
noncomputable def chainRep {n : ℕ} (t : ℕ) (f : Chain n) : Equiv.Perm (Fin n) := by
  classical
  by_cases hv : ValidChain t f
  · let ht : t ≤ n := by
      have hc0 : (f ⟨0, by omega⟩).card = t / 2 ^ 0 := hv.1 ⟨0, by omega⟩
      have hc0' : (f ⟨0, by omega⟩).card = t := by simpa using hc0
      have hle : (f ⟨0, by omega⟩).card ≤ n := by
        simpa using (Finset.card_le_univ (f ⟨0, by omega⟩))
      omega
    exact Classical.choose
      (Commons.Combinatorics.Fin.exists_perm_prefix_chain (n := n) (t := t) (ht := ht) f
        (by intro j; simpa [levelSize] using hv.1 j)
        hv.2)
  · exact 1

/-- prefix property of the chosen permutation -/
lemma chainRep_prefix {n t : ℕ} {f : Chain n} (hv : ValidChain t f)
    (j : Fin (n + 1)) :
    (posPrefix (n := n) (t / 2 ^ (j : ℕ))).image (fun x : Fin n => chainRep t f x) = f j := by
  classical
  dsimp [chainRep]
  rw [dif_pos hv]
  let ht : t ≤ n := by
    have hc0 : (f ⟨0, by omega⟩).card = t / 2 ^ 0 := hv.1 ⟨0, by omega⟩
    have hc0' : (f ⟨0, by omega⟩).card = t := by simpa using hc0
    have hle : (f ⟨0, by omega⟩).card ≤ n := by
      simpa using (Finset.card_le_univ (f ⟨0, by omega⟩))
    omega
  exact Classical.choose_spec
    (Commons.Combinatorics.Fin.exists_perm_prefix_chain (n := n) (t := t) (ht := ht) f
      (by intro j; simpa [levelSize] using hv.1 j)
      hv.2) j

/-- The family: one permutation per valid chain, for every top size `t ≤ n/2`. -/
noncomputable def familyIdx (n : ℕ) : Finset (Σ t : ℕ, Chain n) :=
  (Finset.range (n / 2 + 1)).sigma (fun t : ℕ => chainsFinset n t)

noncomputable def piSet (n : ℕ) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact (familyIdx n).image (fun p : Σ t : ℕ, Chain n => chainRep p.1 p.2)

/-- an index element (with membership) yields a member of the family -/
lemma chainRep_mem_piSet {n : ℕ} {t : ℕ} {f : Chain n} (hv : ValidChain t f)
    (ht : t ≤ n / 2) : chainRep t f ∈ piSet n := by
  classical
  dsimp [piSet]
  refine Finset.mem_image.mpr ⟨⟨t, f⟩, ?_, ?_⟩
  · -- (t, f) ∈ familyIdx n
    dsimp [familyIdx]
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ht), by
      simp [chainsFinset, hv]⟩
  · rfl

/-- cardinality bound for the family -/
lemma piSet_card_le {n : ℕ} : ((piSet n).card : ℝ) ≤ (5 : ℝ) ^ n := by
  classical
  -- card (piSet n) ≤ card (familyIdx n)
  have h1nat : (piSet n).card ≤ (familyIdx n).card := by
    dsimp [piSet]
    exact Finset.card_image_le
  have h1 : ((piSet n).card : ℝ) ≤ ((familyIdx n).card : ℝ) := by exact_mod_cast h1nat
  -- card (familyIdx n) = Σ over t ∈ range (n/2+1) of card (chainsFinset n t)
  have hsig : (familyIdx n).card = ∑ t ∈ Finset.range (n / 2 + 1), (chainsFinset n t).card := by
    dsimp [familyIdx]
    exact Finset.card_sigma (Finset.range (n / 2 + 1)) (fun t : ℕ => chainsFinset n t)
  -- bound each summand
  have hstep : (∑ t ∈ Finset.range (n / 2 + 1), (chainsFinset n t).card : ℝ) ≤
      ∑ t ∈ Finset.range (n / 2 + 1), (n.choose t : ℝ) * (4 : ℝ) ^ t := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have ht' : t ≤ n := by
      exact le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) (Nat.div_le_self n 2)
    have hb := Commons.Combinatorics.Fin.nested_chain_card_bound (n := n) (t := t) ht'
    simpa [chainsFinset, ValidChain, levelSize] using hb
  have hcards : (∑ t ∈ Finset.range (n / 2 + 1), (chainsFinset n t).card : ℝ) = ((familyIdx n).card : ℝ) := by
    exact_mod_cast hsig.symm
  have hhalf : (∑ t ∈ Finset.range (n / 2 + 1), (n.choose t : ℝ) * (4 : ℝ) ^ t) ≤
      (∑ t ∈ Finset.range (n + 1), (n.choose t : ℝ) * (4 : ℝ) ^ t) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro t ht
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp ht) (Nat.succ_le_succ (Nat.div_le_self n 2)))
    · intro t ht' htnot
      exact mul_nonneg (by positivity : 0 ≤ (n.choose t : ℝ)) (pow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) t)
  have hfull : (∑ t ∈ Finset.range (n + 1), (n.choose t : ℝ) * (4 : ℝ) ^ t) = (5 : ℝ) ^ n :=
    Commons.Combinatorics.Fin.sum_choose_pow_four (n := n)
  calc
    ((piSet n).card : ℝ) ≤ ((familyIdx n).card : ℝ) := h1
    _ = (∑ t ∈ Finset.range (n / 2 + 1), (chainsFinset n t).card : ℝ) := hcards.symm
    _ ≤ (∑ t ∈ Finset.range (n / 2 + 1), (n.choose t : ℝ) * (4 : ℝ) ^ t) := hstep
    _ ≤ (∑ t ∈ Finset.range (n + 1), (n.choose t : ℝ) * (4 : ℝ) ^ t) := hhalf
    _ = (5 : ℝ) ^ n := hfull

/-- the family is nonempty -/
lemma piSet_nonempty (n : ℕ) : (piSet n).Nonempty := by
  classical
  let f : Chain n := fun _ => ∅
  have hvalid : ValidChain 0 f := by
    constructor
    · intro j
      simp [f, ValidChain, levelSize]
    · intro j k hjk
      simp [f, ValidChain, levelSize]
  exact ⟨chainRep 0 f, chainRep_mem_piSet hvalid (by simp)⟩


/-! ## The main theorem -/

/-- `(n:ℝ)/2 < ((n/2:ℕ):ℝ)+1` -/
private lemma n_lt_two_mul_half_add (n : ℕ) : (n : ℝ) / 2 < ((n / 2 : ℕ) : ℝ) + 1 := by
  have h2 : n < (n / 2 + 1) * 2 := by
    have hmod : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hdiv : n = (n / 2) * 2 + n % 2 := by
      have hd := Nat.div_add_mod n 2
      have hd' : n = 2 * (n / 2) + n % 2 := hd.symm
      rw [Nat.mul_comm] at hd'
      exact hd'
    omega
  have h2r : (n : ℝ) < (((n / 2 + 1 : ℕ) : ℝ) * (2 : ℝ)) := by exact_mod_cast h2
  have hcast : ((n / 2 + 1 : ℕ) : ℝ) = ((n / 2 : ℕ) : ℝ) + 1 := by norm_cast
  rw [hcast] at h2r
  nlinarith

/-- half-size bound for `t = ⌊δ·n⌋₊` when `δ ≤ 1/2` -/
private lemma floor_mul_half_le {n : ℕ} (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ12 : δ ≤ 1 / 2) :
    ⌊δ * (n : ℝ)⌋₊ ≤ n / 2 := by
  by_contra h
  have hgt : n / 2 < ⌊δ * (n : ℝ)⌋₊ := Nat.lt_of_not_ge h
  have hgtR : ((n / 2 : ℕ) : ℝ) + 1 ≤ (⌊δ * (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hgt)
  have hfl : (⌊δ * (n : ℝ)⌋₊ : ℝ) ≤ δ * (n : ℝ) :=
    Nat.floor_le (mul_nonneg hδ0 (by positivity : 0 ≤ (n : ℝ)))
  have hδn : δ * (n : ℝ) ≤ (n : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_right hδ12 (by positivity : 0 ≤ (n : ℝ))
    linarith
  have hhalf : (n : ℝ) / 2 < ((n / 2 : ℕ) : ℝ) + 1 := n_lt_two_mul_half_add n
  nlinarith

/-- `n+1 ≤ 2^(n+1)` -/
private lemma n_add_one_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n + 2 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 2) := by
          conv_rhs => rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          rw [Nat.mul_comm]

/-- `n/2 < 2^(n+1)` -/
private lemma half_lt_two_pow (n : ℕ) : n / 2 < 2 ^ (n + 1) := by
  have h1 : n / 2 + 1 ≤ n + 1 := by omega
  have h2 : n + 1 ≤ 2 ^ (n + 1) := n_add_one_le_two_pow n
  have h3 : n / 2 + 1 ≤ 2 ^ (n + 1) := le_trans h1 h2
  omega

/-- nesting over all pairs of naturals from consecutive nesting -/
private lemma chain_sub_of_le {n : ℕ} {C : ℕ → Finset (Fin n)}
    (h : ∀ m : ℕ, C (m + 1) ⊆ C m) {j k : ℕ} (hjk : j ≤ k) : C k ⊆ C j := by
  classical
  induction k generalizing j with
  | zero =>
      have : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst j
      exact subset_rfl
  | succ k ih =>
      by_cases hjk' : j ≤ k
      · exact subset_trans (h k) (ih hjk')
      · have : j = k + 1 := by omega
        subst j
        exact subset_rfl

/-- levels `j` with `2^j ≤ t` are below `n+1` when `t ≤ n/2` -/
private lemma level_lt_of_pow_two {n t j : ℕ} (ht : t ≤ n / 2) (h2 : 2 ^ j ≤ t) :
    j < n + 1 := by
  have hb : 2 ^ j ≤ n / 2 := le_trans h2 ht
  by_contra h
  have hj : n + 1 ≤ j := Nat.le_of_not_gt h
  have hp : 2 ^ (n + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
  have hpb : 2 ^ (n + 1) ≤ n / 2 := le_trans hp hb
  have hsmall : n / 2 < 2 ^ (n + 1) := half_lt_two_pow n
  omega

theorem perm_family_top_coords :
    ∃ CPerm : ℝ, 1 ≤ CPerm ∧
    ∀ (n : ℕ) (hn : 2 ≤ n), ∃ PiSet : Finset (Equiv.Perm (Fin n)),
      (PiSet.card : ℝ) ≤ CPerm ^ n ∧
      ∀ (x : Fin n → ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 / 2 →
        ∃ σ : Equiv.Perm (Fin n), σ ∈ PiSet ∧
          ∀ (j : ℕ), (2 : ℝ) ^ j ≤ δ * (n : ℝ) →
            (let k : ℕ := (⌊δ * (n : ℝ) / (2 : ℝ) ^ j⌋₊);
             ∀ ⦃a b : Fin n⦄, (a : ℕ) < k → k ≤ (b : ℕ) → |x (σ b)| ≤ |x (σ a)|) := by
  classical
  refine ⟨(5 : ℝ), by norm_num, ?_⟩
  intro n hn
  refine ⟨piSet n, piSet_card_le (n := n), ?_⟩
  intro x δ hδ0 hδ12
  let t : ℕ := ⌊δ * (n : ℝ)⌋₊
  have hδn0 : 0 ≤ δ * (n : ℝ) := mul_nonneg (le_of_lt hδ0) (by positivity : 0 ≤ (n : ℝ))
  by_cases ht0 : t = 0
  · -- δ·n < 1 : no level satisfies the premise
    rcases piSet_nonempty n with ⟨σ, hσ⟩
    refine ⟨σ, hσ, ?_⟩
    intro j hj
    exfalso
    have hf := (Nat.floor_eq_iff (a := δ * (n : ℝ)) hδn0).mp ht0
    have hlt : δ * (n : ℝ) < 1 := by
      simpa using hf.2
    have hge : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ)) (n := j)
    linarith
  · -- t ≥ 1
    have ht_le_half : t ≤ n / 2 := by
      dsimp [t]
      exact floor_mul_half_le δ (le_of_lt hδ0) hδ12
    have ht_le_n : t ≤ n := le_trans ht_le_half (Nat.div_le_self n 2)
    rcases exists_top_halving_chain x t ht_le_n with ⟨C, hCnav, hCcard, hCdom⟩
    let f : Chain n := fun jj : Fin (n + 1) => C (jj : ℕ)
    have hfv : ValidChain t f := by
      constructor
      · intro jj
        dsimp [f]
        exact hCcard (jj : ℕ)
      · intro jj kk hjk
        dsimp [f]
        exact chain_sub_of_le hCnav hjk
    let σ : Equiv.Perm (Fin n) := chainRep t f
    have hσmem : σ ∈ piSet n := by
      dsimp [σ]
      exact chainRep_mem_piSet hfv ht_le_half
    refine ⟨σ, hσmem, ?_⟩
    intro j hj
    have htwo : 2 ^ j ≤ t := pow_two_le_floor δ n hδn0 j hj
    have hk : (⌊δ * (n : ℝ) / (2 : ℝ) ^ j⌋₊ : ℕ) = t / 2 ^ j := by
      dsimp [t]
      exact floor_div_pow (δ * (n : ℝ)) hδn0 j
    have hj_lt : j < n + 1 := level_lt_of_pow_two ht_le_half htwo
    let jj : Fin (n + 1) := ⟨j, hj_lt⟩
    dsimp
    rw [hk]
    intro a b ha hb
    have hpfx : (posPrefix (n := n) (t / 2 ^ j)).image (fun y : Fin n => σ y) = C j := by
      have h := chainRep_prefix hfv jj
      dsimp [σ, jj] at h ⊢
      simpa using h
    have hσa : σ a ∈ C j := by
      have hamem : a ∈ posPrefix (n := n) (t / 2 ^ j) := (mem_posPrefix a).mpr ha
      rw [← hpfx]
      exact Finset.mem_image.mpr ⟨a, hamem, rfl⟩
    have hσb : σ b ∉ C j := by
      intro hbC
      rw [← hpfx] at hbC
      rcases Finset.mem_image.mp hbC with ⟨b', hb'mem, hσb'⟩
      have hbb' : b = b' := Equiv.injective σ hσb'.symm
      have hb'lt : (b' : ℕ) < t / 2 ^ j := (mem_posPrefix b').mp hb'mem
      omega
    exact hCdom j (σ a) hσa (σ b) hσb

end Commons.LinearAlgebra.Net
