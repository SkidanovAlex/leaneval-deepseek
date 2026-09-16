import Submission.ZagierHoffmanProof.StepL200
import Submission.ZagierHoffmanProof.StepL197

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step L203: Theorem B over `F₂`

When `|F| = 2` the entry bound `< q = 2` forces every entry to be `1`, so

  `𝒯0 F w = {ζ_A(1,…,1)}`   (depth `w`),

a *singleton*; and `ζ_A(1,…,1) ≠ 0` (StepL199/L200).  Hence Theorem B holds for **every** weight
`w` over `F₂`.  The general Theorems B/D remain ABP-gated.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The all-ones tuple of depth `r` (independent of `F`). -/
noncomputable def onesTuple (r : ℕ) : Fin r → ℕ+ := fun _ => oneExp

/-- Every entry of `onesTuple r` is `1`. -/
lemma onesTuple_apply (r : ℕ) (i : Fin r) : (onesTuple r i : ℕ) = 1 := rfl

/-- `weight r (onesTuple r) = r`. -/
lemma weight_onesTuple (r : ℕ) : weight r (onesTuple r) = r := by
  rw [weight]
  simp only [onesTuple]
  rw [show (oneExp : ℕ) = 1 from rfl]
  simp

/-- `onesTuple w` has weight `w`. -/
lemma onesTuple_mem_𝔖 (w : ℕ) : onesTuple w ∈ 𝔖_w w w := by
  have h : weight w (onesTuple w) = w := weight_onesTuple w
  exact (𝔖_w_mem_iff w w (onesTuple w)).mpr h

/-- Over a two-element field the only positive entry below `q` is `1`. -/
lemma eq_oneExp_of_lt_card_two {n : ℕ+} (h : (n : ℕ) < Nat.card F) (h2 : Nat.card F = 2) :
    n = oneExp := by
  apply Subtype.ext
  show (n : ℕ) = (oneExp : ℕ)
  have hn : 1 ≤ (n : ℕ) := n.pos
  have h1 : (oneExp : ℕ) = 1 := rfl
  rw [h1]
  omega

/-- Two tuples of all ones are equal (after identifying the arities). -/
lemma zeta_eq_onesTuple_of_all_one {r w : ℕ} (𝔰 : Fin r → ℕ+)
    (h𝔖 : 𝔰 ∈ 𝔖_w w r) (hones : ∀ i, 𝔰 i = oneExp) :
    ζ_A F 𝔰 = ζ_A F (onesTuple w) := by
  have hw : r = w := by
    have h1 : weight r 𝔰 = w := (𝔖_w_mem_iff w r 𝔰).mp h𝔖
    rw [← h1, show 𝔰 = onesTuple r from funext hones, weight_onesTuple]
  subst hw
  rw [show 𝔰 = onesTuple r from funext hones]

/-! ## `𝒯0 F w` over `F₂` -/

/-- Forward inclusion: any element of `𝒯0 F w` over `F₂` is `ζ_A(1,…,1)`. -/
lemma T0_card_two_subset (h2 : Nat.card F = 2) (w : ℕ) (r : ℕ+) :
    (𝒯0_aux F w r : Set (RatFunc.CompletionAtInfty F)) ⊆ {ζ_A F (onesTuple w)} := by
  intro x hx
  rw [mem_𝒯0_aux_iff F w r] at hx
  obtain ⟨𝔰, h𝔖, hall, rfl⟩ := hx
  exact Set.mem_singleton_iff.mpr (zeta_eq_onesTuple_of_all_one F 𝔰 h𝔖
    (fun i => eq_oneExp_of_lt_card_two F (hall i) h2))

/-- `ζ_A(1,…,1) ∈ 𝒯0 F w` over `F₂`. -/
lemma onesTuple_mem_T0_aux (h2 : Nat.card F = 2) (w : ℕ) (hw : 1 ≤ w) :
    ζ_A F (onesTuple w) ∈ 𝒯0_aux F w ⟨w, by omega⟩ := by
  rw [mem_𝒯0_aux_iff F w ⟨w, by omega⟩]
  refine ⟨onesTuple w, onesTuple_mem_𝔖 w, ?_, rfl⟩
  intro i
  have hi : (onesTuple w i : ℕ) = 1 := rfl
  rw [hi, h2]
  norm_num

/-- ★ Over `F₂`, `𝒯0 F w` is the singleton `{ζ_A(1,…,1)}`. -/
theorem T0_card_two_eq (h2 : Nat.card F = 2) (w : ℕ) (hw : 1 ≤ w) :
    𝒯0 F w = ({ζ_A F (onesTuple w)} : Set (RatFunc.CompletionAtInfty F)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_𝒯0_iff F w] at hx
    obtain ⟨r, hr⟩ := hx
    exact T0_card_two_subset F h2 w r hr
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, mem_𝒯0_iff F w]
    exact ⟨⟨w, by omega⟩, onesTuple_mem_T0_aux F h2 w hw⟩

/-- `ncard (𝒯0 F w) = 1` over `F₂`. -/
theorem ncard_T0_card_two (h2 : Nat.card F = 2) (w : ℕ) (hw : 1 ≤ w) :
    Set.ncard (𝒯0 F w) = 1 := by
  rw [T0_card_two_eq F h2 w hw]
  exact Set.ncard_singleton _

/-- The unique element of `𝒯0 F w` over `F₂` is `ζ_A(1,…,1)`. -/
lemma coe_T0_card_two (h2 : Nat.card F = 2) (w : ℕ) (hw : 1 ≤ w) (i : 𝒯0 F w) :
    (i : RatFunc.CompletionAtInfty F) = ζ_A F (onesTuple w) := by
  simpa only [T0_card_two_eq F h2 w hw, Set.mem_singleton_iff] using i.2

/-- The index type `↥(𝒯0 F w)` is a subsingleton over `F₂`. -/
lemma subsingleton_T0_card_two (h2 : Nat.card F = 2) (w : ℕ) (hw : 1 ≤ w) :
    Subsingleton (𝒯0 F w) :=
  ⟨fun a b => Subtype.ext (by rw [coe_T0_card_two F h2 w hw a, coe_T0_card_two F h2 w hw b])⟩

/-- `ζ_A(1,…,1) ∈ 𝒵 F w`. -/
lemma ones_mem_Z (w : ℕ) (hw : 1 ≤ w) : ζ_A F (onesTuple w) ∈ 𝒵 F w := by
  refine ζ_A_weight_subset_span F w w ?_
  rw [ζ_A_weight_mem_iff F w w]
  exact ⟨onesTuple w, weight_onesTuple w, rfl⟩

/-- `ζ_A(1,…,1) ≠ 0` (no hypothesis on `|F|`). -/
lemma zeta_onesTuple_ne_zero (w : ℕ) (hw : 1 ≤ w) : ζ_A F (onesTuple w) ≠ 0 :=
  zeta_ones_ne_zero F w (by omega)

/-- Over `F₂` the index type `↥(𝒯0 F w)` is linearly independent. -/
theorem linearIndependent_T0_card_two (h2 : Nat.card F = 2) (w : ℕ) (hw : 1 ≤ w) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F w → RatFunc.CompletionAtInfty F) := by
  haveI : Subsingleton (𝒯0 F w) := subsingleton_T0_card_two F h2 w hw
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hsing : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hi, fun j _ => Subsingleton.elim j i⟩
  rw [hsing, Finset.sum_singleton] at hsum
  rcases smul_eq_zero.mp hsum with h | h
  · exact h
  · exact absurd h (by rw [coe_T0_card_two F h2 w hw i]; exact zeta_onesTuple_ne_zero F w hw)

/-- `𝒵 F w` has positive rank (`w ≥ 1`). -/
theorem rank_Z_ones_pos (w : ℕ) (hw : 1 ≤ w) : 0 < Module.rank (RatFunc F) (𝒵 F w) := by
  rw [rank_pos_iff_exists_ne_zero]
  exact ⟨⟨ζ_A F (onesTuple w), ones_mem_Z F w hw⟩, fun h =>
    zeta_onesTuple_ne_zero F w hw (Subtype.ext_iff.mp h)⟩

/-- ★★ THEOREM B over `F₂`: for every weight `w ≥ 1` the MZVs in `𝒯0 F w` are linearly
independent over `K` and `dim_K 𝒵 F w ≥ |𝒯0 F w|`. -/
theorem theorem_B_card_two (h2 : Nat.card F = 2) (w : ℕ) (hw : 1 ≤ w) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F w → RatFunc.CompletionAtInfty F) ∧
      Module.rank (RatFunc F) (𝒵 F w) ≥ Set.ncard (𝒯0 F w) := by
  refine ⟨linearIndependent_T0_card_two F h2 w hw, ?_⟩
  rw [ncard_T0_card_two F h2 w hw]
  exact Cardinal.one_le_iff_ne_zero.mpr (ne_of_gt (rank_Z_ones_pos F w hw))


/-! ## `𝒯 F 2` over `F₂` (Theorem D in the range `w ≤ 2`) -/

/-- `onesTuple r` has entries `< q` over `F₂`. -/
lemma onesTuple_lt_card_two (h2 : Nat.card F = 2) (r : ℕ) (i : Fin r) :
    (onesTuple r i : ℕ) < Nat.card F := by
  have h : (onesTuple r i : ℕ) = 1 := rfl
  rw [h, h2]
  norm_num

/-- Over `F₂`, every element of `𝒯_aux F 2 r` already has all entries `< 2`, i.e. lies in
`𝒯0_aux F 2 r`.  (An entry equal to `2` would exhaust the weight and force `r = 1`, whence that
entry would be the last one, contradicting the defining bound `< 2`.) -/
lemma T_two_card_two_subset_T0 (h2 : Nat.card F = 2) (r : ℕ+) :
    (𝒯_aux F 2 r : Set (RatFunc.CompletionAtInfty F)) ⊆ (𝒯0_aux F 2 r : Set _) := by
  intro x hx
  rw [mem_𝒯_aux_iff F 2 r] at hx
  obtain ⟨𝔰, h𝔖, hle, hlast, rfl⟩ := hx
  rw [mem_𝒯0_aux_iff F 2 r]
  refine ⟨𝔰, h𝔖, fun i => ?_, rfl⟩
  by_contra hcon
  have hcon' : (2 : ℕ) ≤ (𝔰 i : ℕ) := by
    have h := not_lt.mp hcon
    rwa [h2] at h
  have hweight : (∑ j : Fin (↑r), (𝔰 j : ℕ)) = 2 := (𝔖_w_mem_iff 2 (↑r) 𝔰).mp h𝔖
  have hi2 : (𝔰 i : ℕ) = 2 := by
    have h := pnat_entry_le_sum (↑r) 𝔰 i
    rw [hweight] at h
    omega
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin (↑r)))
    (fun j => (𝔰 j : ℕ)) (Finset.mem_univ i)
  rw [hweight] at hsplit
  have herase : (∑ j ∈ (Finset.univ.erase i), (𝔰 j : ℕ)) = 0 := by omega
  have hsub : (Finset.univ : Finset (Fin (↑r))) ⊆ {i} := by
    intro j _
    by_contra hji
    have hji' : j ≠ i := fun h => hji (by rw [Finset.mem_singleton]; exact h)
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji', Finset.mem_univ j⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le _)).mp herase j hmem
    have hp : 1 ≤ (𝔰 j : ℕ) := (𝔰 j).pos
    omega
  have hcard : (↑r : ℕ) ≤ 1 := by
    have h := Finset.card_le_card hsub
    simpa using h
  have hlast' : (𝔰 ⟨↑r - 1, by have := r.pos; omega⟩ : ℕ) < Nat.card F := hlast
  have hmem := hsub (Finset.mem_univ (⟨↑r - 1, by have := r.pos; omega⟩ : Fin (↑r)))
  rw [Finset.mem_singleton] at hmem
  rw [hmem] at hlast'
  rw [h2] at hlast'
  omega

/-- `ζ_A(1,1) ∈ 𝒯 F 2` over `F₂`. -/
lemma onesTuple_mem_T_aux_two (h2 : Nat.card F = 2) :
    ζ_A F (onesTuple 2) ∈ 𝒯_aux F 2 ⟨2, by norm_num⟩ := by
  rw [mem_𝒯_aux_iff F 2 ⟨2, by norm_num⟩]
  refine ⟨onesTuple 2, onesTuple_mem_𝔖 2, ?_, ?_, rfl⟩
  · intro i _
    exact le_of_lt (onesTuple_lt_card_two F h2 2 i)
  · exact onesTuple_lt_card_two F h2 2 _

/-- ★ Over `F₂`, `𝒯 F 2` is the singleton `{ζ_A(1,1)}`. -/
theorem T_two_card_two_eq (h2 : Nat.card F = 2) :
    𝒯 F 2 = ({ζ_A F (onesTuple 2)} : Set (RatFunc.CompletionAtInfty F)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [mem_𝒯_iff F 2] at hx
    obtain ⟨r, hr⟩ := hx
    have h0 : x ∈ 𝒯0 F 2 := by
      rw [mem_𝒯0_iff F 2]
      exact ⟨r, T_two_card_two_subset_T0 F h2 r hr⟩
    rwa [T0_card_two_eq F h2 2 (by norm_num)] at h0
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx, mem_𝒯_iff F 2]
    exact ⟨⟨2, by norm_num⟩, onesTuple_mem_T_aux_two F h2⟩

/-- `ncard (𝒯 F 2) = 1` over `F₂`. -/
theorem ncard_T_card_two_two (h2 : Nat.card F = 2) : Set.ncard (𝒯 F 2) = 1 := by
  rw [T_two_card_two_eq F h2]
  exact Set.ncard_singleton _

/-- The unique element of `𝒯 F 2` over `F₂` is `ζ_A(1,1)`. -/
lemma coe_T_card_two_two (h2 : Nat.card F = 2) (i : 𝒯 F 2) :
    (i : RatFunc.CompletionAtInfty F) = ζ_A F (onesTuple 2) := by
  simpa only [T_two_card_two_eq F h2, Set.mem_singleton_iff] using i.2

/-- `d F 2 = 1` when `|F| = 2`. -/
lemma d_two_card_two (h2 : Nat.card F = 2) : d F 2 = 1 := by
  rw [d]
  rw [if_neg (by norm_num : ¬ (2 = 0))]
  rw [if_neg (by omega : ¬ (2 ≤ Nat.card F - 1))]
  rw [if_pos (by omega : 2 = Nat.card F)]
  norm_num

/-- Over `F₂` the index type `↥(𝒯 F 2)` is linearly independent. -/
theorem linearIndependent_T_card_two_two (h2 : Nat.card F = 2) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F 2 → RatFunc.CompletionAtInfty F) := by
  haveI : Subsingleton (𝒯 F 2) :=
    ⟨fun a b => Subtype.ext (by rw [coe_T_card_two_two F h2 a, coe_T_card_two_two F h2 b])⟩
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have hsing : s = {i} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hi, fun j _ => Subsingleton.elim j i⟩
  rw [hsing, Finset.sum_singleton] at hsum
  rcases smul_eq_zero.mp hsum with h | h
  · exact h
  · exact absurd h (by rw [coe_T_card_two_two F h2 i]
                       exact zeta_onesTuple_ne_zero F 2 (by norm_num))

/-- ★★ THEOREM D over `F₂` at weight `2`: `𝒯 F 2` is a `K`-basis of `𝒵 F 2` and
`dim_K 𝒵 F 2 = d F 2 = 1`. -/
theorem theorem_D_card_two_two (h2 : Nat.card F = 2) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F 2 → RatFunc.CompletionAtInfty F) ∧
      Module.rank (RatFunc F) (𝒵 F 2) = d F 2 := by
  refine ⟨linearIndependent_T_card_two_two F h2, ?_⟩
  have hle : Module.rank (RatFunc F) (𝒵 F 2) ≤ d F 2 := (theorem_A_amb F 2).2
  refine le_antisymm hle ?_
  rw [d_two_card_two F h2]
  exact Cardinal.one_le_iff_ne_zero.mpr (ne_of_gt (rank_Z_ones_pos F 2 (by norm_num)))

/-- ★★ THEOREM D over `F₂`, in the full range `w ≤ 2 = 2q - 2` of its hypothesis. -/
theorem theorem_D_card_two (h2 : Nat.card F = 2) (w : ℕ+) (hw : (w : ℕ) ≤ 2 * Nat.card F - 2) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F w → RatFunc.CompletionAtInfty F) ∧
      Module.rank (RatFunc F) (𝒵 F w) = d F w := by
  rw [h2] at hw
  have hwp : 1 ≤ (w : ℕ) := w.pos
  have hcases : (w : ℕ) = 1 ∨ (w : ℕ) = 2 := by omega
  rcases hcases with h | h
  · have hw1 : w = (⟨1, by norm_num⟩ : ℕ+) := Subtype.ext h
    subst hw1
    exact theorem_D_one F
  · have hw2 : w = (⟨2, by norm_num⟩ : ℕ+) := Subtype.ext h
    subst hw2
    exact theorem_D_card_two_two F h2

/-! ## Non-vanishing of the spanning sets and non-triviality of the weight pieces

These do not need `|F| = 2`: every element of `𝒯 w` (resp. `𝒯0 w`) is an MZV with all entries
`≤ q`, hence nonzero (StepL199), and `𝒵 w` always contains the nonzero `ζ_A(1,…,1)`. -/

/-- ★ Every element of `𝒯 F w` is a nonzero MZV. -/
theorem T_ne_zero {w : ℕ} {x : RatFunc.CompletionAtInfty F} (hx : x ∈ 𝒯 F w) : x ≠ 0 := by
  rw [mem_𝒯_iff F w] at hx
  obtain ⟨r, hr⟩ := hx
  rw [mem_𝒯_aux_iff F w r] at hr
  obtain ⟨𝔰, h𝔖, hle, hlast, rfl⟩ := hr
  refine zeta_entries_le_card_ne_zero F (r := ↑r) r.pos 𝔰 (fun j => ?_)
  have hjle : (j : ℕ) ≤ (r : ℕ) - 1 := by have := j.2; have := r.pos; omega
  rcases lt_or_eq_of_le hjle with h | h
  · exact hle j h
  · have hfin : j = ⟨(r : ℕ) - 1, by have := r.pos; omega⟩ := Fin.ext h
    have hval : (𝔰 j : ℕ) = (𝔰 ⟨(r : ℕ) - 1, by have := r.pos; omega⟩ : ℕ) :=
      congrArg (fun k => (𝔰 k : ℕ)) hfin
    rw [hval]
    exact le_of_lt hlast

/-- ★ Every element of `𝒯0 F w` is a nonzero MZV. -/
theorem T0_ne_zero {w : ℕ} {x : RatFunc.CompletionAtInfty F} (hx : x ∈ 𝒯0 F w) : x ≠ 0 := by
  rw [mem_𝒯0_iff F w] at hx
  obtain ⟨r, hr⟩ := hx
  rw [mem_𝒯0_aux_iff F w r] at hr
  obtain ⟨𝔰, h𝔖, hall, rfl⟩ := hr
  exact zeta_entries_le_card_ne_zero F (r := ↑r) r.pos 𝔰 fun j => le_of_lt (hall j)

/-- ★★ Every weight-`w` zeta space `𝒵 F w` (`w ≥ 1`) is nonzero: it contains the nonzero
`ζ_A(1,…,1)` of weight and depth `w`. -/
theorem Z_ne_bot (w : ℕ) (hw : 1 ≤ w) :
    𝒵 F w ≠ (⊥ : Submodule (RatFunc F) (RatFunc.CompletionAtInfty F)) := by
  intro hbot
  have hmem := ones_mem_Z F w hw
  rw [hbot] at hmem
  exact zeta_onesTuple_ne_zero F w hw (by simpa using hmem)

/-- ★★ Every weight-`w` zeta space has positive `K`-rank (`w ≥ 1`). -/
theorem rank_Z_pos (w : ℕ) (hw : 1 ≤ w) : 0 < Module.rank (RatFunc F) (𝒵 F w) :=
  rank_pos_iff_exists_ne_zero.mpr
    ⟨⟨ζ_A F (onesTuple w), ones_mem_Z F w hw⟩, fun h =>
      zeta_onesTuple_ne_zero F w hw (Subtype.ext_iff.mp h)⟩

end ZagierHoffmanPositiveChar
