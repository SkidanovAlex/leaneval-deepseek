import Mathlib
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.mem_winRho_range_iff
import Submission.Work.OROneRel.band_of_winE_decor
import Submission.Work.OROneRel.band_reduce
import Submission.Work.OROneRel.band_extreme_lo
import Submission.Work.OROneRel.band_levels_between
import Submission.Work.OROneRel.decor_invRev
import Submission.Work.OROneRel.decor_winE_of_red
import Submission.Work.OROneRel.winE_decor_of_band
import Submission.Work.OROneRel.twoLetter_generation
import Submission.Work.OROneRel.gaugeExclDefs

/-!
# The loop subgroups of the `ℤ`-cover attached to an edge set

`belowE c M` / `aboveE c M` are the edge sets of the half-planes of levels `≤ M` / `≥ M`, and
`loopsInE c E` is the subgroup of `FreeGroup α` of the loops whose *reduced* walk uses only edges of
`E`.  Since free reduction only deletes levels of the walk (`decor_sublist_of_red`), this is the same
as asking for the existence of *some* word representing the element with all decorated edges in `E`
(`mem_loopsInE_iff`); the canonical reduced description makes the intersection of two such subgroups
the subgroup of the intersection of the two edge sets (`loopsInE_inf`), which is the
"Mayer--Vietoris" input of the two-letter band splitting.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## Level bounds of a word -/

/-- **All levels of the walk of `L` are `≤ M`.** -/
def levLe (c : α → ℤ) (M : ℤ) (L : List (α × Bool)) : Prop :=
  ∀ k ≤ L.length, lsig c (L.take k) ≤ M

/-- **All levels of the walk of `L` are `≥ M`.** -/
def levGe (c : α → ℤ) (M : ℤ) (L : List (α × Bool)) : Prop :=
  ∀ k ≤ L.length, M ≤ lsig c (L.take k)

theorem levLe_mono {c : α → ℤ} {M M' : ℤ} {L : List (α × Bool)} (h : levLe c M L)
    (hM : M ≤ M') : levLe c M' L := fun k hk => le_trans (h k hk) hM

theorem levGe_mono {c : α → ℤ} {M M' : ℤ} {L : List (α × Bool)} (h : levGe c M L)
    (hM : M' ≤ M) : levGe c M' L := fun k hk => le_trans hM (h k hk)

theorem levLe_nil {c : α → ℤ} {M : ℤ} : levLe c M [] ↔ 0 ≤ M := by
  constructor
  · intro h; simpa [lsig] using h 0 (Nat.zero_le 0)
  · intro h k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simpa [lsig] using h

theorem levGe_nil {c : α → ℤ} {M : ℤ} : levGe c M [] ↔ M ≤ 0 := by
  constructor
  · intro h; simpa [lsig] using h 0 (Nat.zero_le 0)
  · intro h k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simpa [lsig] using h

theorem levLe_append {c : α → ℤ} {M : ℤ} {A B : List (α × Bool)}
    (hA : levLe c M A) (hB : levLe c (M - lsig c A) B) : levLe c M (A ++ B) := by
  intro k hk
  rw [List.take_append]
  have hk' : k - A.length ≤ B.length := by
    simp only [List.length_append] at hk; omega
  by_cases h : k ≤ A.length
  · have h0 : k - A.length = 0 := Nat.sub_eq_zero_of_le h
    rw [h0, List.take_zero, List.append_nil]
    exact hA k h
  · have hle : A.length ≤ k := le_of_lt (not_le.mp h)
    rw [List.take_of_length_le hle, lsig_append]
    have := hB (k - A.length) hk'
    linarith

theorem levGe_append {c : α → ℤ} {M : ℤ} {A B : List (α × Bool)}
    (hA : levGe c M A) (hB : levGe c (M - lsig c A) B) : levGe c M (A ++ B) := by
  intro k hk
  rw [List.take_append]
  have hk' : k - A.length ≤ B.length := by
    simp only [List.length_append] at hk; omega
  by_cases h : k ≤ A.length
  · have h0 : k - A.length = 0 := Nat.sub_eq_zero_of_le h
    rw [h0, List.take_zero, List.append_nil]
    exact hA k h
  · have hle : A.length ≤ k := le_of_lt (not_le.mp h)
    rw [List.take_of_length_le hle, lsig_append]
    have := hB (k - A.length) hk'
    linarith

/-! ## Free reduction of the words of the free group -/

theorem red_wordOf_mul (x y : FreeGroup α) :
    FreeGroup.Red (wordOf x ++ wordOf y) (wordOf (x * y)) := by
  classical
  have h0 : FreeGroup.mk (wordOf x) * FreeGroup.mk (wordOf y) =
      FreeGroup.mk (wordOf (x * y)) := by
    rw [mk_wordOf, mk_wordOf, mk_wordOf]
  have h : FreeGroup.mk (wordOf x ++ wordOf y) = FreeGroup.mk (wordOf (x * y)) := by
    rw [← FreeGroup.mul_mk]; exact h0
  have h1 := FreeGroup.reduce.red (L := wordOf x ++ wordOf y)
  have h2 : FreeGroup.reduce (wordOf x ++ wordOf y) = wordOf (x * y) := by
    have h3 := FreeGroup.reduce.sound h
    have h4 : FreeGroup.reduce (wordOf (x * y)) = wordOf (x * y) := by
      rw [wordOf]
      exact FreeGroup.reduce_toWord (x * y)
    rwa [h4] at h3
  rwa [h2] at h1

theorem red_wordOf_inv (x : FreeGroup α) :
    FreeGroup.Red (FreeGroup.invRev (wordOf x)) (wordOf x⁻¹) := by
  classical
  have h : FreeGroup.mk (FreeGroup.invRev (wordOf x)) = FreeGroup.mk (wordOf x⁻¹) := by
    rw [← FreeGroup.inv_mk, mk_wordOf, mk_wordOf]
  have h1 := FreeGroup.reduce.red (L := FreeGroup.invRev (wordOf x))
  have h2 : FreeGroup.reduce (FreeGroup.invRev (wordOf x)) = wordOf x⁻¹ := by
    have h3 := FreeGroup.reduce.sound h
    have h4 : FreeGroup.reduce (wordOf x⁻¹) = wordOf x⁻¹ := by
      rw [wordOf]
      exact FreeGroup.reduce_toWord x⁻¹
    rwa [h4] at h3
  rwa [h2] at h1

/-- **The decoration of the inverse word**, at level `0`, for a *loop* `x`: it is the reverse of
the decoration of `x` with the letters flipped (so the *edge* `coverEdge` of each decorated letter is
the same one, traversed backwards). -/
theorem decor_invRev_wordOf {c : α → ℤ} {x : FreeGroup α} (hx : cohom c x = 1) :
    decor c 0 (FreeGroup.invRev (wordOf x))
      = ((decor c 0 (wordOf x)).reverse.map (fun p => (p.1, !p.2))) := by
  have hls : lsig c (wordOf x) = 0 := by
    rw [CoedgeBase.lsig_wordOf, hx]
    rfl
  have h1 := decor_invRev c (-(lsig c (wordOf x))) (wordOf x)
  rw [neg_add_cancel] at h1
  rw [h1, hls, neg_zero]

/-! ## Powers of a word -/

/-- The `n`-fold concatenation of a word with itself. -/
def lpow (L : List (α × Bool)) : ℕ → List (α × Bool)
  | 0 => []
  | n + 1 => L ++ lpow L n

@[simp] theorem lpow_zero (L : List (α × Bool)) : lpow L 0 = [] := rfl

theorem lpow_succ (L : List (α × Bool)) (n : ℕ) : lpow L (n + 1) = L ++ lpow L n := rfl

theorem length_lpow (L : List (α × Bool)) (n : ℕ) : (lpow L n).length = n * L.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [lpow_succ, List.length_append, ih]; ring

theorem lsig_lpow (c : α → ℤ) (L : List (α × Bool)) (n : ℕ) :
    lsig c (lpow L n) = n * lsig c L := by
  induction n with
  | zero => simp [lsig]
  | succ n ih => rw [lpow_succ, CoedgeBase.lsig_append, ih]; push_cast; ring

theorem mk_lpow (L : List (α × Bool)) (n : ℕ) :
    FreeGroup.mk (lpow L n) = (FreeGroup.mk L) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lpow_succ, ← FreeGroup.mul_mk, ih, pow_succ']

/-! ## The loop subgroup of an edge set -/

/-- **The edges of the half-plane of levels `≤ M`**: the edges both of whose endpoints are `≤ M`. -/
def belowE (c : α → ℤ) (M : ℤ) : Set (α × ℤ) := {e | e.2 ≤ M ∧ e.2 + c e.1 ≤ M}

/-- **The edges of the half-plane of levels `≥ M`**: the edges both of whose endpoints are `≥ M`. -/
def aboveE (c : α → ℤ) (M : ℤ) : Set (α × ℤ) := {e | M ≤ e.2 ∧ M ≤ e.2 + c e.1}

@[simp] theorem mem_belowE {c : α → ℤ} {M : ℤ} {e : α × ℤ} :
    e ∈ belowE c M ↔ e.2 ≤ M ∧ e.2 + c e.1 ≤ M := Iff.rfl

@[simp] theorem mem_aboveE {c : α → ℤ} {M : ℤ} {e : α × ℤ} :
    e ∈ aboveE c M ↔ M ≤ e.2 ∧ M ≤ e.2 + c e.1 := Iff.rfl

/-- **The subgroup of loops with edges in `E`.**  `x` lies in it when `x` is a loop and the *reduced*
word of `x` has all its decorated edges in `E`. -/
noncomputable def loopsInE (c : α → ℤ) (E : Set (α × ℤ)) : Subgroup (FreeGroup α) where
  carrier := {x | cohom c x = 1 ∧ ∀ p ∈ decor c 0 (wordOf x), coverEdge p ∈ E}
  one_mem' := by
    refine ⟨map_one _, ?_⟩
    intro p hp
    have h : wordOf (1 : FreeGroup α) = [] := by classical simp [wordOf]
    rw [h] at hp
    simp only [decor, List.not_mem_nil] at hp
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨by rw [map_mul, hx1, hy1, mul_one], ?_⟩
    intro p hp
    have hsub := decor_sublist_of_red c 0 (red_wordOf_mul x y)
    have hmem : p ∈ decor c 0 (wordOf x ++ wordOf y) := List.Sublist.mem hp hsub
    rw [decor_append, CoedgeBase.lsig_wordOf, hx1] at hmem
    simp only [toAdd_one, add_zero] at hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hx2 p h
    · exact hy2 p h
  inv_mem' := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨by rw [map_inv, hx1, inv_one], ?_⟩
    intro p hp
    have hsub := decor_sublist_of_red c 0 (red_wordOf_inv x)
    have hmem : p ∈ decor c 0 (FreeGroup.invRev (wordOf x)) := List.Sublist.mem hp hsub
    rw [decor_invRev_wordOf hx1] at hmem
    simp only [List.mem_reverse, List.mem_map] at hmem
    obtain ⟨q, hq, hqe⟩ := hmem
    have : coverEdge p = coverEdge q := by rw [← hqe]; rfl
    rw [this]
    exact hx2 q hq

/-- **The reduced-word (canonical) description of `loopsInE`**: an element is in `loopsInE c E` iff
*some* word representing it (equivalently, its reduced word) is a closed walk whose decorated edges
all lie in `E`. -/
theorem mem_loopsInE_iff (c : α → ℤ) (E : Set (α × ℤ)) (x : FreeGroup α) :
    x ∈ loopsInE c E ↔
      ∃ L : List (α × Bool), FreeGroup.mk L = x ∧ lsig c L = 0 ∧
        ∀ p ∈ decor c 0 L, coverEdge p ∈ E := by
  constructor
  · intro hx
    exact ⟨wordOf x, mk_wordOf x, by rw [CoedgeBase.lsig_wordOf, hx.1]; rfl, hx.2⟩
  · rintro ⟨L, rfl, hlsig, hL⟩
    refine ⟨?_, ?_⟩
    · rw [cohom_mk, hlsig]; simp
    · intro p hp
      have hred : FreeGroup.Red L (wordOf (FreeGroup.mk L)) := by
        classical
        have h : FreeGroup.reduce L = wordOf (FreeGroup.mk L) := by
          rw [wordOf]
          exact FreeGroup.toWord_mk (L₁ := L)
        rw [← h]
        exact FreeGroup.reduce.red
      exact hL p (List.Sublist.mem hp (decor_sublist_of_red c 0 hred))

theorem loopsInE_mono {c : α → ℤ} {E E' : Set (α × ℤ)} (h : E ⊆ E') :
    loopsInE c E ≤ loopsInE c E' := by
  intro x hx
  exact ⟨hx.1, fun p hp => h (hx.2 p hp)⟩

/-- **The intersection of two loop subgroups is the loop subgroup of the intersection** -- the
"Mayer--Vietoris" statement, trivial in the canonical reduced description. -/
theorem loopsInE_inf (c : α → ℤ) (E₁ E₂ : Set (α × ℤ)) :
    loopsInE c E₁ ⊓ loopsInE c E₂ = loopsInE c (E₁ ∩ E₂) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨hx.1.1, fun p hp => ⟨hx.1.2 p hp, hx.2.2 p hp⟩⟩
  · intro x hx
    exact ⟨⟨hx.1, fun p hp => (hx.2 p hp).1⟩, ⟨hx.1, fun p hp => (hx.2 p hp).2⟩⟩

/-! ## Levels and decorated edges -/

/-- The two endpoints of a decorated letter are the two levels of its edge. -/
theorem coverEdge_mem_belowE_iff (c : α → ℤ) (M : ℤ) (p : (α × ℤ) × Bool) :
    coverEdge p ∈ belowE c M ↔ coverSrc c p ≤ M ∧ coverTgt c p ≤ M := by
  obtain ⟨⟨x, i⟩, b⟩ := p
  cases b <;> simp [coverEdge, coverSrc, coverTgt, belowE, and_comm]

theorem coverEdge_mem_aboveE_iff (c : α → ℤ) (M : ℤ) (p : (α × ℤ) × Bool) :
    coverEdge p ∈ aboveE c M ↔ M ≤ coverSrc c p ∧ M ≤ coverTgt c p := by
  obtain ⟨⟨x, i⟩, b⟩ := p
  cases b <;> simp [coverEdge, coverSrc, coverTgt, aboveE, and_comm]

/-- **The running levels are the start together with the endpoints of the decorated letters.** -/
theorem mem_running_iff_endpoints (c : α → ℤ) (L : List (α × Bool)) (v : ℤ) :
    v ∈ running c 0 L ↔ v = 0 ∨ ∃ p ∈ decor c 0 L, coverSrc c p = v ∨ coverTgt c p = v := by
  constructor
  · intro hv
    have hcons : running c 0 L = 0 :: (running c 0 L).tail := by
      simpa using (running_eq_cons_tail c 0 L).symm
    rw [hcons, List.mem_cons] at hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · have hmem : v ∈ (decor c 0 L).map (coverTgt c) := by
        rw [decor_map_coverTgt]; exact hv
      obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
      exact Or.inr ⟨p, hp, Or.inr hpv⟩
  · rintro (rfl | ⟨p, hp, h | h⟩)
    · have hcons : running c 0 L = 0 :: (running c 0 L).tail := by
        simpa using (running_eq_cons_tail c 0 L).symm
      rw [hcons]; exact List.mem_cons_self ..
    · have hmem : coverSrc c p ∈ (decor c 0 L).map (coverSrc c) :=
        List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [decor_map_coverSrc] at hmem
      rw [← h]
      exact List.Sublist.mem hmem (List.dropLast_sublist _)
    · have hmem : coverTgt c p ∈ (decor c 0 L).map (coverTgt c) :=
        List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [decor_map_coverTgt] at hmem
      rw [← h]
      exact List.Sublist.mem hmem (List.tail_sublist _)

/-- `levLe` is the level form of "every decorated edge lies in the lower half-plane `belowE`". -/
theorem levLe_iff_decor_belowE (c : α → ℤ) (M : ℤ) (L : List (α × Bool)) :
    levLe c M L ↔ 0 ≤ M ∧ ∀ p ∈ decor c 0 L, coverEdge p ∈ belowE c M := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 (Nat.zero_le L.length); simpa [lsig] using this
    · intro p hp
      rw [coverEdge_mem_belowE_iff]
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk, hk'⟩ :=
          exists_lsig_take_of_mem_running c L 0 (coverSrc c p) (coverSrc_mem_running hp)
        rw [zero_add] at hk'
        rw [← hk']
        exact h k hk
      · obtain ⟨k, hk, hk'⟩ :=
          exists_lsig_take_of_mem_running c L 0 (coverTgt c p) (coverTgt_mem_running hp)
        rw [zero_add] at hk'
        rw [← hk']
        exact h k hk
  · rintro ⟨h0, hL⟩ k hk
    have hmem := lsig_take_mem_running c 0 L k hk
    rw [mem_running_iff_endpoints] at hmem
    simp only [zero_add] at hmem
    rcases hmem with hzero | ⟨p, hp, hsrc | htgt⟩
    · rw [hzero]; exact h0
    · rw [← hsrc]; exact ((coverEdge_mem_belowE_iff c M p).mp (hL p hp)).1
    · rw [← htgt]; exact ((coverEdge_mem_belowE_iff c M p).mp (hL p hp)).2

/-- `levGe` is the level form of "every decorated edge lies in the upper half-plane `aboveE`". -/
theorem levGe_iff_decor_aboveE (c : α → ℤ) (M : ℤ) (L : List (α × Bool)) :
    levGe c M L ↔ M ≤ 0 ∧ ∀ p ∈ decor c 0 L, coverEdge p ∈ aboveE c M := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 (Nat.zero_le L.length); simpa [lsig] using this
    · intro p hp
      rw [coverEdge_mem_aboveE_iff]
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk, hk'⟩ :=
          exists_lsig_take_of_mem_running c L 0 (coverSrc c p) (coverSrc_mem_running hp)
        rw [zero_add] at hk'
        rw [← hk']
        exact h k hk
      · obtain ⟨k, hk, hk'⟩ :=
          exists_lsig_take_of_mem_running c L 0 (coverTgt c p) (coverTgt_mem_running hp)
        rw [zero_add] at hk'
        rw [← hk']
        exact h k hk
  · rintro ⟨h0, hL⟩ k hk
    have hmem := lsig_take_mem_running c 0 L k hk
    rw [mem_running_iff_endpoints] at hmem
    simp only [zero_add] at hmem
    rcases hmem with hzero | ⟨p, hp, hsrc | htgt⟩
    · rw [hzero]; exact h0
    · rw [← hsrc]; exact ((coverEdge_mem_aboveE_iff c M p).mp (hL p hp)).1
    · rw [← htgt]; exact ((coverEdge_mem_aboveE_iff c M p).mp (hL p hp)).2

/-- A word all of whose decorated edges lie in a window containing the level `0` has all its levels
in the window. -/
theorem band_of_decor_winE {c : α → ℤ} {lo hi : ℤ} {L : List (α × Bool)}
    (h : ∀ p ∈ decor c 0 L, coverEdge p ∈ winE c lo hi) (h0 : lo ≤ 0) (h1 : 0 ≤ hi) :
    band c lo hi L := by
  by_cases hL : L = []
  · subst hL
    exact band_nil c lo hi h0 h1
  · exact band_of_winE_decor c lo hi L hL h


section ZpowPow

variable {G : Type*} [Group G]

/-- The `n`-fold inverse power as a `zpow`. -/
theorem zpow_neg_eq_inv_pow (g : G) (n : ℕ) : g ^ (-(n : ℤ)) = (g⁻¹) ^ n := by
  rw [zpow_neg, zpow_natCast]
  exact (inv_pow g n).symm

theorem inv_zpow_neg_eq_pow (g : G) (n : ℕ) : (g ^ (-(n : ℤ)))⁻¹ = g ^ n := by
  rw [zpow_neg_eq_inv_pow, inv_pow, inv_inv]

end ZpowPow

end Work.OROneRel
