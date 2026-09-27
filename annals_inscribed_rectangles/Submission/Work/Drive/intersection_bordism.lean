import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.even_ncard_of_involution

/-!
# The mod-2 intersection number is a bordism invariant

`Submission/Work/Drive/intersection_parity.lean` proves the Leibniz rule for the mod-2 intersection
pairing of a 2-chain and a 3-chain in `ℝ⁴`: the intersection of the two chains is a compact
1-manifold whose boundary is `∂D ⋔ N` together with `D ⋔ ∂N`, so those two counts have the same
parity.  This file proves the *well-definedness* half of the theory: the pairing depends on the
3-chain only through its bordism class.

Concretely, a *closed* loop `L : ℝ → ℝ⁴` (modelled on `[0,1]`, with `L 0 = L 1`) and a *4-chain*
`M : ℝ⁴ → ℝ⁴` on the unit cube are given.  Writing `τ` for the last coordinate of the cube, the
faces `τ = 0` and `τ = 1` are two 3-chains `N₀`, `N₁` — a bordism between them — and the remaining
faces form the "side" 3-chain.  Applying `Work.Drive.boxParity` to

`homoDiff L M : ℝ⁵ = ℝ × ℝ⁴ → ℝ⁴,  (s,t) ↦ L s - M t`

on the five-box (loop coordinate first, cube coordinates last) counts the boundary points of the
1-manifold `L ⋔ M`:

* `even_ncard_loopEnd_add_side_add_tau` — the total number of boundary points is even, the sum being
  over the four blocks of faces of the five-box: the loop seams (`s ∈ {0,1}`), the sides (`t` on the
  cube's first three faces) and the two `τ`-ends;
* `even_ncard_loopEnd` — the loop seams contribute an even number (they are paired by the closedness
  `L 0 = L 1`);
* `even_ncard_tauMeet_add_tauMeet` — hence the sides together with the two ends contribute an even
  number, and if the loop avoids the side 3-chain then `#(L ⋔ N₀) + #(L ⋔ N₁)` is even:
  **the mod-2 intersection number of a closed loop with a 3-chain is unchanged by a bordism whose
  side boundary is disjoint from the loop.**

This is the well-definedness of the counts used in the chain route to `Work.Drive.chainParity`: it
makes the order function `b u = #(essential loop ⋔ V_u) mod 2` independent of the choice of the chain
representing `ω_{P_u}` (Hugelmeyer's Lemma 1), and mirrors the standard fact that the mod-2
intersection pairing is defined on homology classes.
-/

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The five-box as `loop × cube` -/

/-- The coordinate of the five-box carrying the loop parameter (the first coordinate). -/
def lpIdx : Fin 5 := Fin.castAdd 4 0

/-- The four coordinates of the five-box carrying the 4-chain (the last four coordinates). -/
def chIdx (k : Fin 4) : Fin 5 := Fin.natAdd 1 k

/-- The coordinate of the 4-chain block carrying the bordism parameter `τ` (the last coordinate). -/
def tauIdx : Fin 4 := Fin.last 3

@[simp] lemma lpIdx_val : (lpIdx : ℕ) = 0 := rfl

@[simp] lemma chIdx_val (k : Fin 4) : (chIdx k : ℕ) = 1 + k.val := rfl

@[simp] lemma tauIdx_val : (tauIdx : ℕ) = 3 := rfl

lemma lpIdx_ne_chIdx (k : Fin 4) : lpIdx ≠ chIdx k := by
  intro h
  have h' := congrArg Fin.val h
  simp only [lpIdx_val, chIdx_val] at h'
  omega

lemma chIdx_ne_lpIdx (k : Fin 4) : chIdx k ≠ lpIdx := (lpIdx_ne_chIdx k).symm

lemma chIdx_injective : Function.Injective chIdx := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [chIdx_val] at h'
  exact Fin.ext (by omega)

/-- The three "side" coordinates of the 4-chain block are not the last coordinate. -/
lemma castAdd_ne_tauIdx (j : Fin 3) : Fin.castAdd 1 j ≠ tauIdx := by
  intro h
  have h' := congrArg Fin.val h
  simp only [tauIdx_val] at h'
  have : (Fin.castAdd 1 j : Fin 4).val = j.val := rfl
  omega

/-- **Splitting the coordinates of the five-box** into the loop coordinate and the four coordinates
of the cube. -/
lemma exists_fin_five_loopCube (P : Fin 5 → Prop) :
    (∃ i, P i) ↔ P lpIdx ∨ (∃ k : Fin 4, P (chIdx k)) := by
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.addCases (m := 1) (n := 4) (motive := fun i => P i → _) ?_ ?_ i
    · intro i hi
      have hi0 : i = 0 := Subsingleton.elim i 0
      subst hi0
      exact Or.inl (by simpa [lpIdx] using hi)
    · intro k hk
      exact Or.inr ⟨k, by simpa [chIdx] using hk⟩
  · rintro (h | ⟨k, hk⟩)
    · exact ⟨lpIdx, h⟩
    · exact ⟨chIdx k, hk⟩

/-- **Splitting the coordinates of the cube** into its three "side" coordinates and the last
(bordism) coordinate. -/
lemma exists_fin_four_iff (P : Fin 4 → Prop) :
    (∃ k, P k) ↔ (∃ j : Fin 3, P (Fin.castAdd 1 j)) ∨ P tauIdx := by
  constructor
  · rintro ⟨k, hk⟩
    revert hk
    refine Fin.addCases (m := 3) (n := 1) (motive := fun k => P k → _) ?_ ?_ k
    · intro j hj
      exact Or.inl ⟨j, by simpa using hj⟩
    · intro r hr
      have hr3 : r = 0 := Subsingleton.elim r 0
      subst hr3
      exact Or.inr (by simpa [tauIdx] using hr)
  · rintro (⟨j, hj⟩ | h)
    · exact ⟨Fin.castAdd 1 j, hj⟩
    · exact ⟨tauIdx, h⟩

/-- The projection of the five-box onto the four coordinates of the cube. -/
def chPart (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 fun k => x (chIdx k)

@[simp] lemma chPart_apply (x : EuclideanSpace ℝ (Fin 5)) (k : Fin 4) :
    chPart x k = x (chIdx k) := rfl

/-- The loop coordinate of a point of the five-box. -/
def lpCoord (x : EuclideanSpace ℝ (Fin 5)) : ℝ := x lpIdx

/-- The bordism coordinate `τ` of a point of the five-box. -/
def tauCoord (x : EuclideanSpace ℝ (Fin 5)) : ℝ := x (chIdx tauIdx)

/-- The seam condition: the loop coordinate is at an end of `[0,1]`. -/
def onLoopFace (x : EuclideanSpace ℝ (Fin 5)) : Prop := lpCoord x = 0 ∨ lpCoord x = 1

/-- The side condition: one of the three "side" coordinates of the cube is at the boundary. -/
def onSideFace (x : EuclideanSpace ℝ (Fin 5)) : Prop :=
  ∃ j : Fin 3, x (chIdx (Fin.castAdd 1 j)) = 0 ∨ x (chIdx (Fin.castAdd 1 j)) = 1

/-- The end condition: the bordism coordinate `τ` is at `0` or at `1`. -/
def onTauFace (x : EuclideanSpace ℝ (Fin 5)) : Prop := tauCoord x = 0 ∨ tauCoord x = 1

lemma mem_unitBox_loopCube (x : EuclideanSpace ℝ (Fin 5)) :
    x ∈ unitBox 4 ↔ lpCoord x ∈ Set.Icc (0 : ℝ) 1 ∧ chPart x ∈ unitBox 3 := by
  constructor
  · intro h
    exact ⟨h lpIdx, fun k => h (chIdx k)⟩
  · rintro ⟨h1, h2⟩ i
    revert i
    refine Fin.addCases (m := 1) (n := 4) (motive := fun i => x i ∈ Set.Icc (0 : ℝ) 1) ?_ ?_ 
    · intro i
      have hi0 : i = 0 := Subsingleton.elim i 0
      rw [hi0]
      exact h1
    · intro k
      exact h2 k

lemma mem_unitBoxBdry_loopCube (x : EuclideanSpace ℝ (Fin 5)) :
    x ∈ unitBoxBdry 4 ↔ x ∈ unitBox 4 ∧ (onLoopFace x ∨ onSideFace x ∨ onTauFace x) := by
  constructor
  · rintro ⟨hbox, i, hi⟩
    refine ⟨hbox, ?_⟩
    rcases (exists_fin_five_loopCube (fun i => x i = 0 ∨ x i = 1)).mp ⟨i, hi⟩ with hi | ⟨k, hk⟩
    · exact Or.inl hi
    · rcases (exists_fin_four_iff (fun k => x (chIdx k) = 0 ∨ x (chIdx k) = 1)).mp
        ⟨k, hk⟩ with ⟨j, hj⟩ | hk
      · exact Or.inr (Or.inl ⟨j, hj⟩)
      · exact Or.inr (Or.inr hk)
  · rintro ⟨hbox, h | h | h⟩
    · exact ⟨hbox, lpIdx, h⟩
    · obtain ⟨j, hj⟩ := h
      exact ⟨hbox, chIdx (Fin.castAdd 1 j), hj⟩
    · exact ⟨hbox, chIdx tauIdx, h⟩

/-! ## The difference map of a loop and a bordism of 3-chains -/

/-- **The difference map of a closed loop and a 4-chain.**  Its zeros in `[0,1] × [0,1]⁴` are the
intersections of the loop `L` with the 4-chain `M` (the trace of a bordism of 3-chains). -/
def homoDiff (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 4) :=
  fun x => L (lpCoord x) - M (chPart x)

/-- The intersections of the loop with the 3-chain at the end `τ` of the bordism. -/
def tauMeet (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) (τ : ℝ) :
    Set (EuclideanSpace ℝ (Fin 5)) :=
  {x | x ∈ unitBox 4 ∧ tauCoord x = τ ∧ homoDiff L M x = 0}

/-- The intersections of the loop with the side 3-chain of the bordism (the cube's first three
faces). -/
def sideMeet (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) :
    Set (EuclideanSpace ℝ (Fin 5)) :=
  {x | x ∈ unitBox 4 ∧ onSideFace x ∧ homoDiff L M x = 0}

/-- The intersections of the loop with the 4-chain at the seams of the loop parametrisation (the
faces `s = 0` and `s = 1` of the five-box). -/
def loopEndMeet (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) :
    Set (EuclideanSpace ℝ (Fin 5)) :=
  {x | x ∈ unitBox 4 ∧ onLoopFace x ∧ homoDiff L M x = 0}

/-! ## The boundary of the intersection -/

/-- **The boundary of the intersection `L ⋔ M`.**  The zeros of `homoDiff L M` on the boundary of
the five-box are exactly the seam intersections, the side intersections and the two end
intersections. -/
theorem bdyZeros_homoDiff_eq (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) :
    bdyZeros (homoDiff L M) =
      loopEndMeet L M ∪ sideMeet L M ∪ tauMeet L M 0 ∪ tauMeet L M 1 := by
  ext x
  simp only [bdyZeros, loopEndMeet, sideMeet, tauMeet, Set.mem_ofPred_eq, Set.mem_union,
    mem_unitBoxBdry_loopCube x, onLoopFace, onSideFace, onTauFace, lpCoord, tauCoord]
  constructor
  · intro h
    obtain ⟨h1, hF⟩ := h
    obtain ⟨hbox, hrest⟩ := h1
    rcases hrest with hAB | hrest
    · rcases hAB with hA | hB
      · exact Or.inl (Or.inl (Or.inl ⟨hbox, Or.inl hA, hF⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨hbox, Or.inr hB, hF⟩))
    · rcases hrest with hY | hDE
      · exact Or.inl (Or.inl (Or.inr ⟨hbox, hY, hF⟩))
      · rcases hDE with hD | hE
        · exact Or.inl (Or.inr ⟨hbox, hD, hF⟩)
        · exact Or.inr ⟨hbox, hE, hF⟩
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · rcases h with h | h
        · obtain ⟨hbox, hAB, hF⟩ := h
          rcases hAB with hA | hB
          · exact ⟨⟨hbox, Or.inl (Or.inl hA)⟩, hF⟩
          · exact ⟨⟨hbox, Or.inl (Or.inr hB)⟩, hF⟩
        · obtain ⟨hbox, hY, hF⟩ := h
          exact ⟨⟨hbox, Or.inr (Or.inl hY)⟩, hF⟩
      · obtain ⟨hbox, hD, hF⟩ := h
        exact ⟨⟨hbox, Or.inr (Or.inr (Or.inl hD))⟩, hF⟩
    · obtain ⟨hbox, hE, hF⟩ := h
      exact ⟨⟨hbox, Or.inr (Or.inr (Or.inr hE))⟩, hF⟩

/-- **Two different faces cannot both support a boundary zero.**  If a point of the box has
coordinate `i` on the boundary and all other coordinates strictly inside, then any coordinate `j`
which is also on the boundary satisfies `j = i`. -/
lemma eq_of_mem_Ioo_of_eq_zero_or_one {x : EuclideanSpace ℝ (Fin 5)} {i j : Fin 5}
    (hother : ∀ l, l ≠ i → x l ∈ Set.Ioo (0 : ℝ) 1) (hj : x j = 0 ∨ x j = 1) : j = i := by
  by_contra hne
  have hmem := hother j hne
  rcases hj with h | h
  · rw [h] at hmem
    exact absurd hmem.1 (by norm_num)
  · rw [h] at hmem
    exact absurd hmem.2 (by norm_num)

/-- **The four blocks of boundary faces are pairwise disjoint.**  Under the "exactly one face"
hypothesis of `Submission.Drive.ParityProp`, a boundary zero of `homoDiff L M` lies in exactly one of
the four blocks used in `bdyZeros_homoDiff_eq`. -/
theorem disjoint_blocks (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hface : ∀ x ∈ unitBoxBdry 4, homoDiff L M x = 0 → ∃ i : Fin 5,
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1)) :
    Disjoint (loopEndMeet L M) (sideMeet L M) ∧
      Disjoint (loopEndMeet L M) (tauMeet L M 0) ∧
      Disjoint (loopEndMeet L M) (tauMeet L M 1) ∧
      Disjoint (sideMeet L M) (tauMeet L M 0) ∧
      Disjoint (sideMeet L M) (tauMeet L M 1) ∧
      Disjoint (tauMeet L M 0) (tauMeet L M 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Set.disjoint_left]
    rintro x hx hy
  · -- loop vs side
    obtain ⟨hxbox, hxlp, hxF⟩ := hx
    obtain ⟨-, hxsd, -⟩ := hy
    have hxbdy : x ∈ unitBoxBdry 4 :=
      (mem_unitBoxBdry_loopCube x).mpr ⟨hxbox, Or.inl hxlp⟩
    obtain ⟨i, hi, hother⟩ := hface x hxbdy hxF
    have h1 : lpIdx = i := eq_of_mem_Ioo_of_eq_zero_or_one hother hxlp
    obtain ⟨j, hj⟩ := hxsd
    have h2 : chIdx (Fin.castAdd 1 j) = i := eq_of_mem_Ioo_of_eq_zero_or_one hother hj
    exact lpIdx_ne_chIdx _ (by rw [h1, h2])
  · -- loop vs tau 0
    obtain ⟨hxbox, hxlp, hxF⟩ := hx
    obtain ⟨-, hxtau, -⟩ := hy
    have hxbdy : x ∈ unitBoxBdry 4 :=
      (mem_unitBoxBdry_loopCube x).mpr ⟨hxbox, Or.inl hxlp⟩
    obtain ⟨i, hi, hother⟩ := hface x hxbdy hxF
    have h1 : lpIdx = i := eq_of_mem_Ioo_of_eq_zero_or_one hother hxlp
    have h2 : chIdx tauIdx = i := eq_of_mem_Ioo_of_eq_zero_or_one hother (Or.inl hxtau)
    exact lpIdx_ne_chIdx tauIdx (by rw [h1, h2])
  · -- loop vs tau 1
    obtain ⟨hxbox, hxlp, hxF⟩ := hx
    obtain ⟨-, hxtau, -⟩ := hy
    have hxbdy : x ∈ unitBoxBdry 4 :=
      (mem_unitBoxBdry_loopCube x).mpr ⟨hxbox, Or.inl hxlp⟩
    obtain ⟨i, hi, hother⟩ := hface x hxbdy hxF
    have h1 : lpIdx = i := eq_of_mem_Ioo_of_eq_zero_or_one hother hxlp
    have h2 : chIdx tauIdx = i := eq_of_mem_Ioo_of_eq_zero_or_one hother (Or.inr hxtau)
    exact lpIdx_ne_chIdx tauIdx (by rw [h1, h2])
  · -- side vs tau 0
    obtain ⟨hxbox, hxsd, hxF⟩ := hx
    obtain ⟨-, hxtau, -⟩ := hy
    have hxbdy : x ∈ unitBoxBdry 4 :=
      (mem_unitBoxBdry_loopCube x).mpr ⟨hxbox, Or.inr (Or.inl hxsd)⟩
    obtain ⟨i, hi, hother⟩ := hface x hxbdy hxF
    obtain ⟨j, hj⟩ := hxsd
    have h1 : chIdx (Fin.castAdd 1 j) = i := eq_of_mem_Ioo_of_eq_zero_or_one hother hj
    have h2 : chIdx tauIdx = i := eq_of_mem_Ioo_of_eq_zero_or_one hother (Or.inl hxtau)
    have h3 : (Fin.castAdd 1 j : Fin 4) = tauIdx := chIdx_injective (by rw [h1, h2])
    exact castAdd_ne_tauIdx j h3
  · -- side vs tau 1
    obtain ⟨hxbox, hxsd, hxF⟩ := hx
    obtain ⟨-, hxtau, -⟩ := hy
    have hxbdy : x ∈ unitBoxBdry 4 :=
      (mem_unitBoxBdry_loopCube x).mpr ⟨hxbox, Or.inr (Or.inl hxsd)⟩
    obtain ⟨i, hi, hother⟩ := hface x hxbdy hxF
    obtain ⟨j, hj⟩ := hxsd
    have h1 : chIdx (Fin.castAdd 1 j) = i := eq_of_mem_Ioo_of_eq_zero_or_one hother hj
    have h2 : chIdx tauIdx = i := eq_of_mem_Ioo_of_eq_zero_or_one hother (Or.inr hxtau)
    have h3 : (Fin.castAdd 1 j : Fin 4) = tauIdx := chIdx_injective (by rw [h1, h2])
    exact castAdd_ne_tauIdx j h3
  · -- tau 0 vs tau 1
    obtain ⟨-, h0, -⟩ := hx
    obtain ⟨-, h1, -⟩ := hy
    rw [h0] at h1
    norm_num at h1

/-- **An even sum of three numbers, one of which is even: the other two sum to an even number.** -/
lemma even_add_of_even_add_left {a b c : ℕ} (h : Even (a + b + c)) (ha : Even a) :
    Even (b + c) := by
  rw [Nat.even_iff] at *
  omega

/-! ## The parity of the boundary -/

/-- The reflection of the loop coordinate `0 ↦ 1`, `1 ↦ 0`, required to pair up the two seams of
the loop parametrisation. -/
def flipLoop (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 fun i => if i = lpIdx then 1 - x i else x i

@[simp] lemma flipLoop_lp (x : EuclideanSpace ℝ (Fin 5)) :
    flipLoop x lpIdx = 1 - x lpIdx := by
  simp [flipLoop]

lemma flipLoop_of_ne (x : EuclideanSpace ℝ (Fin 5)) {i : Fin 5} (h : i ≠ lpIdx) :
    flipLoop x i = x i := by
  simp [flipLoop, h]

/-- The reflection does not move the cube coordinates. -/
lemma chPart_flipLoop (x : EuclideanSpace ℝ (Fin 5)) : chPart (flipLoop x) = chPart x := by
  rw [WithLp.ext_iff]
  ext k
  simp only [chPart_apply]
  exact flipLoop_of_ne x (chIdx_ne_lpIdx k)

lemma flipLoop_invol (x : EuclideanSpace ℝ (Fin 5)) : flipLoop (flipLoop x) = x := by
  rw [WithLp.ext_iff]
  ext i
  by_cases h : i = lpIdx
  · subst h
    rw [flipLoop_lp, flipLoop_lp]
    ring
  · rw [flipLoop_of_ne _ h, flipLoop_of_ne _ h]

lemma flipLoop_ne_self (x : EuclideanSpace ℝ (Fin 5)) (h : x lpIdx = 0 ∨ x lpIdx = 1) :
    flipLoop x ≠ x := by
  intro heq
  have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 5) => y lpIdx) heq
  rw [flipLoop_lp] at hc
  rcases h with h0 | h1
  · rw [h0] at hc
    norm_num at hc
  · rw [h1] at hc
    norm_num at hc

/-- The difference map is invariant under the reflection of the loop coordinate, because the loop is
closed (`L 0 = L 1`). -/
lemma homoDiff_flipLoop (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) (hL : L 0 = L 1)
    (x : EuclideanSpace ℝ (Fin 5)) (h : x lpIdx = 0 ∨ x lpIdx = 1) :
    homoDiff L M (flipLoop x) = homoDiff L M x := by
  have hLc : L (1 - x lpIdx) = L (x lpIdx) := by
    rcases h with h0 | h1
    · rw [h0]
      norm_num
      exact hL.symm
    · rw [h1]
      norm_num
      exact hL
  simp only [homoDiff, lpCoord]
  rw [flipLoop_lp, hLc, chPart_flipLoop]

/-- The reflection preserves the seam set. -/
lemma flipLoop_mem_loopEnd (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) (hL : L 0 = L 1)
    {x : EuclideanSpace ℝ (Fin 5)} (hx : x ∈ loopEndMeet L M) :
    flipLoop x ∈ loopEndMeet L M := by
  obtain ⟨hbox, hl, hF⟩ := hx
  have hl' : x lpIdx = 0 ∨ x lpIdx = 1 := hl
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases h : i = lpIdx
    · subst h
      rw [flipLoop_lp]
      rcases hl' with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]; norm_num
    · rw [flipLoop_of_ne x h]
      exact hbox i
  · rw [show onLoopFace (flipLoop x) ↔
      (flipLoop x lpIdx = 0 ∨ flipLoop x lpIdx = 1) from Iff.rfl, flipLoop_lp]
    rcases hl' with h0 | h1
    · right; rw [h0]; norm_num
    · left; rw [h1]; norm_num
  · rw [homoDiff_flipLoop L M hL x hl]
    exact hF

/-- **The seams of the loop parametrisation contribute an even number of intersection points.**  The
reflection `s ↦ 1 - s` of the loop coordinate pairs the intersections on the two seams `s = 0` and
`s = 1`: the loop is closed, `L 0 = L 1`, so a point of the 4-chain met at the seam `s = 0` is also
met at the seam `s = 1`. -/
theorem even_ncard_loopEnd (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) (hL : L 0 = L 1)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (homoDiff L M))
    (hreg : ∀ x ∈ unitBox 4, homoDiff L M x = 0 →
      Function.Surjective (fderiv ℝ (homoDiff L M) x))
    (hface : ∀ x ∈ unitBoxBdry 4, homoDiff L M x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (homoDiff L M) x v.1)) :
    Even (loopEndMeet L M).ncard := by
  obtain ⟨hfin, -⟩ := boxParity 4 (homoDiff L M) hF hreg hface
  have hfin' : (bdyZeros (homoDiff L M)).Finite := hfin
  rw [bdyZeros_homoDiff_eq] at hfin'
  have hfA : (loopEndMeet L M).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inl (Or.inl hx)))
  refine even_ncard_of_involution hfA flipLoop ?_ ?_ ?_
  · intro x hx
    exact flipLoop_mem_loopEnd L M hL hx
  · intro x _
    exact flipLoop_invol x
  · intro x hx
    exact flipLoop_ne_self x hx.2.1

/-- **The boundary of `L ⋔ M` has an even number of points.**  With the transversality hypotheses of
`Submission.Drive.ParityProp`, the number of boundary zeros of `homoDiff L M` — the sum of the seam,
side and two end counts — is even. -/
theorem even_ncard_loopEnd_add_side_add_tau
    (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (homoDiff L M))
    (hreg : ∀ x ∈ unitBox 4, homoDiff L M x = 0 →
      Function.Surjective (fderiv ℝ (homoDiff L M) x))
    (hface : ∀ x ∈ unitBoxBdry 4, homoDiff L M x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (homoDiff L M) x v.1)) :
    Even ((loopEndMeet L M).ncard + (sideMeet L M).ncard +
      (tauMeet L M 0).ncard + (tauMeet L M 1).ncard) := by
  obtain ⟨hfin, heven⟩ := boxParity 4 (homoDiff L M) hF hreg hface
  have hfin' : (bdyZeros (homoDiff L M)).Finite := hfin
  have heven' : Even (bdyZeros (homoDiff L M)).ncard := heven
  rw [bdyZeros_homoDiff_eq] at hfin' heven'
  obtain ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩ :=
    disjoint_blocks L M (fun x hx h0 => (hface x hx h0).imp fun _ h => ⟨h.1, h.2.1⟩)
  have hfA : (loopEndMeet L M).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inl (Or.inl hx)))
  have hfB : (sideMeet L M).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inl (Or.inr hx)))
  have hfC : (tauMeet L M 0).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inr hx))
  have hfD : (tauMeet L M 1).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inr hx)
  have hunion : ((loopEndMeet L M ∪ sideMeet L M) ∪ tauMeet L M 0) ∪ tauMeet L M 1
      = (loopEndMeet L M ∪ sideMeet L M) ∪ (tauMeet L M 0 ∪ tauMeet L M 1) := by
    rw [Set.union_assoc]
  have hdisj : Disjoint (loopEndMeet L M ∪ sideMeet L M) (tauMeet L M 0 ∪ tauMeet L M 1) := by
    rw [Set.disjoint_left]
    rintro x (hx | hx) (hy | hy)
    · exact Set.disjoint_left.mp hAC hx hy
    · exact Set.disjoint_left.mp hAD hx hy
    · exact Set.disjoint_left.mp hBC hx hy
    · exact Set.disjoint_left.mp hBD hx hy
  rw [hunion, Set.ncard_union_eq hdisj (hfA.union hfB) (hfC.union hfD),
    Set.ncard_union_eq hAB hfA hfB, Set.ncard_union_eq hCD hfC hfD] at heven'
  rw [Nat.add_assoc]
  exact heven'

/-- **Finiteness of the four blocks of boundary intersections.**  Under the hypotheses of
`Submission.Drive.ParityProp` the seam, side and end intersection sets are finite, so that the parity
statements about them are not vacuous. -/
theorem finite_loopEnd_and_side_and_tau
    (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hF : ContDiff ℝ Ctop (homoDiff L M))
    (hreg : ∀ x ∈ unitBox 4, homoDiff L M x = 0 →
      Function.Surjective (fderiv ℝ (homoDiff L M) x))
    (hface : ∀ x ∈ unitBoxBdry 4, homoDiff L M x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (homoDiff L M) x v.1)) :
    (loopEndMeet L M).Finite ∧ (sideMeet L M).Finite ∧
      (tauMeet L M 0).Finite ∧ (tauMeet L M 1).Finite := by
  obtain ⟨hfin, -⟩ := boxParity 4 (homoDiff L M) hF hreg hface
  have hfin' : (bdyZeros (homoDiff L M)).Finite := hfin
  rw [bdyZeros_homoDiff_eq] at hfin'
  refine ⟨hfin'.subset ?_, hfin'.subset ?_, hfin'.subset ?_, hfin'.subset ?_⟩
  · intro x hx; simp only [Set.mem_union]; exact Or.inl (Or.inl (Or.inl hx))
  · intro x hx; simp only [Set.mem_union]; exact Or.inl (Or.inl (Or.inr hx))
  · intro x hx; simp only [Set.mem_union]; exact Or.inl (Or.inr hx)
  · intro x hx; simp only [Set.mem_union]; exact Or.inr hx

/-- **The mod-2 intersection number of a closed loop with a 3-chain is a bordism invariant.**  If the
loop avoids the side 3-chain of the bordism `M` between the 3-chains `N₀` (`τ = 0`) and `N₁`
(`τ = 1`), then the numbers of intersection points of the loop with `N₀` and with `N₁` have the same
parity.  Equivalently, `#(L ⋔ N₀) + #(L ⋔ N₁)` is even: the two counts agree mod 2. -/
theorem even_ncard_tauMeet_add_tauMeet
    (L : ℝ → EuclideanSpace ℝ (Fin 4))
    (M : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) (hL : L 0 = L 1)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (homoDiff L M))
    (hreg : ∀ x ∈ unitBox 4, homoDiff L M x = 0 →
      Function.Surjective (fderiv ℝ (homoDiff L M) x))
    (hface : ∀ x ∈ unitBoxBdry 4, homoDiff L M x = 0 → ∃ i : Fin (4 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
        fderiv ℝ (homoDiff L M) x v.1))
    (hdisj : ∀ x, x ∈ unitBox 4 → onSideFace x → homoDiff L M x ≠ 0) :
    Even ((tauMeet L M 0).ncard + (tauMeet L M 1).ncard) := by
  have hmain := even_ncard_loopEnd_add_side_add_tau L M hF hreg hface
  have hseam := even_ncard_loopEnd L M hL hF hreg hface
  have hside : (sideMeet L M).ncard = 0 := by
    have hempty : sideMeet L M = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hs, h0⟩
      exact hdisj x hx hs h0
    rw [hempty, Set.ncard_empty]
  rw [hside] at hmain
  have hseam' : Even ((loopEndMeet L M).ncard + 0) := by
    rw [add_zero]
    exact hseam
  exact even_add_of_even_add_left hmain hseam'

end

end Work.Drive
