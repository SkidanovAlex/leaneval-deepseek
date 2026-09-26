import Mathlib
import Submission.Work.Smooth.JordanSeparation.hex_rect_hard

/-!
# The finite `4`/`8` (Hex) duality on the `N × N` grid

Grid of `N × N` cells indexed by `Fin N × Fin N`; `blocked : Fin N × Fin N → Prop`.

* `Adj4 a b` — `a` and `b` share an edge;
* `Adj8 a b` — `a` and `b` share an edge or a corner;
* `HasBlockedChain blocked` — an `8`-connected chain of blocked cells from the leftmost column
  to the rightmost column;
* `HasFreeChain blocked` — a `4`-connected chain of free cells from the bottom row to the top row.

The main result is the finite Hex duality `hexDualityGrid`:

*either* there is a `4`-connected chain of **free** cells from the bottom row to the top row,
*or* there is an `8`-connected chain of **blocked** cells running from the leftmost column to the
rightmost column.

The hard direction is `hex_hard`: the absence of a blocked `8`-chain from the left column to the
right column forces a free `4`-chain from the bottom row to the top row.  It is an immediate
specialisation of the rectangular statement `hex_rect_hard`, which is proved by following the
boundary (a "wall-following" walk) of the free `4`-component of the bottom row — see
`Submission/Work/Smooth/JordanSeparation/hex_rect_hard.lean` and `wall_LR.lean`.

The easy direction (used to make the disjunction an exclusive one) is the classical "no-draw"
argument: a free `4`-chain from bottom to top and a blocked `8`-chain from left to right would
have to cross, and two crossing chains share a cell, which cannot be both blocked and free.
-/

namespace Work.Smooth.JordanSeparation

open Classical

variable {N : ℕ}

/-! ## Basic grid adjacency on `Fin N × Fin N` -/

/-- Two cells of an `N × N` grid share an edge. -/
def Adj4 (a b : Fin N × Fin N) : Prop :=
  (a.1 = b.1 ∧ (a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)) ∨
  (a.2 = b.2 ∧ (a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1))

/-- Two cells of an `N × N` grid share an edge or a corner. -/
def Adj8 (a b : Fin N × Fin N) : Prop :=
  (a.1 = b.1 ∨ a.1.1 + 1 = b.1.1 ∨ b.1.1 + 1 = a.1.1) ∧
  (a.2 = b.2 ∨ a.2.1 + 1 = b.2.1 ∨ b.2.1 + 1 = a.2.1)

/-- The `8`-connected blocked chain from the left to the right column. -/
def HasBlockedChain (blocked : Fin N × Fin N → Prop) : Prop :=
  ∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, blocked (f i)) ∧
    (∀ i : Fin m, Adj8 (f i.castSucc) (f i.succ)) ∧
    (f 0).1.1 = 0 ∧ (f (Fin.last m)).1.1 + 1 = N

/-- The `4`-connected free chain from the bottom to the top row. -/
def HasFreeChain (blocked : Fin N × Fin N → Prop) : Prop :=
  ∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, ¬ blocked (f i)) ∧
    (∀ i : Fin m, Adj4 (f i.castSucc) (f i.succ)) ∧
    (f 0).2.1 = 0 ∧ (f (Fin.last m)).2.1 + 1 = N

/-! ## The hard direction -/

/-- The hard direction: absence of an `8`-connected blocked left-right chain forces a
`4`-connected free bottom-top chain.  (This is the finite Hex duality.)

It is the square specialisation of `hex_rect_hard` (proved by the wall-following walk of
`Sext`). -/
theorem hex_hard {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop)
    (hno : ¬ HasBlockedChain blocked) : HasFreeChain blocked := by
  have hno' : ¬ ∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, blocked (f i)) ∧
      (∀ i : Fin m, Adj8r (f i.castSucc) (f i.succ)) ∧
      (f 0).1.1 = 0 ∧ (f (Fin.last m)).1.1 + 1 = N := by
    rintro ⟨m, f, hb, hadj, h0, hlast⟩
    exact hno ⟨m, f, hb, fun i => by simpa only [Adj8, Adj8r] using hadj i, h0, hlast⟩
  obtain ⟨m, f, hf, hadj, h0, hlast⟩ := hex_rect_hard hN hN blocked hno'
  exact ⟨m, f, hf, fun i => by simpa only [Adj4, Adj4r] using hadj i, h0, hlast⟩

/-! ## The finite Hex duality -/

/-- The statement to be proved (unchanged). -/
theorem hexDualityGrid {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop) :
    (∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, ¬ blocked (f i)) ∧
        (∀ i : Fin m, (((f i.castSucc).1 = (f i.succ).1) ∧
            ((f i.castSucc).2.1 + 1 = (f i.succ).2.1 ∨ (f i.succ).2.1 + 1 = (f i.castSucc).2.1)) ∨
          (((f i.castSucc).2 = (f i.succ).2) ∧
            ((f i.castSucc).1.1 + 1 = (f i.succ).1.1 ∨ (f i.succ).1.1 + 1 = (f i.castSucc).1.1))) ∧
        (f 0).2.1 = 0 ∧ (f (Fin.last m)).2.1 + 1 = N) ∨
      (∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, blocked (f i)) ∧
        (∀ i : Fin m, (((f i.castSucc).1.1 ≤ (f i.succ).1.1 + 1) ∧
            ((f i.succ).1.1 ≤ (f i.castSucc).1.1 + 1)) ∧
          (((f i.castSucc).2.1 ≤ (f i.succ).2.1 + 1) ∧
            ((f i.succ).2.1 ≤ (f i.castSucc).2.1 + 1))) ∧
        (f 0).1.1 = 0 ∧ (f (Fin.last m)).1.1 + 1 = N) := by
  by_cases hchain : HasBlockedChain blocked
  · obtain ⟨m, f, hb, hadj, h0, hlast⟩ := hchain
    refine Or.inr ⟨m, f, hb, fun i => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h0, hlast⟩
    · obtain ⟨h1, _⟩ := hadj i
      rcases h1 with h | h | h
      · rw [h]; omega
      · omega
      · omega
    · obtain ⟨h1, _⟩ := hadj i
      rcases h1 with h | h | h
      · rw [h]; omega
      · omega
      · omega
    · obtain ⟨_, h2⟩ := hadj i
      rcases h2 with h | h | h
      · rw [h]; omega
      · omega
      · omega
    · obtain ⟨_, h2⟩ := hadj i
      rcases h2 with h | h | h
      · rw [h]; omega
      · omega
      · omega
  · obtain ⟨m, f, hfree, hadj, h0, hlast⟩ := hex_hard hN blocked hchain
    refine Or.inl ⟨m, f, hfree, fun i => ?_, h0, hlast⟩
    rcases hadj i with ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩

end Work.Smooth.JordanSeparation
