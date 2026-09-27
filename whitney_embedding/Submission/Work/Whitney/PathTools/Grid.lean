import Mathlib

/-!
# The mod-2 grid chain complex of the plane

A small combinatorial model used to prove that disjoint compact subsets of `ℝ²`
separate additively.  The plane is equipped with the square grid `ℤ² × ℤ²`.

* `Cell = ℤ × ℤ` indexes the unit squares;
* `Edge = Bool × ℤ × ℤ` indexes the edges (`false` = vertical, `true` = horizontal);
* a `k`-chain is a finitely supported `ZMod 2`-valued function.

The main result is `bdry2_fill`: every `1`-cycle is the boundary of an explicit
`2`-chain (`fill`), i.e. the grid is simply connected.
-/

namespace Work.Whitney.PathTools.Grid

abbrev Cell := ℤ × ℤ
abbrev Edge := Bool × ℤ × ℤ
abbrev Chain1 := Edge →₀ ZMod 2
abbrev Chain0 := (ℤ × ℤ) → ZMod 2
abbrev C2 := Cell → ZMod 2

/-- Boundary of a `2`-chain: the four edges of each square with multiplicity `1` mod 2. -/
noncomputable def bdry2 (w : C2) : Edge → ZMod 2
  | (false, i, j) => w (i, j) + w (i-1, j)
  | (true, i, j) => w (i, j) + w (i, j-1)

/-- Boundary of a `1`-chain, at a vertex `(i,j)`. -/
noncomputable def bdry1 (l : Edge → ZMod 2) : Chain0 :=
  fun (i, j) => l (false,i,j) + l (false,i,j-1) + l (true,i,j) + l (true,i-1,j)

lemma bdry1_add (a b : Edge → ZMod 2) : bdry1 (a + b) = bdry1 a + bdry1 b := by
  funext p; obtain ⟨i,j⟩ := p; simp only [bdry1, Pi.add_apply]; abel

lemma bdry1_bdry2 (w : C2) : bdry1 (bdry2 w) = 0 := by
  funext p; obtain ⟨i,j⟩ := p
  simp only [bdry1, bdry2, Pi.zero_apply]
  rw [show w (i,j) + w (i-1,j) + (w (i,j-1) + w (i-1,j-1)) + (w (i,j) + w (i,j-1)) + (w (i-1,j) + w (i-1,j-1))
        = (w (i,j)+w (i,j)) + (w (i-1,j)+w (i-1,j)) + (w (i,j-1)+w (i,j-1)) + (w (i-1,j-1)+w (i-1,j-1)) from by abel]
  simp [CharTwo.add_self_eq_zero]

/-- The horizontal ("vertical-edge") partial sum defining the primitive of a `1`-chain. -/
noncomputable def fillV (l : Chain1) (j : ℤ) (i : ℤ) : ZMod 2 := by
  classical
  exact ∑ e ∈ l.support, if (∃ i' : ℤ, e = (false, i', j) ∧ i' ≤ i) then l e else 0

/-- Primitive of a `1`-chain: a `2`-chain whose boundary is `l` when `l` is a cycle. -/
noncomputable def fill (l : Chain1) : C2 := fun ij => fillV l ij.2 ij.1

lemma fillV_succ (l : Chain1) (j i : ℤ) :
    fillV l j i + fillV l j (i-1) = l (false,i,j) := by
  classical
  unfold fillV
  rw [← Finset.sum_add_distrib, Finset.sum_eq_single (false,i,j)]
  · rw [if_pos (show ∃ i' : ℤ, (false,i,j) = (false, i', j) ∧ i' ≤ i from ⟨i, rfl, le_refl i⟩),
        if_neg (by rintro ⟨i', hei, hle⟩; simp only [Prod.mk.injEq] at hei; omega)]
    simp
  · intro e he hne
    have key : (∃ i' : ℤ, e = (false, i', j) ∧ i' ≤ i) ↔ (∃ i' : ℤ, e = (false, i', j) ∧ i' ≤ i-1) := by
      constructor
      · rintro ⟨i', hei, hle⟩
        refine ⟨i', hei, ?_⟩
        rcases lt_or_eq_of_le hle with hlt | heq
        · omega
        · exact absurd (by rw [heq] at hei; exact hei) hne
      · rintro ⟨i', hei, hle⟩; exact ⟨i', hei, by omega⟩
    rw [key]; exact CharTwo.add_self_eq_zero _
  · intro h; have hl : l (false,i,j) = 0 := by by_contra hc; exact h (Finsupp.mem_support_iff.mpr hc)
    rw [hl]; simp

lemma fillV_zero_le (l : Chain1) {lo : ℤ} (hlo : ∀ e ∈ l.support, lo ≤ e.2.1) (j i : ℤ)
    (hi : i < lo) : fillV l j i = 0 := by
  classical
  unfold fillV
  rw [Finset.sum_eq_zero]
  intro e he
  rw [if_neg]
  rintro ⟨i', hei, hle⟩
  have h1 : lo ≤ i' := by have := hlo e he; rw [hei] at this; exact this
  omega

lemma exists_lo (l : Chain1) : ∃ lo : ℤ, ∀ e ∈ l.support, lo ≤ e.2.1 := by
  classical
  rcases l.support.eq_empty_or_nonempty with h | h
  · exact ⟨0, by intro e he; rw [h] at he; exact absurd he (Finset.notMem_empty e)⟩
  · exact ⟨(l.support.image (fun e => e.2.1)).min' (h.image _),
      fun e he => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)⟩

lemma fillV_succ2 (l : Chain1) (h : bdry1 (l : Edge → ZMod 2) = 0) (j i : ℤ) :
    fillV l j i + fillV l (j-1) i = l (true,i,j) := by
  classical
  obtain ⟨lo, hlo⟩ := exists_lo l
  have hbase : fillV l j (lo-1) + fillV l (j-1) (lo-1) + l (true,lo-1,j) = 0 := by
    have h1 : fillV l j (lo-1) = 0 := fillV_zero_le l hlo j (lo-1) (by omega)
    have h2 : fillV l (j-1) (lo-1) = 0 := fillV_zero_le l hlo (j-1) (lo-1) (by omega)
    have h3 : l (true,lo-1,j) = 0 := by
      by_contra hc
      exact absurd (hlo (true,lo-1,j) (Finsupp.mem_support_iff.mpr hc)) (by simp)
    rw [h1, h2, h3, zero_add, zero_add]
  have hrec : ∀ n : ℤ, fillV l j n + fillV l (j-1) n + l (true,n,j)
      = fillV l j (n-1) + fillV l (j-1) (n-1) + l (true,n-1,j) := by
    intro n
    have hcyc' : l (false,n,j) + l (false,n,j-1) + l (true,n,j) + l (true,n-1,j) = 0 := by
      have := congrFun h (n,j); simpa [bdry1] using this
    have e1 := fillV_succ l j n
    have e2 := fillV_succ l (j-1) n
    refine CharTwo.add_eq_zero.mp ?_
    rw [show (fillV l j n + fillV l (j-1) n + l (true,n,j))
         + (fillV l j (n-1) + fillV l (j-1) (n-1) + l (true,n-1,j))
         = (fillV l j n + fillV l j (n-1)) + (fillV l (j-1) n + fillV l (j-1) (n-1))
           + (l (true,n,j) + l (true,n-1,j)) from by abel,
        e1, e2]
    rw [show l (false,n,j) + l (false,n,j-1) + (l (true,n,j) + l (true,n-1,j))
         = l (false,n,j) + l (false,n,j-1) + l (true,n,j) + l (true,n-1,j) from by abel, hcyc']
  have hup : ∀ n, lo-1 ≤ n → fillV l j n + fillV l (j-1) n + l (true,n,j) = 0 := by
    intro n hn
    refine Int.leInduction (motive := fun n _ => fillV l j n + fillV l (j-1) n + l (true,n,j) = 0)
      hbase ?_ n hn
    intro m hm ih
    rw [hrec (m+1)]; simpa using ih
  have hdown : ∀ n, n ≤ lo-1 → fillV l j n + fillV l (j-1) n + l (true,n,j) = 0 := by
    intro n hn
    refine Int.leInductionDown (motive := fun n _ => fillV l j n + fillV l (j-1) n + l (true,n,j) = 0)
      hbase ?_ n hn
    intro m hm ih
    rw [← hrec m]; simpa using ih
  rcases lt_or_ge (lo-1) i with hi | hi
  · exact CharTwo.add_eq_zero.mp (hup i (le_of_lt hi))
  · exact CharTwo.add_eq_zero.mp (hdown i hi)

lemma bdry2_fill (l : Chain1) (h : bdry1 (l : Edge → ZMod 2) = 0) :
    bdry2 (fill l) = (l : Edge → ZMod 2) := by
  funext e; obtain ⟨b,i,j⟩ := e
  · cases b
    · exact fillV_succ l j i
    · exact fillV_succ2 l h j i

end Work.Whitney.PathTools.Grid
