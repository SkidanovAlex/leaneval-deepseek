import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Submission.Work.BoseB4.ModeFock
import Submission.Work.BoseB4.Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Frame.frame_quadForm_nonneg`

FS's Bogolubov frame: the hypothesis `hS` is the statement that the (finite) family of
coordinate vectors `f k : Fin m → ℝ` has "quadratic-form norm" at most `C`, i.e. that for
every `w : Fin m → ℝ`

  `Σ_k (gram (f k) w)^2 ≤ C · Σ_l (w l)^2`,

equivalently that the positive semidefinite matrix `A_{l l'} = Σ_k f k l · f k l'`
satisfies `A ≤ C·1` in the Loewner order.  The conclusion is that the quadratic form of
`C·1 − A` is nonnegative on the **excited** coordinates `l ≠ 0` (the condensate coordinate
`l = 0` being removed).  This is the standard "operator norm bound ⇒ PSD compression"
implication, and it is the frame step in which the box/Neumann Bogolubov quadratic form is
seen to be positive once the a priori bound `hS` on the mode family is available.

The proof is three lines of linear algebra:

* `frame_core_identity` — the exact expansion
  `Σ_{i,j} w_i (C δ_{ij} − Σ_k f_{ki} f_{kj}) w_j = C Σ_i w_i² − Σ_k (Σ_i f_{ki} w_i)²`
  on an arbitrary index type (no positivity needed);
* `frame_excited_restrict` — restriction of a bilinear form to a subtype, i.e. replacing
  the sums over `{l // l ≠ 0}` by sums over the ambient type of the vector extended by `0`;
* the assembly, which inserts `w := v` extended by `0` and applies `hS`.
-/

namespace Work.BoseBoxFock.Frame

/-- A sum over a `Finset` filtered by `p` is a sum over the corresponding subtype (in this
direction).  General-purpose reindexing lemma. -/
lemma sum_subtype_val {α M : Type*} [Fintype α] [AddCommMonoid M] (s : Finset α)
    (p : α → Prop) [DecidablePred p] (hsp : ∀ x, x ∈ s ↔ p x) (F : α → M)
    (G : {x // p x} → M) (hFG : ∀ (x : α) (hx : p x), G ⟨x, hx⟩ = F x) :
    (∑ x ∈ s, F x) = ∑ y : {x // p x}, G y := by
  rw [Finset.sum_subtype s hsp F]
  apply Finset.sum_congr rfl; intro y _
  rw [← hFG y.1 y.2]

/-- A sum of a function vanishing off `p` over the whole type is the sum over the subtype.
General-purpose reindexing lemma. -/
lemma sum_of_vanishing {α M : Type*} [Fintype α] [AddCommMonoid M] (p : α → Prop)
    [DecidablePred p] (f : α → M) (hf : ∀ x, ¬ p x → f x = 0) :
    (∑ x : α, f x) = ∑ x : {x // p x}, f x.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter p) (fun x => by simp) f]
  exact (Finset.sum_filter_of_ne (s := Finset.univ) (f := f)
    (fun x _ hx => by by_contra h; exact hx (hf x h))).symm

/-- The quadratic form of `C·1 − A`, `A_{ij} = Σ_k f_{ki} f_{kj}`, expanded as the diagonal
term minus a sum of squares.  Pure algebra; valid for real `C` of either sign. -/
lemma frame_core_identity {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : κ → ι → ℝ) (C : ℝ) (w : ι → ℝ) :
    (∑ i : ι, ∑ j : ι, w i * (C * (if i = j then (1 : ℝ) else 0)
        - ∑ k : κ, f k i * f k j) * w j)
      = C * ∑ i : ι, (w i) ^ 2 - ∑ k : κ, (∑ i : ι, f k i * w i) ^ 2 := by
  have hbody : ∀ i j : ι,
      w i * (C * (if i = j then (1 : ℝ) else 0) - ∑ k : κ, f k i * f k j) * w j
        = (w i * (C * (if i = j then (1 : ℝ) else 0)) * w j)
          - (w i * (∑ k : κ, f k i * f k j) * w j) := fun i j => by ring
  have hsplit : (∑ i : ι, ∑ j : ι, w i * (C * (if i = j then (1 : ℝ) else 0)
        - ∑ k : κ, f k i * f k j) * w j)
      = (∑ i : ι, ∑ j : ι, w i * (C * (if i = j then (1 : ℝ) else 0)) * w j)
        - ∑ i : ι, ∑ j : ι, w i * (∑ k : κ, f k i * f k j) * w j := by
    simp only [hbody, Finset.sum_sub_distrib]
  have hX : (∑ i : ι, ∑ j : ι, w i * (C * (if i = j then (1 : ℝ) else 0)) * w j)
      = C * ∑ i : ι, (w i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]; ring
    · intro j _ hj; rw [if_neg (Ne.symm hj)]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hY : (∑ i : ι, ∑ j : ι, w i * (∑ k : κ, f k i * f k j) * w j)
      = ∑ k : κ, (∑ i : ι, f k i * w i) ^ 2 := by
    have h1 : (∑ i : ι, ∑ j : ι, w i * (∑ k : κ, f k i * f k j) * w j)
        = ∑ i : ι, ∑ j : ι, ∑ k : κ, w i * (f k i * f k j) * w j := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum, Finset.sum_mul]
    have h2 : (∑ i : ι, ∑ j : ι, ∑ k : κ, w i * (f k i * f k j) * w j)
        = ∑ i : ι, ∑ k : κ, ∑ j : ι, w i * (f k i * f k j) * w j := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
    have h3 : (∑ i : ι, ∑ k : κ, ∑ j : ι, w i * (f k i * f k j) * w j)
        = ∑ k : κ, ∑ i : ι, ∑ j : ι, w i * (f k i * f k j) * w j :=
      Finset.sum_comm
    have h4 : (∑ k : κ, (∑ i : ι, f k i * w i) ^ 2)
        = ∑ k : κ, ∑ i : ι, ∑ j : ι, w i * (f k i * f k j) * w j := by
      apply Finset.sum_congr rfl; intro k _
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    rw [h1, h2, h3, h4]
  rw [hsplit, hX, hY]

/-- Restriction of a bilinear form to a subtype: the double sum over `{x // p x}` equals the
double sum over the ambient type of the vector extended by `0` off `p`. -/
lemma frame_excited_restrict {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (F : α → α → ℝ) (v : {x // p x} → ℝ) :
    (∑ l : {x // p x}, ∑ l' : {x // p x}, v l * F l.1 l'.1 * v l')
      = ∑ l : α, ∑ l' : α,
          (if h : p l then v ⟨l, h⟩ else 0) * F l l' * (if h : p l' then v ⟨l', h⟩ else 0) := by
  set W : α → ℝ := fun l => if h : p l then v ⟨l, h⟩ else 0 with hW
  have hW0 : ∀ x : α, ¬ p x → W x = 0 := by
    intro x hx
    simp only [hW]
    exact dif_neg hx
  have hWp : ∀ (x : α) (hx : p x), W x = v ⟨x, hx⟩ := by
    intro x hx
    simp only [hW]
    exact dif_pos hx
  have hinner : ∀ l : α, (∑ l' : α, W l * F l l' * W l')
      = ∑ l' : {x // p x}, W l * F l l'.1 * v l' := by
    intro l
    rw [sum_of_vanishing p (fun l' : α => W l * F l l' * W l') ?_]
    · apply Finset.sum_congr rfl; intro l' _
      rw [show W l'.1 = v l' from hWp l'.1 l'.2]
    · intro x hx
      rw [hW0 x hx]
      ring
  have houter : ∀ l : {x // p x},
      (∑ l' : {x // p x}, W l.1 * F l.1 l'.1 * v l')
        = ∑ l' : {x // p x}, v l * F l.1 l'.1 * v l' := by
    intro l
    apply Finset.sum_congr rfl; intro l' _
    rw [show W l.1 = v l from hWp l.1 l.2]
  have h : (∑ l : α, ∑ l' : α, W l * F l l' * W l')
      = ∑ l : {x // p x}, ∑ l' : {x // p x}, v l * F l.1 l'.1 * v l' := by
    calc (∑ l : α, ∑ l' : α, W l * F l l' * W l')
        = ∑ l : α, ∑ l' : {x // p x}, W l * F l l'.1 * v l' := by
          apply Finset.sum_congr rfl; intro l _; exact hinner l
      _ = ∑ l : {x // p x}, ∑ l' : {x // p x}, W l.1 * F l.1 l'.1 * v l' := by
          refine sum_of_vanishing p
            (fun l : α => ∑ l' : {x // p x}, W l * F l l'.1 * v l') ?_
          intro x hx
          rw [hW0 x hx]
          simp
      _ = ∑ l : {x // p x}, ∑ l' : {x // p x}, v l * F l.1 l'.1 * v l' := by
          apply Finset.sum_congr rfl; intro l _; exact houter l
  have hWgoal : (∑ l : α, ∑ l' : α,
        (if h : p l then v ⟨l, h⟩ else 0) * F l l' * (if h : p l' then v ⟨l', h⟩ else 0))
      = ∑ l : α, ∑ l' : α, W l * F l l' * W l' := by simp only [hW]
  rw [hWgoal]
  exact h.symm

/-- The Bogolubov frame positivity: an operator-norm bound `hS` on the coordinate family
`f` makes `C·1 − Σ_k f_k ⊗ f_k` positive semidefinite on the excited coordinates. -/
theorem frame_quadForm_nonneg {m : ℕ} [NeZero m] {Mode : Type*} [Fintype Mode]
    (f : Mode → Fin m → ℝ) (C : ℝ)
    (hS : ∀ w : Fin m → ℝ,
      ∑ k : Mode, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C * ∑ l : Fin m, (w l) ^ 2) :
    ∀ v : Work.BoseB4.Excited m → ℝ,
      0 ≤ ∑ l : Work.BoseB4.Excited m, ∑ l' : Work.BoseB4.Excited m,
            v l * (C * (if l = l' then (1 : ℝ) else 0)
                    - ∑ k : Mode, f k l.1 * f k l'.1) * v l' := by
  intro v
  have key : (∑ l : Work.BoseB4.Excited m, ∑ l' : Work.BoseB4.Excited m,
        v l * (C * (if l = l' then (1 : ℝ) else 0)
                - ∑ k : Mode, f k l.1 * f k l'.1) * v l')
      = C * ∑ l : Fin m, (if h : l ≠ 0 then v ⟨l, h⟩ else 0) ^ 2
        - ∑ k : Mode, (∑ i : Fin m, f k i * (if h : i ≠ 0 then v ⟨i, h⟩ else 0)) ^ 2 := by
    rw [show (∑ l : Work.BoseB4.Excited m, ∑ l' : Work.BoseB4.Excited m,
          v l * (C * (if l = l' then (1 : ℝ) else 0)
                  - ∑ k : Mode, f k l.1 * f k l'.1) * v l')
        = ∑ l : Work.BoseB4.Excited m, ∑ l' : Work.BoseB4.Excited m,
          v l * (C * (if l.1 = l'.1 then (1 : ℝ) else 0)
                  - ∑ k : Mode, f k l.1 * f k l'.1) * v l' from by
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro l' _
      by_cases h : l.1 = l'.1
      · rw [if_pos (Subtype.ext h), if_pos h]
      · rw [if_neg (fun hh => h (Subtype.ext_iff.mp hh)), if_neg h]]
    rw [frame_excited_restrict (p := fun l : Fin m => l ≠ 0)
      (F := fun l l' => C * (if l = l' then (1 : ℝ) else 0) - ∑ k : Mode, f k l * f k l') v]
    rw [frame_core_identity (f := f) (C := C)
      (w := fun l : Fin m => if h : l ≠ 0 then v ⟨l, h⟩ else 0)]
  rw [key]
  have hSw := hS (fun l : Fin m => if h : l ≠ 0 then v ⟨l, h⟩ else 0)
  simp only [Work.BoseB4.gram] at hSw
  linarith [hSw]

end Work.BoseBoxFock.Frame
