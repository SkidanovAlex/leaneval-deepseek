import Mathlib
import Submission.Work.Peluse.SwapC.Basic
import Submission.Work.Peluse.Ulower.cubeTerm_tail

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## Splitting a function out of a finite function type

`∑_{h : Fin (k+1) → X} F h = ∑_{m : X} ∑_{hs : Fin k → X} F (Fin.cons m hs)`. -/

private lemma consEquiv_eq_cons {k : ℕ} {X : Type*} (m : X) (hs : Fin k → X) :
    (Fin.consEquiv (fun _ : Fin (k+1) => X)) (m, hs) = Fin.cons m hs := by
  funext i
  rw [Fin.consEquiv_apply]

private lemma sum_cons_equiv' {k : ℕ} {X : Type*} [Fintype X]
    (F : (Fin (k+1) → X) → ℂ) :
    ∑ h : Fin (k+1) → X, F h = ∑ m : X, ∑ hs : Fin k → X, F (Fin.cons m hs) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => X)) F]
  rw [Fintype.sum_prod_type]
  simp only [consEquiv_eq_cons]

/-- Swapping the two middle sums of a four-fold sum. -/
private lemma sum_swap_mid {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (G : A → B → C → D → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, G a b c d) = ∑ a, ∑ c, ∑ b, ∑ d, G a b c d := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact Finset.sum_comm

/-- Pulling a constant out of a double sum. -/
private lemma sum_const_mul_sum {X : Type*} [Fintype X] (c : ℂ) (V : X → X → ℂ) :
    (∑ m : X, ∑ m' : X, c * V m m') = c * ∑ m : X, ∑ m' : X, V m m' := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  exact (Finset.mul_sum Finset.univ (fun m' => V m m') c).symm

/-! ## Splitting the slot direction in its first coordinate

For the slot directions `pdir (q₁ j) (q₂ j)`, the function `j ↦ pdir (q₁ j) (q₂ j) (h j)` with
`h = Fin.cons m hs` splits as `Fin.cons (pdir (q₁ 0) (q₂ 0) m) (fun i => pdir (q₁ i.succ) (q₂ i.succ) (hs i))`. -/

private lemma pdir_cons {d M : ℕ} (q₁ q₂ : Fin (d+1) → ℤ)
    (m : Fin M × Fin M) (hs : Fin d → Fin M × Fin M) :
    (fun j : Fin (d+1) => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
      = Fin.cons (pdir (q₁ 0) (q₂ 0) m)
          (fun i : Fin d => pdir (q₁ i.succ) (q₂ i.succ) (hs i)) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero]
  · intro i; simp [Fin.cons_succ]

/-! ## The cube term splits in the first coordinate -/

/-- Peeling the first coordinate of the cube term, `DeltaP`-form. -/
private lemma cubeTerm_cons_deltaP' {k : ℕ} (a b : ℤ) (Hd Hd' : Fin k → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm (Fin.cons a Hd) (Fin.cons b Hd') f x
      = Work.Peluse.cubeTerm Hd Hd' (Work.Peluse.DeltaP a b f) x := by
  rw [Work.Peluse.Ulower.cubeTerm_tail, Fin.tail_cons, Fin.tail_cons, Fin.cons_zero, Fin.cons_zero]
  congr 1
  funext y
  rw [Work.Peluse.DeltaP]
  exact mul_comm _ _

/-- The cube term of order `d + 1` at the slot shifts of `Fin.cons m hs`, `Fin.cons m' hs'` is the
cube term of order `d` of the `Δ'`-difference along the head slots, at the tail slot shifts. -/
private lemma cubeTerm_cons_deltaP {d M : ℕ} (q₁ q₂ : Fin (d+1) → ℤ)
    (m m' : Fin M × Fin M) (hs hs' : Fin d → Fin M × Fin M) (f : ℤ → ℂ) (x : ℤ) :
    (∏ ω : Fin (d+1) → Bool, (star^[weight ω])
        (f (x + cornerShift
          (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
          (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m' hs' : Fin (d+1) → Fin M × Fin M) j)) ω)))
      = ∏ ω : Fin d → Bool, (star^[weight ω])
        (DeltaP (pdir (q₁ 0) (q₂ 0) m) (pdir (q₁ 0) (q₂ 0) m') f
          (x + cornerShift (fun i => pdir (q₁ i.succ) (q₂ i.succ) (hs i))
                           (fun i => pdir (q₁ i.succ) (q₂ i.succ) (hs' i)) ω)) := by
  rw [show (∏ ω : Fin (d+1) → Bool, (star^[weight ω])
        (f (x + cornerShift
          (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
          (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m' hs' : Fin (d+1) → Fin M × Fin M) j)) ω)))
      = Work.Peluse.cubeTerm (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
          (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m' hs' : Fin (d+1) → Fin M × Fin M) j)) f x from rfl]
  rw [pdir_cons (d := d) q₁ q₂ m hs, pdir_cons (d := d) q₁ q₂ m' hs']
  rw [cubeTerm_cons_deltaP']
  rfl

/-! ## The raw (unnormalised) peel -/

/-- The unnormalised multiset box sum of order `d + 1` splits in the first slot. -/
private lemma pbox_raw_peel (d : ℕ) (q₁ q₂ : Fin (d+1) → ℤ) (M : ℕ) (f : ℤ → ℂ) :
    (∑ h : Fin (d+1) → Fin M × Fin M, ∑ h' : Fin (d+1) → Fin M × Fin M,
        ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
          (f (x + cornerShift (fun j => pdir (q₁ j) (q₂ j) (h j))
                              (fun j => pdir (q₁ j) (q₂ j) (h' j)) ω)))
      = ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          ∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
            ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
              (DeltaP (pdir (q₁ 0) (q₂ 0) m) (pdir (q₁ 0) (q₂ 0) m') f
                (x + cornerShift (fun i => pdir (q₁ i.succ) (q₂ i.succ) (h i))
                                 (fun i => pdir (q₁ i.succ) (q₂ i.succ) (h' i)) ω)) := by
  have h1 : (∑ h : Fin (d+1) → Fin M × Fin M, ∑ h' : Fin (d+1) → Fin M × Fin M,
        ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
          (f (x + cornerShift (fun j => pdir (q₁ j) (q₂ j) (h j))
                              (fun j => pdir (q₁ j) (q₂ j) (h' j)) ω)))
      = ∑ m : Fin M × Fin M, ∑ hs : Fin d → Fin M × Fin M,
          ∑ h' : Fin (d+1) → Fin M × Fin M,
            ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
              (f (x + cornerShift
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
                    (fun j => pdir (q₁ j) (q₂ j) (h' j)) ω)) :=
    sum_cons_equiv' (F := fun h => ∑ h' : Fin (d+1) → Fin M × Fin M,
        ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
          (f (x + cornerShift (fun j => pdir (q₁ j) (q₂ j) (h j))
                              (fun j => pdir (q₁ j) (q₂ j) (h' j)) ω)))
  have h2 : (∑ m : Fin M × Fin M, ∑ hs : Fin d → Fin M × Fin M,
          ∑ h' : Fin (d+1) → Fin M × Fin M,
            ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
              (f (x + cornerShift
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
                    (fun j => pdir (q₁ j) (q₂ j) (h' j)) ω)))
      = ∑ m : Fin M × Fin M, ∑ hs : Fin d → Fin M × Fin M,
          ∑ m' : Fin M × Fin M, ∑ hs' : Fin d → Fin M × Fin M,
            ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
              (f (x + cornerShift
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m' hs' : Fin (d+1) → Fin M × Fin M) j)) ω)) := by
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun hs _ => ?_))
    exact sum_cons_equiv' (F := fun h' => ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
              (f (x + cornerShift
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
                    (fun j => pdir (q₁ j) (q₂ j) (h' j)) ω)))
  have h3 : (∑ m : Fin M × Fin M, ∑ hs : Fin d → Fin M × Fin M,
          ∑ m' : Fin M × Fin M, ∑ hs' : Fin d → Fin M × Fin M,
            ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
              (f (x + cornerShift
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m' hs' : Fin (d+1) → Fin M × Fin M) j)) ω)))
      = ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          ∑ hs : Fin d → Fin M × Fin M, ∑ hs' : Fin d → Fin M × Fin M,
            ∑' x : ℤ, ∏ ω : Fin (d+1) → Bool, (star^[weight ω])
              (f (x + cornerShift
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m hs : Fin (d+1) → Fin M × Fin M) j))
                    (fun j => pdir (q₁ j) (q₂ j) ((Fin.cons m' hs' : Fin (d+1) → Fin M × Fin M) j)) ω)) :=
    sum_swap_mid _
  rw [h1, h2, h3]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ =>
    Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ => ?_))))
  exact tsum_congr (fun x => cubeTerm_cons_deltaP q₁ q₂ m m' hs hs' f x)

/-- **The peel (inductive formula) for the multiset box sum.**  Splitting off the first slot
of `pboxSum (d+1)` returns the average over the index set of that slot of the level-`d` box sum of
the `Δ'`-difference: this is the exact analogue of the workspace's proved
`Work.Peluse.Ulower.boxSumPow_split` for the *multiset* slots `q₁ k[M] − q₂ k[M]` of the frozen
vocabulary `Work.Peluse.LadderP.Swap`.

Proof route (mirror of `Ulower/boxSumPow_split.lean`): the cube term of order `d+1` splits in the
first coordinate, `∏_{ω : Fin (d+1) → Bool} C^{|ω|} f (x + cornerShift (cons a hs) (cons b hs') ω)
= ∏_{τ : Fin d → Bool} C^{|τ|} (DeltaP a b f) (x + cornerShift hs hs' τ)` (`cubeTermZ_cons`), the
two shift sums split by `Fin.consEquiv`, and the normalising constants split by `pow_succ`. -/
theorem pbox_peel (d : ℕ) (q₁ q₂ : Fin (d + 1) → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.LadderP.Swap.pboxSum (d + 1) q₁ q₂ M S f
      = ((M : ℂ) ^ 4)⁻¹ *
        ∑ m : Fin M × Fin M, ∑ m' : Fin M × Fin M,
          Work.Peluse.LadderP.Swap.pboxSum d (fun i => q₁ i.succ) (fun i => q₂ i.succ) M S
            (Work.Peluse.DeltaP (Work.Peluse.LadderP.Swap.pdir (q₁ 0) (q₂ 0) m)
              (Work.Peluse.LadderP.Swap.pdir (q₁ 0) (q₂ 0) m') f) := by
  simp only [pboxSum]
  rw [pbox_raw_peel d q₁ q₂ M f]
  rw [sum_const_mul_sum]
  rw [pow_succ]
  ring

end

end Work.Peluse.SwapC
