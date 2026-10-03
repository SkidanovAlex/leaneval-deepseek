/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Peel.tsum_shift_pair
import Submission.Work.Peluse.Peel.rawSum_succ_peel
import Submission.Work.Peluse.Peel.rawSum_deltaP

/-!
# Peeling the first coordinate of Peluse's box sum

Peluse's box-norm power of order `t + 1` on the shift sets `Q : Fin (t+1) → Finset ℤ` and the
support `S` is the normalised cube average

`boxSumPow (t+1) Q S f
   = (1/|S|) (∏_i |Q i|⁻¹)² ∑_{h, h' ∈ ∏_i Q i} ∑_x ∏_{ω : Fin (t+1) → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`.

Splitting off the first coordinate of the two shift tuples, `h = (a, hs)`, `h' = (b, hs')`, the
cube term factorises (`Work.Peluse.BoxNorm.cubeTerm_cons`) as

`∏_{ω} C^{|ω|} f (x + ω·(a,hs) + (1-ω)·(b,hs'))
    = Φ_{hs,hs'}(x + b) · conj (Φ_{hs,hs'}(x + a))`,

where `Φ_{hs,hs'}(v) = ∏_{τ : Fin t → Bool} C^{|τ|} f (v + τ·hs + (1-τ)·hs')` is the cube term of
one lower dimension (`Work.Peluse.BoxNorm.redCube`, called `rCube` here on plain tuples).  Since
`Δ'_{(h,h')} f (u) = f (u + h) · conj (f (u + h'))`, Peluse's recursion on the box norm says that
the `(t+1)`-fold box sum of `f` is the `t`-fold box sum of the difference `Δ'_{(a,b)} f`, averaged
over the two possible first coordinates `a`, `b ∈ Q 0`:

`boxSumPow (t+1) Q S f = |Q 0|⁻² ∑_{a ∈ Q 0} ∑_{b ∈ Q 0} boxSumPow t Q[1:] S (Δ'_{(a,b)} f)`.

This is the identity proved below (`Work.Peluse.Peel.boxSumPow_peel`), the "peel" (or
level-lowering) step of the recursion.

The proof is a reduction of both sides to a common normal form

`|Q 0|⁻² · boxScaling t Q[1:] S · ∑_{hs,hs'} ∑_{a,b} rW_{hs,hs'}(a - b)`,
   where `rW_{hs,hs'}(e) = ∑_y Φ_{hs,hs'}(y) · conj (Φ_{hs,hs'}(y + e))`:

* on the left, `rawSum_succ_peel` splits the two shift sums and `cubeTerm_cons` factorises the cube
  term, leaving the `∑_x` of `Φ(x+b)·conj (Φ(x+a))`, which the reindexing `tsum_shift_pair` turns
  into `rW (a - b)`;
* on the right, `rawSum_deltaP` expands each `boxSumPow t Q[1:] S (Δ'_{(a,b)} f)` into the product
  of the two cube terms, whose `∑_x` is `∑_x Φ(x+a)·conj (Φ(x+b)) = rW (b - a)`;
* the two sums differ only by the flip `(a,b) ↦ (b,a)` of the summation indices, and by the
  splitting `|Q 0|⁻¹` of the normalising constant `boxScaling_succ_aux`.

## Main result

* `Work.Peluse.Peel.boxSumPow_peel`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Peel

noncomputable section

/-! ## The reduced cube term and the shift pairing -/

/-- A shift set `Q` as a type, so that `∑ a : BoxC Q` is the sum over `Q`. -/
abbrev BoxC (Q : Finset ℤ) : Type := {y : ℤ // y ∈ Q}

/-- The product `∏ i, Q i` of the shift sets, as a type. -/
abbrev BoxT (t : ℕ) (Q : Fin t → Finset ℤ) : Type := (i : Fin t) → {x : ℤ // x ∈ Q i}

/-- The reduced cube term of order `t` built from the plain integer tuples `hs`, `hs'`:
`Φ(v) = ∏_{τ : Fin t → Bool} C^{|τ|} f (v + τ·hs + (1-τ)·hs')`.  This is
`Work.Peluse.BoxNorm.redCube` with the subtypes replaced by their values. -/
def rCube {t : ℕ} (hs hs' : Fin t → ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun v => ∏ τ : Fin t → Bool,
    (star^[Work.Peluse.weight τ]) (f (v + Work.Peluse.cornerShift hs hs' τ))

/-- `Work.Peluse.BoxNorm.redCube` is `rCube` on subtype tuples. -/
lemma redCube_eq_rCube {t : ℕ} (Q : Fin (t + 1) → Finset ℤ)
    (hs hs' : BoxT t (fun i : Fin t => Q i.succ)) (f : ℤ → ℂ) :
    Work.Peluse.BoxNorm.redCube Q hs hs' f
      = rCube (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f := rfl

/-- The shift pairing `∑_y Φ y · conj (Φ (y + e))` of a reduced cube term. -/
def rW {t : ℕ} (hs hs' : Fin t → ℤ) (f : ℤ → ℂ) (e : ℤ) : ℂ :=
  ∑' y : ℤ, rCube hs hs' f y * star (rCube hs hs' f (y + e))

/-! ## Elementary bookkeeping of the normalising constants and the finite sums -/

/-- The normalising constant of the box sum splits off the first shift set. -/
lemma boxScaling_succ_aux (t : ℕ) (Q : Fin (t + 1) → Finset ℤ) (S : Finset ℤ) :
    Work.Peluse.BoxNorm.boxScaling (t + 1) Q S
      = ((Q 0).card : ℝ)⁻¹ * ((Q 0).card : ℝ)⁻¹
        * Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S := by
  rw [Work.Peluse.BoxNorm.boxScaling, Work.Peluse.BoxNorm.boxScaling, Fin.prod_univ_succ]
  ring

/-- Swapping the two pairs of a doubly nested fourfold sum. -/
lemma sum4_swap_pairs {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (G : A → B → C → D → ℂ) :
    (∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, G a b c d)
      = ∑ c : C, ∑ d : D, ∑ a : A, ∑ b : B, G a b c d := by
  calc (∑ a : A, ∑ b : B, ∑ c : C, ∑ d : D, G a b c d)
      = ∑ a : A, ∑ c : C, ∑ b : B, ∑ d : D, G a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c : C, ∑ a : A, ∑ b : B, ∑ d : D, G a b c d := Finset.sum_comm
    _ = ∑ c : C, ∑ a : A, ∑ d : D, ∑ b : B, G a b c d :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    _ = ∑ c : C, ∑ d : D, ∑ a : A, ∑ b : B, G a b c d :=
        Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

/-- The two arguments of a double sum can be exchanged. -/
lemma sum_flip {A : Type*} [Fintype A] (F : A → A → ℂ) :
    (∑ a : A, ∑ b : A, F a b) = ∑ a : A, ∑ b : A, F b a :=
  (Finset.sum_comm (f := fun a b : A => F b a)).symm

/-- A constant can be pulled out of a double sum. -/
lemma mul_sum2 {A B : Type*} [Fintype A] [Fintype B] (c : ℂ) (F : A → B → ℂ) :
    (∑ a : A, ∑ b : B, c * F a b) = c * ∑ a : A, ∑ b : B, F a b := by
  rw [show (∑ a : A, ∑ b : B, c * F a b) = ∑ a : A, c * (∑ b : B, F a b) from
    Finset.sum_congr rfl
      (fun a _ => (Finset.mul_sum (s := Finset.univ) (f := fun b : B => F a b) c).symm)]
  rw [← Finset.mul_sum]

/-! ## The peel identity -/

/-- **Peeling the first coordinate of the box sum.**  The `2^{t+1}`-th power of the box norm of
`f` on `Q₁, …, Q_{t+1}` is the average over `a, b ∈ Q₁` of the `2^t`-th power of the box norm of
the difference `Δ'_{(a,b)} f (u) = f (u + a) · conj (f (u + b))` on `Q₂, …, Q_{t+1}`. -/
theorem boxSumPow_peel {t : ℕ} (Q : Fin (t + 1) → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow (t + 1) Q S f
      = ((Q 0).card : ℂ)⁻¹ * ((Q 0).card : ℂ)⁻¹ *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          Work.Peluse.boxSumPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
  classical
  -- The common normal form of both sides.
  let SW : ℂ := ∑ hs : BoxT t (fun i : Fin t => Q i.succ),
        ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
        ∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
          rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f ((a : ℤ) - (b : ℤ))
  have hSW : SW = (∑ hs : BoxT t (fun i : Fin t => Q i.succ),
        ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
        ∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
          rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f ((a : ℤ) - (b : ℤ))) := rfl
  -- the `∑_x` of a reduced cube term shifted in one variable is the pairing `rW`
  have htsum : ∀ (hs hs' : BoxT t (fun i : Fin t => Q i.succ)) (a b : BoxC (Q 0)),
      (∑' x : ℤ, Work.Peluse.BoxNorm.redCube Q hs hs' f (x + (b : ℤ))
          * star (Work.Peluse.BoxNorm.redCube Q hs hs' f (x + (a : ℤ))))
        = rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f ((a : ℤ) - (b : ℤ)) :=
    fun hs hs' a b =>
      tsum_shift_pair (Work.Peluse.BoxNorm.redCube Q hs hs' f) (a : ℤ) (b : ℤ)
  -- the left-hand side
  have hL : Work.Peluse.boxSumPow (t + 1) Q S f
      = ((Q 0).card : ℂ)⁻¹ * ((Q 0).card : ℂ)⁻¹ *
        ((Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) * SW) := by
    rw [Work.Peluse.BoxNorm.boxSumPow_eq_scaling, boxScaling_succ_aux, rawSum_succ_peel]
    push_cast
    have hbig : (∑ hs : BoxT t (fun i : Fin t => Q i.succ),
              ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
              ∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
                ∑' x : ℤ, Work.Peluse.BoxNorm.redCube Q hs hs' f (x + (b : ℤ))
                  * star (Work.Peluse.BoxNorm.redCube Q hs hs' f (x + (a : ℤ)))) = SW := by
      refine (Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ =>
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          htsum hs hs' a b))))).trans hSW
    rw [hbig]
    ring
  -- the right-hand side
  have hR : ((Q 0).card : ℂ)⁻¹ * ((Q 0).card : ℂ)⁻¹ *
        (∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          Work.Peluse.boxSumPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))))
      = ((Q 0).card : ℂ)⁻¹ * ((Q 0).card : ℂ)⁻¹ *
        ((Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) * SW) := by
    -- the sums over `Q 0` are sums over the subtype
    have hsub : (∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          Work.Peluse.boxSumPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))))
        = (∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
            Work.Peluse.boxSumPow t (fun i : Fin t => Q i.succ) S
              (fun u : ℤ => f (u + (a : ℤ)) * star (f (u + (b : ℤ))))) := by
      rw [Finset.sum_subtype (s := Q 0) (p := fun x : ℤ => x ∈ Q 0) (fun x => Iff.rfl)]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      exact Finset.sum_subtype (s := Q 0) (p := fun x : ℤ => x ∈ Q 0) (fun x => Iff.rfl)
        (f := fun h' => Work.Peluse.boxSumPow t (fun i : Fin t => Q i.succ) S
              (fun u : ℤ => f (u + (a : ℤ)) * star (f (u + h'))))
    -- each summand expands into the pairing of the reduced cube term
    have hterm : ∀ a b : BoxC (Q 0),
        Work.Peluse.boxSumPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + (a : ℤ)) * star (f (u + (b : ℤ))))
          = (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
            (∑ hs : BoxT t (fun i : Fin t => Q i.succ),
             ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
               rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                 ((b : ℤ) - (a : ℤ))) := by
      intro a b
      rw [Work.Peluse.BoxNorm.boxSumPow_eq_scaling, rawSum_deltaP]
      congr 1
      refine Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ => ?_))
      exact tsum_shift_pair (rCube (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f)
        (b : ℤ) (a : ℤ)
    -- pull out the constant
    have hc : (∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
          (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
            (∑ hs : BoxT t (fun i : Fin t => Q i.succ),
             ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
               rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                 ((b : ℤ) - (a : ℤ))))
        = (Work.Peluse.BoxNorm.boxScaling t (fun i : Fin t => Q i.succ) S : ℂ) *
          (∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
            ∑ hs : BoxT t (fun i : Fin t => Q i.succ),
            ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
              rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                ((b : ℤ) - (a : ℤ))) :=
      mul_sum2 (A := BoxC (Q 0)) (B := BoxC (Q 0)) _
        (fun a b => ∑ hs : BoxT t (fun i : Fin t => Q i.succ),
             ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
               rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                 ((b : ℤ) - (a : ℤ)))
    -- reorder the sums and flip the pair `(a, b)`
    have hd : (∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
            ∑ hs : BoxT t (fun i : Fin t => Q i.succ),
            ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
              rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                ((b : ℤ) - (a : ℤ))) = SW := by
      have h1 : (∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
            ∑ hs : BoxT t (fun i : Fin t => Q i.succ),
            ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
              rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                ((b : ℤ) - (a : ℤ)))
          = (∑ hs : BoxT t (fun i : Fin t => Q i.succ),
             ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
             ∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
               rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                 ((b : ℤ) - (a : ℤ))) :=
        sum4_swap_pairs (G := fun (a b : BoxC (Q 0))
            (hs hs' : BoxT t (fun i : Fin t => Q i.succ)) =>
            rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f ((b : ℤ) - (a : ℤ)))
      have h2 : (∑ hs : BoxT t (fun i : Fin t => Q i.succ),
             ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
             ∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
               rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                 ((b : ℤ) - (a : ℤ)))
          = (∑ hs : BoxT t (fun i : Fin t => Q i.succ),
             ∑ hs' : BoxT t (fun i : Fin t => Q i.succ),
             ∑ a : BoxC (Q 0), ∑ b : BoxC (Q 0),
               rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f
                 ((a : ℤ) - (b : ℤ))) :=
        Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ =>
          sum_flip (fun a b : BoxC (Q 0) =>
            rW (fun i : Fin t => (hs i).1) (fun i : Fin t => (hs' i).1) f ((b : ℤ) - (a : ℤ)))))
      exact h1.trans (h2.trans hSW)
    rw [hsub]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))]
    rw [hc]
    rw [hd]
  exact hL.trans hR.symm

end

end Work.Peluse.Peel
