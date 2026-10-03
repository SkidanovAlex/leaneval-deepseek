/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# Relabelling invariance of the box sum

The box sum `boxSumPow t Q S f` of Peluse's Definition 2.1 is

`(1/|S|) (∏_i 1/|Q_i|)^2 ∑_{x} E_{h_i,h_i' ∈ Q_i} ∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`.

Every ingredient of it is attached to the coordinate `i : Fin t` only through the set `Q i` -- the
sum over `h` runs over the product `∏_i Q_i`, the product over `ω` runs over all `2^t` sign
patterns, and the weight `|ω|` counts the coordinates on which `ω` is `true`.  Consequently the
whole quantity is invariant under relabelling the coordinates by a permutation of `Fin t`:

`boxSumPow t (fun i => Q (σ i)) S f = boxSumPow t Q S f`   for `σ : Fin t → Fin t` bijective.

This is `Work.Peluse.Track.boxSumPow_comp_bij`.  It lets one move a distinguished coordinate (for
instance a degenerate set `{0}`) into any position, which is what
`Work.Peluse.Track.boxNormPow_v2_degenerate` uses.

## Proof

`boxSumPow_eq_scaling` writes the box sum as `boxScaling t Q S * rawSum t Q f`, separating the
normalising constant from the raw cube average.  Both factors are invariant:

* `boxScaling` is a product over `i : Fin t` of `|Q i|⁻¹`, reindexed with `Equiv.prod_comp`;
* `rawSum` sums over `∏_i Q_i` and over the sign patterns `ω`; the reindexing of the two
  dependent sums uses `Equiv.piCongrLeft`, and the invariance of the cube term
  `∏_ω C^{|ω|} f (x + cornerShift u v ω)` under `u ↦ u ∘ e`, `v ↦ v ∘ e` is the observation that
  composing `ω` with `e.symm` permutes the set of sign patterns while preserving the weight.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Track

noncomputable section

/-! ## Invariance of the weight, the corner shift and the cube term -/

private lemma weight_eq_sum {t : ℕ} (ω : Fin t → Bool) :
    Work.Peluse.weight ω = ∑ i : Fin t, if ω i then 1 else 0 := by
  rw [Work.Peluse.weight, Finset.card_filter]

/-- The weight `|ω|` only depends on the multiset of coordinates on which `ω` is `true`, hence is
invariant under relabelling the coordinates. -/
private lemma weight_comp {t : ℕ} (e : Fin t ≃ Fin t) (ω : Fin t → Bool) :
    Work.Peluse.weight (fun i => ω (e i)) = Work.Peluse.weight ω := by
  rw [weight_eq_sum, weight_eq_sum]
  exact Equiv.sum_comp e (fun i => if ω i then 1 else 0)

/-- Relabelling the coordinates of the corner shift: replacing `(u, v)` by `(u ∘ e, v ∘ e)` is
the same as replacing the sign pattern `ω` by `ω ∘ e.symm`. -/
private lemma cornerShift_comp {t : ℕ} (e : Fin t ≃ Fin t) (u v : Fin t → ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (fun i => u (e i)) (fun i => v (e i)) ω
      = Work.Peluse.cornerShift u v (fun i => ω (e.symm i)) := by
  rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift]
  rw [← Equiv.sum_comp e (fun j => if ω (e.symm j) then u j else v j)]
  simp [Equiv.symm_apply_apply]

/-- The cube term `∏_{ω} C^{|ω|} f (x + cornerShift u v ω)` is invariant when the pair `(u, v)` is
composed with a permutation of the coordinates: composing `u`, `v` with `e` and `ω` with `e.symm`
is a relabelling of the index set of the product. -/
private lemma prod_star_perm {t : ℕ} (e : Fin t ≃ Fin t) (f : ℤ → ℂ) (u v : Fin t → ℤ)
    (x : ℤ) :
    (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (fun i => u (e i)) (fun i => v (e i)) ω)))
      = ∏ τ : Fin t → Bool, (star^[Work.Peluse.weight τ])
        (f (x + Work.Peluse.cornerShift u v τ)) := by
  let ρ : (Fin t → Bool) ≃ (Fin t → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  have hρ : ∀ ω, ρ ω = fun i => ω (e.symm i) := fun ω => by
    funext i; simp [ρ, Equiv.arrowCongr_apply]
  have hstep : ∀ ω : Fin t → Bool,
      (star^[Work.Peluse.weight ω])
          (f (x + Work.Peluse.cornerShift (fun i => u (e i)) (fun i => v (e i)) ω))
        = (star^[Work.Peluse.weight (ρ ω)]) (f (x + Work.Peluse.cornerShift u v (ρ ω))) := by
    intro ω
    rw [hρ ω, cornerShift_comp e u v ω, weight_comp e.symm ω]
  rw [Finset.prod_congr rfl (fun ω _ => hstep ω)]
  exact Equiv.prod_comp ρ (fun τ => (star^[Work.Peluse.weight τ])
      (f (x + Work.Peluse.cornerShift u v τ)))

/-! ## The raw cube average -/

/-- The tuple of values of a dependent family of integers. -/
private def tupleVal {t : ℕ} {Q : Fin t → Finset ℤ} (h : (i : Fin t) → {x : ℤ // x ∈ Q i}) :
    Fin t → ℤ := fun i => (h i).1

/-- The cube term of one fixed pair of shift tuples `u`, `v`, summed over `x`.  It is the summand
of `rawSum` after passing from the dependent shift tuples to their tuples of values. -/
private def cubeSumT (t : ℕ) (f : ℤ → ℂ) (u v : Fin t → ℤ) : ℂ :=
  ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
    (f (x + Work.Peluse.cornerShift u v ω))

private lemma rawSum_eq (t : ℕ) (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.BoxNorm.rawSum t Q f
      = ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            cubeSumT t f (tupleVal h) (tupleVal h') := rfl

private lemma cubeSumT_comp {t : ℕ} (e : Fin t ≃ Fin t) (f : ℤ → ℂ) (u v : Fin t → ℤ) :
    cubeSumT t f (fun i => u (e i)) (fun i => v (e i)) = cubeSumT t f u v := by
  unfold cubeSumT
  exact tsum_congr (fun x => prod_star_perm e f u v x)

/-- The raw cube average is invariant under relabelling the coordinates: reindexing the two
dependent sums over `∏_i Q_i` by `Equiv.piCongrLeft` turns the shift tuples into their composition
with the permutation, which `prod_star_perm` shows to be a relabelling of the cube term. -/
private lemma rawSum_comp {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) (e : Fin t ≃ Fin t) :
    Work.Peluse.BoxNorm.rawSum t (fun i => Q (e i)) f
      = Work.Peluse.BoxNorm.rawSum t Q f := by
  rw [rawSum_eq, rawSum_eq]
  let φ : ((j : Fin t) → {x : ℤ // x ∈ Q j}) ≃ ((i : Fin t) → {x : ℤ // x ∈ Q (e i)}) :=
    (Equiv.piCongrLeft (fun j : Fin t => {x : ℤ // x ∈ Q j}) e).symm
  have hval : ∀ H : (j : Fin t) → {x : ℤ // x ∈ Q j},
      tupleVal (φ H) = fun i => (H (e i)).1 := by
    intro H
    funext i
    show ((φ H) i).1 = (H (e i)).1
    exact congrArg Subtype.val
      (Equiv.piCongrLeft_symm_apply (fun j : Fin t => {x : ℤ // x ∈ Q j}) e H i)
  have key : ∀ (H H' : (j : Fin t) → {x : ℤ // x ∈ Q j}),
      cubeSumT t f (tupleVal (φ H)) (tupleVal (φ H'))
        = cubeSumT t f (tupleVal H) (tupleVal H') := by
    intro H H'
    rw [hval H, hval H']
    exact cubeSumT_comp e f (fun j => (H j).1) (fun j => (H' j).1)
  calc (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q (e i)},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q (e i)},
            cubeSumT t f (tupleVal h) (tupleVal h'))
      = ∑ H : (j : Fin t) → {x : ℤ // x ∈ Q j},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q (e i)},
            cubeSumT t f (tupleVal (φ H)) (tupleVal h') := by
        rw [← Equiv.sum_comp φ (fun h => ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q (e i)},
            cubeSumT t f (tupleVal h) (tupleVal h'))]
    _ = ∑ H : (j : Fin t) → {x : ℤ // x ∈ Q j},
          ∑ H' : (j : Fin t) → {x : ℤ // x ∈ Q j},
            cubeSumT t f (tupleVal (φ H)) (tupleVal (φ H')) := by
        refine Finset.sum_congr rfl (fun H _ => ?_)
        rw [← Equiv.sum_comp φ (fun h' => cubeSumT t f (tupleVal (φ H)) (tupleVal h'))]
    _ = ∑ H : (j : Fin t) → {x : ℤ // x ∈ Q j},
          ∑ H' : (j : Fin t) → {x : ℤ // x ∈ Q j},
            cubeSumT t f (tupleVal H) (tupleVal H') := by
        refine Finset.sum_congr rfl (fun H _ => Finset.sum_congr rfl (fun H' _ => key H H'))

/-! ## The normalising constant -/

private lemma boxScaling_comp {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (e : Fin t ≃ Fin t) :
    Work.Peluse.BoxNorm.boxScaling t (fun i => Q (e i)) S
      = Work.Peluse.BoxNorm.boxScaling t Q S := by
  unfold Work.Peluse.BoxNorm.boxScaling
  rw [Equiv.prod_comp e (fun i => ((Q i).card : ℝ)⁻¹)]

/-! ## The theorem -/

private lemma boxSumPow_comp_equiv {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (e : Fin t ≃ Fin t) :
    Work.Peluse.boxSumPow t (fun i => Q (e i)) S f = Work.Peluse.boxSumPow t Q S f := by
  rw [Work.Peluse.BoxNorm.boxSumPow_eq_scaling, Work.Peluse.BoxNorm.boxSumPow_eq_scaling,
    boxScaling_comp, rawSum_comp]

/-- **Relabelling invariance of the box sum.**  Permuting the coordinates `Fin t` simultaneously in
the family of sets `Q` leaves the box sum `boxSumPow t Q S f` unchanged. -/
theorem boxSumPow_comp_bij {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (σ : Fin t → Fin t) (hσ : Function.Bijective σ) :
    Work.Peluse.boxSumPow t (fun i => Q (σ i)) S f = Work.Peluse.boxSumPow t Q S f := by
  have h : (fun i => Q (σ i)) = (fun i => Q ((Equiv.ofBijective σ hσ) i)) := by
    funext i; rw [Equiv.ofBijective_apply]
  rw [h]
  exact boxSumPow_comp_equiv Q S f (Equiv.ofBijective σ hσ)

end

end Work.Peluse.Track
