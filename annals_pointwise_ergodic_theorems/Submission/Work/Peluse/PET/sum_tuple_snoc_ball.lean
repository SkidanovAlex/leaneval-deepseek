/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# Splitting the shift-tuple sums of the box sum along the last coordinate

The double sum over the shift tuples `h₁, h₂ : (i : Fin (n+1)) → {x // x ∈ Q i}` occurring in the
box sum can be reorganised according to the last coordinate: writing a tuple as `Fin.snoc hs a`
with `hs : (i : Fin n) → {x // x ∈ Q i.castSucc}` its `Fin.init` and `a ∈ Q (Fin.last n)` its last
entry, and bringing the two `a, b`-sums past the `x`-sum, we obtain

`∑_{h₁,h₂} ∑_{x ∈ ball} cubeTermZ Q h h₁ h₂ x
   = ∑_{hs,hs'} ∑_{x ∈ ball} ∑_{a,b} cubeTermZ Q h (snoc hs a) (snoc hs' b) x`.

This is the bookkeeping step that turns the `(n+1)`-dimensional box sum into a sum of squares over
`x + a`, `a ∈ Q (Fin.last n)` (compare `Work.Peluse.BoxNorm.rawSum_eq_cubeNormSqSum`, which does
the same for the *first* coordinate via `Fin.cons`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section

/-- Splitting a sum over `(i : Fin (n+1)) → {x // x ∈ Q i}` into its tail `Fin.init` and its last
coordinate `Fin.last n`, via `Fin.snoc`. -/
lemma sum_snoc_equiv {n : ℕ} {Q : Fin (n + 1) → Finset ℤ}
    (F : ((i : Fin (n + 1)) → {x : ℤ // x ∈ Q i}) → ℂ) :
    ∑ z, F z = ∑ hs : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
      ∑ a : {y : ℤ // y ∈ Q (Fin.last n)}, F (Fin.snoc hs a) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun i => {x : ℤ // x ∈ Q i})) F]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun a _ => ?_))
  apply congrArg F
  funext i
  rw [Fin.snocEquiv_apply]

theorem sum_tuple_snoc_ball {n : ℕ} (Q : Fin (n + 1) → Finset ℤ) (h : ℤ → ℂ) (N : ℕ) :
    (∑ h₁ : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
        ∑ h₂ : (i : Fin (n + 1)) → {x : ℤ // x ∈ Q i},
          ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
            Work.Peluse.BoxNorm.cubeTermZ Q h h₁ h₂ x)
      = ∑ hs : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
          ∑ hs' : (i : Fin n) → {x : ℤ // x ∈ Q i.castSucc},
            ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
              ∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
                ∑ b : {y : ℤ // y ∈ Q (Fin.last n)},
                  Work.Peluse.BoxNorm.cubeTermZ Q h (Fin.snoc hs a) (Fin.snoc hs' b) x := by
  classical
  have step1 : (∑ h₁ : ((i : Fin (n+1)) → {x : ℤ // x ∈ Q i}),
        ∑ h₂ : ((i : Fin (n+1)) → {x : ℤ // x ∈ Q i}),
          ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
            Work.Peluse.BoxNorm.cubeTermZ Q h h₁ h₂ x)
      = ∑ hs : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
          ∑ a : {y : ℤ // y ∈ Q (Fin.last n)},
            ∑ hs' : ((i : Fin n) → {x : ℤ // x ∈ Q i.castSucc}),
              ∑ b : {y : ℤ // y ∈ Q (Fin.last n)},
                ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
                  Work.Peluse.BoxNorm.cubeTermZ Q h (Fin.snoc hs a) (Fin.snoc hs' b) x := by
    rw [sum_snoc_equiv (fun h₁ => ∑ h₂ : ((i : Fin (n+1)) → {x : ℤ // x ∈ Q i}),
          ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
            Work.Peluse.BoxNorm.cubeTermZ Q h h₁ h₂ x)]
    refine Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun a _ => ?_))
    exact sum_snoc_equiv (fun h₂ => ∑ x ∈ Work.Peluse.BoxNorm.ball (n + 1) Q N,
            Work.Peluse.BoxNorm.cubeTermZ Q h (Fin.snoc hs a) h₂ x)
  rw [step1]
  exact Work.Peluse.BoxNorm.Aux.reorder_pair (Work.Peluse.BoxNorm.ball (n + 1) Q N)
    (fun hs a hs' b x => Work.Peluse.BoxNorm.cubeTermZ Q h (Fin.snoc hs a) (Fin.snoc hs' b) x)

end

end Work.Peluse.PET
