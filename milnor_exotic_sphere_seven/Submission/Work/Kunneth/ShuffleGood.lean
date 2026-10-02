import Mathlib
import Submission.Work.Cohomology.Crux33.ShuffleIndex
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.KunnethEZ.ezGen_eval_pp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The exceptional `(p,q)`-shuffle of the cross product

For the Eilenberg–Zilber shuffle `Work.Cohomology.Crux33.ezGen p q X Y σ τ` (a sum over the
`(p,q)`-shuffles `S ∈ PShuffle p q`, i.e. over the `q`-element subsets of `Fin (p+q)` marking the
`N`-steps), the **cross product** cochain `Work.Kunneth.crossCochain X Y p q α β` evaluates on a
single shuffle cell as

  `(α × β)(σ ∘ a_S, τ ∘ b_S) = α(σ ∘ (front_p ∘ a_S)) · β(τ ∘ (back_q ∘ b_S))`.

Exactly one shuffle makes both relevant faces the identity: the shuffle with all `N`-steps **last**,
`S = {j : p ≤ j.val}` (`goodShufF p q`).  It has sign `+1` (its inversion count is `0`), and for
every other shuffle the relevant `Y`-face `back_q ∘ b_S` is non-surjective, so the corresponding
`Y`-simplex is degenerate.

This file collects those four facts about `goodShufF p q`, for **arbitrary** `p` and `q`: they are
the engine of the Kronecker rule `⟨a × b, ezChain u v⟩ = ⟨a,u⟩·⟨b,v⟩`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology
open Work.Cohomology.Crux33

/-- The exceptional `(p,q)`-shuffle: the positions of the `q` `N`-steps are **last**, i.e.
`S = {j : p ≤ j.val}`. -/
def goodShufF (p q : ℕ) : Finset (Fin (p + q)) :=
  (Finset.univ : Finset (Fin (p + q))).filter (fun j => p ≤ j.val)

/-- Membership in the exceptional shuffle. -/
theorem mem_goodShufF (p q : ℕ) (j : Fin (p + q)) : j ∈ goodShufF p q ↔ p ≤ j.val := by
  simp [goodShufF]

/-- The exceptional shuffle has `q` elements. -/
theorem goodShufF_card (p q : ℕ) : (goodShufF p q).card = q := by
  have h : (goodShufF p q).card = (Finset.univ : Finset (Fin q)).card := by
    refine Finset.card_bij
      (fun (j : Fin (p + q)) (hj : j ∈ goodShufF p q) => (⟨j.val - p, by
        rw [mem_goodShufF] at hj
        have := j.isLt
        omega⟩ : Fin q)) ?_ ?_ ?_
    · intro a ha
      simp
    · intro a ha b hb hab
      rw [mem_goodShufF] at ha hb
      apply Fin.ext
      have := Fin.ext_iff.mp hab
      simp only [Fin.val_mk] at this
      omega
    · intro b _
      exact ⟨⟨p + b.val, by have := b.isLt; omega⟩,
        by rw [mem_goodShufF]; simp,
        by apply Fin.ext; simp only [Fin.val_mk]; omega⟩
  rw [h, Finset.card_univ, Fintype.card_fin]

/-- The exceptional `(p,q)`-shuffle. -/
def goodShuf (p q : ℕ) : PShuffle p q := ⟨goodShufF p q, goodShufF_card p q⟩

/-- The number of `E`-steps of the exceptional shuffle before the vertex `i` is `min i p`. -/
theorem pA_goodShufF (p q : ℕ) (i : Fin (p + q + 1)) : pA (goodShufF p q) i = min i.val p := by
  rw [pA]
  have hset : ((Finset.univ : Finset (Fin (p + q))).filter (fun j => j.val < i.val))
        \ goodShufF p q
      = (Finset.univ : Finset (Fin (p + q))).filter (fun j => j.val < min i.val p) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, mem_goodShufF]
    omega
  rw [hset, Work.KunnethEZ.card_filter_val_lt]
  have hi : i.val ≤ p + q := by have := i.isLt; omega
  omega

/-- The number of `N`-steps of the exceptional shuffle before the vertex `i` is `i - p`. -/
theorem pB_goodShufF (p q : ℕ) (i : Fin (p + q + 1)) : pB (goodShufF p q) i = i.val - p := by
  rw [pB]
  have hset : (goodShufF p q).filter (fun j => j.val < i.val)
      = (Finset.univ : Finset (Fin (p + q))).filter (fun j => p ≤ j.val ∧ j.val < i.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodShufF]
  rw [hset]
  have hcard : ((Finset.univ : Finset (Fin (p + q))).filter
        (fun j => p ≤ j.val ∧ j.val < i.val)).card = (Finset.range (i.val - p)).card := by
    refine Finset.card_bij (fun j _ => j.val - p) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [Finset.mem_range]; omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      apply Fin.ext; omega
    · intro b hb
      simp only [Finset.mem_range] at hb
      have hi : i.val ≤ p + q := by have := i.isLt; omega
      refine ⟨⟨p + b, by omega⟩, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [hcard, Finset.card_range]

/-- The inversion count of the exceptional shuffle is `0`. -/
theorem invCount_goodShufF (p q : ℕ) : invCount (goodShufF p q) = 0 := by
  rw [invCount]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_goodShufF] at hj
  rw [pBNat, Finset.card_eq_zero]
  ext k
  constructor
  · intro hk
    rw [Finset.mem_filter, mem_goodShufF] at hk
    exact absurd hk.2 (by omega)
  · intro hk
    exact absurd hk (Finset.notMem_empty k)

/-- The Eilenberg–Zilber sign of the exceptional shuffle is `1`. -/
theorem shufSign_goodShufF (p q : ℕ) : shufSign (goodShufF p q) = 1 := by
  rw [shufSign, invCount_goodShufF, pow_zero]

/-- The front `p`-face of the `E`-count map of the exceptional shuffle is the identity. -/
theorem frontIncl_comp_aHom_goodShufF (p q : ℕ) :
    (frontIncl p (p + q) (Nat.le_add_right p q)) ≫ (aHom (goodShufF p q) (goodShufF_card p q))
      = 𝟙 ⦋p⦌ := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  rw [CategoryTheory.comp_apply, CategoryTheory.id_apply]
  apply Fin.ext
  rw [aHom_val, pA_goodShufF]
  have harg : ((ConcreteCategory.hom (frontIncl p (p + q) (Nat.le_add_right p q))) j)
      = (⟨j.val, by have := Work.KunnethEZ.fin_len_succ_le p j; omega⟩ : Fin (p + q + 1)) :=
    Fin.ext (by rw [Work.Cohomology.hom_frontIncl_val])
  rw [harg, Fin.val_mk]
  exact Nat.min_eq_left (by have := Work.KunnethEZ.fin_len_succ_le p j; omega)

/-- The back `q`-face of the `N`-count map of the exceptional shuffle is the identity. -/
theorem backIncl_comp_bHom_goodShufF (p q : ℕ) :
    backIncl p q ≫ (bHom (goodShufF p q) (goodShufF_card p q)) = 𝟙 ⦋q⦌ := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  rw [CategoryTheory.comp_apply, CategoryTheory.id_apply]
  apply Fin.ext
  rw [bHom_val, pB_goodShufF]
  have harg : ((ConcreteCategory.hom (backIncl p q)) j)
      = (⟨p + j.val, by have := Work.KunnethEZ.fin_len_succ_le q j; omega⟩ : Fin (p + q + 1)) :=
    Fin.ext (by rw [Work.Cohomology.hom_backIncl_val])
  rw [harg, Fin.val_mk]
  omega

/-- A simplex obtained from a non-surjective self-map of `⦋q⦌` is degenerate. -/
theorem mem_degenerate_of_not_surjective_self' {X : SSet} {q : ℕ} (f : ⦋q⦌ ⟶ ⦋q⦌)
    (hf : ¬ Function.Surjective ⇑f.toOrderHom) (x : X _⦋q⦌) : X.map f.op x ∈ X.degenerate q := by
  rcases q with _ | n
  · haveI : Subsingleton (Fin (⦋0⦌.len + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    exact absurd (fun y => ⟨y, Subsingleton.elim _ _⟩) hf
  · exact Work.KunnethEZ.mem_degenerate_of_not_surjective_self f hf x

/-- For a shuffle other than the exceptional one, the back `q`-face of its `N`-count map is not
surjective (so the corresponding `Y`-simplex is degenerate). -/
theorem not_surjective_backIncl_bHom_goodShufF (p q : ℕ) (S : PShuffle p q)
    (hS : S ≠ goodShuf p q) :
    ¬ Function.Surjective ⇑((backIncl p q) ≫ (bHom S.1 S.2)).toOrderHom := by
  change ¬ Function.Surjective (fun i : Fin (q + 1) =>
    (ConcreteCategory.hom ((backIncl p q) ≫ (bHom S.1 S.2))) i)
  intro hsurj
  -- the composite is monotone and hits `0`, hence takes the value `0` at `0`
  obtain ⟨j, hj⟩ := hsurj ⟨0, Nat.zero_lt_succ q⟩
  have hmono : ((ConcreteCategory.hom ((backIncl p q) ≫ (bHom S.1 S.2)))
        ⟨0, Nat.zero_lt_succ q⟩).val
      ≤ ((ConcreteCategory.hom ((backIncl p q) ≫ (bHom S.1 S.2))) j).val := by
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
    have h1 : (ConcreteCategory.hom (bHom S.1 S.2))
        (ConcreteCategory.hom (backIncl p q) ⟨0, Nat.zero_lt_succ q⟩)
        ≤ (ConcreteCategory.hom (bHom S.1 S.2)) (ConcreteCategory.hom (backIncl p q) j) :=
      (bHom S.1 S.2).toOrderHom.monotone (by
        rw [Fin.le_def, Work.Cohomology.hom_backIncl_val, Work.Cohomology.hom_backIncl_val]
        simp)
    exact Fin.le_def.mp h1
  have h0 : ((ConcreteCategory.hom ((backIncl p q) ≫ (bHom S.1 S.2)))
      ⟨0, Nat.zero_lt_succ q⟩).val = 0 := by
    have hjv : ((ConcreteCategory.hom ((backIncl p q) ≫ (bHom S.1 S.2))) j).val = 0 := by
      have h := congrArg Fin.val hj
      simpa using h
    omega
  -- hence `#{k ∈ S : k < p} = 0`, so all elements of `S` are `≥ p`
  have hval : (ConcreteCategory.hom ((backIncl p q) ≫ (bHom S.1 S.2)))
      ⟨0, Nat.zero_lt_succ q⟩
      = (bHom S.1 S.2) (ConcreteCategory.hom (backIncl p q) ⟨0, Nat.zero_lt_succ q⟩) := by
    rw [CategoryTheory.comp_apply]
  have hbval : ((ConcreteCategory.hom (backIncl p q)) ⟨0, Nat.zero_lt_succ q⟩).val = p := by
    rw [Work.Cohomology.hom_backIncl_val]
    simp
  have hpB : pB S.1 (ConcreteCategory.hom (backIncl p q) ⟨0, Nat.zero_lt_succ q⟩) = 0 := by
    have h : (ConcreteCategory.hom (bHom S.1 S.2))
        (ConcreteCategory.hom (backIncl p q) ⟨0, Nat.zero_lt_succ q⟩)
        = (ConcreteCategory.hom ((backIncl p q) ≫ (bHom S.1 S.2)))
          ⟨0, Nat.zero_lt_succ q⟩ := hval.symm
    have h' := congrArg Fin.val h
    rw [bHom_val] at h'
    omega
  have hfilter : S.1.filter (fun k => k.val < p) = ∅ := by
    rw [← Finset.card_eq_zero, ← hpB, pB, hbval]
  have hsub : S.1 ⊆ goodShufF p q := by
    intro k hk
    rw [mem_goodShufF]
    by_contra hcon
    have : k ∈ S.1.filter (fun k => k.val < p) := Finset.mem_filter.mpr ⟨hk, by omega⟩
    rw [hfilter] at this
    exact Finset.notMem_empty k this
  exact hS (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by
    show (goodShufF p q).card ≤ S.1.card
    rw [goodShufF_card, S.2])))

/-! ## The exceptional shuffle, in the `PShuffle` spelling -/

/-- The Eilenberg–Zilber sign of the exceptional shuffle is `1`. -/
theorem shufSign_goodShuf (p q : ℕ) : shufSign (goodShuf p q).1 = 1 :=
  shufSign_goodShufF p q

/-- The front `p`-face of the `E`-count map of the exceptional shuffle is the identity. -/
theorem frontIncl_comp_aHom_goodShuf (p q : ℕ) :
    (frontIncl p (p + q) (Nat.le_add_right p q))
      ≫ (aHom (goodShuf p q).1 (goodShuf p q).2) = 𝟙 ⦋p⦌ :=
  frontIncl_comp_aHom_goodShufF p q

/-- The back `q`-face of the `N`-count map of the exceptional shuffle is the identity. -/
theorem backIncl_comp_bHom_goodShuf (p q : ℕ) :
    backIncl p q ≫ (bHom (goodShuf p q).1 (goodShuf p q).2) = 𝟙 ⦋q⦌ :=
  backIncl_comp_bHom_goodShufF p q

/-- For a shuffle other than the exceptional one, the back `q`-face of its `N`-count map is not
surjective. -/
theorem not_surjective_backIncl_bHom_goodShuf (p q : ℕ) (S : PShuffle p q)
    (hS : S ≠ goodShuf p q) :
    ¬ Function.Surjective ⇑((backIncl p q) ≫ (bHom S.1 S.2)).toOrderHom :=
  not_surjective_backIncl_bHom_goodShufF p q S hS

end

end Work.Kunneth
