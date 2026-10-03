import Mathlib
import Submission.Work.Peluse.Basic

/-!
# Reflecting all the directions of Peluse's box norm

The `2^t`-th power of the Gowers box norm of Peluse's Definition 2.1,

`boxSumPow t Q S f = (1/|S|) ∑_x E_{h,h' ∈ ∏_i Q_i} ∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`,

is unchanged by reflecting *every* direction set `Q_i ↦ -Q_i` in `0` provided the function is also
reflected:

`boxSumPow t (fun i => (Q i).image (fun z => -z)) S f = boxSumPow t Q S (fun x => f (-x))`.

This generalises `Work.Peluse.Ulower.boxSumPow_neg` from the arithmetic progressions
`Q i = arithIcc c D` (all directions equal) to an arbitrary family of direction sets, which is
what the reflection bookkeeping for the `x`-directions of the bilinear averages of
Krause–Mirek–Tao's §5 needs.

The proof is the change of variables `x ↦ -x` (a bijection of `ℤ`) together with the two
reindexings of the shift sums along the componentwise reflection equivalence `piNegReflectEquiv`.
The only structural input is that the corner shift is odd in its two shift arguments
(`cornerShift_neg_int`), while the iterated conjugations `C^{|ω|}` act on the *values* of `f` and
are unaffected by the reflection of the argument.

## Main results

* `Work.Peluse.Pairing.cornerShift_neg_int` : `cornerShift (-h) (-h') ω = -cornerShift h h' ω`;
* `Work.Peluse.Pairing.boxSumPow_neg_directions` : the reflection identity above.

## Reference

S. Peluse, *Bounds for sets with no polynomial progressions*, Forum of Math. Pi **8** (2020), e16,
Definition 2.1; `Work.Peluse.Ulower.boxSumPow_neg`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Peluse.Pairing

open Work.Peluse

noncomputable section

/-! ## Reflecting a finset of integers -/

/-- Membership in the reflection of a finset of integers. -/
lemma mem_image_neg_int {Q : Finset ℤ} {x : ℤ} :
    x ∈ Q.image (fun z : ℤ => -z) ↔ -x ∈ Q := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hyx, neg_neg]
  · intro hx
    exact ⟨-x, hx, by ring⟩

/-- Reflecting a finset of integers in `0` preserves its cardinality. -/
lemma card_image_neg_int (Q : Finset ℤ) : (Q.image (fun z : ℤ => -z)).card = Q.card :=
  Finset.card_image_of_injective _ neg_injective

/-- Reflection `x ↦ -x` as an equivalence `{x // x ∈ -Q} ≃ {x // x ∈ Q}`. -/
abbrev negReflectEquiv (Q : Finset ℤ) :
    {x : ℤ // x ∈ Q.image (fun z : ℤ => -z)} ≃ {x : ℤ // x ∈ Q} where
  toFun x := ⟨-x.1, mem_image_neg_int.mp x.2⟩
  invFun x := ⟨-x.1, mem_image_neg_int.mpr (by simpa only [neg_neg] using x.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

/-- Componentwise reflection of a tuple of shifts. -/
abbrev piNegReflectEquiv (t : ℕ) (Q : Fin t → Finset ℤ) :
    ((i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun z : ℤ => -z)}) ≃
      ((i : Fin t) → {x : ℤ // x ∈ Q i}) where
  toFun h := fun i => negReflectEquiv (Q i) (h i)
  invFun h := fun i => (negReflectEquiv (Q i)).symm (h i)
  left_inv h := by funext i; simp [negReflectEquiv]
  right_inv h := by funext i; simp [negReflectEquiv]

/-- The corner shift is odd in its two shift arguments. -/
lemma cornerShift_neg_int {t : ℕ} (h h' : Fin t → ℤ) (ω : Fin t → Bool) :
    cornerShift (fun i => -h i) (fun i => -h' i) ω = -cornerShift h h' ω := by
  simp only [cornerShift, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by by_cases hi : ω i <;> simp [hi])

/-! ## The reflection identity -/

/-- Reflecting every direction set `Q i ↦ -Q i` in `0` while reflecting the function
`f ↦ f (-·)` leaves the `2^t`-th power of the box norm unchanged. -/
theorem boxSumPow_neg_directions {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow t (fun i : Fin t => (Q i).image (fun z : ℤ => -z)) S f
      = Work.Peluse.boxSumPow t Q S (fun x : ℤ => f (-x)) := by
  have hcard : ∀ i : Fin t, ((Q i).image (fun z : ℤ => -z)).card = (Q i).card :=
    fun i => card_image_neg_int (Q i)
  simp only [Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum, hcard]
  congr 1
  let E := piNegReflectEquiv t Q
  -- The inner `x`-sum, reflected: the `x ↦ -x` change of variables plus the oddness of the
  -- corner shift.
  have key : ∀ (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}),
      (∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (x + cornerShift (fun i => -(h i).1) (fun i => -(h' i).1) ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (-(x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := by
    intro h h'
    have hcs : ∀ ω : Fin t → Bool,
        cornerShift (fun i : Fin t => -(h i).1) (fun i => -(h' i).1) ω
          = -cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω :=
      fun ω => cornerShift_neg_int _ _ ω
    have hpt : ∀ x : ℤ, (∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (x + cornerShift (fun i => -(h i).1) (fun i => -(h' i).1) ω)))
        = ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (x - cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) := by
      intro x
      refine Finset.prod_congr rfl (fun ω _ => ?_)
      rw [hcs ω, sub_eq_add_neg]
    rw [tsum_congr hpt,
      ← tsum_comp_neg (fun x : ℤ => ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (x - cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))]
    refine tsum_congr (fun x => ?_)
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    rw [show -x - cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω
        = -(x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω) by ring]
  -- Reindex the two shift sums by reflection.
  rw [← Equiv.sum_comp E.symm
    (g := fun h : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun z : ℤ => -z)} =>
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun z : ℤ => -z)},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Equiv.sum_comp E.symm
    (g := fun h' : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun z : ℤ => -z)} =>
      ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (x + cornerShift (fun i => (E.symm h i).1) (fun i => (h' i).1) ω)))]
  exact Finset.sum_congr rfl (fun h' _ => key h h')

end

end Work.Peluse.Pairing
