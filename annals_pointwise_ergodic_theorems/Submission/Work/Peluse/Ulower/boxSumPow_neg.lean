import Mathlib
import Submission.Work.Peluse.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Peluse.Ulower

open Work.Peluse

noncomputable section

/-! ## Reflecting the arithmetic progression `c[D]`

The box sum of Peluse's Definition 2.1 uses the shift sets `Q i = c[D]`.  Replacing `c` by `-c`
(and reflecting the function) leaves the box sum unchanged; this is the elementary reflection
identity recorded in `Submission/Work/Peluse/Ulower/NOTES.md`, needed because
`P.leadingCoeff` may be negative while the input `h1` of `PeluseULowering` uses positive shifts.
-/

/-- `arithIcc (-c) D` is the reflection of `arithIcc c D` in `0`. -/
lemma arithIcc_neg_eq_image (c : ℤ) (D : ℕ) :
    arithIcc (-c) D = (arithIcc c D).image (fun x : ℤ => -x) := by
  rw [arithIcc, arithIcc, Finset.image_image]
  have h : (fun n : ℕ => -c * (n : ℤ)) = ((fun x : ℤ => -x) ∘ (fun n : ℕ => c * (n : ℤ))) := by
    funext n; simp
  rw [h]

lemma card_arithIcc_neg (c : ℤ) (D : ℕ) : (arithIcc (-c) D).card = (arithIcc c D).card := by
  rw [arithIcc_neg_eq_image]
  exact Finset.card_image_of_injective _ neg_injective

lemma mem_arithIcc_neg_iff {c : ℤ} {D : ℕ} {x : ℤ} :
    x ∈ arithIcc (-c) D ↔ -x ∈ arithIcc c D := by
  rw [arithIcc_neg_eq_image, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← hyx, neg_neg]
  · intro hx
    exact ⟨-x, hx, by ring⟩

/-- Reflection as an equivalence of the subtypes of shifts. -/
abbrev arithNegEquiv (c : ℤ) (D : ℕ) :
    {x : ℤ // x ∈ arithIcc (-c) D} ≃ {x : ℤ // x ∈ arithIcc c D} where
  toFun x := ⟨-x.1, mem_arithIcc_neg_iff.mp x.2⟩
  invFun x := ⟨-x.1, mem_arithIcc_neg_iff.mpr (by simpa only [neg_neg] using x.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

/-- Componentwise reflection of the tuple of shifts. -/
abbrev piArithNegEquiv (t : ℕ) (c : ℤ) (D : ℕ) :
    ((_ : Fin t) → {x : ℤ // x ∈ arithIcc (-c) D}) ≃
      ((_ : Fin t) → {x : ℤ // x ∈ arithIcc c D}) where
  toFun h := fun i => arithNegEquiv c D (h i)
  invFun h := fun i => (arithNegEquiv c D).symm (h i)
  left_inv h := by funext i; simp [arithNegEquiv]
  right_inv h := by funext i; simp [arithNegEquiv]

/-- `cornerShift` is odd in its two shift arguments. -/
lemma cornerShift_neg {t : ℕ} (h h' : Fin t → ℤ) (ω : Fin t → Bool) :
    cornerShift (fun i => -h i) (fun i => -h' i) ω = -cornerShift h h' ω := by
  simp only [cornerShift, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : ω i <;> simp [hi]

theorem boxSumPow_neg (t : ℕ) (c : ℤ) (D : ℕ) (S : Finset ℤ) (F : ℤ → ℂ) :
    Work.Peluse.boxSumPow t (fun _ : Fin t => Work.Peluse.arithIcc (-c) D) S F
      = Work.Peluse.boxSumPow t (fun _ : Fin t => Work.Peluse.arithIcc c D) S (fun x => F (-x)) := by
  have hcard : (arithIcc (-c) D).card = (arithIcc c D).card := card_arithIcc_neg c D
  simp only [boxSumPow, prodCubeSum, hcard]
  congr 1
  let E := piArithNegEquiv t c D
  -- The pointwise (per pair of shifts) reflection of the inner `x`-sum.
  have key : ∀ (h h' : (_ : Fin t) → {x : ℤ // x ∈ arithIcc c D}),
      (∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x + cornerShift (fun i => -(h i).1) (fun i => -(h' i).1) ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (-(x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := by
    intro h h'
    have hcs : ∀ ω : Fin t → Bool,
        cornerShift (fun i : Fin t => -(h i).1) (fun i => -(h' i).1) ω
          = -cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω :=
      fun ω => cornerShift_neg _ _ ω
    have hpt : ∀ x : ℤ, (∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x + cornerShift (fun i => -(h i).1) (fun i => -(h' i).1) ω)))
        = ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x - cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) := by
      intro x
      refine Finset.prod_congr rfl (fun ω _ => ?_)
      rw [hcs ω, sub_eq_add_neg]
    rw [tsum_congr hpt,
      ← tsum_comp_neg (fun x : ℤ => ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x - cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))]
    refine tsum_congr (fun x => ?_)
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    rw [show -x - cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω
        = -(x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω) by ring]
  -- Reindex the two shift sums by reflection.
  rw [← Equiv.sum_comp E.symm (g := fun h : (_ : Fin t) → {x : ℤ // x ∈ arithIcc (-c) D} =>
      ∑ h' : (_ : Fin t) → {x : ℤ // x ∈ arithIcc (-c) D},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Equiv.sum_comp E.symm (g := fun h' : (_ : Fin t) → {x : ℤ // x ∈ arithIcc (-c) D} =>
      ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (F (x + cornerShift (fun i => (E.symm h i).1) (fun i => (h' i).1) ω)))]
  exact Finset.sum_congr rfl (fun h' _ => key h h')

end

end Work.Peluse.Ulower
