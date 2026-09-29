import Mathlib
import Submission.Work.Resample.fxTensorErrS

/-!
# Mixed error bound for the iterated fixed-point tensor computation

`Submission.Work.Resample.fxTensorErrS` bounds the total error of the iterated tensor
computation when the *input* error is strictly below `δ`.  The resampling argument needs a
slightly different combination: the input error is only known to be `≤ δ` (the value passed to
the recursion is exact, but in intermediate steps only a non-strict bound is available), while
the one-dimensional errors are *strictly* below `ε i`.  Strictness is then inherited from the
`ε`-errors, through `fxTE_axisS`, and the remaining axes are handled by the strict estimate
`fxTensorErrS` applied to the (strictly bounded) output of the first axis.

The hypothesis `ss ≠ []` is necessary: for `ss = []` the conclusion would be
`‖fxC p (u J) - v J‖ * 2^p < δ`, which does not follow from `≤ δ`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Mixed form of the iterated tensor error estimate: non-strict input error, strict
one-dimensional errors.  The list of input dimensions must be non-empty. -/
theorem fxTE_auxMixed (ss : List ℕ) (hne : ss ≠ []) :
    ∀ (ts : List ℕ), ts.length = ss.length → ∀ (p : ℕ)
    (A : (i : ℕ) → (Fin (ss.getD i 0) → ℂ) → (Fin (ts.getD i 0) → ℂ))
    (Fh : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (ε : ℕ → ℝ) (δ : ℝ), 0 ≤ δ →
    (∀ i < ss.length, ∀ x y : Fin (ss.getD i 0) → ℂ, A i (x + y) = A i x + A i y) →
    (∀ i < ss.length, ∀ z : Fin (ss.getD i 0) → ℂ, ‖A i z‖ ≤ ‖z‖) →
    (∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, inDisc p (w j)) → ∀ k : Fin (ts.getD i 0), inDisc p (Fh i w k)) →
    (∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, inDisc p (w j)) → ∀ k : Fin (ts.getD i 0),
      ‖fxC p (Fh i w k) - A i (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p < ε i) →
    ∀ (u : Fin ss.prod → ℤ × ℤ), (∀ j, inDisc p (u j)) → ∀ (v : Fin ss.prod → ℂ),
      (∀ j, ‖fxC p (u j) - v j‖ * (2 : ℝ) ^ p ≤ δ) → ∀ J : Fin ts.prod,
      ‖fxC p (fxTensorRec ss ts Fh u J) - tensorMapRec ss ts A v J‖ * (2 : ℝ) ^ p
        < δ + ((List.range ss.length).map ε).sum := by
  intro ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J
  cases ss with
  | nil => exact absurd rfl hne
  | cons s ss' =>
    cases ts with
    | nil =>
      simp only [List.length_nil, List.length_cons] at hl
      omega
    | cons t ts' =>
      have hTS : ts'.length = ss'.length := by
        simp only [List.length_cons] at hl
        omega
      have hpos : 0 < t * ts'.prod := by simpa only [List.prod_cons] using Fin.pos J
      have ht : 0 < t := fxTE_pos_left hpos
      have h0len : 0 < (s :: ss').length := by
        simp only [List.length_cons]; exact Nat.zero_lt_succ _
      -- `ε 0 ≥ 0`, forced by the strict error hypothesis at the zero fixed-point vector
      have hε0 : 0 ≤ ε 0 := by
        have he := hErr 0 h0len (fun _ : Fin s => (0, 0)) (fun _ => fxTE_inDisc_zero p) ⟨0, ht⟩
        have hnn : (0 : ℝ) ≤ ‖fxC p (Fh 0 (fun _ : Fin s => (0, 0)) ⟨0, ht⟩)
            - A 0 (fun j : Fin s => fxC p ((fun _ : Fin s => (0, 0)) j)) ⟨0, ht⟩‖ * (2 : ℝ) ^ p :=
          mul_nonneg (norm_nonneg _) (by positivity)
        exact le_trans hnn (le_of_lt he)
      -- hypotheses for the tail
      have hAdd' : ∀ i < ss'.length, ∀ x y : Fin (ss'.getD i 0) → ℂ,
          A (i + 1) (x + y) = A (i + 1) x + A (i + 1) y :=
        fun i hi x y => hAdd (i + 1) (by simp only [List.length_cons]; omega) x y
      have hNorm' : ∀ i < ss'.length, ∀ z : Fin (ss'.getD i 0) → ℂ, ‖A (i + 1) z‖ ≤ ‖z‖ :=
        fun i hi z => hNorm (i + 1) (by simp only [List.length_cons]; omega) z
      have hDisc' : ∀ i < ss'.length, ∀ w : Fin (ss'.getD i 0) → ℤ × ℤ,
          (∀ j, inDisc p (w j)) → ∀ k : Fin (ts'.getD i 0), inDisc p (Fh (i + 1) w k) :=
        fun i hi w hw k => hDisc (i + 1) (by simp only [List.length_cons]; omega) w hw k
      have hErr' : ∀ i < ss'.length, ∀ w : Fin (ss'.getD i 0) → ℤ × ℤ,
          (∀ j, inDisc p (w j)) → ∀ k : Fin (ts'.getD i 0),
          ‖fxC p (Fh (i + 1) w k) - A (i + 1) (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p
            < ε (i + 1) :=
        fun i hi w hw k => hErr (i + 1) (by simp only [List.length_cons]; omega) w hw k
      have hδ' : 0 ≤ δ + ε 0 := add_nonneg hδ hε0
      -- the tail is handled by the strict estimate: the axis step below produces a *strict*
      -- bound `< δ + ε 0` for its input error
      have htail : ∀ (w : Fin ss'.prod → ℤ × ℤ) (w' : Fin ss'.prod → ℂ),
          (∀ j, inDisc p (w j)) → (∀ j, ‖fxC p (w j) - w' j‖ * (2 : ℝ) ^ p < δ + ε 0) →
          ∀ k : Fin ts'.prod,
          ‖fxC p (fxTensorRec ss' ts' (fun i => Fh (i + 1)) w k)
            - tensorMapRec ss' ts' (fun i => A (i + 1)) w' k‖ * (2 : ℝ) ^ p
            < (δ + ε 0) + ((List.range ss'.length).map (fun i => ε (i + 1))).sum :=
        fun w w' hw hw' k => fxTensorErrS ss' ts' hTS p (fun i => A (i + 1))
          (fun i => Fh (i + 1)) (fun i => ε (i + 1)) (δ + ε 0) hδ'
          hAdd' hNorm' hDisc' hErr' w hw w' hw' k
      have haxis := fxTE_axisS (s := s) (t := t) (B := ss'.prod) (p := p) (A0 := A 0)
        (F0 := Fh 0) (ε0 := ε 0) (δ := δ) hδ
        (fun x y => hAdd 0 h0len x y) (fun z => hNorm 0 h0len z)
        (fun w hw k => hDisc 0 h0len w hw k) (fun w hw k => hErr 0 h0len w hw k) u v hu hv
      have hblock := fxTE_blockS t ss'.prod ts'.prod p
        (fxTensorRec ss' ts' (fun i => Fh (i + 1))) (tensorMapRec ss' ts' (fun i => A (i + 1)))
        ((δ + ε 0) + ((List.range ss'.length).map (fun i => ε (i + 1))).sum) (δ + ε 0)
        htail (axisFx1Gen s t ss'.prod (Fh 0) u) (axisApply1Gen s t ss'.prod (A 0) v)
        haxis.1 haxis.2
      have hsum : ((List.range (s :: ss').length).map ε).sum
          = ε 0 + ((List.range ss'.length).map (fun i => ε (i + 1))).sum := by
        simp only [List.length_cons]
        exact fxTE_sum_range_succ ε ss'.length
      rw [hsum, ← add_assoc]
      exact hblock J

theorem fxTensorErrMixed (ss ts : List ℕ) (hl : ts.length = ss.length) (p : ℕ)
    (A : (i : ℕ) → (Fin (ss.getD i 0) → ℂ) → (Fin (ts.getD i 0) → ℂ))
    (Fh : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (ε : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hne : ss ≠ [])
    (hpos : ∀ i < ss.length, 0 < ts.getD i 0)
    (hAdd : ∀ i < ss.length, ∀ x y : Fin (ss.getD i 0) → ℂ, A i (x + y) = A i x + A i y)
    (hNorm : ∀ i < ss.length, ∀ z : Fin (ss.getD i 0) → ℂ, ‖A i z‖ ≤ ‖z‖)
    (hDisc : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin (ts.getD i 0), HvdH.inDisc p (Fh i w k))
    (hErr : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin (ts.getD i 0),
      ‖HvdH.fxC p (Fh i w k) - A i (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p < ε i)
    (u : Fin ss.prod → ℤ × ℤ) (hu : ∀ j, HvdH.inDisc p (u j))
    (v : Fin ss.prod → ℂ) (hv : ∀ j, ‖HvdH.fxC p (u j) - v j‖ * (2 : ℝ) ^ p ≤ δ)
    (J : Fin ts.prod) :
    ‖HvdH.fxC p (Work.Resample.fxTensorRec ss ts Fh u J) -
      (Work.Resample.tensorMapRec ss ts A v) J‖ * (2 : ℝ) ^ p <
        δ + ((List.range ss.length).map ε).sum := by
  have _hpos := hpos
  exact fxTE_auxMixed ss hne ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J

end Work.Resample
