import Mathlib
import Submission.Work.Resample.fxTensorErr

/-!
# Strict error bound for the iterated fixed-point tensor computation

`Submission.Work.Resample.fxTensorErr` proves the error estimate of the iterated tensor
computation with non-strict inequalities.  The resampling argument needs the strict form: when
the one-dimensional errors are *strictly* below `ε i` and the input error is *strictly* below
`δ`, the total error is strictly below `δ + Σ ε i`.

The three ingredients (`axis`, `block`, induction) are redone below with strict conclusions.
The strictness comes from the `ε`-errors, through `add_lt_add_of_lt_of_le`; the input error is
converted to its non-strict form by `le_of_lt`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## One axis step, strict form -/

theorem fxTE_axisS {s t B p : ℕ} (A0 : (Fin s → ℂ) → (Fin t → ℂ))
    (F0 : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ)) (ε0 δ : ℝ) (hδ : 0 ≤ δ)
    (hAdd : ∀ x y : Fin s → ℂ, A0 (x + y) = A0 x + A0 y)
    (hNorm : ∀ z : Fin s → ℂ, ‖A0 z‖ ≤ ‖z‖)
    (hDisc : ∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t, inDisc p (F0 w k))
    (hErr : ∀ w : Fin s → ℤ × ℤ, (∀ j, inDisc p (w j)) → ∀ k : Fin t,
      ‖fxC p (F0 w k) - A0 (fun j => fxC p (w j)) k‖ * (2 : ℝ) ^ p < ε0)
    (u : Fin (s * B) → ℤ × ℤ) (v : Fin (s * B) → ℂ)
    (hu : ∀ j, inDisc p (u j))
    (hv : ∀ j, ‖fxC p (u j) - v j‖ * (2 : ℝ) ^ p ≤ δ) :
    (∀ idx : Fin (t * B), inDisc p (axisFx1Gen s t B F0 u idx)) ∧
    (∀ idx : Fin (t * B),
      ‖fxC p (axisFx1Gen s t B F0 u idx) - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p
        < δ + ε0) := by
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hB_of : ∀ idx : Fin (t * B), 0 < B := fun idx => fxTE_pos_right (Fin.pos idx)
  have hdiv_of : ∀ idx : Fin (t * B), (idx : ℕ) / B < t :=
    fun idx => (Nat.div_lt_iff_lt_mul (hB_of idx)).mpr idx.isLt
  constructor
  · intro idx
    rw [fxTE_axisFx1Gen_apply (hB_of idx)]
    exact hDisc _ (fun j => by
      have hlt := fxTE_idx_in_range_axis (hB_of idx) j ⟨(idx : ℕ) % B, Nat.mod_lt _ (hB_of idx)⟩
      rw [fxTE_zget_of_lt _ hlt]
      exact hu ⟨_, hlt⟩) _
  · intro idx
    have hB := hB_of idx
    have hd := hdiv_of idx
    have ha : ‖fxC p (axisFx1Gen s t B F0 u idx)
        - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖ * (2 : ℝ) ^ p
          < ε0 := by
      rw [fxTE_axisFx1Gen_apply hB,
        fxTE_axisApply1Gen_apply A0 (fun m : Fin (s * B) => fxC p (u m)) idx hd]
      have hfun : (fun j : Fin s => fxC p (zget u ((j : ℕ) * B + (idx : ℕ) % B)))
          = (fun j : Fin s => vget (fun m : Fin (s * B) => fxC p (u m))
              ((j : ℕ) * B + (idx : ℕ) % B)) := by
        funext j
        exact fxTE_fxC_zget p u _
      have hdisc : ∀ j : Fin s,
          inDisc p ((fun j : Fin s => zget u ((j : ℕ) * B + (idx : ℕ) % B)) j) := by
        intro j
        have hlt := fxTE_idx_in_range_axis hB j ⟨(idx : ℕ) % B, Nat.mod_lt _ hB⟩
        show inDisc p (zget u ((j : ℕ) * B + (idx : ℕ) % B))
        rw [fxTE_zget_of_lt _ hlt]
        exact hu ⟨_, hlt⟩
      have he := hErr (fun j : Fin s => zget u ((j : ℕ) * B + (idx : ℕ) % B)) hdisc
        ⟨(idx : ℕ) / B, hd⟩
      rw [← hfun]
      exact he
    have hsubpt : axisApply1Gen s t B A0 ((fun m : Fin (s * B) => fxC p (u m)) - v) idx
        = axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
          - axisApply1Gen s t B A0 v idx :=
      congrFun (fxTE_axisApply1Gen_sub A0 hAdd (fun m : Fin (s * B) => fxC p (u m)) v) idx
    have hb : ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
        - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p ≤ δ := by
      rw [← hsubpt,
        fxTE_axisApply1Gen_apply A0 ((fun m : Fin (s * B) => fxC p (u m)) - v) idx hd]
      have hpw : ∀ j : Fin s,
          ‖vget ((fun m : Fin (s * B) => fxC p (u m)) - v) ((j : ℕ) * B + (idx : ℕ) % B)‖
            ≤ δ / (2 : ℝ) ^ p := by
        intro j
        have hlt := fxTE_idx_in_range_axis hB j ⟨(idx : ℕ) % B, Nat.mod_lt _ hB⟩
        have hvv : vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
            ((j : ℕ) * B + (idx : ℕ) % B) = fxC p (u ⟨_, hlt⟩) - v ⟨_, hlt⟩ := by
          rw [fxTE_vget_of_lt _ hlt, Pi.sub_apply]
        rw [hvv, le_div_iff₀ h2p]
        exact hv ⟨_, hlt⟩
      calc ‖(A0 (fun j : Fin s => vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
              ((j : ℕ) * B + (idx : ℕ) % B))) ⟨(idx : ℕ) / B, hd⟩‖ * (2 : ℝ) ^ p
          ≤ ‖A0 (fun j : Fin s => vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
              ((j : ℕ) * B + (idx : ℕ) % B))‖ * (2 : ℝ) ^ p :=
            mul_le_mul_of_nonneg_right
              (fxTE_norm_apply_le _ ⟨(idx : ℕ) / B, hd⟩) (by positivity)
        _ ≤ ‖(fun j : Fin s => vget ((fun m : Fin (s * B) => fxC p (u m)) - v)
              ((j : ℕ) * B + (idx : ℕ) % B))‖ * (2 : ℝ) ^ p :=
            mul_le_mul_of_nonneg_right (hNorm _) (by positivity)
        _ ≤ (δ / (2 : ℝ) ^ p) * (2 : ℝ) ^ p :=
            mul_le_mul_of_nonneg_right
              (fxTE_norm_pi_le (div_nonneg hδ (le_of_lt h2p)) hpw) (by positivity)
        _ = δ := div_mul_cancel₀ δ (ne_of_gt h2p)
    have htri : ‖fxC p (axisFx1Gen s t B F0 u idx) - axisApply1Gen s t B A0 v idx‖
        ≤ ‖fxC p (axisFx1Gen s t B F0 u idx)
            - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖
          + ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
            - axisApply1Gen s t B A0 v idx‖ := by
      have h := dist_triangle (fxC p (axisFx1Gen s t B F0 u idx))
        (axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx)
        (axisApply1Gen s t B A0 v idx)
      simpa only [dist_eq_norm] using h
    calc ‖fxC p (axisFx1Gen s t B F0 u idx) - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p
        ≤ (‖fxC p (axisFx1Gen s t B F0 u idx)
              - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖
            + ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
              - axisApply1Gen s t B A0 v idx‖) * (2 : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right htri (by positivity)
      _ = ‖fxC p (axisFx1Gen s t B F0 u idx)
              - axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx‖ * (2 : ℝ) ^ p
            + ‖axisApply1Gen s t B A0 (fun m : Fin (s * B) => fxC p (u m)) idx
              - axisApply1Gen s t B A0 v idx‖ * (2 : ℝ) ^ p := by ring
      _ < ε0 + δ := add_lt_add_of_lt_of_le ha hb
      _ = δ + ε0 := by ring

/-! ## The blockwise step, strict form -/

theorem fxTE_blockS (t N N' p : ℕ) (Φ : (Fin N → ℤ × ℤ) → (Fin N' → ℤ × ℤ))
    (Ψ : (Fin N → ℂ) → (Fin N' → ℂ)) (b δ' : ℝ)
    (h : ∀ (w : Fin N → ℤ × ℤ) (w' : Fin N → ℂ),
      (∀ j, inDisc p (w j)) → (∀ j, ‖fxC p (w j) - w' j‖ * (2 : ℝ) ^ p < δ') →
      ∀ k : Fin N', ‖fxC p (Φ w k) - Ψ w' k‖ * (2 : ℝ) ^ p < b)
    (u : Fin (t * N) → ℤ × ℤ) (v : Fin (t * N) → ℂ)
    (hu : ∀ j, inDisc p (u j))
    (hv : ∀ j, ‖fxC p (u j) - v j‖ * (2 : ℝ) ^ p < δ') :
    ∀ idx : Fin (t * N'),
      ‖fxC p (fxBlockwise t N N' Φ u idx) - blockwise t N N' Ψ v idx‖ * (2 : ℝ) ^ p < b := by
  intro idx
  rcases Nat.eq_zero_or_pos N' with hN' | hN'pos
  · have hpos := Fin.pos idx
    rw [hN'] at hpos
    simp at hpos
  rw [fxTE_fxBlockwise_apply hN'pos, fxTE_blockwise_apply hN'pos]
  refine h (fun K' : Fin N => zget u ((idx : ℕ) / N' * N + (K' : ℕ)))
    (fun K' : Fin N => vget v ((idx : ℕ) / N' * N + (K' : ℕ))) ?_ ?_
    ⟨(idx : ℕ) % N', Nat.mod_lt _ hN'pos⟩
  · intro j
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact Fin.elim0 j
    · have hlt := fxTE_idx_in_range hN hN'pos idx j
      rw [fxTE_zget_of_lt _ hlt]
      exact hu ⟨_, hlt⟩
  · intro j
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; exact Fin.elim0 j
    · have hlt := fxTE_idx_in_range hN hN'pos idx j
      rw [fxTE_zget_of_lt _ hlt, fxTE_vget_of_lt _ hlt]
      exact hv ⟨_, hlt⟩

/-! ## The iterated estimate, strict form -/

theorem fxTE_auxS (ss : List ℕ) : ∀ (ts : List ℕ), ts.length = ss.length → ∀ (p : ℕ)
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
      (∀ j, ‖fxC p (u j) - v j‖ * (2 : ℝ) ^ p < δ) → ∀ J : Fin ts.prod,
      ‖fxC p (fxTensorRec ss ts Fh u J) - tensorMapRec ss ts A v J‖ * (2 : ℝ) ^ p
        < δ + ((List.range ss.length).map ε).sum := by
  induction ss with
  | nil =>
    intro ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J
    have hts : ts = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hts
    have h1 : fxTensorRec [] [] Fh u J = u J := rfl
    have h2 : tensorMapRec [] [] A v J = v J := rfl
    simpa only [h1, h2, List.length_nil, List.range_zero, List.map_nil, List.sum_nil,
      add_zero] using hv J
  | cons s ss' ih =>
    intro ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J
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
      have hε0 : 0 ≤ ε 0 := by
        have he := hErr 0 h0len (fun _ : Fin s => (0, 0)) (fun _ => fxTE_inDisc_zero p) ⟨0, ht⟩
        have hnn : (0 : ℝ) ≤ ‖fxC p (Fh 0 (fun _ : Fin s => (0, 0)) ⟨0, ht⟩)
            - A 0 (fun j : Fin s => fxC p ((fun _ : Fin s => (0, 0)) j)) ⟨0, ht⟩‖ * (2 : ℝ) ^ p :=
          mul_nonneg (norm_nonneg _) (by positivity)
        exact le_trans hnn (le_of_lt he)
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
      have hIH := ih ts' hTS p (fun i => A (i + 1)) (fun i => Fh (i + 1)) (fun i => ε (i + 1))
        (δ + ε 0) hδ' hAdd' hNorm' hDisc' hErr'
      have haxis := fxTE_axisS (s := s) (t := t) (B := ss'.prod) (p := p) (A0 := A 0) (F0 := Fh 0)
        (ε0 := ε 0) (δ := δ) hδ
        (fun x y => hAdd 0 h0len x y) (fun z => hNorm 0 h0len z)
        (fun w hw k => hDisc 0 h0len w hw k) (fun w hw k => hErr 0 h0len w hw k) u v hu
        (fun j => le_of_lt (hv j))
      have hblock := fxTE_blockS t ss'.prod ts'.prod p
        (fxTensorRec ss' ts' (fun i => Fh (i + 1))) (tensorMapRec ss' ts' (fun i => A (i + 1)))
        ((δ + ε 0) + ((List.range ss'.length).map (fun i => ε (i + 1))).sum) (δ + ε 0)
        (fun w w' hw hw' k => hIH w hw w' hw' k)
        (axisFx1Gen s t ss'.prod (Fh 0) u) (axisApply1Gen s t ss'.prod (A 0) v) haxis.1 haxis.2
      have hsum : ((List.range (s :: ss').length).map ε).sum
          = ε 0 + ((List.range ss'.length).map (fun i => ε (i + 1))).sum := by
        simp only [List.length_cons]
        exact fxTE_sum_range_succ ε ss'.length
      rw [hsum, ← add_assoc]
      exact hblock J

/-! ## The requested strict estimate -/

theorem fxTensorErrS (ss ts : List ℕ) (hl : ts.length = ss.length) (p : ℕ)
    (A : (i : ℕ) → (Fin (ss.getD i 0) → ℂ) → (Fin (ts.getD i 0) → ℂ))
    (Fh : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
    (ε : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hAdd : ∀ i < ss.length, ∀ x y : Fin (ss.getD i 0) → ℂ, A i (x + y) = A i x + A i y)
    (hNorm : ∀ i < ss.length, ∀ z : Fin (ss.getD i 0) → ℂ, ‖A i z‖ ≤ ‖z‖)
    (hDisc : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin (ts.getD i 0), HvdH.inDisc p (Fh i w k))
    (hErr : ∀ i < ss.length, ∀ w : Fin (ss.getD i 0) → ℤ × ℤ,
      (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin (ts.getD i 0),
      ‖HvdH.fxC p (Fh i w k) - A i (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p < ε i)
    (u : Fin ss.prod → ℤ × ℤ) (hu : ∀ j, HvdH.inDisc p (u j))
    (v : Fin ss.prod → ℂ) (hv : ∀ j, ‖HvdH.fxC p (u j) - v j‖ * (2 : ℝ) ^ p < δ)
    (J : Fin ts.prod) :
    ‖HvdH.fxC p (Work.Resample.fxTensorRec ss ts Fh u J) -
      (Work.Resample.tensorMapRec ss ts A v) J‖ * (2 : ℝ) ^ p
      < δ + ((List.range ss.length).map ε).sum :=
  fxTE_auxS ss ts hl p A Fh ε δ hδ hAdd hNorm hDisc hErr u hu v hv J

end Work.Resample
