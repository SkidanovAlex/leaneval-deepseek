import Mathlib
import Submission.Work.Peluse.ladderA_peel

namespace Work.Peluse.LadderA

open Work.Peluse

/-!
# Splitting the averaged hypothesis over the parameter box

The hypothesis of the ladder bounds `γ` by the `(A, a')`-average of the box norms at the window
`symIcc N`, where `a'` ranges over the full parameter box `paramBox M₂`.  The conclusion needs the
average over the slice `a'' s₀ = 0` of the box norms at the *longer* window `symIcc (Kb * N)`,
with the loss factor `1/(Kb+1)`.

Two ingredients finish the job:

* `sum_paramBox_split` reindexes the `(a'', a₀)`-double sum as a single sum over `paramBox M₂`
  (with `a' = Function.update a'' s₀ a₀`), so the conclusion's family is the hypothesis's family;
  the same bijection gives `|paramBox M₂| = |Ioo (-M₂) M₂| * |{a'' | a'' s₀ = 0}|`, which makes the
  two normalising constants coincide;
* `boxNorm_symIcc_ge` bounds each hypothesis term by the corresponding conclusion term, since
  enlarging the support window from `symIcc N` to `symIcc (Kb * N)` costs at most the factor
  `Kb + 1` (and `N ≤ Kb * N` as `Kb ≥ 1`).

`hyp_avg_split_aux` carries out the argument for an abstract family `Q` and function `g`; the
requested statement is its instantiation at the ladder family
`Q a a' j = pDirFam p M₁ a a' j`.
-/

/-- The parameter box splits evenly into the `s₀`-slice and the `s₀`-coordinate: its cardinality is
the product of the cardinalities of `Finset.Ioo (-M₂) M₂` and `{a'' | a'' s₀ = 0}`. -/
theorem paramBox_card_filter {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (M₂ : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι k) :
    (Work.Peluse.UControl.paramBox (k := k) M₂).card =
      (Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card *
        ((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card := by
  have h := sum_paramBox_split (k := k) (M₂ := M₂) (s₀ := s₀) (M := ℕ)
    (fun _ : (Work.Peluse.UControl.Slot ι k → ℤ) => 1)
  simpa using h

/-- **The averaged hypothesis splits over the parameter box.**  For an abstract family `Q` of
direction sets and an abstract `g`, bounding `γ` by the `paramBox`-average of the box norms at the
window `symIcc N` gives `γ/(Kb+1)` bounded by the slice-average of the box norms at the window
`symIcc (Kb*N)`. -/
theorem hyp_avg_split_aux {ι α : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (k : ι → ℕ) (M₂ : ℕ) (s₀ : Work.Peluse.UControl.Slot ι k) (Kb t : ℕ)
    (Adata : Finset α) (N : ℕ) (γ : ℝ)
    (Q : α → (Work.Peluse.UControl.Slot ι k → ℤ) → Fin t → Finset ℤ) (g : α → ℤ → ℂ)
    (hN : 1 ≤ N) (hKb1 : 1 ≤ Kb)
    (hhyp : γ ≤ ((Adata.card : ℝ))⁻¹ * ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
          Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc N) (g a)) :
    γ / ((Kb : ℝ) + 1) ≤ ((Adata.card : ℝ))⁻¹ *
        (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
        ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ *
        ∑ a ∈ Adata,
          ∑ a'' ∈ (Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0),
            ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
              Work.Peluse.boxNorm t (Q a (Function.update a'' s₀ a₀))
                (Work.Peluse.symIcc (Kb * N)) (g a) := by
  classical
  -- The two normalising constants coincide, by the box/slice/coordinate split.
  have hcardinv : ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ)⁻¹ =
      (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
        ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ := by
    have hcast : ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ) =
        ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ) *
          (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ) := by
      rw [paramBox_card_filter k M₂ s₀]; push_cast; ring
    rw [hcast, mul_inv_rev]
  have hNN : N ≤ Kb * N := by
    calc N = 1 * N := (one_mul N).symm
      _ ≤ Kb * N := Nat.mul_le_mul_right N hKb1
  -- Each hypothesis term is dominated by the corresponding conclusion term.
  have hterm : ∀ a ∈ Adata, ∀ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
      Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc N) (g a) / ((Kb : ℝ) + 1)
        ≤ Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc (Kb * N)) (g a) := by
    intro a ha a' ha'
    exact boxNorm_symIcc_ge (Q a a') hN hNN le_rfl (g a)
  -- The conclusion's slice sum is the hypothesis's box sum, at the long window.
  have hreindex : (∑ a ∈ Adata,
        ∑ a'' ∈ (Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0),
          ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
            Work.Peluse.boxNorm t (Q a (Function.update a'' s₀ a₀)) (Work.Peluse.symIcc (Kb * N)) (g a))
      = ∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
          Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc (Kb * N)) (g a) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hsplit := (sum_paramBox_split (k := k) (M₂ := M₂) (s₀ := s₀)
      (fun a' : Work.Peluse.UControl.Slot ι k → ℤ =>
        Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc (Kb * N)) (g a))).symm
    rw [Finset.sum_comm]
    exact hsplit
  -- Summing the termwise bound (multiplying by the nonnegative factor `(Kb+1)⁻¹`).
  have hsum : (∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
        Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc N) (g a)) * ((Kb : ℝ) + 1)⁻¹
      ≤ ∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
          Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc (Kb * N)) (g a) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun a ha => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun a' ha' => ?_)
    rw [← div_eq_mul_inv]
    exact hterm a ha a' ha'
  rw [div_eq_mul_inv, hreindex]
  calc γ * ((Kb : ℝ) + 1)⁻¹
      ≤ (((Adata.card : ℝ))⁻¹ * ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ)⁻¹ *
          ∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
            Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc N) (g a)) * ((Kb : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_right hhyp (by positivity)
    _ = ((Adata.card : ℝ))⁻¹ *
          (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
          ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ *
          ((∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
            Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc N) (g a)) * ((Kb : ℝ) + 1)⁻¹) := by
        rw [hcardinv]; ring
    _ ≤ ((Adata.card : ℝ))⁻¹ *
          (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
          ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ *
          (∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
            Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc (Kb * N)) (g a)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((Adata.card : ℝ))⁻¹ *
        (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
        ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
          Work.Peluse.boxNorm t (Q a a') (Work.Peluse.symIcc (Kb * N)) (g a) := by
        ring

theorem hyp_avg_split {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (m : ℕ)
    (hm : Fintype.card (Work.Peluse.UControl.FamIdx kω) = m) (Kb : ℕ)
    (Adata : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ : ℝ) (f : (Fin n → ℤ) → ℤ → ℂ)
    (hM₂ : 1 ≤ M₂) (hN : 1 ≤ N)
    (hKb : Kb = m * (Fintype.card (Work.Peluse.UControl.Slot ι k) * D + 1) + 1)
    (hhyp : γ ≤ ((Adata.card : ℝ))⁻¹ *
        ((Work.Peluse.UControl.paramBox (k := k) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ Adata, ∑ a' ∈ Work.Peluse.UControl.paramBox (k := k) M₂,
          Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx kω))
            (fun j => Work.Peluse.UControl.pDirFam p M₁ a a'
              ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j))
            (Work.Peluse.symIcc N) (f a)) :
    γ / ((Kb : ℝ) + 1) ≤ ((Adata.card : ℝ))⁻¹ *
        (((Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0)).card : ℝ)⁻¹ *
        ((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ)⁻¹ *
        ∑ a ∈ Adata,
          ∑ a'' ∈ (Work.Peluse.UControl.paramBox (k := k) M₂).filter (fun a'' => a'' s₀ = 0),
            ∑ a₀ ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
              Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx kω))
                (fun j => Work.Peluse.UControl.pDirFam p M₁ a (Function.update a'' s₀ a₀)
                  ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j))
                (Work.Peluse.symIcc (Kb * N)) (f a) := by
  have hKb1 : 1 ≤ Kb := by rw [hKb]; omega
  exact hyp_avg_split_aux (k := k) (M₂ := M₂) (s₀ := s₀) (Kb := Kb)
    (t := Fintype.card (Work.Peluse.UControl.FamIdx kω))
    (Adata := Adata) (N := N) (γ := γ)
    (Q := fun a a' j => Work.Peluse.UControl.pDirFam p M₁ a a'
      ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j))
    (g := f) hN hKb1 hhyp

end Work.Peluse.LadderA
