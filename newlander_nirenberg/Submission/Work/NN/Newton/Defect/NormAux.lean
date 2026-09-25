import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.CR.Flat.Holder.Bilinear

/-!
# Elementary subadditivity lemmas for the `C^{0,α}`-norm at order `0`

The workspace's `holderNorm_add_le` / `holderNorm_smul` require `ContDiffOn` hypotheses (and an
open domain).  For the final assembly of `coordDatum_defect_quadratic` we need the corresponding
bounds for *arbitrary* functions on an arbitrary set, since the individual terms of the quadratic
remainder are only known to be `C^{0,α}` (they are not known to be smooth on the whole polydisc
without extra work).  The lemmas below provide exactly those tool-free bounds, together with a
`List` version used to bound the ten-term remainder `TA` term by term.
-/

namespace Work.NN.Newton

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma holderNorm_zero_eq (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α f Ω
      = Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.holderSeminorm 0 α f Ω := by
  simp [Work.CR.Flat.holderNorm]

/-- The `C^{k,α}`-norm only depends on the values on `Ω`. -/
lemma holderNorm_congrOn {k : ℕ} {α : ℝ} {f g : X → ℂ} {Ω : Set X}
    (h : ∀ x ∈ Ω, f x = g x) :
    Work.CR.Flat.holderNorm k α f Ω = Work.CR.Flat.holderNorm k α g Ω := by
  unfold Work.CR.Flat.holderNorm
  refine Finset.sum_congr rfl fun i _ => ?_
  show Work.CR.Flat.Holder.iDN i f Ω + Work.CR.Flat.Holder.hSN i α f Ω
      = Work.CR.Flat.Holder.iDN i g Ω + Work.CR.Flat.Holder.hSN i α g Ω
  rw [Work.CR.Flat.Holder.iDN_congr h, Work.CR.Flat.Holder.hSN_congr h]

/-- Subadditivity of the `C^{0,α}`-norm at order `0`, for arbitrary functions. -/
theorem holderNorm_zero_add_le {α : ℝ} {f g : X → ℂ} {Ω : Set X} :
    Work.CR.Flat.holderNorm 0 α (fun z => f z + g z) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω := by
  have h1 : Work.CR.Flat.iterDerivNorm 0 (fun z => f z + g z) Ω
      ≤ Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.iterDerivNorm 0 g Ω := by
    rw [Work.CR.Flat.iterDerivNorm_zero, Work.CR.Flat.iterDerivNorm_zero,
      Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun x hx => ?_
    calc ENNReal.ofReal ‖f x + g x‖ ≤ ENNReal.ofReal (‖f x‖ + ‖g x‖) :=
          ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ = ENNReal.ofReal ‖f x‖ + ENNReal.ofReal ‖g x‖ :=
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
      _ ≤ (⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖) + (⨆ x ∈ Ω, ENNReal.ofReal ‖g x‖) :=
          add_le_add (le_iSup₂_of_le x hx le_rfl) (le_iSup₂_of_le x hx le_rfl)
  have h2 : Work.CR.Flat.holderSeminorm 0 α (fun z => f z + g z) Ω
      ≤ Work.CR.Flat.holderSeminorm 0 α f Ω + Work.CR.Flat.holderSeminorm 0 α g Ω := by
    change Work.CR.Flat.Holder.hSN 0 α (fun z => f z + g z) Ω
      ≤ Work.CR.Flat.Holder.hSN 0 α f Ω + Work.CR.Flat.Holder.hSN 0 α g Ω
    rw [Work.CR.Flat.Holder.hSN_zero_deriv, Work.CR.Flat.Holder.hSN_zero_deriv,
      Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hd : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    have hnum : ‖(f x + g x) - (f y + g y)‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := by
      rw [show (f x + g x) - (f y + g y) = (f x - f y) + (g x - g y) from by ring]
      exact norm_add_le _ _
    calc ENNReal.ofReal (‖(f x + g x) - (f y + g y)‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal ((‖f x - f y‖ + ‖g x - g y‖) / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hnum (le_of_lt hd))
      _ = ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
            + ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) := by
          rw [add_div]
          exact ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (le_of_lt hd))
            (div_nonneg (norm_nonneg _) (le_of_lt hd))
      _ ≤ (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α))
            + (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y),
                ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)) :=
          add_le_add
            (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
            (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
  calc Work.CR.Flat.holderNorm 0 α (fun z => f z + g z) Ω
      = Work.CR.Flat.iterDerivNorm 0 (fun z => f z + g z) Ω
          + Work.CR.Flat.holderSeminorm 0 α (fun z => f z + g z) Ω :=
        holderNorm_zero_eq α _ Ω
    _ ≤ (Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.iterDerivNorm 0 g Ω)
          + (Work.CR.Flat.holderSeminorm 0 α f Ω + Work.CR.Flat.holderSeminorm 0 α g Ω) :=
        add_le_add h1 h2
    _ = (Work.CR.Flat.iterDerivNorm 0 f Ω + Work.CR.Flat.holderSeminorm 0 α f Ω)
          + (Work.CR.Flat.iterDerivNorm 0 g Ω + Work.CR.Flat.holderSeminorm 0 α g Ω) := by
        ring
    _ = Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω := by
        rw [holderNorm_zero_eq α f Ω, holderNorm_zero_eq α g Ω]

/-- Homogeneity of the `C^{0,α}`-norm at order `0` under multiplication by a constant. -/
theorem holderNorm_zero_const_mul_le {α : ℝ} {c : ℂ} {f : X → ℂ} {Ω : Set X} :
    Work.CR.Flat.holderNorm 0 α (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderNorm 0 α f Ω := by
  have h1 : Work.CR.Flat.iterDerivNorm 0 (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.iterDerivNorm 0 f Ω := by
    rw [Work.CR.Flat.iterDerivNorm_zero, Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun x hx => ?_
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg c)]
    have hx' : ENNReal.ofReal ‖f x‖ ≤ ⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖ :=
      le_iSup₂_of_le x hx le_rfl
    exact mul_le_mul_right hx' (ENNReal.ofReal ‖c‖)
  have h2 : Work.CR.Flat.holderSeminorm 0 α (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderSeminorm 0 α f Ω := by
    change Work.CR.Flat.Holder.hSN 0 α (fun z => c * f z) Ω
      ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.Holder.hSN 0 α f Ω
    rw [Work.CR.Flat.Holder.hSN_zero_deriv, Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [show ENNReal.ofReal (‖c * f x - c * f y‖ / ‖x - y‖ ^ α)
        = ENNReal.ofReal ‖c‖ * ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) from by
      rw [← mul_sub, norm_mul, mul_div_assoc, ENNReal.ofReal_mul (norm_nonneg c)]]
    have hle : ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)
        ≤ ⨆ (_ : x ≠ y), ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) :=
      le_iSup (fun _ : x ≠ y => ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α)) hxy
    exact mul_le_mul_right (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy hle))
      (ENNReal.ofReal ‖c‖)
  calc Work.CR.Flat.holderNorm 0 α (fun z => c * f z) Ω
      = Work.CR.Flat.iterDerivNorm 0 (fun z => c * f z) Ω
          + Work.CR.Flat.holderSeminorm 0 α (fun z => c * f z) Ω :=
        holderNorm_zero_eq α _ Ω
    _ ≤ ENNReal.ofReal ‖c‖ * Work.CR.Flat.iterDerivNorm 0 f Ω
          + ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderSeminorm 0 α f Ω := add_le_add h1 h2
    _ = ENNReal.ofReal ‖c‖ * (Work.CR.Flat.iterDerivNorm 0 f Ω
          + Work.CR.Flat.holderSeminorm 0 α f Ω) := by rw [mul_add]
    _ = ENNReal.ofReal ‖c‖ * Work.CR.Flat.holderNorm 0 α f Ω := by
        rw [holderNorm_zero_eq α f Ω]

/-- Negation does not change the `C^{0,α}`-norm at order `0`. -/
theorem holderNorm_zero_neg {α : ℝ} {f : X → ℂ} {Ω : Set X} :
    Work.CR.Flat.holderNorm 0 α (fun z => -f z) Ω = Work.CR.Flat.holderNorm 0 α f Ω := by
  refine le_antisymm ?_ ?_
  · have h := holderNorm_zero_const_mul_le (α := α) (c := (-1 : ℂ)) (f := f) (Ω := Ω)
    simpa using h
  · have h := holderNorm_zero_const_mul_le (α := α) (c := (-1 : ℂ))
      (f := fun z => -f z) (Ω := Ω)
    simpa using h

/-- Subadditivity of the `C^{0,α}`-norm at order `0` for differences. -/
theorem holderNorm_zero_sub_le {α : ℝ} {f g : X → ℂ} {Ω : Set X} :
    Work.CR.Flat.holderNorm 0 α (fun z => f z - g z) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω :=
  (holderNorm_zero_add_le (f := f) (g := fun z => -g z) (Ω := Ω)).trans
    (add_le_add le_rfl (le_of_eq (holderNorm_zero_neg (f := g) (α := α) (Ω := Ω))))

/-- Subadditivity of the `C^{0,α}`-norm at order `0` over a list of functions. -/
theorem holderNorm_zero_list_sum_le {α : ℝ} (l : List (X → ℂ)) (Ω : Set X) :
    Work.CR.Flat.holderNorm 0 α (fun z => (l.map (fun f => f z)).sum) Ω
      ≤ (l.map (fun f => Work.CR.Flat.holderNorm 0 α f Ω)).sum := by
  induction l with
  | nil =>
      have h0 : (fun z : X => (List.map (fun f => f z) ([] : List (X → ℂ))).sum)
          = (0 : X → ℂ) := by funext z; simp
      rw [h0]; simp
  | cons f t ih =>
      have hsp : (fun z => ((f :: t).map (fun g => g z)).sum)
          = fun z => f z + (t.map (fun g => g z)).sum := by
        funext z; simp [List.map_cons, List.sum_cons]
      rw [hsp, List.map_cons, List.sum_cons]
      exact holderNorm_zero_add_le.trans (add_le_add le_rfl ih)

end Work.NN.Newton
