import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.Rec
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Core.TelTwoDF.Solves
import Submission.Work.CR.Flat.Cauchy.contDiff_dbarTransform

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-! ## Regularity, at an arbitrary finite order, of one step of the telescoping

`S2` is a sum of functions `uPsi G η s l = TL G s (κ_s · uD G η s s l)`, where `TL G s` (the
Cauchy-type transform, extended linearly to all data) agrees on continuous data with the integral
`dbarTransform (G.r s) s`.  Since the Cauchy kernel `1/w` is locally integrable and the
integration takes place in a *fixed* disc of the fibre variable, the transform loses no
derivatives: it maps `C^N` data supported in `{‖y s‖ < G.b s}` to `C^N` functions
(`contDiff_dbarTransform`).  Hence, by induction on the stage `m`, all the stages `uD G η m` are
`C^N` as soon as the data `η` are. -/

/-- `TL G s` maps `C^N` data supported in `{‖y s‖ < G.b s}` (more precisely, vanishing on
`G.b s ≤ ‖y s‖`) to `C^N` functions. -/
lemma contDiff_TL' (G : Geom n) {s : Fin n} {N : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ N g) (hsupp : ∀ y, G.b s ≤ ‖y s‖ → g y = 0) :
    ContDiff ℝ N (TL G s g) := by
  rw [TL_eq G s hg.continuous]
  exact Work.CR.Flat.Cauchy.contDiff_dbarTransform
    (by have h1 := G.hbr s; have h2 := G.hr s; linarith) s N hg hsupp

/-- One step of the recursion preserves `C^N` regularity. -/
lemma contDiff_uStep' (G : Geom n) {s : Fin n} {N : ℕ}
    {D : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hD : ∀ i l, ContDiff ℝ N (D i l)) (i l : Fin n) :
    ContDiff ℝ N (uStep G s D i l) := by
  by_cases hc : i = s ∨ l = s
  · have hfun : uStep G s D i l = fun z => (1 - kappa G s z) * D i l z := by
      funext z; rw [uStep_apply, if_pos hc]; ring
    rw [hfun]
    exact ((contDiff_const.sub (contDiff_kappa G s)).of_le (le_infty'' N)).mul (hD i l)
  · have hfun : uStep G s D i l = fun z => (1 - kappa G s z) * D i l z
        + TL G s (fun y => kappabar G s y * D i l y) z := by
      funext z; rw [uStep_apply, if_neg hc]
    rw [hfun]
    refine ContDiff.add (((contDiff_const.sub (contDiff_kappa G s)).of_le (le_infty'' N)).mul
      (hD i l)) ?_
    exact contDiff_TL' G (((contDiff_kappabar G s).of_le (le_infty'' N)).mul (hD i l))
      (fun y hy => by rw [kappabar_eq_zero_of_ge G s hy, zero_mul])

theorem S2_smooth {n : ℕ} (G : Work.NN.Core.TelTwoDF.Geom n) {ρ' : Fin n → ℝ}
    (hρ' : ∀ j, 0 < ρ' j) (hsub : ∀ j, ρ' j < G.e j)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ (N : ℕ) (i l : Fin n), ContDiff ℝ N (η i l)) (j : Fin n) (N : ℕ) :
    ContDiffOn ℝ N (Work.NN.Core.TelTwoDF.S2 G η j) (Work.CR.Flat.polydisc 0 ρ') := by
  -- all the stages of the recursion are `C^N`
  have hD : ∀ m ≤ n, ∀ i l, ContDiff ℝ N (uD G η m i l) := by
    intro m
    induction m with
    | zero => intro _ i l; simpa using hη N i l
    | succ m ih =>
        intro hm i l
        have hm' : m < n := by omega
        rw [uD_succ_of_lt G η hm']
        exact contDiff_uStep' G (s := ⟨m, hm'⟩) (D := uD G η m) (fun i l => ih (by omega) i l) i l
  -- hence so is every `(0,1)`-form produced by the recursion
  have huPsi : ∀ s : Fin n, ContDiff ℝ N (uPsi G η s j) := by
    intro s
    have hs : (s : ℕ) ≤ n := by have := s.isLt; omega
    have hsm : ContDiff ℝ N (fun y => kappa G s y * uD G η (s : ℕ) s j y) :=
      ((contDiff_kappa G s).of_le (le_infty'' N)).mul (hD (s : ℕ) hs s j)
    exact contDiff_TL' G hsm (fun y hy => by rw [kappa_eq_zero G s hy, zero_mul])
  -- and so is their sum `S2 G η j`
  have hsum : ContDiff ℝ N (fun z => ∑ s : Fin n, uPsi G η s j z) :=
    ContDiff.sum (s := Finset.univ) (fun s _ => huPsi s)
  have hfun : S2 G η j = fun z => ∑ s : Fin n, uPsi G η s j z := by
    funext z; rw [S2_apply]
  rw [hfun]
  exact hsum.contDiffOn

end Work.NN.Core.TelTwoDF
