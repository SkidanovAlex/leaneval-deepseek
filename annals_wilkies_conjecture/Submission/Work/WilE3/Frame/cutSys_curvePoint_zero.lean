/-
  annals_wilkies_conjecture, AREA E3, count half: a point of the straightened curve satisfies the
  perturbed cut system.

  The count half of `E3_identity` (`Work.WilE3.Frame.order_le_multiplicity`) counts the simple zeros
  of the one-variable function `t ↦ eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` as nondegenerate zeros of the
  `k × k` system `cutSys h (fun a => cutPoly ι (μ a) x) f` perturbed by `ε • pertSys`.  This file
  provides the *verification* of the equations of the perturbed system, i.e. that the point
  `Zt = Ψ (u₀ + t • w_ℂ, 0)` (or, more precisely, any point `Zt` with `PhiC c h ι Zt = (u₀ + t • w_ℂ, 0)`)
  satisfies

  `eaEvalC c (cutSys h (fun a => cutPoly ι (μ a) x) f i) Zt + ε * eaEvalC c (pertSys hjk i) Zt = 0`

  whenever `eaEvalC c f Zt = ε`.

  The three blocks are checked separately (`cutSys_cases`):
  * the `h`-rows: `PhiC c h ι Zt = (·, 0)` gives `eaEvalC c (h a) Zt = 0`, and `pertSys` vanishes
    off the `f`-row;
  * the cut rows: `Zt i = x i + t * w i` for the tangential coordinates `i : U k ι`, so
    `eaEvalC c (cutPoly ι (μ a) x) Zt = t * ∑ i, μ a i * w i = 0` by `CutForms`;
  * the `f`-row: `eaEvalC c f Zt = ε` and `pertSys` is `-1` there.
-/
import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.CutPolyVal

namespace Work.WilE3.Frame

open WilkiesDesign.E
open Work.WilE3

/-- The `h`-rows of the cut system are not the `f`-row. -/
lemma rowH_ne_rowF {k j : ℕ} (hjk : j < k) (a : Fin j) : rowH hjk a ≠ rowF hjk := by
  intro hh
  have hval : (rowH hjk a).val = (rowF hjk).val := congrArg Fin.val hh
  simp only [rowH, rowF] at hval
  omega

/-- The cut rows of the cut system are not the `f`-row. -/
lemma rowL_ne_rowF {k j : ℕ} (hjk : j < k) (a : Fin (k - j - 1)) : rowL hjk a ≠ rowF hjk := by
  intro hh
  have hval : (rowL hjk a).val = (rowF hjk).val := congrArg Fin.val hh
  simp only [rowL, rowF] at hval
  omega

theorem cutSys_curvePoint_zero {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k) (x : Fin k → ℝ)
    (hjk : j < k) (w : Work.WilE3.Frame.U k ι → ℝ)
    (μ : Fin (k - j - 1) → (Work.WilE3.Frame.U k ι → ℝ))
    (hμ : Work.WilE3.Frame.CutForms ι w μ) (f : WilkiesDesign.E.EAPoly k r)
    (t ε : ℂ) (Zt : Fin k → ℂ)
    (hZ : Work.WilE3.Frame.PhiC c h ι Zt
      = (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x)
          + t • (fun i => (w i : ℂ)), 0))
    (hf : Work.WilE3.eaEvalC c f Zt = ε) :
    ∀ i : Fin k, Work.WilE3.eaEvalC c
        (Work.WilE3.Frame.cutSys h (fun a => Work.WilE3.Frame.cutPoly ι (μ a) x) f i) Zt
      + ε * Work.WilE3.eaEvalC c (Work.WilE3.Frame.pertSys (k := k) (r := r) hjk i) Zt = 0 := by
  -- The two components of the hypothesis `PhiC c h ι Zt = (u₀ + t • w_ℂ, 0)`.
  have hZ1 : uCoord k ι Zt = uCoord k ι (toC x) + t • (fun i => (w i : ℂ)) := by
    have h1 := congrArg Prod.fst hZ
    simpa [PhiC] using h1
  have hZ2 : ∀ a, eaEvalC c (h a) Zt = 0 := by
    intro a
    have h1 := congrFun (congrArg Prod.snd hZ) a
    simpa [PhiC] using h1
  -- Tangential coordinates of `Zt`: `Zt i = x i + t * w i` for `i : U k ι`.
  have hcoord : ∀ i : U k ι, Zt i.1 = (x i.1 : ℂ) + t * (w i : ℂ) := by
    intro i
    have h1 := congrFun hZ1 i
    simpa [uCoord, toC, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1
  intro i
  rcases cutSys_cases hjk i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · -- `h`-rows
    have hrow : cutSys h (fun a => cutPoly ι (μ a) x) f (rowH hjk a) = h a :=
      cutSys_rowH hjk h _ f a
    rw [hrow, hZ2 a, pertSys_of_ne hjk (rowH_ne_rowF hjk a), Work.WilE3.API.eaEvalC_zero]
    ring
  · -- cut rows
    have hrow : cutSys h (fun a => cutPoly ι (μ a) x) f (rowL hjk a)
        = cutPoly ι (μ a) x :=
      cutSys_rowL hjk h (fun a => cutPoly ι (μ a) x) f a
    have hw0 : (∑ i : U k ι, (μ a i : ℂ) * (w i : ℂ)) = 0 := by
      have hh' : ((∑ i : U k ι, μ a i * w i : ℝ) : ℂ) = 0 := by
        rw [hμ.1 a]
        simp
      rw [← hh', Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.ofReal_mul]
    have hsum : eaEvalC c (cutPoly ι (μ a) x) Zt = 0 := by
      rw [eaEvalC_cutPoly]
      have h1 : (∑ i : U k ι, (μ a i : ℂ) * (Zt i.1 - (x i.1 : ℂ)))
          = t * ∑ i : U k ι, (μ a i : ℂ) * (w i : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoord i]
        ring
      rw [h1, hw0]
      ring
    rw [hrow, hsum, pertSys_of_ne hjk (rowL_ne_rowF hjk a), Work.WilE3.API.eaEvalC_zero]
    ring
  · -- the `f`-row
    have hrow : cutSys h (fun a => cutPoly ι (μ a) x) f (rowF hjk) = f :=
      cutSys_rowF hjk h _ f
    rw [hrow, hf, eaEvalC_pertSys]
    ring

end Work.WilE3.Frame
