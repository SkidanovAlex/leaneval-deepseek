import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imgFibre_boxSmooth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibre2_boxSmooth`

The **mirror** of `Work.BoseBoxFock.imgFibre_boxSmooth`: the fibre `imgFibre₂C ℓ p F₁ G`
(`Work.BoseBoxFock.imagesFibre`), whose inner `boxL`-average sits in the **`p.2`-slot** of the
first state factor, also agrees on the box squared with a `C^∞` function.

The argument is verbatim the one of the sibling file (the fibre is the parametric integral, over
the two fixed compact boxes `boxL ℓ` and `boxPiSet ℓ`, of a jointly `C^∞` integrand, and the state
carries no box indicator), with the single change that the integrated variable `s` is inserted in
the **first** slot of `insertCoord2` in the `F₁`-factor instead of the second.  Nothing else in the
proof depends on which slot is averaged, so the two files differ only in the definition of the
smooth candidate and in the bookkeeping of that one insertion.

* `imgFibre₂Core` — the smooth candidate (the `ℂ`-valued form of `imgFibre₂`);
* `contDiff_imgFibre₂Core` — it is `C^∞`;
* `imgFibre₂Core_eq` — it agrees with `imgFibre₂C` everywhere (via `integral_ofReal`);
* `imgFibre2_boxSmooth` — the requested statement.

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The smooth candidate for the mirror fibre: the box-restricted integral of the jointly `C^∞`
mirror integrand, spelled with `ℂ`-valued integrals so that it is manifestly smooth. -/
noncomputable def imgFibre₂Core {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F₁ G : Submission.BoseGases.X n → ℝ) (u v : E3) : ℂ :=
  (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) *
    ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
      ∫ s in boxL ℓ,
        ((F₁ (insertCoord2 p u s x') : ℂ) * (G (insertCoord2 p u v x') : ℂ))

/-- **The candidate is `C^∞`.**  Both integration domains are compact and the integrand is jointly
`C^∞` in `(u, v, x', s)`, so the parametric integral is `C^∞` — once for `s ∈ boxL ℓ`, once for
`x' ∈ boxPiSet ℓ`. -/
theorem contDiff_imgFibre₂Core {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (imgFibre₂Core ℓ p F₁ G)) := by
  have hK1 : IsCompact (boxL ℓ) := by
    rw [corpusBox_boxL_eq_acube hℓ]
    exact Submission.BoseGases.acube_compact hℓ
  have hK2 : IsCompact (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ) := isCompact_boxPiSet hℓ
  have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  -- the two insertions of a slot value, as functions of `(u, v, x', s)`
  have hins₁ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3 =>
        insertCoord2 p z.1.1.1 z.2 z.1.2) :=
    contDiff_insertCoord2_comp p (contDiff_fst.comp (contDiff_fst.comp contDiff_fst))
      contDiff_snd (contDiff_snd.comp contDiff_fst)
  have hins₂ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3 =>
        insertCoord2 p z.1.1.1 z.1.1.2 z.1.2) :=
    contDiff_insertCoord2_comp p (contDiff_fst.comp (contDiff_fst.comp contDiff_fst))
      (contDiff_snd.comp (contDiff_fst.comp contDiff_fst)) (contDiff_snd.comp contDiff_fst)
  -- joint smoothness of the integrand
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun (r : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))
          (s : E3) =>
        (F₁ (insertCoord2 p r.1.1 s r.2) : ℂ) * (G (insertCoord2 p r.1.1 r.1.2 r.2) : ℂ))) := by
    show ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) × E3 =>
        (F₁ (insertCoord2 p z.1.1.1 z.2 z.1.2) : ℂ) *
          (G (insertCoord2 p z.1.1.1 z.1.1.2 z.1.2) : ℂ))
    exact (hcast.comp (hF₁.comp hins₁)).mul (hcast.comp (hG.comp hins₂))
  -- the `s`-integral over the compact box `boxL ℓ`
  have hstep1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun r : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        ∫ s in boxL ℓ,
          (F₁ (insertCoord2 p r.1.1 s r.2) : ℂ) * (G (insertCoord2 p r.1.1 r.1.2 r.2) : ℂ)) :=
    contDiff_setIntegral_compact_gen hK1 hF
  -- the `x'`-integral over the compact box `boxPiSet ℓ`
  have hstep2 : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 × E3 =>
      ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ∫ s in boxL ℓ, (F₁ (insertCoord2 p q.1 s x') : ℂ) *
          (G (insertCoord2 p q.1 q.2 x') : ℂ)) := by
    have hfun : Function.uncurry
        (fun (q : E3 × E3) (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
          ∫ s in boxL ℓ, (F₁ (insertCoord2 p q.1 s x') : ℂ) *
            (G (insertCoord2 p q.1 q.2 x') : ℂ))
        = fun r : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
            ∫ s in boxL ℓ, (F₁ (insertCoord2 p r.1.1 s r.2) : ℂ) *
              (G (insertCoord2 p r.1.1 r.1.2 r.2) : ℂ) := rfl
    refine contDiff_setIntegral_compact_gen hK2 ?_
    rw [hfun]
    exact hstep1
  have hmain : ContDiff ℝ (⊤ : ℕ∞) (fun q : E3 × E3 => (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) *
      ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ∫ s in boxL ℓ, (F₁ (insertCoord2 p q.1 s x') : ℂ) *
          (G (insertCoord2 p q.1 q.2 x') : ℂ)) :=
    hstep2.const_smul (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)
  have hfun2 : Function.uncurry (imgFibre₂Core ℓ p F₁ G) = fun q : E3 × E3 =>
      (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) *
        ∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ∫ s in boxL ℓ, (F₁ (insertCoord2 p q.1 s x') : ℂ) *
            (G (insertCoord2 p q.1 q.2 x') : ℂ) := rfl
  rw [hfun2]
  exact hmain

/-- **The candidate agrees with `imgFibre₂C`** (everywhere, not merely on the box squared).  The two
`ℂ`-valued integrals are the casts of the two `ℝ`-valued ones by `integral_ofReal`, and the
elementwise cast is `Complex.ofReal_mul`. -/
theorem imgFibre₂Core_eq {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    (F₁ G : Submission.BoseGases.X n → ℝ) :
    imgFibre₂Core ℓ p F₁ G = imgFibre₂C ℓ p F₁ G := by
  funext u v
  have hinner : ∀ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3,
      (∫ s in boxL ℓ, (F₁ (insertCoord2 p u s x') : ℂ) *
        (G (insertCoord2 p u v x') : ℂ))
        = ((∫ s in boxL ℓ, F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x') : ℝ) : ℂ) := by
    intro x'
    have h1 : (∫ s in boxL ℓ, (F₁ (insertCoord2 p u s x') : ℂ) *
          (G (insertCoord2 p u v x') : ℂ))
        = ∫ s in boxL ℓ,
            ((F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x') : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [Complex.ofReal_mul]
    rw [h1]
    exact integral_ofReal
  have houter : (∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ∫ s in boxL ℓ, (F₁ (insertCoord2 p u s x') : ℂ) *
          (G (insertCoord2 p u v x') : ℂ))
      = ((∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
          ∫ s in boxL ℓ, F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x') : ℝ) : ℂ) := by
    have heq : (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 =>
          ∫ s in boxL ℓ, (F₁ (insertCoord2 p u s x') : ℂ) *
            (G (insertCoord2 p u v x') : ℂ))
        = fun x' => ((∫ s in boxL ℓ,
            F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x') : ℝ) : ℂ) :=
      funext hinner
    rw [heq]
    exact integral_ofReal
  show (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∫ x' in boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ,
        ∫ s in boxL ℓ, (F₁ (insertCoord2 p u s x') : ℂ) *
          (G (insertCoord2 p u v x') : ℂ))
      = ((imgFibre₂ ℓ p F₁ G u v : ℝ) : ℂ)
  rw [imgFibre₂, Complex.ofReal_mul, houter]

theorem imgFibre2_boxSmooth {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Work.BoseBoxFock.BoxSmooth ℓ (Work.BoseBoxFock.imgFibre₂C ℓ p F₁ G) :=
  ⟨imgFibre₂Core ℓ p F₁ G, contDiff_imgFibre₂Core hℓ hF₁ hG,
    fun u v _ _ => congrFun (congrFun (imgFibre₂Core_eq ℓ p F₁ G) u) v⟩

end Work.BoseBoxFock
