import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dent_annulus_defs
import Submission.Work.Drive.Final.fderiv_sweepHeight_dent_sub_le
import Submission.Work.Drive.Final.dent_annulus_margin

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

/-!
# L4a: regularity of the deformed sweep height on the dent annulus

The dent `D.deform` changes the sweep height `ℓ ∘ par` by a bump of size `≤ a' ‖ℓ‖ (κ/r) ‖d(par)‖`
(`fderiv_sweepHeight_dent_sub_le`).  On the *annulus* `r/2 ≤ ‖par q − centre‖ ≤ r`, in the closed box
and the closed slab, the *undeformed* sweep height is bounded below by `m` and transverse to the slab
functional and the box norm with determinant `≥ m` (`dent_annulus_margin`).  Since the two
determinants are Lipschitz with constant `2 ‖·‖ ‖·‖` (`det2_sub_le`), the single inequality

  `a' ‖ℓ‖ (κ/r) M (1 + 2M) < m/2`

keeps the deformed height non-zero, and keeps it from being proportional to either face functional.
This file isolates the two abstract linear-algebra steps and applies them.
-/

/-! ## Abstract bricks -/

/-- `det2` is homogeneous in its first argument. -/
theorem det2_smulClm (t : ℝ) (L D : (ℝ × ℝ) →L[ℝ] ℝ) :
    det2 (t • L) D = t * det2 L D := by
  simp only [det2, smul_apply, smul_eq_mul]
  ring

/-- A linear form has vanishing `det2` against itself. -/
theorem det2_selfClm (L : (ℝ × ℝ) →L[ℝ] ℝ) : det2 L L = 0 := by
  simp only [det2]
  ring

/-- **Non-vanishing from closeness to a form bounded below by `m`.** -/
theorem clm_ne_zero_of_close {L S : (ℝ × ℝ) →L[ℝ] ℝ} {ε m : ℝ}
    (hε : ‖L - S‖ ≤ ε) (hm : m ≤ ‖S‖) (hlt : ε < m) : L ≠ 0 := by
  intro h0
  have hS : S - L = S := by rw [h0, sub_zero]
  have h1 : ‖S‖ ≤ ε := by
    calc ‖S‖ = ‖S - L‖ := by rw [hS]
      _ = ‖L - S‖ := (norm_sub_rev L S).symm
      _ ≤ ε := hε
  linarith

/-- **Non-proportionality from closeness to a transverse pair.**  If `L` is within `ε` of `S`, the
form `P` is bounded by `M`, the pair `(S, P)` is transverse with `|det2 S P| ≥ m`, and
`2 ε M < m`, then `L` is nowhere a multiple of `P`. -/
theorem not_smul_of_det2_close {L S P : (ℝ × ℝ) →L[ℝ] ℝ} {ε M m : ℝ}
    (hε : ‖L - S‖ ≤ ε) (hP : ‖P‖ ≤ M) (hdet : m ≤ |det2 S P|)
    (hlt : 2 * ε * M < m) : ∀ t : ℝ, L ≠ t • P := by
  intro t ht
  have hεnn : 0 ≤ ε := le_trans (norm_nonneg _) hε
  have hzero : det2 L P = 0 := by rw [ht, det2_smulClm, det2_selfClm, mul_zero]
  have hbound : |det2 L P - det2 S P| ≤ 2 * ε * M := by
    refine le_trans (det2_sub_le S L P) ?_
    have h1 : ‖L - S‖ * ‖P‖ ≤ ε * M := mul_le_mul hε hP (norm_nonneg _) hεnn
    calc 2 * ‖L - S‖ * ‖P‖ = 2 * (‖L - S‖ * ‖P‖) := by ring
      _ ≤ 2 * (ε * M) := by linarith
      _ = 2 * ε * M := by ring
  have hm' : m ≤ 2 * ε * M := by
    calc m ≤ |det2 S P| := hdet
      _ = |det2 S P - det2 L P| := by rw [hzero, sub_zero]
      _ = |det2 L P - det2 S P| := abs_sub_comm _ _
      _ ≤ 2 * ε * M := hbound
  linarith

theorem dent_annulus_regular {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U) {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hmargin : ∀ q : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ q ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q)| ≤ h →
      ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ ≤ M ∧
      ‖fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q‖ ≤ M ∧
      m ≤ ‖fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q‖ ∧
      (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q)| = h →
        m ≤ |Work.Drive.Final.det2 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q)
                 (fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q)|) ∧
      (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) = s →
        ‖fderiv ℝ (fun q' : ℝ × ℝ =>
            Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q‖ ≤ M ∧
        m ≤ |Work.Drive.Final.det2 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q)
                 (fderiv ℝ (fun q' : ℝ × ℝ =>
                    Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q)|))
    (hχ : ContDiff ℝ 1 D.χ) (hχ1 : ∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1)
    (ha : D.a' * ‖ℓ‖ * (D.κ / D.r) * M * (1 + 2 * M) < m / 2)
    {q : ℝ × ℝ} (h1 : D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q - D.centre‖)
    (h2 : ‖Work.BoxShrink.Pinch.par ψ q - D.centre‖ ≤ D.r)
    (h3 : Work.BoxShrink.Pinch.par ψ q ∈ closure (Submission.PBox s c σ))
    (h4 : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q)| ≤ h) :
    fderiv ℝ (fun q' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q'))) q ≠ 0 ∧
    (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q)| = h → ∀ t : ℝ,
      fderiv ℝ (fun q' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q'))) q ≠
        t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q) ∧
    (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) = s → ∀ t : ℝ,
      fderiv ℝ (fun q' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q'))) q ≠
        t • fderiv ℝ (fun q' : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q) := by
  obtain ⟨hM1, hM2, hm3, hh4, hh5⟩ := hmargin q h1 h2 h3 h4
  -- the constant of the perturbation
  have hCnneg : 0 ≤ D.a' * ‖ℓ‖ * (D.κ / D.r) :=
    mul_nonneg (mul_nonneg D.a'_pos.le (norm_nonneg ℓ)) (div_pos D.κ_pos D.r_pos).le
  have hCMnn : 0 ≤ D.a' * ‖ℓ‖ * (D.κ / D.r) * M := mul_nonneg hCnneg hM.le
  -- the undeformed gradient is at least `m`; the dent moves it by at most `a' ‖ℓ‖ (κ/r) M`
  have hsub :
      ‖fderiv ℝ (fun q' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q'))) q -
          fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q‖ ≤
        D.a' * ‖ℓ‖ * (D.κ / D.r) * M :=
    le_trans (fderiv_sweepHeight_dent_sub_le D hχ hχ1 q)
      (mul_le_mul_of_nonneg_left hM1 hCnneg)
  -- the two slack inequalities
  have hlt1 : D.a' * ‖ℓ‖ * (D.κ / D.r) * M < m := by
    have h1 : D.a' * ‖ℓ‖ * (D.κ / D.r) * M ≤
        D.a' * ‖ℓ‖ * (D.κ / D.r) * M * (1 + 2 * M) := by
      have h2 : (1 : ℝ) ≤ 1 + 2 * M := by linarith [hM]
      simpa using mul_le_mul_of_nonneg_left h2 hCMnn
    linarith [h1, ha, hm]
  have htwo : 2 * (D.a' * ‖ℓ‖ * (D.κ / D.r) * M) * M < m := by
    have h2M : 2 * M ≤ 1 + 2 * M := by linarith [hM]
    have hle : D.a' * ‖ℓ‖ * (D.κ / D.r) * M * (2 * M) ≤
        D.a' * ‖ℓ‖ * (D.κ / D.r) * M * (1 + 2 * M) :=
      mul_le_mul_of_nonneg_left h2M hCMnn
    linarith [hle, ha, hm, hCMnn]
  refine ⟨?_, ?_, ?_⟩
  · exact clm_ne_zero_of_close hsub hm3 hlt1
  · intro hh t
    exact not_smul_of_det2_close hsub hM2 (hh4 hh) htwo t
  · intro hbn t
    exact not_smul_of_det2_close hsub (hh5 hbn).1 (hh5 hbn).2 htwo t


end Work.Drive.Final
