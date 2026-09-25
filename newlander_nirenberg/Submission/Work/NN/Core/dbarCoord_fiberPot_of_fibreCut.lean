import Mathlib
import Submission.Work.NN.Core.fiberPot
import Submission.Work.CR.Flat.Cauchy.dbarTransform_dbarCoord
import Submission.Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self
import Submission.Work.CR.Flat.Cauchy.cauchyGreen_origin

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Work.NN.Core

/-- The fixed-disc Cauchy potential, written as an integral over the disc centred at `-(y j)` with
the pole at the origin: substituting `w = s + y j` in the defining integral. -/
private lemma fiberPot_eq_shift {n : ℕ} (R : ℝ) (j : Fin n) (v : (Fin n → ℂ) → ℂ)
    (y : Fin n → ℂ) :
    fiberPot R j v y = -((Real.pi : ℂ))⁻¹ *
      ∫ s in Metric.ball (-(y j)) R, v (y + Function.update (0 : Fin n → ℂ) j s) / s := by
  have hfun : ∀ x : ℂ,
      Function.update y j (x + y j) = y + Function.update (0 : Fin n → ℂ) j x := by
    intro x
    funext l
    by_cases hl : l = j
    · subst hl
      simp only [Function.update_self, Pi.add_apply]
      ring
    · simp only [Function.update_of_ne hl, Pi.add_apply, Pi.zero_apply, add_zero]
  have hpre : (fun x : ℂ => x + y j) ⁻¹' Metric.ball (0 : ℂ) R = Metric.ball (-(y j)) R := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero, sub_neg_eq_add]
  have hmp : MeasurePreserving (fun x : ℂ => x + y j) volume volume :=
    MeasureTheory.measurePreserving_add_right volume (y j)
  have hemb : MeasurableEmbedding (fun x : ℂ => x + y j) :=
    (MeasurableEquiv.addRight (y j)).measurableEmbedding
  have hkey : ∫ w in Metric.ball (0 : ℂ) R, v (Function.update y j w) / (w - y j)
      = ∫ s in Metric.ball (-(y j)) R, v (y + Function.update (0 : Fin n → ℂ) j s) / s := by
    have hpre_int := hmp.setIntegral_preimage_emb hemb
        (fun w : ℂ => v (Function.update y j w) / (w - y j)) (Metric.ball (0 : ℂ) R)
    rw [← hpre_int, hpre]
    refine setIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
    rw [hfun x, add_sub_cancel_right]
  rw [Work.NN.Core.fiberPot_apply, hkey]

/-- Fibre translations act trivially on the Cauchy-type transform `dbarTransform`: replacing the
data `φ` by `y ↦ φ (y + a)` amounts to shifting the point of evaluation by `-a`. -/
private lemma dbarTransform_comp_add {n : ℕ} (ρ : ℝ) (j : Fin n) (a : Fin n → ℂ)
    (φ : (Fin n → ℂ) → ℂ) (w : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.dbarTransform ρ j (fun y => φ (y + a)) w
      = Work.CR.Flat.Cauchy.dbarTransform ρ j φ (w + a) := by
  rw [Work.CR.Flat.Cauchy.dbarTransform, Work.CR.Flat.Cauchy.dbarTransform]
  congr 1
  refine setIntegral_congr_fun measurableSet_ball (fun s _ => ?_)
  rw [show w + Function.update (0 : Fin n → ℂ) j s + a
      = (w + a) + Function.update (0 : Fin n → ℂ) j s from by abel]

/-- The `j`-th `∂̄`-operator is invariant under translations: `∂̄_j (φ ∘ (· + a)) = (∂̄_j φ) ∘ (· + a)`. -/
private lemma dbarCoord_comp_add {n : ℕ} (j : Fin n) (a : Fin n → ℂ)
    (φ : (Fin n → ℂ) → ℂ) (y : Fin n → ℂ) :
    Work.CR.Flat.dbarCoord j (fun y => φ (y + a)) y = Work.CR.Flat.dbarCoord j φ (y + a) := by
  rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, fderiv_comp_add_right a]

theorem dbarCoord_fiberPot_of_fibreCut {n : ℕ} (R : ℝ) (hR : 0 < R) (j : Fin n)
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiff ℝ 1 u) {z : Fin n → ℂ} (hz : ‖z j‖ < R)
    {c : ℂ → ℂ} (hc : ContDiff ℝ 1 c) {ρ : ℝ} (hρnn : 0 ≤ ρ) (hρR : ‖z j‖ + ρ < R)
    (hcsupp : ∀ ζ : ℂ, ρ ≤ ‖ζ‖ → c ζ = 0) (hc0 : c 0 = 1) :
    Work.CR.Flat.dbarCoord j
      (Work.NN.Core.fiberPot R j (fun y => u y * c (y j - z j))) z = u z := by
  -- the cutoff radius is positive: `c` is `1` at `0` but vanishes outside the disc of radius `ρ`
  have hρpos : 0 < ρ := by
    rcases eq_or_lt_of_le hρnn with h | h
    · exfalso
      have h0 : c 0 = 0 := hcsupp 0 (by rw [norm_zero]; exact le_of_eq h.symm)
      rw [hc0] at h0
      exact one_ne_zero h0
    · exact h
  set v : (Fin n → ℂ) → ℂ := fun y => u y * c (y j - z j) with hvdef
  have hvcd : ContDiff ℝ 1 v := by
    rw [hvdef]
    refine hu.mul (hc.comp ?_)
    exact ((contDiff_apply ℝ ℂ j).sub contDiff_const).of_le le_top
  -- on the neighbourhood `‖y j - z j‖ < ρ` the fixed-disc potential agrees with the
  -- translation-invariant Cauchy transform of radius `2ρ`
  have key : ∀ y : Fin n → ℂ, ‖y j - z j‖ < ρ →
      fiberPot R j v y = Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v y := by
    intro y hy
    rw [fiberPot_eq_shift R j v y]
    rw [show Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v y
        = -((Real.pi : ℂ))⁻¹ * ∫ s in Metric.ball (0 : ℂ) (2 * ρ),
            v (y + Function.update (0 : Fin n → ℂ) j s) / s from rfl]
    congr 1
    have hpt : ∀ s : ℂ,
        v (y + Function.update (0 : Fin n → ℂ) j s)
          = u (y + Function.update (0 : Fin n → ℂ) j s) * c ((y j + s) - z j) := by
      intro s
      rw [hvdef]
      simp only [Pi.add_apply, Function.update_self]
    have hA : ∀ s : ℂ, s ∉ Metric.ball (-(y j)) R →
        v (y + Function.update (0 : Fin n → ℂ) j s) / s = 0 := by
      intro s hs
      rw [Metric.mem_ball, not_lt, dist_eq_norm] at hs
      have h1 : R ≤ ‖s + y j‖ := by simpa [sub_neg_eq_add] using hs
      have h2 : ρ < ‖(y j + s) - z j‖ := by
        have hle : ‖s + y j‖ ≤ ‖(y j + s) - z j‖ + ‖z j‖ := by
          calc ‖s + y j‖ = ‖((y j + s) - z j) + z j‖ := by congr 1; ring
            _ ≤ ‖(y j + s) - z j‖ + ‖z j‖ := norm_add_le _ _
        linarith
      rw [hpt s, hcsupp ((y j + s) - z j) (le_of_lt h2)]
      simp
    have hB : ∀ s : ℂ, s ∉ Metric.ball (0 : ℂ) (2 * ρ) →
        v (y + Function.update (0 : Fin n → ℂ) j s) / s = 0 := by
      intro s hs
      rw [Metric.mem_ball, not_lt, dist_eq_norm, sub_zero] at hs
      have h2 : ρ < ‖(y j + s) - z j‖ := by
        have hle : ‖s‖ ≤ ‖(y j + s) - z j‖ + ‖y j - z j‖ := by
          calc ‖s‖ = ‖((y j + s) - z j) - (y j - z j)‖ := by congr 1; ring
            _ ≤ ‖(y j + s) - z j‖ + ‖y j - z j‖ := norm_sub_le _ _
        linarith
      rw [hpt s, hcsupp ((y j + s) - z j) (le_of_lt h2)]
      simp
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hA,
      setIntegral_eq_integral_of_forall_compl_eq_zero hB]
  -- consequently the two functions agree near `z`, so their `fderiv`s at `z` agree
  have hev : (fun y => fiberPot R j v y) =ᶠ[𝓝 z]
      (fun y => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v y) := by
    have hopen : {y : Fin n → ℂ | ‖y j - z j‖ < ρ} ∈ 𝓝 z :=
      (isOpen_lt ((continuous_apply j).sub continuous_const |>.norm) continuous_const).mem_nhds
        (by simp [hρpos])
    filter_upwards [hopen] with y hy
    exact key y hy
  have hfd : fderiv ℝ (fun y => fiberPot R j v y) z
      = fderiv ℝ (fun y => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v y) z :=
    hev.fderiv_eq
  have hstep : Work.CR.Flat.dbarCoord j (fun y => fiberPot R j v y) z
      = Work.CR.Flat.dbarCoord j
          (fun y => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v y) z := by
    rw [Work.CR.Flat.dbarCoord, Work.CR.Flat.dbarCoord, hfd]
  -- shift the fibre so that the support is centred at the origin: set `a = z j e_j`
  set a : Fin n → ℂ := Function.update (0 : Fin n → ℂ) j (z j) with hadef
  set sh : Fin n → ℂ := Function.update z j 0 with hshdef
  have hsh_a : sh + a = z := by
    funext i
    by_cases hi : i = j
    · subst hi; simp [hadef, hshdef, Pi.add_apply]
    · simp [hadef, hshdef, Pi.add_apply, Function.update_of_ne hi]
  set G : (Fin n → ℂ) → ℂ := fun y => v (y + a) with hGdef
  have hGcd : ContDiff ℝ 1 G := by
    rw [hGdef]
    exact hvcd.comp (contDiff_id.add contDiff_const)
  have hGsupp : ∀ y : Fin n → ℂ, (2 * ρ) / 2 ≤ ‖y j‖ → G y = 0 := by
    intro y hy
    have hy0 : ρ ≤ ‖y j‖ := by linarith
    have h1 : G y = u (y + a) * c (y j) := by
      simp only [hGdef, hvdef, hadef, Pi.add_apply, Function.update_self,
        add_sub_cancel_right]
    rw [h1, hcsupp (y j) hy0, mul_zero]
  -- The statement carries `0 < R` even though it follows from `‖z j‖ + ρ < R` and `0 ≤ ρ`;
  -- the two radius hypotheses together give `2ρ > 0`, which is what the transform needs.
  have htwoρ : (0 : ℝ) < 2 * ρ := by
    have h2R : (0 : ℝ) < 2 * R := mul_pos two_pos hR
    exact Or.elim (Or.inl h2R) (fun _ => by positivity) (fun h => h)
  have hsh_small : ‖sh j‖ < (2 * ρ) / 2 := by
    have h0 : sh j = 0 := by simp [hshdef]
    rw [h0, norm_zero]; linarith
  have hkey1 : Work.CR.Flat.dbarCoord j
      (fun y => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j G y) sh = G sh := by
    rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord j j hGcd sh]
    exact Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self htwoρ j
      hGcd hGsupp (by linarith [hsh_small])
  have hkey2 : Work.CR.Flat.dbarCoord j
      (fun y => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j G y) sh
      = Work.CR.Flat.dbarCoord j
          (fun y => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v y) z := by
    have hfun : (fun y => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j G y)
        = fun y => (fun ξ => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v ξ) (y + a) := by
      funext y
      rw [hGdef]
      exact dbarTransform_comp_add (2 * ρ) j a v y
    rw [hfun, dbarCoord_comp_add j a (fun ξ => Work.CR.Flat.Cauchy.dbarTransform (2 * ρ) j v ξ) sh,
      hsh_a]
  have hGsh : G sh = v z := by simp only [hGdef, hsh_a]
  have hvz : v z = u z := by
    rw [hvdef]
    simp [hc0]
  have hmain : Work.CR.Flat.dbarCoord j (fun y => fiberPot R j v y) z = u z := by
    rw [hstep, ← hkey2, hkey1, hGsh, hvz]
  rw [show Work.CR.Flat.dbarCoord j
        (Work.NN.Core.fiberPot R j (fun y => u y * c (y j - z j))) z
      = Work.CR.Flat.dbarCoord j (fun y => fiberPot R j v y) z from by rw [hvdef]]
  exact hmain

end Work.NN.Core
