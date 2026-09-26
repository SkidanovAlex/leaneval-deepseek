import Mathlib
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Final.anyEvent_isolated
import Submission.Work.Drive.Final.annulus_cornerFree
import Submission.Work.Drive.Final.dent_annulus_margin
import Submission.Work.Drive.Final.dent_annulus_regular
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Final.anyDentData_exists_depthFn
import Submission.Work.Drive.Final.sphereCover_pinch_margin

namespace Work.Drive.Final

noncomputable section

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **The dent data at an event, with the depth bounded by a prescribed `η > 0`** (project lead's
`NOTES_LEAD_LD_interface.md` item 4(b), the producer half of `Work.Drive.Final.eventTraceData_holds`).

At every event `pp` of a good tilted sweep and every neighbourhood `U` of its image there is a dent
datum `D` (over `U`) whose depth is controlled so that all of the following hold:

* `D.r < 1/4` (the dent's ball is inessential) and `D.a' * D.κ < D.r` (so `D.deform` is a
  homeomorphism, `Work.Drive.Final.dentDeform_homeomorph`);
* the cutoff is `C^∞` and `= 1` on `|t| ≤ 1/2` (the core of `D.deform` is a translation);
* **event isolation at the dent's own radius**: every event whose image lies within `D.r` of
  `D.centre` has image `D.centre`;
* the event's level `λ* = ℓ D.centre` and the shifted level `λ' = ℓ D.centre - D.a' * ℓ D.d` both lie
  in `[lam0, lam1]`, and **`λ' ∉ exc`**;
* the **annulus regularity** of the deformed wall: the conclusion of
  `Work.Drive.Final.dent_annulus_regular` on the annulus `D.r/2 ≤ ρ ≤ D.r`;
* the **annulus is corner-free**: no point of the annulus is simultaneously on the box sphere and on
  a slab face (this is `hslack`, the hypothesis of `Work.Drive.Final.dent_annulus_margin`, and it is
  *not* implied by the regularity clause — without it the trace in the annulus has a four-armed
  triple junction, see `NOTES_L4b_triple_obstruction.md`). -/
theorem exists_dentCaptureDepth {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ} (hs : 0 < s) {η : ℝ} (hη : 0 < η)
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    ∀ (pp : ℝ × ℝ), Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp → ∀ U : Set R3,
      U ∈ nhds (Work.BoxShrink.Pinch.par ψ pp) →
      ∃ D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U,
        D.p = pp ∧ D.r < 1 / 4 ∧ D.a' * D.κ < D.r ∧ D.a' < η ∧
        ContDiff ℝ (⊤ : ℕ∞) D.χ ∧ (∀ t : ℝ, |t| ≤ 1 / 2 → D.χ t = 1) ∧
        (∀ p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
          ‖Work.BoxShrink.Pinch.par ψ p' - D.centre‖ ≤ D.r →
          Work.BoxShrink.Pinch.par ψ p' = D.centre) ∧
        lam0 ≤ ℓ D.centre ∧ ℓ D.centre ≤ lam1 ∧
        lam0 ≤ ℓ D.centre - D.a' * ℓ D.d ∧
        (ℓ D.centre - D.a' * ℓ D.d) ∉ (exc : Set ℝ) ∧
        (∀ q' : ℝ × ℝ,
          D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
          ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
          ¬ (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s ∧
            |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h)) ∧
        (∀ q' : ℝ × ℝ,
          D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
          ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
          Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
          |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
          fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠ 0 ∧
          (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h → ∀ t : ℝ,
            fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
              t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q') ∧
          (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s → ∀ t : ℝ,
            fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
              t • fderiv ℝ (fun q'' : ℝ × ℝ =>
                Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q')) := by
  classical
  intro pp hp U hU
  -- the window containing the event's level
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hexcwin⟩ := hDP.1.tilt
  have hEVmem : ℓ (Work.BoxShrink.Pinch.par ψ pp) ∈ (exc : Set ℝ) := eventValue_mem_exc hDP hp
  have hlevelmem : ℓ (Work.BoxShrink.Pinch.par ψ pp) ∈ Set.Icc lam0 lam1 :=
    ⟨le_of_lt (hexcwin _ hEVmem).1, le_of_lt (hexcwin _ hEVmem).2⟩
  have hlevellt : lam0 < ℓ (Work.BoxShrink.Pinch.par ψ pp) := (hexcwin _ hEVmem).1
  -- the isolation radius and the corner-free radius
  obtain ⟨r₁, hr₁, hisoEv⟩ := anyEvent_isolated hDP hp
  obtain ⟨δ₀, hδ₀, hcorner⟩ := exists_annulus_cornerFree hs hDP hp
  -- the shrunken neighbourhood
  set ρ' : ℝ := min r₁ (min δ₀ (1 / 2)) / 4 with hρ'def
  have hρ'pos : 0 < ρ' := by
    rw [hρ'def]
    exact div_pos (lt_min hr₁ (lt_min hδ₀ (by norm_num))) (by norm_num)
  have hρ'le_r₁ : ρ' ≤ r₁ := by
    rw [hρ'def]
    have h := min_le_left r₁ (min δ₀ (1 / 2))
    linarith
  have hρ'le_δ₀ : ρ' ≤ δ₀ := by
    rw [hρ'def]
    have h := min_le_right r₁ (min δ₀ (1 / 2))
    have h2 := min_le_left δ₀ (1 / 2)
    linarith
  have hρ'lt : ρ' < 1 / 4 := by
    rw [hρ'def]
    have h := min_le_right r₁ (min δ₀ (1 / 2))
    have h2 := min_le_right δ₀ (1 / 2)
    linarith
  have hρ'le_min : ρ' ≤ min r₁ δ₀ := le_min hρ'le_r₁ hρ'le_δ₀
  set U' : Set R3 := U ∩ Metric.ball (Work.BoxShrink.Pinch.par ψ pp) ρ' with hU'def
  have hU'sub : U' ⊆ U := fun z hz => hz.1
  have hU' : U' ∈ nhds (Work.BoxShrink.Pinch.par ψ pp) :=
    Filter.inter_mem hU (Metric.ball_mem_nhds _ hρ'pos)
  -- the gap from the event's level to the rest of the exceptional set
  set Dst : Finset ℝ := (exc.erase (ℓ (Work.BoxShrink.Pinch.par ψ pp))).image
      (fun t => |t - ℓ (Work.BoxShrink.Pinch.par ψ pp)|) with hDstdef
  have hDst_pos : ∀ x ∈ Dst, 0 < x := by
    intro x hx
    rw [hDstdef] at hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have hne : t ≠ ℓ (Work.BoxShrink.Pinch.par ψ pp) := (Finset.mem_erase.mp ht).1
    rw [abs_pos]
    exact sub_ne_zero.mpr hne
  set gap : ℝ := if h : Dst.Nonempty then Dst.min' h else 1 with hgapdef
  have hgap_pos : 0 < gap := by
    rw [hgapdef]
    split_ifs with h
    · exact hDst_pos _ (Finset.min'_mem _ h)
    · norm_num
  have hgap_le : ∀ t ∈ exc, t ≠ ℓ (Work.BoxShrink.Pinch.par ψ pp) →
      gap ≤ |t - ℓ (Work.BoxShrink.Pinch.par ψ pp)| := by
    intro t ht hne
    have hmem : |t - ℓ (Work.BoxShrink.Pinch.par ψ pp)| ∈ Dst := by
      rw [hDstdef]
      exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨hne, ht⟩, rfl⟩
    rw [hgapdef]
    split_ifs with h
    · exact Finset.min'_le _ _ hmem
    · exact absurd ⟨_, hmem⟩ h
  -- the margin constants at a radius
  have hmargExists : ∀ r : ℝ, 0 < r → r ≤ min r₁ δ₀ →
      ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
        (∀ q' : ℝ × ℝ,
          r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ →
          ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ r →
          Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
          |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
          ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q'‖ ≤ M ∧
          ‖fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q'‖ ≤ M ∧
          m ≤ ‖fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q'‖ ∧
          (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h →
            m ≤ |Work.Drive.Final.det2 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q')
                     (fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q')|) ∧
          (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s →
            ‖fderiv ℝ (fun q'' : ℝ × ℝ =>
                Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q'‖ ≤ M ∧
            m ≤ |Work.Drive.Final.det2 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q')
                     (fderiv ℝ (fun q'' : ℝ × ℝ =>
                        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q')|)) := by
    intro r hr hrle
    have hrr : r ≤ r₁ := le_trans hrle (min_le_left _ _)
    have hslack : ∀ q' : ℝ × ℝ,
        r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ →
        ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ r →
        ¬ (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s ∧
          |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h) := by
      intro q' h1 h2
      exact hcorner q' (by linarith) (le_trans h2 (le_trans hrle (min_le_right _ _)))
    obtain ⟨m, hm, M, hM, hprop⟩ := dent_annulus_margin hDP hp hr₁ hisoEv hr hrr hslack
    exact ⟨m, M, hm, hM, hprop⟩
  let margOf : ℝ → ℝ × ℝ := fun r =>
    if h : 0 < r ∧ r ≤ min r₁ δ₀ then
      (Classical.choose (hmargExists r h.1 h.2),
       Classical.choose (Classical.choose_spec (hmargExists r h.1 h.2)))
    else (1, 1)
  have hmargOf_pos : ∀ r : ℝ, 0 < (margOf r).1 ∧ 0 < (margOf r).2 := by
    intro r
    dsimp only [margOf]
    split_ifs with h
    · exact ⟨(Classical.choose_spec (Classical.choose_spec (hmargExists r h.1 h.2))).1,
             (Classical.choose_spec (Classical.choose_spec (hmargExists r h.1 h.2))).2.1⟩
    · norm_num
  have hmargOf_spec : ∀ r : ℝ, 0 < r → r ≤ min r₁ δ₀ →
      0 < (margOf r).1 ∧ 0 < (margOf r).2 ∧
        (∀ q' : ℝ × ℝ,
          r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ →
          ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ r →
          Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
          |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
          ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q'‖ ≤ (margOf r).2 ∧
          ‖fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q'‖ ≤ (margOf r).2 ∧
          (margOf r).1 ≤ ‖fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q'‖ ∧
          (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h →
            (margOf r).1 ≤ |Work.Drive.Final.det2
                     (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q')
                     (fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q')|) ∧
          (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s →
            ‖fderiv ℝ (fun q'' : ℝ × ℝ =>
                Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q'‖ ≤ (margOf r).2 ∧
            (margOf r).1 ≤ |Work.Drive.Final.det2
                     (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q')
                     (fderiv ℝ (fun q'' : ℝ × ℝ =>
                        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q')|)) := by
    intro r hr hrle
    have heq : margOf r = (Classical.choose (hmargExists r hr hrle),
        Classical.choose (Classical.choose_spec (hmargExists r hr hrle))) := by
      dsimp only [margOf]
      rw [dif_pos ⟨hr, hrle⟩]
    have hspec := Classical.choose_spec (Classical.choose_spec (hmargExists r hr hrle))
    rw [heq]
    exact ⟨hspec.1, hspec.2.1, hspec.2.2⟩
  -- the depth function
  let A : ℝ → ℝ → ℝ := fun r κ =>
    min (η / 2)
      (min (r / (2 * κ)) (min ((ℓ (Work.BoxShrink.Pinch.par ψ pp) - lam0) / (2 * ‖ℓ‖ + 2))
        (min (gap / (2 * ‖ℓ‖ + 2))
          ((margOf r).1 * r / (4 * (‖ℓ‖ + 1) * κ * (margOf r).2 *
            (1 + 2 * (margOf r).2))))))
  have hA : ∀ r κ : ℝ, 0 < r → 0 < κ → 0 < A r κ := by
    intro r κ hr hrκ
    have h1 : 0 < r / (2 * κ) := div_pos hr (by linarith)
    have h2 : 0 < (ℓ (Work.BoxShrink.Pinch.par ψ pp) - lam0) / (2 * ‖ℓ‖ + 2) :=
      div_pos (by linarith [hlevellt]) (by positivity)
    have h3 : 0 < gap / (2 * ‖ℓ‖ + 2) := div_pos hgap_pos (by positivity)
    have h4 : 0 < (margOf r).1 * r / (4 * (‖ℓ‖ + 1) * κ * (margOf r).2 *
        (1 + 2 * (margOf r).2)) :=
      div_pos (mul_pos (hmargOf_pos r).1 hr)
        (by have := (hmargOf_pos r).2; positivity)
    have h0 : 0 < η / 2 := by linarith
    dsimp only [A]
    exact lt_min h0 (lt_min h1 (lt_min h2 (lt_min h3 h4)))
  -- the produced datum over `U'`
  obtain ⟨D', hD'p, hD'a', hD'χ, hD'χ1⟩ :=
    anyDentData_exists_depthFn hDP.2.1 hp hU' A hA
  -- the same datum, read over `U`
  let D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U :=
    { D' with ball_sub := fun z hz => hU'sub (D'.ball_sub z hz) }
  have hDp : D.p = pp := hD'p
  have hcentre : D.centre = Work.BoxShrink.Pinch.par ψ pp := by
    have h1 : D.centre = Work.BoxShrink.Pinch.par ψ D.p := D.centre_eq
    rw [h1, show D.p = pp from hD'p]
  -- the radius is strictly below the shrunken radius
  have hDr_lt_ρ' : D.r < ρ' := by
    set u1 : R3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hu1def
    have hu1norm : ‖u1‖ = 1 := by
      rw [hu1def]; simp
    set z : R3 := D.centre + (D.r + D.δ) • u1 with hzdef
    have hδRpos : 0 < D.r + D.δ := by linarith [D.r_pos, D.δ_pos]
    have hz : ‖z - D.centre‖ ≤ D.r + D.δ := by
      have hsub : z - D.centre = (D.r + D.δ) • u1 := by rw [hzdef]; abel
      rw [hsub, norm_smul, hu1norm, mul_one, Real.norm_eq_abs, abs_of_pos hδRpos]
    have hzU' : z ∈ U' := D'.ball_sub z hz
    rw [hU'def] at hzU'
    have hzball : z ∈ Metric.ball (Work.BoxShrink.Pinch.par ψ pp) ρ' := hzU'.2
    rw [Metric.mem_ball, dist_eq_norm] at hzball
    have hsub2 : z - Work.BoxShrink.Pinch.par ψ pp = (D.r + D.δ) • u1 := by
      rw [hzdef, hcentre]; abel
    rw [hsub2, norm_smul, hu1norm, mul_one, Real.norm_eq_abs, abs_of_pos hδRpos] at hzball
    linarith [hzball, D.δ_pos]
  have hDr_le_r₁ : D.r ≤ r₁ := le_trans (le_of_lt hDr_lt_ρ') hρ'le_r₁
  have hDr_le_min : D.r ≤ min r₁ δ₀ := le_trans (le_of_lt hDr_lt_ρ') hρ'le_min
  have hDr_lt_δ₀ : D.r < δ₀ := lt_of_lt_of_le hDr_lt_ρ' hρ'le_δ₀
  -- the four terms of `A` at the datum's radius
  have hA0 : A D.r D.κ ≤ η / 2 := by
    dsimp only [A]; exact min_le_left _ _
  have hA1 : A D.r D.κ ≤ D.r / (2 * D.κ) := by
    dsimp only [A]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hA2 : A D.r D.κ ≤ (ℓ (Work.BoxShrink.Pinch.par ψ pp) - lam0) / (2 * ‖ℓ‖ + 2) := by
    dsimp only [A]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hA3 : A D.r D.κ ≤ gap / (2 * ‖ℓ‖ + 2) := by
    dsimp only [A]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hA4 : A D.r D.κ ≤ (margOf D.r).1 * D.r / (4 * (‖ℓ‖ + 1) * D.κ * (margOf D.r).2 *
      (1 + 2 * (margOf D.r).2)) := by
    dsimp only [A]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- the norm of `ℓ` dominates `ℓ D.d`
  have hℓd_le : ℓ D.d ≤ ‖ℓ‖ := by
    have h1 : ‖ℓ D.d‖ ≤ ‖ℓ‖ * ‖D.d‖ := ℓ.le_opNorm D.d
    rw [D.d_norm, mul_one] at h1
    calc ℓ D.d ≤ |ℓ D.d| := le_abs_self _
      _ = ‖ℓ D.d‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ := h1
  -- the margin data at the datum's radius
  obtain ⟨hmpos, hMpos, hmargin⟩ := hmargOf_spec D.r D.r_pos hDr_le_min
  have hmarginD : ∀ q : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ q ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q)| ≤ h →
      ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q‖ ≤ (margOf D.r).2 ∧
      ‖fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q‖ ≤ (margOf D.r).2 ∧
      (margOf D.r).1 ≤ ‖fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q‖ ∧
      (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q)| = h →
        (margOf D.r).1 ≤ |Work.Drive.Final.det2
                 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q)
                 (fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q)|) ∧
      (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) = s →
        ‖fderiv ℝ (fun q' : ℝ × ℝ =>
            Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q‖ ≤ (margOf D.r).2 ∧
        (margOf D.r).1 ≤ |Work.Drive.Final.det2
                 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q)
                 (fderiv ℝ (fun q' : ℝ × ℝ =>
                    Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q')) q)|) := by
    intro q h1 h2 h3 h4
    rw [hcentre] at h1 h2
    exact hmargin q h1 h2 h3 h4
  refine ⟨D, ?hpt, ?hr, ?hadepth, ?hadepthEta, ?hchiC, ?hchi1, ?hiso, ?hlamA, ?hlamB, ?hlev,
    ?hexc, ?hslack, ?hann⟩
  · exact hDp
  · exact lt_trans hDr_lt_ρ' hρ'lt
  · have hDa'_le1 : D.a' ≤ D.r / (2 * D.κ) := le_trans hD'a' hA1
    calc D.a' * D.κ ≤ (D.r / (2 * D.κ)) * D.κ :=
          mul_le_mul_of_nonneg_right hDa'_le1 (le_of_lt D.κ_pos)
      _ = D.r / 2 := by
            rw [div_mul_eq_mul_div, mul_comm D.r D.κ, mul_comm (2 : ℝ) D.κ,
              mul_div_mul_left D.r 2 (ne_of_gt D.κ_pos)]
      _ < D.r := by linarith [D.r_pos]
  · have hDa'_leη : D.a' ≤ η / 2 := le_trans hD'a' hA0
    linarith
  · exact hD'χ
  · exact hD'χ1
  · intro p' hp' hdist
    rw [hcentre] at hdist ⊢
    exact hisoEv p' hp' (le_trans hdist hDr_le_r₁)
  · rw [hcentre]; exact hlevelmem.1
  · rw [hcentre]; exact hlevelmem.2
  · have hDa'_le2 : D.a' ≤ (ℓ (Work.BoxShrink.Pinch.par ψ pp) - lam0) / (2 * ‖ℓ‖ + 2) :=
      le_trans hD'a' hA2
    have hden : 0 < 2 * ‖ℓ‖ + 2 := by positivity
    have h1 : D.a' * (2 * ‖ℓ‖ + 2) ≤ ℓ (Work.BoxShrink.Pinch.par ψ pp) - lam0 := by
      have h := mul_le_mul_of_nonneg_right hDa'_le2 (le_of_lt hden)
      rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at h
    have hDa'ℓ : D.a' * ‖ℓ‖ ≤ (ℓ (Work.BoxShrink.Pinch.par ψ pp) - lam0) / 2 := by
      nlinarith [h1, D.a'_pos, norm_nonneg ℓ]
    have ha'ld_le : D.a' * ℓ D.d ≤ (ℓ (Work.BoxShrink.Pinch.par ψ pp) - lam0) / 2 := by
      have h := mul_le_mul_of_nonneg_left hℓd_le (le_of_lt D.a'_pos)
      linarith [hDa'ℓ, h]
    rw [hcentre]
    linarith [ha'ld_le, hlevellt]
  · intro hmem
    have ha'ld_pos : 0 < D.a' * ℓ D.d := mul_pos D.a'_pos D.push_pos
    have hgap_half : D.a' * ℓ D.d ≤ gap / 2 := by
      have hDa'_le3 : D.a' ≤ gap / (2 * ‖ℓ‖ + 2) := le_trans hD'a' hA3
      have hden : 0 < 2 * ‖ℓ‖ + 2 := by positivity
      have h1 : D.a' * (2 * ‖ℓ‖ + 2) ≤ gap := by
        have h := mul_le_mul_of_nonneg_right hDa'_le3 (le_of_lt hden)
        rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at h
      have h := mul_le_mul_of_nonneg_left hℓd_le (le_of_lt D.a'_pos)
      nlinarith [h1, h, D.a'_pos, norm_nonneg ℓ]
    have hℓcentre : ℓ D.centre = ℓ (Work.BoxShrink.Pinch.par ψ pp) := by rw [hcentre]
    by_cases hEq : ℓ D.centre - D.a' * ℓ D.d = ℓ (Work.BoxShrink.Pinch.par ψ pp)
    · rw [hℓcentre] at hEq
      have hzero : D.a' * ℓ D.d = 0 := by linarith
      linarith [ha'ld_pos, hzero]
    · have hgaple := hgap_le _ hmem hEq
      have habs : |(ℓ D.centre - D.a' * ℓ D.d) - ℓ (Work.BoxShrink.Pinch.par ψ pp)| =
          D.a' * ℓ D.d := by
        have h : (ℓ D.centre - D.a' * ℓ D.d) - ℓ (Work.BoxShrink.Pinch.par ψ pp) =
            -(D.a' * ℓ D.d) := by rw [hℓcentre]; ring
        rw [h, abs_neg, abs_of_pos ha'ld_pos]
      rw [habs] at hgaple
      linarith [hgaple, hgap_half, hgap_pos]
  · intro q' h1 h2
    rw [hcentre] at h1 h2
    exact hcorner q' (by linarith [h1, D.r_pos]) (le_trans h2 (le_of_lt hDr_lt_δ₀))
  · intro q' h1 h2 h3 h4
    have ha : D.a' * ‖ℓ‖ * (D.κ / D.r) * (margOf D.r).2 * (1 + 2 * (margOf D.r).2) <
        (margOf D.r).1 / 2 := by
      have hDa'_le4 : D.a' ≤ (margOf D.r).1 * D.r /
          (4 * (‖ℓ‖ + 1) * D.κ * (margOf D.r).2 * (1 + 2 * (margOf D.r).2)) :=
        le_trans hD'a' hA4
      have hkey : ((margOf D.r).1 * D.r /
            (4 * (‖ℓ‖ + 1) * D.κ * (margOf D.r).2 * (1 + 2 * (margOf D.r).2))) *
            (‖ℓ‖ * (D.κ / D.r) * (margOf D.r).2 * (1 + 2 * (margOf D.r).2)) =
          (margOf D.r).1 * ‖ℓ‖ / (4 * (‖ℓ‖ + 1)) := by
        have hκ' : D.κ ≠ 0 := ne_of_gt D.κ_pos
        have hr' : D.r ≠ 0 := ne_of_gt D.r_pos
        have hM' : (margOf D.r).2 ≠ 0 := ne_of_gt hMpos
        have hM2' : (1 + 2 * (margOf D.r).2) ≠ 0 := by linarith
        field_simp
        try ring
      have hnn : 0 ≤ ‖ℓ‖ * (D.κ / D.r) * (margOf D.r).2 * (1 + 2 * (margOf D.r).2) :=
        mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg ℓ)
          (div_pos D.κ_pos D.r_pos).le) hMpos.le) (by linarith [hMpos])
      have hstep1 : D.a' * ‖ℓ‖ * (D.κ / D.r) * (margOf D.r).2 * (1 + 2 * (margOf D.r).2) ≤
          (margOf D.r).1 * ‖ℓ‖ / (4 * (‖ℓ‖ + 1)) := by
        calc D.a' * ‖ℓ‖ * (D.κ / D.r) * (margOf D.r).2 * (1 + 2 * (margOf D.r).2)
            = D.a' * (‖ℓ‖ * (D.κ / D.r) * (margOf D.r).2 * (1 + 2 * (margOf D.r).2)) := by
              ring
          _ ≤ ((margOf D.r).1 * D.r / (4 * (‖ℓ‖ + 1) * D.κ * (margOf D.r).2 *
                (1 + 2 * (margOf D.r).2))) *
              (‖ℓ‖ * (D.κ / D.r) * (margOf D.r).2 * (1 + 2 * (margOf D.r).2)) :=
                mul_le_mul_of_nonneg_right hDa'_le4 hnn
          _ = (margOf D.r).1 * ‖ℓ‖ / (4 * (‖ℓ‖ + 1)) := hkey
      have hstep2 : (margOf D.r).1 * ‖ℓ‖ / (4 * (‖ℓ‖ + 1)) ≤ (margOf D.r).1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hmpos, norm_nonneg ℓ]
      linarith [hstep1, hstep2, hmpos]
    exact dent_annulus_regular D hmpos hMpos hmarginD (hD'χ.of_le (by simp)) hD'χ1 ha h1 h2 h3 h4

end

end Work.Drive.Final
