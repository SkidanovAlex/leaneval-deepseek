import Mathlib
import Submission.Work.OddRadon.RadialDefs
import Submission.Work.OddRadon.RadialSystemAux
import Submission.Work.OddRadon.RadialSystemC1Lemmas

/-!
# Existence of the radial pair with `C¹` control (`Work.OddRadon`)

The odd-dimensional step of the paper needs, for every sufficiently small smooth perturbation
`(A,B)` of the ball's data, a pair of radial functions `(R,r)` solving the two-power system

  `(R^{d+1} + r^{d+1}) cos²α = (2 + A α) cos²α`,   `(R^d - r^d) cos α = B α cos α`

with `R(π/2) = r(π/2) = 1` and, in addition to closeness of `R, r` to `1`, a bound on the
derivatives of `R, r`.

The subtle point is that `A` and `B` are only smooth on `[0,π/2]`: the values of `R, r` on the
interval are determined by the local inverse of the two-power map, but the two-sided derivative of
`R = radialLocalInv n (2 + A, B)` at an endpoint of the interval depends on the behaviour of
`A, B` outside the interval, which is unconstrained.  We therefore replace `A, B` by the piecewise
affine extensions `radialExtensionOf A`, `radialExtensionOf B` whose slopes at `0` and `π/2` are
the one-sided derivatives of `A, B` there, and build `R, r` from those extensions.  On
`[0,π/2]` the extension agrees with the original data, so the equations still hold with the
original `(A,B)`.
-/

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

theorem radialSystem_exists_C1 (n : ℕ) (hn : 1 ≤ n) :
    ∃ ε > 0, ∀ A B : ℝ → ℝ,
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Icc 0 (Real.pi / 2)) →
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B (Set.Icc 0 (Real.pi / 2)) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |A α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |B α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv A α| < ε) →
      (∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv B α| < ε) →
      A (Real.pi / 2) = 0 → B (Real.pi / 2) = 0 →
      deriv A 0 = 0 → deriv B 0 = 0 →
      ∃ R r : ℝ → ℝ,
        ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R (Set.Icc 0 (Real.pi / 2)) ∧
        ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r (Set.Icc 0 (Real.pi / 2)) ∧
        RadialSystem n (fun α => (2 + A α) * Real.cos α ^ 2)
          (fun α => B α * Real.cos α) R r ∧
        R (Real.pi / 2) = 1 ∧ r (Real.pi / 2) = 1 ∧
        (∀ α ∈ Set.Icc 0 (Real.pi / 2),
          |R α - 1| < 1 / 4 ∧ |r α - 1| < 1 / 4 ∧
          |deriv R α| < 1 / 4 ∧ |deriv r α| < 1 / 4) := by
  obtain ⟨δ, hδpos, C, hCpos, u, huopen, hup0, hδu, hucont, hprops⟩ :=
    radialLocalInv_ball_data n
  set ε : ℝ := min δ (1 / (8 * C)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min hδpos (by positivity)
  have hεδ : ε ≤ δ := by rw [hεdef]; exact min_le_left _ _
  have hεC : ε ≤ 1 / (8 * C) := by rw [hεdef]; exact min_le_right _ _
  have hCeps : C * ε < 1 / 4 := by
    have h1 : C * ε ≤ C * (1 / (8 * C)) :=
      mul_le_mul_of_nonneg_left hεC (le_of_lt hCpos)
    have h2 : C * (1 / (8 * C)) = 1 / 8 := by field_simp
    linarith
  refine ⟨ε, hεpos, ?_⟩
  set s : Set ℝ := Set.Icc 0 (Real.pi / 2) with hs
  intro A B hA hB hAε hBε hA'ε hB'ε hAend hBend hA0 hB0
  have hpi : (0:ℝ) < Real.pi / 2 := by positivity
  have h0s : (0:ℝ) ∈ s := ⟨le_refl 0, le_of_lt hpi⟩
  have hpis : (Real.pi / 2) ∈ s := ⟨le_of_lt hpi, le_refl _⟩
  have hlevel : (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by simp
  set p0 : ℝ × ℝ := Commons.Geometry.Ulam.radialMap n (1, 1) with hp0
  set G : ℝ × ℝ → ℝ × ℝ := Commons.Geometry.Ulam.radialLocalInv n with hG
  set y : ℝ → ℝ × ℝ := fun x => (2 + A x, B x) with hy
  set Atil : ℝ → ℝ := radialExtensionOf A with hAtil
  set Btil : ℝ → ℝ := radialExtensionOf B with hBtil
  set ytil : ℝ → ℝ × ℝ := fun x => (2 + Atil x, Btil x) with hytil
  have haytil : ∀ x ∈ s, Atil x = A x := by
    intro x hx; rw [hAtil]; exact radialExtensionOf_eqOn A x hx
  have hbytil : ∀ x ∈ s, Btil x = B x := by
    intro x hx; rw [hBtil]; exact radialExtensionOf_eqOn B x hx
  have hy_eq : ∀ x ∈ s, ytil x = y x := by
    intro x hx
    simp only [hytil, hy, haytil x hx, hbytil x hx]
  -- the data on the interval lies in the small ball
  have hyball : ∀ α ∈ s, y α ∈ Metric.ball p0 δ := by
    intro α hα
    have hmax : max |A α| |B α| < ε := max_lt (hAε α hα) (hBε α hα)
    rw [Metric.mem_ball, hy, hp0, dist_radialMap_pair]
    exact lt_of_lt_of_le hmax hεδ
  have hytilball : ∀ α ∈ s, ytil α ∈ Metric.ball p0 δ := by
    intro α hα; rw [hy_eq α hα]; exact hyball α hα
  -- smoothness
  have hycont : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) y s := by
    rw [hy]
    exact (contDiffOn_const.add hA).prodMk hB
  have hymaps : Set.MapsTo y s u := fun α hα => hδu (hyball α hα)
  have hcomp : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun x => G (y x)) s :=
    hucont.comp hycont hymaps
  have hRcont : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun x => (G (ytil x)).1) s := by
    refine hcomp.fst.congr (fun x hx => ?_)
    rw [hy_eq x hx]
  have hrcont : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun x => (G (ytil x)).2) s := by
    refine hcomp.snd.congr (fun x hx => ?_)
    rw [hy_eq x hx]
  -- the system
  have hsys : RadialSystem n (fun α => (2 + A α) * Real.cos α ^ 2)
      (fun α => B α * Real.cos α) (fun x => (G (ytil x)).1) (fun x => (G (ytil x)).2) := by
    intro α hα
    have hmem : Commons.Geometry.Ulam.radialMap n (G (y α)) = y α :=
      (hprops (y α) (hyball α hα)).2.1
    have h1 : (G (y α)).1 ^ (2 * n + 2) + (G (y α)).2 ^ (2 * n + 2) = 2 + A α := by
      have h := congrArg Prod.fst hmem
      simpa only [Commons.Geometry.Ulam.radialMap, hy] using h
    have h2 : (G (y α)).1 ^ (2 * n + 1) - (G (y α)).2 ^ (2 * n + 1) = B α := by
      have h := congrArg Prod.snd hmem
      simpa only [Commons.Geometry.Ulam.radialMap, hy] using h
    simp only [hy_eq α hα]
    exact ⟨by rw [h1], by rw [h2]⟩
  -- values at the right endpoint
  have hyend : ytil (Real.pi / 2) = p0 := by
    rw [hytil, hp0, Commons.Geometry.Ulam.radialMap]
    simp only [haytil _ hpis, hbytil _ hpis, hAend, hBend]
    norm_num
  have hRend : (G (ytil (Real.pi / 2))).1 = 1 := by
    rw [hyend, hG, Commons.Geometry.Ulam.radialLocalInv_apply_image n]
  have hrend : (G (ytil (Real.pi / 2))).2 = 1 := by
    rw [hyend, hG, Commons.Geometry.Ulam.radialLocalInv_apply_image n]
  -- closeness of the values
  have hval : ∀ z ∈ s, |(G (ytil z)).1 - 1| < 1 / 4 ∧ |(G (ytil z)).2 - 1| < 1 / 4 := by
    intro z hz
    have hmem : G (y z) ∈ Metric.ball (1, 1) (1 / 4) := (hprops (y z) (hyball z hz)).1
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hmem
    rw [hy_eq z hz]
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hmem, lt_of_le_of_lt (le_max_right _ _) hmem⟩
  -- derivative bounds
  have hGAt : ∀ w ∈ u, HasFDerivAt G (fderiv ℝ G w) w := fun w hw =>
    ((hucont.contDiffAt (huopen.mem_nhds hw)).differentiableAt hlevel).hasFDerivAt
  have hCbound : ∀ w ∈ Metric.ball p0 δ, ‖fderiv ℝ G w‖ ≤ C := fun w hw => (hprops w hw).2.2
  have hderivkey : ∀ z ∈ s, ∃ v : ℝ × ℝ, ‖v‖ ≤ C * ε ∧
      HasDerivAt (fun x => (G (ytil x)).1) v.1 z ∧
      HasDerivAt (fun x => (G (ytil x)).2) v.2 z := by
    intro z hz
    have hcomp_fst : ∀ v : ℝ × ℝ, HasDerivAt (G ∘ ytil) v z →
        HasDerivAt (fun x => (G (ytil x)).1) v.1 z := fun v hv => by
      simpa using hv.hasFDerivAt.fst.hasDerivAt
    have hcomp_snd : ∀ v : ℝ × ℝ, HasDerivAt (G ∘ ytil) v z →
        HasDerivAt (fun x => (G (ytil x)).2) v.2 z := fun v hv => by
      simpa using hv.hasFDerivAt.snd.hasDerivAt
    by_cases h0 : z = 0
    · subst h0
      have hAext := radialExtensionOf_hasDerivAt A ε hA hA'ε
      have hBext := radialExtensionOf_hasDerivAt B ε hB hB'ε
      have hytil0 : HasDerivAt ytil (derivWithin A s 0, derivWithin B s 0) 0 := by
        rw [hytil]
        exact (hAext.1.const_add 2).prodMk hBext.1
      have hmem0 : ytil 0 ∈ Metric.ball p0 δ := by rw [hy_eq 0 h0s]; exact hyball 0 h0s
      refine ⟨(fderiv ℝ G (ytil 0)) (derivWithin A s 0, derivWithin B s 0), ?_,
        hcomp_fst _ ((hGAt (ytil 0) (hδu hmem0)).comp_hasDerivAt 0 hytil0),
        hcomp_snd _ ((hGAt (ytil 0) (hδu hmem0)).comp_hasDerivAt 0 hytil0)⟩
      calc ‖(fderiv ℝ G (ytil 0)) (derivWithin A s 0, derivWithin B s 0)‖
          ≤ ‖fderiv ℝ G (ytil 0)‖ * ‖(derivWithin A s 0, derivWithin B s 0)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ε := by
            refine mul_le_mul (hCbound _ hmem0) ?_ (norm_nonneg _) (le_of_lt hCpos)
            rw [Prod.norm_def]
            refine max_le ?_ ?_
            · rw [Real.norm_eq_abs]; exact hAext.2.1
            · rw [Real.norm_eq_abs]; exact hBext.2.1
    · by_cases h1 : z = Real.pi / 2
      · subst h1
        have hAext := radialExtensionOf_hasDerivAt A ε hA hA'ε
        have hBext := radialExtensionOf_hasDerivAt B ε hB hB'ε
        have hytil1 : HasDerivAt ytil
            (derivWithin A s (Real.pi / 2), derivWithin B s (Real.pi / 2)) (Real.pi / 2) := by
          rw [hytil]
          exact (hAext.2.2.1.const_add 2).prodMk hBext.2.2.1
        have hmem1 : ytil (Real.pi / 2) ∈ Metric.ball p0 δ := by
          rw [hy_eq _ hpis]; exact hyball _ hpis
        refine ⟨(fderiv ℝ G (ytil (Real.pi / 2)))
            (derivWithin A s (Real.pi / 2), derivWithin B s (Real.pi / 2)), ?_,
          hcomp_fst _ ((hGAt (ytil (Real.pi / 2)) (hδu hmem1)).comp_hasDerivAt (Real.pi / 2) hytil1),
          hcomp_snd _ ((hGAt (ytil (Real.pi / 2)) (hδu hmem1)).comp_hasDerivAt (Real.pi / 2) hytil1)⟩
        calc ‖(fderiv ℝ G (ytil (Real.pi / 2)))
              (derivWithin A s (Real.pi / 2), derivWithin B s (Real.pi / 2))‖
            ≤ ‖fderiv ℝ G (ytil (Real.pi / 2))‖ *
                ‖(derivWithin A s (Real.pi / 2), derivWithin B s (Real.pi / 2))‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ε := by
              refine mul_le_mul (hCbound _ hmem1) ?_ (norm_nonneg _) (le_of_lt hCpos)
              rw [Prod.norm_def]
              refine max_le ?_ ?_
              · rw [Real.norm_eq_abs]; exact hAext.2.2.2
              · rw [Real.norm_eq_abs]; exact hBext.2.2.2
      · -- interior point
        have hsnhds : s ∈ 𝓝 z :=
          Icc_mem_nhds (lt_of_le_of_ne hz.1 (Ne.symm h0)) (lt_of_le_of_ne hz.2 h1)
        have hAat : HasDerivAt A (deriv A z) z :=
          ((hA.contDiffAt hsnhds).differentiableAt hlevel).hasDerivAt
        have hBat : HasDerivAt B (deriv B z) z :=
          ((hB.contDiffAt hsnhds).differentiableAt hlevel).hasDerivAt
        have hyat : HasDerivAt y (deriv A z, deriv B z) z := by
          rw [hy]
          exact (hAat.const_add 2).prodMk hBat
        have hGcomp : HasDerivAt (G ∘ y) ((fderiv ℝ G (y z)) (deriv A z, deriv B z)) z :=
          (hGAt (y z) (hδu (hyball z hz))).comp_hasDerivAt z hyat
        have hev : (G ∘ ytil) =ᶠ[𝓝 z] (G ∘ y) := by
          filter_upwards [hsnhds] with x hx
          simp only [Function.comp_apply, hy_eq x hx]
        refine ⟨(fderiv ℝ G (y z)) (deriv A z, deriv B z), ?_,
          hcomp_fst _ (hGcomp.congr_of_eventuallyEq hev),
          hcomp_snd _ (hGcomp.congr_of_eventuallyEq hev)⟩
        calc ‖(fderiv ℝ G (y z)) (deriv A z, deriv B z)‖
            ≤ ‖fderiv ℝ G (y z)‖ * ‖(deriv A z, deriv B z)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ε := by
              refine mul_le_mul (hCbound _ (hyball z hz)) ?_ (norm_nonneg _) (le_of_lt hCpos)
              rw [Prod.norm_def]
              refine max_le ?_ ?_
              · rw [Real.norm_eq_abs]; exact le_of_lt (hA'ε z hz)
              · rw [Real.norm_eq_abs]; exact le_of_lt (hB'ε z hz)
  refine ⟨fun x => (G (ytil x)).1, fun x => (G (ytil x)).2, hRcont, hrcont, hsys, hRend, hrend, ?_⟩
  intro z hz
  obtain ⟨v, hvC, hv1, hv2⟩ := hderivkey z hz
  obtain ⟨hv11, hv12⟩ := hval z hz
  refine ⟨hv11, hv12, ?_, ?_⟩
  · rw [hv1.deriv]
    exact lt_of_le_of_lt (le_trans (by rw [← Real.norm_eq_abs]; exact norm_fst_le v) hvC) hCeps
  · rw [hv2.deriv]
    exact lt_of_le_of_lt (le_trans (by rw [← Real.norm_eq_abs]; exact norm_snd_le v) hvC) hCeps

end Work.OddRadon
