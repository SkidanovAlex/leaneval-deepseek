import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Smooth.Morse.Immersion.isImmersion
import Submission.Work.Drive.EpsForm.exists_unit_orthogonal_close_strict
import Submission.Work.Drive.EpsForm.tiltVector_of_small_angle
import Submission.Work.Drive.EpsForm.goodHeight_exists

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## Helpers for `tiltedSweepGenericity_holds_sized` -/

/-- **A unit vector orthogonal to the slab direction `shiftVσ σ 1`.**  This is the anchor point of
the ball in which the good height direction is sought (the good direction is nearly orthogonal to
`shiftVσ σ 1`, which is what the tilt of the slab requires). -/
theorem exists_unit_orthogonal_shiftVσ (σ : Equiv.Perm (Fin 3)) :
    ∃ n₀ : R3, ‖n₀‖ = 1 ∧ inner ℝ n₀ (Work.BoxShrink.shiftVσ σ 1) = 0 := by
  refine ⟨EuclideanSpace.single (σ 0) (1 : ℝ), ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq]
    have h : ∀ i : Fin 3,
        ‖(EuclideanSpace.single (σ 0) (1 : ℝ)).ofLp i‖ ^ 2 = if i = σ 0 then 1 else 0 := by
      intro i
      rw [EuclideanSpace.single_apply]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simp
  · rw [EuclideanSpace.inner_single_left, Work.BoxShrink.shiftVσ_apply]
    have hne : σ 0 ≠ σ 2 := by
      intro h
      exact absurd (σ.injective h) (by decide)
    simp [hne]

/-- **The Morse form of `ae_height_morse` as injectivity of the Hessian.** -/
theorem injective_fderiv_fderiv_of_forall {Φ : ℝ × ℝ → R3} {n : R3}
    (h : ∀ p : ℝ × ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Φ q)) p = 0 →
      ∀ w : ℝ × ℝ, (∀ w' : ℝ × ℝ,
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Φ q))) p) w w' = 0) → w = 0) :
    ∀ p : ℝ × ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Φ q)) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Φ q))) p) := by
  intro p hp a b hab
  have h0 : (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Φ q))) p) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h1 : ∀ w' : ℝ × ℝ,
      (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Φ q))) p) (a - b) w' = 0 := by
    intro w'
    rw [h0]
    rfl
  exact sub_eq_zero.mp (h p hp (a - b) h1)

/-- **A bound for the box.**  Every point of `PBox s c σ` is within `R` of the centre `c`. -/
theorem boxBound (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R := by
  by_cases hs : 0 ≤ s
  · refine ⟨5 / 2 * s, by linarith, fun y hy => ?_⟩
    have h := Submission.PBox_subset_ball s hs c σ hy
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact le_of_lt h
  · refine ⟨0, le_refl 0, fun y hy => ?_⟩
    exfalso
    have h := hy 0
    simp only [Submission.boxSide_zero] at h
    have h2 := Submission.boxSide_pos 0
    linarith [abs_nonneg (y (σ 0) - c (σ 0))]

/-- **P1 of the tilted sweep, strengthened with the two clauses the consumers need.**

For every `ε > 0` (the consumer instantiates it at the box-shrink margin, which tends to `0` as the
box shrinks, so it cannot be the fixed `Submission.eps`) and every configuration, there are a unit
direction `v` across the slab within `ε` of the `σ 2` direction, a bound `R` for the box
(`‖y - c‖ ≤ R` on `PBox s c σ`), a slab half-width `h` larger than `ε·R` (the tilted endgame needs a
definite side of the untitled cutting plane, see `Drive/EpsForm/sweepThrough.lean`), a functional `ℓ`
vanishing on `v` but nonzero, and a finite set `exc` of levels such that

  (i) away from `exc` the wall `{ℓ = ·}` meets the surface transversally at every surface point of the
      box inside the closed slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` (interior regularity, P2's `hreg`);
  (ii) away from `exc` the sweep height is also regular **on the two slab faces**
      `|⟪v,·⟫ - (⟪v,c⟫ + u)| = h`: there the differential of the height is not parallel to the
      differential of the face function (P2's `hface`, mandatory after the machine-checked
      counterexample `WSCex.counterexample`; this clause folds the *boundary* critical values into
      `exc`, a boundary critical point not being an interior one);
  (iii) at every critical point of the sweep height inside the box and the slab, the height is
      nondegenerate in the parameter plane and its value lies in `exc`;
  (iv) two such critical points with the same value coincide (one handle per level, what P3
      consumes). -/
theorem tiltedSweepGenericity_holds_sized (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (R : ℝ),
      ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ ε ∧
      ℓ v = 0 ∧ ℓ ≠ 0 ∧
      (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧ ε * R < h ∧
      (∀ lam ∉ exc, ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) ∧
      (∀ lam ∉ exc, ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
        ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) ∧
      (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
        Function.Injective (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ)) p) ∧
          ℓ (Work.BoxShrink.Pinch.par ψ p) ∈ exc) ∧
      (∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
        Work.BoxShrink.Pinch.par ψ p ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        Work.BoxShrink.Pinch.par ψ p' ∈
          Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' = 0 →
        ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
        Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') := by
  classical
  -- ## 0. the slab direction and the anchor direction
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have he1 : ‖e‖ = 1 := norm_shiftVσ_one σ
  obtain ⟨a₀, ha₀1, ha₀e⟩ := exists_unit_orthogonal_shiftVσ σ
  -- ## 1. the two radii
  set r₁ : ℝ := min (1 / 64) (ε / 128) with hr₁
  have hr₁pos : 0 < r₁ := by rw [hr₁]; exact lt_min (by norm_num) (by positivity)
  have hr₁le : r₁ ≤ ε / 128 := by rw [hr₁]; exact min_le_right _ _
  set r₂ : ℝ := min r₁ (ε / 128) with hr₂
  have hr₂pos : 0 < r₂ := by rw [hr₂]; exact lt_min hr₁pos (by positivity)
  have hr₂le : r₂ ≤ r₁ := by rw [hr₂]; exact min_le_left _ _
  have hr₂le' : r₂ ≤ ε / 128 := by rw [hr₂]; exact min_le_right _ _
  -- ## 2. a Morse direction near the anchor
  have hΦ3 : ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) :=
    (Work.Smooth.Morse.param_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)
  have himm : ∀ p : ℝ × ℝ, Function.Injective (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) :=
    Work.Smooth.Morse.Immersion.isImmersion ψ
  have hae : ∀ᵐ n ∂(MeasureTheory.volume : MeasureTheory.Measure R3),
      ∀ p : ℝ × ℝ,
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        ∀ w : ℝ × ℝ, (∀ w' : ℝ × ℝ,
          (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q))) p)
            w w' = 0) → w = 0 :=
    Work.Drive.Generic.ae_height_morse hΦ3 himm
  obtain ⟨n₁, hn₁ball, hn₁w⟩ := exists_mem_ball_of_ae
    (fun n : R3 => ∀ p : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
      ∀ w : ℝ × ℝ, (∀ w' : ℝ × ℝ,
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q))) p)
          w w' = 0) → w = 0)
    hae a₀ hr₁pos
  have hn₁Morse : ∀ p : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₁ (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₁ (Work.BoxShrink.Pinch.par ψ q))) p) :=
    injective_fderiv_fderiv_of_forall hn₁w
  have hn₁_a₀ : ‖n₁ - a₀‖ < r₁ := by
    rw [Metric.mem_ball, dist_eq_norm] at hn₁ball
    exact hn₁ball
  -- ## 3. the good height direction
  obtain ⟨n, hn_ball, hn_morse, hn_dist⟩ := goodHeight_exists ψ n₁ r₂ hr₂pos hn₁Morse
  have hn_n₁ : ‖n - n₁‖ < r₂ := by
    rw [Metric.mem_ball, dist_eq_norm] at hn_ball
    exact hn_ball
  have hn_a₀ : ‖n - a₀‖ < r₁ + r₂ := by
    calc ‖n - a₀‖ ≤ ‖n - n₁‖ + ‖n₁ - a₀‖ := by
          have h : n - a₀ = (n - n₁) + (n₁ - a₀) := by abel
          rw [h]; exact norm_add_le _ _
      _ < r₂ + r₁ := add_lt_add hn_n₁ hn₁_a₀
      _ = r₁ + r₂ := by ring
  -- ## 4. the tilt
  have hr₁64 : r₁ ≤ 1 / 64 := by rw [hr₁]; exact min_le_left _ _
  have hr₂64 : r₂ ≤ 1 / 64 := le_trans hr₂le hr₁64
  have hn_norm : (1 : ℝ) / 2 ≤ ‖n‖ := by
    have h5 : ‖a₀‖ ≤ ‖n‖ + ‖n - a₀‖ := by
      have h2 : ‖a₀‖ = ‖n + (a₀ - n)‖ := congrArg norm (show a₀ = n + (a₀ - n) from by abel)
      rw [h2]
      have h3 : ‖n + (a₀ - n)‖ ≤ ‖n‖ + ‖a₀ - n‖ := norm_add_le n (a₀ - n)
      rwa [norm_sub_rev a₀ n] at h3
    rw [ha₀1] at h5
    have h4 : ‖n - a₀‖ < 1 / 32 := by linarith [hn_a₀, hr₁64, hr₂64]
    linarith
  have hn_e : |inner ℝ n e| ≤ ‖n‖ * ε / 2 := by
    have h1 : inner ℝ n e = inner ℝ (n - a₀) e := by rw [inner_sub_left, ha₀e, sub_zero]
    have h2 : |inner ℝ (n - a₀) e| ≤ ‖n - a₀‖ := by
      have hh2 := abs_real_inner_le_norm (n - a₀) e
      rwa [he1, mul_one] at hh2
    have h3 : r₁ + r₂ ≤ ε / 4 := by linarith [hr₁le, hr₂le']
    have h6 : |inner ℝ n e| ≤ r₁ + r₂ := by rw [h1]; linarith [h2, hn_a₀]
    have h7 : ε / 4 ≤ ‖n‖ * ε / 2 := by
      have hh7 := mul_le_mul_of_nonneg_right hn_norm (le_of_lt hε)
      linarith
    linarith
  have hnpos : 0 < ‖n‖ := by linarith [hn_norm]
  obtain ⟨v, hv1, hnv, hve⟩ := tiltVector_of_small_angle he1 hnpos ε hε hn_e
  -- ## 5. the box bound, the half-width and the wall functional
  obtain ⟨R, hR0, hRbox⟩ := boxBound s c σ
  set h : ℝ := ε * R + R + |u| + 1 with hh
  have hh_eps : ε * R < h := by rw [hh]; linarith [hR0, abs_nonneg u]
  have hh_big : R + |u| < h := by rw [hh]; nlinarith [hε, hR0]
  set ℓ : R3 →L[ℝ] ℝ := (innerSL ℝ) n with hℓ
  have hℓne : ℓ ≠ 0 := by
    rw [hℓ]
    intro hzero
    have h1 : inner ℝ n n = 0 := by
      have := congrArg (fun (L : R3 →L[ℝ] ℝ) => L n) hzero
      simpa [innerSL_apply_apply] using this
    have h2 : ‖n‖ = 0 := by
      rw [real_inner_self_eq_norm_sq] at h1
      nlinarith [h1, norm_nonneg n]
    linarith [hn_norm, h2]
  have hvℓ : ℓ v = 0 := by
    rw [hℓ]
    simpa using hnv
  have hsweep : sweepHeight ψ ℓ = fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q) := by
    rw [hℓ]
    exact sweepHeight_innerSL ψ n
  -- ## 6. the finite set `exc` of critical values in the box
  have hcd : ContDiff ℝ 2 (sweepHeight ψ ℓ) := sweepHeight_contDiff_two ψ ℓ
  have hMorse : ∀ p : ℝ × ℝ, fderiv ℝ (sweepHeight ψ ℓ) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (sweepHeight ψ ℓ)) p) := by
    intro p hp
    rw [hsweep] at hp ⊢
    exact hn_morse p hp
  have hfin : ({p : ℝ × ℝ | fderiv ℝ (sweepHeight ψ ℓ) p = 0} ∩
      (Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi))).Finite :=
    finite_critSet_box hcd hMorse
  set exc : Finset ℝ := (hfin.toFinset.filter
      (fun q => Work.BoxShrink.Pinch.par ψ q ∈ Submission.PBox s c σ)).image
      (fun q => sweepHeight ψ ℓ q) with hexc
  have mem_exc : ∀ p : ℝ × ℝ, fderiv ℝ (sweepHeight ψ ℓ) p = 0 →
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      sweepHeight ψ ℓ p ∈ exc := by
    intro p hp hpBox
    obtain ⟨p', hp'Q, hp'crit, hp'par⟩ := exists_fundamental_of_crit ψ ℓ hp
    have hp'PBox : Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ := by
      rw [hp'par]; exact hpBox
    have hp'fin : p' ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨hp'crit, hp'Q⟩
    rw [hexc]
    refine Finset.mem_image.mpr ⟨p', ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨hp'fin, hp'PBox⟩
    · have h1 : sweepHeight ψ ℓ p' = ℓ (Work.BoxShrink.Pinch.par ψ p') := rfl
      rw [h1, hp'par]
      rfl
  -- ## 7. assembly
  refine ⟨v, h, ℓ, exc, R, hv1, ?_, hvℓ, hℓne, hRbox, hh_eps, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact hve
  · -- (i) interior regularity away from `exc`
    intro lam hlam p hpBox hpSlab hval hcrit
    obtain ⟨p', hp'Q, hp'crit, hp'par⟩ := exists_fundamental_of_crit ψ ℓ hcrit
    have hp'PBox : Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ := by
      rw [hp'par]; exact hpBox
    have hmem := mem_exc p' hp'crit hp'PBox
    have h1 : sweepHeight ψ ℓ p' = ℓ (Work.BoxShrink.Pinch.par ψ p') := rfl
    have hval' : sweepHeight ψ ℓ p' = lam := by
      rw [h1, hp'par]
      exact hval
    rw [hval'] at hmem
    exact hlam hmem
  · -- (ii) the slab strictly contains the box, so there are no face points inside it
    intro lam hlam p hpBox hface hval t
    have h2 : inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u) =
        inner ℝ v (Work.BoxShrink.Pinch.par ψ p - c) - u := by
      rw [inner_sub_right]; ring
    have h1 : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| < h := by
      rw [h2]
      have h3 : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p - c) - u| ≤
          |inner ℝ v (Work.BoxShrink.Pinch.par ψ p - c)| + |u| := by
        have := abs_sub_le (inner ℝ v (Work.BoxShrink.Pinch.par ψ p - c)) 0 u
        simpa using this
      have h4 : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p - c)| ≤
          ‖Work.BoxShrink.Pinch.par ψ p - c‖ := by
        have hh4 := abs_real_inner_le_norm v (Work.BoxShrink.Pinch.par ψ p - c)
        rwa [hv1, one_mul] at hh4
      have h5 := hRbox _ hpBox
      linarith [h3, h4, h5, hh_big]
    linarith [h1, hface]
  · -- (iii) nondegeneracy and the critical value
    intro p hpBox hpSlab hcrit
    refine ⟨?_, ?_⟩
    · rw [hsweep] at hcrit ⊢
      exact hn_morse p hcrit
    · have hmem := mem_exc p hcrit hpBox
      exact hmem
  · -- (iv) distinct critical values
    intro p p' hpBox hpBox' hpSlab hpSlab' hcrit hcrit' hval
    have hcrit2 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 := by
      rw [← hsweep]; exact hcrit
    have hcrit3 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p' = 0 := by
      rw [← hsweep]; exact hcrit'
    have hval' : inner ℝ n (Work.BoxShrink.Pinch.par ψ p) =
        inner ℝ n (Work.BoxShrink.Pinch.par ψ p') := by
      have h1 : ℓ (Work.BoxShrink.Pinch.par ψ p) = inner ℝ n (Work.BoxShrink.Pinch.par ψ p) := by
        rw [hℓ]; exact innerSL_apply_apply ℝ n _
      have h2 : ℓ (Work.BoxShrink.Pinch.par ψ p') = inner ℝ n (Work.BoxShrink.Pinch.par ψ p') := by
        rw [hℓ]; exact innerSL_apply_apply ℝ n _
      rw [h1, h2] at hval
      exact hval
    exact hn_dist p p' hcrit2 hcrit3 hval'

end

end Work.Drive.EpsForm
