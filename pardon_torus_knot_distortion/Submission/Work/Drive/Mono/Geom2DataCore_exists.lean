import Mathlib
import Submission.Work.Drive.Mono.TiltDataSmallSlab
import Submission.Work.Drive.Mono.Geom3Defs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- **The radius bound on the box sphere.**  A point whose box norm is `s` is within `5/2 * s` of the
centre `c`.  (This is `Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox` with the box sphere entering
directly: each coordinate of `z - c` is bounded by `boxSide i * s`, and `∑ boxSide i ^ 2 < 25/4`.) -/
theorem norm_sub_le_of_boxNorm_eq {s : ℝ} (hs : 0 ≤ s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {z : R3} (hz : Submission.boxNorm c σ z = s) : ‖z - c‖ ≤ 5 / 2 * s := by
  have hcoord : ∀ i : Fin 3, |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro i
    have hle : |z (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ z := by
      rw [Submission.boxNorm]
      fin_cases i <;> simp
    have h1 : |z (σ i) - c (σ i)| / Submission.boxSide i ≤ s := by rwa [hz] at hle
    have hb := Submission.boxSide_pos i
    rw [div_le_iff₀ hb] at h1
    linarith [h1]
  have hsum : ∑ i : Fin 3, (z (σ i) - c (σ i)) ^ 2 ≤
      (∑ i : Fin 3, Submission.boxSide i ^ 2) * s ^ 2 := by
    calc ∑ i : Fin 3, (z (σ i) - c (σ i)) ^ 2
        ≤ ∑ i : Fin 3, (Submission.boxSide i * s) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hcoord i
          have h2 := pow_le_pow_left₀ (abs_nonneg (z (σ i) - c (σ i))) h 2
          rwa [sq_abs] at h2
      _ = (∑ i : Fin 3, Submission.boxSide i ^ 2) * s ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hnorm : ‖z - c‖ ^ 2 = ∑ i : Fin 3, (z (σ i) - c (σ i)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Equiv.sum_comp σ (fun i => (z i - c i) ^ 2)]
    exact Finset.sum_congr rfl fun i _ => by rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  have hlt : ‖z - c‖ ^ 2 ≤ ((5 / 2) * s) ^ 2 := by
    rw [hnorm]
    have hb := Submission.sum_boxSide_sq_lt
    nlinarith [hsum, hb, hs, sq_nonneg s]
  have h5 : (0 : ℝ) ≤ 5 / 2 * s := by linarith
  nlinarith [norm_nonneg (z - c), hlt, h5]

/-- **The core geometric data of the deliverable.**  At every crux configuration and *every*
cutting level `u` and box level `s` there are tilt data whose slab is as thin as prescribed
(`h < η`) and which satisfy the data conjuncts `TiltData`, the window on the closed box,
`SlabCutsBox`, the thinness `h + |u| < boxWidth`, the closeness `‖v - shiftVσ σ 1‖ ≤ 1/8` of the
tilt direction, the *trace band* `|z (σ 2) - (c (σ 2) + u)| ≤ 2h` on the box sphere, the face
regularity on the box and the level-frontier genericity. -/
theorem Geom2DataCore_exists
    (ψ : Submission.Diffeo) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u r η : ℝ)
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r) (hη : 0 < η) :
    ∃ (v : LeanEval.KnotTheory.PardonDistortion.R3) (h R : ℝ)
      (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
      (lam0 lam1 : ℝ) (exc : Finset ℝ),
      Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
      0 < h ∧ h < η ∧
      (∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) ∧
      Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v ∧
      (h + |u| < Work.Drive.Mono.boxWidth s σ v) ∧
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 ∧
      (∀ z : LeanEval.KnotTheory.PardonDistortion.R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        Submission.boxNorm c σ z = s →
        |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
        |z (σ 2) - (c (σ 2) + u)| ≤ 2 * h) ∧
      (∀ z : LeanEval.KnotTheory.PardonDistortion.R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        z ∈ Submission.PBox s c σ →
        |inner ℝ v z - (inner ℝ v c + u)| = h →
        ∃ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ pp = z ∧
          fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) pp ≠ 0) ∧
      Work.Drive.Mono.LevelFrontierGen s c σ u v h ℓ exc lam0 lam1 := by
  classical
  have hs0 : 0 < s := lt_trans hr hrs
  -- the tilt direction (within `1/8` of `shiftVσ σ 1`), the good height direction, and the
  -- thin-slab data with the face regularity, at a half-width `h < η`
  obtain ⟨v, n, hv1, hn1, hvn, hgood, hve, hvη⟩ := exists_dirData_close ψ s σ η hs0 hη
  obtain ⟨h, nn, exc, hh0, hhη, hsize5, hcut, _hclosen, hnn1, hvnn, hgen, _hV, hfaceP, hfaceM⟩ :=
    tiltData_small_of_dir_near_junction ψ s c σ u r η 1 v n (∅ : Finset ℝ)
      hr hrs hu hη (by norm_num) hv1 hn1 hvn hgood hve hvη
  have hℓne : (innerSL ℝ) nn ≠ 0 := by
    intro h0
    have h1 : inner ℝ nn nn = 0 := by
      rw [← innerSL_apply_apply (𝕜 := ℝ) nn nn, h0]
      rfl
    have h2 : ‖nn‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq nn]; exact h1
    have h3 : ‖nn‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    rw [hnn1] at h3
    exact one_ne_zero h3
  have hℓv : (innerSL ℝ) nn v = 0 := by
    rw [innerSL_apply_apply, real_inner_comm]
    exact hvnn
  have hRbox : ∀ y ∈ closure (Submission.PBox s c σ), ‖y - c‖ ≤ 5 / 2 * s :=
    fun y hy => norm_sub_le_of_mem_closure_PBox (le_of_lt hs0) hy
  -- the window bookkeeping
  obtain ⟨lam0, lam1, hT, hwin⟩ :=
    exists_window_of_genericity hs0 hgen hv1 hℓne hℓv hsize5 hRbox
  -- the slab really cuts the box
  have hcut' : SlabCutsBox s c σ (inner ℝ v c + u) h v := slabCutsBox_of_width hs0 hh0 hcut
  -- the level-frontier genericity, at the enlarged exceptional set
  obtain ⟨B, hBwin, hLF⟩ := exists_levelFrontierGen s c σ u v h ((innerSL ℝ) nn) lam0 lam1
    hv1 hh0 hℓv hℓne hcut' hwin
  have hLF' : LevelFrontierGen s c σ u v h ((innerSL ℝ) nn) (exc ∪ B) lam0 lam1 := by
    simpa [Finset.union_comm] using levelFrontierGen_mono_exc (B := exc) hLF
  have hT' : TiltData ψ s c σ u v h (5 / 2 * s) ((innerSL ℝ) nn) (exc ∪ B) lam0 lam1 := by
    obtain ⟨hgen', hv1', hℓne', hℓv', hsize', hh', hbox', hlow', hhigh', hl', hexc'⟩ := hT
    exact ⟨tiltedGenericity_monoExc hgen', hv1', hℓne', hℓv', hsize', hh', hbox', hlow', hhigh',
      hl', fun t ht => by
        rcases Finset.mem_union.mp ht with hmem | hmem
        · exact hexc' t hmem
        · exact hBwin t hmem⟩
  -- the face regularity on the closed box
  have hface : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ pp = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) pp ≠ 0 := by
    intro z hzc hzbox hzface
    rw [Work.Drive.EpsSphere.torusOf, Work.Smooth.Morse.torus_carrier] at hzc
    obtain ⟨p, hp⟩ := hzc
    have hp' : Work.BoxShrink.Pinch.par ψ p = z := hp
    obtain ⟨p₀, hp₀Icc, hp₀par, _hp₀fd⟩ := Work.Drive.Mono.Band.fundamentalDomain_reduction ψ p
    have hp₀box : Work.BoxShrink.Pinch.par ψ p₀ ∈ closure (Submission.PBox s c σ) := by
      rw [hp₀par, hp']
      exact subset_closure hzbox
    have hval : Work.Drive.Mono.Band.heightV ψ v p₀ = inner ℝ v c + u + h ∨
        Work.Drive.Mono.Band.heightV ψ v p₀ = inner ℝ v c + u - h := by
      have hh2 : inner ℝ v (Work.BoxShrink.Pinch.par ψ p₀) = inner ℝ v z := by
        rw [hp₀par, hp']
      rw [Work.Drive.Mono.Band.heightV, hh2]
      rcases abs_eq hh0.le |>.mp hzface with h' | h'
      · exact Or.inl (by linarith [h'])
      · exact Or.inr (by linarith [h'])
    refine ⟨p₀, hp₀par.trans hp', ?_⟩
    rcases hval with h' | h'
    · exact hfaceP p₀ ⟨hp₀Icc, hp₀box⟩ h'
    · exact hfaceM p₀ ⟨hp₀Icc, hp₀box⟩ h'
  -- the trace band: the `σ 2`-coordinate is within `2h` of the cutting level
  have htraceBand : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      |z (σ 2) - (c (σ 2) + u)| ≤ 2 * h := by
    intro z _hzc hznorm hzface
    have hzc_le : ‖z - c‖ ≤ 5 / 2 * s := norm_sub_le_of_boxNorm_eq (le_of_lt hs0) hznorm
    have hsplit : inner ℝ v z - inner ℝ v c =
        (z (σ 2) - c (σ 2)) +
          inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
      have h1 : inner ℝ v z - inner ℝ v c = inner ℝ v (z - c) := (inner_sub_right _ _ _).symm
      have hvde : v = Work.BoxShrink.shiftVσ σ 1 + (v - Work.BoxShrink.shiftVσ σ 1) := by abel
      rw [h1, hvde, inner_add_left, Work.Drive.Mono.inner_shiftVσ_one]
      simp [PiLp.sub_apply]
    have herr : |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| ≤
        ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖ := abs_real_inner_le_norm _ _
    have herr2 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * ‖z - c‖ ≤
        ‖v - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) :=
      mul_le_mul_of_nonneg_left hzc_le (norm_nonneg _)
    have herrlt : |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| < h := by
      linarith [herr, herr2, hsize5]
    have hkey : z (σ 2) - (c (σ 2) + u) =
        (inner ℝ v z - (inner ℝ v c + u)) -
          inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c) := by
      linarith [hsplit]
    rw [hkey]
    calc |(inner ℝ v z - (inner ℝ v c + u)) -
            inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)|
        ≤ |inner ℝ v z - (inner ℝ v c + u)| +
            |inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (z - c)| := abs_sub _ _
      _ ≤ 2 * h := by linarith [hzface, herrlt]
  exact ⟨v, h, 5 / 2 * s, (innerSL ℝ) nn, lam0, lam1, exc ∪ B,
    hT', hh0, hhη, hwin, hcut', hcut, hve, htraceBand, hface, hLF'⟩

end

end Work.Drive.Mono
