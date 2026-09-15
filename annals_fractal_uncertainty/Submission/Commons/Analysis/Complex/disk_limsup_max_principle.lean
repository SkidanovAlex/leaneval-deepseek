import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Complex.Harmonic.harmonic_eqOn_of_isMaxOn_open

/-!
# Interior (limsup) maximum principle on the unit disk

If `u : ℂ → ℝ` is harmonic at every point of the open unit disk and its
boundary limsup from inside the disk is `≤ 0` at every boundary point
(formally: for every `ε > 0` and every boundary point `ζ` of the unit
circle there is a neighbourhood `U` of `ζ` with `u z < ε` for all
`z ∈ ball 0 1 ∩ U`), then `u z ≤ 0` throughout the open unit disk.

Proof outline.
1. *Uniform interior band* (from the boundary condition): for each `ε > 0`
   there is `0 < δ < 1` such that `u z < ε` on the inner band
   `{z | 1 - δ < ‖z‖ < 1}`.  (Compactness of the unit circle: cover it by
   the neighbourhoods of the hypothesis, take a finite subcover, and use
   the thickening lemma to pass from the open cover to a uniform band.)
2. *Closed-disk maximum principle*: if `u` is harmonic on the closed ball
   `closedBall 0 R` and `u ≤ S` on the circle `{‖z‖ = R}`, then `u w ≤ S`
   for every `w ∈ ball 0 R`.  (Max on the compact closed ball; an interior
   maximiser forces constancy on the connected open ball by the strong
   maximum principle, extended to the boundary circle by continuity —
   contradicting the circle bound.)
3. For fixed `z₀ ∈ ball 0 1` and `ε > 0`, apply 1. and pick a radius
   `R ∈ (max ‖z₀‖ (1-δ/2), 1)`; the whole circle `{‖z‖ = R}` lies in the
   band, so 2. gives `u z₀ ≤ ε`.  Let `ε → 0`.
-/

noncomputable section

open Set Metric Complex InnerProductSpace Filter
open scoped Topology Real

namespace Commons.Analysis.Complex

/-- Uniform interior band from pointwise boundary smallness.  If for every
boundary point `ζ` (‖ζ‖ = 1) and every `ε > 0` there is a neighbourhood of
`ζ` on which `u < ε` inside the unit disk, then for every `ε > 0` there is a
whole inner band `{z | 1 - δ < ‖z‖ < 1}` on which `u < ε`. -/
private lemma interior_uniform_band {u : ℂ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hcircle : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ U ∈ 𝓝 ζ, ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → z ∈ U → u z < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → 1 - δ < ‖z‖ → u z < ε := by
  classical
  let C : Set ℂ := {ζ : ℂ | ‖ζ‖ = 1}
  have hV (ζ : ℂ) (hζ : ζ ∈ C) : ∃ V : Set ℂ, IsOpen V ∧ ζ ∈ V ∧
      ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → z ∈ V → u z < ε := by
    rcases hcircle ζ hζ ε hε with ⟨U, hU, hprop⟩
    rcases (nhds_basis_opens ζ).mem_iff.mp hU with ⟨O, hO, hOsub⟩
    refine ⟨O, hO.2, hO.1, ?_⟩
    intro z hzball hzO
    exact hprop z hzball (hOsub hzO)
  let cV : C → Set ℂ := fun c => Classical.choose (hV c.1 c.2)
  have hcVopen (c : C) : IsOpen (cV c) := (Classical.choose_spec (hV c.1 c.2)).1
  have hcVmem (c : C) : (c : ℂ) ∈ cV c := (Classical.choose_spec (hV c.1 c.2)).2.1
  have hcVprop (c : C) : ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → z ∈ cV c → u z < ε :=
    (Classical.choose_spec (hV c.1 c.2)).2.2
  have hsphere_sub : sphere (0 : ℂ) 1 ⊆ ⋃ c : C, cV c := by
    intro ζ hζsphere
    have hζn : ‖ζ‖ = 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hζsphere
      exact hζsphere
    let c : C := ⟨ζ, hζn⟩
    have hc : ζ ∈ cV c := hcVmem c
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  rcases IsCompact.elim_finite_subcover (isCompact_sphere (0 : ℂ) 1) cV hcVopen hsphere_sub with ⟨t, htcover⟩
  let V : Set ℂ := ⋃ c ∈ t, cV c
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_biUnion (s := (t : Set C)) (fun c hc => hcVopen c)
  have hsubV : sphere (0 : ℂ) 1 ⊆ V := by
    simpa [V] using htcover
  rcases IsCompact.exists_thickening_subset_open (isCompact_sphere (0 : ℂ) 1) hVopen hsubV with ⟨δ, hδ, hthick⟩
  let δ₀ : ℝ := min δ (1 / 2)
  have hδ₀ : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min hδ (by norm_num)
  have hδ₀lt1 : δ₀ < 1 := by
    dsimp [δ₀]
    exact lt_of_le_of_lt (min_le_right δ (1 / 2)) (by norm_num)
  have hδ₀leδ : δ₀ ≤ δ := by
    dsimp [δ₀]
    exact min_le_left δ (1 / 2)
  refine ⟨δ₀, hδ₀, hδ₀lt1, ?_⟩
  intro z hzball hzδ
  have hz1 : ‖z‖ < 1 := by
    simpa [mem_ball, dist_eq_norm] using hzball
  have hzpos : 0 < ‖z‖ := by
    have : 0 < 1 - δ₀ := by linarith [hδ₀lt1]
    linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hzthickδ : z ∈ Metric.thickening δ (sphere (0 : ℂ) 1) := by
    rw [Metric.mem_thickening_iff]
    let z' : ℂ := (‖z‖⁻¹) • z
    refine ⟨z', ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      dsimp [z']
      have hz'n : ‖z‖ ≠ 0 := ne_of_gt hzpos
      calc
        ‖((‖z‖⁻¹ : ℝ) : ℂ) * z‖ = ‖((‖z‖⁻¹ : ℝ) : ℂ)‖ * ‖z‖ := by rw [norm_mul]
        _ = ‖z‖⁻¹ * ‖z‖ := by
          congr 1
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))
        _ = 1 := by field_simp [hz'n]
    · rw [dist_eq_norm]
      dsimp [z']
      have hz'n : ‖z‖ ≠ 0 := ne_of_gt hzpos
      calc
        ‖z - ((‖z‖⁻¹ : ℝ) : ℂ) * z‖ = ‖((1 : ℂ) - ((‖z‖⁻¹ : ℝ) : ℂ)) * z‖ := by
          congr 1
          ring
        _ = ‖((1 : ℂ) - ((‖z‖⁻¹ : ℝ) : ℂ))‖ * ‖z‖ := by rw [norm_mul]
        _ = (‖z‖⁻¹ - 1) * ‖z‖ := by
          have h1 : ‖((1 : ℂ) - ((‖z‖⁻¹ : ℝ) : ℂ))‖ = ‖z‖⁻¹ - 1 := by
            rw [← Complex.ofReal_one]
            rw [← Complex.ofReal_sub]
            rw [Complex.norm_real, Real.norm_eq_abs]
            have hle : 1 ≤ ‖z‖⁻¹ := by
              rw [one_le_inv₀ hzpos]  -- 1 ≤ ‖z‖⁻¹ iff ‖z‖ ≤ 1
              exact le_of_lt hz1
            have habs : |1 - ‖z‖⁻¹| = ‖z‖⁻¹ - 1 := by
              have hnonpos : 1 - ‖z‖⁻¹ ≤ 0 := by linarith
              rw [abs_of_nonpos hnonpos]
              ring
            exact habs
          rw [h1]
        _ = ‖z‖⁻¹ * ‖z‖ - 1 * ‖z‖ := by ring
        _ = 1 - ‖z‖ := by field_simp [hz'n]
        _ < δ₀ := by linarith
        _ ≤ δ := hδ₀leδ
  have hzV : z ∈ V := hthick hzthickδ
  rcases (Set.mem_iUnion₂.mp hzV) with ⟨c, hct, hzcV⟩
  exact hcVprop c z hzball hzcV

/-- Closed-disk maximum principle (centred at 0): a function harmonic on the
closed ball `closedBall 0 R` whose values on the bounding circle
`{z | ‖z‖ = R}` are `≤ S` satisfies `u w ≤ S` at every interior point
`w ∈ ball 0 R`. -/
private lemma disk_value_le_of_circle_le {u : ℂ → ℝ} {R S : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (closedBall (0 : ℂ) R))
    (hbd : ∀ z : ℂ, ‖z‖ = R → u z ≤ S) :
    ∀ w : ℂ, w ∈ ball (0 : ℂ) R → u w ≤ S := by
  classical
  intro w hw
  let K : Set ℂ := closedBall (0 : ℂ) R
  have hKcomp : IsCompact K := isCompact_closedBall (0 : ℂ) R
  have hKn : K.Nonempty := ⟨(0 : ℂ), by simp [K, le_of_lt hR]⟩
  have hcont : ContinuousOn u K := by
    simpa [K] using hu.continuousOn
  rcases IsCompact.exists_isMaxOn hKcomp hKn hcont with ⟨p, hpK, hpmax⟩
  have hpK' : ‖p‖ ≤ R := by
    simpa [K, dist_eq_norm] using hpK
  have hpmax_le_S : u p ≤ S := by
    rcases eq_or_lt_of_le hpK' with hp_eqR | hp_ltR
    · exact hbd p hp_eqR
    · -- p in the interior: strong max principle makes u constant on ball 0 R,
      -- extend to the boundary by continuity, contradict the circle bound.
      have huBall : ∀ x : ℂ, x ∈ ball (0 : ℂ) R → HarmonicAt u x := fun x hx =>
        hu x (ball_subset_closedBall hx)
      have hmaxBall : ∀ x : ℂ, x ∈ ball (0 : ℂ) R → u x ≤ u p := fun x hx =>
        hpmax (ball_subset_closedBall hx)
      have hpBall : p ∈ ball (0 : ℂ) R := by
        rw [mem_ball, dist_eq_norm, sub_zero]
        exact hp_ltR
      have hEq : ∀ x : ℂ, x ∈ ball (0 : ℂ) R → u x = u p := fun x hx =>
        Commons.Analysis.Complex.Harmonic.harmonic_eqOn_of_isMaxOn_open
          (U := ball (0 : ℂ) R)
          (isOpen_ball : IsOpen (ball (0 : ℂ) R)) (Metric.isPreconnected_ball)
          huBall hpBall hmaxBall x hx
      have hEqOn : EqOn u (fun _ : ℂ => u p) (ball (0 : ℂ) R) := by
        intro x hx
        exact hEq x hx
      have hcontCl : ContinuousOn u (closedBall (0 : ℂ) R) := hu.continuousOn
      have hEqCl : EqOn u (fun _ : ℂ => u p) (closedBall (0 : ℂ) R) := by
        have hcl : closure (ball (0 : ℂ) R) = closedBall (0 : ℂ) R :=
          closure_ball (0 : ℂ) hR.ne'
        exact hEqOn.of_subset_closure hcontCl continuousOn_const
          (by intro x hx; exact ball_subset_closedBall hx)
          (by rw [hcl])
      have hq_norm : ‖(R : ℂ)‖ = R := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hR)]
      have hqK : (R : ℂ) ∈ closedBall (0 : ℂ) R := by
        rw [mem_closedBall, dist_eq_norm, sub_zero]
        exact le_of_eq hq_norm
      have hup_eq : u p = u (R : ℂ) := (hEqCl hqK).symm
      have hbdq : u (R : ℂ) ≤ S := hbd (R : ℂ) hq_norm
      linarith
  exact le_trans (hpmax (ball_subset_closedBall hw)) hpmax_le_S

/-- **Interior (limsup) maximum principle on the unit disk.**  If `u` is
harmonic on the open unit disk and for every boundary point `ζ` (‖ζ‖ = 1)
and every `ε > 0` the values of `u` are `< ε` on a neighbourhood of `ζ`
inside the disk, then `u z ≤ 0` for every `z` in the open unit disk. -/
theorem disk_limsup_max_principle {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (ball (0 : ℂ) 1))
    (hcircle : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ U ∈ 𝓝 ζ, ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → z ∈ U → u z < ε) :
    ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → u z ≤ 0 := by
  intro z hz
  apply le_of_forall_pos_le_add
  intro ε hε
  rcases interior_uniform_band (u := u) (ε := ε) hε hcircle with ⟨δ, hδ0, hδ1, hband⟩
  let m : ℝ := max ‖z‖ (1 - δ / 2)
  let R : ℝ := (m + 1) / 2
  have hm_lt_1 : m < 1 := by
    dsimp [m]
    exact max_lt (by simpa [mem_ball, dist_eq_norm] using hz) (by linarith)
  have hz_lt_R : ‖z‖ < R := by
    dsimp [R, m]
    have hle : ‖z‖ ≤ max ‖z‖ (1 - δ / 2) := le_max_left _ _
    linarith
  have hR_lt_1 : R < 1 := by
    dsimp [R]
    linarith
  have hR_gt_band : 1 - δ < R := by
    dsimp [R, m]
    have hge : 1 - δ / 2 ≤ max ‖z‖ (1 - δ / 2) := le_max_right _ _
    linarith
  have hR_pos : 0 < R := by
    dsimp [R]
    have hm_nonneg : 0 ≤ m := le_trans (norm_nonneg z) (by dsimp [m]; exact le_max_left _ _)
    linarith
  have hu_cl : HarmonicOnNhd u (closedBall (0 : ℂ) R) := hu.mono (by
    intro x hx
    have hxle : ‖x‖ ≤ R := by simpa [dist_eq_norm] using hx
    rw [mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt hxle hR_lt_1)
  have hbd_circle : ∀ x : ℂ, ‖x‖ = R → u x ≤ ε := by
    intro x hx
    have hxin : x ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      rw [hx]
      exact hR_lt_1
    have hbandx : 1 - δ < ‖x‖ := by rw [hx]; exact hR_gt_band
    exact le_of_lt (hband x hxin hbandx)
  have hz_mem : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    exact hz_lt_R
  have hle := disk_value_le_of_circle_le (u := u) (R := R) (S := ε) hR_pos hu_cl
    hbd_circle z hz_mem
  simpa using hle

end Commons.Analysis.Complex