import Mathlib
import Submission.Work.ThomBordism.TwoSet.ConeDescent

/-!
# `cubeBoundaryCollapse`: the collapse `I^d → ∂I^{d+1}`

This file builds an explicit continuous surjection `Θ : I^d → ∂I^{d+1}` which collapses the boundary
`∂I^d` to a single point and is injective off `∂I^d` (so `Θ` realises the quotient
`I^d/∂I^d ≅ S^d ≅ ∂I^{d+1}`).

Writing `ρ x := rad hd x` for the `ℓ∞`-radius (`0` at the centre `c`, `1` exactly on `∂I^d`) and
`b x := bpt hd x` for the boundary point on the ray from `c` through `x`, the map is
`Θ x = (c + κ(ρ x)·(b x - c), τ(ρ x))` with `κ = min (min (3ρ) (3 - 3ρ)) 1` and
`τ = min (max (3ρ - 1) 0) 1`.  The first `d` coordinates are the "space part", the last one the
"suspension part".
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology unitInterval

variable {d : ℕ}

/-- The centre of the cube. -/
noncomputable def cubeCentre (d : ℕ) : IC d := fun _ => ⟨1/2, by norm_num⟩

theorem cubeCentre_apply (d : ℕ) (i : Fin d) : ((cubeCentre d) i : ℝ) = 1/2 := rfl

theorem rad_cubeCentre (hd : 1 ≤ d) : rad hd (cubeCentre d) = 0 := by
  refine le_antisymm ?_ (rad_nonneg hd _)
  rw [rad]
  refine Finset.sup'_le (finset_univ_nonempty hd) _ fun i _ => ?_
  show |2 * ((cubeCentre d i : unitInterval) : ℝ) - 1| ≤ 0
  rw [cubeCentre_apply]
  norm_num

theorem bpt_cubeCentre (hd : 1 ≤ d) : bpt hd (cubeCentre d) = cubeCentre d := by
  funext i
  apply Subtype.ext
  rw [bpt_coe, bptR, rad_cubeCentre hd, div_zero, add_zero]
  rfl

/-- The "cone" coordinate `κ = min (min (3ρ) (3 - 3ρ)) 1`. -/
noncomputable def coverKappa (hd : 1 ≤ d) (x : IC d) : ℝ :=
  min (min (3 * rad hd x) (3 - 3 * rad hd x)) 1

/-- The "suspension" coordinate `τ = min (max (3ρ - 1) 0) 1`. -/
noncomputable def coverTau (hd : 1 ≤ d) (x : IC d) : ℝ :=
  min (max (3 * rad hd x - 1) 0) 1

theorem coverKappa_nonneg (hd : 1 ≤ d) (x : IC d) : 0 ≤ coverKappa hd x := by
  have h0 := rad_nonneg hd x
  have h1 := rad_le_one hd x
  simp only [coverKappa]
  exact le_min (le_min (by linarith) (by linarith)) (by norm_num)

theorem coverKappa_le_one (hd : 1 ≤ d) (x : IC d) : coverKappa hd x ≤ 1 := by
  simp only [coverKappa]; exact min_le_right _ _

theorem coverKappa_le_three (hd : 1 ≤ d) (x : IC d) : coverKappa hd x ≤ 3 * rad hd x := by
  simp only [coverKappa]
  exact le_trans (min_le_left _ _) (min_le_left _ _)

theorem continuous_coverKappa (hd : 1 ≤ d) : Continuous (coverKappa hd) := by
  have h1 : Continuous fun x : IC d => 3 * rad hd x :=
    continuous_const.mul (continuous_rad hd)
  have h2 : Continuous fun x : IC d => 3 - 3 * rad hd x := continuous_const.sub h1
  exact (h1.min h2).min continuous_const

theorem coverTau_nonneg (hd : 1 ≤ d) (x : IC d) : 0 ≤ coverTau hd x := by
  simp only [coverTau]
  exact le_min (le_max_right _ _) (by norm_num)

theorem coverTau_le_one (hd : 1 ≤ d) (x : IC d) : coverTau hd x ≤ 1 := by
  simp only [coverTau]; exact min_le_right _ _

theorem coverTau_le_three (hd : 1 ≤ d) (x : IC d) : coverTau hd x ≤ 3 * rad hd x := by
  have h0 := rad_nonneg hd x
  have h1 : coverTau hd x ≤ max (3 * rad hd x - 1) 0 := by
    simp only [coverTau]; exact min_le_left _ _
  have h2 : max (3 * rad hd x - 1) 0 ≤ 3 * rad hd x := max_le (by linarith) (by linarith)
  linarith

theorem continuous_coverTau (hd : 1 ≤ d) : Continuous (coverTau hd) := by
  have h1 : Continuous fun x : IC d => 3 * rad hd x - 1 :=
    (continuous_const.mul (continuous_rad hd)).sub continuous_const
  exact (h1.max continuous_const).min continuous_const

/-- The suspension coordinate as an element of the unit interval. -/
noncomputable def coverTauI (hd : 1 ≤ d) (x : IC d) : unitInterval :=
  ⟨coverTau hd x, coverTau_nonneg hd x, coverTau_le_one hd x⟩

theorem coverTauI_coe (hd : 1 ≤ d) (x : IC d) : ((coverTauI hd x : unitInterval) : ℝ) = coverTau hd x :=
  rfl

/-- The space part of the collapse: `c + κ·(b - c)`. -/
noncomputable def coverSpace (hd : 1 ≤ d) (x : IC d) : IC d :=
  fun i => ⟨1/2 + coverKappa hd x * (((bpt hd x) i : ℝ) - 1/2), by
    have hk0 := coverKappa_nonneg hd x
    have hk1 := coverKappa_le_one hd x
    have hb0 := (bpt hd x i).2.1
    have hb1 := (bpt hd x i).2.2
    have hb : |(((bpt hd x) i : ℝ) - 1/2)| ≤ 1/2 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hk : |coverKappa hd x| ≤ 1 := by rw [abs_of_nonneg hk0]; exact hk1
    have hmul : |coverKappa hd x * (((bpt hd x) i : ℝ) - 1/2)| ≤ 1/2 := by
      rw [abs_mul]
      calc |coverKappa hd x| * |(((bpt hd x) i : ℝ) - 1/2)| ≤ 1 * (1/2) :=
            mul_le_mul hk hb (abs_nonneg _) (by norm_num)
        _ = 1/2 := by norm_num
    constructor
    · have := (abs_le.mp hmul).1; linarith
    · have := (abs_le.mp hmul).2; linarith⟩

theorem coverSpace_coe (hd : 1 ≤ d) (x : IC d) (i : Fin d) :
    ((coverSpace hd x) i : ℝ) = 1/2 + coverKappa hd x * (((bpt hd x) i : ℝ) - 1/2) := rfl

/-- The south pole of `∂I^{d+1}`: the image of `∂I^d`. -/
noncomputable def southPole (d : ℕ) : IC (d+1) :=
  Fin.snoc (cubeCentre d) (⟨0, by norm_num⟩ : unitInterval)

/-- The collapse map as a function into `I^{d+1}`. -/
noncomputable def coverFun (hd : 1 ≤ d) (x : IC d) : IC (d+1) :=
  Fin.snoc (coverSpace hd x) (coverTauI hd x)

theorem coverFun_last (hd : 1 ≤ d) (x : IC d) :
    ((coverFun hd x) (Fin.last d) : ℝ) = coverTau hd x := by
  rw [coverFun, Fin.snoc_last]; rfl

theorem coverFun_castSucc (hd : 1 ≤ d) (x : IC d) (i : Fin d) :
    ((coverFun hd x) (Fin.castSucc i) : ℝ) = ((coverSpace hd x) i : ℝ) := by
  rw [coverFun, Fin.snoc_castSucc]

/-- The radial coordinate identity: `x = c + ρ x · (b x - c)`. -/
theorem rad_bpt_eq (hd : 1 ≤ d) (x : IC d) (i : Fin d) :
    (x i : ℝ) = 1/2 + rad hd x * (((bpt hd x) i : ℝ) - 1/2) := by
  rw [bpt_coe, bptR]
  by_cases h : rad hd x = 0
  · have hx : x = cubeCentre d := eq_cen_of_rad_eq_zero hd h
    rw [hx]
    simp only [cubeCentre_apply]
    rw [rad_cubeCentre hd]
    norm_num
  · field_simp
    ring

theorem coverSpace_cubeCentre (hd : 1 ≤ d) : coverSpace hd (cubeCentre d) = cubeCentre d := by
  funext i
  apply Subtype.ext
  rw [coverSpace_coe]
  have hk : coverKappa hd (cubeCentre d) = 0 := by
    have h0 := rad_nonneg hd (cubeCentre d)
    simp only [coverKappa, rad_cubeCentre hd]
    norm_num
  rw [hk]
  simp only [cubeCentre_apply]
  ring

theorem coverFun_cubeCentre (hd : 1 ≤ d) :
    coverFun hd (cubeCentre d) = southPole d := by
  rw [coverFun, coverSpace_cubeCentre]
  congr 1
  apply Subtype.ext
  simp only [coverTauI_coe, coverTau, rad_cubeCentre hd]
  norm_num

/-- Pointwise bounds on the coordinates of the collapse. -/
theorem coverFun_coord_bound (hd : 1 ≤ d) (x : IC d) (j : Fin (d+1)) :
    |(((coverFun hd x) j : unitInterval) : ℝ)
      - ((southPole d j : unitInterval) : ℝ)| ≤ 3 * rad hd x := by
  have hρ := rad_nonneg hd x
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [coverFun_last]
    have h1 : (southPole d (Fin.last d) : unitInterval) = (⟨0, by norm_num⟩ : unitInterval) :=
      Fin.snoc_last _ _
    rw [h1]
    have h2 : (((⟨0, by norm_num⟩ : unitInterval)) : ℝ) = 0 := rfl
    rw [h2]
    have h3 := coverTau_le_three hd x
    have h4 := coverTau_nonneg hd x
    rw [sub_zero, abs_of_nonneg h4]
    exact h3
  · rw [coverFun_castSucc]
    have h1 : (southPole d (Fin.castSucc i) : unitInterval) = cubeCentre d i :=
      Fin.snoc_castSucc _ _ _
    rw [h1, coverSpace_coe]
    have hb0 := (bpt hd x i).2.1
    have hb1 := (bpt hd x i).2.2
    have hδ : |(((bpt hd x) i : ℝ) - 1/2)| ≤ 1/2 := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hk := coverKappa_le_three hd x
    have hk0 := coverKappa_nonneg hd x
    have hstep : |coverKappa hd x * (((bpt hd x) i : ℝ) - 1/2)| ≤ (3 * rad hd x) * (1/2) := by
      rw [abs_mul, abs_of_nonneg hk0]
      exact mul_le_mul hk hδ (abs_nonneg _) (by linarith)
    have hgoal : (1/2 + coverKappa hd x * (((bpt hd x) i : ℝ) - 1/2)) - (cubeCentre d i : ℝ)
        = coverKappa hd x * (((bpt hd x) i : ℝ) - 1/2) := by
      rw [cubeCentre_apply]; ring
    rw [hgoal]
    calc |coverKappa hd x * (((bpt hd x) i : ℝ) - 1/2)| ≤ (3 * rad hd x) * (1/2) := hstep
      _ ≤ 3 * rad hd x := by linarith

/-- If `min a 1 = 0` then `a = 0`. -/
lemma min_one_eq_zero {a : ℝ} (h : min a 1 = 0) : a = 0 := by
  rcases le_total a 1 with h1 | h1
  · rwa [min_eq_left h1] at h
  · rw [min_eq_right h1] at h; norm_num at h

lemma min_one_eq_one {a : ℝ} (h : min a 1 = 1) : 1 ≤ a := by
  rcases le_total a 1 with h1 | h1
  · rw [min_eq_left h1] at h; exact le_of_eq h.symm
  · exact h1

/-- The affine point `c + lam·(b - c)` of the cube (clamped to `[0,1]`); for `0 ≤ lam ≤ 1` it is
the point of the ray from the centre `c` through `b` at parameter `lam`. -/
noncomputable def affinePt (hd : 1 ≤ d) (b : IC d) (lam : ℝ) : IC d :=
  if h : 0 ≤ lam ∧ lam ≤ 1 then
    fun i => ⟨1/2 + lam * (((b i : ℝ)) - 1/2), by
      have hb0 := (b i).2.1
      have hb1 := (b i).2.2
      have hδ : |(((b i : ℝ)) - 1/2)| ≤ 1/2 := by
        rw [abs_le]; exact ⟨by linarith, by linarith⟩
      have hlam : |lam| ≤ 1 := by rw [abs_of_nonneg h.1]; exact h.2
      have hmul : |lam * (((b i : ℝ)) - 1/2)| ≤ 1/2 := by
        rw [abs_mul]
        calc |lam| * |(((b i : ℝ)) - 1/2)| ≤ 1 * (1/2) :=
              mul_le_mul hlam hδ (abs_nonneg _) (by norm_num)
          _ = 1/2 := by norm_num
      constructor
      · have := (abs_le.mp hmul).1; linarith
      · have := (abs_le.mp hmul).2; linarith⟩
  else cubeCentre d

theorem affinePt_coe (hd : 1 ≤ d) (b : IC d) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    {i : Fin d} :
    ((affinePt hd b lam) i : ℝ) = 1/2 + lam * (((b i : ℝ)) - 1/2) := by
  rw [affinePt, dif_pos ⟨h0, h1⟩]

theorem coverSpace_eq_affinePt (hd : 1 ≤ d) (x : IC d) :
    coverSpace hd x = affinePt hd (bpt hd x) (coverKappa hd x) := by
  funext i
  apply Subtype.ext
  rw [coverSpace_coe, affinePt_coe hd _ (coverKappa_nonneg hd x) (coverKappa_le_one hd x)]

theorem rad_affinePt (hd : 1 ≤ d) (b : IC d) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    rad hd (affinePt hd b lam) = lam * rad hd b := by
  refine le_antisymm ?_ ?_
  · rw [rad]
    refine Finset.sup'_le (finset_univ_nonempty hd) _ fun i _ => ?_
    rw [affinePt_coe hd b h0 h1]
    have hbi : |2 * (b i : ℝ) - 1| ≤ rad hd b := rad_le hd b i
    calc |2 * (1/2 + lam * ((b i : ℝ) - 1/2)) - 1| = lam * |2 * (b i : ℝ) - 1| := by
          rw [show 2 * (1/2 + lam * ((b i : ℝ) - 1/2)) - 1 = lam * (2 * (b i : ℝ) - 1) from by ring]
          rw [abs_mul, abs_of_nonneg h0]
      _ ≤ lam * rad hd b := mul_le_mul_of_nonneg_left hbi h0
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finset_univ_nonempty hd)
      (fun i => |2 * (b i : ℝ) - 1|)
    have hbnd : |2 * ((affinePt hd b lam) i : ℝ) - 1| ≤ rad hd (affinePt hd b lam) :=
      rad_le hd _ i
    rw [affinePt_coe hd b h0 h1] at hbnd
    rw [show 2 * (1/2 + lam * ((b i : ℝ) - 1/2)) - 1 = lam * (2 * (b i : ℝ) - 1) from by ring] at hbnd
    rw [abs_mul, abs_of_nonneg h0] at hbnd
    have hb' : rad hd b = |2 * (b i : ℝ) - 1| := hi
    rw [hb']
    exact hbnd

theorem bpt_affinePt (hd : 1 ≤ d) {b : IC d} (hb : rad hd b = 1) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1) : bpt hd (affinePt hd b lam) = b := by
  have h1' : rad hd (affinePt hd b lam) = lam := by
    rw [rad_affinePt hd b (le_of_lt h0) h1, hb, mul_one]
  funext i
  apply Subtype.ext
  rw [bpt_coe, bptR, h1', affinePt_coe hd b (le_of_lt h0) h1]
  field_simp
  ring

/-- `x` is recovered from its radius and its boundary direction. -/
theorem eq_affinePt_bpt (hd : 1 ≤ d) {x : IC d} (hρ : 0 < rad hd x) :
    affinePt hd (bpt hd x) (rad hd x) = x := by
  funext i
  apply Subtype.ext
  rw [affinePt_coe hd _ (le_of_lt hρ) (rad_le_one hd x)]
  exact (rad_bpt_eq hd x i).symm
theorem rad_coverSpace (hd : 1 ≤ d) (x : IC d) : rad hd (coverSpace hd x) = coverKappa hd x := by
  rw [coverSpace_eq_affinePt,
    rad_affinePt hd (bpt hd x) (coverKappa_nonneg hd x) (coverKappa_le_one hd x)]
  by_cases h : rad hd x = 0
  · have hx : x = cubeCentre d := eq_cen_of_rad_eq_zero hd h
    have hκ : coverKappa hd x = 0 := by simp only [coverKappa, h]; norm_num
    have hb : rad hd (bpt hd x) = 0 := by rw [hx, bpt_cubeCentre hd, rad_cubeCentre hd]
    rw [hκ, hb, mul_zero]
  · have hc : bpt hd x ∈ Cube.boundary (Fin d) := bpt_mem_boundary hd x h
    rw [rad_boundary_eq_one hd hc, mul_one]

theorem coverKappa_eq_zero_iff (hd : 1 ≤ d) (x : IC d) :
    coverKappa hd x = 0 ↔ rad hd x = 0 ∨ rad hd x = 1 := by
  have hρ0 := rad_nonneg hd x
  have hρ1 := rad_le_one hd x
  simp only [coverKappa]
  constructor
  · intro h
    have h1 : min (3 * rad hd x) (3 - 3 * rad hd x) = 0 := min_one_eq_zero h
    rcases le_total (3 * rad hd x) (3 - 3 * rad hd x) with hc | hc
    · left; rw [min_eq_left hc] at h1; linarith
    · right; rw [min_eq_right hc] at h1; linarith
  · intro h
    rcases h with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num

theorem coverTau_eq_zero_iff (hd : 1 ≤ d) (x : IC d) : coverTau hd x = 0 ↔ rad hd x ≤ 1/3 := by
  simp only [coverTau]
  constructor
  · intro h
    have h1 : max (3 * rad hd x - 1) 0 = 0 := min_one_eq_zero h
    have h2 : 3 * rad hd x - 1 ≤ 0 := max_eq_right_iff.mp h1
    linarith
  · intro h
    rw [max_eq_right (by linarith), min_eq_left (by norm_num)]

theorem coverTau_eq_one_iff (hd : 1 ≤ d) (x : IC d) : coverTau hd x = 1 ↔ 2/3 ≤ rad hd x := by
  simp only [coverTau]
  constructor
  · intro h
    have h1 : 1 ≤ max (3 * rad hd x - 1) 0 := min_one_eq_one h
    have h2 : 1 ≤ 3 * rad hd x - 1 := by
      rcases le_total 0 (3 * rad hd x - 1) with hc | hc
      · rwa [max_eq_left hc] at h1
      · rw [max_eq_right hc] at h1; norm_num at h1
    linarith
  · intro h
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]

theorem coverKappa_eq_three_rad_of_tau_zero (hd : 1 ≤ d) (x : IC d) (h : coverTau hd x = 0) :
    coverKappa hd x = 3 * rad hd x := by
  have h3 : rad hd x ≤ 1/3 := (coverTau_eq_zero_iff hd x).mp h
  simp only [coverKappa]
  rw [min_eq_left (le_trans (min_le_left _ _) (by linarith)), min_eq_left (by linarith)]

theorem coverKappa_eq_of_tau_one (hd : 1 ≤ d) (x : IC d) (h : coverTau hd x = 1) :
    coverKappa hd x = 3 - 3 * rad hd x := by
  have h3 : 2/3 ≤ rad hd x := (coverTau_eq_one_iff hd x).mp h
  simp only [coverKappa]
  rw [min_eq_left (le_trans (min_le_right _ _) (by linarith)), min_eq_right (by linarith)]

theorem coverKappa_eq_one_of_tau_pos (hd : 1 ≤ d) (x : IC d) (h0 : 0 < coverTau hd x)
    (h1 : coverTau hd x < 1) : coverKappa hd x = 1 := by
  have h2 : 1/3 < rad hd x := by
    by_contra hc
    push_neg at hc
    have hz := (coverTau_eq_zero_iff hd x).mpr hc
    linarith
  have h3 : rad hd x < 2/3 := by
    by_contra hc
    push_neg at hc
    have hz := (coverTau_eq_one_iff hd x).mpr hc
    linarith
  simp only [coverKappa]
  rw [min_eq_right (le_min (by linarith) (by linarith))]

theorem coverTau_eq_of_tau_pos (hd : 1 ≤ d) (x : IC d) (h0 : 0 < coverTau hd x)
    (h1 : coverTau hd x < 1) : coverTau hd x = 3 * rad hd x - 1 := by
  have h2 : 1/3 < rad hd x := by
    by_contra hc
    push_neg at hc
    have hz := (coverTau_eq_zero_iff hd x).mpr hc
    linarith
  have h3 : rad hd x < 2/3 := by
    by_contra hc
    push_neg at hc
    have hz := (coverTau_eq_one_iff hd x).mpr hc
    linarith
  simp only [coverTau]
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

theorem rad_eq_of_kappa_tau_eq (hd : 1 ≤ d) {x y : IC d}
    (hκ : coverKappa hd x = coverKappa hd y) (hτ : coverTau hd x = coverTau hd y) :
    rad hd x = rad hd y := by
  rcases lt_trichotomy (coverTau hd x) 0 with h0 | h0 | h0
  · have := coverTau_nonneg hd x; linarith
  · have hxm := coverKappa_eq_three_rad_of_tau_zero hd x h0
    have hy0 : coverTau hd y = 0 := by rw [← hτ, h0]
    have hym := coverKappa_eq_three_rad_of_tau_zero hd y hy0
    have : 3 * rad hd x = 3 * rad hd y := by rw [← hxm, ← hym, hκ]
    linarith
  · rcases lt_trichotomy (coverTau hd x) 1 with h1 | h1 | h1
    · have htx := coverTau_eq_of_tau_pos hd x h0 h1
      have hy0 : 0 < coverTau hd y := by rw [← hτ]; exact h0
      have hy1 : coverTau hd y < 1 := by rw [← hτ]; exact h1
      have hty := coverTau_eq_of_tau_pos hd y hy0 hy1
      have : 3 * rad hd x - 1 = 3 * rad hd y - 1 := by rw [← htx, ← hty, hτ]
      linarith
    · have hxm := coverKappa_eq_of_tau_one hd x h1
      have hy1 : coverTau hd y = 1 := by rw [← hτ, h1]
      have hym := coverKappa_eq_of_tau_one hd y hy1
      have : 3 - 3 * rad hd x = 3 - 3 * rad hd y := by rw [← hxm, ← hym, hκ]
      linarith
    · have := coverTau_le_one hd x; linarith

/-- The image of the boundary of the cube: the "north pole" `(c, 1)`. -/
noncomputable def northPole (d : ℕ) : IC (d+1) :=
  Fin.snoc (cubeCentre d) (⟨1, by norm_num⟩ : unitInterval)

theorem coe_one_unitInterval : ((1 : unitInterval) : ℝ) = 1 := rfl

theorem coe_zero_unitInterval : ((0 : unitInterval) : ℝ) = 0 := rfl

theorem zero_mem_boundary (hd : 1 ≤ d) : (0 : IC d) ∈ Cube.boundary (Fin d) :=
  ⟨⟨0, hd⟩, Or.inl rfl⟩

theorem rad_zero (hd : 1 ≤ d) : rad hd (0 : IC d) = 1 := by
  rw [rad]
  refine Finset.sup'_eq_of_forall _ _ fun i _ => ?_
  show |2 * (((0 : IC d) i : unitInterval) : ℝ) - 1| = 1
  simp

theorem mem_boundary_of_rad_eq_one (hd : 1 ≤ d) {x : IC d} (h : rad hd x = 1) :
    x ∈ Cube.boundary (Fin d) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finset_univ_nonempty hd)
    (fun i => |2 * (x i : ℝ) - 1|)
  have hi' : rad hd x = |2 * (x i : ℝ) - 1| := hi
  have hi'' : |2 * (x i : ℝ) - 1| = 1 := by rw [← hi', h]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hi'' with h' | h'
  · refine ⟨i, Or.inr ?_⟩
    apply Subtype.ext
    rw [coe_one_unitInterval]
    linarith
  · refine ⟨i, Or.inl ?_⟩
    apply Subtype.ext
    rw [coe_zero_unitInterval]
    linarith

theorem rad_eq_one_iff (hd : 1 ≤ d) {x : IC d} :
    rad hd x = 1 ↔ x ∈ Cube.boundary (Fin d) :=
  ⟨mem_boundary_of_rad_eq_one hd, rad_boundary_eq_one hd⟩

/-- The collapse sends the boundary of `I^d` to the north pole. -/
theorem coverFun_boundary_eq (hd : 1 ≤ d) {x : IC d} (hx : x ∈ Cube.boundary (Fin d)) :
    coverFun hd x = northPole d := by
  have hρ : rad hd x = 1 := rad_boundary_eq_one hd hx
  have hκ : coverKappa hd x = 0 := by simp only [coverKappa, hρ]; norm_num
  have hτ : coverTauI hd x = (⟨1, by norm_num⟩ : unitInterval) := by
    apply Subtype.ext
    rw [coverTauI_coe]
    simp only [coverTau, hρ]; norm_num
  have hsp : coverSpace hd x = cubeCentre d := by
    rw [coverSpace_eq_affinePt]
    funext i
    apply Subtype.ext
    rw [affinePt_coe hd _ (coverKappa_nonneg hd x) (coverKappa_le_one hd x), hκ]
    simp only [cubeCentre_apply]; ring
  rw [coverFun, hsp, hτ, northPole]

/-- The collapse lands in the boundary of `I^{d+1}`. -/
theorem coverFun_mem_boundary (hd : 1 ≤ d) (x : IC d) :
    coverFun hd x ∈ Cube.boundary (Fin (d+1)) := by
  by_cases h : 3 * rad hd x - 1 ≤ 0
  · refine ⟨Fin.last d, Or.inl ?_⟩
    apply Subtype.ext
    have hcv : ((coverFun hd x) (Fin.last d) : ℝ) = 0 := by
      rw [coverFun_last, coverTau, max_eq_right h, min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
    rw [hcv, coe_zero_unitInterval]
  · have h0 : 0 < 3 * rad hd x - 1 := not_le.mp h
    by_cases h2 : 1 ≤ 3 * rad hd x - 1
    · refine ⟨Fin.last d, Or.inr ?_⟩
      apply Subtype.ext
      have hcv : ((coverFun hd x) (Fin.last d) : ℝ) = 1 := by
        rw [coverFun_last, coverTau, max_eq_left (le_of_lt h0), min_eq_right h2]
      rw [hcv, coe_one_unitInterval]
    · have h2' : 3 * rad hd x - 1 < 1 := not_le.mp h2
      have hρ : 0 < rad hd x := by linarith
      obtain ⟨i, hi⟩ := bpt_mem_boundary hd x (ne_of_gt hρ)
      refine ⟨Fin.castSucc i, ?_⟩
      have hκ : coverKappa hd x = 1 := by
        simp only [coverKappa]
        rw [min_eq_right (le_min (by linarith) (by linarith))]
      have hsp : ((coverFun hd x) (Fin.castSucc i) : ℝ) = ((bpt hd x) i : ℝ) := by
        rw [coverFun_castSucc, coverSpace_coe, hκ]; ring
      rcases hi with hi | hi
      · left; apply Subtype.ext; rw [hsp, hi]
      · right; apply Subtype.ext; rw [hsp, hi]

/-- Coordinate continuity of the collapse on `{rad ≠ 0}`. -/
theorem continuousOn_coverFun_coord (hd : 1 ≤ d) (j : Fin (d+1)) :
    Continuous fun q : {y : IC d // rad hd y ≠ 0} =>
      (((coverFun hd q.1) j : unitInterval) : ℝ) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have h' : (fun q : {y : IC d // rad hd y ≠ 0} =>
        (((coverFun hd q.1) (Fin.last d) : unitInterval) : ℝ))
        = fun q => coverTau hd q.1 := by
      funext q; exact coverFun_last hd q.1
    rw [h']
    exact (continuous_coverTau hd).comp continuous_subtype_val
  · have h' : (fun q : {y : IC d // rad hd y ≠ 0} =>
        (((coverFun hd q.1) (Fin.castSucc i) : unitInterval) : ℝ))
        = fun q => 1/2 + coverKappa hd q.1 * (((bpt hd q.1) i : ℝ) - 1/2) := by
      funext q
      rw [coverFun_castSucc, coverSpace_coe]
    rw [h']
    have h1 : Continuous fun q : {y : IC d // rad hd y ≠ 0} => coverKappa hd q.1 :=
      (continuous_coverKappa hd).comp continuous_subtype_val
    have h2 : Continuous fun q : {y : IC d // rad hd y ≠ 0} => (((bpt hd q.1) i : ℝ)) := by
      rw [show (fun q : {y : IC d // rad hd y ≠ 0} => (((bpt hd q.1) i : ℝ)))
          = fun q => bptR hd q.1 i from funext (fun q => bpt_coe hd q.1 i)]
      exact bptR_continuous hd i
    exact continuous_const.add (h1.mul (h2.sub continuous_const))

theorem continuous_coverFun (hd : 1 ≤ d) : Continuous (coverFun hd) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : rad hd x = 0
  · have hxc : x = cubeCentre d := eq_cen_of_rad_eq_zero hd hx
    rw [hxc, Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε/6, by linarith, fun y hy => ?_⟩
    rw [coverFun_cubeCentre hd]
    have hyε : ∀ i : Fin d, |(y i : ℝ) - 1/2| < ε/6 := by
      intro i
      have h1 : dist (y i) (cubeCentre d i) ≤ dist y (cubeCentre d) := dist_le_pi_dist y _ i
      have h2 : dist (y i) (cubeCentre d i) = |(y i : ℝ) - 1/2| := by
        rw [Subtype.dist_eq, Real.dist_eq]; rfl
      rw [h2] at h1
      linarith
    have hρy : rad hd y < ε/3 := by
      rw [rad, Finset.sup'_lt_iff]
      intro i _
      have h := hyε i
      rw [abs_lt] at h ⊢
      constructor <;> linarith
    have hbd : dist (coverFun hd y) (southPole d) ≤ 3 * rad hd y := by
      exact (dist_pi_le_iff (show (0:ℝ) ≤ 3 * rad hd y by
        have h := rad_nonneg hd y; linarith)).mpr (fun j => by
        rw [Subtype.dist_eq, Real.dist_eq]
        exact coverFun_coord_bound hd y j)
    have h3 := mul_lt_mul_of_pos_left hρy (by norm_num : (0:ℝ) < 3)
    linarith
  · have hopen : {y : IC d | rad hd y ≠ 0} ∈ 𝓝 x :=
      ((isOpen_ne (x := (0:ℝ))).preimage (continuous_rad hd)).mem_nhds hx
    have hCO : ContinuousOn (coverFun hd) {y : IC d | rad hd y ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine continuous_pi (fun j => ?_)
      refine continuous_induced_rng.mpr ?_
      exact continuousOn_coverFun_coord hd j
    exact hCO.continuousAt hopen

/-- The collapse is injective off the boundary. -/
theorem coverFun_injective_off (hd : 1 ≤ d) {x y : IC d} (h : coverFun hd x = coverFun hd y) :
    x = y ∨ (x ∈ Cube.boundary (Fin d) ∧ y ∈ Cube.boundary (Fin d)) := by
  have hτ : coverTau hd x = coverTau hd y := by
    have := congrArg (fun w : IC (d+1) => ((w (Fin.last d) : unitInterval) : ℝ)) h
    simpa only [coverFun_last] using this
  have hcoord : ∀ i : Fin d, ((coverSpace hd x) i : ℝ) = ((coverSpace hd y) i : ℝ) := by
    intro i
    have := congrArg (fun w : IC (d+1) => ((w (Fin.castSucc i) : unitInterval) : ℝ)) h
    simpa only [coverFun_castSucc] using this
  have hsp : coverSpace hd x = coverSpace hd y := by
    funext i; exact Subtype.ext (hcoord i)
  have hκ : coverKappa hd x = coverKappa hd y := by
    rw [← rad_coverSpace hd x, ← rad_coverSpace hd y, hsp]
  have hρ : rad hd x = rad hd y := rad_eq_of_kappa_tau_eq hd hκ hτ
  by_cases hx0 : rad hd x = 0
  · left
    have hx : x = cubeCentre d := eq_cen_of_rad_eq_zero hd hx0
    have hy : y = cubeCentre d := eq_cen_of_rad_eq_zero hd (by rw [← hρ]; exact hx0)
    rw [hx, hy]
  · by_cases hx1 : rad hd x = 1
    · right
      exact ⟨(rad_eq_one_iff hd).mp hx1, (rad_eq_one_iff hd).mp (by rw [← hρ]; exact hx1)⟩
    · left
      have hκ0 : coverKappa hd x ≠ 0 := by
        intro hc
        rcases (coverKappa_eq_zero_iff hd x).mp hc with h' | h'
        · exact hx0 h'
        · exact hx1 h'
      have hbpt : bpt hd x = bpt hd y := by
        funext i
        apply Subtype.ext
        have h1 := hcoord i
        rw [coverSpace_eq_affinePt, coverSpace_eq_affinePt] at h1
        rw [affinePt_coe hd (bpt hd x) (coverKappa_nonneg hd x) (coverKappa_le_one hd x),
          affinePt_coe hd (bpt hd y) (coverKappa_nonneg hd y) (coverKappa_le_one hd y)] at h1
        rw [hκ] at h1
        have h2 : coverKappa hd y * (((bpt hd x) i : ℝ) - 1/2)
            = coverKappa hd y * (((bpt hd y) i : ℝ) - 1/2) := by linarith
        have hκ0y : coverKappa hd y ≠ 0 := by rw [← hκ]; exact hκ0
        have h3 := mul_left_cancel₀ hκ0y h2
        linarith
      funext i
      apply Subtype.ext
      rw [rad_bpt_eq hd x i, rad_bpt_eq hd y i, hρ,
        congrArg (fun z : IC d => ((z i : unitInterval) : ℝ)) hbpt]

/-- If the last coordinate of a point of `∂I^{d+1}` is not `0` or `1`, its space part is on
`∂I^d`. -/
theorem spacePart_mem_boundary (hd : 1 ≤ d) {w : IC (d+1)}
    (hw : w ∈ Cube.boundary (Fin (d+1))) {t : unitInterval} (ht : w (Fin.last d) = t)
    (ht0 : (t : ℝ) ≠ 0) (ht1 : (t : ℝ) ≠ 1) :
    (fun i : Fin d => w (Fin.castSucc i)) ∈ Cube.boundary (Fin d) := by
  obtain ⟨j, hj⟩ := hw
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | hlast
  · exact ⟨i, hj⟩
  · exfalso
    rw [hlast] at hj
    rw [ht] at hj
    rcases hj with h | h
    · exact ht0 (congrArg Subtype.val h)
    · exact ht1 (congrArg Subtype.val h)

theorem rad_third (hd : 1 ≤ d) (y : IC d) (hy : rad hd y ≠ 0) :
    rad hd (affinePt hd (bpt hd y) (rad hd y / 3)) = rad hd y / 3 := by
  rw [rad_affinePt hd _ (by linarith [rad_nonneg hd y]) (by linarith [rad_le_one hd y])]
  have hc : bpt hd y ∈ Cube.boundary (Fin d) := bpt_mem_boundary hd y hy
  rw [rad_boundary_eq_one hd hc, mul_one]

theorem bpt_third (hd : 1 ≤ d) (y : IC d) (hy : rad hd y ≠ 0) :
    bpt hd (affinePt hd (bpt hd y) (rad hd y / 3)) = bpt hd y := by
  have hc : bpt hd y ∈ Cube.boundary (Fin d) := bpt_mem_boundary hd y hy
  have hρ : rad hd (bpt hd y) = 1 := rad_boundary_eq_one hd hc
  have hpos : 0 < rad hd y := lt_of_le_of_ne (rad_nonneg hd y) (Ne.symm hy)
  exact bpt_affinePt hd hρ (by linarith) (by linarith [rad_le_one hd y])

theorem rad_one_sub (hd : 1 ≤ d) (y : IC d) (hy : rad hd y ≠ 0) :
    rad hd (affinePt hd (bpt hd y) (1 - rad hd y / 3)) = 1 - rad hd y / 3 := by
  rw [rad_affinePt hd _ (by linarith [rad_le_one hd y]) (by linarith [rad_nonneg hd y])]
  have hc : bpt hd y ∈ Cube.boundary (Fin d) := bpt_mem_boundary hd y hy
  rw [rad_boundary_eq_one hd hc, mul_one]

theorem bpt_one_sub (hd : 1 ≤ d) (y : IC d) (hy : rad hd y ≠ 0) :
    bpt hd (affinePt hd (bpt hd y) (1 - rad hd y / 3)) = bpt hd y := by
  have hc : bpt hd y ∈ Cube.boundary (Fin d) := bpt_mem_boundary hd y hy
  have hρ : rad hd (bpt hd y) = 1 := rad_boundary_eq_one hd hc
  have hpos : 0 < 1 - rad hd y / 3 := by
    have := rad_le_one hd y; linarith
  exact bpt_affinePt hd hρ hpos (by linarith [rad_nonneg hd y])

theorem coverFun_surjective (hd : 1 ≤ d) :
    Function.Surjective fun x : IC d => (⟨coverFun hd x, coverFun_mem_boundary hd x⟩ :
      {w : IC (d+1) // w ∈ Cube.boundary (Fin (d+1))}) := by
  intro w
  set y : IC d := fun i => w.1 (Fin.castSucc i) with hy
  set t : unitInterval := w.1 (Fin.last d) with ht
  have hyi : ∀ i : Fin d, w.1 (Fin.castSucc i) = y i := fun i => by rw [hy]
  have hti : w.1 (Fin.last d) = t := by rw [ht]
  have key : ∀ (x : IC d), coverTau hd x = (t : ℝ) → coverSpace hd x = y →
      (⟨coverFun hd x, coverFun_mem_boundary hd x⟩ :
        {w : IC (d+1) // w ∈ Cube.boundary (Fin (d+1))}) = w := by
    intro x hlast hsp
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · apply Subtype.ext
      rw [coverFun_last, hti]
      exact hlast
    · apply Subtype.ext
      rw [coverFun_castSucc, hyi i]
      exact congrArg (fun z : IC d => ((z i : unitInterval) : ℝ)) hsp
  rcases lt_trichotomy (t : ℝ) 0 with ht0 | ht0 | ht0
  · exact absurd t.2.1 (not_le_of_gt ht0)
  · -- t = 0
    by_cases hρ0 : rad hd y = 0
    · have hyc : y = cubeCentre d := eq_cen_of_rad_eq_zero hd hρ0
      refine ⟨cubeCentre d, key _ ?_ ?_⟩
      · rw [ht0, coverTau_eq_zero_iff, rad_cubeCentre hd]; norm_num
      · rw [coverSpace_cubeCentre hd, hyc]
    · have hρ : 0 < rad hd y := lt_of_le_of_ne (rad_nonneg hd y) (Ne.symm hρ0)
      have hκ : coverKappa hd (affinePt hd (bpt hd y) (rad hd y / 3)) = rad hd y := by
        rw [coverKappa_eq_three_rad_of_tau_zero hd _ (by
          rw [coverTau_eq_zero_iff, rad_third hd y hρ0]
          have := rad_le_one hd y; linarith), rad_third hd y hρ0]
        ring
      refine ⟨affinePt hd (bpt hd y) (rad hd y / 3), key _ ?_ ?_⟩
      · rw [ht0, coverTau_eq_zero_iff, rad_third hd y hρ0]
        have := rad_le_one hd y; linarith
      · funext i
        apply Subtype.ext
        rw [coverSpace_coe, bpt_third hd y hρ0, hκ, rad_bpt_eq hd y i]
  · rcases lt_trichotomy (t : ℝ) 1 with ht1 | ht1 | ht1
    · -- 0 < t < 1
      have hymem : y ∈ Cube.boundary (Fin d) :=
        spacePart_mem_boundary hd w.2 ht (ne_of_gt ht0) (ne_of_lt ht1)
      have hyrad : rad hd y = 1 := rad_boundary_eq_one hd hymem
      have hybpt : bpt hd y = y := bpt_eq_self_of_mem_boundary hd hymem
      have hlam0 : (0:ℝ) ≤ ((t:ℝ) + 1) / 3 := by linarith [t.2.1]
      have hlam1 : ((t:ℝ) + 1) / 3 ≤ 1 := by linarith [t.2.2]
      have hrad : rad hd (affinePt hd y (((t:ℝ) + 1) / 3)) = ((t:ℝ) + 1) / 3 := by
        rw [rad_affinePt hd y hlam0 hlam1, hyrad, mul_one]
      have hbpt : bpt hd (affinePt hd y (((t:ℝ) + 1) / 3)) = y :=
        bpt_affinePt (hd := hd) (b := y) (hb := hyrad) (lam := ((t:ℝ) + 1) / 3)
          (h0 := by linarith [t.2.1]) (h1 := hlam1)
      have hτ : coverTau hd (affinePt hd y (((t:ℝ) + 1) / 3)) = (t : ℝ) := by
        simp only [coverTau, hrad]
        rw [max_eq_left (by linarith [t.2.1]), min_eq_left (by linarith [t.2.2])]
        ring
      have hκ : coverKappa hd (affinePt hd y (((t:ℝ) + 1) / 3)) = 1 := by
        simp only [coverKappa, hrad]
        rw [min_eq_right (le_min (by linarith [t.2.1]) (by linarith [t.2.2]))]
      refine ⟨affinePt hd y (((t:ℝ) + 1) / 3), key _ ?_ ?_⟩
      · exact hτ
      · funext i
        apply Subtype.ext
        rw [coverSpace_coe, hbpt, hκ]
        simp only [one_mul]
        rw [rad_bpt_eq hd y i, hyrad]
        ring
    · -- t = 1
      by_cases hρ0 : rad hd y = 0
      · have hyc : y = cubeCentre d := eq_cen_of_rad_eq_zero hd hρ0
        have hb : bpt hd (0 : IC d) = 0 := by
          funext i
          apply Subtype.ext
          rw [bpt_coe, bptR, rad_zero]
          norm_num
        have hκ : coverKappa hd (0 : IC d) = 0 := by
          rw [coverKappa_eq_zero_iff, rad_zero]
          right; rfl
        have hsp : coverSpace hd (0 : IC d) = y := by
          rw [coverSpace_eq_affinePt, hb, hκ, hyc]
          funext i
          apply Subtype.ext
          rw [affinePt_coe hd _ (by norm_num) (by norm_num)]
          simp only [cubeCentre_apply]
          ring
        refine ⟨(0 : IC d), key _ ?_ ?_⟩
        · rw [ht1, coverTau_eq_one_iff, rad_zero]; norm_num
        · exact hsp
      · have hlam0 : (0:ℝ) ≤ 1 - rad hd y / 3 := by linarith [rad_le_one hd y]
        have hlam1 : 1 - rad hd y / 3 ≤ 1 := by linarith [rad_nonneg hd y]
        have hrad : rad hd (affinePt hd (bpt hd y) (1 - rad hd y / 3)) = 1 - rad hd y / 3 :=
          rad_one_sub hd y hρ0
        have hbpt : bpt hd (affinePt hd (bpt hd y) (1 - rad hd y / 3)) = bpt hd y :=
          bpt_one_sub hd y hρ0
        have hκ : coverKappa hd (affinePt hd (bpt hd y) (1 - rad hd y / 3)) = rad hd y := by
          rw [coverKappa_eq_of_tau_one hd _ (by
            rw [coverTau_eq_one_iff, hrad]
            have := rad_le_one hd y; linarith), hrad]
          ring
        refine ⟨affinePt hd (bpt hd y) (1 - rad hd y / 3), key _ ?_ ?_⟩
        · rw [ht1, coverTau_eq_one_iff, hrad]
          have := rad_le_one hd y; linarith
        · funext i
          apply Subtype.ext
          rw [coverSpace_coe, hbpt, hκ, rad_bpt_eq hd y i]
    · exact absurd t.2.2 (not_le_of_gt ht1)

/-- **The collapse of the cube onto the boundary of the next cube.** -/
theorem cubeBoundaryCollapse (d : ℕ) (hd : 1 ≤ d) :
    ∃ Θ : C(IC d, {x : IC (d+1) // x ∈ Cube.boundary (Fin (d+1))}),
      (∀ x ∈ Cube.boundary (Fin d), Θ x = Θ 0) ∧
      Function.Surjective Θ ∧
      Topology.IsQuotientMap Θ ∧
      (∀ x y, Θ x = Θ y →
        x = y ∨ (x ∈ Cube.boundary (Fin d) ∧ y ∈ Cube.boundary (Fin d))) := by
  have hcont : Continuous fun x : IC d =>
      (⟨coverFun hd x, coverFun_mem_boundary hd x⟩ :
        {x : IC (d+1) // x ∈ Cube.boundary (Fin (d+1))}) := by
    refine continuous_induced_rng.mpr ?_
    exact continuous_coverFun hd
  let Θ : C(IC d, {x : IC (d+1) // x ∈ Cube.boundary (Fin (d+1))}) :=
    ⟨fun x => ⟨coverFun hd x, coverFun_mem_boundary hd x⟩, hcont⟩
  have hsurj : Function.Surjective Θ := coverFun_surjective hd
  have hbd : ∀ x ∈ Cube.boundary (Fin d), Θ x = Θ 0 := by
    intro x hx
    apply Subtype.ext
    rw [show (Θ x).1 = coverFun hd x from rfl, show (Θ 0).1 = coverFun hd 0 from rfl,
      coverFun_boundary_eq hd hx, coverFun_boundary_eq hd (zero_mem_boundary hd)]
  have hcl : Topology.IsQuotientMap Θ := by
    refine IsClosedMap.isQuotientMap ?_ Θ.continuous hsurj
    intro s hs
    exact (hs.isCompact.image Θ.continuous).isClosed
  have hfib : ∀ x y, Θ x = Θ y →
      x = y ∨ (x ∈ Cube.boundary (Fin d) ∧ y ∈ Cube.boundary (Fin d)) := by
    intro x y h
    exact coverFun_injective_off hd (congrArg Subtype.val h)
  exact ⟨Θ, hbd, hsurj, hcl, hfib⟩

end Work.ThomBordism.TwoSet
