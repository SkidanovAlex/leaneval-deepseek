import Submission.Work.BoxShrink.Pinch.Plane
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.BoxShrink.Bubble.HalfDefs

/-!
# The push-off fails at the standard small box

`BubbleHalf` fails at the standard round torus with the small box `s = 3/2`, `c = 0`,
`σ = swap 1 2`, `u = 0`: the region inside the box carries an essential loop (the inner equator,
of winding `(1,0)`), while both half-regions are inessential.  This is the counterexample that
delimits the push-off, and the witness for
`Work.BoxShrink.Pinch.not_exists_planeFlow_of_not_bubbleHalf` (the impossibility of the
parameter-plane flow route).

The proof is self-contained and uses only the parameter-plane criterion of `Plane.lean`:

* `containsEssentialLoop_of_periodicPath` for the box region;
* `not_containsEssentialLoop_of_disjoint_windows` for the two halves, with the pairwise disjoint
  windows `(kπ, (k+1)π) × (2πl + 2/5, 2πl + 2π - 2/5)`: the point is that a point of the box region
  lying in the upper half has `sin θ > 0`, `(2+cos φ)|cos θ| < 3/2` and
  `(2+cos φ)|sin θ| < 2^{2/3}·3/2`, whence `2 + cos φ < 73/25`, i.e. `cos φ < 23/25`; but if `φ` is
  within `2/5` of a multiple of `2π` then `cos φ ≥ 23/25` (Taylor bound).  Since the first
  coordinate of a point of a half-region is never a multiple of `π` (`y = (2+cos φ) sin θ ≠ 0`),
  the preimage is covered by the disjoint windows.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-! ## Coordinates of the standard torus map -/

theorem torusMap_apply_zero (θ φ : ℝ) :
    (Work.Core.torusMap θ φ).ofLp 0 = (2 + Real.cos φ) * Real.cos θ := by
  simp [Work.Core.torusMap, WithLp.ofLp_toLp]

theorem torusMap_apply_one (θ φ : ℝ) :
    (Work.Core.torusMap θ φ).ofLp 1 = (2 + Real.cos φ) * Real.sin θ := by
  simp [Work.Core.torusMap, WithLp.ofLp_toLp]

theorem torusMap_apply_two (θ φ : ℝ) :
    (Work.Core.torusMap θ φ).ofLp 2 = Real.sin φ := by
  simp [Work.Core.torusMap, WithLp.ofLp_toLp]

/-- The parametrisation of the standard torus. -/
theorem standard_psi (θ φ : ℝ) :
    (Work.CoreTopology.standard).psi θ φ = Work.Core.torusMap θ φ := rfl

theorem boxSide_zero : Submission.boxSide 0 = 1 := by
  simp [Submission.boxSide]

theorem boxSide_one : Submission.boxSide 1 = (2 : ℝ) ^ (1 / 3 : ℝ) := by
  simp [Submission.boxSide]

theorem boxSide_two : Submission.boxSide 2 = (2 : ℝ) ^ (2 / 3 : ℝ) := by
  simp [Submission.boxSide]

/-- The box norm at the standard configuration. -/
theorem std_boxNorm (y : R3) : Submission.boxNorm 0 (Equiv.swap 1 2) y =
    max (max (|y.ofLp 0|) (|y.ofLp 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
      (|y.ofLp 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  unfold Submission.boxNorm
  simp [Equiv.swap_apply_def, Submission.boxSide]

/-- The coordinates in the box at the standard configuration: `|x| < 3/2`,
`|z| < 2^{1/3}·3/2`, `|y| < 2^{2/3}·3/2`. -/
theorem std_mem_PBox_iff (y : R3) :
    y ∈ Submission.PBox (3 / 2) 0 (Equiv.swap 1 2) ↔
      |y.ofLp 0| < 3 / 2 ∧ |y.ofLp 2| < (2 : ℝ) ^ (1 / 3 : ℝ) * (3 / 2) ∧
        |y.ofLp 1| < (2 : ℝ) ^ (2 / 3 : ℝ) * (3 / 2) := by
  simp only [Submission.PBox, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.isValue]
  simp [Equiv.swap_apply_def, Submission.boxSide]

/-- The plane coordinate at the standard configuration. -/
theorem std_planeCoord (y : R3) :
    Work.BoxShrink.Bubble.planeCoord 0 (Equiv.swap 1 2) 0 y = y.ofLp 1 := by
  simp [Work.BoxShrink.Bubble.planeCoord, Equiv.swap_apply_def]

/-! ## The key estimate: a point of a half-region has `cos φ < 23/25` -/

theorem two_rpow_third_lt : (2 : ℝ) ^ (1 / 3 : ℝ) < 4 / 3 := by
  have h3 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hcube : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 < ((4 : ℝ) / 3) ^ 3 := by
    rw [h3]; norm_num
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) hcube

theorem two_rpow_four_thirds_lt : (2 : ℝ) ^ (4 / 3 : ℝ) < 8 / 3 := by
  have h : (2 : ℝ) ^ (4 / 3 : ℝ) = 2 * (2 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add (by norm_num)]
    norm_num
  rw [h]
  linarith [two_rpow_third_lt]

/-- **The key estimate**: a point of the upper region at the standard small configuration has
`cos φ < 23/25`.  The box bounds give `(2+cos φ)² < (9/4)(1 + 2^{4/3}) < (73/25)²`. -/
theorem cos_lt_of_mem_upperRegion {θ φ : ℝ}
    (h : Work.Core.torusMap θ φ ∈ Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard
      (3 / 2) 0 (Equiv.swap 1 2) 0) : Real.cos φ < 23 / 25 := by
  obtain ⟨-, hPBox, hpos⟩ := (Work.BoxShrink.Core.mem_upperRegion).mp h
  obtain ⟨hx, hz, hy⟩ := (std_mem_PBox_iff _).mp hPBox
  have hpos1 : 0 < (Work.Core.torusMap θ φ).ofLp 1 := by
    simpa only [Work.CoreTopology.standard, WithLp.ofLp_zero, Pi.zero_apply, zero_add, standard_psi,
      Work.BoxShrink.Bubble.planeCoord, show (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 2 = 1 from rfl]
      using hpos
  rw [torusMap_apply_zero] at hx
  rw [torusMap_apply_one] at hy
  set c := 2 + Real.cos φ with hc
  have hcpos : 0 < c := by rw [hc]; linarith [Real.neg_one_le_cos φ]
  have h1 : (c * Real.cos θ) ^ 2 < (3 / 2) ^ 2 := by
    have := abs_lt.mp hx
    nlinarith [this.1, this.2]
  have h2 : (c * Real.sin θ) ^ 2 < ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 / 2)) ^ 2 := by
    have := abs_lt.mp hy
    nlinarith [this.1, this.2]
  have h4 : ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 / 2)) ^ 2 = (2 : ℝ) ^ (4 / 3 : ℝ) * (9 / 4) := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hc2 : c ^ 2 < (9 / 4) * (1 + (2 : ℝ) ^ (4 / 3 : ℝ)) := by
    rw [h4] at h2
    nlinarith [h1, h2, hsq]
  have hfin : (9 / 4) * (1 + (2 : ℝ) ^ (4 / 3 : ℝ)) < (73 / 25 : ℝ) ^ 2 := by
    nlinarith [two_rpow_four_thirds_lt]
  have : c < 73 / 25 := by nlinarith [hcpos, hc2, hfin]
  rw [hc] at this
  linarith

/-- If `φ` is within `2/5` of a multiple of `2π` then `cos φ ≥ 23/25` (Taylor's bound at `2/5`). -/
theorem cos_ge_of_close {φ : ℝ} {l : ℤ} (h : |φ - l * (2 * Real.pi)| ≤ 2 / 5) :
    23 / 25 ≤ Real.cos φ := by
  have h1 : 1 - (φ - l * (2 * Real.pi)) ^ 2 / 2 ≤ Real.cos (φ - l * (2 * Real.pi)) :=
    Real.one_sub_sq_div_two_le_cos
  have h2 : Real.cos (φ - l * (2 * Real.pi)) = Real.cos φ := by
    have h := Real.cos_add_int_mul_two_pi (φ - l * (2 * Real.pi)) l
    rw [show φ - l * (2 * Real.pi) + l * (2 * Real.pi) = φ by ring] at h
    exact h.symm
  have h3 : (φ - l * (2 * Real.pi)) ^ 2 ≤ (2 / 5) ^ 2 := by
    nlinarith [abs_le.mp h, abs_nonneg (φ - l * (2 * Real.pi))]
  rw [h2] at h1
  linarith

/-! ## Integer windows -/

theorem exists_int_window (θ : ℝ) (h : Real.sin θ ≠ 0) :
    ∃ k : ℤ, k * Real.pi < θ ∧ θ < (k + 1) * Real.pi := by
  have hne : ∀ k : ℤ, θ ≠ k * Real.pi := by
    intro k hk
    exact h (by rw [hk]; simpa using Real.sin_int_mul_pi k)
  refine ⟨⌊θ / Real.pi⌋, ?_, ?_⟩
  · have hle : ((⌊θ / Real.pi⌋ : ℤ) : ℝ) ≤ θ / Real.pi := Int.floor_le _
    have hmul : ((⌊θ / Real.pi⌋ : ℤ) : ℝ) * Real.pi ≤ θ := by
      rw [le_div_iff₀ Real.pi_pos] at hle; linarith
    exact lt_of_le_of_ne hmul (fun he => hne _ he.symm)
  · have hlt : θ / Real.pi < ((⌊θ / Real.pi⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hmul : θ < (((⌊θ / Real.pi⌋ : ℤ) : ℝ) + 1) * Real.pi := by
      rw [div_lt_iff₀ Real.pi_pos] at hlt; linarith
    simpa [add_mul] using hmul

theorem exists_phi_window (φ : ℝ) (h : ∀ l : ℤ, 2 / 5 < |φ - l * (2 * Real.pi)|) :
    ∃ l : ℤ, l * (2 * Real.pi) + 2 / 5 < φ ∧ φ < l * (2 * Real.pi) + 2 * Real.pi - 2 / 5 := by
  have hπ : 0 < 2 * Real.pi := by positivity
  refine ⟨⌊φ / (2 * Real.pi)⌋, ?_, ?_⟩
  · have hle : ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ φ / (2 * Real.pi) := Int.floor_le _
    have hmul : ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ φ := by
      rw [le_div_iff₀ hπ] at hle; linarith
    have hlt := h ⌊φ / (2 * Real.pi)⌋
    rw [abs_of_nonneg (by linarith : 0 ≤ φ - ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi))] at hlt
    linarith
  · have hlt : φ / (2 * Real.pi) < ((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hmul : φ < (((⌊φ / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2 * Real.pi) := by
      rw [div_lt_iff₀ hπ] at hlt; linarith
    have hnext := h (⌊φ / (2 * Real.pi)⌋ + 1)
    have hval : φ - ((⌊φ / (2 * Real.pi)⌋ + 1 : ℤ) : ℝ) * (2 * Real.pi) < 0 := by
      push_cast at hmul ⊢; linarith
    rw [abs_of_neg hval] at hnext
    push_cast at hnext ⊢
    linarith

/-! ## The windows -/

/-- The windows `(kπ,(k+1)π) × (2πl + 2/5, 2πl + 2π - 2/5)`. -/
def halfWindows : Set (Set (ℝ × ℝ)) :=
  {W | ∃ k l : ℤ, W = Set.Ioo (k * Real.pi) ((k + 1) * Real.pi) ×ˢ
    Set.Ioo (l * (2 * Real.pi) + 2 / 5) (l * (2 * Real.pi) + 2 * Real.pi - 2 / 5)}

theorem mem_halfWindows {W : Set (ℝ × ℝ)} :
    W ∈ halfWindows ↔ ∃ k l : ℤ, W = Set.Ioo (k * Real.pi) ((k + 1) * Real.pi) ×ˢ
      Set.Ioo (l * (2 * Real.pi) + 2 / 5) (l * (2 * Real.pi) + 2 * Real.pi - 2 / 5) := Iff.rfl

theorem isWindow_halfWindows (W : Set (ℝ × ℝ)) (hW : W ∈ halfWindows) : IsWindow W := by
  obtain ⟨k, l, rfl⟩ := mem_halfWindows.mp hW
  refine isWindow_Ioo ?_ ?_
  · push_cast; linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

theorem isOpen_halfWindows (W : Set (ℝ × ℝ)) (hW : W ∈ halfWindows) : IsOpen W := by
  obtain ⟨k, l, rfl⟩ := mem_halfWindows.mp hW
  exact isOpen_Ioo.prod isOpen_Ioo

theorem pairwiseDisjoint_halfWindows : halfWindows.Pairwise Disjoint := by
  rintro W hW W' hW' hne
  obtain ⟨k, l, rfl⟩ := mem_halfWindows.mp hW
  obtain ⟨k', l', rfl⟩ := mem_halfWindows.mp hW'
  rcases eq_or_ne k k' with rfl | hk
  · rcases eq_or_ne l l' with rfl | hl
    · exact absurd rfl hne
    · rw [Set.disjoint_left]
      intro q hq hq'
      obtain ⟨-, hq2⟩ := hq
      obtain ⟨-, hq2'⟩ := hq'
      rcases lt_or_gt_of_ne hl with h | h
      · have hcast : (l : ℝ) + 1 ≤ (l' : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
        nlinarith [Real.pi_pos, hq2.2, hq2'.1]
      · have hcast : (l' : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
        nlinarith [Real.pi_pos, hq2'.2, hq2.1]
  · rw [Set.disjoint_left]
    intro q hq hq'
    obtain ⟨hq1, -⟩ := hq
    obtain ⟨hq1', -⟩ := hq'
    rcases lt_or_gt_of_ne hk with h | h
    · have hcast : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
      nlinarith [Real.pi_pos, hq1.2, hq1'.1]
    · have hcast : (k' : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h
      nlinarith [Real.pi_pos, hq1'.2, hq1.1]

/-! ## The three regions are respectively essential and inessential -/

theorem boxRegion_essential :
    (Work.CoreTopology.standard).ContainsEssentialLoop
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2)) := by
  refine containsEssentialLoop_of_periodicPath (P := Work.CoreTopology.standard)
    (q := fun t : ℝ => (t * (2 * Real.pi), Real.pi)) (k := 1) (l := 0) ?_ ?_ ?_ ?_
  · exact (continuous_id.mul continuous_const).prodMk continuous_const
  · intro t
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  · norm_num
  · intro t
    rw [Phi_apply, Work.BoxShrink.Core.mem_boxRegion, std_mem_PBox_iff]
    refine ⟨?_, ?_⟩
    · exact Set.mem_range.mpr ⟨(t * (2 * Real.pi), Real.pi), rfl⟩
    · rw [standard_psi, torusMap_apply_zero, torusMap_apply_one, torusMap_apply_two]
      have hcosπ : Real.cos Real.pi = -1 := Real.cos_pi
      have hsinπ : Real.sin Real.pi = 0 := Real.sin_pi
      rw [hcosπ, hsinπ]
      norm_num
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_lt]
        exact ⟨by linarith [Real.neg_one_le_cos (t * (2 * Real.pi))],
          by linarith [Real.cos_le_one (t * (2 * Real.pi))]⟩
      · exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / 3 : ℝ)
      · rw [abs_lt]
        refine ⟨?_, ?_⟩
        · nlinarith [Real.neg_one_le_sin (t * (2 * Real.pi)),
            Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2 / 3)]
        · nlinarith [Real.sin_le_one (t * (2 * Real.pi)),
            Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2 / 3)]

theorem upperRegion_preimage_subset :
    Work.BoxShrink.Pinch.planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0)
      ⊆ ⋃₀ halfWindows := by
  intro q hq
  rw [mem_planePreimage] at hq
  rw [standard_psi] at hq
  have hcos : Real.cos q.2 < 23 / 25 := cos_lt_of_mem_upperRegion hq
  have hsin : Real.sin q.1 ≠ 0 := by
    intro h0
    have hpos := ((Work.BoxShrink.Core.mem_upperRegion).mp hq).2.2
    rw [show (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 2 = 1 from rfl, WithLp.ofLp_zero,
      Pi.zero_apply, zero_add, torusMap_apply_one, h0, mul_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨k, hk1, hk2⟩ := exists_int_window q.1 hsin
  have hfar : ∀ l : ℤ, 2 / 5 < |q.2 - l * (2 * Real.pi)| := by
    intro l
    exact lt_of_not_ge (fun hle => absurd (cos_ge_of_close hle) (not_le.mpr hcos))
  obtain ⟨l, hl1, hl2⟩ := exists_phi_window q.2 hfar
  exact mem_sUnion.mpr ⟨_, ⟨k, l, rfl⟩, ⟨hk1, hk2⟩, ⟨hl1, hl2⟩⟩

theorem lowerRegion_preimage_subset :
    Work.BoxShrink.Pinch.planePreimage Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0)
      ⊆ ⋃₀ halfWindows := by
  intro q hq
  rw [mem_planePreimage] at hq
  rw [standard_psi] at hq
  -- the same estimate, with `-sin θ > 0`
  have hcos : Real.cos q.2 < 23 / 25 := by
    obtain ⟨-, hPBox, hneg⟩ := (Work.BoxShrink.Core.mem_lowerRegion).mp hq
    obtain ⟨hx, hz, hy⟩ := (std_mem_PBox_iff _).mp hPBox
    rw [torusMap_apply_zero] at hx
    rw [torusMap_apply_one] at hy
    set c := 2 + Real.cos q.2 with hc
    have hcpos : 0 < c := by rw [hc]; linarith [Real.neg_one_le_cos q.2]
    have h1 : (c * Real.cos q.1) ^ 2 < (3 / 2) ^ 2 := by
      have := abs_lt.mp hx; nlinarith [this.1, this.2]
    have h2 : (c * Real.sin q.1) ^ 2 < ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 / 2)) ^ 2 := by
      have := abs_lt.mp hy; nlinarith [this.1, this.2]
    have h4 : ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 / 2)) ^ 2 = (2 : ℝ) ^ (4 / 3 : ℝ) * (9 / 4) := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hsq : Real.cos q.1 ^ 2 + Real.sin q.1 ^ 2 = 1 := Real.cos_sq_add_sin_sq q.1
    have hc2 : c ^ 2 < (9 / 4) * (1 + (2 : ℝ) ^ (4 / 3 : ℝ)) := by
      rw [h4] at h2; nlinarith [h1, h2, hsq]
    have hfin : (9 / 4) * (1 + (2 : ℝ) ^ (4 / 3 : ℝ)) < (73 / 25 : ℝ) ^ 2 := by
      nlinarith [two_rpow_four_thirds_lt]
    have : c < 73 / 25 := by nlinarith [hcpos, hc2, hfin]
    rw [hc] at this
    linarith
  have hsin : Real.sin q.1 ≠ 0 := by
    intro h0
    have hneg := ((Work.BoxShrink.Core.mem_lowerRegion).mp hq).2.2
    rw [show (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 2 = 1 from rfl, WithLp.ofLp_zero,
      Pi.zero_apply, zero_add, torusMap_apply_one, h0, mul_zero] at hneg
    exact absurd hneg (lt_irrefl 0)
  obtain ⟨k, hk1, hk2⟩ := exists_int_window q.1 hsin
  have hfar : ∀ l : ℤ, 2 / 5 < |q.2 - l * (2 * Real.pi)| := by
    intro l
    exact lt_of_not_ge (fun hle => absurd (cos_ge_of_close hle) (not_le.mpr hcos))
  obtain ⟨l, hl1, hl2⟩ := exists_phi_window q.2 hfar
  exact mem_sUnion.mpr ⟨_, ⟨k, l, rfl⟩, ⟨hk1, hk2⟩, ⟨hl1, hl2⟩⟩

theorem not_containsEssentialLoop_upperRegion :
    ¬ (Work.CoreTopology.standard).ContainsEssentialLoop
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0) :=
  not_containsEssentialLoop_of_disjoint_windows _ halfWindows isWindow_halfWindows
    isOpen_halfWindows pairwiseDisjoint_halfWindows upperRegion_preimage_subset

theorem not_containsEssentialLoop_lowerRegion :
    ¬ (Work.CoreTopology.standard).ContainsEssentialLoop
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0) :=
  not_containsEssentialLoop_of_disjoint_windows _ halfWindows isWindow_halfWindows
    isOpen_halfWindows pairwiseDisjoint_halfWindows lowerRegion_preimage_subset

/-- **The push-off fails at the standard small box.**  The region inside the box carries the inner
equator (winding `(1,0)`), while neither half-region carries an essential loop. -/
theorem BubbleHalfRefuted :
    ¬ Work.BoxShrink.Bubble.BubbleHalf Work.CoreTopology.standard (3 / 2) 0 (Equiv.swap 1 2) 0 := by
  intro h
  rcases h boxRegion_essential with hup | hlo
  · exact not_containsEssentialLoop_upperRegion hup
  · exact not_containsEssentialLoop_lowerRegion hlo

end

end Work.BoxShrink.Pinch
