import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs

/-!
# A dent exists at every event of the tilted sweep, of any of the three types

(Project lead, `NOTES_LEAD_L4_L1.md` §4, task **L3**.)

At every event `p` of a good tilted sweep (`Work.Drive.Final.IsAnyEvent`, with the data
`Work.Drive.Final.GoodSweepData3`) this file produces *one* datum
`D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U` with `D.p = p` and `D.a' ≤ a₀`, for a
prescribed neighbourhood `U ∋ par ψ p` and any prescribed positive bound `a₀` on the depth.

The construction is the one of `Work.Drive.Final.dentData_exists` (the interior case) extended to the
two boundary types:

* the **cutoff** `χ` is the smooth bump of real analysis (`ContDiffBump`), which is non-negative —
  the extra field `χ_nonneg` of `AnyDentDatum`, needed to control the sign of the level shift;
* the **push direction** `d`: at an interior or face event, any unit `d` with `⟪v,d⟫ = 0` and
  `ℓ d > 0` (as produced by `exists_dent_direction`); at a **corner** event, `d` must additionally be
  *tangent to the unique active box face*, and this pins it to `± v × e_{σ i₀}` (`crossDir`);
* the **box preservation** field `box_pres`, which replaces the (impossible at a boundary point)
  "support inside the open box" field of `DentDatum`: the deformation preserves `PBox` on the ball of
  radius `r`, and this needs exactly the slack condition `box_pres_of_slack` below.

## Why corner events are one-sided

At a corner event the centre `z = par ψ p` lies on the box sphere (`boxNorm c σ z = s`).  Because `z`
is in the *carrier* (`Work.BoxShrink.Pinch.par_mem_carrier` — every `par ψ p` is a point of the
surface), the clauses

* `SlabInBelt` (`|z (σ 2) - c (σ 2)| < boxSide 2 * s` on the carrier's part of the closed slab) and
* `EdgeFree` (the carrier's part of the closed slab misses the box edges)

force `z` to lie on **exactly one** face of the box, at a label `i₀ ≠ 2` (`corner_extremal_unique`).
The push `± v × e_{σ i₀}` then leaves the `σ i₀`-coordinate fixed, and the corner direction clause
`ℓ (v × e_{σ i}) ≠ 0` (`i ≠ 2`) supplies the correct sign; on the two remaining coordinates the ball
of radius `r` has positive slack, which is the hypothesis of `box_pres_of_slack`.
-/

open LeanEval.KnotTheory.PardonDistortion
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-! ## The corner direction: `v × e_k` -/

/-- The corner direction `Work.Drive.Final.crossDir v k` is orthogonal to `v`. -/
theorem inner_crossDir (v : R3) (k : Fin 3) : inner ℝ v (crossDir v k) = 0 := by
  fin_cases k <;> simp [crossDir, PiLp.inner_apply, Fin.sum_univ_three] <;> ring

/-- The `k`-th coordinate of `Work.Drive.Final.crossDir v k` vanishes: the corner push leaves the
active box coordinate unchanged. -/
theorem crossDir_apply_self (v : R3) (k : Fin 3) : crossDir v k k = 0 := by
  fin_cases k <;> simp [crossDir]

/-- **The corner push direction**: if `ℓ` does not vanish at `crossDir v k`, normalizing it with the
sign chosen by `ℓ` gives a unit vector orthogonal to `v`, positive for `ℓ`, and with vanishing
`k`-th coordinate. -/
theorem exists_unit_of_crossDir {v : R3} {ℓ : R3 →L[ℝ] ℝ} {k : Fin 3}
    (hℓ : ℓ (crossDir v k) ≠ 0) :
    ∃ d : R3, ‖d‖ = 1 ∧ inner ℝ v d = 0 ∧ 0 < ℓ d ∧ d k = 0 := by
  set w : R3 := crossDir v k with hwdef
  have hw : w ≠ 0 := by intro h0; exact hℓ (by rw [h0, map_zero])
  have hwk : w k = 0 := by rw [hwdef]; exact crossDir_apply_self v k
  have hwin : inner ℝ v w = 0 := by rw [hwdef]; exact inner_crossDir v k
  refine ⟨(if 0 < ℓ w then (1:ℝ) else -1) • (‖w‖⁻¹ • w), ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg w)]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), mul_one]
    split_ifs <;> norm_num
  · rw [inner_smul_right, inner_smul_right, hwin, mul_zero, mul_zero]
  · rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hinv : 0 < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
    by_cases h : 0 < ℓ w
    · rw [if_pos h]; nlinarith
    · rw [if_neg h]; push Not at h
      have hlt : ℓ w < 0 := lt_of_le_of_ne h hℓ
      nlinarith
  · split_ifs <;> simp [hwk]

/-- **The push direction at an interior or face event**: a unit vector `d` orthogonal to `v` on which
`ℓ` is positive.  (Copied from `Work.Drive.Final.exists_dent_direction` so that this file rests only
on the event vocabulary.) -/
theorem exists_dent_direction {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : ‖v‖ = 1) (hℓv : ℓ v = 0)
    (hℓ : ℓ ≠ 0) : ∃ d : R3, ‖d‖ = 1 ∧ inner ℝ v d = 0 ∧ 0 < ℓ d := by
  have hw : ∃ w : R3, ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hw
  set q : R3 := w - (inner ℝ v w) • v with hq
  have hqin : inner ℝ v q = 0 := by
    rw [hq, inner_sub_right, inner_smul_right]
    have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    rw [hvv, mul_one, sub_self]
  have hqℓ : ℓ q = ℓ w := by rw [hq, map_sub, map_smul, hℓv, smul_eq_mul, mul_zero, sub_zero]
  have hq_ne : q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hqℓ
    exact hw hqℓ.symm
  have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq_ne
  have hqne : ℓ q ≠ 0 := by rw [hqℓ]; exact hw
  refine ⟨(if 0 < ℓ q then (1:ℝ) else -1) • (‖q‖⁻¹ • q), ?_, ?_, ?_⟩
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg q)]
    rw [inv_mul_cancel₀ hqnorm, mul_one]
    split_ifs <;> norm_num
  · rw [inner_smul_right, inner_smul_right, hqin, mul_zero, mul_zero]
  · rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hinv : 0 < ‖q‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hq_ne)
    by_cases h : 0 < ℓ q
    · rw [if_pos h]; nlinarith
    · rw [if_neg h]
      push Not at h
      have hlt : ℓ q < 0 := lt_of_le_of_ne h hqne
      nlinarith

/-! ## Box preservation -/

/-- **The box is preserved by a small push, provided the push is tangent to every active face.**  If
for every label `i` either `d` has no `σ i`-coordinate or the centre has positive slack in that
coordinate, then there are `r > 0` and `A > 0` such that for every `z` in the closed ball of radius
`r` about the centre and every `t ∈ [0, A]`, the points `z` and `z + t • d` are in the open box
`PBox s c σ` simultaneously.

Indeed, take `m > 0` below all the positive slacks; for `r = A = m/4` the slacks of `z` (and of
`z + t • d`, `‖t • d‖ ≤ A` since `‖d‖ = 1`) stay positive in the coordinates where `d` moves, and the
other coordinates are untouched. -/
theorem box_pres_of_slack {s : ℝ} {c centre d : R3} {σ : Equiv.Perm (Fin 3)}
    (hd : ‖d‖ = 1)
    (hslack : ∀ i : Fin 3,
      d (σ i) = 0 ∨ |centre (σ i) - c (σ i)| < Submission.boxSide i * s) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ, 0 < A ∧ ∀ z : R3, ‖z - centre‖ ≤ r →
      ∀ t : ℝ, 0 ≤ t → t ≤ A →
        (z ∈ Submission.PBox s c σ ↔ z + t • d ∈ Submission.PBox s c σ) := by
  set f : Fin 3 → ℝ := fun i =>
    if d (σ i) = 0 then 1 else Submission.boxSide i * s - |centre (σ i) - c (σ i)| with hfdef
  have hfpos : ∀ i, 0 < f i := by
    intro i
    have h := hslack i
    simp only [hfdef]
    by_cases hd0 : d (σ i) = 0
    · simp [hd0]
    · simp only [hd0, if_false]
      rcases h with h' | h'
      · exact absurd h' hd0
      · linarith
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ f ⟨0, Finset.mem_univ 0⟩
  have hmpos : 0 < f i₀ := hfpos i₀
  have hle : ∀ i : Fin 3, f i₀ ≤ f i := fun i => hmin i (Finset.mem_univ i)
  have hcoord : ∀ (y : R3) (i : Fin 3), |y i - centre i| ≤ ‖y - centre‖ := by
    intro y i
    have := PiLp.norm_apply_le (p := 2) (x := y - centre) i
    simpa only [Real.norm_eq_abs, PiLp.sub_apply] using this
  have hcoordd : ∀ i : Fin 3, |d i| ≤ 1 := by
    intro i
    have := PiLp.norm_apply_le (p := 2) (x := d) i
    simpa only [Real.norm_eq_abs, hd] using this
  refine ⟨f i₀ / 4, by linarith, f i₀ / 4, by linarith, ?_⟩
  intro z hz t ht0 htA
  have hzt : ∀ i : Fin 3, |z i - centre i| ≤ f i₀ / 4 := fun i => le_trans (hcoord z i) hz
  have key : ∀ i : Fin 3, (|z (σ i) - c (σ i)| < Submission.boxSide i * s ↔
      |(z + t • d) (σ i) - c (σ i)| < Submission.boxSide i * s) := by
    intro i
    by_cases hd0 : d (σ i) = 0
    · have hsame : (z + t • d) (σ i) = z (σ i) := by simp [hd0]
      rw [hsame]
    · have hfi : f i₀ ≤ Submission.boxSide i * s - |centre (σ i) - c (σ i)| := by
        have := hle i; simpa only [hfdef, hd0, if_false] using this
      have htd : |t * d (σ i)| ≤ f i₀ / 4 := by
        rw [abs_mul, abs_of_nonneg ht0]
        calc t * |d (σ i)| ≤ (f i₀ / 4) * 1 :=
              mul_le_mul htA (hcoordd (σ i)) (abs_nonneg _) (by linarith)
          _ = f i₀ / 4 := by ring
      have hA : |z (σ i) - c (σ i)| < Submission.boxSide i * s := by
        have h1 : |z (σ i) - c (σ i)| ≤ |z (σ i) - centre (σ i)| + |centre (σ i) - c (σ i)| :=
          abs_sub_le _ _ _
        have := hzt (σ i); linarith
      have hB : |(z + t • d) (σ i) - c (σ i)| < Submission.boxSide i * s := by
        have he : (z + t • d) (σ i) = z (σ i) + t * d (σ i) := by simp
        have h1 : |z (σ i) + t * d (σ i) - c (σ i)| ≤ |z (σ i) - centre (σ i)| + |t * d (σ i)| +
            |centre (σ i) - c (σ i)| := by
          have hr : z (σ i) + t * d (σ i) - c (σ i) =
              (z (σ i) - centre (σ i)) + t * d (σ i) + (centre (σ i) - c (σ i)) := by ring
          rw [hr]; exact abs_add_three _ _ _
        rw [he]
        have := hzt (σ i); linarith
      exact ⟨fun _ => hB, fun _ => hA⟩
  rw [Submission.mem_PBox, Submission.mem_PBox]
  exact forall_congr' key

/-! ## The one-sidedness of a corner -/

/-- **A corner event of a good sweep lies on exactly one face of the box, at a label `≠ 2`.**  For a
point `z` of the carrier in the closure of the box with `boxNorm c σ z = s` and `|slabFn| = h`,
`SlabInBelt` excludes the `σ 2` coordinate and `EdgeFree` excludes every *pair* of extremal
coordinates; hence there is a label `i₀ ≠ 2` which is extremal and every other label is strictly
inside the box. -/
theorem corner_extremal_unique {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ}
    (hEF : Work.Drive.Mono.EdgeFree ψ s c σ u v h)
    (hbelt : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) → |slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s)
    {z : R3} (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hclos : z ∈ closure (Submission.PBox s c σ))
    (hbn : Submission.boxNorm c σ z = s) (hslab : |slabFn c u v z| = h) :
    ∃ i₀ : Fin 3, i₀ ≠ 2 ∧ |z (σ i₀) - c (σ i₀)| = Submission.boxSide i₀ * s ∧
      ∀ j : Fin 3, j ≠ i₀ → |z (σ j) - c (σ j)| < Submission.boxSide j * s := by
  have hbelt' : |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s :=
    hbelt z hz hclos (le_of_eq hslab)
  have hq2 : |z (σ 2) - c (σ 2)| / Submission.boxSide 2 < s := by
    rw [div_lt_iff₀ (Submission.boxSide_pos 2)]; simpa [mul_comm] using hbelt'
  have hle : ∀ i : Fin 3, |z (σ i) - c (σ i)| / Submission.boxSide i ≤ s := by
    intro i
    have h := hbn
    rw [Submission.boxNorm] at h
    rcases max_le_iff.mp (le_of_eq h) with ⟨h1, h2⟩
    rcases max_le_iff.mp h1 with ⟨h10, h11⟩
    fin_cases i
    · exact h10
    · exact h11
    · exact h2
  have htoeq : ∀ i : Fin 3, |z (σ i) - c (σ i)| / Submission.boxSide i = s →
      |z (σ i) - c (σ i)| = Submission.boxSide i * s := by
    intro i h
    rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos i))] at h
    simpa [mul_comm] using h
  have htolt : ∀ i : Fin 3, |z (σ i) - c (σ i)| / Submission.boxSide i < s →
      |z (σ i) - c (σ i)| < Submission.boxSide i * s := by
    intro i h
    rw [div_lt_iff₀ (Submission.boxSide_pos i)] at h
    simpa [mul_comm] using h
  have hslab' : |inner ℝ v z - (inner ℝ v c + u)| = h := by
    simpa only [slabFn_apply] using hslab
  have hnq : ∀ i j : Fin 3, i ≠ j →
      |z (σ i) - c (σ i)| / Submission.boxSide i = s →
      |z (σ j) - c (σ j)| / Submission.boxSide j = s → False := by
    intro i j hij hi hj
    have hlt := hEF z hz hbn ⟨i, j, hij, htoeq i hi, htoeq j hj⟩
    rw [hslab'] at hlt
    exact lt_irrefl h hlt
  have hmax : max (|z (σ 0) - c (σ 0)| / Submission.boxSide 0)
      (|z (σ 1) - c (σ 1)| / Submission.boxSide 1) = s := by
    have h := hbn
    rw [Submission.boxNorm] at h
    rcases max_eq_iff.mp h with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (ne_of_lt hq2)
  rcases max_eq_iff.mp hmax with ⟨h0, -⟩ | ⟨h1, -⟩
  · refine ⟨0, by decide, htoeq 0 h0, ?_⟩
    intro j hj
    exact htolt j (by
      rcases lt_or_eq_of_le (hle j) with hlt | heq
      · exact hlt
      · exact (hnq j 0 hj heq h0).elim)
  · refine ⟨1, by decide, htoeq 1 h1, ?_⟩
    intro j hj
    exact htolt j (by
      rcases lt_or_eq_of_le (hle j) with hlt | heq
      · exact hlt
      · exact (hnq j 1 hj heq h1).elim)

/-! ## The radius of a dent, and the cutoff -/

/-- **A radius about an off-knot point which misses the knot.**  The range of the knot is the image of
the compact `[0, 2π]` (by `2π`-periodicity) and hence compact, so the distance to `p` attains a
positive minimum.  (Copied from `Work.Drive.Final.knotAvoids_radius_exists`.) -/
theorem knotAvoids_radius_exists (K : Knot) (p : R3) (hoff : ∀ t : ℝ, K.curve t ≠ p) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, r ≤ ‖K.curve t - p‖ := by
  have hcont : Continuous K.curve := K.smooth.continuous
  have hScomp : IsCompact (K.curve '' Set.Icc 0 (2 * Real.pi)) := isCompact_Icc.image hcont
  have hSne : (K.curve '' Set.Icc 0 (2 * Real.pi)).Nonempty :=
    ⟨K.curve 0, ⟨0, ⟨le_refl 0, by positivity⟩, rfl⟩⟩
  obtain ⟨z₀, hz₀S, hmin⟩ := hScomp.exists_isMinOn hSne
    (((continuous_id.sub continuous_const : Continuous (fun z : R3 => z - p))).norm).continuousOn
  have hz₀ne : z₀ ≠ p := by
    obtain ⟨t, -, ht⟩ := hz₀S
    rintro rfl
    exact hoff t ht
  have hdpos : 0 < ‖z₀ - p‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hz₀ne
  have hrange : Set.range K.curve ⊆ K.curve '' Set.Icc 0 (2 * Real.pi) := by
    intro y hy
    obtain ⟨t, rfl⟩ := hy
    obtain ⟨k, hk, -⟩ :=
      existsUnique_sub_zsmul_mem_Ico (a := 2 * Real.pi) (by positivity) t 0
    refine ⟨t - k • (2 * Real.pi), ⟨hk.1, by linarith [hk.2]⟩, ?_⟩
    conv_rhs => rw [← sub_add_cancel t (k • (2 * Real.pi))]
    exact (Function.Periodic.zsmul K.periodic k (t - k • (2 * Real.pi))).symm
  exact ⟨‖z₀ - p‖, hdpos, fun t => hmin (hrange ⟨t, rfl⟩)⟩

/-- **A cutoff function for a dent, non-negative.**  A smooth bump `χ` with `χ 0 = 1`, vanishing
beyond `1`, `0 ≤ χ ≤ 1`, equal to `1` near `0`, with a bound `κ` on `|χ'|`.

This is `Work.Drive.Final.exists_dent_cutoff` with the extra conclusion `0 ≤ χ`, which
`AnyDentDatum` requires (the sign of the level shift of the dented region is controlled by it). -/
theorem exists_dent_cutoff_nonneg :
    ∃ (χ : ℝ → ℝ) (κ : ℝ), Continuous χ ∧ χ 0 = 1 ∧ (∀ t : ℝ, 1 ≤ t → χ t = 0) ∧
      (∀ t : ℝ, |χ t| ≤ 1) ∧ (∀ t : ℝ, 0 ≤ χ t) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε → χ t = 1) ∧
      Differentiable ℝ χ ∧ 0 < κ ∧ (∀ t : ℝ, |deriv χ t| ≤ κ) := by
  let F : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩
  have hFdiff : Differentiable ℝ (F : ℝ → ℝ) := (F.contDiff (n := 1)).differentiable (by simp)
  have hFcont : Continuous (deriv (F : ℝ → ℝ)) := (F.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨t₀, -, hmax⟩ := (isCompact_closedBall (0:ℝ) 1).exists_isMaxOn ⟨0, by simp⟩
    hFcont.abs.continuousOn
  refine ⟨F, |deriv (F : ℝ → ℝ) t₀| + 1, F.continuous, ?_, ?_, ?_, ?_, ?_, hFdiff, by positivity,
    ?_⟩
  · simpa using F.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num : (0:ℝ) ≤ 1/2))
  · intro t ht
    refine F.zero_of_le_dist ?_
    show (1:ℝ) ≤ dist t (0:ℝ)
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]
    exact ht
  · intro t
    rw [abs_of_nonneg F.nonneg]
    exact F.le_one
  · intro t
    exact F.nonneg
  · refine ⟨1/2, by norm_num, fun t ht => ?_⟩
    refine F.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    exact ht
  · intro t
    by_cases ht : t ∈ Metric.closedBall (0:ℝ) 1
    · have hle : |deriv (↑F) t| ≤ |deriv (↑F) t₀| := hmax ht
      linarith
    · have h1 : 1 < |t| := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs] at ht
        push Not at ht
        exact ht
      have hev : (F : ℝ → ℝ) =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds h1] with s hs
        refine F.zero_of_le_dist ?_
        show (1:ℝ) ≤ dist s (0:ℝ)
        rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
        linarith [hs]
      rw [hev.deriv_eq]
      simp only [deriv_const, abs_zero]
      linarith [abs_nonneg (deriv (↑F) t₀)]

/-! ## Assembly -/

/-- **The datum exists as soon as the direction and the slack are given.**  Given a unit push `d`
orthogonal to `v`, positive for `ℓ`, and tangent to every face of the box which is active at the
centre (`hslack`), the datum of a dent of depth `≤ a₀` supported in the prescribed neighbourhood `U`
exists. -/
theorem anyDentDatum_of_direction {ψ : Submission.Diffeo} {K : Knot} {s R : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (hoffK : ∀ p : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p)
    {p : ℝ × ℝ} (hp : IsAnyEvent ψ s c σ u v h ℓ p)
    (hU : U ∈ nhds (Work.BoxShrink.Pinch.par ψ p)) (a₀ : ℝ) (ha₀ : 0 < a₀)
    {d : R3} (hdn : ‖d‖ = 1) (hdv : inner ℝ v d = 0) (hdpos : 0 < ℓ d)
    (hslack : ∀ i : Fin 3, d (σ i) = 0 ∨
      |Work.BoxShrink.Pinch.par ψ p (σ i) - c (σ i)| < Submission.boxSide i * s) :
    ∃ D : AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ D.a' ≤ a₀ := by
  obtain ⟨rb, hrb, Ab, hAb, hboxpres⟩ :=
    box_pres_of_slack (centre := Work.BoxShrink.Pinch.par ψ p) hdn hslack
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r₀, hr₀, havoids₀⟩ :=
    knotAvoids_radius_exists K (Work.BoxShrink.Pinch.par ψ p) (hoffK p hp)
  obtain ⟨χ, κ, hχcont, hχ0, hχout, hχle, hχnn, hχε, hχdiff, hκpos, hκbd⟩ :=
    exists_dent_cutoff_nonneg
  set r : ℝ := min rb (min (ρ / 4) r₀) with hrdef
  set a' : ℝ := min Ab (min a₀ (ρ / 4)) with hadef
  have hrpos : 0 < r := lt_min hrb (lt_min (by linarith) hr₀)
  have hapos : 0 < a' := lt_min hAb (lt_min ha₀ (by linarith))
  have hrle : r ≤ rb := min_le_left _ _
  have hrleρ : r ≤ ρ / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrler₀ : r ≤ r₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hale : a' ≤ Ab := min_le_left _ _
  have hale₀ : a' ≤ a₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have haleρ : a' ≤ ρ / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨{ χ := χ, χ_cont := hχcont, χ_zero_apply := hχ0, χ_eq_zero := hχout, χ_le_one := hχle,
            χ_nonneg := hχnn, χ_eq_one_near := hχε, χ_diff := hχdiff, κ := κ, κ_pos := hκpos,
            χ_deriv_bound := hκbd, p := p, isEvent := hp,
            centre := Work.BoxShrink.Pinch.par ψ p, centre_eq := rfl, d := d, d_norm := hdn,
            d_orth_v := hdv, push_pos := hdpos, r := r, r_pos := hrpos, a' := a', a'_pos := hapos,
            δ := a', δ_pos := hapos, a'_le_δ := le_rfl, ball_sub := ?_, box_pres := ?_,
            knotAvoids := ?_ }, rfl, hale₀⟩
  · -- the ball of radius `r + a'` about the centre lies in `U`
    intro z hz
    apply hρsub
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  · -- the deformation preserves the open box on the ball of radius `r`
    intro z hz
    have hz' : ‖z - Work.BoxShrink.Pinch.par ψ p‖ ≤ rb := le_trans hz hrle
    have ht0 : 0 ≤ a' * χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) :=
      mul_nonneg (le_of_lt hapos) (hχnn _)
    have htA : a' * χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) ≤ Ab := by
      have h1 : χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) ≤ 1 :=
        le_trans (le_abs_self _) (hχle _)
      have h2 : a' * χ (‖z - Work.BoxShrink.Pinch.par ψ p‖ / r) ≤ a' * 1 :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hapos)
      linarith
    exact hboxpres z hz' _ ht0 htA
  · -- the radius misses the knot
    intro t
    exact le_trans hrler₀ (havoids₀ t)

/-- **A dent exists at every event of the tilted sweep, of any of the three types.**  The depth `a'`
of the datum is at most the prescribed `a₀`, and its support (the ball of radius `r + a'`) lies in
the prescribed neighbourhood `U` of the event's image. -/
theorem anyDentData_exists {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot}
    {s R : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    {p : ℝ × ℝ} (hp : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p)
    (hU : U ∈ nhds (Work.BoxShrink.Pinch.par ψ p)) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∃ D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ D.a' ≤ a₀ := by
  obtain ⟨hGS2, hEF, hbelt, -, -, -, hcross, hoffK, -, -⟩ := hG
  obtain ⟨hGS, -, -, -, -, -⟩ := hGS2
  obtain ⟨hTilt, -, -, -, -⟩ := hGS
  obtain ⟨-, hv1, hℓne, hℓv, -, -, -, -, -, -, -⟩ := hTilt
  rcases hp with hp1 | hp2 | hp3
  · -- an interior event: the centre lies in the open box
    obtain ⟨d, h1, h2, h3⟩ := exists_dent_direction hv1 hℓv hℓne
    exact anyDentDatum_of_direction hoffK (Or.inl hp1) hU a₀ ha₀ h1 h2 h3
      (fun i => Or.inr (Submission.mem_PBox.mp hp1.1 i))
  · -- a face event: the centre lies in the open box as well
    obtain ⟨d, h1, h2, h3⟩ := exists_dent_direction hv1 hℓv hℓne
    exact anyDentDatum_of_direction hoffK (Or.inr (Or.inl hp2)) hU a₀ ha₀ h1 h2 h3
      (fun i => Or.inr (Submission.mem_PBox.mp hp2.1 i))
  · -- a corner event: the centre lies on the boundary of the box
    obtain ⟨hclos, hbn, hslab⟩ := hp3
    obtain ⟨i₀, hi₀2, -, hlt⟩ :=
      corner_extremal_unique hEF hbelt (Work.BoxShrink.Pinch.par_mem_carrier ψ p) hclos hbn hslab
    obtain ⟨d, h1, h2, h3, h4⟩ :=
      exists_unit_of_crossDir (v := v) (ℓ := ℓ) (k := σ i₀) (hcross i₀ hi₀2)
    refine anyDentDatum_of_direction hoffK (Or.inr (Or.inr ⟨hclos, hbn, hslab⟩)) hU a₀ ha₀
      h1 h2 h3 ?_
    intro i
    by_cases hii : i = i₀
    · left; rw [hii]; exact h4
    · exact Or.inr (hlt i hii)

end

end Work.Drive.Final
