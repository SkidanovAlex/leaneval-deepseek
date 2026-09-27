import Mathlib

/-!
# The Euclidean radial push

For a real normed space `E`, a base point `p : E` and a threshold `L : ℝ`, this file defines
the one-parameter family of *radial pushes away from* `p` with threshold `L`:

`pushGen p L s x = p + (radLam s (dist x p) L / dist x p) • (x - p)`,

where `radLam s d L = s * d + (1 - s) * max d L` interpolates between `d` and `max d L`.
Thus

* `pushGen p L 1 = id` (the parameter `s = 1` is the identity),
* `pushGen p L 0 = push p L` (the parameter `s = 0` is the push), and
* for `s ∈ [0,1]`, `pushGen p L s x` lies on the ray from `p` through `x`, at distance
  `radLam s (dist x p) L ∈ [dist x p, max (dist x p) L]` from `p`.

The push `push p L` fixes everything at distance `≥ L` from `p` and pushes everything at
distance `< L` radially out to the sphere of radius `L` about `p`.

The main geometric facts are `pushGen_notMem_convex` (the push sends points outside a convex
set containing `p` to points outside it) and `continuousOn_pushGen` (the map is continuous
away from `p`).
-/

open Set Metric
open scoped Topology unitInterval

namespace Work.Geo.Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

/-- The radial profile of the push: it interpolates between `d` (at `s = 0`) and
`max d L` (at `s = 1`). -/
def radLam (s d L : ℝ) : ℝ := s * d + (1 - s) * max d L

/-- The parametrised radial push of `x` away from `p` with threshold `L`. -/
def pushGen (p : E) (L : ℝ) (s : ℝ) (x : E) : E :=
  p + (radLam s (dist x p) L / dist x p) • (x - p)

/-- The radial push: everything at distance `< L` from `p` is pushed out to distance `L`,
everything at distance `≥ L` is fixed. -/
def push (p : E) (L : ℝ) (x : E) : E := pushGen p L 0 x

/-! ## The one dimensional profile -/

theorem radLam_zero (d L : ℝ) : radLam 0 d L = max d L := by simp [radLam]

theorem radLam_one (d L : ℝ) : radLam 1 d L = d := by simp [radLam]

theorem radLam_nonneg {s d L : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hd : 0 ≤ d) :
    0 ≤ radLam s d L := by
  rw [radLam]
  have h1 : 0 ≤ s * d := mul_nonneg hs.1 hd
  have h2 : 0 ≤ (1 - s) * max d L := mul_nonneg (by linarith [hs.2]) (le_trans hd (le_max_left _ _))
  linarith

theorem le_radLam {s d L : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hd : 0 ≤ d) :
    d ≤ radLam s d L := by
  have hmax : d ≤ max d L := le_max_left _ _
  have h : 0 ≤ (1 - s) * (max d L - d) := mul_nonneg (by linarith [hs.2]) (by linarith)
  rw [radLam] at *
  nlinarith

theorem radLam_le_max {s d L : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hd : 0 ≤ d) :
    radLam s d L ≤ max d L := by
  have hmax : d ≤ max d L := le_max_left _ _
  have h1 : 0 ≤ 1 - s := by linarith [hs.2]
  have h2 : (1 - s) * d ≤ (1 - s) * max d L := mul_le_mul_of_nonneg_left hmax h1
  have h3 : s * d ≤ s * max d L := mul_le_mul_of_nonneg_left hmax hs.1
  rw [radLam]
  linarith

theorem radLam_le {s d L : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hd : d ≤ L) :
    radLam s d L ≤ L := by
  rw [radLam, max_eq_right hd]
  nlinarith [hs.1, hs.2]

/-! ## Basic properties of the push -/

theorem pushGen_self (p : E) (L s : ℝ) : pushGen p L s p = p := by
  simp [pushGen]

theorem pushGen_one (p : E) (L : ℝ) (x : E) : pushGen p L 1 x = x := by
  rw [pushGen, radLam_one]
  rcases eq_or_ne (dist x p) 0 with h | h
  · rw [h, dist_eq_zero.mp h]
    simp
  · rw [div_self h, one_smul]
    abel

theorem dist_pushGen {p x : E} {L s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hx : x ≠ p) :
    dist (pushGen p L s x) p = radLam s (dist x p) L := by
  have hd : 0 < dist x p := dist_pos.mpr hx
  have hne : dist x p ≠ 0 := ne_of_gt hd
  have hnn : 0 ≤ radLam s (dist x p) L := radLam_nonneg hs hd.le
  rw [pushGen, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hnn hd.le), ← dist_eq_norm]
  exact div_mul_cancel₀ _ hne

theorem pushGen_ne_p {p x : E} {L s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hx : x ≠ p) :
    pushGen p L s x ≠ p := by
  intro h
  have hd : 0 < dist x p := dist_pos.mpr hx
  have h1 : dist (pushGen p L s x) p = radLam s (dist x p) L := dist_pushGen hs hx
  rw [h, dist_self] at h1
  have h2 : dist x p ≤ radLam s (dist x p) L := le_radLam hs hd.le
  linarith

theorem dist_pushGen_le {p x : E} {L s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hx : x ≠ p)
    (hd : dist x p ≤ L) : dist (pushGen p L s x) p ≤ L := by
  rw [dist_pushGen hs hx]
  exact radLam_le hs hd

theorem dist_pushGen_ge {p x : E} {L s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hx : x ≠ p)
    (hd : L ≤ dist x p) : L ≤ dist (pushGen p L s x) p := by
  rw [dist_pushGen hs hx]
  exact le_trans hd (le_radLam hs (le_of_lt (dist_pos.mpr hx)))

theorem pushGen_id_of_le {p x : E} {L s : ℝ} (hL : 0 < L) (hd : L ≤ dist x p) :
    pushGen p L s x = x := by
  have hd' : 0 < dist x p := lt_of_lt_of_le hL hd
  have hne : dist x p ≠ 0 := ne_of_gt hd'
  have hmax : max (dist x p) L = dist x p := max_eq_left hd
  have hlam : radLam s (dist x p) L = dist x p := by
    rw [radLam, hmax]; ring
  rw [pushGen, hlam, div_self hne, one_smul]
  abel

/-- **The geometric core.**  If `C` is convex, `p ∈ C` and `x ∉ C`, then every point of the
ray from `p` through `x` beyond `x` is outside `C`; in particular the radial push of `x`
(with parameter `s ∈ [0,1]`) is outside `C`. -/
theorem pushGen_notMem_convex {C : Set E} (hC : Convex ℝ C) {p x : E} {L s : ℝ}
    (hp : p ∈ C) (hx : x ∉ C) (hs : s ∈ Icc (0 : ℝ) 1) : pushGen p L s x ∉ C := by
  intro hmem
  have hxp : x ≠ p := fun h => hx (h ▸ hp)
  have hd : 0 < dist x p := dist_pos.mpr hxp
  have hlam : dist x p ≤ radLam s (dist x p) L := le_radLam hs hd.le
  have hpos : 0 < radLam s (dist x p) L := lt_of_lt_of_le hd hlam
  have hcoef : dist x p / radLam s (dist x p) L * (radLam s (dist x p) L / dist x p) = 1 := by
    field_simp
  have hkey : p + (dist x p / radLam s (dist x p) L) • (pushGen p L s x - p) = x := by
    rw [pushGen, add_sub_cancel_left, smul_smul, hcoef, one_smul]
    abel
  have ht : dist x p / radLam s (dist x p) L ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hd.le hpos.le, (div_le_one hpos).mpr hlam⟩
  have hseg := hC.add_smul_sub_mem hp hmem ht
  rw [hkey] at hseg
  exact hx hseg

/-! ## The push -/

theorem dist_push {p x : E} {L : ℝ} (hx : x ≠ p) :
    dist (push p L x) p = max (dist x p) L := by
  rw [push, dist_pushGen (s := 0) ⟨le_refl 0, zero_le_one⟩ hx, radLam_zero]

theorem push_ne_p {p x : E} {L : ℝ} (hx : x ≠ p) : push p L x ≠ p :=
  pushGen_ne_p (s := 0) ⟨le_refl 0, zero_le_one⟩ hx

theorem push_id_of_le {p x : E} {L : ℝ} (hL : 0 < L) (hd : L ≤ dist x p) :
    push p L x = x :=
  pushGen_id_of_le (s := 0) hL hd

/-- The push of a point at distance `> L + r` from `p` is at distance `> r` from `c`. -/
theorem push_notMem_closedBall {p c x : E} {L r : ℝ} (hx : x ≠ p)
    (h : dist p c + r < L) : push p L x ∉ Metric.closedBall c r := by
  rw [Metric.mem_closedBall, not_le]
  have h1 : dist (push p L x) p = max (dist x p) L := dist_push hx
  have h2 : L ≤ dist (push p L x) p := by rw [h1]; exact le_max_right _ _
  have h3 : dist (push p L x) p ≤ dist (push p L x) c + dist c p := dist_triangle _ _ _
  rw [dist_comm c p] at h3
  linarith

/-- If `L = 3ρ/4` and `dist p c < ρ/4`, then any point of the push of an `x` with
`dist x p < L` is at distance `< ρ` from `c`. -/
theorem pushGen_mem_ball_of_lt {p c x : E} {L ρ s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hL0 : 0 ≤ L) (hpc : dist p c + L < ρ) (hd : dist x p < L) :
    dist (pushGen p L s x) c < ρ := by
  rcases eq_or_ne x p with rfl | hx
  · rw [pushGen_self]; linarith
  · have h1 : dist (pushGen p L s x) p ≤ L := dist_pushGen_le hs hx (le_of_lt hd)
    have h2 : dist (pushGen p L s x) c ≤ dist (pushGen p L s x) p + dist p c :=
      dist_triangle _ _ _
    linarith

/-! ## Continuity -/

theorem continuous_radLam (L : ℝ) : Continuous fun r : ℝ × ℝ => radLam r.1 r.2 L := by
  unfold radLam
  fun_prop

theorem continuousOn_radCoef (L : ℝ) :
    ContinuousOn (fun r : ℝ × ℝ => radLam r.1 r.2 L / r.2) (univ ×ˢ {d : ℝ | d ≠ 0}) := by
  refine ContinuousOn.div ((continuous_radLam L).continuousOn) continuousOn_snd ?_
  intro r hr
  exact hr.2

theorem continuousOn_pushGen (p : E) (L : ℝ) :
    ContinuousOn (fun q : ℝ × E => pushGen p L q.1 q.2) (univ ×ˢ {x : E | x ≠ p}) := by
  have hpair : Continuous fun q : ℝ × E => (q.1, dist q.2 p) :=
    continuous_fst.prodMk (continuous_snd.dist continuous_const)
  have hcoef : ContinuousOn (fun q : ℝ × E => radLam q.1 (dist q.2 p) L / dist q.2 p)
      (univ ×ˢ {x : E | x ≠ p}) :=
    (continuousOn_radCoef L).comp hpair.continuousOn (fun q hq => by
      simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_ofPred_eq] at hq ⊢
      exact dist_ne_zero.mpr hq)
  have hmain : ContinuousOn
      (fun q : ℝ × E => p + (radLam q.1 (dist q.2 p) L / dist q.2 p) • (q.2 - p))
      (univ ×ˢ {x : E | x ≠ p}) :=
    continuousOn_const.add (hcoef.smul (continuous_snd.sub continuous_const).continuousOn)
  simpa only [pushGen] using hmain

set_option maxHeartbeats 1000000 in
theorem continuousOn_pushGen_I (p : E) (L : ℝ) :
    ContinuousOn (fun q : I × E => pushGen p L (q.1 : ℝ) q.2) (univ ×ˢ {x : E | x ≠ p}) := by
  have hf : Continuous fun q : I × E => (((q.1 : ℝ), q.2) : ℝ × E) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_id.comp continuous_snd)
  refine (continuousOn_pushGen p L).comp hf.continuousOn ?_
  rintro ⟨s, x⟩ ⟨-, hx⟩
  exact ⟨trivial, hx⟩

end

end Work.Geo.Radial
