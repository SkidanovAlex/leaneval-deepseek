import Mathlib
import Submission.Work.Smooth.Jordan.JordanIndex
import Submission.Work.Smooth.Jordan.Circle
import Submission.Work.Smooth.Jordan.unitCircle_wind_inside
import Submission.Work.Smooth.Jordan.unitCircle_wind_outside
import Submission.Work.Smooth.Jordan.unitCircle_isSimple

/-!
# The standard circle satisfies the full classical plane input

We construct a `PlaneJordanSchoenflies` datum for the positively oriented unit circle
`unitCircle : t ↦ e^{it}`.  The two sides are the exterior and the interior of the closed unit
disc,

* `U = {z : ℂ | 1 < ‖z‖}` — the outside,
* `V = {z : ℂ | ‖z‖ < 1}` — the inside,

the spanning embedding is the inclusion `Disc ↪ ℂ` (whose range is the closed unit disc `𝔻`, the
closure of `V`), and the index values are the classical ones: `ind unitCircle x = 0` for `‖x‖ > 1`
(`unitCircle_wind_outside`) and `|ind unitCircle x| = 1` for `‖x‖ < 1` (`unitCircle_wind_inside`).

The only topological input beyond the winding computations is the preconnectedness of the exterior
`{z : ℂ | 1 < ‖z‖}`, which is proved here by exhibiting it as a union of preconnected sets with a
common point: the sphere of radius `2` together with the open rays through its points starting at
distance `1`.
-/

set_option linter.unnecessarySimpa false

open Set
open Classical

namespace Work.Smooth.Jordan

noncomputable section

/-- **The exterior of the closed unit disc is preconnected.**  Writing
`{z : ℂ | 1 < ‖z‖} = ⋃ y ∈ S(0,2), C_y` where `C_y` is the open ray starting at `y/2` through `y`,
every set `C_y ∪ S(0,2)` is preconnected (the union of the preconnected ray `C_y` and the
preconnected sphere `S(0,2)`, which meet at `y`), and all of them contain the sphere `S(0,2)`, so
their union is preconnected. -/
theorem isPreconnected_exterior_unitBall : IsPreconnected {z : ℂ | 1 < ‖z‖} := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hS : IsPreconnected (Metric.sphere (0 : ℂ) 2) := isPreconnected_sphere hrank 0 2
  have hCpre : ∀ y : Metric.sphere (0 : ℂ) 2,
      IsPreconnected ((fun t : ℝ => t • (y : ℂ)) '' Set.Ioi (1 / 2 : ℝ)) := fun y =>
    isPreconnected_Ioi.image _ (continuous_id.smul continuous_const).continuousOn
  have hunion : (⋃ y : Metric.sphere (0 : ℂ) 2,
      ((fun t : ℝ => t • (y : ℂ)) '' Set.Ioi (1 / 2 : ℝ)) ∪ Metric.sphere (0 : ℂ) 2)
      = {z : ℂ | 1 < ‖z‖} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_image, Set.mem_Ioi, Set.mem_ofPred_eq,
      Metric.mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩ | hz⟩
      · have hy2 : ‖(y : ℂ)‖ = 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using y.2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t), hy2]
        linarith
      · linarith
    · intro hz
      have hzpos : (0 : ℝ) < ‖z‖ := by linarith
      have h2z : ‖(2 / ‖z‖) • z‖ = 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hzpos)]
        field_simp
      refine ⟨⟨(2 / ‖z‖) • z, by rw [Metric.mem_sphere, dist_zero_right]; exact h2z⟩,
        Or.inl ⟨‖z‖ / 2, by linarith, ?_⟩⟩
      rw [smul_smul]
      have hcoef : ‖z‖ / 2 * (2 / ‖z‖) = 1 := by field_simp
      rw [hcoef, one_smul]
  rw [← hunion]
  refine isPreconnected_iUnion ?_ (fun y => ?_)
  · refine ⟨(2 : ℂ), ?_⟩
    simp only [mem_iInter]
    intro y
    right
    rw [Metric.mem_sphere, dist_zero_right]; norm_num
  · refine IsPreconnected.union (y : ℂ) ?_ ?_ (hCpre y) hS
    · exact ⟨1, by norm_num, by simp⟩
    · simpa [Metric.mem_sphere, dist_zero_right] using y.2

/-- The inclusion of the closed model disc `𝔻` into `ℂ`, as a spanning embedding. -/
private def discEmbedding : C(Disc, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The range of the inclusion `𝔻 ↪ ℂ` is the closed unit disc. -/
private theorem range_discEmbedding : Set.range discEmbedding = Metric.closedBall (0 : ℂ) 1 := by
  show Set.range (Subtype.val : Disc → ℂ) = Metric.closedBall (0 : ℂ) 1
  rw [Subtype.range_coe]

/-- The closure of the open unit disc is the closed unit disc. -/
private theorem closure_ball_zero_one :
    closure ({z : ℂ | ‖z‖ < 1} : Set ℂ) = Metric.closedBall (0 : ℂ) 1 := by
  have hVball : ({z : ℂ | ‖z‖ < 1} : Set ℂ) = Metric.ball (0 : ℂ) 1 := by
    ext z; simp [Metric.mem_ball, dist_zero_right]
  rw [hVball, closure_ball (0 : ℂ) one_ne_zero]

/-- **The standard unit circle satisfies the full classical input of the plane.**  The Jordan
separation is by the outside and inside of the closed unit disc, and the classical input of
`PlaneJordanSchoenflies` is the explicit winding computation. -/
theorem unitCircle_jordanSchoenflies : Nonempty (PlaneJordanSchoenflies unitCircle) := by
  have hVpre : IsPreconnected ({z : ℂ | ‖z‖ < 1} : Set ℂ) := by
    have hVball : ({z : ℂ | ‖z‖ < 1} : Set ℂ) = Metric.ball (0 : ℂ) 1 := by
      ext z; simp [Metric.mem_ball, dist_zero_right]
    rw [hVball]; exact Metric.isPreconnected_ball
  refine ⟨{
    sep := {
      simple := unitCircle_isSimple
      U := {z : ℂ | 1 < ‖z‖}
      V := {z : ℂ | ‖z‖ < 1}
      isOpen_U := isOpen_lt continuous_const continuous_norm
      isOpen_V := isOpen_lt continuous_norm continuous_const
      preconn_U := isPreconnected_exterior_unitBall
      preconn_V := hVpre
      nonempty_U := ⟨((2 : ℝ) : ℂ), by
        change (1 : ℝ) < ‖((2 : ℝ) : ℂ)‖
        rw [Complex.norm_real, Real.norm_eq_abs]; norm_num⟩
      nonempty_V := ⟨0, by change ‖(0 : ℂ)‖ < 1; norm_num⟩
      disjoint_UV := by
        rw [Set.disjoint_left]
        intro z hzU hzV
        change 1 < ‖z‖ at hzU
        change ‖z‖ < 1 at hzV
        linarith
      union_eq := by
        ext z
        simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
        rw [unitCircle_trace, Metric.mem_sphere, dist_zero_right]
        constructor
        · rintro (h | h) hc <;> linarith
        · intro hc; exact lt_or_gt_of_ne (Ne.symm hc)
      bounded_V := by
        refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 1)) ?_
        intro z hz
        change ‖z‖ < 1 at hz
        rw [Metric.mem_closedBall, dist_zero_right]
        linarith }
    ind_eq_zero_U := by
      intro x hx
      change 1 < ‖x‖ at hx
      have hw : wind unitCircle x = 0 := unitCircle_wind_outside x hx
      have hint : ∃ k : ℤ, wind unitCircle x = (k : ℂ) := ⟨0, by rw [hw]; norm_num⟩
      have h := ind_spec unitCircle hint
      rw [hw] at h
      exact_mod_cast h
    ind_abs_eq_one_V := by
      intro x hx
      change ‖x‖ < 1 at hx
      have hw : wind unitCircle x = 1 := unitCircle_wind_inside x hx
      have hint : ∃ k : ℤ, wind unitCircle x = (k : ℂ) := ⟨1, by rw [hw]; norm_num⟩
      have h := ind_spec unitCircle hint
      rw [hw] at h
      have hind : ind unitCircle x = 1 := by exact_mod_cast h
      rw [hind]; norm_num
    e := discEmbedding
    inj := fun a b h => Subtype.coe_injective h
    boundary := by
      intro θ
      show ((circlePoint θ : Disc) : ℂ) = unitCircle.γ θ
      rw [circlePoint_coe, unitCircle_apply]
    range_e := by
      rw [range_discEmbedding]
      exact (closure_ball_zero_one).symm }⟩

end

end Work.Smooth.Jordan
