import Mathlib
import Submission.Work.Drive.framedCInfSlices
import Submission.Work.Drive.exists_cInf_angle_lift
import Submission.Work.Drive.needleToCircleFamily

/-!
# Polar data of a planar star-shaped `C^∞` curve, and the needle-to-circle family

The framed polar machinery (`Work.Drive.framedCurve`, `Work.Drive.framedPolarGraph_unknotted`,
`Work.Drive.sweepNeedleToCircle_clauses`) consumes *polar data*: a positive `period`-periodic
radius function and a strictly increasing angle function.  A curve that is only *geometrically*
described (the thin lens at the low end of the chord sweep) has to be converted into that data
first.  This file does the conversion:

* `Work.Drive.polarRad`, `Work.Drive.polarCoord`, `Work.Drive.polarDir` — the radius and the two
  coordinates of the direction of `N t - c` in an orthonormal frame `(u, v)`;
* `Work.Drive.polarData_of_starShaped` — a planar, `C^∞`, `period`-periodic curve `N`, avoiding
  `c`, whose direction map is injective on one period (every ray from `c` meets the curve at most
  once: the curve is *star-shaped* about `c`) and whose angular velocity is positive, *is* a framed
  polar graph: there is a `C^∞` angle `psi` with `psi (t + period) = psi t + period`, `psi' > 0`
  and `N t = c + polarRad N c t • (cos (psi t) • u + sin (psi t) • v)`.  The angle is produced by
  `Work.Drive.exists_cInf_angle_lift` (the primitive of the angular velocity is the angle);
* `Work.Drive.needleToCircle_of_starShaped` — the resulting **low end of the chord sweep**: the
  curve `N` is joined to the round circle `t ↦ cos t • u + sin t • v` by a jointly `C¹` family of
  `C^∞` knots.

Every hypothesis here is a geometric condition on the curve `N` itself, so a proof that the
(flattened) needle is star-shaped — with a positively oriented parametrisation — closes the low
end of the sweep, feeding `Work.Drive.sweepNeedleToCircle_clauses` and hence the endgame
`Work.Drive.cInfKnotPath_to_unknotted`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- The radius of `N ·` about the point `c`. -/
def polarRad (N : ℝ → Space) (c : Space) (t : ℝ) : ℝ := ‖N t - c‖

/-- The first coordinate of the unit direction of `N t - c` in the direction `u`. -/
def polarCoord (N : ℝ → Space) (c u : Space) (t : ℝ) : ℝ :=
  inner ℝ (N t - c) u / ‖N t - c‖

/-- The direction of `N t - c` in the orthonormal frame `(u, v)`, as a pair of coordinates. -/
def polarDir (N : ℝ → Space) (c u v : Space) (t : ℝ) : ℝ × ℝ :=
  (polarCoord N c u t, polarCoord N c v t)

lemma polarRad_pos {N : ℝ → Space} (c : Space) (hne : ∀ t : ℝ, N t ≠ c) (t : ℝ) :
    0 < polarRad N c t := norm_pos_iff.mpr (sub_ne_zero.mpr (hne t))

lemma polarRad_smooth {N : ℝ → Space} (c : Space) (hN : ContDiff ℝ cInfT N)
    (hne : ∀ t : ℝ, N t ≠ c) : ContDiff ℝ cInfT (polarRad N c) :=
  ContDiff.norm ℝ (hN.sub (contDiff_const (c := c))) (fun t => sub_ne_zero.mpr (hne t))

lemma polarRad_periodic {N : ℝ → Space} (c : Space) (hNper : Function.Periodic N period) :
    Function.Periodic (polarRad N c) period := by
  intro t
  simp only [polarRad]
  rw [hNper t]

lemma polarCoord_smooth {N : ℝ → Space} (c u : Space) (hN : ContDiff ℝ cInfT N)
    (hne : ∀ t : ℝ, N t ≠ c) : ContDiff ℝ cInfT (polarCoord N c u) :=
  ContDiff.div (ContDiff.inner ℝ (hN.sub (contDiff_const (c := c))) contDiff_const)
    (polarRad_smooth c hN hne) (fun t => ne_of_gt (polarRad_pos c hne t))

/-- **The plane Pythagoras identity.**  A vector of the plane spanned by an orthonormal pair
`(u, v)` has squared norm the sum of the squares of its coordinates. -/
lemma norm_sq_eq_coords {p u v : Space} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0)
    (hp : p = inner ℝ p u • u + inner ℝ p v • v) :
    ‖p‖ ^ 2 = (inner ℝ p u) ^ 2 + (inner ℝ p v) ^ 2 := by
  have hnorm : ‖p‖ ^ 2 = inner ℝ p p := (real_inner_self_eq_norm_sq p).symm
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm]; exact huv
  rw [hnorm, hp]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, huu, hvv,
    huv, hvu, RCLike.conj_to_real, mul_one, mul_zero, add_zero, zero_add]
  ring

/-- **Polar data of a planar star-shaped curve.**  If `N` is a `C^∞`, `period`-periodic curve in
the plane `c + ℝu + ℝv` of the orthonormal pair `(u, v)`, avoiding `c`, with `polarDir N c u v`
injective on one period, equal to `(1, 0)` at `0` and with everywhere positive angular velocity,
then `N` is a framed polar graph about `c` with a `C^∞` angle of positive derivative. -/
theorem polarData_of_starShaped {N : ℝ → Space} {c u v : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hN : ContDiff ℝ cInfT N) (hNper : Function.Periodic N period)
    (hplane : ∀ t : ℝ,
      N t - c = inner ℝ (N t - c) u • u + inner ℝ (N t - c) v • v)
    (hne : ∀ t : ℝ, N t ≠ c)
    (h0 : polarDir N c u v 0 = (1, 0))
    (hinj : Set.InjOn (polarDir N c u v) (Set.Ico (0 : ℝ) period))
    (hpos : ∀ t : ℝ,
      0 < polarCoord N c u t * deriv (polarCoord N c v) t
        - polarCoord N c v t * deriv (polarCoord N c u) t) :
    ∃ psi : ℝ → ℝ, ContDiff ℝ cInfT psi ∧ StrictMono psi ∧ psi 0 = 0 ∧
      (∀ t : ℝ, psi (t + period) = psi t + period) ∧ (∀ t : ℝ, 0 < deriv psi t) ∧
      (∀ t : ℝ, N t = c + polarRad N c t • (Real.cos (psi t) • u + Real.sin (psi t) • v)) := by
  have ha_sm : ContDiff ℝ cInfT (polarCoord N c u) := polarCoord_smooth c u hN hne
  have hb_sm : ContDiff ℝ cInfT (polarCoord N c v) := polarCoord_smooth c v hN hne
  have hnpos : ∀ t : ℝ, polarRad N c t ≠ 0 := fun t => ne_of_gt (polarRad_pos c hne t)
  -- the norm relation
  have hnorm : ∀ t : ℝ, polarCoord N c u t ^ 2 + polarCoord N c v t ^ 2 = 1 := by
    intro t
    have hp := norm_sq_eq_coords hu hv huv (hplane t)
    have hlt : polarRad N c t ≠ 0 := hnpos t
    have hlam2 : polarRad N c t ^ 2
        = (inner ℝ (N t - c) u) ^ 2 + (inner ℝ (N t - c) v) ^ 2 := by
      rw [polarRad]; exact hp
    have ha' : polarCoord N c u t = inner ℝ (N t - c) u / polarRad N c t := by
      rw [polarCoord, polarRad]
    have hb' : polarCoord N c v t = inner ℝ (N t - c) v / polarRad N c t := by
      rw [polarCoord, polarRad]
    rw [ha', hb', div_pow, div_pow, ← add_div,
      div_eq_one_iff_eq (by positivity), hlam2]
  have h0' : polarCoord N c u 0 = 1 ∧ polarCoord N c v 0 = 0 := by
    have h := h0
    rw [polarDir] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hper' : ∀ t : ℝ, polarCoord N c u (t + period) = polarCoord N c u t ∧
      polarCoord N c v (t + period) = polarCoord N c v t := by
    intro t
    constructor <;>
      · rw [polarCoord, polarCoord, hNper t]
  have hinj' : Set.InjOn (fun t : ℝ => (polarCoord N c u t, polarCoord N c v t))
      (Set.Ico (0 : ℝ) period) := hinj
  have hpos' : ∀ t : ℝ, 0 < polarCoord N c u t * deriv (polarCoord N c v) t
      - polarCoord N c v t * deriv (polarCoord N c u) t := hpos
  obtain ⟨psi, hpsi_sm, hpsi0, hpsishift, hpsisincos⟩ :=
    exists_cInf_angle_lift ha_sm hb_sm hnorm h0' hper' hinj' hpos'
  have hcos : ∀ t : ℝ, polarCoord N c u t = Real.cos (psi t) := fun t => (hpsisincos t).1
  have hsin : ∀ t : ℝ, polarCoord N c v t = Real.sin (psi t) := fun t => (hpsisincos t).2
  have hpsi_diff : ∀ t : ℝ, DifferentiableAt ℝ psi t :=
    fun t => ((hpsi_sm.differentiable cInfT_ne_zero).differentiableAt)
  -- the two chain rules
  have hderiv_cos : ∀ t : ℝ, deriv (fun s : ℝ => Real.cos (psi s)) t
      = -Real.sin (psi t) * deriv psi t := by
    intro t
    exact (((Real.hasDerivAt_cos (psi t)).comp t (hpsi_diff t).hasDerivAt)).deriv
  have hderiv_sin : ∀ t : ℝ, deriv (fun s : ℝ => Real.sin (psi s)) t
      = Real.cos (psi t) * deriv psi t := by
    intro t
    exact (((Real.hasDerivAt_sin (psi t)).comp t (hpsi_diff t).hasDerivAt)).deriv
  -- the derivative of the angle is the angular velocity
  have hpsideriv : ∀ t : ℝ, deriv psi t
      = polarCoord N c u t * deriv (polarCoord N c v) t
        - polarCoord N c v t * deriv (polarCoord N c u) t := by
    intro t
    have hda : deriv (polarCoord N c u) t = deriv (fun s : ℝ => Real.cos (psi s)) t := by
      rw [show polarCoord N c u = fun s : ℝ => Real.cos (psi s) from
        funext fun s => hcos s]
    have hdb : deriv (polarCoord N c v) t = deriv (fun s : ℝ => Real.sin (psi s)) t := by
      rw [show polarCoord N c v = fun s : ℝ => Real.sin (psi s) from
        funext fun s => hsin s]
    rw [hda, hdb, hderiv_cos t, hderiv_sin t, hcos t, hsin t]
    have hs : Real.sin (psi t) ^ 2 + Real.cos (psi t) ^ 2 = 1 := Real.sin_sq_add_cos_sq (psi t)
    have hexp : Real.cos (psi t) * (Real.cos (psi t) * deriv psi t)
        - Real.sin (psi t) * (-Real.sin (psi t) * deriv psi t)
        = (Real.sin (psi t) ^ 2 + Real.cos (psi t) ^ 2) * deriv psi t := by ring
    rw [hexp, hs, one_mul]
  refine ⟨psi, hpsi_sm, ?_, hpsi0, hpsishift, ?_, ?_⟩
  · exact strictMono_of_deriv_pos (fun t => by rw [hpsideriv t]; exact hpos t)
  · intro t
    rw [hpsideriv t]
    exact hpos t
  · intro t
    have h1 : inner ℝ (N t - c) u = polarRad N c t * Real.cos (psi t) := by
      have ha : inner ℝ (N t - c) u / polarRad N c t = Real.cos (psi t) := by
        change polarCoord N c u t = Real.cos (psi t)
        exact hcos t
      calc inner ℝ (N t - c) u
          = (inner ℝ (N t - c) u / polarRad N c t) * polarRad N c t :=
            (div_mul_cancel₀ _ (hnpos t)).symm
        _ = Real.cos (psi t) * polarRad N c t := by rw [ha]
        _ = polarRad N c t * Real.cos (psi t) := by ring
    have h2 : inner ℝ (N t - c) v = polarRad N c t * Real.sin (psi t) := by
      have hb : inner ℝ (N t - c) v / polarRad N c t = Real.sin (psi t) := by
        change polarCoord N c v t = Real.sin (psi t)
        exact hsin t
      calc inner ℝ (N t - c) v
          = (inner ℝ (N t - c) v / polarRad N c t) * polarRad N c t :=
            (div_mul_cancel₀ _ (hnpos t)).symm
        _ = Real.sin (psi t) * polarRad N c t := by rw [hb]
        _ = polarRad N c t * Real.sin (psi t) := by ring
    have key : N t - c = polarRad N c t • (Real.cos (psi t) • u + Real.sin (psi t) • v) := by
      rw [hplane t, h1, h2, ← smul_smul, ← smul_smul, ← smul_add]
    calc N t = (N t - c) + c := (sub_add_cancel _ _).symm
      _ = polarRad N c t • (Real.cos (psi t) • u + Real.sin (psi t) • v) + c := by rw [key]
      _ = c + polarRad N c t • (Real.cos (psi t) • u + Real.sin (psi t) • v) := by rw [add_comm]

/-- **The low end of the chord sweep, from the star-shapedness of the needle.**  A planar, `C^∞`,
`period`-periodic star-shaped curve `N` (as in `Work.Drive.polarData_of_starShaped`) is joined to
the round circle `t ↦ cos t • u + sin t • v` by a jointly `C¹` family of `C^∞` knots. -/
theorem needleToCircle_of_starShaped {N : ℝ → Space} {c u v : Space}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hN : ContDiff ℝ cInfT N) (hNper : Function.Periodic N period)
    (hplane : ∀ t : ℝ,
      N t - c = inner ℝ (N t - c) u • u + inner ℝ (N t - c) v • v)
    (hne : ∀ t : ℝ, N t ≠ c)
    (h0 : polarDir N c u v 0 = (1, 0))
    (hinj : Set.InjOn (polarDir N c u v) (Set.Ico (0 : ℝ) period))
    (hpos : ∀ t : ℝ,
      0 < polarCoord N c u t * deriv (polarCoord N c v) t
        - polarCoord N c v t * deriv (polarCoord N c u) t) :
    ∃ F : ℝ → ℝ → Space,
      ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
      (∀ s t : ℝ, F (t + period) s = F t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
      (∀ t : ℝ, F t 0 = N t) ∧
      (∀ t : ℝ, F t 1 = Real.cos t • u + Real.sin t • v) := by
  obtain ⟨psi, hpsi_sm, hpsi_mono, hpsi0, hpsishift, hpsideriv, hrep⟩ :=
    polarData_of_starShaped hu hv huv hN hNper hplane hne h0 hinj hpos
  obtain ⟨hjoint, hper, hslice, hzero, hone⟩ :=
    sweepNeedleToCircle_clauses hu hv huv (polarRad_smooth c hN hne) hpsi_sm
      (polarRad_pos c hne) (polarRad_periodic c hNper) hpsi_mono hpsishift hpsideriv
  refine ⟨fun t s => framedCurve (polarRad N c) psi c u v s t, hjoint, ?_, ?_, ?_, ?_⟩
  · intro s t
    exact hper s t
  · intro s hs
    exact hslice s hs
  · intro t
    show framedCurve (polarRad N c) psi c u v 0 t = N t
    rw [hzero t]
    exact (hrep t).symm
  · intro t
    show framedCurve (polarRad N c) psi c u v 1 t = Real.cos t • u + Real.sin t • v
    exact hone t

end Work.Drive
