import Mathlib
import Submission.Work.Smooth.SphereJordan.PDU.Mobius
import Submission.Work.Smooth.SphereJordan.PDU.Root
import Submission.Work.Smooth.SphereJordan.PDU.Hurwitz
import Submission.Work.Smooth.SphereJordan.PDU.BijOnBallHomeo
import Submission.Work.Smooth.SphereJordan.hurwitz
import Submission.Work.Smooth.SphereJordan.montel
import Submission.Work.Smooth.SphereJordan.exists_seed
import Submission.Work.Smooth.SphereJordan.riemannMapping

/-!
# The planar classification: an open, bounded, simply connected `s ⊆ ℂ` is a disc

Target (fixed statement, proved below):

  `{s : Set ℂ} (hs : IsOpen s) (hne : s.Nonempty) (hb : Bornology.IsBounded s)
   (hsc : SimplyConnectedSpace s) → Nonempty (s ≃ₜ Metric.ball (0 : ℂ) 1)`

This is the topological Riemann mapping theorem (the Riemann mapping theorem gives a
*biholomorphism* `s → 𝔻 = Metric.ball 0 1`, hence a homeomorphism).  `hb` gives `s ≠ Set.univ`, and
`hsc` is `IsSimplyConnected s` definitionally (`IsSimplyConnected s := SimplyConnectedSpace s`).

The analytic development used here lives in the sibling directory `PDU/`; see
`PDU/README.md` and `PDU/STATUS.md` for the plan and the current state:

* `PDU/Mobius.lean` — the disc automorphisms `z ↦ (z - a)/(1 - star a * z)` (proved);
* `PDU/Root.lean` — `differentiableOn_of_pow_eq`: a continuous `n`-th root of a holomorphic
  function on an open set is holomorphic, i.e. `h z ^ n = F z`, `h` continuous, `h ≠ 0`
  ⟹ `h` holomorphic (proved).
* `PDU/Hurwitz.lean` — `le_norm_of_forall_mem_sphere_le` (minimum modulus principle) and
  `injOn_or_exists_forall_eq_of_tendstoLocallyUniformlyOn` (Hurwitz' theorem: a locally uniform
  limit of injective holomorphic functions is injective or constant) — proved, axiom-clean.
  The same statement was also proved independently, in parallel, as
  `Work.Smooth.SphereJordan.hurwitz` (`Submission/Work/Smooth/SphereJordan/hurwitz.lean`).

Remaining pieces (statements and Mathlib ingredients in `PDU/STATUS.md`):
Montel's theorem (complete, API-verified plan in `STATUS.md`), the seed map
`∃ f, MapsTo f s 𝔻 ∧ InjOn f s ∧ deriv f ≠ 0`,
the extremal argument (maximal `‖deriv g p‖` over injective holomorphic `g : s → 𝔻` with
`g p = 0`, attained by Montel, injective by Hurwitz, onto by the square root trick using
`PDU/Root.lean` and `PDU/Mobius.lean`), and the final homeomorphism from a biholomorphism
(`Equiv.toHomeomorphOfContinuousOpen` + the open mapping theorem).
-/

namespace Work.Smooth.SphereJordan

theorem planeDomain_homeo_unitBall {s : Set ℂ} (hs : IsOpen s) (hne : s.Nonempty)
    (hb : Bornology.IsBounded s) (hsc : SimplyConnectedSpace s) :
    Nonempty (s ≃ₜ Metric.ball (0 : ℂ) 1) := by
  -- a bounded set is not all of `ℂ`
  have hU : s ≠ Set.univ := by
    intro h
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hb
    obtain ⟨x, hx⟩ := hne
    have hy : x + (((|C| + 1 : ℝ)) : ℂ) ∈ s := by rw [h]; trivial
    have hd := hC hx hy
    have h1 : dist x (x + (((|C| + 1 : ℝ)) : ℂ)) = |C| + 1 := by
      have h2 : x - (x + (((|C| + 1 : ℝ)) : ℂ)) = -(((|C| + 1 : ℝ)) : ℂ) := by ring
      rw [dist_eq_norm, h2, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [abs_nonneg C])]
    have : |C| + 1 ≤ C := h1 ▸ hd
    linarith [le_abs_self C]
  -- simple connectivity gives connectivity
  have hsp : IsPreconnected s :=
    isPreconnected_iff_preconnectedSpace.mpr inferInstance
  obtain ⟨g, hg, hd⟩ := Work.Smooth.SphereJordan.riemannMapping hs hne hsc hU
  exact Work.Smooth.SphereJordan.bijOn_ball_homeo hs hsp hg hd

end Work.Smooth.SphereJordan
