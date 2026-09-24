import Submission.Work.Mori.PeriodHom
import Submission.Work.Mori.Circle
import Submission.Work.Mori.harmonicOnX_log_norm_sub_center
import Submission.Work.Mori.holomorphicOnX_opens_sub_const
import Submission.Work.Mori.not_hasArg_circle
import Submission.Work.Mori.exists_sphere_eq_empty
import Submission.Work.Mori.Polar
import Submission.Work.Mori.hasArg_of_holomorphic_conjugate
import Submission.Work.Mori.exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero
import Submission.Work.Parabolic.harmonicOnX_comp_biholomorph
import Submission.Work.Parabolic.holomorphicOnX_comp_biholomorph

/-!
# The winding-number homomorphism, and the winding obstruction in its classical form

The requested parabolic case of uniformization quotes Mori's theorem and then argues: if `X ≃ₘ ℂ ∖ E`
with `E` polar and non-empty, then "the winding number of a loop in `ℂ ∖ E` around `p ∈ E` is a well
defined homomorphism `π₁(ℂ ∖ E) → ℤ → ℝ` which is non-trivial", contradicting
`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)`.

This module formalises exactly that, in the form of the library's period homomorphism of the conjugate
étale space (`Work.Mori.conjPeriodHomOf`):

* `Work.Mori.argumentPeriodHom U p hp x₀ : Additive (FundamentalGroup U x₀) →+ ℝ` — the winding
  (argument-period) homomorphism of a plane domain around an exterior point `p`, obtained from the
  harmonic function `z ↦ log ‖z - p‖` (`Work.Mori.harmonicOnX_log_norm_sub_center`);
* `Work.Mori.argumentPeriodHom_ne_zero` — it is non-trivial as soon as `U` contains a circle around
  `p`: if it vanished, the conjugate of `log ‖z - p‖` would be global
  (`Work.Mori.exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero`), the argument of `z - p`
  would be periodic along every loop (`Work.Mori.hasArg_of_holomorphic_conjugate`), contradicting
  `Work.Mori.not_hasArg_circle`;
* `Work.Mori.exists_nontrivial_hom_of_diffeomorph_of_isPolar_of_nonempty` — the classical form of the
  winding obstruction: a surface biholomorphic to the complement of a non-empty polar set has a
  non-trivial homomorphism of its fundamental group to `ℝ`.

(The `False`-valued form of the same obstruction, which is what the parabolic branch consumes, is
`Work.Mori.not_diffeomorph_of_isPolar_of_nonempty` in `Argument.lean`.)
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

/-- **The argument-period (winding) homomorphism of a plane domain around an exterior point.**  Its
value on a loop is the drift of the argument of `z - p` along that loop; it is the monodromy
homomorphism of the conjugate of `log ‖z - p‖`
(`Work.Mori.conjPeriodHomOf` applied to `Work.Mori.harmonicOnX_log_norm_sub_center`). -/
noncomputable def argumentPeriodHom (U : TopologicalSpace.Opens ℂ) (p : ℂ)
    (hp : p ∉ (U : Set ℂ)) (x₀ : U) : Additive (FundamentalGroup U x₀) →+ ℝ :=
  conjPeriodHomOf (harmonicOnX_log_norm_sub_center U p hp) x₀

/-- **A circle winds once around every point strictly inside it.**  The argument of `z - p` along
`circle c R` is not periodic when `‖p - c‖ < R`.

The loops `t ↦ circle (c + φ s · (p - c)) (R - φ s · ‖p - c‖) t - p`, where `φ s = max 0 (min 1 s)`
clamps the deformation parameter to `[0,1]`, form a nowhere-zero homotopy between the curve
`circle c R · - p` and the circle of centre `p`; the homotopy invariance of the vanishing of the
winding number (`Commons.Topology.Winding.hasArg_homotopy_invariant`) transfers the failure of
`Work.Mori.not_hasArg_circle` at the centre. -/
theorem not_hasArg_circle_of_norm_sub_lt {c p : ℂ} {R : ℝ} (hR : 0 < R) (hp : ‖p - c‖ < R) :
    ¬ Commons.Topology.Winding.HasArg (circle c R) p := by
  set u : ℝ := ‖p - c‖ with hu
  have hu_lt : u < R := hp
  set φ : ℝ → ℝ := fun s => max 0 (min 1 s) with hφdef
  have hφcont : Continuous φ := by rw [hφdef]; fun_prop
  have hφmem : ∀ s : ℝ, 0 ≤ φ s ∧ φ s ≤ 1 := by
    intro s
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  have hφ1 : φ 1 = 1 := by simp [hφdef]
  set F : ℝ × ℝ → ℂ := fun q =>
    circle (c + ((φ q.2 : ℝ) : ℂ) * (p - c)) (R - φ q.2 * u) q.1 - p with hFdef
  have hFcont : Continuous F := by
    rw [hFdef]
    simp only [circle]
    fun_prop
  have hFper : ∀ t s : ℝ, F (t + 1, s) = F (t, s) := by
    intro t s
    show circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) (t + 1) - p
        = circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) t - p
    rw [circle_periodic]
  have hnz : ∀ t s : ℝ, F (t, s) ≠ 0 := by
    intro t s
    obtain ⟨hs0, hs1⟩ := hφmem s
    have h2 : ‖circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) t
        - (c + ((φ s : ℝ) : ℂ) * (p - c))‖ = R - φ s * u :=
      norm_circle_sub _ (by nlinarith) t
    have h3 : ‖p - (c + ((φ s : ℝ) : ℂ) * (p - c))‖ = (1 - φ s) * u := by
      have hsplit : p - (c + ((φ s : ℝ) : ℂ) * (p - c)) = (1 - (φ s : ℂ)) * (p - c) := by ring
      have hcast : (1 : ℂ) - ((φ s : ℝ) : ℂ) = (((1 - φ s : ℝ)) : ℂ) := by push_cast; ring
      have h1φ : (0 : ℝ) ≤ 1 - φ s := by linarith [hs1]
      have hnorm : ‖(1 : ℂ) - ((φ s : ℝ) : ℂ)‖ = 1 - φ s := by
        rw [hcast,
          show (‖(((1 - φ s : ℝ)) : ℂ)‖ : ℝ) = |(1 - φ s : ℝ)| from
            RCLike.norm_ofReal (1 - φ s),
          abs_of_nonneg h1φ]
      rw [hsplit, norm_mul, hnorm, ← hu]
    have hlow : 0 < ‖circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) t - p‖ := by
      have hkey : R - u ≤ ‖circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) t - p‖ := by
        calc R - u = (R - φ s * u) - ((1 - φ s) * u) := by ring
          _ = ‖circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) t
                - (c + ((φ s : ℝ) : ℂ) * (p - c))‖
              - ‖p - (c + ((φ s : ℝ) : ℂ) * (p - c))‖ := by rw [h2, h3]
          _ ≤ ‖(circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) t
                - (c + ((φ s : ℝ) : ℂ) * (p - c)))
                - (p - (c + ((φ s : ℝ) : ℂ) * (p - c)))‖ := norm_sub_norm_le _ _
          _ = ‖circle (c + ((φ s : ℝ) : ℂ) * (p - c)) (R - φ s * u) t - p‖ := by
                congr 1
                ring
      linarith
    rw [hFdef]
    simp only []
    intro hzero
    rw [hzero, norm_zero] at hlow
    exact lt_irrefl _ hlow
  have h := Commons.Topology.Winding.hasArg_homotopy_invariant hFcont hFper hnz
  have h0 : (fun t : ℝ => F (t, 0)) = fun t : ℝ => circle c R t - p := by
    funext t
    simp only [hFdef, Prod.snd_zero, hφ0]
    push_cast
    ring_nf
  have h1 : (fun t : ℝ => F (t, 1)) = fun t : ℝ => circle p (R - u) t - p := by
    funext t
    simp only [hFdef, Prod.snd_one, hφ1]
    push_cast
    ring_nf
  rw [h0, h1] at h
  intro hcon
  have hcon' : Commons.Topology.Winding.HasArg (fun t : ℝ => circle c R t - p) 0 :=
    (hasArg_shift (circle c R) p).mpr hcon
  have h1' : Commons.Topology.Winding.HasArg (fun t : ℝ => circle p (R - u) t - p) 0 :=
    h.mp hcon'
  exact not_hasArg_circle p (R - u) (by linarith)
    ((hasArg_shift (circle p (R - u)) p).mp h1')

/-- **The winding homomorphism does not vanish as soon as some loop of the domain has no periodic
argument around `p`** — i.e. as soon as some loop winds (non-trivially) around `p`.

If the homomorphism vanished, the conjugate of `log ‖z - p‖` would be single-valued on `U`
(`Work.Mori.exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero`), so the argument of `z - p`
would be periodic along every loop of `U` (`Work.Mori.hasArg_of_holomorphic_conjugate`), in
particular along the loop given. -/
theorem argumentPeriodHom_ne_zero_of_not_hasArg (U : TopologicalSpace.Opens ℂ) [ConnectedSpace U]
    (p : ℂ) (hp : p ∉ (U : Set ℂ))
    {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f 1)
    (hval : ∀ t : ℝ, f t ∈ (U : Set ℂ))
    (hno : ¬ Commons.Topology.Winding.HasArg f p) (x₀ : U) :
    argumentPeriodHom U p hp x₀ ≠ 0 := by
  intro hzero
  obtain ⟨F, hFhol, hFre⟩ :=
    exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero
      (harmonicOnX_log_norm_sub_center U p hp) x₀ hzero
  set γ : ℝ → U := fun t => ⟨f t, hval t⟩ with hγdef
  have hγcont : Continuous γ := hf.subtype_mk hval
  have hγper : ∀ t : ℝ, γ (t + 1) = γ t := fun t => Subtype.ext (hper t)
  have hGhol : Submission.HolomorphicOnX (fun z : U => (z : ℂ) - p) Set.univ :=
    holomorphicOnX_opens_sub_const U p
  have hGne : ∀ z : U, (z : ℂ) - p ≠ 0 := by
    intro z h
    have hzp : (z : ℂ) = p := sub_eq_zero.mp h
    exact hp (hzp ▸ z.2)
  have harg := hasArg_of_holomorphic_conjugate hGhol hGne hFhol hFre hγcont hγper
  have hfun : (fun t : ℝ => (fun z : U => (z : ℂ) - p) (γ t)) = fun t : ℝ => f t - p := by
    funext t
    simp [hγdef]
  rw [hfun] at harg
  exact hno ((hasArg_shift f p).mp harg)

/-- **The winding homomorphism of a plane domain with a hole is non-trivial**: if `U` contains the
circle of radius `r > 0` around a point `p ∉ U`, then `argumentPeriodHom U p hp x₀ ≠ 0`.

This is `Work.Mori.argumentPeriodHom_ne_zero_of_not_hasArg` applied to the circle, which winds once
around its centre (`Work.Mori.not_hasArg_circle`). -/
theorem argumentPeriodHom_ne_zero (U : TopologicalSpace.Opens ℂ) [ConnectedSpace U] (p : ℂ)
    (hp : p ∉ (U : Set ℂ))
    (hcircle : ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - p‖ = r → z ∈ (U : Set ℂ)) (x₀ : U) :
    argumentPeriodHom U p hp x₀ ≠ 0 := by
  obtain ⟨r, hr, hcirc⟩ := hcircle
  refine argumentPeriodHom_ne_zero_of_not_hasArg U p hp (continuous_circle p r)
    (circle_periodic p r) (fun t => hcirc _ (norm_circle_sub p hr.le t)) ?_ x₀
  exact not_hasArg_circle p r hr

/-- **The winding homomorphism is non-trivial for a loop surrounding an exterior point.**  If `U`
contains the circle of centre `c` and radius `R`, and `p ∉ U` lies strictly inside that circle, then
`argumentPeriodHom U p hp x₀ ≠ 0`: the circle winds once around every interior point
(`Work.Mori.not_hasArg_circle_of_norm_sub_lt`).

This is the classical statement that a plane domain has a non-trivial homomorphism `π₁ → ℝ` as soon as
it surrounds a point it does not contain. -/
theorem argumentPeriodHom_ne_zero_of_mem_ball (U : TopologicalSpace.Opens ℂ) [ConnectedSpace U]
    (c p : ℂ) (R : ℝ) (hpU : p ∉ (U : Set ℂ)) (hR : 0 < R)
    (hcircle : ∀ t : ℝ, circle c R t ∈ (U : Set ℂ)) (hp : ‖p - c‖ < R) (x₀ : U) :
    argumentPeriodHom U p hpU x₀ ≠ 0 :=
  argumentPeriodHom_ne_zero_of_not_hasArg U p hpU (continuous_circle c R) (circle_periodic c R)
    hcircle (not_hasArg_circle_of_norm_sub_lt hR hp) x₀

/-- **The classical form of the winding obstruction.**  If `X` is biholomorphic to the complement of
a *non-empty* polar closed set, then `X` has a non-trivial homomorphism of its fundamental group to
`ℝ` (the winding number around a point of the exceptional set).  Equivalently, such an `X` can never
satisfy `Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)`.

The proof transports the harmonic function `log ‖· - p‖` and the winding homomorphism of
`Work.Mori.argumentPeriodHom` from the plane domain to `X` along the biholomorphism; its
non-vanishing is invariant because the argument of the circle around `p` is transported as well. -/
theorem exists_nontrivial_hom_of_diffeomorph_of_isPolar_of_nonempty
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : TopologicalSpace.Opens ℂ} (hpolar : IsPolar ((U : Set ℂ)ᶜ))
    (hne : ((U : Set ℂ)ᶜ).Nonempty)
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X U
      ((⊤ : ℕ∞) : WithTop ℕ∞)) :
    ∃ (x : X) (f : Additive (FundamentalGroup X x) →+ ℝ), f ≠ 0 := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, hrK⟩ := hpolar.exists_sphere_eq_empty U.isOpen.isClosed_compl hp
  have hcirc : ∀ z : ℂ, ‖z - p‖ = r → z ∈ (U : Set ℂ) := by
    intro z hz
    by_contra h
    exact hrK _ h hz
  -- the harmonic function `log ‖Φ · - p‖` on `X`
  have hu : Submission.HarmonicOnX (fun z : U => Real.log ‖(z : ℂ) - p‖) Set.univ :=
    harmonicOnX_log_norm_sub_center U p hp
  have huX : Submission.HarmonicOnX (fun y : X => Real.log ‖(Φ y : ℂ) - p‖) Set.univ := by
    have h := Work.Parabolic.harmonicOnX_comp_biholomorph (Φ := Φ) hu
    simpa only [Set.preimage_univ] using h
  refine ⟨Φ.symm ⟨circle p r 0, hcirc _ (norm_circle_sub p hr.le 0)⟩,
    conjPeriodHomOf huX (Φ.symm ⟨circle p r 0, hcirc _ (norm_circle_sub p hr.le 0)⟩), ?_⟩
  -- suppose the period homomorphism on `X` vanished
  intro hzero
  obtain ⟨F, hFhol, hFre⟩ :=
    exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero huX _ hzero
  -- the circle, transported into `X`
  have hmem : ∀ t : ℝ, circle p r t ∈ (U : Set ℂ) :=
    fun t => hcirc _ (norm_circle_sub p hr.le t)
  set γ : ℝ → X :=
    fun t => Φ.symm ⟨circle p r t, hmem t⟩ with hγdef
  have hγcont : Continuous γ :=
    Φ.symm.continuous.comp ((continuous_circle p r).subtype_mk hmem)
  have hγper : ∀ t : ℝ, γ (t + 1) = γ t :=
    fun t => congrArg Φ.symm (Subtype.ext (circle_periodic p r t))
  -- `G = Φ · - p` is holomorphic and nowhere zero on `X`
  have hGhol : Submission.HolomorphicOnX (fun y : X => (Φ y : ℂ) - p) Set.univ := by
    have hf : Submission.HolomorphicOnX (fun z : U => (z : ℂ) - p) Set.univ :=
      holomorphicOnX_opens_sub_const U p
    have h := Work.Parabolic.holomorphicOnX_comp_biholomorph (Φ := Φ) hf
    simpa only [Set.preimage_univ] using h
  have hGne : ∀ y : X, (Φ y : ℂ) - p ≠ 0 := by
    intro y h
    exact hp (sub_eq_zero.mp h ▸ (Φ y).2)
  have hFre' : ∀ y : X, (F y).re = Real.log ‖(Φ y : ℂ) - p‖ := hFre
  have harg := hasArg_of_holomorphic_conjugate hGhol hGne hFhol hFre' hγcont hγper
  have hfun : (fun t : ℝ => (fun y : X => (Φ y : ℂ) - p) (γ t))
      = fun t : ℝ => circle p r t - p := by
    funext t
    simp only [hγdef, Diffeomorph.apply_symm_apply]
  rw [hfun] at harg
  exact not_hasArg_circle p r hr ((hasArg_shift (circle p r) p).mp harg)

end Work.Mori
