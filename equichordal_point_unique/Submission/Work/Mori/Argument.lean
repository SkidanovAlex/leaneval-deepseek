import Submission.Work.Mori.Defs
import Submission.Work.Mori.Circle
import Submission.Work.Mori.exists_sphere_eq_empty
import Submission.Work.Mori.holomorphicOnX_opens_sub_const
import Submission.Work.Mori.not_hasArg_circle
import Submission.Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton
import Submission.Work.Parabolic.holomorphicOnX_comp_biholomorph

/-!
# The winding argument: a non-empty polar set is impossible

This is the step of Mori's route that removes the exceptional set, and it is unconditional.

If `Φ : X ≃ₘ U` is a biholomorphism onto an open `U ⊆ ℂ` whose complement is polar and non-empty,
pick `p ∈ Uᶜ` and put `G = fun y => (Φ y : ℂ) - p`, holomorphic and nowhere zero on `X`.  The
challenge hypothesis `Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)` makes the argument of
every nowhere-zero holomorphic function single-valued along every loop of `X`
(`Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton`).  Meanwhile polar sets are thin: some circle
`Work.Mori.circle p r` of radius `r > 0` lies entirely in `U`
(`Work.Mori.exists_sphere_eq_empty`).  Transporting that circle into `X` along `Φ.symm` produces a
`1`-periodic curve along which `G` equals `circle p r - p`, whose argument is *not* periodic
(`Work.Mori.not_hasArg_circle`) — contradiction.

The conclusion is `Work.Mori.not_diffeomorph_of_isPolar_of_nonempty`: there is no such
biholomorphism, so in Mori's normal form the polar set must be empty.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set

namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The winding obstruction: a space whose fundamental group has no non-trivial homomorphism to `ℝ`
is not biholomorphic to the complement of a non-empty polar set.**

This is the step that removes the polar set in Mori's normal form, and it is unconditional.  If
`Φ : X ≃ₘ U` with `U` open in `ℂ` and `Uᶜ` polar and non-empty, pick `p ∈ Uᶜ` and let
`G = fun y => (Φ y : ℂ) - p`, which is holomorphic and nowhere zero on `X` (since `Φ y ∈ U`).  Then
`log ‖G‖` is harmonic, so by `Submission.exists_holomorphicOnX_re_of_harmonic` (which uses exactly the
`Subsingleton` hypothesis) it has a global holomorphic conjugate `F`; the quotient
`G * exp (-F)` is holomorphic with constant modulus `1`, hence constant, and this makes the argument
of `G` single-valued and periodic along every loop of `X`
(`Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton`).  But `IsPolar` makes `Uᶜ` thin
(`Work.Mori.exists_sphere_eq_empty`), so some circle `circle p r` of positive radius lies in `U`; the
loop `Φ.symm ∘ circle p r` of `X` then has `G (Φ.symm (circle p r t)) = circle p r t - p`, whose
argument is *not* periodic (`Work.Mori.not_hasArg_circle`) — contradiction. -/
theorem not_diffeomorph_of_isPolar_of_nonempty (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    {U : TopologicalSpace.Opens ℂ} (hpolar : IsPolar ((U : Set ℂ)ᶜ))
    (hne : ((U : Set ℂ)ᶜ).Nonempty)
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X U
      ((⊤ : ℕ∞) : WithTop ℕ∞)) : False := by
  -- the polar set is closed and non-empty, so some circle around one of its points avoids it
  obtain ⟨p, hp⟩ := hne
  have hclosed : IsClosed ((U : Set ℂ)ᶜ) := U.isOpen.isClosed_compl
  obtain ⟨r, hr, hrK⟩ := exists_sphere_eq_empty hpolar hclosed hp
  have hsphere : ∀ t : ℝ, circle p r t ∈ (U : Set ℂ) := by
    intro t
    by_contra hnot
    exact hrK _ hnot (norm_circle_sub p hr.le t)
  -- the nowhere-zero holomorphic function `G = Φ · - p` on `X`
  set G : X → ℂ := fun y => (Φ y : ℂ) - p with hGdef
  have hGne : ∀ y : X, G y ≠ 0 := by
    intro y hy
    have hΦy : (Φ y : ℂ) = p := sub_eq_zero.mp hy
    exact hp (hΦy ▸ (Φ y).2)
  have hGhol : Submission.HolomorphicOnX G Set.univ := by
    have hf : Submission.HolomorphicOnX (fun z : U => (z : ℂ) - p) Set.univ :=
      holomorphicOnX_opens_sub_const U p
    have h := Work.Parabolic.holomorphicOnX_comp_biholomorph (Φ := Φ) hf
    simpa [hGdef, Set.preimage_univ, Function.comp_def] using h
  -- the circle of `U`, transported to `X`
  set γ : ℝ → X := fun t => Φ.symm ⟨circle p r t, hsphere t⟩ with hγdef
  have hγcont : Continuous γ := by
    rw [hγdef]
    exact Φ.symm.continuous.comp ((continuous_circle p r).subtype_mk hsphere)
  have hγper : ∀ t : ℝ, γ (t + 1) = γ t := by
    intro t
    rw [hγdef]
    exact congrArg Φ.symm (Subtype.ext (circle_periodic p r t))
  -- along that loop, `G` is the circle around `p`
  have harg : Commons.Topology.Winding.HasArg (fun t : ℝ => circle p r t - p) 0 := by
    have h := hasArg_comp_of_holomorphic_of_subsingleton (x := x) hGhol hGne hγcont hγper
    have hfun : (fun t : ℝ => G (γ t)) = fun t : ℝ => circle p r t - p := by
      funext t
      simp only [hGdef, hγdef, Diffeomorph.apply_symm_apply]
    rwa [hfun] at h
  exact not_hasArg_circle p r hr ((hasArg_shift (circle p r) p).mp harg)

/-- **The contrapositive form of the winding obstruction.**  If `X` is biholomorphic to the complement
of a *non-empty* polar closed set, then some homomorphism `π₁(X,x) → ℝ` is non-trivial; equivalently
`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)` fails.  The non-trivial homomorphism is (up to
the identification) the winding number around a point of the polar set. -/
theorem not_subsingleton_hom_of_diffeomorph_of_isPolar_of_nonempty (x : X)
    {U : TopologicalSpace.Opens ℂ} (hpolar : IsPolar ((U : Set ℂ)ᶜ))
    (hne : ((U : Set ℂ)ᶜ).Nonempty)
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X U
      ((⊤ : ℕ∞) : WithTop ℕ∞)) :
    ¬ Subsingleton (Additive (FundamentalGroup X x) →+ ℝ) := by
  intro h
  haveI := h
  exact not_diffeomorph_of_isPolar_of_nonempty (X := X) x hpolar hne Φ

end Work.Mori
