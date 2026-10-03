import Submission.Lib.Unif2.Work.Mori.ArgumentPeriod
import Submission.Lib.Unif2.Work.Mori.Interface
import Submission.Lib.Unif2.Work.Mori.exists_diffeomorph_range_of_injective_holomorphic
import Submission.Lib.Unif2.Work.Mori.UnitGreen
import Submission.Lib.Unif2.Work.Mori.nonempty_diffeomorph_opens_top

/-!
# The plane-domain form of the parabolic case: winding circles

The classical route to the parabolic case of uniformization replaces Mori's normal form by the
following *plane-domain* statement (the Myrberg-type analysis of the type problem):

> a connected plane domain `U ⊆ ℂ` other than `ℂ` that is parabolic — carries no Green function —
> contains a circle `{z | ‖z - p‖ = r}` about a point `p ∉ U`.

Such a *winding circle* immediately produces a non-trivial homomorphism `π₁(U,u) →+ ℝ`
(`Work.Mori.argumentPeriodHom_ne_zero`); consequently a parabolic plane domain on whose fundamental
group every homomorphism to `ℝ` vanishes is all of `ℂ`
(`Work.Mori.planeDomain_eq_univ_of_isParabolic`), and hence a non-compact parabolic Riemann surface
that embeds holomorphically into `ℂ` is biholomorphic to `ℂ` with no simple-connectivity input
(`Work.Mori.plane_of_no_unitGreenFunction_of_planeParabolic`).

This module contains:

* `Work.Mori.HasWindingCircle U` — `U` contains a circle about a point it misses;
* `Work.Mori.hasWindingCircle_of_isPolar_compl` — if `Uᶜ` is polar then `U` has a winding circle
  (thinness of polar sets, `Work.Mori.exists_sphere_eq_empty`, proved earlier in this directory);
* `Work.Mori.hasWindingCircle_of_isBounded_compl` — if `Uᶜ` is bounded and non-empty, a large circle
  about a point of `Uᶜ` misses `Uᶜ`;
* `Work.Mori.hasWindingCircle_of_hasIsolatedBoundaryPoint` — an isolated point of `Uᶜ` has small
  circles around it inside `U`;
* `Work.Mori.exists_nontrivial_hom_of_diffeomorph_of_hasWindingCircle` — the winding obstruction: a
  surface biholomorphic to a plane domain with a winding circle has a non-trivial homomorphism of its
  fundamental group to `ℝ`;
* `Work.Mori.PlaneParabolicTheorem` — the Myrberg-type input, as a named `Prop`;
* `Work.Mori.planeDomain_eq_univ_of_isParabolic` — the plane-domain statement from that input;
* `Work.Mori.plane_of_no_unitGreenFunction_of_planeParabolic` — the parabolic case of uniformization
  from the plane-domain input together with holomorphic embeddability into `ℂ`.

## Note on the shape of the input

The input is *not* "the exceptional set `E` is polar" — that statement is false with the
relative-compactness notion of Green function used throughout this workspace: the punctured disc
`𝔻 ∖ {0}` is parabolic in that sense (a Green function at `z₀` would be bounded near the isolated
boundary point `0`, extend to `𝔻`, and have to be the Green function of `𝔻`, whose value at `0` is
`log 2 ≠ 0`, contradicting the boundary condition), while its complement `{0} ∪ {|z| ≥ 1}` is not
polar.  What survives — and what the winding argument actually consumes — is the existence of a
*winding circle*, which the punctured disc does have (every circle `{|z| = r}`, `0 < r < 1`).

The three cases above cover `Uᶜ` polar, `Uᶜ` bounded and `Uᶜ` with an isolated point.  The remaining
case of `PlaneParabolicTheorem` — `Uᶜ` non-polar, unbounded, with no isolated point — is the
classical Myrberg–Walsh construction (Chebyshev polynomials and the equilibrium potential of `Uᶜ`
produce a Green function when a winding circle is absent).  See `README.md` for the status.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

/-- **A plane domain contains a circle about a point it misses.**  A loop of this shape winds once
around `p`, and hence detects a non-trivial homomorphism `π₁(U) →+ ℝ`. -/
def HasWindingCircle (U : TopologicalSpace.Opens ℂ) : Prop :=
  ∃ p : ℂ, p ∉ (U : Set ℂ) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - p‖ = r → z ∈ (U : Set ℂ)

/-- **`U` has an isolated boundary point**: a point of `Uᶜ` with a punctured neighbourhood contained
in `U`.  Such a domain is parabolic (a positive harmonic function on it with a logarithmic pole
would be bounded near the isolated point, extend across it, and contradict the minimum principle),
and its small circles are winding circles. -/
def HasIsolatedBoundaryPoint (U : TopologicalSpace.Opens ℂ) : Prop :=
  ∃ p : ℂ, p ∉ (U : Set ℂ) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, z ∉ (U : Set ℂ) → ‖z - p‖ < ε → z = p

/-- **A polar complement gives a winding circle.**  A closed polar set is *thin* at each of its
points (`Work.Mori.exists_sphere_eq_empty`): there is a circle about `p ∈ Uᶜ` that misses `Uᶜ`, i.e.
lies entirely in `U`. -/
theorem hasWindingCircle_of_isPolar_compl {U : TopologicalSpace.Opens ℂ}
    (h : IsPolar ((U : Set ℂ)ᶜ)) (hne : ((U : Set ℂ)ᶜ).Nonempty) : HasWindingCircle U := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, hrK⟩ := h.exists_sphere_eq_empty U.isOpen.isClosed_compl hp
  refine ⟨p, hp, r, hr, fun z hz => ?_⟩
  by_contra hzu
  exact hrK z hzu hz

/-- **A bounded complement gives a winding circle.**  If `Uᶜ` is bounded and non-empty, every circle
about a point `p ∈ Uᶜ` of radius larger than `Uᶜ`'s extent misses `Uᶜ`, i.e. lies in `U`. -/
theorem hasWindingCircle_of_isBounded_compl {U : TopologicalSpace.Opens ℂ}
    (h : Bornology.IsBounded ((U : Set ℂ)ᶜ)) (hne : ((U : Set ℂ)ᶜ).Nonempty) :
    HasWindingCircle U := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall p).mp h
  have hR0 : 0 ≤ R := by
    have := hR hp
    simpa [Metric.mem_closedBall] using this
  refine ⟨p, hp, R + 1, by linarith, fun z hz => ?_⟩
  by_contra hzu
  have h1 : z ∈ Metric.closedBall p R := hR hzu
  have h2 : ‖z - p‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using h1
  rw [hz] at h2
  linarith

/-- **An isolated boundary point gives a winding circle.**  If `B(p,ε) ∖ {p} ⊆ U` then the circle of
radius `ε/2` about `p` lies in `U`. -/
theorem hasWindingCircle_of_hasIsolatedBoundaryPoint {U : TopologicalSpace.Opens ℂ}
    (h : HasIsolatedBoundaryPoint U) : HasWindingCircle U := by
  obtain ⟨p, hp, ε, hε, hiso⟩ := h
  refine ⟨p, hp, ε / 2, by linarith, fun z hz => ?_⟩
  by_contra hzu
  have hlt : ‖z - p‖ < ε := by rw [hz]; linarith
  have hzp : z = p := hiso z hzu hlt
  rw [hzp, sub_self, norm_zero] at hz
  linarith

/-- **The punctured unit disc.**  The model example showing that the relative-compactness notion of
parabolicity used throughout this workspace is weaker than the classical one: `𝔻 ∖ {0}` is parabolic
in this sense (`Work.Mori.isParabolic_puncturedUnitDisc`), while classically its Green function
exists and fails only the boundary condition at the isolated point `0`. -/
def puncturedUnitDisc : TopologicalSpace.Opens ℂ :=
  ⟨{z : ℂ | z ≠ 0} ∩ Metric.ball (0 : ℂ) 1, isOpen_ne.inter Metric.isOpen_ball⟩

/-- **The punctured unit disc has an isolated boundary point** (namely `0`). -/
theorem hasIsolatedBoundaryPoint_puncturedUnitDisc :
    HasIsolatedBoundaryPoint puncturedUnitDisc := by
  refine ⟨0, by simp [puncturedUnitDisc], 1, one_pos, fun z hz hlt => ?_⟩
  by_contra hz0
  exact hz (by simpa [puncturedUnitDisc, hz0] using hlt)

/-- **The punctured unit disc contains winding circles**: the circle of radius `1/2` about `0`. -/
theorem hasWindingCircle_puncturedUnitDisc : HasWindingCircle puncturedUnitDisc := by
  refine ⟨0, by simp [puncturedUnitDisc], 1 / 2, by norm_num, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, sub_zero, norm_zero] at hz
    norm_num at hz
  rw [sub_zero] at hz
  exact ⟨hz0, Metric.mem_ball.mpr (by rw [dist_eq_norm, sub_zero, hz]; norm_num)⟩

/-- **The winding obstruction, in the form of a winding circle.**  If `X` is biholomorphic to a plane
domain `U` containing a circle about a point it misses, then `X` has a non-trivial homomorphism
`π₁(X,x) →+ ℝ`.  Equivalently, such an `X` never satisfies
`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)`.

The proof transports the harmonic function `log ‖· - p‖` (together with the winding circle) from `U`
to `X` along the biholomorphism; it is the same computation as in the polar case
(`Work.Mori.exists_nontrivial_hom_of_diffeomorph_of_isPolar_of_nonempty`). -/
theorem exists_nontrivial_hom_of_diffeomorph_of_hasWindingCircle
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : TopologicalSpace.Opens ℂ} (hW : HasWindingCircle U)
    (Φ : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) X U
      ((⊤ : ℕ∞) : WithTop ℕ∞)) (x : X) :
    ∃ f : Additive (FundamentalGroup X x) →+ ℝ, f ≠ 0 := by
  obtain ⟨p, hpU, r, hr, hcirc⟩ := hW
  have hu : Submission.HarmonicOnX (fun z : U => Real.log ‖(z : ℂ) - p‖) Set.univ :=
    harmonicOnX_log_norm_sub_center U p hpU
  have huX : Submission.HarmonicOnX (fun y : X => Real.log ‖(Φ y : ℂ) - p‖) Set.univ := by
    have h := Work.Parabolic.harmonicOnX_comp_biholomorph (Φ := Φ) hu
    simpa only [Set.preimage_univ] using h
  refine ⟨conjPeriodHomOf huX x, ?_⟩
  intro hzero
  obtain ⟨F, hFhol, hFre⟩ := exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero huX x hzero
  have hmem : ∀ t : ℝ, circle p r t ∈ (U : Set ℂ) :=
    fun t => hcirc _ (norm_circle_sub p hr.le t)
  set γ : ℝ → X := fun t => Φ.symm ⟨circle p r t, hmem t⟩ with hγdef
  have hγcont : Continuous γ :=
    Φ.symm.continuous.comp ((continuous_circle p r).subtype_mk hmem)
  have hγper : ∀ t : ℝ, γ (t + 1) = γ t :=
    fun t => congrArg Φ.symm (Subtype.ext (circle_periodic p r t))
  have hGhol : Submission.HolomorphicOnX (fun y : X => (Φ y : ℂ) - p) Set.univ := by
    have hf : Submission.HolomorphicOnX (fun z : U => (z : ℂ) - p) Set.univ :=
      holomorphicOnX_opens_sub_const U p
    have h := Work.Parabolic.holomorphicOnX_comp_biholomorph (Φ := Φ) hf
    simpa only [Set.preimage_univ] using h
  have hGne : ∀ y : X, (Φ y : ℂ) - p ≠ 0 := by
    intro y h
    exact hpU (sub_eq_zero.mp h ▸ (Φ y).2)
  have hFre' : ∀ y : X, (F y).re = Real.log ‖(Φ y : ℂ) - p‖ := hFre
  have harg := hasArg_of_holomorphic_conjugate hGhol hGne hFhol hFre' hγcont hγper
  have hfun : (fun t : ℝ => (fun y : X => (Φ y : ℂ) - p) (γ t))
      = fun t : ℝ => circle p r t - p := by
    funext t
    simp only [hγdef, Diffeomorph.apply_symm_apply]
  rw [hfun] at harg
  exact not_hasArg_circle p r hr ((hasArg_shift (circle p r) p).mp harg)

/-- **The Myrberg-type geometric input of the plane-domain form of the parabolic case.**

Every connected parabolic plane domain other than `ℂ` contains a circle about a point of its
complement: a domain that misses no such circle is either all of `ℂ` or carries a Green function.

The cases `Uᶜ` polar, `Uᶜ` bounded (and non-empty) and `Uᶜ` with an isolated point are proved above;
the remaining case is the classical Myrberg–Walsh construction. -/
def PlaneParabolicTheorem : Prop :=
  ∀ U : TopologicalSpace.Opens ℂ, IsConnected (U : Set ℂ) → Work.Parabolic.IsParabolic ↥U →
    (U : Set ℂ) ≠ Set.univ → HasWindingCircle U

/-- **A connected parabolic plane domain without non-trivial homomorphisms is all of `ℂ`.**  From the
Myrberg-type input: if `U ≠ ℂ` then `U` contains a winding circle about some `p ∉ U`, hence
(`Work.Mori.argumentPeriodHom_ne_zero`) a non-trivial homomorphism `π₁(U,u) →+ ℝ`, contradicting the
hypothesis. -/
theorem planeDomain_eq_univ_of_isParabolic (h : PlaneParabolicTheorem)
    {U : TopologicalSpace.Opens ℂ} (hconn : IsConnected (U : Set ℂ))
    (hpar : Work.Parabolic.IsParabolic ↥U) {u : U}
    [Subsingleton (Additive (FundamentalGroup U u) →+ ℝ)] :
    (U : Set ℂ) = Set.univ := by
  by_contra hne
  obtain ⟨p, hpU, r, hr, hcirc⟩ := h U hconn hpar hne
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconn
  exact argumentPeriodHom_ne_zero U p hpU ⟨r, hr, hcirc⟩ u (Subsingleton.elim _ _)

/-- **The parabolic case of uniformization, from the plane-domain (Myrberg) input and holomorphic
embeddability into `ℂ`.**

The holomorphic embedding is converted into a plane domain by
`Work.Mori.exists_diffeomorph_range_of_injective_holomorphic`; if that domain is all of `ℂ` we are
done, and otherwise `PlaneParabolicTheorem` produces a winding circle, hence a non-trivial
homomorphism `π₁(X,x) →+ ℝ` (`Work.Mori.exists_nontrivial_hom_of_diffeomorph_of_hasWindingCircle`),
contradicting the hypothesis.

Unlike the ABS route (`Work.Mori.plane_of_no_unitGreenFunction_of_ABS`), this needs *no* simple
connectivity input; it is the route the request for this chapter describes as "Mori's". -/
theorem plane_of_no_unitGreenFunction_of_planeParabolic
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (h : PlaneParabolicTheorem) (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (hgreen : ¬ ∃ (z₀ : X) (E : X → ℝ), Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hplanar : HasHolomorphicEmbedding X) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) := by
  obtain ⟨φ, hφ, hinj⟩ := hplanar
  obtain ⟨U, hU, ⟨Φ⟩⟩ := exists_diffeomorph_range_of_injective_holomorphic hφ hinj
  have hparU : Work.Parabolic.IsParabolic ↥U :=
    isParabolic_of_diffeomorph Φ (isParabolic_of_not_exists_isUnitGreenFunction hX hgreen)
  have hconnU : IsConnected (U : Set ℂ) := hU ▸ isConnected_range hφ.continuous
  by_cases huniv : (U : Set ℂ) = Set.univ
  · have hUt : U = ⊤ := TopologicalSpace.Opens.ext huniv
    obtain ⟨e⟩ := nonempty_diffeomorph_opens_top
    exact ⟨Φ.trans (hUt ▸ e)⟩
  · obtain ⟨f, hf⟩ :=
      exists_nontrivial_hom_of_diffeomorph_of_hasWindingCircle (h U hconnU hparU huniv) Φ x
    exact absurd (Subsingleton.elim f 0) hf

end Work.Mori
