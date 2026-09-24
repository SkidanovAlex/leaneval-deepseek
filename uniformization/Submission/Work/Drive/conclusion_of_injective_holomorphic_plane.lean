import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Parabolic.Reduction
import Submission.Work.SimplyConnected.ABS.winding_substitute
import Submission.Work.Analysis.RiemannSurface.DivisorBasics

namespace Work.Drive


/-! ## Two elementary steps of the `√`-trick (proved here, so that the endgame below is
self-contained) -/

/-- **The `√`-trick, analytic part.**  An injective holomorphic `Φ : X → ℂ` which is not surjective
produces an injective holomorphic `R : X → ℂ` whose image misses a whole disc `Metric.ball c ρ`,
with `R x` strictly farther than `ρ` from `c`.  This is `R := √(Φ - w)` for `w ∉ Φ '' univ`: the
square root exists because `Hom (π₁ X, ℝ) = 0` is exactly what
`Work.SimplyConnected.ABS.exists_log_of_ne_zero_of_subsingleton` needs, and the image of `√` is
disjoint from its negative, an open set. -/
theorem sqrt_exists_le_dist_of_injective_holomorphic_not_surjective {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (x : X) [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    {Φ : X → ℂ} (hΦ : Submission.HolomorphicOnX Φ Set.univ) (hinj : Function.Injective Φ)
    (hnot : ¬ Function.Surjective Φ) :
    ∃ (R : X → ℂ) (c : ℂ) (ρ : ℝ), Submission.HolomorphicOnX R Set.univ ∧
      Function.Injective R ∧ 0 < ρ ∧ (∀ z : X, ρ ≤ ‖R z - c‖) ∧ ρ < ‖R x - c‖ := by
  obtain ⟨w, hw⟩ := not_forall.mp hnot
  have hw' : ∀ z : X, Φ z ≠ w := fun z hz => hw ⟨z, hz⟩
  -- the nowhere vanishing holomorphic function `Φ - w` and its logarithm
  obtain ⟨H, hHhol, hHexp⟩ :=
    Work.SimplyConnected.ABS.exists_log_of_ne_zero_of_subsingleton (X := X) x
      (f := fun z => Φ z - w) (hΦ.sub (Submission.holomorphicOnX_const w))
      (fun z hz => hw' z (sub_eq_zero.mp hz))
  set R : X → ℂ := fun z => Complex.exp (H z * (2 : ℂ)⁻¹) with hRdef
  have hRhol : Submission.HolomorphicOnX R Set.univ := fun z hz =>
    ((hHhol z hz).mul_const ((2 : ℂ)⁻¹)).cexp
  have hRsq : ∀ z : X, R z ^ 2 = Φ z - w := by
    intro z
    change Complex.exp (H z * (2 : ℂ)⁻¹) ^ 2 = Φ z - w
    rw [hHexp z, sq, ← Complex.exp_add]
    congr 1
    ring_nf
  have hRinj : Function.Injective R := by
    intro p q hpq
    have h2 : R p ^ 2 = R q ^ 2 := by rw [hpq]
    rw [hRsq p, hRsq q] at h2
    exact hinj (by linear_combination h2)
  -- `R x ≠ 0`
  have hRxne : R x ≠ 0 := by
    intro h
    have h2 := hRsq x
    rw [h] at h2
    have h3 : Φ x - w = 0 := by simpa using h2.symm
    exact hw' x (sub_eq_zero.mp h3)
  have hRxpos : 0 < ‖R x‖ := norm_pos_iff.mpr hRxne
  -- `R '' univ` and `-(R '' univ)` are disjoint nonempty open sets
  have hopen : IsOpen (Set.range R) :=
    (Work.Parabolic.isOpenMap_of_injective_holomorphic hRhol hRinj).isOpen_range
  have hneg : IsOpen (-(Set.range R)) := hopen.neg
  have hnotin : ∀ z : X, R z ∉ -(Set.range R) := by
    intro z hz
    rw [Set.mem_neg] at hz
    obtain ⟨q, hq⟩ := hz
    have hsq : R q ^ 2 = R z ^ 2 := by rw [hq]; ring
    rw [hRsq q, hRsq z] at hsq
    have hqz : q = z := hinj (by linear_combination hsq)
    rw [hqz] at hq
    have hz0 : R z = 0 := by linear_combination (2 : ℂ)⁻¹ * hq
    have h2 := hRsq z
    rw [hz0] at h2
    have h3 : Φ z - w = 0 := by simpa using h2.symm
    exact hw' z (sub_eq_zero.mp h3)
  have hmem : -R x ∈ -(Set.range R) := by
    rw [Set.mem_neg]
    simpa using (Set.mem_range_self (f := R) x)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hneg (-R x) hmem
  refine ⟨R, -R x, min ε ‖R x‖ / 2, hRhol, hRinj, ?_, ?_, ?_⟩
  · exact div_pos (lt_min hε hRxpos) (by norm_num)
  · intro z
    by_contra hcon
    have hcon' : ‖R z - (-R x)‖ < min ε ‖R x‖ / 2 := not_le.mp hcon
    have hltε : ‖R z - (-R x)‖ < ε := by
      have h1 : min ε ‖R x‖ / 2 ≤ ε := by
        have := min_le_left ε ‖R x‖
        linarith
      linarith
    refine hnotin z (hball ?_)
    rw [Metric.mem_ball, dist_eq_norm]
    exact hltε
  · have h1 : min ε ‖R x‖ / 2 ≤ ‖R x‖ / 2 := by
      have := min_le_right ε ‖R x‖
      linarith
    have h2 : ‖R x - (-R x)‖ = 2 * ‖R x‖ := by
      have h3 : R x - (-R x) = (2 : ℂ) * R x := by ring
      rw [h3, norm_mul]
      norm_num
    rw [h2]
    linarith

/-- **The `√`-trick, Möbius part.**  An injective holomorphic `R` whose image avoids the disc
`Metric.ball c ρ`, with `R x` strictly outside it, can be normalised to an injective holomorphic
`X → 𝔻` vanishing at `x`: take `z ↦ ρ / (R z - c)`, which lands in the closed disc and has norm
`< 1` at `x`, and post-compose with the disc automorphism `Submission.mobiusA` killing that
value. -/
theorem injFamily_nonempty_of_dist_ge_of_injective_holomorphic {X : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (x : X) {R : X → ℂ} (hR : Submission.HolomorphicOnX R Set.univ)
    (hinjR : Function.Injective R) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hle : ∀ z : X, ρ ≤ ‖R z - c‖) (hlt : ρ < ‖R x - c‖) :
    (Submission.injFamily x).Nonempty := by
  have hne : ∀ z : X, R z - c ≠ 0 := by
    intro z hz
    have h0 : ‖R z - c‖ = 0 := by rw [hz, norm_zero]
    linarith [hle z]
  set ψ : X → ℂ := fun z => (ρ : ℂ) * (R z - c)⁻¹ with hψdef
  have hψhol : Submission.HolomorphicOnX ψ Set.univ := by
    intro z hz
    have hsub : Submission.HolomorphicOnXAt (fun y => R y - c) z :=
      (hR z hz).sub (Submission.holomorphicOnXAt_const c z)
    have hinv : Submission.HolomorphicOnXAt (fun y => (R y - c)⁻¹) z :=
      Work.Analysis.RiemannSurface.HolomorphicOnXAt.inv hsub (hne z)
    exact Submission.HolomorphicOnXAt.const_mul (ρ : ℂ) hinv
  have hψval : ∀ z : X, ψ z = (ρ : ℂ) * (R z - c)⁻¹ := fun z => rfl
  have hψnorm : ∀ z : X, ‖ψ z‖ ≤ 1 := by
    intro z
    have hpos : 0 < ‖R z - c‖ := lt_of_lt_of_le hρ (hle z)
    have h1 : ‖ψ z‖ = ρ / ‖R z - c‖ := by
      rw [hψval z, norm_mul, norm_inv, Complex.norm_of_nonneg (le_of_lt hρ), div_eq_mul_inv]
    rw [h1]
    exact (div_le_one hpos).mpr (hle z)
  have hv : ‖ψ x‖ < 1 := by
    have hpos : 0 < ‖R x - c‖ := lt_trans hρ hlt
    have h1 : ‖ψ x‖ = ρ / ‖R x - c‖ := by
      rw [hψval x, norm_mul, norm_inv, Complex.norm_of_nonneg (le_of_lt hρ), div_eq_mul_inv]
    rw [h1]
    exact (div_lt_one hpos).mpr hlt
  have hψinj : Function.Injective ψ := by
    intro p q hpq
    rw [hψval p, hψval q] at hpq
    have h1 : (R p - c)⁻¹ = (R q - c)⁻¹ :=
      mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hρ)) hpq
    have h2 : R p - c = R q - c := inv_inj.mp h1
    exact hinjR (by linear_combination h2)
  exact ⟨fun z => Submission.mobiusA (ψ x) (ψ z),
    ⟨hψhol.mobiusA_comp (fun z _ => hψnorm z) hv,
      fun z => Submission.norm_mobiusA_le hv (hψnorm z),
      Submission.mobiusA_self (ψ x)⟩,
    fun p q hpq => hψinj (Submission.mobiusA_injOn hv (hψnorm p) (hψnorm q) hpq)⟩


/-- **The endgame: an injective holomorphic function into `ℂ` finishes the proof.**

DO NOT use `Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal` or anything else from
`Submission/Work/Spine`: that chapter still contains a `sorry`, and any proof resting on it will be
rejected by the axiom check. Use instead the `√`-trick, which needs no simple connectivity:

* `injFamily`-free route. Let `Ω := Φ '' Set.univ` (a domain in `ℂ`). If `Ω = Set.univ`, then `Φ` is
  a bijection `X → ℂ` and `Submission.nonempty_diffeomorph_plane_of_bijective`
  (with `deriv_ne_zero_of_injective_analytic`) gives `Or.inl`.
* Otherwise pick `w ∉ Ω`. Then `x ↦ Φ x - w` is holomorphic on `X` and nowhere zero, so
  `Work.SimplyConnected.ABS.exists_log_of_ne_zero_of_subsingleton x hf hne` gives `H` with
  `Φ - w = exp ∘ H`. Put `R := exp ∘ (H/2)`, so `R² = Φ - w`. Then `R` is injective and
  `R '' univ` is disjoint from `-(R '' univ)`; since the latter is a nonempty open set, `R` misses
  a disc, and composing with a Möbius `z ↦ r/(z-c)` and then a disc automorphism (see
  `Submission.mobiusA`) yields `g` with `HolomorphicOnX g univ`, `‖g‖ ≤ 1`, `g x = 0`, injective,
  i.e. `g ∈ Submission.injFamily x`. Then
  `Submission.uniformization_of_injective_into_disc (x₀ := x) hg` gives
  `X ≅ ℂ ∨ X ≅ ℍ`, and the second disjunct is impossible by
  `Work.Parabolic.isParabolic.not_nonempty_diffeomorph_upperHalfPlane hpar`. -/
theorem conclusion_of_injective_holomorphic_plane {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X)
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)]
    (hpar : Work.Parabolic.IsParabolic X) {Φ : X → ℂ}
    (hΦ : Submission.HolomorphicOnX Φ Set.univ) (hinj : Function.Injective Φ) :
    Work.Drive.Conclusion X := by
  by_cases hsurj : Function.Surjective Φ
  · refine Or.inl (Submission.nonempty_diffeomorph_plane_of_bijective hΦ ⟨hinj, hsurj⟩ ?_)
    intro z
    exact Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic (Φ := Φ) hinj
      (fun y => hΦ y (Set.mem_univ y)) (Submission.exists_ne_of_chartedSpace z)
  · obtain ⟨R, c, ρ, hR, hinjR, hρ, hle, hlt⟩ :=
      sqrt_exists_le_dist_of_injective_holomorphic_not_surjective (X := X) x hΦ hinj hsurj
    obtain ⟨g, hg⟩ :=
      injFamily_nonempty_of_dist_ge_of_injective_holomorphic (X := X) x hR hinjR hρ hle hlt
    rcases Submission.uniformization_of_injective_into_disc (x₀ := x) ⟨g, hg⟩ with hpl | hH
    · exact Or.inl hpl
    · exact absurd hH
        (Work.Parabolic.isParabolic.not_nonempty_diffeomorph_upperHalfPlane hpar)

end Work.Drive
