import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.CoreResiduals.Defs
import Submission.Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData
import Submission.Work.CoreResiduals.exists_eps_min_lam
import Submission.Work.CoreResiduals.norm_timeDeriv_sub_le_of_secondDeriv_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- The `∂ₜ`-slices of the constructed vorticity are locally Lipschitz in `t`, uniformly in `x`,
i.e. `Work.CoreResiduals.TimeDerivLocallyLipschitz (solVort P) P.T`.

Near a time `t₀` of the half-window one takes a small interval whose closure stays in `preWindow P.T`
and on which `λ̄` is bounded below by some `m > 0` (continuity of `λ̄`); the second-order slice
identity `Work.ConstructionInstance.timeDeriv_timeDeriv_selfSimVort` then gives, for every `y`, the
`t`-differentiability of `s ↦ ∂ₜω(y,s)` there together with the box
`‖∂ₜ²ω(y,t)‖ ≤ Λ(m)` (an explicit function of the second-order data `Cg''` of the profile and `K₂`
of the modulation), and the mean value argument turns the box into the asserted Lipschitz bound.
The hypotheses are the second-order profile/modulation data of
`Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData`. -/
theorem solVort_timeDeriv_lipschitz {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) {Cg'' K₂ : ℝ}
    (hgdiff2 : ∀ z θ : ℝ, 0 < z → HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz (Work.ConstructionInstance.profile
        (Work.ConstructionInstance.profExp α) P.g) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile
        (Work.ConstructionInstance.profExp α) P.g)) z θ) z)
    (hg3 : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (Work.ConstructionInstance.profile
        (Work.ConstructionInstance.profExp α) P.g)) z θ| ≤ Cg'')
    (hlamdif2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      HasDerivAt (deriv P.lam) (deriv (deriv P.lam) t) t)
    (hlamd2 : ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      |deriv (deriv P.lam) t| ≤ K₂) :
    Work.CoreResiduals.TimeDerivLocallyLipschitz
      (Work.ConstructionInstance.solVort P) P.T := by
  intro t₀ ht₀
  have hp : 0 < Work.ConstructionInstance.profExp α :=
    Work.ConstructionInstance.profExp_pos P.hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith [P.hα13]
  have hI0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hCg : 0 ≤ P.Cg := P.hCg
  have hCg' : 0 ≤ P.Cg' := by simpa using P.hg2 0 0 le_rfl hI0
  have hCg'' : 0 ≤ Cg'' := by simpa using hg3 0 0 le_rfl hI0
  have hK₂ : 0 ≤ K₂ := le_trans (abs_nonneg _) (hlamd2 0 ⟨by norm_num, P.hT⟩)
  -- a small interval around `t₀` whose closure stays in the half-window, on which `λ̄ ≥ m > 0`
  obtain ⟨ε, hεpos, hsub, m, hmpos, hmle⟩ :=
    Work.CoreResiduals.exists_eps_min_lam (T := P.T) (lam := P.lam) P.hlam P.hlamdif ht₀
  -- the second-order box
  set Λ : ℝ := K₂ * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 2
      + P.K ^ 2 * (2 * (5 * Work.ConstructionInstance.profExp α + P.Cg') + Cg'') / m ^ 3
      + 2 * P.K ^ 2 * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 3
    with hΛdef
  have hΛ : 0 ≤ Λ := by
    rw [hΛdef]
    have h1 : 0 ≤ K₂ * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 2 :=
      div_nonneg (mul_nonneg hK₂ (by linarith)) (by positivity)
    have h2 : 0 ≤ P.K ^ 2 * (2 * (5 * Work.ConstructionInstance.profExp α + P.Cg') + Cg'') / m ^ 3 :=
      div_nonneg (mul_nonneg (sq_nonneg P.K) (by linarith)) (by positivity)
    have h3 : 0 ≤ 2 * P.K ^ 2 * (20 * Work.ConstructionInstance.profExp α + P.Cg + P.Cg') / m ^ 3 :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
    linarith
  refine ⟨ε, hεpos, Λ, ?_⟩
  intro t ht t' ht' y
  -- the second-order slice identity with its box, on the closed interval
  have hmem : ∀ s ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => FiniteTimeSingularity.timeDeriv (Work.ConstructionInstance.solVort P) y u)
        (FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv
          (Work.ConstructionInstance.solVort P)) y s) s
      ∧ ‖FiniteTimeSingularity.timeDeriv (FiniteTimeSingularity.timeDeriv
          (Work.ConstructionInstance.solVort P)) y s‖ ≤ Λ := by
    intro s hs
    have hspre : s ∈ Work.ConstructionInstance.preWindow P.T := hsub hs
    have h := Work.ConstructionInstance.timeDeriv_timeDeriv_selfSimVort
      (p := Work.ConstructionInstance.profExp α) (g := P.g) (L := P.L) (lam := P.lam)
      (T := P.T) (m := m) (Cg := P.Cg) (Cg' := P.Cg') (Cg'' := Cg'') (K := P.K) (K₂ := K₂)
      hp hp1 P.hvt.1 (Work.ConstructionInstance.bdd_g P) P.hg2 hg3 P.hgdiff hgdiff2 P.hlam
      P.hlamdif hlamdif2 P.hlamd hlamd2 P.hK hK₂ hspre hmpos (hmle s hs) y
    refine ⟨h.1, ?_⟩
    rw [hΛdef]
    exact h.2
  -- the mean value argument
  exact Work.CoreResiduals.norm_timeDeriv_sub_le_of_secondDeriv_bound
    (a := t₀ - ε) (b := t₀ + ε) (C := Λ)
    (fun y z hz => (hmem z hz).1) (fun y z hz => (hmem z hz).2)
    t ht t' ht' y

end Work.CoreResiduals
