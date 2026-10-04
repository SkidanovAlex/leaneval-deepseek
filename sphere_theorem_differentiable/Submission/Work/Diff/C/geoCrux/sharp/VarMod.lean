import Mathlib
import Submission.Work.Diff.C.geoCrux.sharp.Defs
import Submission.Work.Diff.C.JacobiLogDeriv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp modulus bound for the radial variation field

This file assembles the sharp radial modulus bound for the radial variation fields
`Z_ξ(t) = ∂_r|₀ GExp q (t • (v + r • ξ))` out of the pieces:

* the anchor `‖Z_η(σ)‖ ≤ sin σ (1 + 7ε₁)‖η‖` for `2σ ≤ ρ₀`, `cos σ ≥ 1/2`
  (`Work.Diff.C.geoCrux.sharp.anchor_of_twoCentre`);
* the non-vanishing `Z_η(t) ≠ 0` for `0 < t ≤ ρ₀` (`Work.Diff.C.geoCrux.sharp.varfield_ne_zero`);
* the log-derivative bound `(log ‖Z_η‖)'(t) ≤ cot t + ε₁/sin t` for `t < ρ₀`
  (`Work.Diff.C.geoCrux.sharp.log_deriv_of_ray`);
* the pure real-analysis pieces `modulus_anchored_pos` (the anchored Sturm comparison with the
  positivity hypothesis only at the two endpoints) and `anchor_arith` (the numerical endgame).

The argument: for `ρ ≤ π/3` the anchor is applied directly at `σ = ρ`; for `ρ > π/3` one anchors at
`δ = π/3` (always admissible, since `c ≤ 1/4` gives `2π/3 < ρ₀`) and integrates the log-derivative
bound from `δ` to `ρ`, which the Sturm comparison converts into the factor
`(tan(ρ/2)/tan(π/6))^{ε₁}`, absorbed by the numerical inequality.

Following `Submission/Work/Diff/C/geoCrux/rauch_sphere_map.lean`, the assembly `varMod_core` is stated
with the binders *explicitly unfolded* (the four inputs as plain Π-types in the ambient variable
context) rather than through the closed `Prop`s: a local hypothesis whose type is an `abbrev`-`Prop`
has its implicit universe arguments frozen at the binder.  The final theorem instantiates the
unfolded hypotheses from the delegated lemmas, whose universes are instantiated freshly at the call
site.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp Submission.Geodesic Submission.JacobiGlobal

namespace Work.Diff.C.geoCrux.sharp

/-- The statement of `Work.Diff.C.geoCrux.sharp.modulus_anchored_pos`: the anchored Sturm comparison
with the positivity of `v` assumed only at the two endpoints. -/
abbrev ModAnchProp : Prop :=
  ∀ {v w : ℝ → ℝ} {ε δ d A : ℝ}, 0 < δ → δ < d → 0 ≤ ε → d < Real.pi →
    0 < v δ → 0 < v d →
    (∀ t ∈ Set.Icc δ d, HasDerivAt (fun s : ℝ => Real.log (v s)) (w t) t) →
    (∀ t ∈ Set.Ioo (0 : ℝ) d, w t ≤ Real.cot t + ε / Real.sin t) →
    v δ ≤ Real.exp A * Real.sin δ →
    v d ≤ Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε

/-- The statement of `Work.Diff.C.geoCrux.sharp.anchor_arith`: the numerical endgame. -/
abbrev ArithProp : Prop :=
  ∀ {c ε₁ ρ : ℝ}, 0 < c → c ≤ 1 / 4 → 0 ≤ ε₁ → 4 * ε₁ * Real.pi < c →
    Real.pi / 3 < ρ → ρ ≤ Real.pi - Real.arccos (1 - c) →
    (1 + 7 * ε₁) * (Real.tan (ρ / 2) / Real.tan (Real.pi / 6)) ^ ε₁
      ≤ 1 + 25 * ε₁ / Real.sin ρ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- `Zf` and `fv` are the same field (the ascription of the type is the only difference). -/
lemma Zf_eq_fv (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (t : ℝ) :
    Zf (cov := cov) hmet q v ξ t = fv (cov := cov) hmet q v ξ t := rfl

/-- **Linearity** of `Zf` in the direction, at the point of the ray. -/
lemma Zf_smul (hmet : IsMetricCompatible cov) (q : M) (v ξ : TangentSpace I q) (σ a : ℝ) :
    Zf (cov := cov) hmet q v (a • ξ) σ = a • Zf (cov := cov) hmet q v ξ σ := by
  rw [Zf_eq_fv, Zf_eq_fv]
  exact Work.Diff.C.geoCrux.fv_smul (cov := cov) hmet q v ξ σ a

/-- `2π/3 < ρ₀ = π - arccos (1-c)` for `0 < c ≤ 1/4`. -/
lemma two_thirds_lt_rho0 {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) :
    2 * Real.pi / 3 < Real.pi - Real.arccos (1 - c) := by
  have hhalf : Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  have hlt : Real.arccos (1 - c) < Real.pi / 3 := by
    have h := Real.arccos_lt_arccos (x := (1 : ℝ) / 2) (y := 1 - c)
      (by norm_num) (by linarith) (by linarith)
    rwa [hhalf] at h
  linarith

/-- `cos (π - arccos (1-c)) = -1 + c`. -/
lemma cos_rho0 {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) :
    Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
  rw [Real.cos_pi_sub, Real.cos_arccos (by linarith) (by linarith)]
  ring

/-- **The sharp modulus bound for the radial variation field** (the assembly).

The inputs are the four pieces, with the binders unfolded (see the module docstring). -/
theorem varMod_core
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρπ : ρ ≤ Real.pi - Real.arccos (1 - c))
    (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0)
    (hanch : ∀ (σ : ℝ), 0 < σ → 2 * σ ≤ Real.pi - Real.arccos (1 - c) →
      1 / 2 ≤ Real.cos σ → ∀ (η : TangentSpace I q), Inner.inner ℝ v η = 0 →
      ‖Zf (cov := cov) hmet q v η σ‖ ≤ Real.sin σ * (1 + 7 * ε₁) * ‖η‖)
    (hnz : ∀ (η : TangentSpace I q), Inner.inner ℝ v η = 0 → η ≠ 0 → ∀ t : ℝ, 0 < t →
      t ≤ Real.pi - Real.arccos (1 - c) → Zf (cov := cov) hmet q v η t ≠ 0)
    (hlog : ∀ (η : TangentSpace I q), Inner.inner ℝ v η = 0 → η ≠ 0 → ∀ t : ℝ, 0 < t →
      t < Real.pi - Real.arccos (1 - c) →
      Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v η) t)
          (Zf (cov := cov) hmet q v η t)
        / Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)
        ≤ Real.cot t + ε₁ / Real.sin t)
    (hmodanch : ∀ {v' w' : ℝ → ℝ} {ε δ d A : ℝ}, 0 < δ → δ < d → 0 ≤ ε → d < Real.pi →
      0 < v' δ → 0 < v' d →
      (∀ t ∈ Set.Icc δ d, HasDerivAt (fun s : ℝ => Real.log (v' s)) (w' t) t) →
      (∀ t ∈ Set.Ioo (0 : ℝ) d, w' t ≤ Real.cot t + ε / Real.sin t) →
      v' δ ≤ Real.exp A * Real.sin δ →
      v' d ≤ Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε)
    (harith : ∀ {c' ε₁' ρ' : ℝ}, 0 < c' → c' ≤ 1 / 4 → 0 ≤ ε₁' → 4 * ε₁' * Real.pi < c' →
      Real.pi / 3 < ρ' → ρ' ≤ Real.pi - Real.arccos (1 - c') →
      (1 + 7 * ε₁') * (Real.tan (ρ' / 2) / Real.tan (Real.pi / 6)) ^ ε₁'
        ≤ 1 + 25 * ε₁' / Real.sin ρ') :
    ‖Zf (cov := cov) hmet q v ξ ρ‖ ≤ (Real.sin ρ + 25 * ε₁) * ‖ξ‖ := by
  have hvn : ‖v‖ = 1 := by
    have h : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hv
    nlinarith [norm_nonneg v]
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hvn; simp at hvn
  have hρ₀π : Real.pi - Real.arccos (1 - c) < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have hdπ : ρ < Real.pi := lt_of_le_of_lt hρπ hρ₀π
  have hγ : ContMDiff (modelWithCornersSelf ℝ ℝ) I ∞
      (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet q hv0
  have hnevel : ∀ t : ℝ, Submission.Geodesic.curveVelocity (I := I)
      (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) t ≠ 0 :=
    fun t => Submission.EnergyRayCover.curveVelocity_GExp_smul_ne_zero (cov := cov) hmet hv0 t
  -- The unit-direction version.
  have hunit : ∀ (η : TangentSpace I q), Inner.inner ℝ v η = 0 → Inner.inner ℝ η η = 1 →
      ‖Zf (cov := cov) hmet q v η ρ‖ ≤ Real.sin ρ + 25 * ε₁ := by
    intro η hη hη1
    have hη0 : η ≠ 0 := by
      intro h; rw [h] at hη1; simp at hη1
    have hJ : ∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • v))
        (Zf (cov := cov) hmet q v η) t := by
      intro t
      have h := Work.Diff.C.geoCrux.fv_isJacobiAt (cov := cov) hmet htor q hv0 hvn (ξ := η) t
      have he : (fun s : ℝ => fv (cov := cov) hmet q v η s) = Zf (cov := cov) hmet q v η := by
        funext s
        exact (Zf_eq_fv (cov := cov) hmet q v η s).symm
      rwa [he] at h
    have hηn : ‖η‖ = 1 := by
      have h2 : ‖η‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hη1
      nlinarith [norm_nonneg η]
    by_cases hsmall : ρ ≤ Real.pi / 3
    · -- the anchor at `σ = ρ`
      have h2ρ : 2 * ρ ≤ Real.pi - Real.arccos (1 - c) := by
        have := two_thirds_lt_rho0 hc hc1
        linarith
      have hcos : 1 / 2 ≤ Real.cos ρ := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := ρ) (y := Real.pi / 3)
          hρ0.le (by linarith [Real.pi_pos]) hsmall
        rwa [Real.cos_pi_div_three] at h
      have h' := hanch ρ hρ0 h2ρ hcos η hη
      rw [hηn, mul_one] at h'
      have hle : Real.sin ρ * (1 + 7 * ε₁) ≤ Real.sin ρ + 25 * ε₁ := by
        have hs := Real.sin_le_one ρ
        nlinarith [hε₁, hs]
      linarith
    · push_neg at hsmall
      -- the propagation from the anchor at `δ = π/3`
      set δ : ℝ := Real.pi / 3 with hδdef
      have hδ0 : 0 < δ := by rw [hδdef]; positivity
      have hδρ : δ < ρ := by rw [hδdef]; exact hsmall
      have hδ2 : 2 * δ ≤ Real.pi - Real.arccos (1 - c) := by
        have := two_thirds_lt_rho0 hc hc1
        rw [hδdef]; linarith
      have hcosδ : 1 / 2 ≤ Real.cos δ := by rw [hδdef, Real.cos_pi_div_three]
      have hanchδ := hanch δ hδ0 hδ2 hcosδ η hη
      have hδpos : 0 < ‖Zf (cov := cov) hmet q v η δ‖ := by
        rw [norm_pos_iff]
        exact hnz η hη hη0 δ hδ0 (le_trans hδρ.le hρπ)
      have hρpos : 0 < ‖Zf (cov := cov) hmet q v η ρ‖ := by
        rw [norm_pos_iff]
        exact hnz η hη hη0 ρ hρ0 hρπ
      have hder : ∀ t ∈ Set.Icc δ ρ,
          HasDerivAt (fun s : ℝ => Real.log ‖Zf (cov := cov) hmet q v η s‖)
            (Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v η) t)
                (Zf (cov := cov) hmet q v η t)
              / Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)) t := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hδ0 ht.1
        have htρ₀ : t ≤ Real.pi - Real.arccos (1 - c) := le_trans ht.2 hρπ
        have hnet : Zf (cov := cov) hmet q v η t ≠ 0 := hnz η hη hη0 t ht0 htρ₀
        have h0 := Work.Diff.C.jld_log_deriv_of_jacobi (I := I) (M := M) (cov := cov)
          hmet htor hγ hJ hnevel hnet
        have hfun : (fun s : ℝ => Real.log
              (Inner.inner ℝ (Zf (cov := cov) hmet q v η s) (Zf (cov := cov) hmet q v η s)) / 2)
            = fun s : ℝ => Real.log ‖Zf (cov := cov) hmet q v η s‖ := by
          funext s
          rw [real_inner_self_eq_norm_sq, Real.log_pow]
          norm_num
        rw [hfun] at h0
        exact h0
      have hwb : ∀ t ∈ Set.Ioo (0 : ℝ) ρ,
          Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov (Zf (cov := cov) hmet q v η) t)
              (Zf (cov := cov) hmet q v η t)
            / Inner.inner ℝ (Zf (cov := cov) hmet q v η t) (Zf (cov := cov) hmet q v η t)
            ≤ Real.cot t + ε₁ / Real.sin t := by
        intro t ht
        have htρ₀ : t < Real.pi - Real.arccos (1 - c) := lt_of_lt_of_le ht.2 hρπ
        exact hlog η hη hη0 t ht.1 htρ₀
      have hanchor : ‖Zf (cov := cov) hmet q v η δ‖
          ≤ Real.exp (Real.log (1 + 7 * ε₁)) * Real.sin δ := by
        have h' : ‖Zf (cov := cov) hmet q v η δ‖ ≤ Real.sin δ * (1 + 7 * ε₁) * ‖η‖ := hanchδ
        rw [hηn, mul_one] at h'
        rw [Real.exp_log (by positivity : (0 : ℝ) < 1 + 7 * ε₁)]
        linarith
      have hmain := hmodanch hδ0 hδρ hε₁ hdπ hδpos hρpos hder hwb hanchor
      have htan : Real.tan (δ / 2) = Real.tan (Real.pi / 6) := by
        congr 1
        rw [hδdef]; ring
      rw [Real.exp_log (by positivity : (0 : ℝ) < 1 + 7 * ε₁), htan] at hmain
      have har := harith hc hc1 hε₁ hnum2 hsmall hρπ
      have hsin0 : 0 ≤ Real.sin ρ := Real.sin_nonneg_of_nonneg_of_le_pi hρ0.le hdπ.le
      have hsinne : Real.sin ρ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hρ0 hdπ).ne'
      have h1 : Real.sin ρ * ((1 + 7 * ε₁) * (Real.tan (ρ / 2) / Real.tan (Real.pi / 6)) ^ ε₁)
          ≤ Real.sin ρ * (1 + 25 * ε₁ / Real.sin ρ) :=
        mul_le_mul_of_nonneg_left har hsin0
      have h2 : Real.sin ρ * (1 + 25 * ε₁ / Real.sin ρ) = Real.sin ρ + 25 * ε₁ := by
        field_simp
      calc ‖Zf (cov := cov) hmet q v η ρ‖
          ≤ Real.sin ρ * ((1 + 7 * ε₁) * (Real.tan (ρ / 2) / Real.tan (Real.pi / 6)) ^ ε₁) := by
            linarith [hmain]
        _ ≤ Real.sin ρ * (1 + 25 * ε₁ / Real.sin ρ) := h1
        _ = Real.sin ρ + 25 * ε₁ := h2
  -- `ξ = 0`
  rcases eq_or_ne ξ 0 with h | h
  · subst h
    have hz : Zf (cov := cov) hmet q v 0 ρ = 0 :=
      (Zf_eq_fv (cov := cov) hmet q v 0 ρ).trans
        (Work.Diff.C.geoCrux.fv_zero (cov := cov) hmet q v ρ)
    rw [hz]
    simp
  · set μ : TangentSpace I q := (‖ξ‖)⁻¹ • ξ with hμ
    have hμorth : Inner.inner ℝ v μ = 0 := by
      rw [hμ, inner_smul_right, hξ, mul_zero]
    have hξn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hμ1 : Inner.inner ℝ μ μ = 1 := by
      have h2 : ‖μ‖ = 1 := by
        rw [hμ, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)),
          inv_mul_cancel₀ hξn]
      rw [real_inner_self_eq_norm_sq μ, h2]
      norm_num
    have hunitμ := hunit μ hμorth hμ1
    have hscale : ξ = ‖ξ‖ • μ := by
      rw [hμ]
      exact (smul_inv_smul₀ hξn ξ).symm
    have hnorm : ‖Zf (cov := cov) hmet q v ξ ρ‖ = ‖ξ‖ * ‖Zf (cov := cov) hmet q v μ ρ‖ := by
      conv_lhs => rw [hscale]
      rw [Zf_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg ξ)]
    rw [hnorm]
    calc ‖ξ‖ * ‖Zf (cov := cov) hmet q v μ ρ‖ ≤ ‖ξ‖ * (Real.sin ρ + 25 * ε₁) :=
          mul_le_mul_of_nonneg_left hunitμ (norm_nonneg ξ)
      _ = (Real.sin ρ + 25 * ε₁) * ‖ξ‖ := by ring

end Work.Diff.C.geoCrux.sharp
