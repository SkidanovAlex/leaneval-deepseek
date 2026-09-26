/-
# Weight-twelve rigidity, eigenvalue `+1`: `SingleRigidityP 12 1 1`

This file proves the paper's Lemma `lem:noPsolutions` at `(k, ε, c) = (12, +1, 1)`, i.e.
CKMRV, *Universal optimality of the E8 and Leech lattices and interpolation formulas*,
Ann. of Math. 196 (2022), Lemma `lem:noPsolutions`, in the `(S − I)`-eigen case at weight
twelve:

> no nonzero `f ∈ Ann₁₂(𝓘₋, 𝒫)` satisfies `f(τ) = o(e^{-2π Im τ})` along the strip
> `-1 ≤ Re τ ≤ 1`.

## Structure of the proof

Let `f` satisfy the hypotheses: `f ∈ 𝒫` (moderate growth, `Work.Kernels.InP`), `(T-I)²f = 0`,
`f ∣[12] S = f`, and the strip decay `o(e^{-2π Im τ})`.  Put

  `P := fstDiff f = f(τ+1) − f(τ)`.

Then

* `P` is holomorphic (`MDiff`) and lies in `𝒫` (moderate growth), since it is a difference of
  translates of `f` (`InP_fstDiff`);
* `P` is `1`-periodic (`fstDiff_vadd_one_iff`);
* `P` satisfies the trace identity
  `P τ + τ^{-12} P(S•τ) + (τ+1)^{-12} P(S•(τ+1)) = 0` (`fstDiff_trace`);
* `P = O(e^{-4π Im τ})` for `Im τ ≥ 1` (`fstDiff_q2_bound`), i.e. in terms of `q = e^{2πiτ}`
  the `q`-expansion of `P` starts at order `q²`.

The heart of the argument is the rigidity statement `FstDiffRigidTwelve` for `P`, proved from
the paper's description of `Ann₁₂(𝓘₋,𝒫)` and the `q`-expansion computation of
`lem:noPsolutions`:

* `Work.Rigidity.XiClassificationTwelve`: the first difference of a solution lies in
  `ξ₄M₈(Γ(1)) + ξ₂M₁₀(Γ(1)) = ℂ·ξ₄E₄² ⊕ ℂ·ξ₂E₄E₆` (CKMRV Proposition 4.3, via the
  Eichler–Zagier decomposition of `M(Γ(2))`);
* `Work.Rigidity.XiCombinationDecay`: the `o(q)` bound forces `c₁ = c₂ = 0` in
  `c₁ξ₄E₄² + c₂ξ₂E₄E₆` (the `q⁰` and `q¹` coefficients are `2c₁ + 2c₂` and
  `672c₁ − 480c₂`).

Finally `fstDiff f = 0` makes `f` invariant under `T`, so `f` is holomorphic, `T`- and
`S`-invariant of weight twelve and decays like `o(e^{-2π Im τ})` in the strip:
`Work.Rigidity.invariant_decay_eq_zero` (a weight-twelve level-one Sturm-bound argument via
the vanishing of the first two `q`-coefficients) gives `f = 0`.
-/
import Mathlib
import Submission.Work.Rigidity.ModerateGrowth
import Submission.Work.Rigidity.fstDiff_q2_bound
import Submission.Work.Rigidity.fstDiff_trace
import Submission.Work.Rigidity.invariant_decay_eq_zero
import Submission.Work.Rigidity.XiClassificationTwelve
import Submission.Work.Rigidity.XiCombinationDecay

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

open Filter

/-! ## The first difference of a function of `𝒫` -/

/-- The weight-`k` slash action of `T` is translation: `(F ∣[k] T) τ = F (τ + 1)`. -/
lemma slash_T_eq_shift (k : ℤ) (F : ℍ → ℂ) :
    F ∣[k] ModularGroup.T = fun τ : ℍ => F ((1 : ℝ) +ᵥ τ) := by
  funext τ
  rw [Work.Kernels.slash_apply', Work.Kernels.jFun_apply, UpperHalfPlane.modular_T_smul]
  have h10 : ((ModularGroup.T : SL(2, ℤ)) 1 0 : ℂ) = 0 := by simp [ModularGroup.coe_T]
  have h11 : ((ModularGroup.T : SL(2, ℤ)) 1 1 : ℂ) = 1 := by simp [ModularGroup.coe_T]
  rw [h10, h11, zero_mul, zero_add, _root_.one_zpow, mul_one]

/-- The first difference of a holomorphic function is holomorphic. -/
lemma mdifferentiable_fstDiff {f : ℍ → ℂ} (hf : MDiff f) : MDiff (fstDiff f) := by
  have h1 : fstDiff f = f ∣[(4 : ℤ)] ModularGroup.T - f := by
    funext τ
    rw [fstDiff_apply, slash_T_eq_shift]
    rfl
  rw [h1]
  exact ((hf.slash (4 : ℤ) (Work.Kernels.glOf ModularGroup.T))).sub hf

/-- The first difference of a function of moderate growth has moderate growth. -/
lemma InP_fstDiff {f : ℍ → ℂ} (hf : Work.Kernels.InP f) : Work.Kernels.InP (fstDiff f) := by
  have h1 : fstDiff f = f ∣[(4 : ℤ)] ModularGroup.T - f := by
    funext τ
    rw [fstDiff_apply, slash_T_eq_shift]
    rfl
  rw [h1]
  exact (Work.Kernels.InP.slash hf (4 : ℤ) ModularGroup.T).sub hf

/-- The weight-`12` slash of `P` by `S` is `τ ↦ τ^{-12} P (S • τ)`. -/
lemma slash_S_eq (P : ℍ → ℂ) :
    P ∣[(12 : ℤ)] ModularGroup.S = fun τ : ℍ => (τ : ℂ) ^ (-12 : ℤ) * P (ModularGroup.S • τ) := by
  funext τ
  rw [Work.Kernels.slash_apply', Work.Kernels.jFun_apply]
  have h10 : ((ModularGroup.S : SL(2, ℤ)) 1 0 : ℂ) = 1 := by simp [ModularGroup.coe_S]
  have h11 : ((ModularGroup.S : SL(2, ℤ)) 1 1 : ℂ) = 0 := by simp [ModularGroup.coe_S]
  rw [h10, h11, one_mul, add_zero]
  ring

/-! ## Exponential decay helpers

These transfer the `q²` bound of `P` into the shape needed by the `o(q)`-form of the paper's
`q`-expansion computation (`Work.Rigidity.XiCombinationDecay`). -/

/-- `exp (-(c Im τ)) → 0` along `Im τ → ∞`. -/
lemma tendsto_exp_neg_im_atImInfty {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun τ : ℍ => Real.exp (-(c * τ.im))) UpperHalfPlane.atImInfty (nhds 0) := by
  have hg : Filter.Tendsto (fun y : ℝ => Real.exp (-(c * y))) atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => c * y) atTop atTop := tendsto_id.const_mul_atTop hc
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  rw [UpperHalfPlane.atImInfty]
  exact hg.comp (Filter.tendsto_comap (f := fun τ : ℍ => τ.im))

/-- A `q²` bound along the strip gives the `o(q)` bound in exponential form. -/
lemma tendsto_norm_mul_exp_atImInfty {P : ℍ → ℂ}
    (hq2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖P τ‖ ≤ C * Real.exp (-(4 * Real.pi * τ.im))) :
    Filter.Tendsto (fun τ : ℍ => ‖P τ‖ * Real.exp (2 * Real.pi * τ.im))
      UpperHalfPlane.atImInfty (nhds 0) := by
  obtain ⟨C, _hC, hbound⟩ := hq2
  have hev : ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty, (1 : ℝ) ≤ τ.im := by
    rw [UpperHalfPlane.atImInfty, Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨1, fun y hy a ha => ?_⟩
    rw [ha]; exact hy
  refine squeeze_zero' (f := fun τ : ℍ => ‖P τ‖ * Real.exp (2 * Real.pi * τ.im))
    (g := fun τ : ℍ => C * Real.exp (-(2 * Real.pi * τ.im))) ?_ ?_ ?_
  · filter_upwards with τ; positivity
  · filter_upwards [hev] with τ hτ
    calc ‖P τ‖ * Real.exp (2 * Real.pi * τ.im)
        ≤ (C * Real.exp (-(4 * Real.pi * τ.im))) * Real.exp (2 * Real.pi * τ.im) :=
          mul_le_mul_of_nonneg_right (hbound τ hτ) (Real.exp_nonneg _)
      _ = C * Real.exp (-(2 * Real.pi * τ.im)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  · have h := tendsto_exp_neg_im_atImInfty (c := 2 * Real.pi) (by positivity)
    simpa using h.const_mul C

/-! ## The rigidity statement for the first difference -/

/-- **The rigidity statement for the first difference at weight twelve, eigenvalue `+1`.**

CKMRV Proposition 4.3 (the description of `Ann₁₂(𝓘₋,𝒫)`) together with the `q`-expansion
computation of `lem:noPsolutions`: a holomorphic `P ∈ 𝒫` which is `1`-periodic, satisfies the
trace identity `P + P∣[12]S + P∣[12]ST = 0` and whose `q`-expansion starts at order `q²`
vanishes. -/
theorem FstDiffRigidTwelve (P : ℍ → ℂ) (hP : Work.Kernels.InP P)
    (hper : ∀ τ : ℍ, P ((1 : ℝ) +ᵥ τ) = P τ)
    (htrace : ∀ τ : ℍ, P τ + (τ : ℂ) ^ (-12 : ℤ) * P (ModularGroup.S • τ)
        + ((τ : ℂ) + 1) ^ (-12 : ℤ) * P (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) = 0)
    (hq2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖P τ‖ ≤ C * Real.exp (-(4 * Real.pi * τ.im))) :
    P = 0 := by
  -- `P ∣[12] S` is again of moderate growth: it is `τ ↦ τ^{-12} P (S • τ)`.
  have hPS : Work.Kernels.InP (fun τ : ℍ => (τ : ℂ) ^ (-12 : ℤ) * P (ModularGroup.S • τ)) := by
    rw [← slash_S_eq P]
    exact Work.Kernels.InP.slash hP 12 ModularGroup.S
  -- the classification of the solutions of the trace system
  obtain ⟨c1, c2, hc⟩ := Work.Rigidity.XiClassificationTwelve P hP hPS hper htrace
  -- the `q²` bound upgrades to `o(q)`
  have hlim : Filter.Tendsto (fun τ : ℍ => ‖P τ‖ * Real.exp (2 * Real.pi * τ.im))
      UpperHalfPlane.atImInfty (nhds 0) := tendsto_norm_mul_exp_atImInfty hq2
  have hlim' : Filter.Tendsto (fun τ : ℍ =>
        ‖c1 * Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2
          + c2 * Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ‖
        * Real.exp (2 * Real.pi * τ.im)) UpperHalfPlane.atImInfty (nhds 0) := by
    refine hlim.congr' ?_
    filter_upwards with τ
    rw [hc τ]
    ring_nf
  obtain ⟨h1, h2⟩ := Work.Rigidity.XiCombinationDecay c1 c2 hlim'
  funext τ
  have h0 : P τ = 0 := by
    rw [hc τ, h1, h2]
    ring
  exact h0

/-! ## The target -/

/-- **The paper's `lem:noPsolutions` at `k = 12`, `ε = +1`, `c = 1`.** -/
theorem AnnMinusWeightTwelveP : Work.Rigidity.SingleRigidityP 12 (1 : ℂ) 1 := by
  intro f hfP hT2 hS hdec
  have hhol : MDiff f := hfP.1
  -- the first difference satisfies the hypotheses of the rigidity statement for `P`
  have hper : ∀ τ : ℍ, fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ :=
    (fstDiff_vadd_one_iff f).mp hT2
  have htrace := fstDiff_trace hT2 hS
  have hq2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖fstDiff f τ‖ ≤ C * Real.exp (-(4 * Real.pi * τ.im)) :=
    fstDiff_q2_bound hhol hT2 hdec
  have hzero : fstDiff f = 0 :=
    FstDiffRigidTwelve (fstDiff f) (InP_fstDiff hfP) hper htrace hq2
  -- hence `f` is invariant under `T`
  have hT : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ := by
    intro τ
    have h := congrFun hzero τ
    simp only [fstDiff, Pi.zero_apply] at h
    linear_combination h
  -- and `S`-invariant of weight twelve, in the form used by `invariant_decay_eq_zero`
  have hS' : ∀ τ : ℍ, (τ : ℂ) ^ (-12 : ℤ) * f (ModularGroup.S • τ) = f τ := by
    intro τ
    have h := hS τ
    rw [slash_S_apply, one_mul] at h
    exact h
  exact invariant_decay_eq_zero hhol hT hS' hdec

end

end Work.Rigidity
