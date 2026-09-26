/-
# The target statement `Work.FE.HomogeneousRigidity` is false: the missing hypothesis is `𝒫`

## What the paper proves

CKMRV's Lemma `lem:noPsolutions` (`univopt.tex`, line 3409) reads:

> No nonzero `f ∈ Ann₄(𝓘_±,𝒫)` satisfies `f(τ) = o(1)` … Likewise no nonzero
> `f ∈ Ann₁₂(𝓘_±,𝒫)` satisfies `f(τ) = o(e^{−2π Im τ})`.

and the Section 8 lemma that it feeds (`𝓘_± = (S ∓ I)R + (T − I)²R`) is stated for
`g, g̃ ∈ 𝒫`.  Here `𝒫` is the class of *holomorphic functions of moderate growth*,
`|F(τ)| ≤ α((Im τ)^{−β} + |τ|^γ)` (`Work.Kernels.InP`).  The growth hypothesis is used in
the paper's Proposition `prop: HFE plus` exactly once, to conclude that the invariant
function `h₂ = τ²g₀ − 2τg₁ + g₂` is a *classical* modular form rather than an arbitrary
modular function.

## What happens without it

Dropping `𝒫` enlarges the solution space enormously: for every holomorphic modular function
of weight `0` (e.g. every polynomial in `j`) one gets new solutions.  Concretely, for `k = 4`
the function

  `f₄ = φ₂·(E₄²E₆/Δ) + φ₀·E₄·(2016 − 2j) + φ₋₂·E₆·(j − 288)`

(where `φ₋₂ = τ`, `φ₀ = τE₂ − 3i/π`, `φ₂ = τE₂² − (6i/π)E₂` are the CKMRV basis functions,
`j` is the `j`-invariant `E₄³/Δ`, and `Δ` is the discriminant) is

* holomorphic on `ℍ` (`Δ` has no zeros there),
* annihilated by `(T − I)²` and by `S + I` at weight `4` (each term is `φ_j · (a function of
  `j`, of the complementary weight)`, and `φ_j` is annihilated by `(T − I)²` and `S + I`
  while `j` is `T`- and `S`-invariant),
* **nonzero**, and
* `o(1)` along the strip `−1 ≤ Re τ ≤ 1`: writing `f₄ = τ·A − (3i/π)·B` with
  `A = E₂²(E₄²E₆/Δ) + E₂E₄(2016 − 2j) + E₆(j − 288)` and `B = 2E₂(E₄²E₆/Δ) + E₄(2016 − 2j)`,
  the `q`-expansions of `A` and `B` begin at `q¹` — every coefficient of `q^n` with `n ≤ 0`
  cancels — while the coefficient of `q¹` in `A` is `−518400 ≠ 0`.  Hence
  `f₄ = Σ_{n ≥ 1}(τ A_n − (3i/π) B_n) q^n = O((1 + |τ|)|q|) = o(1)`.

The cancellation is an explicit finite computation with the `q`-expansions of `E₂, E₄, E₆, Δ`,
carried out (in exact rational arithmetic) by `verification/verify_ce.py` in this directory;
the same script verifies the weight-`12` analogue

  `f₁₂ = φ₂·E₁₀·(j − 510) + φ₀·Δ·(−2j² + 3036j − 362880) + φ₋₂·E₁₄·(j − 798)`,

whose `q`-expansion begins at `q²`, giving `f₁₂ = o(e^{−2π Im τ})`.

The bridge from the one-function statement to the two-variable one is:

* `Work.Rigidity.not_homogeneousRigidity_of_singleCounterexample` : *any* nonzero `f` with
  `(T − I)² f = 0`, `f ∣[k] S = −f` and the strip decay refutes the two-variable statement
  `Work.FE.HomogeneousRigidity n c` (take `g = g̃ = f/2`).  This is proved below.

So `Work.FE.HomogeneousRigidity 8 0` and `Work.FE.HomogeneousRigidity 24 1` — the two targets
of `Submission/Work/Rigidity/` — are **false** as stated in
`Submission/Work/FunctionalEquations/Gap.lean`, and the corrected statements are
`Work.Rigidity.HomogeneousRigidityP 8 0` and `Work.Rigidity.HomogeneousRigidityP 24 1`
(`ModerateGrowth.lean`), which carry the paper's hypothesis `g, g̃ ∈ 𝒫`.
-/
import Mathlib
import Submission.Work.Rigidity.Reduction

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

open Filter

/-- The coercion of `ofComplex τ` is `τ` when `0 < Im τ`. -/
lemma coe_ofComplex_of_pos {τ : ℂ} (h : 0 < τ.im) :
    ((UpperHalfPlane.ofComplex τ : ℍ) : ℂ) = τ := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos h]

/-- On the upper half plane, `ofComplex (τ + 2) = 2 +ᵥ ofComplex τ`. -/
lemma ofComplex_add_two_of_pos {τ : ℂ} (h : 0 < τ.im) :
    UpperHalfPlane.ofComplex (τ + 2) = (2 : ℝ) +ᵥ UpperHalfPlane.ofComplex τ := by
  apply UpperHalfPlane.ext
  rw [coe_ofComplex_of_pos (by simp [h]), UpperHalfPlane.coe_vadd, coe_ofComplex_of_pos h]
  push_cast
  ring

/-- On the upper half plane, `ofComplex (τ + 1) = 1 +ᵥ ofComplex τ`. -/
lemma ofComplex_add_one_of_pos {τ : ℂ} (h : 0 < τ.im) :
    UpperHalfPlane.ofComplex (τ + 1) = (1 : ℝ) +ᵥ UpperHalfPlane.ofComplex τ := by
  apply UpperHalfPlane.ext
  rw [coe_ofComplex_of_pos (by simp [h]), UpperHalfPlane.coe_vadd, coe_ofComplex_of_pos h]
  push_cast
  ring

/-- On the upper half plane, `ofComplex (-1/τ) = S • ofComplex τ`. -/
lemma ofComplex_neg_one_div {τ : ℂ} (h : 0 < τ.im) :
    UpperHalfPlane.ofComplex (-1 / τ) = ModularGroup.S • UpperHalfPlane.ofComplex τ := by
  have h' : 0 < (-1 / τ).im := by
    have h1 : 0 < (ModularGroup.S • (⟨τ, h⟩ : ℍ)).im :=
      (ModularGroup.S • (⟨τ, h⟩ : ℍ)).im_pos
    have h2 : (((ModularGroup.S • (⟨τ, h⟩ : ℍ)) : ℍ) : ℂ) = -1 / τ := by
      simp only [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg,
        neg_one_div]
    rw [← UpperHalfPlane.coe_im, h2] at h1
    exact h1
  apply UpperHalfPlane.ext
  rw [coe_ofComplex_of_pos h', UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
    coe_ofComplex_of_pos h, inv_neg, neg_one_div]

/-- **A single-function counterexample refutes the two-variable statement.**  If `f ≠ 0` is
holomorphic, killed by `(T − I)²`, satisfies `f ∣[k] S = −f` and the strip decay, then the
pair `(f/2, f/2)` satisfies all the hypotheses of `Work.FE.HomogeneousRigidity n c` (with
`(i/τ)^k = τ^{-k}`) but not its conclusion. -/
theorem not_homogeneousRigidity_of_singleCounterexample {n : ℕ} [NeZero n] {k : ℤ} {c : ℝ}
    (hsf : ∀ τ : ℍ, Work.FE.slashFactor n (τ : ℂ) = (τ : ℂ) ^ (-k))
    {f : ℍ → ℂ} (hfne : f ≠ 0) (hmf : MDiff f) (hT2 : AnnT2 f) (hS : SlashEigen k (-1) f)
    (hdec : StripDecay c f) :
    ¬ Work.FE.HomogeneousRigidity n c := by
  intro H
  set g : ℂ → Work.FE.E n → ℂ :=
    fun τ _ => f (UpperHalfPlane.ofComplex τ) / 2 with hg
  have hdiff : ∀ x : Work.FE.E n,
      DifferentiableOn ℂ (fun τ : ℂ => g τ x) {τ : ℂ | 0 < τ.im} := by
    intro x
    have h := (UpperHalfPlane.mdifferentiable_iff.mp hmf)
    simpa [hg] using h.div_const 2
  have hT2g : ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
      g (τ + 2) x - 2 * g (τ + 1) x + g τ x = 0 := by
    intro τ x hτ
    have e2 := ofComplex_add_two_of_pos hτ
    have e1 := ofComplex_add_one_of_pos hτ
    have h := congrFun hT2 (UpperHalfPlane.ofComplex τ)
    simp only [Work.Kernels.T2op, Pi.zero_apply] at h
    simp only [hg]
    rw [e2, e1]
    linear_combination h / 2
  have hSg : ∀ (τ : ℂ) (x : Work.FE.E n), 0 < τ.im →
      g τ x + Work.FE.slashFactor n τ * g (-1 / τ) x = 0 := by
    intro τ x hτ
    have e := ofComplex_neg_one_div hτ
    have h := hS (UpperHalfPlane.ofComplex τ)
    rw [Work.Kernels.slash_S_apply, coe_ofComplex_of_pos hτ] at h
    -- h : f (S • ofComplex τ) * τ ^ (-k) = -1 * f (ofComplex τ)
    have hsf' : Work.FE.slashFactor n τ = τ ^ (-k) := by
      have := hsf ⟨τ, hτ⟩
      simpa using this
    simp only [hg]
    rw [e, hsf']
    linear_combination h / 2
  have hdecg : Work.FE.TendsToZeroInStrip n c g := by
    intro x
    obtain ⟨φ, hφ, hφ'⟩ := hdec
    refine ⟨φ, hφ, fun τ hτ h1 h2 => ?_⟩
    have hτ' : InStrip (UpperHalfPlane.ofComplex τ) := by
      refine ⟨?_, ?_⟩
      · rw [← UpperHalfPlane.coe_re, coe_ofComplex_of_pos hτ]; exact h1
      · rw [← UpperHalfPlane.coe_re, coe_ofComplex_of_pos hτ]; exact h2
    have hb := hφ' (UpperHalfPlane.ofComplex τ) hτ'
    rw [← UpperHalfPlane.coe_im, coe_ofComplex_of_pos hτ] at hb
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    simp only [hg]
    rw [norm_div, h2]
    linarith [hb, norm_nonneg (f (UpperHalfPlane.ofComplex τ))]
  have hzero := H g g hdiff hdiff hT2g hT2g hSg hdecg hdecg
  apply hfne
  funext s
  have hzero' := (hzero (s : ℂ) (Classical.arbitrary (Work.FE.E n)) s.im_pos).1
  simp only [hg, UpperHalfPlane.ofComplex_apply] at hzero'
  have h2 : f s = 2 * (f s / 2) := by ring
  rw [hzero'] at h2
  simpa using h2

end Work.Rigidity
