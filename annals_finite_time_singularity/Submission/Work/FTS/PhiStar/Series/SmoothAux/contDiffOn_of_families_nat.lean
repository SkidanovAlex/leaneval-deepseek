/-
# `contDiffOn_of_families_nat` — the corrected (ℕ-indexed) bootstrap

The statement delivered as `Work.FTS.PhiStar.Series.SmoothAux.contDiffOn_of_families`
(file `contDiffOn_of_families.lean` in this directory) is **false as written**: its trailing
binder `∀ n, ...` is elaborated at the order type `ℕ∞ω = WithTop ℕ∞`, not at `ℕ`, because the
order argument of `ContDiffOn` has that type.  The delivered statement therefore also demands the
case `n = ω`, i.e. that `R` be *analytic* on the open quadrant `Q0`, which the hypotheses do not
imply (see `NOTES_contDiffOn_of_families_FALSE.md` in this directory for the counterexample:
`R z θ = Real.smoothTransition (z - 1)`, `Z a = iteratedDeriv a R`, `V = W = G = 0`).

This file contains the statement the requester intended — the same hypotheses with the conclusion
restricted to `n : ℕ` — together with a complete, `sorry`-free proof.  It is what the bootstrap
described in `SmoothAux/Main.lean` actually needs (`∀ n : ℕ` is exactly the hypothesis of
`Work.FTS.EllipticEst.smoothOpen_of_forall`, giving `SmoothOpen R`, i.e. `C^∞` of `R` on the open
quadrant).

The proof is an induction on `n` with the package
`P(n) := (∀ a, Z a ∈ C^n) ∧ (∀ a, V a ∈ C^n) ∧ (∀ a, W a ∈ C^n)` on the open quadrant:

* `P(0)` is the continuity hypothesis `hcZ`, `hcV`, `hcW`;
* `hG n` turns `P(n)` into `∀ a, G a ∈ C^n`;
* `P(n) → P(n+1)`: each of `Z a`, `V a`, `W a` is `C^{n+1}` because both of its slice derivatives
  are `C^n` (`contDiffOn_succ_of_partials`): for `∂_z` this shifts the `a`-index at level `n`
  (induction hypothesis), for `∂_θ` this moves along the chain `Z → V → W → G` (`G` enters only
  at level `n` via `hG n`).

The criterion `contDiffOn_succ_of_partials` is the two-variable form of "`C^{n+1}` from `C^n`
partials"; its analytic input is Mathlib's `hasStrictFDerivAt_uncurry_coprod`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Filter

namespace Work.FTS.PhiStar.Series.SmoothAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The criterion `C^{n+1}` from `C^n` partial derivatives -/

/-- The continuous linear map `(x, y) ↦ ((a, b) ↦ a * x + b * y)` from `ℝ²` to `ℝ² →L[ℝ] ℝ`;
it is the total derivative of a function whose partial derivatives at the point are `x` and `y`. -/
def cclm : ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ) :=
  (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ))
  + (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma cclm_apply (p z : ℝ × ℝ) : cclm p z = z.1 * p.1 + z.2 * p.2 := by
  obtain ⟨x, y⟩ := p
  obtain ⟨a, b⟩ := z
  simp only [cclm, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rfl

lemma cclm_eq (x y : ℝ) :
    cclm (x, y) = (ContinuousLinearMap.toSpanSingleton ℝ x).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ y) := by
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨a, b⟩ := z
  simp only [cclm_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  ring

/-- **`C¹` from continuous partial derivatives.**  On an open set `U`, if both slice derivatives of
`f` exist everywhere on `U` and the corresponding partial-derivative functions `g`, `h` are
continuous on `U`, then `uncurry f` is differentiable at every point of `U`, with derivative the
continuous linear map whose matrix is `(g p, h p)`. -/
theorem hasFDerivAt_of_hasDerivAt_slices {f g h : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hg : ContinuousOn (Function.uncurry g) U)
    (hh : ContinuousOn (Function.uncurry h) U)
    (hz : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun z' => f z' θ) (g z θ) z)
    (hθ : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun θ' => f z θ') (h z θ) θ) :
    ∀ p ∈ U, HasFDerivAt (Function.uncurry f) (cclm (g p.1 p.2, h p.1 p.2)) p := by
  intro p hp
  have hcts : Continuous fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous
  have hdf₁ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun z' => f z' v.2)
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (g a b)) v) v.1 :=
    mem_of_superset (hU.mem_nhds hp) fun v hv => (hz v.1 v.2 hv).hasFDerivAt
  have hdf₂ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun θ' => f v.1 θ')
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (h a b)) v) v.2 :=
    mem_of_superset (hU.mem_nhds hp) fun v hv => (hθ v.1 v.2 hv).hasFDerivAt
  have hc₁ : ContinuousAt
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (g a b))) p :=
    hcts.continuousAt.comp (hg.continuousAt (hU.mem_nhds hp))
  have hc₂ : ContinuousAt
      (Function.uncurry (fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (h a b))) p :=
    hcts.continuousAt.comp (hh.continuousAt (hU.mem_nhds hp))
  have hmain := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p) (f := f)
    (f₁ := fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (g a b))
    (f₂ := fun a b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (h a b))
    hdf₁ hdf₂ hc₁ hc₂
  refine hmain.hasFDerivAt.congr_fderiv ?_
  show (ContinuousLinearMap.toSpanSingleton ℝ (g p.1 p.2)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (h p.1 p.2)) = cclm (g p.1 p.2, h p.1 p.2)
  rw [cclm_eq]

/-- **`C^{n+1}` from `C^n` partial derivatives.**  If the two slice derivatives of `f` are given
pointwise on the open set `U` by the functions `g`, `h` and both of these are `C^n` on `U`, then
`f` is `C^{n+1}` on `U`. -/
theorem contDiffOn_succ_of_partials {f g h : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : ℕ}
    (hz : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun z' => f z' θ) (g z θ) z)
    (hθ : ∀ (z θ : ℝ), (z, θ) ∈ U → HasDerivAt (fun θ' => f z θ') (h z θ) θ)
    (hg : ContDiffOn ℝ n (Function.uncurry g) U)
    (hh : ContDiffOn ℝ n (Function.uncurry h) U) :
    ContDiffOn ℝ (n + 1) (Function.uncurry f) U := by
  have hF' : ∀ p ∈ U, HasFDerivAt (Function.uncurry f) (cclm (g p.1 p.2, h p.1 p.2)) p :=
    hasFDerivAt_of_hasDerivAt_slices hU hg.continuousOn hh.continuousOn hz hθ
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).2 ?_
  refine ⟨fun hn => absurd hn (by simp), fun p => cclm (g p.1 p.2, h p.1 p.2), ?_, ?_⟩
  · exact cclm.contDiff.comp_contDiffOn (hg.prodMk hh)
  · intro p hp
    exact (hF' p hp).hasFDerivWithinAt

/-! ## The corrected bootstrap -/

/-- **The ℕ-indexed bootstrap.**  If the `z`-chains `Z`, `V`, `W` (the successive `z`-derivatives
of `R = Z 0` and of its first two `θ`-derivatives) are continuous on the open quadrant `Q0`, with
the differentiation chains `∂_z Z a = Z (a+1)`, `∂_z V a = V (a+1)`, `∂_z W a = W (a+1)`,
`∂_θ Z a = V a`, `∂_θ V a = W a`, and if `G` (the `θ`-derivative of `W`) is `C^n` whenever the
three families are `C^n`, then `R` is `C^n` on `Q0` for every `n : ℕ` (hence `C^∞`).

This is the statement intended by the requester of `contDiffOn_of_families`; the delivered version
of that lemma quantifies `n` over the whole order type `ℕ∞ω`, hence also over the *analytic* order
`ω`, and is false (`NOTES_contDiffOn_of_families_FALSE.md`). -/
theorem contDiffOn_of_families_nat {Z V W G : ℕ → ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    (hZ0 : ∀ z θ, Z 0 z θ = R z θ)
    (hZz : ∀ (a : ℕ) (z θ : ℝ), (z,θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' => Z a z' θ) (Z (a+1) z θ) z)
    (hVz : ∀ (a : ℕ) (z θ : ℝ), (z,θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' => V a z' θ) (V (a+1) z θ) z)
    (hWz : ∀ (a : ℕ) (z θ : ℝ), (z,θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' => W a z' θ) (W (a+1) z θ) z)
    (hZV : ∀ (a : ℕ) (z θ : ℝ), (z,θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' => Z a z θ') (V a z θ) θ)
    (hVW : ∀ (a : ℕ) (z θ : ℝ), (z,θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' => V a z θ') (W a z θ) θ)
    (hWG : ∀ (a : ℕ) (z θ : ℝ), (z,θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' => W a z θ') (G a z θ) θ)
    (hcZ : ∀ a, ContinuousOn (Function.uncurry (Z a)) Work.FTS.EllipticEst.Q0)
    (hcV : ∀ a, ContinuousOn (Function.uncurry (V a)) Work.FTS.EllipticEst.Q0)
    (hcW : ∀ a, ContinuousOn (Function.uncurry (W a)) Work.FTS.EllipticEst.Q0)
    (hG : ∀ (n : ℕ), (∀ a, ContDiffOn ℝ n (Function.uncurry (Z a)) Work.FTS.EllipticEst.Q0) →
      (∀ a, ContDiffOn ℝ n (Function.uncurry (V a)) Work.FTS.EllipticEst.Q0) →
      (∀ a, ContDiffOn ℝ n (Function.uncurry (W a)) Work.FTS.EllipticEst.Q0) →
      ∀ a, ContDiffOn ℝ n (Function.uncurry (G a)) Work.FTS.EllipticEst.Q0) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry R) Work.FTS.EllipticEst.Q0 := by
  have hU : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have key : ∀ n : ℕ,
      (∀ a, ContDiffOn ℝ n (Function.uncurry (Z a)) Work.FTS.EllipticEst.Q0) ∧
      (∀ a, ContDiffOn ℝ n (Function.uncurry (V a)) Work.FTS.EllipticEst.Q0) ∧
      (∀ a, ContDiffOn ℝ n (Function.uncurry (W a)) Work.FTS.EllipticEst.Q0) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun a => ?_, fun a => ?_, fun a => ?_⟩
      · simpa using (contDiffOn_zero (𝕜 := ℝ)).mpr (hcZ a)
      · simpa using (contDiffOn_zero (𝕜 := ℝ)).mpr (hcV a)
      · simpa using (contDiffOn_zero (𝕜 := ℝ)).mpr (hcW a)
    | succ n ih =>
      obtain ⟨ihZ, ihV, ihW⟩ := ih
      have hG' : ∀ a, ContDiffOn ℝ n (Function.uncurry (G a)) Work.FTS.EllipticEst.Q0 :=
        hG n ihZ ihV ihW
      refine ⟨fun a => ?_, fun a => ?_, fun a => ?_⟩
      · exact contDiffOn_succ_of_partials hU (fun z θ h => hZz a z θ h)
          (fun z θ h => hZV a z θ h) (ihZ (a + 1)) (ihV a)
      · exact contDiffOn_succ_of_partials hU (fun z θ h => hVz a z θ h)
          (fun z θ h => hVW a z θ h) (ihV (a + 1)) (ihW a)
      · exact contDiffOn_succ_of_partials hU (fun z θ h => hWz a z θ h)
          (fun z θ h => hWG a z θ h) (ihW (a + 1)) (hG' a)
  intro n
  exact ((key n).1 0).congr (fun p _ => (hZ0 p.1 p.2).symm)

end Work.FTS.PhiStar.Series.SmoothAux
