import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.StrongLWP.Sobolev

/-!
# `C⁴` from a continuous partial-derivative tower on an open subset of `ℝ²`

The main result below, `contDiffOn_four_of_partial_tower`, shows that a function
`F = Function.uncurry φ : ℝ × ℝ → ℝ` is `C⁴` on an open set `U` as soon as there is a
"partial derivative tower" `D : ℕ → ℕ → ℝ → ℝ → ℝ` with

* `D 0 0 = φ`,
* every `D a b` with `a + b ≤ 4` is continuous on `U`,
* the two one-variable slices of `D a b` have one-sided (in fact two-sided) derivatives
  `D (a+1) b` resp. `D a (b+1)` on `U`, for `a + b ≤ 3`.

The proof is an induction on the order `n ∈ {0,1,2,3,4}` of the statement
`main n` ("a continuous tower up to order `n` and slice derivatives up to order `n-1`
give `ContDiffOn ℝ n`").  The induction step needs the classical fact that a function on
an open subset of `ℝ × ℝ` whose two slice derivatives exist everywhere and are
continuous is (strictly) Fréchet differentiable with derivative given by the two slices —
Mathlib's `hasStrictFDerivAt_uncurry_coprod` — together with the observation that the
Fréchet derivative function `fderivWithin ℝ F U`, written in terms of the two slice
derivatives, is `Cⁿ` as soon as the two slice derivatives are (closure of `ContDiffOn`
under postcomposition with the continuous linear map `(x,y) ↦ x ⊗ fst + y ⊗ snd`).
-/

/-- The continuous linear map `ℝ × ℝ →L[ℝ] ℝ` which is the Fréchet derivative of a
function with slice derivatives `x` (in the first variable) and `y` (in the second). -/
private noncomputable def cop (x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).coprod (ContinuousLinearMap.toSpanSingleton ℝ y)

/-- `p ↦ cop (a p) (b p)` is `Cⁿ` on `U` when `a` and `b` are.  This is the closure step
that makes the induction below possible: the Fréchet derivative function of a function with
continuous slice derivatives is built from those slice derivatives by a fixed continuous
linear operation. -/
private lemma cop_pair_eq {n : WithTop ℕ∞} {U : Set (ℝ × ℝ)} {a b : ℝ × ℝ → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U) :
    ContDiffOn ℝ n (fun p => cop (a p) (b p)) U := by
  have heq : (fun q : ℝ × ℝ => cop q.1 q.2)
      = fun q : ℝ × ℝ =>
        q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + q.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    funext q
    apply ContinuousLinearMap.ext
    intro v
    rw [show cop q.1 q.2 v = v.1 * q.1 + v.2 * q.2 from by
      simp [cop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul]]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) v = v.1 from rfl,
        show (ContinuousLinearMap.snd ℝ ℝ ℝ) v = v.2 from rfl]
    ring
  have hc : ContDiff ℝ n (fun q : ℝ × ℝ => cop q.1 q.2) := by
    rw [heq]
    exact ((contDiff_fst (𝕜 := ℝ)).smul_const _).add ((contDiff_snd (𝕜 := ℝ)).smul_const _)
  have h := hc.comp_contDiffOn (ha.prodMk hb)
  simpa [Function.comp_def] using h

/-- The map `c ↦ x ↦ x • c` is continuous. -/
private lemma continuous_toSpanSingleton :
    Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ)) := by
  have h : (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ))
      = ⇑(ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)) := by
    funext c
    simp [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous

/-- **Slice derivatives give the Fréchet derivative.**  If the two one-variable slices of
`φ` have derivative `a z θ` resp. `b z θ` at every point of the open set `U`, and these slice
derivative functions are continuous on `U`, then `Function.uncurry φ` is differentiable on
`U`, with `fderivWithin ℝ (Function.uncurry φ) U p = cop (a p.1 p.2) (b p.1 p.2)`. -/
private lemma differentiableOn_uncurry_of_slices {φ : ℝ → ℝ → ℝ} {a b : ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (ha : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (a z θ) z)
    (hb : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (b z θ) θ)
    (hca : ContinuousOn (Function.uncurry a) U) (hcb : ContinuousOn (Function.uncurry b) U) :
    DifferentiableOn ℝ (Function.uncurry φ) U ∧
      Set.EqOn (fderivWithin ℝ (Function.uncurry φ) U)
        (fun p => cop (a p.1 p.2) (b p.1 p.2)) U := by
  have key : ∀ p ∈ U, HasFDerivAt (Function.uncurry φ) (cop (a p.1 p.2) (b p.1 p.2)) p := by
    intro p hp
    have hmem : U ∈ 𝓝 p := hU.mem_nhds hp
    have h1 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ x v.2)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ)) v) v.1 := by
      filter_upwards [hmem] with v hv
      exact (ha v.1 v.2 hv).hasFDerivAt
    have h2 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ v.1 x)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) v) v.2 := by
      filter_upwards [hmem] with v hv
      exact (hb v.1 v.2 hv).hasFDerivAt
    have c1 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hca.continuousAt hmem)
    have c2 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hcb.continuousAt hmem)
    have h := hasStrictFDerivAt_uncurry_coprod (u := p) (f := φ)
      (f₁ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))
      (f₂ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) h1 h2 c1 c2
    exact h.hasFDerivAt
  constructor
  · intro p hp; exact (key p hp).differentiableAt.differentiableWithinAt
  · intro p hp
    exact ((key p hp).hasFDerivWithinAt).fderivWithin (hU.uniqueDiffOn p hp)

/-- **The induction.**  Given a partial-derivative tower continuous up to order `n` on the
open set `U`, whose slices are differentiable with the next tower entries as derivatives for
all `a + b < n`, the function `Function.uncurry φ` is `Cⁿ` on `U`. -/
private theorem main : ∀ n : ℕ, ∀ (φ : ℝ → ℝ → ℝ) (D : ℕ → ℕ → ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)),
    IsOpen U → (∀ z θ, φ z θ = D 0 0 z θ) →
    (∀ a b, a + b ≤ n → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U) →
    (∀ a b, a + b < n → ∀ z θ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z) →
    (∀ a b, a + b < n → ∀ z θ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ) →
    ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry φ) U := by
  intro n
  induction n with
  | zero =>
      intro φ D U hU hφ hcont hsz hth
      have h : ContinuousOn (Function.uncurry φ) U :=
        (hcont 0 0 le_rfl).congr (fun p hp => hφ p.1 p.2)
      simpa [Nat.cast_zero] using (contDiffOn_zero (𝕜 := ℝ)).2 h
  | succ k ih =>
      intro φ D U hU hφ hcont hsz hth
      -- the two slice derivative functions `D 1 0` and `D 0 1` are `Cᵏ` by induction,
      -- applied to the shifted towers
      have hcontX : ContDiffOn ℝ k (Function.uncurry (D 1 0)) U :=
        ih (D 1 0) (fun i j => D (i + 1) j) U hU (fun z θ => rfl)
          (fun i j hij => hcont (i + 1) j (by omega))
          (fun i j hij z θ hz => hsz (i + 1) j (by omega) z θ hz)
          (fun i j hij z θ hz => hth (i + 1) j (by omega) z θ hz)
      have hcontY : ContDiffOn ℝ k (Function.uncurry (D 0 1)) U :=
        ih (D 0 1) (fun i j => D i (j + 1)) U hU (fun z θ => rfl)
          (fun i j hij => hcont i (j + 1) (by omega))
          (fun i j hij z θ hz => hsz i (j + 1) (by omega) z θ hz)
          (fun i j hij z θ hz => hth i (j + 1) (by omega) z θ hz)
      -- the slice derivatives of `φ` itself
      have hsz0 : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (D 1 0 z θ) z := by
        intro z θ hz
        have hfs : (fun z' => φ z' θ) = fun z' => D 0 0 z' θ := funext fun z' => hφ z' θ
        rw [hfs]
        exact hsz 0 0 (by omega) z θ hz
      have hth0 : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (D 0 1 z θ) θ := by
        intro z θ hz
        have hfs : (fun θ' => φ z θ') = fun θ' => D 0 0 z θ' := funext fun θ' => hφ z θ'
        rw [hfs]
        exact hth 0 0 (by omega) z θ hz
      have hP1 := differentiableOn_uncurry_of_slices hU hsz0 hth0
        (hcont 1 0 (by omega)) (hcont 0 1 (by omega))
      have hfderiv : ContDiffOn ℝ k (fderivWithin ℝ (Function.uncurry φ) U) U :=
        (cop_pair_eq (n := (k : WithTop ℕ∞))
          (a := Function.uncurry (D 1 0)) (b := Function.uncurry (D 0 1)) hcontX hcontY).congr
          (fun p hp => hP1.2 hp)
      have hsucc := contDiffOn_succ_of_fderivWithin hP1.1 (fun hω => absurd hω (by simp)) hfderiv
      simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hsucc

theorem contDiffOn_four_of_partial_tower {φ : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hφ : ∀ z θ, φ z θ = D 0 0 z θ)
    (hcont : ∀ a b : ℕ, a + b ≤ 4 → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U)
    (hsz : ∀ a b : ℕ, a + b ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z)
    (hth : ∀ a b : ℕ, a + b ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ)
    : ContDiffOn ℝ 4 (Function.uncurry φ) U := by
  have h := main 4 φ D U hU hφ
    (fun a b hab => hcont a b hab)
    (fun a b hab => hsz a b (by omega))
    (fun a b hab => hth a b (by omega))
  simpa using h

end Work.FTS.StrongLWP.Sobolev
