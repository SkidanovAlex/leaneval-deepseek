/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The local `∂̄`-splitting of a real analytic function in a fibre variable

The main theorem of this file, `Work.NN.Core.TelTwoDF.exists_analytic_holomorphic_dbar_split`,
is the local analytic input of the `(0,2)`-telescoping: for a real analytic function `D` on an
open set `V ⊆ ℂⁿ` and a point `x ∈ V`, there are a neighbourhood `U` of `(x, x s)` in `ℂⁿ × ℂ`
and real analytic functions `H, A` on `U`, with `H` holomorphic in the second variable, such that

  `D (Function.update p.1 s p.2) = H p + ∂̄ (A (p.1, ·)) p.2`   for all `p ∈ U`.

In fact much more is true: one can take `H = 0`, i.e. the fibre function `E q = D (update q.1 s q.2)`
has a *real analytic* fibre-wise `∂̄`-primitive.  This is the content of the reduction
`exists_analytic_holomorphic_dbar_split_of_crux` below, and the input is the local
`∂̄`-Poincaré lemma `exists_analytic_fibre_dbar_primitive` (delegated, stated in terms of the
general statement about real analytic functions on `ℂⁿ × ℂ`).

The route to the `∂̄`-Poincaré lemma used here: complexify the fibre variable.  If `E` is real
analytic near `q₀ = (p₀, w₀)`, then (after centring at `q₀`) the power series of `E` at `q₀`
can be decomposed, slot by slot, along the `ℝ`-basis `(1, i)` of `ℂ`, and the resulting
*complexified* series `Φ(p, z, ζ)` (same coefficients, with `\bar z` promoted to an independent
variable `ζ`) is holomorphic in `z`, real analytic in `(p, z, ζ)` and satisfies
`Φ(p, z, \bar z) = E(p, z)`.  Then `A(p, z) := \bar z ∫₀¹ Φ(p, z, t \bar z) dt` is real analytic
and `∂̄_z A = Φ(p, z, \bar z) = E`: indeed
`∂̄_z A = ∫₀¹ Φ(p,z,t\bar z)dt + \bar z ∫₀¹ t (∂_ζΦ)(p,z,t\bar z)dt`
and, since `t ↦ Φ(p,z,t\bar z)` is `C¹`, the second integral is
`Φ(p,z,\bar z) - ∫₀¹Φ(p,z,t\bar z)dt` by integration by parts.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.analyticOn_real_of_differentiableAt_complex
import Submission.Work.NN.Core.TelTwoDF.exists_analytic_fibre_dbar_primitive

namespace Work.NN.Core.TelTwoDF

open Set Metric

variable {n : ℕ}

/-- `(p, w) ↦ Function.update p s w`, as a continuous linear map. -/
noncomputable def insL (s : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    if i = s then ContinuousLinearMap.snd ℝ (Fin n → ℂ) ℂ
    else (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℂ) ℂ)

@[simp] lemma insL_apply (s : Fin n) (p : Fin n → ℂ) (w : ℂ) :
    insL s (p, w) = Function.update p s w := by
  ext i
  simp only [insL, ContinuousLinearMap.pi_apply, Function.update_apply]
  by_cases h : i = s
  · subst h; simp
  · simp [h]

/-- The map `q = (p, w) ↦ Function.update p s (c + w)`. -/
noncomputable def insMap (s : Fin n) (c : ℂ) : ((Fin n → ℂ) × ℂ) → (Fin n → ℂ) :=
  fun q => insL s q + Function.update (0 : Fin n → ℂ) s c

@[simp] lemma insMap_apply (s : Fin n) (c : ℂ) (q : (Fin n → ℂ) × ℂ) :
    insMap s c q = Function.update q.1 s (c + q.2) := by
  obtain ⟨p, w⟩ := q
  simp only [insMap, insL_apply]
  ext i
  by_cases h : i = s
  · subst h; simp [add_comm]
  · simp [h]

lemma continuous_insMap (s : Fin n) (c : ℂ) : Continuous (insMap (n := n) s c) :=
  ((insL s).continuous.add continuous_const)

lemma analyticAt_insMap (s : Fin n) (c : ℂ) (q : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℝ (insMap (n := n) s c) q :=
  (ContinuousLinearMap.analyticAt (insL s) q).add analyticAt_const

/-- The fibre function `q ↦ D (Function.update q.1 s (c + q.2))`. -/
noncomputable def fibreFun (D : (Fin n → ℂ) → ℂ) (s : Fin n) (c : ℂ) :
    ((Fin n → ℂ) × ℂ) → ℂ :=
  D ∘ insMap s c

@[simp] lemma fibreFun_apply (D : (Fin n → ℂ) → ℂ) (s : Fin n) (c : ℂ)
    (q : (Fin n → ℂ) × ℂ) :
    fibreFun D s c q = D (Function.update q.1 s (c + q.2)) := by
  simp only [fibreFun, Function.comp_apply, insMap_apply]

lemma analyticOn_fibreFun {V : Set (Fin n → ℂ)} {D : (Fin n → ℂ) → ℂ}
    (hD : AnalyticOn ℝ D V) (s : Fin n) (c : ℂ) :
    AnalyticOn ℝ (fibreFun D s c) (insMap s c ⁻¹' V) := by
  rw [fibreFun]
  refine AnalyticOn.comp hD (fun q _ => ?_) (fun q hq => hq)
  exact (analyticAt_insMap s c q).analyticWithinAt

/-- **Reduction of the main theorem to the local `∂̄`-Poincaré lemma.**

If every real analytic function on an open subset of `ℂⁿ × ℂ` has, near each of its points, a
real analytic fibre-wise `∂̄`-primitive, then the local splitting
`D (update p.1 s p.2) = H p + ∂̄ (A (p.1, ·)) p.2` holds, with `H = 0`. -/
theorem exists_analytic_holomorphic_dbar_split_of_crux {n : ℕ}
    (crux : ∀ {Ω : Set ((Fin n → ℂ) × ℂ)}, IsOpen Ω → ∀ {F : ((Fin n → ℂ) × ℂ) → ℂ},
      AnalyticOn ℝ F Ω → ∀ q ∈ Ω, ∃ U : Set ((Fin n → ℂ) × ℂ), IsOpen U ∧ q ∈ U ∧ U ⊆ Ω ∧
        ∃ A : ((Fin n → ℂ) × ℂ) → ℂ, AnalyticOn ℝ A U ∧
          ∀ r ∈ U, F r = Work.CR.Flat.dbarC (fun w : ℂ => A (r.1, w)) r.2)
    {V : Set (Fin n → ℂ)} (hV : IsOpen V) {D : (Fin n → ℂ) → ℂ} (hD : AnalyticOn ℝ D V)
    {x : Fin n → ℂ} (hx : x ∈ V) (s : Fin n) :
    ∃ U : Set ((Fin n → ℂ) × ℂ), IsOpen U ∧ (x, x s) ∈ U ∧
      (∀ p ∈ U, Function.update p.1 s p.2 ∈ V) ∧
      ∃ H A : (Fin n → ℂ) × ℂ → ℂ,
        AnalyticOn ℝ H U ∧ AnalyticOn ℝ A U ∧
        (∀ p ∈ U, DifferentiableAt ℂ (fun w : ℂ => H (p.1, w)) p.2) ∧
        (∀ p ∈ U, D (Function.update p.1 s p.2)
            = H p + Work.CR.Flat.dbarC (fun w : ℂ => A (p.1, w)) p.2) := by
  obtain ⟨U, hUo, hqU, hUV, A, hAan, hAeq⟩ :=
    crux (hV.preimage (continuous_insMap s 0)) (analyticOn_fibreFun (V := V) hD s 0)
      (q := (x, x s)) (by
        simp only [mem_preimage, insMap_apply, zero_add]
        rw [Function.update_eq_self]
        exact hx)
  refine ⟨U, hUo, hqU, ?_, 0, A, analyticOn_const, hAan, ?_, ?_⟩
  · intro p hp
    have h := hUV hp
    simpa only [mem_preimage, insMap_apply, zero_add] using h
  · intro p _; exact differentiableAt_const _
  · intro p hp
    have h := hAeq p hp
    simp only [fibreFun_apply, zero_add] at h
    rw [h]
    simp

theorem exists_analytic_holomorphic_dbar_split {n : ℕ} {V : Set (Fin n → ℂ)} (hV : IsOpen V)
    {D : (Fin n → ℂ) → ℂ} (hD : AnalyticOn ℝ D V) {x : Fin n → ℂ} (hx : x ∈ V) (s : Fin n) :
    ∃ U : Set ((Fin n → ℂ) × ℂ), IsOpen U ∧ (x, x s) ∈ U ∧
      (∀ p ∈ U, Function.update p.1 s p.2 ∈ V) ∧
      ∃ H A : (Fin n → ℂ) × ℂ → ℂ,
        AnalyticOn ℝ H U ∧ AnalyticOn ℝ A U ∧
        (∀ p ∈ U, DifferentiableAt ℂ (fun w : ℂ => H (p.1, w)) p.2) ∧
        (∀ p ∈ U, D (Function.update p.1 s p.2)
            = H p + Work.CR.Flat.dbarC (fun w : ℂ => A (p.1, w)) p.2) :=
  exists_analytic_holomorphic_dbar_split_of_crux
    (fun {Ω} hΩ {F} hF q hq => exists_analytic_fibre_dbar_primitive hΩ hF hq) hV hD hx s

end Work.NN.Core.TelTwoDF
