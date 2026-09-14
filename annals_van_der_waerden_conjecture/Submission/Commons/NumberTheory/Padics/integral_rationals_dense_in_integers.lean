import Mathlib.Algebra.Algebra.Field
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.RingTheory.DedekindDomain.AdicValuation

open IsDedekindDomain
open scoped WithZero

noncomputable section

namespace Commons.NumberTheory.Padics

/-! # Integral rationals are dense in the integers of the completion

For a height-one prime `v` of `ℤ` (a rational prime), the ring of integers of the
`v`-adic completion of `ℚ` (i.e. `ℤ_p` in classical notation) is the closure, inside
the completion, of the set of rationals with `v`-adic valuation at most `1`
(the rationals integral at `v`).

We prove this by (1) observing that on the value group `ℤᵐ⁰` the condition `x ≤ 1`
is equivalent to `x < exp 1` (there is no value strictly between `1` and `exp 1`),
(2) applying the Mathlib result `Valued.closure_coe_completion_v_lt` that identifies
the closure of the image of `{x | v x < γ}` in the completion, with `γ = exp 1`, and
(3) transferring the resulting set equality from the underlying uniform completion to
the (uniformly isomorphic) `adicCompletion` wrapper. -/

open Filter Topology WithZero UniformSpace

/-- On the value group `ℤᵐ⁰`, being `≤ 1` is equivalent to being `< exp 1`. -/
lemma val_le_one_iff_lt_exp_one (z : ℤᵐ⁰) : z ≤ (1 : ℤᵐ⁰) ↔ z < WithZero.exp (1 : ℤ) := by
  constructor
  · intro hz
    by_cases hz0 : z = 0
    · rw [hz0]
      exact WithZero.zero_lt_coe _
    · have hlogz : WithZero.exp (WithZero.log z) = z := WithZero.exp_log hz0
      have hle0 : WithZero.log z ≤ (0 : ℤ) := by
        have : WithZero.exp (WithZero.log z) ≤ WithZero.exp (0 : ℤ) := by
          simpa [hlogz] using hz
        exact WithZero.exp_le_exp.mp this
      have hlt1 : WithZero.log z < (1 : ℤ) := by omega
      rw [← hlogz]
      exact WithZero.exp_lt_exp.mpr hlt1
  · intro hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hlogz : WithZero.exp (WithZero.log z) = z := WithZero.exp_log hz0
      have hlt1 : WithZero.log z < (1 : ℤ) := by
        have : WithZero.exp (WithZero.log z) < WithZero.exp (1 : ℤ) := by
          simpa [hlogz] using hz
        exact WithZero.exp_lt_exp.mp this
      have hle0 : WithZero.log z ≤ (0 : ℤ) := by omega
      rw [← hlogz]
      exact WithZero.exp_le_exp.mpr hle0

section Main

variable (v : IsDedekindDomain.HeightOneSpectrum ℤ)

/-- The uniform completion of `ℚ` with respect to the `v`-adic valuation (the type
underlying `v.adicCompletion ℚ`). -/
abbrev Wv := (v.valuation ℚ).Completion

/-- The `v`-adic completion of `ℚ`. -/
abbrev Av := v.adicCompletion ℚ

/-- `exp 1` as a unit of the value group equals `exp 1` as an element. -/
lemma gamma_val_eq_exp_one :
    ((WithZero.expEquiv (1 : ℤ) : (ℤᵐ⁰)ˣ) : ℤᵐ⁰) = WithZero.exp (1 : ℤ) := by
  exact WithZero.coe_expEquiv_apply (1 : ℤ)

/-- Embedding a rational into the completion is the composite of the embedding into
`WithVal (v.valuation ℚ)` with the completion map. -/
lemma coe_rat_eq_coe'_toVal (q : ℚ) :
    (q : Wv v) = UniformSpace.Completion.coe' (WithVal.toVal (v.valuation ℚ) q) := by
  rw [(algebraMap.coe_ratCast ℚ (Wv v) q).symm]
  change UniformSpace.Completion.coeRingHom (algebraMap ℚ (WithVal (v.valuation ℚ)) q) =
    UniformSpace.Completion.coe' (WithVal.toVal (v.valuation ℚ) q)
  rfl

/-- The image under `toVal` of the rationals of valuation `< γ` is exactly the
elements of `WithVal (v.valuation ℚ)` of valuation `< γ`. -/
lemma withVal_lt_image (γ : ℤᵐ⁰) :
    {u : WithVal (v.valuation ℚ) | Valued.v u < γ} =
      WithVal.toVal (v.valuation ℚ) '' {q : ℚ | v.valuation ℚ q < γ} := by
  ext u
  constructor
  · intro hu
    refine ⟨u.ofVal, ?_, ?_⟩
    · simpa [WithVal.apply_ofVal] using hu
    · exact WithVal.toVal_ofVal (v := v.valuation ℚ) u
  · rintro ⟨q, hq, rfl⟩
    simpa [WithVal.valued_toVal] using hq

/-- The ring of integers of the completion (in the underlying completion type) is the
closure of the image of the rationals integral at `v`. -/
lemma closure_integers_in_completion :
    closure ((fun q : ℚ => (q : Wv v)) '' {q : ℚ | v.valuation ℚ q ≤ (1 : ℤᵐ⁰)}) =
      {x : Wv v | Valued.v x ≤ (1 : ℤᵐ⁰)} := by
  let γ : (ℤᵐ⁰)ˣ := WithZero.expEquiv (1 : ℤ)
  have hγ : (γ : ℤᵐ⁰) = WithZero.exp (1 : ℤ) := gamma_val_eq_exp_one
  have hle : ∀ q : ℚ, v.valuation ℚ q ≤ (1 : ℤᵐ⁰) ↔ v.valuation ℚ q < (γ : ℤᵐ⁰) := by
    intro q
    rw [hγ]
    exact val_le_one_iff_lt_exp_one (v.valuation ℚ q)
  have hcl := Valued.closure_coe_completion_v_lt (K := WithVal (v.valuation ℚ)) (Γ₀ := ℤᵐ⁰)
    (γ := γ)
  have hqset : {q : ℚ | v.valuation ℚ q ≤ (1 : ℤᵐ⁰)} =
      {q : ℚ | v.valuation ℚ q < (γ : ℤᵐ⁰)} := by
    ext q
    exact hle q
  have hu : {u : WithVal (v.valuation ℚ) | Valued.v u < (γ : ℤᵐ⁰)} =
      WithVal.toVal (v.valuation ℚ) '' {q : ℚ | v.valuation ℚ q < (γ : ℤᵐ⁰)} :=
    withVal_lt_image v (γ : ℤᵐ⁰)
  calc
    closure ((fun q : ℚ => (q : Wv v)) '' {q : ℚ | v.valuation ℚ q ≤ (1 : ℤᵐ⁰)})
        = closure ((fun q : ℚ => (q : Wv v)) '' {q : ℚ | v.valuation ℚ q < (γ : ℤᵐ⁰)}) := by
          rw [hqset]
    _ = closure ((UniformSpace.Completion.coe' ∘ WithVal.toVal (v.valuation ℚ)) ''
          {q : ℚ | v.valuation ℚ q < (γ : ℤᵐ⁰)}) := by
          rw [show (fun q : ℚ => (q : Wv v)) =
              UniformSpace.Completion.coe' ∘ WithVal.toVal (v.valuation ℚ) from
            by
              funext q
              exact coe_rat_eq_coe'_toVal v q]
    _ = closure (UniformSpace.Completion.coe' ''
          (WithVal.toVal (v.valuation ℚ) '' {q : ℚ | v.valuation ℚ q < (γ : ℤᵐ⁰)})) := by
          rw [Set.image_comp]
    _ = closure (UniformSpace.Completion.coe' '' {u : WithVal (v.valuation ℚ) |
          Valued.v u < (γ : ℤᵐ⁰)}) := by
          rw [hu]
    _ = {x : Wv v | Valued.v x ≤ (1 : ℤᵐ⁰)} := by
          rw [hcl]
          ext x
          constructor
          · intro hx
            exact (val_le_one_iff_lt_exp_one (Valued.extensionValuation x)).2
              (by simpa [hγ] using hx)
          · intro hx
            rw [hγ]
            exact (val_le_one_iff_lt_exp_one (Valued.extensionValuation x)).1 hx

/-- The uniform equivalence `toCompletion` sends the image of a rational in
`adicCompletion` to its image in the underlying completion. -/
lemma uniformEquiv_coe_rat (q : ℚ) :
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv ℚ v)
      (q : Av v) = (q : Wv v) := by
  rw [(algebraMap.coe_ratCast ℚ (Av v) q).symm]
  rw [(algebraMap.coe_ratCast ℚ (Wv v) q).symm]
  change IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion
      (algebraMap ℚ (Wv v) q)) = algebraMap ℚ (Wv v) q
  rfl

/-- Membership transfer along a homeomorphism: `x` lies in the closure of `s` iff its
image lies in the closure of the image of `s`. -/
lemma mem_closure_homeomorph_image_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {s : Set X} {x : X} :
    x ∈ closure s ↔ e x ∈ closure (e '' s) := by
  constructor
  · intro hx
    rw [← Homeomorph.image_closure e s]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← Homeomorph.image_closure e s] at hx
    rcases hx with ⟨y, hy, hyx⟩
    have : y = x := e.injective hyx
    simpa [this] using hy

/-- Every element of the ring of integers of the `adicCompletion` has completion
valuation at most `1`. -/
lemma adicCompletionIntegers_val_le_one (x : v.adicCompletionIntegers ℚ) :
    Valued.v (x : Av v) ≤ (1 : ℤᵐ⁰) := x.2

end Main

/-- The ring of integers of the completion is the closure of the image of the
integral rationals. -/
theorem integral_rationals_dense_in_integers (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x : v.adicCompletionIntegers ℚ) :
    (x : v.adicCompletion ℚ) ∈ closure
      {y : v.adicCompletion ℚ | ∃ q : ℚ, v.valuation ℚ q ≤ 1 ∧ (q : v.adicCompletion ℚ) = y} := by
  let X : Set ℚ := {q : ℚ | v.valuation ℚ q ≤ (1 : ℤᵐ⁰)}
  let S : Set (v.adicCompletion ℚ) :=
    {y : v.adicCompletion ℚ | ∃ q : ℚ, v.valuation ℚ q ≤ 1 ∧ (q : v.adicCompletion ℚ) = y}
  let e : v.adicCompletion ℚ ≃ᵤ (v.valuation ℚ).Completion :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv ℚ v
  have hS : S = (fun q : ℚ => (q : v.adicCompletion ℚ)) '' X := by
    rfl
  have hfun : e ∘ (fun q : ℚ => (q : v.adicCompletion ℚ)) =
      fun q : ℚ => (q : (v.valuation ℚ).Completion) := by
    funext q
    exact uniformEquiv_coe_rat v q
  have heimg : e.toHomeomorph '' S =
      (fun q : ℚ => (q : (v.valuation ℚ).Completion)) '' X := by
    rw [hS]
    rw [← Set.image_comp]
    change (⇑e ∘ fun q : ℚ => (q : v.adicCompletion ℚ)) '' X =
      (fun q : ℚ => (q : (v.valuation ℚ).Completion)) '' X
    rw [hfun]
  have hxint : Valued.v (e (x : v.adicCompletion ℚ)) ≤ (1 : ℤᵐ⁰) := by
    change Valued.v (x : v.adicCompletion ℚ).toCompletion ≤ (1 : ℤᵐ⁰)
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_toCompletion
      (R := ℤ) (K := ℚ) (v := v)]
    exact adicCompletionIntegers_val_le_one v x
  have hmem : e (x : v.adicCompletion ℚ) ∈ closure (e.toHomeomorph '' S) := by
    rw [heimg]
    rw [closure_integers_in_completion v]
    exact hxint
  exact (mem_closure_homeomorph_image_iff (e.toHomeomorph) (s := S)).2 hmem

end Commons.NumberTheory.Padics