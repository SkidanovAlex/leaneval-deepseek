import Mathlib

/-!
# Whitney's local model: an immersion of `ℝⁿ` in `ℝ^{2n}` with a single double point

This file defines the explicit local model behind Whitney's construction ("To introduce a local
double point, Whitney created immersions `α_m : ℝ^m → ℝ^{2m}` which are approximately linear outside
of the unit ball, but containing a single double point", Whitney 1944; see also
<https://en.wikipedia.org/wiki/Whitney_embedding_theorem>).

With `u x = ∏ᵢ (1 + xᵢ²)` the model is

  `model n x = (fun i ↦ if i = 0 then x i - 2 * x i / u x else x i,
                fun i ↦ if i = 0 then 1 / u x else x 0 * x i / u x)`,

a map `(Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)`.  Its only double point is
`model n (e0 n) = model n (-(e0 n)) = (0, (1/2) • e0 n)`, and it is *approximately* the linear
inclusion `inclModel n x = (x, 0)` for large `‖x‖` (the correction terms are `O (1 / ‖x‖)`).

The model is the basic building block of the "introduce a double point" move
(`Work.Whitney.addDoublePoint`): glued into a chart of an immersion `f : Mⁿ → ℝ^{2n}` with the help
of a *linearisation* of the chart representation (`Work.Whitney.exists_linearization`) it adds
exactly one transverse double point of a controllable sign, which is what lets one choose the
self-intersection number of an immersion freely and hence finish Whitney's strong embedding
theorem by cancelling pairs of opposite sign.
-/

namespace Work.Whitney

open scoped BigOperators

/-- `u x = ∏ᵢ (1 + xᵢ²)`, the denominator of Whitney's local model.  It satisfies `u x ≥ 1`. -/
def uu (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, (1 + x i ^ 2)

/-- The vector `e₀ = (1, 0, …, 0)`. -/
def e0 (n : ℕ) [NeZero n] : Fin n → ℝ := Pi.single 0 1

/-- Whitney's local model `α_n`, written as a map into a product of two copies of `ℝⁿ` (the two
blocks of coordinates of `ℝ^{2n}`). -/
noncomputable def model (n : ℕ) [NeZero n] (x : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => x i - (if i = 0 then 2 * x i / uu n x else 0),
   fun i => if i = 0 then 1 / uu n x else x 0 * x i / uu n x)

/-- The linear inclusion `x ↦ (x, 0)`, the "linear part" of Whitney's local model. -/
def inclModel (n : ℕ) (x : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) := (x, 0)

@[simp] theorem inclModel_fst (n : ℕ) (x : Fin n → ℝ) : (inclModel n x).1 = x := rfl
@[simp] theorem inclModel_snd (n : ℕ) (x : Fin n → ℝ) : (inclModel n x).2 = 0 := rfl

/-- The two coordinates of the model, unfolded. -/
theorem model_fst (n : ℕ) [NeZero n] (x : Fin n → ℝ) (i : Fin n) :
    (model n x).1 i = x i - (if i = 0 then 2 * x i / uu n x else 0) := rfl

theorem model_snd (n : ℕ) [NeZero n] (x : Fin n → ℝ) (i : Fin n) :
    (model n x).2 i = if i = 0 then 1 / uu n x else x 0 * x i / uu n x := rfl

/-- The mirror of a point of `ℝⁿ × ℝⁿ`: negation of the *first* coordinate of the **second** block.
Reason to care: `mirrorFun n` is linear, it *fixes* the linear inclusion `inclModel`
(`mirrorFun n (x, 0) = (x, 0)`), it has determinant `-1`, and hence `mirrorFun n ∘ model n` has a
double point at the same pair `±e₀` as `model n` but of the *opposite* sign; this is what allows one
to move the self-intersection number of an immersion in either direction while keeping the model
glueable. -/
def mirrorFun (n : ℕ) [NeZero n] (y : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (y.1, fun i => if i = 0 then - y.2 i else y.2 i)

@[simp] theorem mirrorFun_fst (n : ℕ) [NeZero n] (y : (Fin n → ℝ) × (Fin n → ℝ)) :
    (mirrorFun n y).1 = y.1 := rfl

@[simp] theorem mirrorFun_snd (n : ℕ) [NeZero n] (y : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    (mirrorFun n y).2 i = if i = 0 then - y.2 i else y.2 i := rfl

/-- The mirror fixes the linear inclusion. -/
@[simp] theorem mirrorFun_inclModel (n : ℕ) [NeZero n] (x : Fin n → ℝ) :
    mirrorFun n (inclModel n x) = inclModel n x := by
  refine Prod.ext rfl ?_
  funext i
  simp [mirrorFun, inclModel]

end Work.Whitney
