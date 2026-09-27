import Mathlib
import Submission.Work.Drive.TripleGeneral
import Submission.Work.Drive.mk2CLM

/-!
# The transversality of the *encoded chains* of the ends clause

`Work.Drive.HasClassLinearization` (`Submission/Work/Drive/classTripleOdd.lean`) asks, among other
things, for the `Meet3Hyp` data of the three chains

> `encodedChains (homotopyChain (H k)) (cls j) (cls l) c₀ : Fin 3 → ℝ³ → ℝP³ × ℝ`

(`Work.Drive.encodedChains`, `Submission/Work/Drive/meet32_bordism_invariance.lean`): **block `0`** is
the homotopy `W := homotopyChain (H k)` sitting in the level slice `{c₀}`, and **blocks `1`, `2`** are
the two class maps `cls j`, `cls l` of `ℝ² → ℝP³`, thickened by their level coordinate.

Its derivative at a parameter `x : ℝ³` therefore has, in the splitting `T(ℝP³ × ℝ) = TℝP³ ⊕ ℝ∂_λ`,

* block `0`: `(dW, 0)`,
* block `j`, `l`: `(d(cls) ∘ mk2CLM, coordCLM2)`,

i.e. exactly the block shape of `Work.Drive.encBlock0` / `Work.Drive.encBlock` below.  The point of this
file is that `TripleTransverse` for that shape is **equivalent to two checkable conditions**:

* `dW` is **onto** (`TℝP³` is `3`-dimensional and `dW` has a `3`-dimensional source, so this says the
  homotopy's time direction fills the transversal direction `∂_λ` is *not* in — the real genericity
  condition on the homotopy), and
* the two class `2`-planes satisfy `dX.range ⊔ dY.range = ⊤` (the general position of the two class
  derivatives — for the design's triple this is the `hV`-type condition of `ClassTripleRegular`).

Nothing else enters; in particular the statement does not involve the levels, the injectivity of the
class derivatives, or any `hup`-type hypothesis.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The block shape

The parameter of an encoded chain is a point of `ℝ³`; block `0` uses all three coordinates, blocks
`1`, `2` use the first two (`mk2CLM`) as the class parameter and the third (`coordCLM2`) as the level.
-/

/-- **The derivative of block `0`** of an encoded chain: the bordism direction, with the level
component constant (`c₀`). -/
def encBlock0 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) : EuclideanSpace ℝ (Fin 3) →L[ℝ] E × ℝ :=
  D.prod 0

@[simp] lemma encBlock0_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) (v : EuclideanSpace ℝ (Fin 3)) :
    encBlock0 D v = (D v, 0) := rfl

/-- **The derivative of block `1`/`2`** of an encoded chain: the class derivative composed with the
parameter projection `mk2CLM`, and the third coordinate as the level. -/
def encBlock {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) : EuclideanSpace ℝ (Fin 3) →L[ℝ] E × ℝ :=
  (X.comp mk2CLM).prod coordCLM2

@[simp] lemma encBlock_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) (v : EuclideanSpace ℝ (Fin 3)) :
    encBlock X v = (X (mk2 (v 0) (v 1)), v 2) := rfl

/-! ## 2. The reduction -/

/-- The vector of `ℝ³` with parameter `a` and third coordinate `t`. -/
def mk3 (a : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (![a 0, a 1, t] : Fin 3 → ℝ)

@[simp] lemma mk3_apply_zero (a : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3 a t 0 = a 0 := rfl
@[simp] lemma mk3_apply_one (a : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3 a t 1 = a 1 := rfl
@[simp] lemma mk3_apply_two (a : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk3 a t 2 = t := rfl

lemma mk2_mk3 (a : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : mk2 (mk3 a t 0) (mk3 a t 1) = a := by
  ext i
  fin_cases i <;> rfl

/-- **The class `2`-planes of the two blocks span**, from `dX.range ⊔ dY.range = ⊤`: every element of
`E` is a difference of two class derivatives. -/
lemma exists_sub_eq_of_sup_range_eq_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X Y : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) (h : X.range ⊔ Y.range = ⊤) (b : E) :
    ∃ p₁ p₂ : EuclideanSpace ℝ (Fin 2), X p₁ - Y p₂ = b := by
  have hb : b ∈ X.range ⊔ Y.range := by rw [h]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hb
  obtain ⟨p₁, rfl⟩ := hx
  obtain ⟨p₂, rfl⟩ := hy
  exact ⟨p₁, -p₂, by rw [map_neg, sub_neg_eq_add]; exact hxy⟩

/-- **The transversality of an encoded chain triple, in block form.**  If the bordism derivative `D`
is onto and the two class derivatives `X`, `Y` span, then the triple of blocks `(D,0)`, `(X,1)`,
`(Y,1)` is transverse — with no further hypothesis. -/
theorem tripleTransverseE_encoded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) (hD : Function.Surjective D)
    (X Y : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) (hXY : X.range ⊔ Y.range = ⊤) :
    TripleTransverseE (encBlock0 D) (encBlock X) (encBlock Y) := by
  intro w₁ w₂
  obtain ⟨a₁, α₁⟩ := w₁
  obtain ⟨a₂, α₂⟩ := w₂
  -- the two class parameters solving the two class equations
  obtain ⟨p₁, p₂, hp⟩ := exists_sub_eq_of_sup_range_eq_top X Y hXY (a₂ - a₁)
  -- the bordism parameter solving the first class equation
  obtain ⟨v₀, hv₀⟩ := hD (a₁ + X p₁)
  refine ⟨![v₀, mk3 p₁ (-α₁), mk3 p₂ (-α₂)], ?_, ?_⟩
  · -- the first difference
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, encBlock0_apply, encBlock_apply, mk2_mk3,
      mk3_apply_two, Prod.mk_sub_mk, hv₀]
    refine Prod.ext ?_ ?_
    · show a₁ + X p₁ - X p₁ = a₁
      abel
    · show (0 : ℝ) - -α₁ = α₁
      ring
  · -- the second difference
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_one, Matrix.head_cons, encBlock0_apply, encBlock_apply, mk2_mk3,
      mk3_apply_two, Prod.mk_sub_mk, hv₀]
    refine Prod.ext ?_ ?_
    · show a₁ + X p₁ - Y p₂ = a₂
      have h3 : a₁ + X p₁ - Y p₂ = a₁ + (X p₁ - Y p₂) := by abel
      rw [h3, hp]; abel
    · show (0 : ℝ) - -α₂ = α₂
      ring

/-! ## 3. The common-direction (face) condition for the encoded shape

The `face` field of `Meet3Hyp` uses `TripleCommonDir`: a tangent direction whose three images coincide.
For the encoded shape it is characterised below: the two *level* components of the common direction must
vanish (block `0` has zero level component), and the three class values must agree.  So the only
component of a common direction that can witness a *time* face of block `0` is its third coordinate
`v 0 2`; the slice faces of blocks `1`, `2` are witnessed by the class coordinates. -/

/-- **The common-direction condition in block form.** -/
theorem tripleCommonDirE_encoded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E) (X Y : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    TripleCommonDirE (encBlock0 D) (encBlock X) (encBlock Y) v ↔
      v 1 2 = 0 ∧ v 2 2 = 0 ∧
        D (v 0) = X (mk2 (v 1 0) (v 1 1)) ∧ D (v 0) = Y (mk2 (v 2 0) (v 2 1)) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    have h1a : D (v 0) = X (mk2 (v 1 0) (v 1 1)) := congrArg Prod.fst h1
    have h1b : (0 : ℝ) = v 1 2 := congrArg Prod.snd h1
    have h2a : D (v 0) = Y (mk2 (v 2 0) (v 2 1)) := congrArg Prod.fst h2
    have h2b : (0 : ℝ) = v 2 2 := congrArg Prod.snd h2
    exact ⟨h1b.symm, h2b.symm, h1a, h2a⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨Prod.ext h3 h1.symm, Prod.ext h4 h2.symm⟩

end

end Work.Drive
