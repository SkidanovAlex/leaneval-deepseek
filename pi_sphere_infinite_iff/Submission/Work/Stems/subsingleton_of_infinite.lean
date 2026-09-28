import Mathlib

/-!
# Homotopy groups indexed by an infinite type are trivial

Mathlib defines the `N`-th homotopy group `HomotopyGroup N X x` of a pointed space `(X, x)` as the
quotient of the *generalized loops* `Ω^ N X x`, i.e. of the continuous maps `I^N → X` that send the
boundary `∂I^N = ⋃_i {yᵢ = 0} ∪ {yᵢ = 1}` to `x`, by homotopy relative to the boundary.

For **finite** `N` this is the usual (generally nontrivial) `n`-th homotopy group.  The point of the
present lemma is that for **infinite** `N` the group collapses: the boundary of the infinite cube
`I^N` is *dense*, and this density can be exploited to contract every generalized loop.

Concretely, fix an embedding `e : ℕ ↪ N` of the natural numbers into the index type (which exists
because `N` is infinite; `Infinite.natEmbedding N`).  For `t : I` and `y : I^N` define the
"escape" map `CubeEscape.escape e t y` by scaling the coordinate at `e n` by the factor

  `max 0 (1 - t * (n + 1))`.

Then

* `escape e 0 y = y`,
* `escape e 1 y = 0` (the constant map at `0`),
* `escape e t y ∈ Cube.boundary N` for every `t ≠ 0` (for `t > 0` the factor at `e n` vanishes as
  soon as `n ≥ 1/t - 1`),
* `(t, y) ↦ escape e t y` is continuous (the product topology on `I^N` only constrains finitely
  many coordinates, and all of them tend to the identity as `t → 0`).

Given a generalized loop `f : Ω^ N X x`, the composite `(t, y) ↦ f (escape e t y)` is a continuous
map `I × I^N → X` which at `t = 0` equals `f`, at `t = 1` is constantly `x`, and is constantly `x`
on `I × ∂I^N` (on the boundary `f` takes the value `x` by definition, and for `t ≠ 0` the escape
map lands in the boundary).  Hence `f` is null-homotopic relative to the boundary, and all
generalized loops are homotopic: `HomotopyGroup N X x` is a subsingleton.

No separation hypothesis on `X` is needed: the homotopy is simply a composite of continuous maps.
The argument is the standard observation that the "pseudo-boundary" `∂I^N` of the infinite cube is
homotopy dense in `I^N`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

namespace CubeEscape

variable {N : Type*}

/-- The index of `i : N` as a natural number, read off along an embedding `e : ℕ ↪ N` (and an
arbitrary value off the range of `e`; only coordinates in the range of `e` are used). -/
noncomputable def idx (e : ℕ ↪ N) (i : N) : ℕ := Function.invFun (⇑e) i

/-- The (real valued) factor by which the coordinate `i` of the cube is scaled at time `t` of the
escape homotopy: `max 0 (1 - t * (n + 1))` where `n` is the index of `i` along `e`.  It equals `1`
at `t = 0`, vanishes at `t = 1`, and vanishes at `i = e n` as soon as `t * (n + 1) ≥ 1`. -/
noncomputable def cR (e : ℕ ↪ N) (t : I) (i : N) : ℝ :=
  max 0 (1 - (t : ℝ) * (((idx e i : ℕ) : ℝ) + 1))

lemma cR_nonneg (e : ℕ ↪ N) (t : I) (i : N) : 0 ≤ cR e t i := le_max_left _ _

lemma cR_le_one (e : ℕ ↪ N) (t : I) (i : N) : cR e t i ≤ 1 := by
  refine max_le zero_le_one ?_
  have h : 0 ≤ (t : ℝ) * (((idx e i : ℕ) : ℝ) + 1) := mul_nonneg t.2.1 (by positivity)
  linarith

/-- On the range of the embedding, `idx` is the inverse of `e`. -/
lemma idx_apply (e : ℕ ↪ N) (n : ℕ) : idx e (e n) = n :=
  Function.leftInverse_invFun e.injective n

lemma cR_zero (e : ℕ ↪ N) (i : N) : cR e 0 i = 1 := by simp [cR]

lemma cR_one (e : ℕ ↪ N) (i : N) : cR e 1 i = 0 := by
  have h : 1 - ((1 : I) : ℝ) * (((idx e i : ℕ) : ℝ) + 1) ≤ 0 := by
    simp only [Set.Icc.coe_one, one_mul]
    have : (0 : ℝ) ≤ (idx e i : ℕ) := by positivity
    linarith
  rw [cR, max_eq_left h]

/-- The escape map: scale the coordinate `e n` of the infinite cube by `max 0 (1 - t * (n + 1))`.
It deforms the identity (`t = 0`) into the constant map at zero (`t = 1`), and for every `t ≠ 0`
its image lies in the boundary of the cube. -/
noncomputable def escape (e : ℕ ↪ N) (t : I) (y : N → I) : N → I :=
  fun i => ⟨cR e t i * (y i : ℝ),
    unitInterval.mul_mem ⟨cR_nonneg e t i, cR_le_one e t i⟩ (y i).2⟩

lemma continuous_escape (e : ℕ ↪ N) : Continuous fun p : I × (N → I) => escape e p.1 p.2 := by
  refine continuous_pi fun i => ?_
  apply Continuous.subtype_mk
  show Continuous fun p : I × (N → I) => cR e p.1 i * ((p.2 i : I) : ℝ)
  refine Continuous.mul ?_ ?_
  · show Continuous fun p : I × (N → I) =>
      max 0 (1 - ((p.1 : I) : ℝ) * (((idx e i : ℕ) : ℝ) + 1))
    refine Continuous.max continuous_const ?_
    exact continuous_const.sub (((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  · exact continuous_subtype_val.comp (continuous_apply i |>.comp continuous_snd)

lemma escape_zero (e : ℕ ↪ N) (y : N → I) : escape e 0 y = y := by
  funext i
  apply Subtype.ext
  show cR e 0 i * (y i : ℝ) = (y i : ℝ)
  rw [cR_zero, one_mul]

lemma escape_one (e : ℕ ↪ N) (y : N → I) : escape e 1 y = 0 := by
  funext i
  apply Subtype.ext
  show cR e 1 i * (y i : ℝ) = (0 : ℝ)
  rw [cR_one, zero_mul]

/-- For every `t ≠ 0` the escape map lands in the boundary of the cube. -/
lemma escape_boundary (e : ℕ ↪ N) {t : I} (ht : t ≠ 0) (y : N → I) :
    escape e t y ∈ Cube.boundary N := by
  have htpos : (0 : ℝ) < (t : ℝ) :=
    lt_of_le_of_ne t.2.1 (Ne.symm (unitInterval.coe_ne_zero.2 ht))
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t : ℝ))
  have h1 : 1 ≤ (t : ℝ) * ((n : ℝ) + 1) := by
    have h2 : 1 < (t : ℝ) * (n : ℝ) := by
      have := mul_lt_mul_of_pos_left hn htpos
      rwa [mul_one_div, div_self (ne_of_gt htpos)] at this
    have h3 : (t : ℝ) * (n : ℝ) ≤ (t : ℝ) * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) htpos.le
    linarith
  refine ⟨e n, Or.inl ?_⟩
  have hc : cR e t (e n) = 0 := by
    rw [cR, idx_apply, max_eq_left]
    linarith
  apply Subtype.ext
  show cR e t (e n) * (y (e n) : ℝ) = (0 : ℝ)
  rw [hc, zero_mul]

end CubeEscape

/-- Every generalized loop indexed by an infinite type is null-homotopic relative to the boundary:
the escape homotopy pushes the cube into its boundary, where the loop is constant. -/
theorem homotopic_const {N X : Type*} [TopologicalSpace X] (e : ℕ ↪ N) (x : X)
    (f : GenLoop N X x) : GenLoop.Homotopic f (GenLoop.const : GenLoop N X x) := by
  have key : ∀ t : I, ∀ y : N → I, y ∈ Cube.boundary N →
      f (CubeEscape.escape e t y) = f y := by
    intro t y hy
    rcases eq_or_ne t 0 with h0 | ht
    · rw [h0, CubeEscape.escape_zero]
    · exact (f.2 _ (CubeEscape.escape_boundary e ht y)).trans (f.2 y hy).symm
  refine ⟨{ toFun := fun q => f (CubeEscape.escape e q.1 q.2),
            continuous_toFun := ?_,
            map_zero_left := ?_,
            map_one_left := ?_,
            prop' := ?_ }⟩
  · exact f.1.continuous.comp (CubeEscape.continuous_escape e)
  · intro y
    show f (CubeEscape.escape e 0 y) = f y
    rw [CubeEscape.escape_zero]
  · intro y
    show f (CubeEscape.escape e 1 y) = x
    rw [CubeEscape.escape_one]
    exact f.2 _ ⟨e 0, Or.inl rfl⟩
  · intro t y hy
    show f (CubeEscape.escape e t y) = f y
    exact key t y hy

/-- **The homotopy group of an infinite index type is trivial.**  For any topological space `X`,
base point `x : X` and infinite type `N`, the quotient of the generalized loops `Ω^ N X x` by
homotopy relative to the boundary is a subsingleton. -/
theorem subsingleton_of_infinite {N X : Type*} [TopologicalSpace X] [Infinite N] (x : X) :
    Subsingleton (HomotopyGroup N X x) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h f =>
    induction b using Quotient.inductionOn with
    | h g =>
      exact Quotient.sound (GenLoop.Homotopic.trans
        (homotopic_const (Infinite.natEmbedding N) x f)
        (GenLoop.Homotopic.symm (homotopic_const (Infinite.natEmbedding N) x g)))

end Work.Stems
