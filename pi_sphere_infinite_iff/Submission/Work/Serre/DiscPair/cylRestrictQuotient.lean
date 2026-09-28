import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.DiscPair.cylCylinderPartOpen
import Submission.Work.Serre.DiscPair.cylPreimageDefs

set_option linter.unusedSectionVars false

namespace Work.Serre.DiscPair

open scoped Topology unitInterval

variable {P X : Type} [TopologicalSpace P] [TopologicalSpace X]

/-- The part of the presenting disjoint union of the mapping cylinder which is not the top circle:
the points `inl (p,t)` with `t ≠ 1`. -/
def cylInterior : Set ((P × unitInterval) ⊕ X) :=
  {a | ∃ p : P, ∃ t : unitInterval, (t : ℝ) < 1 ∧ a = Sum.inl (p, t)}

/-- The complement of the interior: the top circle together with the target copy. -/
def cylTop : Set ((P × unitInterval) ⊕ X) := Set.compl (cylInterior (P := P) (X := X))

lemma mem_cylInterior_iff {a : (P × unitInterval) ⊕ X} :
    a ∈ cylInterior (P := P) (X := X) ↔
      ∃ p : P, ∃ t : unitInterval, (t : ℝ) < 1 ∧ a = Sum.inl (p, t) := Iff.rfl

lemma sum_inl_mem_cylInterior {p : P} {t : unitInterval} (ht : (t : ℝ) < 1) :
    (Sum.inl (p, t) : (P × unitInterval) ⊕ X) ∈ cylInterior (P := P) (X := X) :=
  ⟨p, t, ht, rfl⟩

lemma sum_inr_not_mem_cylInterior (x : X) :
    (Sum.inr x : (P × unitInterval) ⊕ X) ∉ cylInterior (P := P) (X := X) := by
  rintro ⟨p, t, -, h⟩
  exact Sum.inr_ne_inl h

lemma isOpen_cylInterior : IsOpen (cylInterior (P := P) (X := X)) := by
  have hcont : Continuous
      (Sum.elim (fun z : P × unitInterval => (z.2 : ℝ)) (fun _ : X => (1 : ℝ))) :=
    Continuous.sumElim (continuous_subtype_val.comp continuous_snd) continuous_const
  have hset : cylInterior (P := P) (X := X)
      = {a | (Sum.elim (fun z : P × unitInterval => (z.2 : ℝ)) (fun _ : X => (1 : ℝ))) a < 1} := by
    ext a
    constructor
    · rintro ⟨p, t, ht, rfl⟩
      simpa using ht
    · intro ha
      rcases a with z | x
      · exact ⟨z.1, z.2, by simpa using ha, rfl⟩
      · simp at ha
  rw [hset]
  exact isOpen_Iio.preimage hcont

/-- A point of the top part is either a top-circle point `inl (p,1)` or a target point `inr x`. -/
lemma cylTop_cases {a : (P × unitInterval) ⊕ X} (ha : a ∈ cylTop (P := P) (X := X)) :
    (∃ p : P, a = Sum.inl (p, (1 : unitInterval))) ∨ (∃ x : X, a = Sum.inr x) := by
  rcases a with z | x
  · left
    obtain ⟨p, t⟩ := z
    refine ⟨p, ?_⟩
    have ht : t = 1 := by
      refine Subtype.ext (le_antisymm t.2.2 (not_lt.mp ?_))
      intro hlt
      exact ha ⟨p, t, hlt, rfl⟩
    rw [ht]
  · exact Or.inr ⟨x, rfl⟩

end Work.Serre.DiscPair

namespace Work.Serre.DiscPair

open scoped Topology unitInterval

variable {P X : Type} [TopologicalSpace P] [TopologicalSpace X]

lemma cylMk_inl_one' (f : C(P, X)) (p : P) :
    Work.Serre.cylMk f (Sum.inl (p, (1 : unitInterval))) = Work.Serre.cylInr f (f p) :=
  Work.Serre.cyl_mk_inl_one f p

/-- A point of `T = (cylRetract f) ⁻¹' S` whose preimage lies in the top part is a target point
`cylInr f x` with `x ∈ S`. -/
lemma exists_cylInr_of_mem_T_of_not_mem_cylInterior (f : C(P, X)) (S : Set X)
    {y : Work.Serre.cyl f} (hy : y ∈ (Work.Serre.cylRetract f) ⁻¹' S)
    {a : (P × unitInterval) ⊕ X} (ha : Work.Serre.cylMk f a = y)
    (hna : a ∉ cylInterior (P := P) (X := X)) :
    ∃ x : X, x ∈ S ∧ y = Work.Serre.cylInr f x := by
  have htop : a ∈ cylTop (P := P) (X := X) := hna
  rcases cylTop_cases (P := P) (X := X) htop with ⟨p, hp⟩ | ⟨x, hx⟩
  · refine ⟨f p, ?_, ?_⟩
    · have h2 : Work.Serre.cylRetract f
          (Work.Serre.cylMk f (Sum.inl (p, (1 : unitInterval)))) ∈ S := by
        rw [show Work.Serre.cylMk f (Sum.inl (p, (1 : unitInterval))) = y from by
          rw [← hp]; exact ha]
        exact Set.mem_preimage.mp hy
      simpa using h2
    · rw [← ha, hp]
      exact Work.Serre.cyl_mk_inl_one f p
  · refine ⟨x, ?_, ?_⟩
    · have h2 : Work.Serre.cylRetract f (Work.Serre.cylMk f (Sum.inr x)) ∈ S := by
        rw [show Work.Serre.cylMk f (Sum.inr x) = y from by rw [← hx]; exact ha]
        exact Set.mem_preimage.mp hy
      simpa using h2
    · rw [← ha, hx]
      rfl

end Work.Serre.DiscPair

/-!

# `cylRestrictQuotient` is FALSE as stated -- counterexample

The requested statement is, for arbitrary `S ⊆ X`,

  `IsQuotientMap (((cylRetract f) ⁻¹' S).restrictPreimage (cylMk f))`,

i.e. the map `g = q|_A : A → T`, where `q = cylMk f`, `T = (cylRetract f) ⁻¹' S` and
`A = q ⁻¹' T = f⁻¹S × I ⊔ S`, is a quotient map.  It is *false*: the mapping-cylinder structure
does not rescue the general (false) statement "the restriction of a quotient map to a saturated
set is a quotient map" (which classically requires the saturated set to be open or closed;
Mathlib has exactly the open case, `Topology.IsQuotientMap.restrictPreimage_isOpen`).

## Criterion used

`g` is a quotient map iff for every `V ⊆ T` with `W := q ⁻¹' V` open in `A`, `V` is open in `T`,
and (since `q` is a quotient map and `W = q ⁻¹' V` is saturated)

  `V` is open in `T`  ⟺  ∃ open *saturated* `Ω ⊆ (P × I) ⊔ X` with `Ω ∩ A = W`.

(⟸: `q Ω` is open and `T ∩ q Ω = q(Ω ∩ A) = q W = V`.  ⟹: `Ω := q ⁻¹' O` for `V = T ∩ O`.)
So it suffices to exhibit `W = q ⁻¹' V` open in `A` such that no such `Ω` exists.

## The counterexample

Take

* `P := ℝ × ℝ`, `X := ℝ`, `f := Prod.fst` (so `f (u,v) = u`; continuous);
* `S := ℚ ⊆ X`, `P₀ := (-1,1)`, so `S_V := S ∩ P₀ = ℚ ∩ (-1,1)` is open in `S` and `0 ∈ S_V`;
* `F := {(1/(n√2), n) : n ≥ 1} ⊆ P`, a closed discrete set (its points have no accumulation
  point, since the second coordinate tends to `∞`), with `F ∩ f⁻¹S_V = ∅` because the first
  coordinate `1/(n√2)` is irrational;
* `c := dist (·, F) : P → [0,∞)`, and

  `W₁ := {z : f⁻¹S_V × I | (z.2 : ℝ) > 1 - min (c z.1) (1/2)}`,

  `W := Sum.inl '' W₁ ∪ Sum.inr '' S_V`, and `V := cylMk f '' W`.

Note `f⁻¹S_V = (ℚ ∩ (-1,1)) × ℝ` and `f⁻¹S = ℚ × ℝ`, so `f⁻¹S_V` is open in `f⁻¹S` (as
`f⁻¹P₀` is open), `W₁` is open in `f⁻¹S_V × I` (it is the epigraph of the continuous function
`1 - min (c ·) (1/2)`), its top slice is all of `f⁻¹S_V × {1}` (since `c > 0` on `f⁻¹S_V`), and
`W` is open in `A` and saturated, because for `p ∈ P`

  `(p,1) ∈ W₁ ⟺ p ∈ f⁻¹S_V ⟺ f p ∈ S_V = S ∩ P₀`.

Hence `q ⁻¹' V = W`, so `V` is a legitimate subset of `T` with `q ⁻¹' V` open in `A`.

## `V` is not open in `T`

Suppose `Ω = O₁ ⊔ O₂` (`O₁ ⊆ P × I`, `O₂ ⊆ X` open, the summands of `Y = (P × I) ⊔ X`) is open,
saturated, with `Ω ∩ A = W`.  Then

* `O₂ ∩ S = S_V`, hence `S_V ⊆ O₂`, in particular `0 ∈ O₂`;
* `O₁ ∩ (f⁻¹S × I) = W₁`;
* (saturation) `O₁ ∩ (P × {1}) = f⁻¹O₂ × {1}`.

Since `O₂` is an open neighbourhood of `0` and `f (p_n) = 1/(n√2) → 0`, there is `n ≥ 1` with
`f (p_n) ∈ O₂`; then `inr (f (p_n)) ∈ Ω` and, by saturation, `(p_n, 1) ∈ Ω`, i.e. `(p_n,1) ∈ O₁`
(note `p_n ∈ f⁻¹O₂`).  So there are an open `Vₙ ∋ p_n` and `ε > 0` with
`Vₙ × (1-ε, 1] ⊆ O₁`; taking `Vₙ` small enough that it meets `f⁻¹S` only in `f⁻¹S_V` (possible,
since `p_n ∉ f⁻¹S` and `f⁻¹S \ f⁻¹S_V = (ℚ \ P₀) × ℝ` is closed away from `p_n`), the trace
condition `O₁ ∩ (f⁻¹S × I) = W₁` gives

  `∀ q ∈ Vₙ ∩ f⁻¹S_V,  c(q) ≥ ε`.

But `p_n ∈ closure (f⁻¹S_V)`: for any neighbourhood `U × J ∋ p_n` and any `ε' > 0` we may pick a
rational `r ∈ P₀` with `|r - 1/(n√2)| < min(ε', ...)`, and then `q := (r, n) ∈ f⁻¹S_V` lies in
`U × J` and has `c(q) ≤ |r - 1/(n√2)| < ε'` (because `p_n ∈ F`).  So the infimum of `c` over
`Vₙ ∩ f⁻¹S_V` is `0`, contradiction.

Hence no such `Ω` exists, `V` is not open in `T`, and `((cylRetract f) ⁻¹' S).restrictPreimage
(cylMk f)` is **not** a quotient map.

## A cleaner way to say the same thing

The mechanism is: a point `p ∈ closure (f⁻¹S_V) \ f⁻¹S_V` whose fibre partner `(p,1)` is
*forced* into every admissible `O₁` (because `f p ∈ O₂` is forced, `O₂ ⊇ S_V` and `f p → y ∈ S_V`)
while the height function of `W₁` degenerates at `p`, so the slab that `O₁` needs around `(p,1)`
cannot fit into `W₁`.  The "spread" needed for a bad point that is *not* itself in `f⁻¹S_V` is
supplied here by the second coordinate of `P = ℝ × ℝ` (with `f = Prod.fst`), which lets the
points `p_n` have irrational `f`-values approaching `0 ∈ S_V` while `f⁻¹S_V` still accumulates at
them.  With `P = X = ℝ` and `f = id` no counterexample exists (then `f (p_n) → y ∈ S_V` forces a
limit point of the `p_n` inside `f⁻¹S_V`), which is why several natural attempts fail.

## The correct statement

If `S` is open in `X` then `T = (cylRetract f) ⁻¹' S` is open in `cyl f` and
`Topology.IsQuotientMap.restrictPreimage_isOpen` applies; if `S` is closed then so is `T` and the
classical closed version of the same theorem applies.  It is *not* enough that the classes of the
gluing relation be finite, nor that `W` be saturated.

-/
