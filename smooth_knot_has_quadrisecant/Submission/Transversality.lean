import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.CollinearityMap
import Submission.Commons.Analysis.CrossProduct.inner_cross3_self_left
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
import Submission.Commons.Analysis.LinearAlgebra.linearIndependent_pair_smul

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer A (vii) — the rank / regular-value criterion for the collinearity map

The transversality engine of the structure theory of `O`: on a zero of the
collinearity map `Φ(a,b,m) = (r a − r b) × (r a − r m)` (a strict-trisecant
triple of the smooth knot `r`), the *directional derivative* — assembled in
`CollinearityMap.lean` as
`(da,db,dm) ↦ da • ∂_a + db • ∂_b + dm • ∂_m` with the three hinge partials

    ∂_a = v(a) × (r a − r m) + (r a − r b) × v(a)
    ∂_b = (r a − r m) × v(b)
    ∂_m = v(m) × (r a − r b)

— has range equal to the span of the partials, which lies in the plane
perpendicular to the chord when the chord vectors are parallel (the
collinearity `Φ = 0`).  The **rank-two criterion**: the derivative has rank
2 — the hypothesis making `Φ⁻¹(0)` a smooth curve through the triple — iff
the partials contain two linearly independent members
(`PartialRankTwo`), which under the parallelism of the two chord vectors is
equivalent to the velocities being in general position relative to the chord
direction.

This module provides the provable core and records the exact geometric
hypotheses (the fleet lemmas `cross3_eq_zero_iff_smul` — still in flight —
and `inner_cross3_self_left` — committed) that complete the equivalence:

* the **easy (degenerate) direction**: if the three partials all lie on one
  line through the origin (`collPartialOnLine`), then no two of them are
  linearly independent, so `¬ PartialRankTwo`
  (`not_PartialRankTwo_of_collPartialOnLine`): the derivative cannot have
  rank two;
* **orthogonality of the partials to the chord**: the cross product is
  perpendicular to both factors (`inner_cross3_self_left`, with the right
  version derived), so `∂_b ⟂ (r a − r m)` unconditionally, and `∂_a`,
  `∂_m` are perpendicular to `r a − r m` once the chord vectors are parallel
  (`inner_partialA_chord_of_parallel`, `inner_partialM_chord_of_parallel`,
  combined in `partials_orthogonal_chord_of_parallel`).

The converse direction of the criterion — from two independent partials
(equivalently, two velocities transverse to the chord and not coplanar with
it) to the smooth-curve structure of `Φ⁻¹(0)` — is the next assembly step,
using the parallel/orthogonality facts above.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The first hinge partial: `∂_a = v(a) × (r a − r m) + (r a − r b) × v(a)`. -/
def collPartialA (r : ℝ → Space) (a b m : ℝ) : Space :=
  cross3 (velocity r a) (r a - r m) + cross3 (r a - r b) (velocity r a)

/-- The middle hinge partial: `∂_b = (r a − r m) × v(b)`. -/
def collPartialB (r : ℝ → Space) (a b m : ℝ) : Space :=
  cross3 (r a - r m) (velocity r b)

/-- The third hinge partial: `∂_m = v(m) × (r a − r b)`. -/
def collPartialM (r : ℝ → Space) (a b m : ℝ) : Space :=
  cross3 (velocity r m) (r a - r b)

/-- The three hinge partials, indexed by `Fin 3`
(`0 ↦ ∂_a`, `1 ↦ ∂_b`, `2 ↦ ∂_m`). -/
def collPartial (r : ℝ → Space) (a b m : ℝ) : Fin 3 → Space
  | ⟨0, _⟩ => collPartialA r a b m
  | ⟨1, _⟩ => collPartialB r a b m
  | _ => collPartialM r a b m

/-- The span of the three partials — the range of the directional derivative
map of the collinearity map at `(a,b,m)`. -/
def collPartialSpan (r : ℝ → Space) (a b m : ℝ) : Submodule ℝ Space :=
  Submodule.span ℝ ({collPartialA r a b m, collPartialB r a b m,
    collPartialM r a b m} : Set Space)

/-- **Rank-two criterion (operative form)**: the directional derivative of
the collinearity map at `(a,b,m)` has rank at least two — equivalently its
range (the span of the partials) contains a two-dimensional subspace — iff
two of the three hinge partials are linearly independent.  On a zero of
`Φ` this is the condition making the trisecant locus a smooth curve through
the triple (regular-value hypothesis of the structure theory). -/
def PartialRankTwo (r : ℝ → Space) (a b m : ℝ) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ LinearIndependent ℝ ![collPartial r a b m i, collPartial r a b m j]

/-- The three partials all lie on one line through the origin (equivalently,
the derivative range is contained in a line): there is a single vector `v`
spanned by each partial. -/
def collPartialOnLine (r : ℝ → Space) (a b m : ℝ) : Prop :=
  ∃ v : Space,
    collPartialA r a b m ∈ Submodule.span ℝ ({v} : Set Space) ∧
    collPartialB r a b m ∈ Submodule.span ℝ ({v} : Set Space) ∧
    collPartialM r a b m ∈ Submodule.span ℝ ({v} : Set Space)

/-- Two vectors in the span of a single vector are linearly dependent (the
elementary content of "rank ≤ 1"). -/
lemma linearDependent_pair_of_mem_span_singleton {x y v : Space}
    (hx : x ∈ Submodule.span ℝ ({v} : Set Space))
    (hy : y ∈ Submodule.span ℝ ({v} : Set Space)) :
    ¬ LinearIndependent ℝ ![x, y] := by
  rw [Submodule.mem_span_singleton] at hx hy
  rcases hx with ⟨a, hx⟩
  rcases hy with ⟨b, hy⟩
  intro hLI
  have h := (Fintype.linearIndependent_iff (R := ℝ) (v := ![x, y])).mp hLI
  by_cases ha : a = 0
  · -- x = 0; the combination (1, 0) is a nontrivial annihilation
    have hx0 : x = 0 := by rw [← hx, ha]; simp
    have hsum : (∑ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i • ![x, y] i) = 0 := by
      simp [Fin.sum_univ_two, hx0]
    have hc := h ![1, 0] hsum 0
    norm_num at hc
  · -- x = a•v, y = b•v; the combination (b, −a) annihilates them
    have hsum : (∑ i : Fin 2, (![b, -a] : Fin 2 → ℝ) i • ![x, y] i) = 0 := by
      simp [Fin.sum_univ_two, hx.symm, hy.symm]
      module
    have hc := h ![b, -a] hsum 1
    simp at hc
    exact ha hc

/-- **Easy direction of the rank-two criterion**: if the three partials all
lie on a common line, no two of them are linearly independent — the
directional derivative cannot have rank two. -/
theorem not_PartialRankTwo_of_collPartialOnLine {r : ℝ → Space} (a b m : ℝ)
    (h : collPartialOnLine r a b m) :
    ¬ PartialRankTwo r a b m := by
  rcases h with ⟨v, hA, hB, hM⟩
  rintro ⟨i, j, hij, hLI⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact linearDependent_pair_of_mem_span_singleton hA hB hLI
  · exact linearDependent_pair_of_mem_span_singleton hA hM hLI
  · exact linearDependent_pair_of_mem_span_singleton hB hA hLI
  · exact (hij rfl).elim
  · exact linearDependent_pair_of_mem_span_singleton hB hM hLI
  · exact linearDependent_pair_of_mem_span_singleton hM hA hLI
  · exact linearDependent_pair_of_mem_span_singleton hM hB hLI
  · exact (hij rfl).elim

/-- The cross product is perpendicular to its second factor (right version of
the commons `inner_cross3_self_left`, by antisymmetry). -/
lemma inner_cross3_self_right (u v : Space) : inner ℝ (cross3 u v) v = 0 := by
  have hsw : cross3 u v = - cross3 v u := cross3_anticomm (u := v) (v := u)
  rw [hsw]
  rw [inner_neg_left]
  have hz : inner ℝ (cross3 v u) v = 0 := by
    unfold cross3
    simpa using (Commons.Analysis.CrossProduct.inner_cross3_self_left (u := v) (v := u))
  simp [hz]

/-- The middle partial `∂_b = (r a − r m) × v(b)` is perpendicular to the
chord vector `r a − r m` (its first factor), unconditionally. -/
lemma inner_partialB_chord (r : ℝ → Space) (a b m : ℝ) :
    inner ℝ (collPartialB r a b m) (r a - r m) = 0 := by
  unfold collPartialB
  unfold cross3
  simpa using
    (Commons.Analysis.CrossProduct.inner_cross3_self_left (u := r a - r m)
      (v := velocity r b))

/-- Given that the two chord vectors are parallel (`r a − r m = t • (r a − r b)`),
the first partial `∂_a` is perpendicular to the chord direction `r a − r m`. -/
lemma inner_partialA_chord_of_parallel (r : ℝ → Space) (a b m : ℝ) {t : ℝ}
    (hW : r a - r m = t • (r a - r b)) :
    inner ℝ (collPartialA r a b m) (r a - r m) = 0 := by
  unfold collPartialA
  rw [inner_add_left]
  have h1 : inner ℝ (cross3 (velocity r a) (r a - r m)) (r a - r m) = 0 :=
    inner_cross3_self_right (velocity r a) (r a - r m)
  have h2 : inner ℝ (cross3 (r a - r b) (velocity r a)) (r a - r m) = 0 := by
    rw [hW, inner_smul_right]
    have hinner : inner ℝ (cross3 (r a - r b) (velocity r a)) (r a - r b) = 0 := by
      unfold cross3
      simpa using
        (Commons.Analysis.CrossProduct.inner_cross3_self_left (u := r a - r b)
          (v := velocity r a))
    simp [hinner]
  rw [h1, h2, add_zero]

/-- Given that the two chord vectors are parallel (`r a − r m = t • (r a − r b)`),
the third partial `∂_m` is perpendicular to the chord direction `r a − r m`. -/
lemma inner_partialM_chord_of_parallel (r : ℝ → Space) (a b m : ℝ) {t : ℝ}
    (hW : r a - r m = t • (r a - r b)) :
    inner ℝ (collPartialM r a b m) (r a - r m) = 0 := by
  unfold collPartialM
  rw [hW, inner_smul_right]
  have hinner : inner ℝ (cross3 (velocity r m) (r a - r b)) (r a - r b) = 0 :=
    inner_cross3_self_right (velocity r m) (r a - r b)
  simp [hinner]

/-- When the two chord vectors of a zero of `Φ` are parallel
(`r a − r m = t • (r a − r b)` — implied by `collinearityValue r a b m = 0`
together with the fleet lemma `cross3_eq_zero_iff_smul` once it lands), all
three partials are perpendicular to the chord direction `r a − r m`: the
derivative range lies in the plane perpendicular to the chord. -/
theorem partials_orthogonal_chord_of_parallel (r : ℝ → Space) (a b m : ℝ) {t : ℝ}
    (hW : r a - r m = t • (r a - r b)) :
    inner ℝ (collPartialA r a b m) (r a - r m) = 0 ∧
    inner ℝ (collPartialB r a b m) (r a - r m) = 0 ∧
    inner ℝ (collPartialM r a b m) (r a - r m) = 0 := by
  exact ⟨inner_partialA_chord_of_parallel r a b m hW,
    inner_partialB_chord r a b m, inner_partialM_chord_of_parallel r a b m hW⟩

/-! ### The converse data: chord parallelism at a zero of `Φ`

With the fleet lemma `cross3_eq_zero_iff_smul` (now committed) a zero of the
collinearity map forces the two chord vectors to be parallel:
`collinearityValue r a b m = 0` and `r a − r b ≠ 0` give
`∃ t, r a − r m = t • (r a − r b)` (`chord_parallel_of_collinearity_eq_zero`).
Writing `Z := r a − r b` and `W := r a − r m = t • Z`, the three hinge partials
factor as nonzero scalar multiples of the *velocity-cross* vectors:

    ∂_a = (t − 1) • (v(a) × Z)      ∂_b = −t • (v(b) × Z)      ∂_m = 1 • (v(m) × Z)

(`collPartialA_eq_smul`, `collPartialB_eq_smul`, `collPartialM_eq_smul`; the
scalars are nonzero for a nondegenerate triple: `t ≠ 0` since `W ≠ 0` and
`t ≠ 1` since that would give `r m = r b`).  Hence the rank-two question —
two independent partials — is exactly the question whether two of the
velocity-cross vectors `v(·) × Z` are independent: the pair-scaling lemma
`linearIndependent_pair_smul` (delegated to the commons) transfers
independence through the nonzero scalars.  This completes the reduction of
the rank-two criterion to the general-position condition on the velocities
relative to the chord direction `Z` (nondegenerate: no velocity parallel to
`Z`; two velocities not coplanar with `Z`). -/

/-- Cross-product zero, in terms of the local `cross3`: two vectors are
linearly dependent (one is zero or the other is a scalar multiple). -/
lemma cross3_eq_zero_iff_smul_local (u v : Space) :
    cross3 u v = 0 ↔ u = 0 ∨ ∃ t : ℝ, v = t • u := by
  simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul u v)

/-- At a zero of the collinearity map with the first chord vector nonzero,
the two chord vectors are parallel: `r a − r m = t • (r a − r b)`. -/
lemma chord_parallel_of_collinearity_eq_zero {r : ℝ → Space} {a b m : ℝ}
    (hZ : r a - r b ≠ 0) (hΦ : collinearityValue r a b m = 0) :
    ∃ t : ℝ, r a - r m = t • (r a - r b) := by
  have hc : cross3 (r a - r b) (r a - r m) = 0 := by
    simpa using hΦ
  rcases (cross3_eq_zero_iff_smul_local (u := r a - r b) (v := r a - r m)).mp hc with hz | ⟨t, ht⟩
  · exact False.elim (hZ hz)
  · exact ⟨t, ht⟩

/-- Factorisation of the first partial: with `r a − r m = t • (r a − r b)`,
`∂_a = (t − 1) • (v(a) × (r a − r b))`. -/
lemma collPartialA_eq_smul (r : ℝ → Space) (a b m : ℝ) {t : ℝ}
    (hW : r a - r m = t • (r a - r b)) :
    collPartialA r a b m = (t - 1) • cross3 (velocity r a) (r a - r b) := by
  unfold collPartialA
  rw [hW, cross3_smul_right]
  rw [cross3_anticomm (u := velocity r a) (v := r a - r b)]
  module

/-- Factorisation of the middle partial: with `r a − r m = t • (r a − r b)`,
`∂_b = −t • (v(b) × (r a − r b))`. -/
lemma collPartialB_eq_smul (r : ℝ → Space) (a b m : ℝ) {t : ℝ}
    (hW : r a - r m = t • (r a - r b)) :
    collPartialB r a b m = (-t) • cross3 (velocity r b) (r a - r b) := by
  unfold collPartialB
  rw [hW, cross3_smul_left]
  rw [cross3_anticomm (u := velocity r b) (v := r a - r b)]
  module

/-- Factorisation of the third partial: `∂_m = 1 • (v(m) × (r a − r b))`
(no hypothesis needed). -/
lemma collPartialM_eq_smul (r : ℝ → Space) (a b m : ℝ) :
    collPartialM r a b m = (1 : ℝ) • cross3 (velocity r m) (r a - r b) := by
  unfold collPartialM
  simp

/-! ### The rank-two criterion: assembly

The reduction is completed by indexing the three parameters and their
factorisation scalars: `collParam a b m : Fin 3 → ℝ` picks `a, b, m` at
indices `0, 1, 2`, and `collCoeff t` records the three nonzero scalars
`t − 1, −t, 1` (nonzero when `t ∉ {0, 1}`, `collCoeff_ne_zero`).  The
factorisation `collPartial_eq_coeff` bundles the three partial-factorisation
lemmas: `∂_i = collCoeff t i • (v(p_i) × Z)`.  With the pair-scaling
independence lemma `linearIndependent_pair_smul` (commons), scaling by the
nonzero `collCoeff`s transfers independence in both directions, giving the
**rank-two criterion**: under `Φ = 0` (i.e. `r a − r m = t • (r a − r b)`,
`t ∉ {0,1}`, `Z := r a − r b ≠ 0`), the directional derivative of `Φ` at
`(a,b,m)` has rank two iff two of the *velocity-cross* vectors
`v(p_i) × Z` are linearly independent — the general-position condition on
the velocities relative to the chord direction. -/

/-- The parameter of the knot at index `0 ↦ a`, `1 ↦ b`, `2 ↦ m`. -/
def collParam (a b m : ℝ) : Fin 3 → ℝ
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | _ => m

/-- The factorisation scalar of the partial at index `0 ↦ t − 1`,
`1 ↦ −t`, `2 ↦ 1` (from `∂_a = (t−1)(v(a)×Z)`, `∂_b = (−t)(v(b)×Z)`,
`∂_m = 1·(v(m)×Z)`). -/
def collCoeff (t : ℝ) : Fin 3 → ℝ
  | ⟨0, _⟩ => t - 1
  | ⟨1, _⟩ => -t
  | _ => 1

/-- The factorisation scalars are nonzero when `t ∉ {0, 1}` (a nondegenerate
trisecant: `t = 1` would collapse `m` onto `b`, `t = 0` onto `a`). -/
lemma collCoeff_ne_zero (t : ℝ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (i : Fin 3) :
    collCoeff t i ≠ 0 := by
  fin_cases i
  · change t - 1 ≠ 0
    intro h
    apply ht1
    linarith
  · change -t ≠ 0
    intro h
    apply ht0
    linarith
  · change (1 : ℝ) ≠ 0
    norm_num

/-- The bundled partial factorisation at every index:
`∂_i = collCoeff t i • (v(collParam a b m i) × (r a − r b))` whenever
`r a − r m = t • (r a − r b)`. -/
lemma collPartial_eq_coeff (r : ℝ → Space) (a b m t : ℝ)
    (hW : r a - r m = t • (r a - r b)) (i : Fin 3) :
    collPartial r a b m i =
      collCoeff t i • cross3 (velocity r (collParam a b m i)) (r a - r b) := by
  fin_cases i
  · change collPartialA r a b m = (t - 1) • cross3 (velocity r a) (r a - r b)
    exact collPartialA_eq_smul r a b m hW
  · change collPartialB r a b m = (-t) • cross3 (velocity r b) (r a - r b)
    exact collPartialB_eq_smul r a b m hW
  · change collPartialM r a b m = (1 : ℝ) • cross3 (velocity r m) (r a - r b)
    exact collPartialM_eq_smul r a b m

/-- Scaling a linearly independent pair of vectors by *nonzero* scalars
preserves independence in both directions (wrapper of the commons
`linearIndependent_pair_smul`). -/
lemma linearIndependent_pair_smul_iff {c d : ℝ} (hc : c ≠ 0) (hd : d ≠ 0)
    {X Y : Space} :
    LinearIndependent ℝ ![c • X, d • Y] ↔ LinearIndependent ℝ ![X, Y] := by
  constructor
  · intro h
    have hinv := Commons.Analysis.LinearAlgebra.linearIndependent_pair_smul
      (x := c • X) (y := d • Y) (c := c⁻¹) (d := d⁻¹)
      (by exact inv_ne_zero hc) (by exact inv_ne_zero hd) h
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hc, inv_mul_cancel₀ hd, one_smul, one_smul] at hinv
    exact hinv
  · intro h
    exact Commons.Analysis.LinearAlgebra.linearIndependent_pair_smul hc hd h

/-- **The rank-two criterion**: under a zero of the collinearity map with
`r a − r m = t • (r a − r b)`, `t ∉ {0, 1}`, the directional derivative of
`Φ` at `(a,b,m)` has rank two — two of the three hinge partials are linearly
independent (`PartialRankTwo`) — iff two of the velocity-cross vectors
`v(p_i) × (r a − r b)` are linearly independent: the general-position
condition on the velocities relative to the chord direction `r a − r b`
(no velocity parallel to the chord; some two velocities not coplanar with
it). -/
theorem PartialRankTwo_iff_velocityCross_pair (r : ℝ → Space) (a b m : ℝ) {t : ℝ}
    (hW : r a - r m = t • (r a - r b))
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    PartialRankTwo r a b m ↔
      ∃ i j : Fin 3, i ≠ j ∧
        LinearIndependent ℝ ![cross3 (velocity r (collParam a b m i)) (r a - r b),
          cross3 (velocity r (collParam a b m j)) (r a - r b)] := by
  constructor
  · rintro ⟨i, j, hij, hLI⟩
    have hcfi : collCoeff t i ≠ 0 := collCoeff_ne_zero t ht0 ht1 i
    have hcfj : collCoeff t j ≠ 0 := collCoeff_ne_zero t ht0 ht1 j
    rw [collPartial_eq_coeff r a b m t hW i, collPartial_eq_coeff r a b m t hW j] at hLI
    exact ⟨i, j, hij,
      (linearIndependent_pair_smul_iff (c := collCoeff t i) (d := collCoeff t j)
        hcfi hcfj).mp hLI⟩
  · rintro ⟨i, j, hij, hLI⟩
    have hcfi : collCoeff t i ≠ 0 := collCoeff_ne_zero t ht0 ht1 i
    have hcfj : collCoeff t j ≠ 0 := collCoeff_ne_zero t ht0 ht1 j
    refine ⟨i, j, hij, ?_⟩
    have hscaled : LinearIndependent ℝ ![collCoeff t i • cross3 (velocity r (collParam a b m i)) (r a - r b),
        collCoeff t j • cross3 (velocity r (collParam a b m j)) (r a - r b)] :=
      (linearIndependent_pair_smul_iff (c := collCoeff t i) (d := collCoeff t j)
        hcfi hcfj).mpr hLI
    rw [collPartial_eq_coeff r a b m t hW i, collPartial_eq_coeff r a b m t hW j]
    exact hscaled

/-! ### The criterion at a zero of `Φ` (final form)

Combining the parallelism extraction with the criterion: at a nondegenerate
zero of the collinearity map (all three pairwise image-distinct, so the two
chord vectors and their difference are nonzero) the rank-two criterion holds
in its geometric form — two of the velocity-cross vectors `v(p_i) × Z` are
linearly independent. -/

/-- `t ≠ 1` follows from `r m − r b ≠ 0` when `r a − r m = t • (r a − r b)`
(since `t = 1` would give `r m = r b`). -/
lemma t_ne_one_of_chord {r : ℝ → Space} {a b m : ℝ} {t : ℝ}
    (hmb : r m - r b ≠ 0) (hW : r a - r m = t • (r a - r b)) : t ≠ 1 := by
  intro h
  apply hmb
  have hEq : r a - r m = r a - r b := by simpa [h] using hW
  have hEq0 : (r a - r m) - (r a - r b) = 0 := by
    rw [hEq]
    simp
  have hsub : r m - r b = 0 := by
    calc
      r m - r b = -((r a - r m) - (r a - r b)) := by abel
      _ = 0 := by rw [hEq0, neg_zero]
  exact hsub

/-- `t ≠ 0` follows from `r a − r m ≠ 0` when `r a − r m = t • (r a − r b)`. -/
lemma t_ne_zero_of_chord {r : ℝ → Space} {a b m : ℝ} {t : ℝ}
    (hW0 : r a - r m ≠ 0) (hW : r a - r m = t • (r a - r b)) : t ≠ 0 := by
  intro h
  apply hW0
  simp [hW, h]

/-- **The rank-two criterion at a nondegenerate zero of `Φ`** (final form):
if `Φ(a,b,m) = 0` with the three knot points pairwise distinct (so the two
chord vectors and their difference are nonzero), then the directional
derivative of `Φ` has rank two iff two of the velocity-cross vectors
`v(p_i) × (r a − r b)` are linearly independent.  This is the regular-value
condition of the smooth-curve structure of `Φ⁻¹(0)` at the triple. -/
theorem rank_two_criterion_at_collinearity_zero {r : ℝ → Space} {a b m : ℝ}
    (hZ : r a - r b ≠ 0) (hW : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hΦ : collinearityValue r a b m = 0) :
    PartialRankTwo r a b m ↔
      ∃ i j : Fin 3, i ≠ j ∧
        LinearIndependent ℝ ![cross3 (velocity r (collParam a b m i)) (r a - r b),
          cross3 (velocity r (collParam a b m j)) (r a - r b)] := by
  rcases chord_parallel_of_collinearity_eq_zero hZ hΦ with ⟨t, hWpar⟩
  have ht0 : t ≠ 0 := t_ne_zero_of_chord hW hWpar
  have ht1 : t ≠ 1 := t_ne_one_of_chord hmb hWpar
  exact PartialRankTwo_iff_velocityCross_pair r a b m hWpar ht0 ht1

/-- The partial at index `0` is `∂_a`. -/
lemma collPartial_eq_A (r : ℝ → Space) (a b m : ℝ) :
    collPartial r a b m (0 : Fin 3) = collPartialA r a b m := by
  change collPartialA r a b m = collPartialA r a b m
  rfl

/-- The partial at index `1` is `∂_b`. -/
lemma collPartial_eq_B (r : ℝ → Space) (a b m : ℝ) :
    collPartial r a b m (1 : Fin 3) = collPartialB r a b m := by
  change collPartialB r a b m = collPartialB r a b m
  rfl

/-- The partial at index `2` is `∂_m`. -/
lemma collPartial_eq_M (r : ℝ → Space) (a b m : ℝ) :
    collPartial r a b m (2 : Fin 3) = collPartialM r a b m := by
  change collPartialM r a b m = collPartialM r a b m
  rfl

end LeanEval.KnotTheory.Quadrisecant
