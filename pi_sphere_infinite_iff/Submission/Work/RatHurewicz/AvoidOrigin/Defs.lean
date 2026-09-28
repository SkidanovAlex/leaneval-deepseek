import Mathlib
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.RatHurewicz.rawWeight_eqvGen

/-!
# The vocabulary of "transporting a cell along the gluing relation" of the cycle model

This module fixes the vocabulary used to prove `Work.RatHurewicz.avoidCellOrigin`.

For a point `x` of a copy of `Δ^{n+2}` whose support is a given set `S` of vertices, the *transport*
of `x` along a map `τ` of the vertices of `S` is the point whose mass at `t ∈ S` has been moved to
the vertex `τ t`.  The generating relations of `modelRel D` are exactly of the form
"`facept p u` is glued to `facept q u`", and on the level of mass distributions this says that the
mass is moved by the vertex map `succ_q ∘ invSuccAbove p`.  The inductive relation `ChainTrans`
below describes the cells and vertex maps reachable from a cell `(i,S)` by a chain of such moves; it
is the combinatorial skeleton of the description of the class of a point of `Model D`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- The extension of a map defined on the vertices of `S` by the identity outside `S`. -/
def vertExt {S : Finset (Fin (n + 2))} (τ : {t // t ∈ S} → Fin (n + 2)) :
    Fin (n + 2) → Fin (n + 2) :=
  fun t => if h : t ∈ S then τ ⟨t, h⟩ else t

/-- The mass distribution obtained by moving the mass carried by the vertex `t ∈ S` to the
vertex `τ t`. -/
def transportFun {S : Finset (Fin (n + 2))} (x : Fin (n + 2) → ℝ)
    (τ : {t // t ∈ S} → Fin (n + 2)) : Fin (n + 2) → ℝ :=
  fun w => ∑ t : {t // t ∈ S}, if τ t = w then x t else 0

@[simp] theorem transportFun_apply {S : Finset (Fin (n + 2))} (x : Fin (n + 2) → ℝ)
    (τ : {t // t ∈ S} → Fin (n + 2)) (w : Fin (n + 2)) :
    transportFun x τ w = ∑ t : {t // t ∈ S}, if τ t = w then x t else 0 := rfl

/-- The sum of the coordinates of a point of the simplex over the support is `1`. -/
theorem sum_attach_eq_one {S : Finset (Fin (n + 2))} {x : stdSimplex ℝ (Fin (n + 2))}
    (hx : ptSupport x = S) : (∑ t : {t // t ∈ S}, (x : Fin (n + 2) → ℝ) t) = 1 := by
  have hzero : ∀ w : Fin (n + 2), w ∉ S → (x : Fin (n + 2) → ℝ) w = 0 := by
    intro w hw
    by_contra hne
    exact hw (hx ▸ mem_ptSupport.mpr hne)
  exact (Finset.sum_attach S fun t => (x : Fin (n + 2) → ℝ) t).trans
    ((Finset.sum_subset (Finset.subset_univ S) fun w _ hw => hzero w hw).trans x.2.2)

/-- **The transport of a point of the standard simplex along a map of vertices.** -/
def transportPt {S : Finset (Fin (n + 2))} (x : stdSimplex ℝ (Fin (n + 2)))
    (hx : ptSupport x = S) (τ : {t // t ∈ S} → Fin (n + 2))
    (hτ : Function.Injective τ) : stdSimplex ℝ (Fin (n + 2)) :=
  ⟨transportFun x τ, by
    refine ⟨fun w => Finset.sum_nonneg fun t _ => ?_, ?_⟩
    · by_cases h : τ t = w
      · simp only [h, if_true]; exact x.2.1 t
      · simp only [h, if_false]; exact le_refl 0
    · simp only [transportFun]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact sum_attach_eq_one hx⟩

@[simp] theorem transportPt_apply {S : Finset (Fin (n + 2))} (x : stdSimplex ℝ (Fin (n + 2)))
    (hx : ptSupport x = S) (τ : {t // t ∈ S} → Fin (n + 2)) (hτ : Function.Injective τ)
    (w : Fin (n + 2)) :
    (transportPt x hx τ hτ : Fin (n + 2) → ℝ) w
      = ∑ t : {t // t ∈ S}, if τ t = w then (x : Fin (n + 2) → ℝ) t else 0 := rfl

/-- The "inverse" of `Fin.succAbove P`: the increasing bijection from `Fin (m+1) ∖ {P}` onto
`Fin m`, with a junk value at `P`. -/
def invSuccAbove {m : ℕ} [NeZero m] (P : Fin (m + 1)) : Fin (m + 1) → Fin m :=
  fun i => if h : ∃ v : Fin m, P.succAbove v = i then Classical.choose h else 0

theorem invSuccAbove_succAbove {m : ℕ} [NeZero m] (P : Fin (m + 1)) (v : Fin m) :
    invSuccAbove P (P.succAbove v) = v := by
  have h : ∃ w : Fin m, P.succAbove w = P.succAbove v := ⟨v, rfl⟩
  have h1 : invSuccAbove P (P.succAbove v) = Classical.choose h := by
    rw [invSuccAbove]; exact dif_pos h
  rw [h1]
  exact P.succAbove_right_injective (Classical.choose_spec h)

theorem succAbove_invSuccAbove {m : ℕ} [NeZero m] (P : Fin (m + 1)) {i : Fin (m + 1)}
    (hi : i ≠ P) : P.succAbove (invSuccAbove P i) = i := by
  have h : ∃ v : Fin m, P.succAbove v = i := Fin.exists_succAbove_eq hi
  have h1 : invSuccAbove P i = Classical.choose h := by rw [invSuccAbove]; exact dif_pos h
  rw [h1]
  exact Classical.choose_spec h

theorem strictMono_invSuccAbove {m : ℕ} [NeZero m] (P : Fin (m + 1)) :
    ∀ {i j : Fin (m + 1)}, i ≠ P → j ≠ P → i < j → invSuccAbove P i < invSuccAbove P j := by
  intro i j hi hj hij
  by_contra h
  have h1 : P.succAbove (invSuccAbove P j) ≤ P.succAbove (invSuccAbove P i) :=
    (Fin.strictMono_succAbove P).le_iff_le.mpr (not_lt.mp h)
  rw [succAbove_invSuccAbove P hi, succAbove_invSuccAbove P hj] at h1
  exact absurd h1 (not_le.mpr hij)

theorem invSuccAbove_injOn {m : ℕ} [NeZero m] (P : Fin (m + 1)) {i j : Fin (m + 1)}
    (hi : i ≠ P) (hj : j ≠ P) (h : invSuccAbove P i = invSuccAbove P j) : i = j := by
  rw [← succAbove_invSuccAbove P hi, h, succAbove_invSuccAbove P hj]

/-- **The cells (and vertex maps) reachable from a cell `(i,S)` of the model.**  A chain is a
sequence of gluings: the step is the algebraic content of the generating relation
`facept p u ~ facept q u` of the model, namely the transport of the mass by the vertex map
`succ_q ∘ invSuccAbove p`. -/
inductive ChainTrans (D : MData X n x₀) (i : D.Idx) (S : Finset (Fin (n + 2))) :
    (j : D.Idx) → ({t // t ∈ S} → Fin (n + 2)) → Prop
  | refl : ChainTrans D i S i (fun t => t.1)
  | step {j : D.Idx} {τ : {t // t ∈ S} → Fin (n + 2)} {l : D.Idx} {p q : Fin (n + 2)} :
      ChainTrans D i S j τ → (∀ t, τ t ≠ p) →
      (D.simplexMap j).comp (facept (n + 1) p) = (D.simplexMap l).comp (facept (n + 1) q) →
      ChainTrans D i S l (fun t => Fin.succAbove q (invSuccAbove p (τ t)))

end

end Work.RatHurewicz
