import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.RealizationDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology

set_option linter.unusedVariables false

noncomputable section

/-! ### Combinatorial model: a single vertex and nothing above it

The `Δ`-complex with one `0`-simplex and no positive-dimensional simplices.  The
cardinality function is written as `Nat.casesOn k 1 (fun _ => 0)` so that
`card (k+1)` and `card (k+2)` *reduce* to `0` definitionally; this makes every
face map and every semi-simplicial identity vacuous, with no transport needed. -/

/-- The number of `k`-simplices: one in degree `0`, none above. -/
def finOneCard : ℕ → ℕ := fun k => Nat.casesOn k 1 (fun _ => 0)

lemma finOneCard_pos {k : ℕ} (h : 0 < k) : finOneCard k = 0 := by
  cases k with
  | zero => omega
  | succ k => rfl

/-- The face maps, vacuous: their domain is `Fin 0`. -/
def finOneCxFace : ∀ {k : ℕ}, Fin (finOneCard (k+1)) → Fin (k+2) → Fin (finOneCard k) :=
  fun {k} σ _ => Fin.elim0 σ

/-- The semi-simplicial identities, vacuous: their domain is `Fin 0`. -/
lemma finOneCxFace_face : ∀ {k : ℕ} (σ : Fin (finOneCard (k+2))) (i j : Fin (k+2)), i ≤ j →
    finOneCxFace (finOneCxFace σ (Fin.succ j)) i = finOneCxFace (finOneCxFace σ (Fin.castSucc i)) j := by
  intro k σ
  exact Fin.elim0 σ

lemma finOneCxCard_eq_zero : ∀ k : ℕ, 0 < k → finOneCard k = 0 := fun k h => finOneCard_pos h

/-- The `Δ`-complex with a single vertex and no higher simplices. -/
def finOneCx : DeltaCx where
  dim := 0
  card := finOneCard
  face := finOneCxFace
  face_face := finOneCxFace_face
  card_eq_zero := finOneCxCard_eq_zero

lemma finOneCx_card_zero : finOneCx.card 0 = 1 := rfl

lemma finOneCx_card_pos (k : ℕ) (h : 0 < k) : finOneCx.card k = 0 := finOneCard_pos h

/-! ### Realizing it in the one-point space -/

/-- The one-point space. -/
abbrev finOneSpace : TopCat := TopCat.of (Fin 1)

/-- The unique singular `0`-simplex of the one-point space. -/
def finOneSingZero : (TopCat.toSSet.obj finOneSpace).obj (Opposite.op (SimplexCategory.mk 0)) :=
  (TopCat.toSSetObjEquiv finOneSpace (Opposite.op (SimplexCategory.mk 0))).symm
    (ContinuousMap.const (StdSimplex ℝ (Fin 1)) (0 : Fin 1))

/-- The characteristic maps: the (unique) singular `0`-simplex in degree `0` and
nothing in positive degrees. -/
def finOneChi : (k : ℕ) → Fin (finOneCx.card k) →
    (TopCat.toSSet.obj finOneSpace).obj (Opposite.op (SimplexCategory.mk k))
  | 0, _ => finOneSingZero
  | (k+1), σ => Fin.elim0 σ

lemma finOneChi_face_compat : ∀ {k : ℕ} (σ : Fin (finOneCx.card (k+1))) (i : Fin (k+2)),
    finOneChi k (finOneCx.face σ i) = singFace i (finOneChi (k+1) σ) := by
  intro k σ
  exact Fin.elim0 σ

/-- The characteristic maps of the single vertex, compatible with faces. -/
def finOneSimplexMap : DeltaSimplexMap finOneCx finOneSpace where
  χ := finOneChi
  face_compat := fun {k} σ i => finOneChi_face_compat σ i

/-- The interior point of the unique `0`-simplex. -/
def finOnePt : OpenSimplex finOneCx where
  dim := 0
  idx := ⟨0, finOneCx_card_zero.symm ▸ Nat.zero_lt_one⟩
  pt := StdSimplex.single (0 : Fin 1)
  pos := by
    intro i
    rw [StdSimplex.weights_apply_eq_one (StdSimplex.single (0 : Fin 1)) i]
    norm_num

/-- The open simplices of `finOneCx` form a subsingleton: the dimension is forced
to be `0` by the existence of an index, and then the index and the interior point
are both unique. -/
instance finOneSubsingletonOpenSimplex : Subsingleton (OpenSimplex finOneCx) where
  allEq p q := by
    obtain ⟨pd, pi, pp, ppos⟩ := p
    obtain ⟨qd, qi, qp, qpos⟩ := q
    have hp : pd = 0 := by
      by_contra h
      have h0 : finOneCx.card pd = 0 := finOneCx_card_pos pd (Nat.pos_of_ne_zero h)
      exact Fin.elim0 (Fin.cast h0 pi)
    have hq : qd = 0 := by
      by_contra h
      have h0 : finOneCx.card qd = 0 := finOneCx_card_pos qd (Nat.pos_of_ne_zero h)
      exact Fin.elim0 (Fin.cast h0 qi)
    subst hp
    subst hq
    have : Subsingleton (Fin (finOneCx.card 0)) := by rw [finOneCx_card_zero]; infer_instance
    have h1 : pi = qi := Subsingleton.elim _ _
    have h2 : pp = qp := Subsingleton.elim _ _
    subst h1
    subst h2
    have h3 : ppos = qpos := Subsingleton.elim _ _
    rw [h3]

/-- The realization of the single-vertex `Δ`-complex in the one-point space. -/
def finOneRealization : DeltaRealization finOneCx finOneSpace where
  toDeltaSimplexMap := finOneSimplexMap
  compact := inferInstance
  t2 := inferInstance
  bij := fun x => ⟨finOnePt, Subsingleton.elim _ _, fun q _ => Subsingleton.elim q finOnePt⟩
  weak := fun s => ⟨fun hs => fun k σ => (finOneSimplexMap.cls k σ).continuous.isOpen_preimage s hs,
                   fun _ => isOpen_discrete s⟩

/-- **Consistency of the realization interface.**  There is a `Δ`-complex with a
single vertex and no higher simplices (so `K.card 0 = 1` and `K.card k = 0` for
`k > 0`) realized in the one-point space `TopCat.of (Fin 1)`.

This is a non-vacuity check for `DeltaRealization`: it shows that the fields
(compact Hausdorff, every point in exactly one open simplex, the weak topology)
can be satisfied, and in particular that `DeltaRealization K X` is inhabited.
Hints: `K := { dim := 0, card := fun k => if k = 0 then 1 else 0, face := ... }`
with faces eliminated through `Fin.elim0` (their domain is `Fin 0`) and both
`face_face` and `face_compat` vacuous; the `χ` field at `k = 0` is the (unique)
singular `0`-simplex of `Fin 1`; `bij` uses that `StdSimplex ℝ (Fin 1)` is a
singleton with weight `1`; `weak` is trivial because `Fin 1` is discrete. -/
theorem exists_realization_finOne :
    ∃ (K : DeltaCx) (R : DeltaRealization K (TopCat.of (Fin 1))),
      K.card 0 = 1 ∧ (∀ k : ℕ, 0 < k → K.card k = 0) := by
  exact ⟨finOneCx, finOneRealization, finOneCx_card_zero, fun k h => finOneCx_card_pos k h⟩

end

end Work.DeltaHomology
