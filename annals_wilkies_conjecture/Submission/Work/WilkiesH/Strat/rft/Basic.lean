import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Cell
import Submission.Work.WilkiesH.Dim.dimLE_mono
import Submission.Work.WilkiesH.Strat.BadCell
import Submission.Work.WilkiesH.Strat.thin_union_cyl
import Submission.Work.WilkiesH.Strat.cellData
import Submission.Work.WilkiesH.Strat.dimLE_iUnion_fin
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG5.Reindex2
import Submission.Work.WilG5.Reindex3

/-!
# The relative frontier of `X` in `V` is thin

The target of this file is `Work.WilkiesH.Strat.rel_frontier_thin`:

> for `X ∈ Ω` and a semialgebraic `V ∈ Ω` with `DimLE V μ`, the relative frontier
> `X ∩ V ∩ closure (V \ X)` has o-minimal dimension `≤ μ - 1`.

The mathematical content is the standard o-minimal dimension drop for a definable set inside a
definable set (here the second set is semialgebraic), together with the dimension theorem for
`Ω`-graphs ("a definable map does not increase dimension"), which is developed here from the
`SharpCD` axiom: `dimLE_of_graphOver` and its thin-source refinement.

## Contents

* `existsThinLevel` — uncountably many disjoint sets with nonempty interior cannot all sit in an
  interval (second countability of `ℝᵐ`); the uncountably-many-thin-level input of `master`.
* `GraphOver` — `G ⊆ ℝ^{m+t}` is a graph over its first `m` coordinates.
* `thin_source` — the thin-source step of the dimension theorem.
* `master` — the master step.
* `dimLE_of_graphOver` — the dimension theorem for `Ω`-graphs.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture
open Work.WilG5

variable {S : WilkiesDesign.SOMin}

/-! ## 1. Thin levels -/

/-- Uncountably many pairwise disjoint sets with nonempty interior cannot be contained in an
interval: at most countably many disjoint open sets fit in `ℝᵐ` (second countability). -/
theorem existsThinLevel {m : ℕ} (a b : ℝ) (hab : a < b) (Φ : ℝ → Set (Fin m → ℝ))
    (hdisj : ∀ c ∈ Set.Ioo a b, ∀ c' ∈ Set.Ioo a b, c ≠ c' → Disjoint (Φ c) (Φ c')) :
    ∃ c ∈ Set.Ioo a b, interior (Φ c) = ∅ := by
  by_contra h
  push_neg at h
  haveI : TopologicalSpace.SeparableSpace (Fin m → ℝ) := inferInstance
  have he : (Set.Ioo a b).Countable :=
    Set.PairwiseDisjoint.countable_of_nonempty_interior (s := Φ) (a := Set.Ioo a b)
      hdisj fun c hc => h c hc
  have hle : b ≤ a := Cardinal.Real.Ioo_countable_iff.mp he
  exact absurd hab (not_lt.mpr hle)

/-! ## 2. Graphs over the first coordinates -/

/-- `G ⊆ ℝ^{m+t}` is a graph over its first `m` coordinates: the projection to those coordinates
is injective on `G`. -/
def GraphOver (m : ℕ) {t : ℕ} (G : Set (Fin (m + t) → ℝ)) : Prop :=
  ∀ z ∈ G, ∀ z' ∈ G, (∀ i : Fin m, z (Fin.castAdd t i) = z' (Fin.castAdd t i)) → z = z'

/-- A point of `ℝ^{m+t}` is determined by its first `m` and its last `t` coordinates. -/
theorem eq_of_castAdd_natAdd {m t : ℕ} {x y : Fin (m + t) → ℝ}
    (h : ∀ i : Fin m, x (Fin.castAdd t i) = y (Fin.castAdd t i))
    (h' : ∀ j : Fin t, x (Fin.natAdd m j) = y (Fin.natAdd m j)) : x = y := by
  funext i
  rcases Nat.lt_or_ge i.val m with hlt | hge
  · rw [show i = Fin.castAdd t ⟨i.val, hlt⟩ from Fin.ext rfl]
    exact h _
  · have hji : i = Fin.natAdd m (⟨i.val - m, by have := i.isLt; omega⟩ : Fin t) := by
      apply Fin.ext
      show i.val = m + (i.val - m)
      omega
    rw [hji]
    exact h' _

/-- The first `m` coordinates of `Fin.append x y` are those of `x`. -/
theorem append_castAdd {m t : ℕ} (x : Fin m → ℝ) (y : Fin t → ℝ) (i : Fin m) :
    Fin.append x y (Fin.castAdd t i) = x i := Fin.append_left x y i

/-- The last `t` coordinates of `Fin.append x y` are those of `y`. -/
theorem append_natAdd {m t : ℕ} (x : Fin m → ℝ) (y : Fin t → ℝ) (j : Fin t) :
    Fin.append x y (Fin.natAdd m j) = y j := Fin.append_right x y j

/-- Membership in `lastN`. -/
theorem mem_lastN' {m t : ℕ} {G : Set (Fin (m + t) → ℝ)} {y : Fin t → ℝ} :
    y ∈ lastN t G ↔ ∃ x : Fin m → ℝ, Fin.append x y ∈ G := Iff.rfl

/-- Membership in `projN`. -/
theorem mem_projN' {m t : ℕ} {G : Set (Fin (m + t) → ℝ)} {x : Fin m → ℝ} :
    x ∈ projN t G ↔ ∃ y : Fin t → ℝ, Fin.append x y ∈ G := Iff.rfl

/-- Membership in `coordImage`. -/
theorem mem_coordImage' {m N : ℕ} {ι : Fin m → Fin N} {A : Set (Fin N → ℝ)} {u : Fin m → ℝ} :
    u ∈ coordImage ι A ↔ ∃ x ∈ A, x ∘ ι = u := Iff.rfl

/-- Membership in `liftFirst`. -/
theorem mem_liftFirst' {m k : ℕ} {A : Set (Fin m → ℝ)} {z : Fin (m + k) → ℝ} :
    z ∈ liftFirst k A ↔ (fun i : Fin m => z (Fin.castAdd k i)) ∈ A := Iff.rfl

/-- Two `Fin.append`s are equal iff their parts are. -/
theorem eq_of_append {m t : ℕ} {x x' : Fin m → ℝ} {y y' : Fin t → ℝ}
    (h : Fin.append x y = Fin.append x' y') : x = x' ∧ y = y' := by
  constructor
  · funext i
    have hh := congrFun h (Fin.castAdd t i)
    rwa [append_castAdd, append_castAdd] at hh
  · funext j
    have hh := congrFun h (Fin.natAdd m j)
    rwa [append_natAdd, append_natAdd] at hh

/-! ## 3. Elementary dimension lemmas -/

/-- The image of an interior point of `X` under a coordinate map is an interior point of the
image of `X`. -/
theorem mem_interior_image_coord {n m : ℕ} (e : Fin m ↪ Fin n) {X : Set (Fin n → ℝ)}
    {x : Fin n → ℝ} (hx : x ∈ interior X) :
    (x ∘ e) ∈ interior ((fun y : Fin n → ℝ => y ∘ e) '' X) := by
  obtain ⟨ε, hε, hbox⟩ := mem_interior_iff_boxAround.mp hx
  refine mem_interior_iff_boxAround.mpr ⟨ε, hε, fun w hw => ?_⟩
  refine ⟨Function.extend e w x, ?_, ?_⟩
  · refine hbox (mem_boxAround.mpr fun j => ?_)
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      have hh := mem_boxAround.mp hw i
      rw [Function.comp_apply] at hh
      rw [Function.Injective.extend_apply e.injective w x i]
      exact hh
    · rw [Function.extend_apply' w x j h, sub_self, abs_zero]
      exact hε
  · funext i
    exact Function.Injective.extend_apply e.injective w x i

/-- A subsingleton in `ℝⁿ`, `n ≥ 1`, has empty interior. -/
theorem interior_eq_empty_of_subsingleton' {n : ℕ} (hn : 1 ≤ n) {X : Set (Fin n → ℝ)}
    (hX : X.Subsingleton) : interior X = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨ε, hε, hbox⟩ := mem_interior_iff_boxAround.mp hx
  have hxX : x ∈ X := interior_subset hx
  let y : Fin n → ℝ := fun j => if j = ⟨0, hn⟩ then x j + ε / 2 else x j
  have hy0 : y ⟨0, hn⟩ = x ⟨0, hn⟩ + ε / 2 := by
    dsimp only [y]; rw [if_pos rfl]
  have hyj : ∀ j, j ≠ ⟨0, hn⟩ → y j = x j := by
    intro j hj; dsimp only [y]; rw [if_neg hj]
  have hyX : y ∈ X := hbox (mem_boxAround.mpr fun j => by
    by_cases hj : j = ⟨0, hn⟩
    · subst hj
      rw [hy0, add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith
    · rw [hyj j hj, sub_self, abs_zero]
      exact hε)
  have hxy : x = y := hX hxX hyX
  have hne : y ≠ x := by
    intro h
    have hh := congrFun h ⟨0, hn⟩
    rw [hy0] at hh
    linarith
  exact hne hxy.symm

/-- `DimLE X (n-1)` for `X ⊆ ℝⁿ` (`n ≥ 1`) says exactly that `X` has empty interior. -/
theorem interior_eq_empty_of_dimLE' {n : ℕ} (hn : 1 ≤ n) {X : Set (Fin n → ℝ)}
    (h : WilkiesDesign.DimLE X (n - 1)) : interior X = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hcast : n - 1 + 1 = n := Nat.sub_add_cancel hn
  let e : Fin (n - 1 + 1) ↪ Fin n := (Equiv.cast (congrArg Fin hcast)).toEmbedding
  have hmem := mem_interior_image_coord e hx
  rw [h e] at hmem
  exact hmem

/-! ## 4. The two index transports -/

/-- The index map of the *thin source* transport. -/
def thinIdx {m k t : ℕ} (e : Fin k ↪ Fin m) : Fin (k + t) → Fin (m + t) :=
  fun i => if h : i.val < k then Fin.castAdd t (e ⟨i.val, h⟩)
    else Fin.natAdd m ⟨i.val - k, by omega⟩

theorem thinIdx_castAdd {m k t : ℕ} (e : Fin k ↪ Fin m) (i : Fin k) :
    thinIdx e (Fin.castAdd t i) = Fin.castAdd t (e i) := by
  unfold thinIdx
  rw [dif_pos (by simpa using i.isLt)]
  rfl

theorem thinIdx_natAdd {m k t : ℕ} (e : Fin k ↪ Fin m) (j : Fin t) :
    thinIdx e (Fin.natAdd k j) = Fin.natAdd m j := by
  unfold thinIdx
  rw [dif_neg (by rw [natAdd_val]; omega)]
  congr 1
  apply Fin.ext
  show ↑(Fin.natAdd k j) - k = ↑j
  rw [natAdd_val]
  omega

/-- The index map of the *slicing* transport. -/
def sliceIdx {m t : ℕ} (e : Fin (m + 1) ↪ Fin t) : Fin (m + (m + 1)) → Fin (m + t) :=
  fun i => if h : i.val < m then Fin.castAdd t ⟨i.val, by omega⟩
    else Fin.natAdd m (e ⟨i.val - m, by omega⟩)

theorem sliceIdx_castAdd {m t : ℕ} (e : Fin (m + 1) ↪ Fin t) (i : Fin m) :
    sliceIdx e (Fin.castAdd (m + 1) i) = Fin.castAdd t i := by
  unfold sliceIdx
  rw [dif_pos (by simpa using i.isLt)]
  rfl

theorem sliceIdx_natAdd {m t : ℕ} (e : Fin (m + 1) ↪ Fin t) (j : Fin (m + 1)) :
    sliceIdx e (Fin.natAdd m j) = Fin.natAdd m (e j) := by
  unfold sliceIdx
  rw [dif_neg (by rw [natAdd_val]; omega)]
  congr 1
  congr 1
  apply Fin.ext
  show ↑(Fin.natAdd m j) - m = ↑j
  rw [natAdd_val]
  omega

/-! ## 5. The `Ω`-bookkeeping lemmas used by the induction -/

/-- Membership in a coordinate hyperplane is `Ω`. -/
theorem eq_coord_mem (n : ℕ) (i : Fin n) (c : ℝ) :
    {z : Fin n → ℝ | z i = c} ∈ S.Ω (4 * n + 16) 4 n := by
  have hdeg : (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 :=
    le_trans (td_sub_le _ _) (max_le (td_X_le _) (le_trans (td_C_le _) (by omega)))
  have heq : {z : Fin n → ℝ | z i = c} =
      {x : Fin n → ℝ | MvPolynomial.eval x (MvPolynomial.X i - MvPolynomial.C c :
        MvPolynomial (Fin n) ℝ) = 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact mem_mono (S.hyp n _) _ _ (by omega) (by omega)

/-- The intersection of two `Ω`-sets (with possibly different formats and degrees). -/
theorem inter_two_mem {n F D F' D' : ℕ} {A B : Set (Fin n → ℝ)} (hA : A ∈ S.Ω F D n)
    (hB : B ∈ S.Ω F' D' n) : A ∩ B ∈ S.Ω (max F F' + 1) (D + D') n := by
  have h1 : A ∈ S.Ω (max F F') D n := mem_mono hA _ _ (le_max_left _ _) le_rfl
  have h2 : B ∈ S.Ω (max F F') D' n := mem_mono hB _ _ (le_max_right _ _) le_rfl
  have hinter := S.inter (fun i : Fin 2 => if i = 0 then D else D')
    (fun i : Fin 2 => if i = 0 then A else B) (by
      intro i; fin_cases i
      · simpa using h1
      · simpa using h2)
  rw [show (∑ i : Fin 2, if i = 0 then D else D') = D + D' from by simp [Fin.sum_univ_two]] at hinter
  have hset : (⋂ i : Fin 2, if i = 0 then A else B) = A ∩ B := by
    ext z; simp [Fin.forall_fin_two]
  rwa [hset] at hinter


end Work.WilkiesH.Strat
