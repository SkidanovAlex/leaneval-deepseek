/-
  WilC4/crit_germ_oc2 : the fibres of the parametric relations `PMonoLA Y`, `PMonoHA Y`
  (`Y ⊆ ℝ^{k+2}` a `∅`-definable family of partial functions) are finite unions of
  order-convex sets.

  The proof is a reduction to `Work.WilC4.monoLHset_ordConnected`, which already performs the
  o-minimality step: from the `∅`-definability of `MonoLA Y'`, `MonoHA Y'` for a single
  partial function `Y' ⊆ ℝ²`, it produces, for every `a : ℝ`, `MonoLset Y' a` and
  `MonoHset Y' a` as finite unions of order-convex sets.

  So it suffices to know that the individual fibre relations `MonoLA (Cfib Y c)` and
  `MonoHA (Cfib Y c)` are `∅`-definable.  Two steps:

  * `MonoLA (Cfib Y c) = Pfibre (PMonoLA Y) c` (and the same for `H`); this is pure
    index bookkeeping: `PMonoLA Y` is the set of `v : Fin (k+2) → ℝ` whose first two
    coordinates form a point of `MonoLA` for the fibre at `Fin.tail (Fin.tail v)`, so
    substituting the parameters `c` recovers `MonoLA (Cfib Y c)`.
  * `Pfibre Y c` is `∅`-definable whenever `Y` is (`paramFibre_definable_aux`): writing
    `τ : Fin (n+2) → Fin 2 ⊕ Fin n` for the index map `0 ↦ inl 0`, `1 ↦ inl 1`,
    `j+2 ↦ inr j`, the set `Pfibre Y c` is the projection, along the `Fin n` parameters, of
    `{u : (Fin 2 ⊕ Fin n) → ℝ | u ∘ τ ∈ Y ∧ ∀ j, u (inr j) = c j}`.

  All the vocabulary used here (`Cfib`, `Pfibre`, `PMonoLA`, `PMonoHA`, `MonoLA`, `MonoHA`,
  `MonoLset`, `MonoHset`) is defined in the sibling modules `CritDefs`, `ParamMonoDefs` and
  `monoDefs`.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC4.monoLHset_ordConnected
import Submission.Work.WilC2.fibre_definable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The index map `Fin (n+2) → Fin 2 ⊕ Fin n`

`cgτ n` sends `0 ↦ Sum.inl 0`, `1 ↦ Sum.inl 1` and `j+2 ↦ Sum.inr j`; it is the reindexing
along which `Pfibre` is defined (the `Fin 2` summand carries the `(x, y)` point, the `Fin n`
summand the parameters). -/
def cgτ (n : ℕ) : Fin (n + 2) → Fin 2 ⊕ Fin n :=
  Fin.cons (Sum.inl 0) (Fin.cons (Sum.inl 1) (fun j : Fin n => Sum.inr j))

/-- Composing a split vector `Sum.elim v c` with `cgτ n` rebuilds the `Fin.cons`-vector
`Fin.cons (v 0) (Fin.cons (v 1) c)` whose first two coordinates are `v` and whose remaining
coordinates are `c`. -/
lemma cgτ_sumElim (n : ℕ) (v : Fin 2 → ℝ) (c : Fin n → ℝ) :
    Sum.elim v c ∘ cgτ n = Fin.cons (v 0) (Fin.cons (v 1) c) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => rfl

/-! ## 2. Definability of the individual fibre `Pfibre Y c` -/

/-- If `Y ⊆ ℝ^{n+2}` is `∅`-definable then so is the individual fibre relation
`Pfibre Y c = {(x, y) | (x, y, c) ∈ Y}` at every parameter `c : Fin n → ℝ`.

Indeed `Pfibre Y c` is the existential projection of
`{u : (Fin 2 ⊕ Fin n) → ℝ | u ∘ cgτ n ∈ Y ∧ ∀ j, u (Sum.inr j) = c j}`
along the `Fin n` summand; the first condition is a definable preimage, the coordinate
equations are `∅`-definable because `LRc` names every real, and the projection of a definable
set along finitely many variables is definable (`Definable.exists_of_finite`). -/
lemma paramFibre_definable_aux {n : ℕ} {Y : Set (Fin (n + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (c : Fin n → ℝ) :
    (∅ : Set ℝ).Definable LRc (Pfibre Y c) := by
  have hA : (∅ : Set ℝ).Definable LRc {g : Fin 2 ⊕ Fin n → ℝ | g ∘ cgτ n ∈ Y} :=
    hY.preimage_comp (cgτ n)
  have hB : (∅ : Set ℝ).Definable LRc
      {g : Fin 2 ⊕ Fin n → ℝ | ∀ j : Fin n, g (Sum.inr j) = c j} := by
    rw [← Set.iInter_ofPred]
    exact Set.definable_iInter_of_finite
      (fun j : Fin n => empty_definable_coord_eq (Sum.inr j) (c j))
  have hproj := (hA.inter hB).exists_of_finite (α := Fin 2) (β := Fin n)
  have hset : Pfibre Y c = {v : Fin 2 → ℝ | ∃ u : Fin n → ℝ,
      (Sum.elim v u) ∘ cgτ n ∈ Y ∧ ∀ j : Fin n, u j = c j} := by
    ext v
    constructor
    · intro hv
      simp only [Pfibre, Set.mem_ofPred_eq] at hv
      exact ⟨c, by simpa only [cgτ_sumElim n v c] using hv, fun _ => rfl⟩
    · rintro ⟨u, hu, huc⟩
      have h1 : u = c := funext huc
      rw [h1] at hu
      simp only [Pfibre, Set.mem_ofPred_eq]
      simpa only [cgτ_sumElim n v c] using hu
  rw [hset]
  exact hproj

/-! ## 3. The fibre relations `MonoLA (Cfib Y c)`, `MonoHA (Cfib Y c)` -/

/-- `MonoLA (Cfib Y c)` is exactly the fibre of the parametric relation `PMonoLA Y` over the
parameters `c`. -/
lemma cg_MonoLA_Cfib {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) :
    MonoLA (Cfib Y c) = Pfibre (PMonoLA Y) c := by
  ext w
  simp only [MonoLA, Cfib, CGr, PMonoLA, Pfibre, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.cons_zero, Fin.cons_succ, Fin.cons_one]

/-- `MonoHA (Cfib Y c)` is exactly the fibre of the parametric relation `PMonoHA Y` over the
parameters `c`. -/
lemma cg_MonoHA_Cfib {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) :
    MonoHA (Cfib Y c) = Pfibre (PMonoHA Y) c := by
  ext w
  simp only [MonoHA, Cfib, CGr, PMonoHA, Pfibre, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.cons_zero, Fin.cons_succ, Fin.cons_one]

/-! ## 4. The theorem -/

theorem crit_germ_oc2 {k : ℕ} (hOM : WilkiesDesign.CG.OMinModels)
    (Y : Set (Fin (k + 2) → ℝ))
    (hLA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLA Y))
    (hHA : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHA Y)) :
    (∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoLset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ))) ∧
    (∀ (c : Fin k → ℝ) (a : ℝ), ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧
      MonoHset (Cfib Y c) a = ⋃₀ (s : Set (Set ℝ))) := by
  have hL : ∀ c : Fin k → ℝ, (∅ : Set ℝ).Definable LRc (MonoLA (Cfib Y c)) := by
    intro c
    rw [cg_MonoLA_Cfib]
    exact paramFibre_definable_aux hLA c
  have hH : ∀ c : Fin k → ℝ, (∅ : Set ℝ).Definable LRc (MonoHA (Cfib Y c)) := by
    intro c
    rw [cg_MonoHA_Cfib]
    exact paramFibre_definable_aux hHA c
  constructor
  · intro c a
    exact (monoLHset_ordConnected (hL c) (hH c) hOM).1 a
  · intro c a
    exact (monoLHset_ordConnected (hL c) (hH c) hOM).2 a

end Work.WilC4
