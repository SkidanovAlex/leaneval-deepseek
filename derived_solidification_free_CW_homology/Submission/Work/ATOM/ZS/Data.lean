import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.ZS.Level
import Submission.Work.ATOM.exists_level_enumeration

/-!
# AREA ATOM / `ℤ[S]`: the level data of an infinite light profinite set

This file packages the combinatorial input of `NOTES_LEAD_solid_gaps1.md` §3.1 (proved as
`Work.ATOM.exists_level_enumeration` on top of the tower `Work.ATOM.sig`/`Work.ATOM.e` of
`Submission/Work/ATOM/ZS/Level.lean`) into a structure `Work.ATOM.LevelData S`, and records the
elementary consequences used by the rest of the area.

* `s₀` is a base point fixed by all idempotents `e_n`;
* `A n = range (e S n)` is the finite image of `e_n`, `D = ⋃ n, A n` (`Work.ATOM.levelSet`);
* `lv y` is the least `n` with `y ∈ A n` (for `y ∈ D`);
* `a : ℕ → ↥S` is an enumeration of `D \ {s₀}` with inverse `idx`;
* `n(j) := lv (a j)` is the "level" of the `j`-th enumerated point.

The maps `ψ`, `φ_P`, `β`, `ẽ` of §3.1, and the null sequence `g : P ⟶ ℤ[S]`, are built from this
data in `Submission/Work/ATOM/ZS/Topo/`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

namespace Work.ATOM

/-- The level structure of `NOTES_LEAD_solid_gaps1.md` §3.1: a base point, the level function and
an enumeration of the set of "new points" of an infinite light profinite set. -/
structure LevelData (S : LightProfinite.{0}) where
  /-- the base point, fixed by every idempotent `e_n` -/
  s₀ : ↥S
  /-- the level of a point -/
  lv : ↥S → ℕ
  /-- the enumeration of `D \ {s₀}` -/
  a : ℕ → ↥S
  /-- the inverse of the enumeration -/
  idx : ↥S → ℕ
  e_fix : ∀ n, e S n s₀ = s₀
  mem_A0 : s₀ ∈ A S 0
  A_mono : ∀ n, A S n ⊆ A S (n + 1)
  e_fix_A : ∀ n y, y ∈ A S n → e S n y = y
  e_comp : ∀ n m, e S n ≫ e S m = e S (min n m)
  lv_mem : ∀ y, y ∈ (⋃ n, A S n) → y ∈ A S (lv y)
  lv_min : ∀ y, y ∈ (⋃ n, A S n) → ∀ m, m < lv y → y ∉ A S m
  a_inj : Function.Injective a
  a_range : Set.range a = (⋃ n, A S n) \ {s₀}
  idx_a : ∀ j, idx (a j) = j
  a_idx : ∀ y, ∀ _ : y ∈ (⋃ n, A S n) \ {s₀}, a (idx y) = y
  e_lv_a : ∀ j, e S (lv (a j)) (a j) = a j

theorem nonempty_levelData (S : LightProfinite.{0}) [Infinite S] : Nonempty (LevelData S) := by
  obtain ⟨s₀, lv, a, idx, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    exists_level_enumeration S
  have h4' : ∀ n y, y ∈ A S n → e S n y = y := by
    intro n y hy
    obtain ⟨z, rfl⟩ := hy
    simp only [e_apply]
    exact h4 n _ ⟨S.proj n z, rfl⟩
  exact ⟨⟨s₀, lv, a, idx, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

/-- The chosen level data of an infinite light profinite set. -/
noncomputable def levelData (S : LightProfinite.{0}) [Infinite S] : LevelData S :=
  Classical.choice (nonempty_levelData S)

/-- `D = ⋃ n, A n`, the set of points of finite level. -/
def levelSet (S : LightProfinite.{0}) : Set ↥S := ⋃ n, A S n

/-- `D \ {s₀}`, the set enumerated by `a`. -/
def levelSet' (S : LightProfinite.{0}) [Infinite S] : Set ↥S :=
  levelSet S \ {(levelData S).s₀}

/-- The level of the `j`-th enumerated point: `n(j) = lv (a j)`. -/
def lvl (S : LightProfinite.{0}) [Infinite S] (j : ℕ) : ℕ :=
  (levelData S).lv ((levelData S).a j)

variable {S : LightProfinite.{0}}

section Consequences

variable [Infinite S]

lemma levelData_range : Set.range (levelData S).a = levelSet' S :=
  (levelData S).a_range

lemma levelData_a_inj : Function.Injective (levelData S).a := (levelData S).a_inj

lemma levelData_a_mem (j : ℕ) : (levelData S).a j ∈ levelSet S := by
  have h : (levelData S).a j ∈ levelSet' S := levelData_range (S := S) ▸ Set.mem_range_self j
  rw [levelSet', Set.mem_diff] at h
  exact h.1

lemma levelData_a_ne (j : ℕ) : (levelData S).a j ≠ (levelData S).s₀ := by
  have h : (levelData S).a j ∈ levelSet' S := levelData_range (S := S) ▸ Set.mem_range_self j
  rw [levelSet', Set.mem_sdiff, Set.mem_singleton_iff] at h
  exact h.2

/-- `y ∈ D` embeds into the corresponding finite component. -/
lemma levelData_mem_range_sig {y : ↥S} (hy : y ∈ levelSet S) :
    y ∈ Set.range (sig S ((levelData S).lv y)) := by
  obtain ⟨z, hz⟩ := (levelData S).lv_mem y hy
  exact ⟨S.proj _ z, (e_apply S _ z).symm.trans hz⟩

/-- Every point of `D` is fixed by the idempotent of its own level. -/
lemma levelData_e_lv (y : ↥S) (hy : y ∈ levelSet S) : e S ((levelData S).lv y) y = y :=
  (levelData S).e_fix_A _ y ((levelData S).lv_mem y hy)

/-- The finality of the level: if `y ∈ A m` then `lv y ≤ m`. -/
lemma levelData_lv_le {y : ↥S} {m : ℕ} (hy : y ∈ A S m) : (levelData S).lv y ≤ m := by
  by_contra h
  exact (levelData S).lv_min y (Set.mem_iUnion.mpr ⟨m, hy⟩) m (by omega) hy

/-- `y ∈ D` iff `y` is enumerated by `a` (i.e. `y ∈ range a`) or `y = s₀`. -/
lemma levelData_mem_levelSet_iff (y : ↥S) :
    y ∈ levelSet S ↔ y ∈ Set.range (levelData S).a ∨ y = (levelData S).s₀ := by
  constructor
  · intro hy
    by_cases h : y = (levelData S).s₀
    · exact Or.inr h
    · refine Or.inl ?_
      have hy' : y ∈ levelSet' S := by
        simp only [levelSet', Set.mem_sdiff, Set.mem_singleton_iff]
        exact ⟨hy, h⟩
      exact levelData_range (S := S) ▸ hy'
  · rintro (⟨j, rfl⟩ | rfl)
    · exact levelData_a_mem j
    · exact Set.mem_iUnion.mpr ⟨0, (levelData S).mem_A0⟩

/-- The inverse property of `idx`: for `y ∈ D \ {s₀}`, `a (idx y) = y`. -/
lemma levelData_a_idx (y : ↥S) (hy : y ∈ levelSet' S) :
    (levelData S).a ((levelData S).idx y) = y :=
  (levelData S).a_idx y hy

/-- The level sets are finite: only finitely many `j` have `n(j) = k`. -/
lemma levelData_finite_level (k : ℕ) :
    {j : ℕ | (levelData S).lv ((levelData S).a j) = k}.Finite := by
  haveI : Finite ↥(S.component k) :=
    inferInstanceAs (Finite (FintypeCat.toLightProfinite.obj (S.fintypeDiagram.obj ⟨k⟩)))
  have hfin : (Set.range (sig S k)).Finite := Set.finite_range _
  refine (hfin.preimage (levelData S).a_inj.injOn).subset ?_
  intro j hj
  rw [Set.mem_setOf_eq] at hj
  have h := levelData_mem_range_sig (S := S) (levelData_a_mem j)
  rwa [hj] at h

/-- `n(j) → ∞`: only finitely many `j` have level `< N`. -/
lemma levelData_finite_level_lt (N : ℕ) :
    {j : ℕ | (levelData S).lv ((levelData S).a j) < N}.Finite := by
  rw [show {j : ℕ | (levelData S).lv ((levelData S).a j) < N} =
      ⋃ k ∈ Set.Iio N, {j : ℕ | (levelData S).lv ((levelData S).a j) = k} by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iio]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨k, hk, hkj⟩ => hkj ▸ hk⟩]
  exact Set.Finite.biUnion (Set.finite_Iio N) fun k _ => levelData_finite_level k

lemma levelData_lvl (j : ℕ) : (levelData S).lv ((levelData S).a j) = lvl S j := rfl

/-- `e_{n(j)}` fixes `a_j`. -/
lemma levelData_e_lvl_a (j : ℕ) : e S (lvl S j) ((levelData S).a j) = (levelData S).a j :=
  (levelData S).e_lv_a j

/-- If `e_k x = a_j` and `n(j) = k` then `idx (e_k x) = j`. -/
lemma levelData_idx_eq (j : ℕ) {x : ↥S} (hx : e S (lvl S j) x = (levelData S).a j) :
    (levelData S).idx (e S (lvl S j) x) = j := by
  rw [hx, (levelData S).idx_a j]

end Consequences

end Work.ATOM
