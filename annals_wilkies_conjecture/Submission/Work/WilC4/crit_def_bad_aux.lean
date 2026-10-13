/-
  WilC4/crit_def_bad_aux : the elementary `LRc`-definability primitives used by
  `Work.WilC4.crit_def_bad`.

  The only things that make `LRc`-definability of the one-sided "bad" families non-formal are
    * the fact that the order of `ℝ` is `∅`-definable (via `x ≤ y ↔ ∃ z, x + z*z = y`);
    * the substitution of coordinates (an argument slot, a value slot and a parameter tail) into a
      definable set `Y ⊆ ℝ^{k+2}`, which is a plain reindexing (`GrSub`/`GrSub_definable`);
    * the elementary coordinate sets `{u | c < u i}`, `{u | u i = u j + u l}`,
      `{u | u i < u j + u l}`, `{u | u i + u j ≤ u l}`.

  `shape_lemma` packages the quantifier bookkeeping shared by all four one-sided bad families:
  starting from a definable "outer" set `O ⊆ ℝ^{k+1+3}` (carrying the variables `(v, ε, δ, y)`)
  and a definable "bad" set `B ⊆ ℝ^{k+1+3+2}` (carrying `(v, ε, δ, y, t, w)`), it produces the
  set of `v` for which some `(ε,δ,y)` satisfies `O` and *no* `(t,w)` satisfies `B`.
-/
import Mathlib
import Submission.Work.WilC4.CritDefs
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC2.bnd_definable_alt
import Submission.Work.WilC2.finite_definable_singleton

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc TR rexpL)

variable {k : ℕ}

/-! ## 1. The order of `ℝ` is `∅`-definable -/

lemma real_sq (x : ℝ) (hx : 0 ≤ x) : ∃ z : ℝ, x = z * z :=
  ⟨Real.sqrt x, by rw [← pow_two]; exact (Real.sq_sqrt hx).symm⟩

lemma real_definable_le {α : Type*} (i j : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i ≤ v j} :=
  WilC2.definable_le (A := (∅ : Set ℝ)) real_sq i j

lemma real_definable_lt {α : Type*} (i j : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i < v j} :=
  WilC2.definable_lt (A := (∅ : Set ℝ)) real_sq i j

/-! ## 2. Substituting coordinates into a definable set -/

lemma comp_cons_cons {ρ : Type} (u : ρ → ℝ) (a b : ρ) (ι : Fin k → ρ) :
    u ∘ (Fin.cons a (Fin.cons b ι)) = Fin.cons (u a) (Fin.cons (u b) (u ∘ ι)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

/-- `GrSub Y emb a b` is the set of `u : ρ → ℝ` for which the tuple
`(u a, u b, u ∘ emb ∘ Fin.succ)` lies in `Y`: the argument `u a`, the value `u b` and the
parameter tail read off along `emb`. -/
def GrSub (Y : Set (Fin (k+2) → ℝ)) {ρ : Type} (emb : Fin (k+1) → ρ) (a b : ρ) :
    Set (ρ → ℝ) :=
  {u | Fin.cons (u a) (Fin.cons (u b) (u ∘ (emb ∘ Fin.succ))) ∈ Y}

theorem GrSub_definable {Y : Set (Fin (k+2) → ℝ)} {ρ : Type}
    (hY : (∅ : Set ℝ).Definable LRc Y) (emb : Fin (k+1) → ρ) (a b : ρ) :
    (∅ : Set ℝ).Definable LRc (GrSub Y emb a b) := by
  have h := hY.preimage_comp (Fin.cons a (Fin.cons b (emb ∘ Fin.succ)))
  have hset : GrSub Y emb a b =
      (fun g : ρ → ℝ => g ∘ (Fin.cons a (Fin.cons b (emb ∘ Fin.succ)))) ⁻¹' Y := by
    ext u
    simp only [Set.mem_preimage, GrSub, Set.mem_ofPred_eq, comp_cons_cons]
  rw [hset]; exact h

/-! ## 3. Elementary coordinate sets -/

/-- `{u | c < u i}`. -/
theorem definable_lt_const {ρ : Type} (c : ℝ) (i : ρ) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | c < u i} := by
  have h1 : (∅ : Set ℝ).Definable LRc {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) = c} :=
    empty_definable_coord_eq (α := ρ ⊕ Fin 1) (Sum.inr 0) c
  have h2 : (∅ : Set ℝ).Definable LRc {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) < x (Sum.inl i)} :=
    real_definable_lt (Sum.inr 0) (Sum.inl i)
  have h := (h1.inter h2).exists_of_finite (α := ρ) (β := Fin 1)
  have hset : {v : ρ → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈
        ({x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) = c} ∩
          {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) < x (Sum.inl i)})}
      = {u : ρ → ℝ | c < u i} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_setOf_eq, Sum.elim_inl,
      Sum.elim_inr]
    constructor
    · rintro ⟨u0, h1, h2⟩; rw [← h1]; exact h2
    · intro hv; exact ⟨fun _ => c, rfl, hv⟩
  rw [hset] at h; exact h

/-- The ring formula `v 0 = v 1 + v 2`. -/
def eqAddF : Language.ring.Formula (Fin 3) :=
  Term.bdEqual (Term.var (Sum.inl (0 : Fin 3)))
    (Term.var (Sum.inl (1 : Fin 3)) + Term.var (Sum.inl (2 : Fin 3)))

theorem eqAddF_realize {M : Type} [Add M] [Mul M] [Neg M] [One M] [Zero M]
    [Ring.CompatibleRing M]
    (v : Fin 3 → M) : eqAddF.Realize v ↔ v 0 = v 1 + v 2 := by
  rw [eqAddF, Formula.Realize, BoundedFormula.realize_bdEqual]
  simp only [Ring.realize_add, Term.realize_var, Sum.elim_inl]

/-- `{u | u i = u j + u l}`. -/
theorem definable_eq_add {ρ : Type} (i j l : ρ) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | u i = u j + u l} := by
  rw [Set.empty_definable_iff]
  refine ⟨WilC2.liftR ![i, j, l] eqAddF, ?_⟩
  ext u
  simp only [Set.mem_ofPred_eq]
  have hcomp : (u ∘ ![i, j, l]) = ![u i, u j, u l] := by
    funext x; fin_cases x <;> rfl
  rw [WilC2.liftR_realize ![i, j, l] eqAddF u, hcomp, eqAddF_realize]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `{u | u i < u j + u l}`. -/
theorem definable_lt_add {ρ : Type} (i j l : ρ) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | u i < u j + u l} := by
  have h1 : (∅ : Set ℝ).Definable LRc
      {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) = x (Sum.inl j) + x (Sum.inl l)} :=
    definable_eq_add (Sum.inr 0) (Sum.inl j) (Sum.inl l)
  have h2 : (∅ : Set ℝ).Definable LRc
      {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inl i) < x (Sum.inr 0)} :=
    real_definable_lt (Sum.inl i) (Sum.inr 0)
  have h := (h1.inter h2).exists_of_finite (α := ρ) (β := Fin 1)
  have hset : {v : ρ → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈
        ({x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) = x (Sum.inl j) + x (Sum.inl l)} ∩
          {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inl i) < x (Sum.inr 0)})}
      = {u : ρ → ℝ | u i < u j + u l} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_setOf_eq, Sum.elim_inl,
      Sum.elim_inr]
    constructor
    · rintro ⟨u0, h1, h2⟩; rw [← h1]; exact h2
    · intro hv; exact ⟨fun _ => v j + v l, rfl, hv⟩
  rw [hset] at h; exact h

/-- `{u | u i + u j ≤ u l}`. -/
theorem definable_le_sum {ρ : Type} (i j l : ρ) :
    (∅ : Set ℝ).Definable LRc {u : ρ → ℝ | u i + u j ≤ u l} := by
  have h1 : (∅ : Set ℝ).Definable LRc
      {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) = x (Sum.inl i) + x (Sum.inl j)} :=
    definable_eq_add (Sum.inr 0) (Sum.inl i) (Sum.inl j)
  have h2 : (∅ : Set ℝ).Definable LRc
      {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) ≤ x (Sum.inl l)} :=
    real_definable_le (Sum.inr 0) (Sum.inl l)
  have h := (h1.inter h2).exists_of_finite (α := ρ) (β := Fin 1)
  have hset : {v : ρ → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈
        ({x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) = x (Sum.inl i) + x (Sum.inl j)} ∩
          {x : ρ ⊕ Fin 1 → ℝ | x (Sum.inr 0) ≤ x (Sum.inl l)})}
      = {u : ρ → ℝ | u i + u j ≤ u l} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_setOf_eq, Sum.elim_inl,
      Sum.elim_inr]
    constructor
    · rintro ⟨u0, h1, h2⟩; rw [← h1]; exact h2
    · intro hv; exact ⟨fun _ => v i + v j, rfl, hv⟩
  rw [hset] at h; exact h

/-! ## 4. The two parameter blocks -/

/-- The parameter block `(v, ε, δ, y)`. -/
abbrev ρ3 (k : ℕ) := Fin (k+1) ⊕ Fin 3

/-- The parameter block `(v, ε, δ, y, t, w)`. -/
abbrev ρR (k : ℕ) := ρ3 k ⊕ Fin 2

/-- The `v`-block inside `ρ3`. -/
abbrev e3 : Fin (k+1) → ρ3 k := Sum.inl

/-- The `v`-block inside `ρR`. -/
abbrev eR : Fin (k+1) → ρR k := fun i => Sum.inl (Sum.inl i)

/-- `ε` inside `ρ3`. -/
abbrev eps3 : ρ3 k := Sum.inr 0
/-- `δ` inside `ρ3`. -/
abbrev del3 : ρ3 k := Sum.inr 1
/-- `y` inside `ρ3`. -/
abbrev y3 : ρ3 k := Sum.inr 2
/-- The argument `v 0` inside `ρ3`. -/
abbrev v03 : ρ3 k := Sum.inl 0

/-- `ε` inside `ρR`. -/
abbrev epsR : ρR k := Sum.inl (Sum.inr 0)
/-- `δ` inside `ρR`. -/
abbrev delR : ρR k := Sum.inl (Sum.inr 1)
/-- `y` inside `ρR`. -/
abbrev yR : ρR k := Sum.inl (Sum.inr 2)
/-- The argument `v 0` inside `ρR`. -/
abbrev v0R : ρR k := Sum.inl (Sum.inl 0)
/-- `t` inside `ρR`. -/
abbrev tR : ρR k := Sum.inr 0
/-- `w` inside `ρR`. -/
abbrev wR : ρR k := Sum.inr 1

/-! ## 5. The shared quantifier shape -/

/-- **Shared shape.**  Given a definable `O ⊆ ℝ^{k+1+3}` (the "outer" conditions on
`(v, ε, δ, y)`) and a definable `B ⊆ ℝ^{k+1+3+2}` (the "bad" conditions on
`(v, ε, δ, y, t, w)`), the set of `v` for which some `(ε,δ,y)` satisfies `O` and no `(t,w)`
satisfies `B` is `∅`-definable. -/
theorem shape_lemma {O : Set (ρ3 k → ℝ)} {B : Set (ρR k → ℝ)}
    (hO : (∅ : Set ℝ).Definable LRc O) (hB : (∅ : Set ℝ).Definable LRc B) :
    (∅ : Set ℝ).Definable LRc
      {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ O ∧
        Sum.elim v u ∉ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' B)} := by
  have h1 : (∅ : Set ℝ).Definable LRc
      (O ∩ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' B)ᶜ) :=
    hO.inter (hB.image_comp (Sum.inl : ρ3 k → ρR k)).compl
  have h2 := h1.exists_of_finite (α := Fin (k+1)) (β := Fin 3)
  have hset : {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈
        (O ∩ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' B)ᶜ)}
      = {v : Fin (k+1) → ℝ | ∃ u : Fin 3 → ℝ, Sum.elim v u ∈ O ∧
          Sum.elim v u ∉ ((fun g : ρR k → ℝ => g ∘ (Sum.inl : ρ3 k → ρR k)) '' B)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  rw [hset] at h2; exact h2

/-! ## 6. The four one-sided "bad" loci as named sets -/

/-- `RUpart Y`: some `(ε,δ,y)` with `0<ε`, `0<δ`, `(x,y) ∈ Y` and all values of the fibre on
`(x, x+δ)` at least `y+ε`. -/
def RUpart (Y : Set (Fin (k+2) → ℝ)) : Set (Fin (k+1) → ℝ) :=
  {v | ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 < t → t < v 0 + δ → ∀ w : ℝ, CGr Y (tup v) t w → y + ε ≤ w}

/-- `RDpart Y`: some `(ε,δ,y)` with `0<ε`, `0<δ`, `(x,y) ∈ Y` and all values of the fibre on
`(x, x+δ)` at most `y-ε`. -/
def RDpart (Y : Set (Fin (k+2) → ℝ)) : Set (Fin (k+1) → ℝ) :=
  {v | ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 < t → t < v 0 + δ → ∀ w : ℝ, CGr Y (tup v) t w → w + ε ≤ y}

/-- `LUpart Y`: some `(ε,δ,y)` with `0<ε`, `0<δ`, `(x,y) ∈ Y` and all values of the fibre on
`(x-δ, x)` at least `y+ε`. -/
def LUpart (Y : Set (Fin (k+2) → ℝ)) : Set (Fin (k+1) → ℝ) :=
  {v | ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 - δ < t → t < v 0 → ∀ w : ℝ, CGr Y (tup v) t w → y + ε ≤ w}

/-- `LDpart Y`: some `(ε,δ,y)` with `0<ε`, `0<δ`, `(x,y) ∈ Y` and all values of the fibre on
`(x-δ, x)` at most `y-ε`. -/
def LDpart (Y : Set (Fin (k+2) → ℝ)) : Set (Fin (k+1) → ℝ) :=
  {v | ∃ ε δ y : ℝ, 0 < ε ∧ 0 < δ ∧ CGr Y (tup v) (v 0) y ∧
    ∀ t : ℝ, v 0 - δ < t → t < v 0 → ∀ w : ℝ, CGr Y (tup v) t w → w + ε ≤ y}

end Work.WilC4
