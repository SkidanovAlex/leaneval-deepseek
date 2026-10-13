/-
  WilC4g : the `∅`-definable graph of a *singleton-valued* `LRc`-definable family, uniformly in the
  parameters.

  Given an `LRc`-formula `φ` in `n + 2` free variables, split as `Fin n ⊕ Fin 2` (the `n`
  "parameter" variables come first, then the two variables `y`, `x` in this order), this file
  produces a single `∅`-definable set `Y ⊆ M^{n+2}` whose fibre over `(x, c)` is exactly the
  unique `y` with `φ(c, y, x)`, provided such a `y` is unique.

  The tuple of `Y` is indexed by `Fin (n+2)` with the layout
  `Fin.cons x (Fin.cons y c)`, i.e. coordinate `0` is `x`, coordinate `1` is `y` and
  coordinates `2 + i` are the parameters `c i`.  Thus `Y` is the `∅`-definable *graph* of the
  partial function `(x, c) ↦ y` implicitly defined by `φ`.

  The construction is purely syntactic: `Y` is defined by the formula

    `φ(c, w 1, w 0) ∧ ∀ y', φ(c, y', w 0) → y' = w 1`,

  which mentions `φ` but no parameters of `M`.  The formal work is the reindexing between
  `Fin n ⊕ Fin 2` and `Fin (n+2)` (`sig1`, `sig2` below) together with the finite universal
  quantifier `Set.Definable.forall_of_finite`.
-/
import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4g

open FirstOrder FirstOrder.Language

/-- Reindexing of the `(n + 2)`-variable context `Fin (n+2)` (layout `x, y, c`) onto the
`Fin n ⊕ Fin 2` context of an `LRc`-formula, the `n` parameters coming from coordinates `2, …, n+1`
and the two formula variables being `y` (coordinate `1`) and `x` (coordinate `0`). -/
def sig1 (n : ℕ) : Fin n ⊕ Fin 2 → Fin (n + 2) :=
  Sum.elim (fun i => Fin.succ (Fin.succ i)) (fun j => if j = 0 then 1 else 0)

/-- Reindexing of the `(n + 2) ⊕ 1`-variable context `Fin (n+2) ⊕ Fin 1` (layout `x, y, c, y'`)
onto the `Fin n ⊕ Fin 2` context of an `LRc`-formula: the `n` parameters come from the `Fin (n+2)`
part, the two formula variables are `y'` (the `Fin 1` part) and `x` (coordinate `0` of `Fin (n+2)`).

This is `sig1` with the formula variable `y` replaced by the extra quantified variable `y'`. -/
def sig2 (n : ℕ) : Fin n ⊕ Fin 2 → Fin (n + 2) ⊕ Fin 1 :=
  Sum.elim (fun i => Sum.inl (Fin.succ (Fin.succ i)))
    (fun j => if j = 0 then Sum.inr 0 else Sum.inl 0)

/-- Universal quantification over the (one-element) index type `Fin 1` is ordinary universal
quantification: `∀ u : Fin 1 → α, P (u 0) ↔ ∀ a, P a`. -/
lemma forall_fin_one {α : Type} (P : α → Prop) :
    (∀ u : Fin 1 → α, P (u 0)) ↔ (∀ a : α, P a) :=
  ⟨fun h a => h (fun _ => a), fun h u => h (u 0)⟩

/-- Realisation of `φ` after reindexing along `sig1`. -/
lemma cons_comp_sig1 {M : Type} {n : ℕ} (c' : Fin n → M) (x y : M) :
    (Fin.cons x (Fin.cons y c') : Fin (n + 2) → M) ∘ sig1 n = Sum.elim c' ![y, x] := by
  funext i
  rcases i with i | j
  · simp [sig1]
  · fin_cases j <;> simp [sig1]

/-- Realisation of `φ` after reindexing along `sig2`, with one extra free variable `u`. -/
lemma sumelim_comp_sig2 {M : Type} {n : ℕ} (v : Fin (n + 2) → M) (u : Fin 1 → M) :
    (Sum.elim v u) ∘ sig2 n =
      Sum.elim (fun i : Fin n => v (Fin.succ (Fin.succ i))) ![u 0, v 0] := by
  funext i
  rcases i with i | j
  · simp [sig2]
  · fin_cases j <;> simp [sig2]

/-- The parameter block of `Fin.cons x (Fin.cons y c')` is `c'`. -/
lemma cons_tail {M : Type} {n : ℕ} (c' : Fin n → M) (x y : M) :
    (fun i : Fin n => (Fin.cons x (Fin.cons y c') : Fin (n + 2) → M) (Fin.succ (Fin.succ i))) =
      c' := by
  funext i
  simp

/-- The `y`-coordinate of `Fin.cons x (Fin.cons y c')` is `y`. -/
lemma cons_one_eq {M : Type} {n : ℕ} (c' : Fin n → M) (x y : M) :
    (Fin.cons x (Fin.cons y c') : Fin (n + 2) → M) 1 = y := by
  simp

/-- **The `∅`-definable graph of a singleton-valued `LRc`-definable family.**

For every `LRc`-formula `φ` (free variables `Fin n ⊕ Fin 2`, the `Fin 2` block being `y, x` in
this order) the set
`Y = {w | φ(φtail w, w 1, w 0) ∧ ∀ y', φ(φtail w, y', w 0) → y' = w 1}`
is `∅`-definable; it is single-valued in the `y`-coordinate for every choice of parameters, and
over the fixed parameters `c` its fibre is exactly the unique `y` with `φ(c, y, x)`.

The set `Y` does not depend on `c`: the given clause with `c` is obtained by evaluating the
`∅`-definable formula at the parameters `c`. -/
theorem exists_ulpm_of_formula {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {n : ℕ} (φ : WilkiesDesign.CG.LRc.Formula (Fin n ⊕ Fin 2)) (c : Fin n → M) : ∃ Y : Set (Fin (n + 2) → M), (∅ : Set M).Definable WilkiesDesign.CG.LRc Y ∧ (∀ (c' : Fin n → M) (x y y' : M), Fin.cons x (Fin.cons y c') ∈ Y → Fin.cons x (Fin.cons y' c') ∈ Y → y = y') ∧ (∀ x y : M, Fin.cons x (Fin.cons y c) ∈ Y ↔ (φ.Realize (Sum.elim c ![y, x]) ∧ ∀ y' : M, φ.Realize (Sum.elim c ![y', x]) → y' = y)) := by
  classical
  -- the set defined by `φ` itself is `∅`-definable
  have hφ : (∅ : Set M).Definable WilkiesDesign.CG.LRc (Set.ofPred φ.Realize) :=
    Set.empty_definable_iff.mpr ⟨φ, rfl⟩
  -- the `x`- and the `y`-coordinate of the tuple
  have hDec : (∅ : Set M).Definable WilkiesDesign.CG.LRc
      {w : Fin (n + 2) → M | φ.Realize (w ∘ sig1 n)} := by
    convert hφ.preimage_comp (sig1 n) using 1
    ext w
    simp [Set.mem_ofPred_eq]
  -- the relation `y' = y` on the extended context `Fin (n+2) ⊕ Fin 1`
  have hB' : (∅ : Set M).Definable WilkiesDesign.CG.LRc
      {g : Fin (n + 2) ⊕ Fin 1 → M | g (Sum.inr 0) = g (Sum.inl 1)} := by
    refine Set.DefinableFun.ofPred_eq (A := (∅ : Set M)) (L := WilkiesDesign.CG.LRc)
      (f := fun g : Fin (n + 2) ⊕ Fin 1 → M => g (Sum.inr 0))
      (g := fun g : Fin (n + 2) ⊕ Fin 1 → M => g (Sum.inl 1)) ?_ ?_
    · exact Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set M))
        (α := Fin (n + 2) ⊕ Fin 1) (i := Sum.inr 0)
    · exact Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := (∅ : Set M))
        (α := Fin (n + 2) ⊕ Fin 1) (i := Sum.inl 1)
  -- the relation `φ(c, y', x)` on the extended context
  have hA' : (∅ : Set M).Definable WilkiesDesign.CG.LRc
      {g : Fin (n + 2) ⊕ Fin 1 → M | φ.Realize (g ∘ sig2 n)} := by
    convert hφ.preimage_comp (sig2 n) using 1
    ext g
    simp [Set.mem_ofPred_eq]
  -- `φ(c, y', x) → y' = y`
  have hS : (∅ : Set M).Definable WilkiesDesign.CG.LRc
      (({g : Fin (n + 2) ⊕ Fin 1 → M | φ.Realize (g ∘ sig2 n)})ᶜ ∪
        {g : Fin (n + 2) ⊕ Fin 1 → M | g (Sum.inr 0) = g (Sum.inl 1)}) :=
    hA'.compl.union hB'
  -- quantify `y'` (`Fin 1 → M`) universally
  have hUniq : (∅ : Set M).Definable WilkiesDesign.CG.LRc
      {w : Fin (n + 2) → M | ∀ u : Fin 1 → M,
        φ.Realize ((Sum.elim w u) ∘ sig2 n) → u 0 = w 1} := by
    have h := Set.Definable.forall_of_finite (A := (∅ : Set M)) (L := WilkiesDesign.CG.LRc)
      (α := Fin (n + 2)) (β := Fin 1) hS
    convert h using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
      Sum.elim_inr, Sum.elim_inl, imp_iff_not_or]
  refine ⟨{w : Fin (n + 2) → M | φ.Realize (w ∘ sig1 n) ∧
      (∀ u : Fin 1 → M, φ.Realize ((Sum.elim w u) ∘ sig2 n) → u 0 = w 1)}, ?_, ?_, ?_⟩
  · exact hDec.inter hUniq
  · -- single-valuedness in the `y`-coordinate, for every parameter tuple
    intro c' x y y' h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    have h2a' : φ.Realize (Sum.elim c' ![y', x]) := by
      rw [cons_comp_sig1] at h2a
      exact h2a
    have hkey := h1b (fun _ : Fin 1 => y')
    rw [sumelim_comp_sig2] at hkey
    simp only [cons_tail, Fin.cons_zero, cons_one_eq] at hkey
    exact (hkey h2a').symm
  · -- the fibre over the fixed parameters `c`
    intro x y
    simp only [Set.mem_ofPred_eq]
    have h1 : φ.Realize ((Fin.cons x (Fin.cons y c) : Fin (n + 2) → M) ∘ sig1 n) ↔
        φ.Realize (Sum.elim c ![y, x]) := by
      rw [cons_comp_sig1]
    have h2 : (∀ u : Fin 1 → M,
          φ.Realize ((Sum.elim (Fin.cons x (Fin.cons y c) : Fin (n + 2) → M) u) ∘ sig2 n) →
            u 0 = (Fin.cons x (Fin.cons y c) : Fin (n + 2) → M) 1)
        ↔ (∀ y' : M, φ.Realize (Sum.elim c ![y', x]) → y' = y) := by
      have hQ : ∀ u : Fin 1 → M,
          (φ.Realize ((Sum.elim (Fin.cons x (Fin.cons y c) : Fin (n + 2) → M) u) ∘ sig2 n) →
              u 0 = (Fin.cons x (Fin.cons y c) : Fin (n + 2) → M) 1)
            ↔ (φ.Realize (Sum.elim c ![u 0, x]) → u 0 = y) := by
        intro u
        rw [sumelim_comp_sig2]
        simp only [cons_tail, Fin.cons_zero, cons_one_eq]
      rw [forall_congr' hQ]
      exact forall_fin_one (fun y' : M => φ.Realize (Sum.elim c ![y', x]) → y' = y)
    exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

end Work.WilC4g
