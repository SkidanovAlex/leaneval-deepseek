import Mathlib
import Submission.Work.Peluse.SwapA.genDefs

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapA

/-- The **patch** construction: from two prescribed values `a`, `b` and a function `g` on the
complement of `{ε, ε'}`, rebuild the function `Δ → V` taking the value `a` at `ε`, `b` at `ε'`,
and `g` elsewhere. -/
def evalPairPatch {Δ V : Type} [DecidableEq Δ] (ε ε' : Δ) (a b : V)
    (g : {x : Δ // x ≠ ε ∧ x ≠ ε'} → V) : Δ → V :=
  fun x => if hx : x = ε then a else if hx' : x = ε' then b else g ⟨x, hx, hx'⟩

lemma evalPairPatch_self {Δ V : Type} [DecidableEq Δ] {ε ε' : Δ} {a b : V}
    {g : {x : Δ // x ≠ ε ∧ x ≠ ε'} → V} :
    evalPairPatch ε ε' a b g ε = a := by
  simp [evalPairPatch]

lemma evalPairPatch_self' {Δ V : Type} [DecidableEq Δ] {ε ε' : Δ} (h : ε ≠ ε') {a b : V}
    {g : {x : Δ // x ≠ ε ∧ x ≠ ε'} → V} :
    evalPairPatch ε ε' a b g ε' = b := by
  simp [evalPairPatch, Ne.symm h]

lemma evalPairPatch_of_ne {Δ V : Type} [DecidableEq Δ] {ε ε' : Δ} {a b : V}
    {g : {x : Δ // x ≠ ε ∧ x ≠ ε'} → V} (x : {x : Δ // x ≠ ε ∧ x ≠ ε'}) :
    evalPairPatch ε ε' a b g x.1 = g x := by
  simp [evalPairPatch, x.2.1, x.2.2]

/-- **Patching is a right inverse to evaluation** on the pair `(ε, ε')`: rebuilding a function from
its own two values and its restriction to the complement returns the function. -/
lemma evalPairPatch_ofFun {Δ V : Type} [DecidableEq Δ] {ε ε' : Δ} (ι : Δ → V) :
    evalPairPatch ε ε' (ι ε) (ι ε') (fun x => ι x.1) = ι := by
  funext x
  simp only [evalPairPatch]
  split_ifs with hx hx'
  · rw [hx]
  · rw [hx']
  · rfl

/-- Evaluation of the patch at the two distinguished points, packaged with the restriction to the
complement. -/
lemma evalPairPatch_eval {Δ V : Type} [DecidableEq Δ] {ε ε' : Δ} (h : ε ≠ ε') (a b : V)
    (g : {x : Δ // x ≠ ε ∧ x ≠ ε'} → V) :
    ((evalPairPatch ε ε' a b g ε, evalPairPatch ε ε' a b g ε'),
        fun x => evalPairPatch ε ε' a b g x.1) = ((a, b), g) := by
  simp only [Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [evalPairPatch]
  · simp [evalPairPatch, Ne.symm h]
  · funext x
    simp [evalPairPatch, x.2.1, x.2.2]

/-- The decomposition `(Δ → V) ≃ (V × V) × ({x // x ≠ ε ∧ x ≠ ε'} → V)`: a function is exactly a
pair of values at the two distinguished inputs together with its restriction to the complement. -/
def evalPairEquiv {Δ V : Type} [DecidableEq Δ] {ε ε' : Δ} (h : ε ≠ ε') :
    (Δ → V) ≃ (V × V) × ({x : Δ // x ≠ ε ∧ x ≠ ε'} → V) where
  toFun ι := ((ι ε, ι ε'), fun x => ι x.1)
  invFun z := evalPairPatch ε ε' z.1.1 z.1.2 z.2
  left_inv ι := evalPairPatch_ofFun ι
  right_inv z := evalPairPatch_eval h z.1.1 z.1.2 z.2

/-- The same decomposition restricted to the functions whose pair of values lies in `S`:
`{ι // (ι ε, ι ε') ∈ S} ≃ {p // p ∈ S} × ({x // x ≠ ε ∧ x ≠ ε'} → V)`. -/
def evalPairSubtypeEquiv {Δ V : Type} [DecidableEq Δ] {ε ε' : Δ} (h : ε ≠ ε')
    (S : Finset (V × V)) :
    {ι : Δ → V // (ι ε, ι ε') ∈ S} ≃
      {p : V × V // p ∈ S} × ({x : Δ // x ≠ ε ∧ x ≠ ε'} → V) where
  toFun a := (⟨(a.1 ε, a.1 ε'), a.2⟩, fun x => a.1 x.1)
  invFun z := ⟨evalPairPatch ε ε' z.1.1.1 z.1.1.2 z.2, by
    have hh := evalPairPatch_eval h z.1.1.1 z.1.1.2 z.2
    rw [show (evalPairPatch ε ε' z.1.1.1 z.1.1.2 z.2 ε,
              evalPairPatch ε ε' z.1.1.1 z.1.1.2 z.2 ε') = (z.1.1.1, z.1.1.2)
          from congrArg Prod.fst hh]
    exact z.1.2⟩
  left_inv a := by
    dsimp only
    apply Subtype.ext
    dsimp only
    exact evalPairPatch_ofFun a.1
  right_inv z := by
    obtain ⟨⟨p, hp⟩, g⟩ := z
    dsimp only
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      dsimp only
      exact congrArg Prod.fst (evalPairPatch_eval h p.1 p.2 g)
    · dsimp only
      exact congrArg Prod.snd (evalPairPatch_eval h p.1 p.2 g)

/-- **(fiber count)** Evaluation at two distinct inputs is a uniform fibration: for `ε ≠ ε'`
in a finite type `Δ` and any `S ⊆ V × V`, the number of functions `ι : Δ → V` whose pair of values
`(ι ε, ι ε')` lies in `S` is `#S · |V|^(|Δ|-2)`.  Equivalently (multiplying by `|V|²` and using
`|Δ → V| = |V|^|Δ|`) the form stated below. -/
theorem evalPairFiber {Δ V : Type} [Fintype Δ] [DecidableEq Δ] [Fintype V] [DecidableEq V]
    {ε ε' : Δ} (h : ε ≠ ε') (S : Finset (V × V)) :
    ((Finset.univ.filter (fun ι : Δ → V => (ι ε, ι ε') ∈ S)).card : ℝ) * (Fintype.card V : ℝ) ^ 2
      = (S.card : ℝ) * (Fintype.card (Δ → V) : ℝ) := by
  classical
  -- The filtered set of functions is in bijection with `S` times the functions on the complement.
  have hA : Fintype.card {ι : Δ → V // (ι ε, ι ε') ∈ S}
      = (Finset.univ.filter (fun ι : Δ → V => (ι ε, ι ε') ∈ S)).card := by
    rw [Fintype.card_subtype]
  have hB : Fintype.card {ι : Δ → V // (ι ε, ι ε') ∈ S}
      = Fintype.card ({p : V × V // p ∈ S} × ({x : Δ // x ≠ ε ∧ x ≠ ε'} → V)) :=
    Fintype.card_congr (evalPairSubtypeEquiv h S)
  have hD : Fintype.card ({p : V × V // p ∈ S} × ({x : Δ // x ≠ ε ∧ x ≠ ε'} → V))
      = S.card * (Fintype.card V) ^ (Fintype.card {x : Δ // x ≠ ε ∧ x ≠ ε'}) := by
    rw [Fintype.card_prod, Fintype.card_fun]
    congr 1
    exact Fintype.card_coe S
  have hcount : (Finset.univ.filter (fun ι : Δ → V => (ι ε, ι ε') ∈ S)).card
      = S.card * (Fintype.card V) ^ (Fintype.card {x : Δ // x ≠ ε ∧ x ≠ ε'}) := by
    rw [← hA, hB, hD]
  -- And `|Δ → V| = |V|² · |V|^#{x // x ≠ ε ∧ x ≠ ε'}` by the same decomposition.
  have hE : Fintype.card (Δ → V)
      = (Fintype.card V) ^ 2 * (Fintype.card V) ^ (Fintype.card {x : Δ // x ≠ ε ∧ x ≠ ε'}) := by
    rw [Fintype.card_congr (evalPairEquiv (V := V) h)]
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_prod]
    ring
  rw [hcount, hE]
  push_cast
  ring

end Work.Peluse.SwapA
