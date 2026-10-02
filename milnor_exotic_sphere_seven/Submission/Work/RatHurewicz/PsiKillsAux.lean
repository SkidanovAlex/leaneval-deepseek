import Mathlib
import Submission.Work.RatHurewicz.psiDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The assembly of the pieces of an `(m+3)`-cube

`Work.RatHurewicz.Psi_kills_boundary` states that the alternating product of the classes of the
based-ifications `Ψ N m K hN (τ ∘ faceCM i (cval b))` of the faces of an `(m+3)`-cube `τ` is `1`
(Hutchings' `(2.5)`).

This file supplies the *algebraic* half of the reduction: the "assembly" (the layers concatenated
with `GenLoop.transAt`) is a based cube whose class is exactly the alternating product, so that the
statement reduces to the geometric fact that the assembly is null-homotopic
(`Work.RatHurewicz.assembly_null`).

NOTE (formalisation): the class of a based cube is `Quotient.mk (GenLoop.Homotopic.setoid _ _) p`,
whose type is *not* syntactically `HomotopyGroup _ X x₀`; since `HomotopyGroup` is a plain `def`,
type class inference for `*` and `^` fails on the unfolded type.  We therefore introduce the
wrapper `cl`, whose codomain is `HomotopyGroup _ X x₀`, and state all the algebra with it.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The class of a based cube, as an element of the homotopy group (a wrapper that keeps the type
`HomotopyGroup _ X x₀` visible to type class inference). -/
def cl (n : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X) :
    GenLoop (Fin n) X x₀ → HomotopyGroup (Fin n) X x₀ :=
  Quotient.mk _

/-- The `(i,b)`-th piece of an `(m+3)`-cube: the based-ification of its `(i,b)`-face. -/
def piece (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (k : Fin (m + 3) × Fin 2) : GenLoop (Fin (m + 2)) X x₀ :=
  Psi N m K hN (τ.comp (faceCM k.1 (cval k.2)))

/-- The sign `(-1)^{i+b}` of the face `(i,b)`. -/
def esign (m : ℕ) (i : Fin (m + 3)) (b : Fin 2) : ℤ :=
  (-1 : ℤ) ^ ((i : ℕ) + (b : ℕ))

/-- The layer attached to the face `(i,b)`: the piece, reversed in coordinate `1` when the sign
`(-1)^{i+b}` is `-1`. -/
def layer (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (i : Fin (m + 3)) (b : Fin 2) : GenLoop (Fin (m + 2)) X x₀ :=
  if Even ((i : ℕ) + (b : ℕ)) then piece N m K hN τ (i, b)
  else GenLoop.symmAt (1 : Fin (m + 2)) (piece N m K hN τ (i, b))

/-- The concatenation of the two layers of one coordinate direction. -/
def row (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    (i : Fin (m + 3)) : GenLoop (Fin (m + 2)) X x₀ :=
  (List.finRange 2).foldl
    (fun acc b => GenLoop.transAt 0 (layer N m K hN τ i b) acc) GenLoop.const

/-- **The assembly**: all the layers of `τ` concatenated along the first coordinate. -/
def assembly (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X)) :
    GenLoop (Fin (m + 2)) X x₀ :=
  (List.finRange (m + 3)).foldl
    (fun acc i => GenLoop.transAt 0 (row N m K hN τ i) acc) GenLoop.const

section Algebra

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

/-- The class of a `transAt`-concatenation. -/
theorem cl_transAt (p q : GenLoop (Fin n) X x₀) :
    cl n X x₀ (GenLoop.transAt (0 : Fin n) q p) = cl n X x₀ p * cl n X x₀ q := by
  have h := HomotopyGroup.mul_spec (N := Fin n) (X := X) (x := x₀) (i := (0 : Fin n))
    (p := p) (q := q)
  simpa only [cl] using h.symm

/-- The class of a `transAt`-fold of based cubes: the product of the classes (in any order, the
group being commutative). -/
theorem foldl_transAt_class {α : Type} (l : List α) (L : α → GenLoop (Fin n) X x₀)
    (a : GenLoop (Fin n) X x₀) :
    cl n X x₀ (l.foldl (fun acc k => GenLoop.transAt (0 : Fin n) (L k) acc) a)
      = (l.map (fun k => cl n X x₀ (L k))).prod * cl n X x₀ a := by
  induction l generalizing a with
  | nil => rw [List.foldl_nil, List.map_nil, List.prod_nil, one_mul]
  | cons k l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, cl_transAt]
    ac_rfl

/-- The class of the constant cube is `1`. -/
theorem cl_const : cl n X x₀ (GenLoop.const : GenLoop (Fin n) X x₀) = 1 :=
  HomotopyGroup.one_def.symm

/-- The product of a `List.finRange` is the `Finset` product over `Fin n`. -/
theorem finRange_prod {G : Type} [CommMonoid G] (n : ℕ) (g : Fin n → G) :
    ((List.finRange n).map g).prod = ∏ i : Fin n, g i := by
  rw [← List.prod_toFinset g (List.nodup_finRange n), List.toFinset_finRange]

end Algebra

/-- The class of a layer is the `esign`-th power of the class of the piece. -/
theorem layer_class (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    [Nontrivial (Fin (m + 2))] (i : Fin (m + 3)) (b : Fin 2) :
    cl (m + 2) X x₀ (layer N m K hN τ i b)
      = (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b) := by
  have hinv := HomotopyGroup.inv_spec (N := Fin (m + 2)) (X := X) (x := x₀)
    (i := (1 : Fin (m + 2))) (p := piece N m K hN τ (i, b))
  unfold layer esign
  by_cases h : Even ((i : ℕ) + (b : ℕ))
  · rw [if_pos h, h.neg_one_pow, zpow_one]
  · rw [if_neg h, (Nat.not_even_iff_odd.mp h).neg_one_pow, zpow_neg_one]
    simpa only [cl] using hinv.symm

/-- The class of a row. -/
theorem row_class (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    [Nontrivial (Fin (m + 2))] (i : Fin (m + 3)) :
    cl (m + 2) X x₀ (row N m K hN τ i)
      = ∏ b : Fin 2,
          (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b) := by
  have h := foldl_transAt_class (n := m + 2) (List.finRange 2)
    (fun b => layer N m K hN τ i b) GenLoop.const
  rw [row, h, cl_const, mul_one, finRange_prod]
  exact Finset.prod_congr rfl fun b _ => layer_class N m K hN τ i b

/-- **The class of the assembly is the alternating product of the pieces.** -/
theorem assembly_class (N m : ℕ) (K : Tower x₀ N) (hN : m + 1 ≤ N) (τ : C(IC (m + 3), X))
    [Nontrivial (Fin (m + 2))] :
    cl (m + 2) X x₀ (assembly N m K hN τ)
      = ∏ i : Fin (m + 3), ∏ b : Fin 2,
          (cl (m + 2) X x₀ (piece N m K hN τ (i, b))) ^ (esign m i b) := by
  have h := foldl_transAt_class (n := m + 2) (List.finRange (m + 3))
    (fun i => row N m K hN τ i) GenLoop.const
  rw [assembly, h, cl_const, mul_one, finRange_prod]
  exact Finset.prod_congr rfl fun i _ => row_class N m K hN τ i

end

end Work.RatHurewicz
