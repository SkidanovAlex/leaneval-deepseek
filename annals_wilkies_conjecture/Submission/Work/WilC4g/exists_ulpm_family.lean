import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC2.definable_fin_params
import Submission.Work.WilC4g.exists_ulpm_of_formula

namespace Work.WilC4g

open FirstOrder FirstOrder.Language

/-!
  ## A uniform family of last-free-variable partial maps

  Given `Z ⊆ M × M` definable in `LRc` with parameters in `T`, we produce finitely many
  parameters `c ∈ T^k` together with a *parameter free* `LRc`-definable set `Y ⊆ M^{k+2}` such
  that `Y` is the graph of a partial map of the first coordinate (over every parameter tuple)
  and the fibre of `Y` at `c` is exactly the graph of the (partial) map determined by `Z`:
  `(x, y, c) ∈ Y ↔ (y, x) ∈ Z ∧ ∃! y', (y', x) ∈ Z`.

  The mathematical content is split in two:

  * `exists_param_formula` : a `T`-definable set uses only finitely many parameters; enumerating
    them as `c : Fin k → M` and turning the constants into free variables produces a single
    parameterised formula `φ` with `φ(c, w) ↔ (w 0, w 1) ∈ Z`.
  * `exists_ulpm_of_formula` : from an arbitrary parameterised formula one builds the
    parameter free set `Y` by *pushing the parameters into tuple coordinates* and adjoining the
    uniqueness condition `∀ y', φ(p, y', x) → y' = y`; this makes `Y` a graph for every `p`.
-/

/-- **Finitely many parameters, as a fibred formula.** If `Z ⊆ M × M` is `LRc`-definable with
parameters in `T`, then there are `k`, a tuple `c : Fin k → M` with `c i ∈ T` and an
`LRc`-formula `φ` over the variable block `Fin k ⊕ Fin 2` with `φ.Realize (c, w) ↔ (w 0, w 1) ∈ Z`.

The formula `φ` is parameter free: its constants have been turned into the free variables
`Fin k`, and `c` is the point at which we recover `Z`. -/
theorem exists_param_formula {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {T : Set M} {Z : Set (M × M)} (hZd : T.Definable₂ WilkiesDesign.CG.LRc Z) :
    ∃ (k : ℕ) (c : Fin k → M) (φ : WilkiesDesign.CG.LRc.Formula (Fin k ⊕ Fin 2)),
      (∀ i, c i ∈ T) ∧
      (∀ w : Fin 2 → M, φ.Realize (Sum.elim c w) ↔ (w 0, w 1) ∈ Z) := by
  classical
  obtain ⟨A0, hA0sub, hA0⟩ := Set.definable_iff_finitely_definable.mp hZd
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hA0
  have hφ' : ∀ w : Fin 2 → M, (w 0, w 1) ∈ Z ↔ φ.Realize (Sum.elim (Subtype.val) w) := by
    intro w
    have h := congrArg (fun s : Set (Fin 2 → M) => w ∈ s) hφ
    simpa [Set.mem_ofPred_eq] using h
  let k := A0.card
  let e : ↥(A0 : Set M) ≃ Fin k := A0.equivFin
  let cc : Fin k → M := fun i => (e.symm i).val
  let g₁ : (↥(A0 : Set M) ⊕ Fin 2) → (Fin k ⊕ Fin 2) := Sum.map (fun a => (e a : Fin k)) id
  let φ₁ : WilkiesDesign.CG.LRc.Formula (Fin k ⊕ Fin 2) := φ.relabel g₁
  have hrel : ∀ w : Fin 2 → M,
      φ₁.Realize (Sum.elim cc w) ↔
        φ.Realize (Sum.elim (fun a : ↥(A0 : Set M) => cc (e a)) w) := by
    intro w
    change (Formula.relabel g₁ φ).Realize (Sum.elim cc w) ↔ _
    rw [Formula.realize_relabel]
    have hcomp : Sum.elim cc w ∘ g₁ = Sum.elim (fun a : ↥(A0 : Set M) => cc (e a)) w := by
      funext z
      rcases z with a | j <;> rfl
    rw [hcomp]
  have hcc : (fun a : ↥(A0 : Set M) => cc (e a)) = Subtype.val := by
    funext a
    change (e.symm (e a)).val = (a : M)
    rw [Equiv.symm_apply_apply]
  exact ⟨k, cc, φ₁, fun i => hA0sub (e.symm i).2, fun w => by
    rw [hrel w, hcc]
    exact (hφ' w).symm⟩

/-- **A uniform family of partial maps.** Given a parameter free `LRc`-formula `φ` over the
variable block `Fin n ⊕ Fin 2` and a parameter tuple `c : Fin n → M`, there is a parameter free
`LRc`-definable set `Y ⊆ M^{n+2}` such that `Y` is a graph in its second coordinate over every
parameter tuple, and the fibre of `Y` at `c` is the graph of the partial map determined by
`w ↦ φ.Realize (Sum.elim c w)`.

The proof pushes the parameters `Fin n` into the last tuple coordinates and adjoins the
uniqueness condition, which is what makes `Y` a graph for *every* tuple of parameters. -/
theorem exists_ulpm_family {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {T : Set M} {Z : Set (M × M)} (hZd : T.Definable₂ WilkiesDesign.CG.LRc Z) :
    ∃ (k : ℕ) (c : Fin k → M) (Y : Set (Fin (k + 2) → M)),
      (∀ i, c i ∈ T) ∧ (∅ : Set M).Definable WilkiesDesign.CG.LRc Y ∧
      (∀ (c' : Fin k → M) (x y y' : M), Fin.cons x (Fin.cons y c') ∈ Y →
        Fin.cons x (Fin.cons y' c') ∈ Y → y = y') ∧
      (∀ x y : M, Fin.cons x (Fin.cons y c) ∈ Y ↔
        ((y, x) ∈ Z ∧ ∀ y' : M, (y', x) ∈ Z → y' = y)) := by
  classical
  obtain ⟨k, c, φ, hcm, hkey⟩ := exists_param_formula hZd
  obtain ⟨Y, hYdef, hYfun, hYfib⟩ := exists_ulpm_of_formula φ c
  refine ⟨k, c, Y, hcm, hYdef, hYfun, ?_⟩
  intro x y
  rw [hYfib x y]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using (hkey ![y, x]).mp h1, fun y' hy' => h2 y' ?_⟩
    exact (hkey ![y', x]).mpr (by simpa using hy')
  · rintro ⟨h1, h2⟩
    refine ⟨(hkey ![y, x]).mpr (by simpa using h1), fun y' hy' => ?_⟩
    exact h2 y' (by simpa using (hkey ![y', x]).mp hy')

end Work.WilC4g
