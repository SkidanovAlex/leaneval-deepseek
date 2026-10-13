import Mathlib
import Submission.Work.WilC2.Square
import Submission.Work.WilC4g.exists_ulpm_family
import Submission.Work.WilC4g.exists_ulpm_of_formula
import Submission.Work.WilC4.exists_Tdefinable_fibre
import Submission.Work.WilC4.dcl_elementary
import Submission.Work.WilC4.Defs
import Submission.Work.WilVP.definable_bound
import Submission.Work.WilVP.adjoin_bound_family

namespace Work.WilVP

/-! ### The ordered-field fact completing the square-sum bound

The relation `bound x R := ∃ u, x * x + u * u = R * R` encodes `|x| ≤ |R|`: the forward
implication holds in every ordered field (it is `Work.WilVP.abs_le_of_sq_sum_eq`, in the module
`Submission.Work.WilVP.adjoin_bound_family`), while the reverse needs the square root of the
nonnegative element `R² - x²`, which exists in a model of `TR`
(`Work.WilC2.model_exists_sq`). -/

/-- In a model of `TR`, `|x| ≤ R` exhibits `x` as a "bounded" element: `x² + u² = R²` for some
`u` (namely `u = √(R² - x²)`). -/
lemma sq_sum_eq_of_abs_le {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : M ⊨ WilkiesDesign.CG.TR) {x R : M} (h : |x| ≤ R) :
    ∃ u : M, x * x + u * u = R * R := by
  have hR0 : 0 ≤ R := le_trans (abs_nonneg x) h
  have hxR : |x| ≤ |R| := by rwa [abs_of_nonneg hR0]
  have hsq : x * x ≤ R * R := by
    have h2 : x ^ 2 ≤ R ^ 2 := sq_le_sq.mpr hxR
    simpa [sq] using h2
  obtain ⟨u, hu⟩ := Work.WilC2.model_exists_sq hM (R * R - x * x) (by nlinarith)
  exact ⟨u, by nlinarith⟩

/-- An element `w` definable from `S ∪ {z}` is the value at `z` of an `∅`-definable functional
family with parameters in `S` and *uniformly bounded* domain fibres.

(The earlier statement at the path `exists_bounded_family` omitted `[M ⊨ TR]` and was declared
FALSE for that reason: the encoding `bound(x,R) := ∃ z, x*x + z*z = R*R` of `|x| ≤ R` is only
complete in a model of `TR`, where `Work.WilC2.model_exists_sq` gives square roots of nonnegative
elements.  The implication `x²+z² = R² → |x| ≤ |R|` holds in every ordered field, so only the
membership `(z,w) ∈ Y` needs `TR`.)

Route: `((S:Set M) ∪ {z}).Definable LRc {fun _ : Fin 1 => w}` is
`Work.WilC4.DefinableElt (S:Set M) {z} w`, so `Work.WilC4.exists_Tdefinable_fibre` gives a set
`Z ⊆ M × M` with `S.Definable₂ LRc Z`, `(w,z) ∈ Z` and `{v | (v,z) ∈ Z} = {w}`; then
`Work.WilC4g.exists_ulpm_family` (applied to the *bounded* relation `Z ∩ {|x| ≤ R}`, definable
over `S` since `R ∈ S`, and `|z| ≤ R` gives `bound(z,R)` by `TR`) gives `k, c, Y₀` with `Y₀` an
`∅`-definable family of graphs and `(z,w)` in the `c`-fibre.
CAUTION: `exists_ulpm_family` only controls the `c`-fibre, not arbitrary tuples, so to satisfy
the `∀ c' ∃ R'` clause you cannot use `Y₀` directly — either adjoin the bound as an extra
*parameter* coordinate (pullback plus intersection with `bound(v 0, v 2)`, parameter tuple
`Fin.cons R c`; every `c'`-fibre is then bounded by `|c' 0|`) or reproduce the construction of
`Work.WilC4g.exists_ulpm_of_formula` with the bound conjunct exposed so that the general fibre
characterisation `(x,y,c') ∈ Y ↔ (… ∧ bound(x, c'_R))` is available. -/
theorem exists_bdd_family {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {z w R : M} (hR : R ∈ (S : Set M))
    (hzR : |z| ≤ R)
    (hw : ((S : Set M) ∪ {z}).Definable WilkiesDesign.CG.LRc {fun _ : Fin 1 => w}) :
    ∃ (k : ℕ) (c : Fin k → M) (Y : Set (Fin (k + 2) → M)), (∀ i, c i ∈ (S : Set M)) ∧
      (∅ : Set M).Definable WilkiesDesign.CG.LRc Y ∧
      (∀ (c' : Fin k → M) (x y y' : M), Fin.cons x (Fin.cons y c') ∈ Y →
        Fin.cons x (Fin.cons y' c') ∈ Y → y = y') ∧
      (∀ c' : Fin k → M, ∃ R' : M, ∀ x y : M, Fin.cons x (Fin.cons y c') ∈ Y → |x| ≤ R') ∧
      Fin.cons z (Fin.cons w c) ∈ Y := by
  -- `w` is definable from `S ∪ {z}`, so it is the unique value of an `S`-definable graph at `z`.
  have hdE : Work.WilC4.DefinableElt (S : Set M) {z} w := hw
  obtain ⟨Z, hZd, hZmem, hZuniq⟩ := Work.WilC4.exists_Tdefinable_fibre hdE
  -- `Z` is the graph of a partial map; turn it into a parameter-free definable family `Y₀` of
  -- graphs with parameters `c ∈ S^k`.
  obtain ⟨k, c, Y₀, hc, hY₀def, hY₀fun, hY₀fib⟩ :=
    Work.WilC4g.exists_ulpm_family (T := (S : Set M)) hZd
  -- the square-sum bound is `∅`-definable
  have hBnd : (∅ : Set M).Definable WilkiesDesign.CG.LRc
      {v : Fin ((k + 1) + 2) → M | ∃ u : M, v 0 * v 0 + u * u = v 2 * v 2} :=
    definable_bound (M := M) (α := Fin ((k + 1) + 2)) 0 2
  -- adjoin the bound `R` as the first parameter coordinate; every fibre is then bounded
  obtain ⟨Y, hYdef, hYfun, hYbdd, hYmem⟩ := adjoin_bound_family (k := k) hY₀def hY₀fun hBnd
  refine ⟨k + 1, Fin.cons R c, Y, ?_, hYdef, hYfun, hYbdd, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => exact hR
    | succ j => exact hc j
  · refine hYmem z w R c ?_ ?_
    · rw [hY₀fib]
      exact ⟨hZmem, fun y' hy' => hZuniq y' hy'⟩
    · exact sq_sum_eq_of_abs_le (inferInstance : M ⊨ WilkiesDesign.CG.TR) hzR

end Work.WilVP
