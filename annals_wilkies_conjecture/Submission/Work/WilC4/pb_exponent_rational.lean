/-
  WilC4/pb_exponent_rational : the second "R-side tool" of the C4 route.

  `PolyBoundedRExp` says that every `LRc`-definable family of functions `x ↦ y` (with a fixed
  finite set of exponents for the whole family) is, for large `x`, either eventually `0` or
  asymptotic to a monomial `a · x^q` with `q : ℚ`, `a ≠ 0`.

  Here `Y ⊆ ℝ²` is the graph of a partial function of `x` with unbounded domain, and its values
  are squeezed between `C⁻¹ x^σ` and `C x^σ` for large `x`.  Applying `hPB` (with no parameters,
  `k = 0`) gives either the "eventually `0`" branch — which the lower bound `C⁻¹ x^σ > 0`
  refutes — or an exponent `q ∈ Qs` with `y / x^q → a ≠ 0`; combining the two asymptotic
  descriptions forces `σ = q`, hence `σ ∈ ℚ`.

  The two independent analytic ingredients are proved in sibling files and imported here:
  * `Work.WilC4.pb_not_eventually_zero` (the "eventually `0`" branch is impossible);
  * `Work.WilC4.pb_exponent_asymptotic` (the asymptotic branch forces `σ = q`).
-/
import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC0.Main
import Submission.Work.WilC4.pb_exponent_asymptotic
import Submission.Work.WilC4.pb_not_eventually_zero

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

/-- `Fin.cons x (Fin.cons y c) ∈ Y` and `![x, y] ∈ Y` say the same thing for the unique
`c : Fin 0 → ℝ`.  This bridges the shape `hPB` uses (the coordinate block `(x, y, c)` with
`k = 0` parameters) with the shape `![x, y]` used by the hypotheses on `Y`. -/
private lemma cons_cons_fin0_mem_iff {Y : Set (Fin 2 → ℝ)} (c : Fin 0 → ℝ) (x y : ℝ) :
    Fin.cons x (Fin.cons y c) ∈ Y ↔ ![x, y] ∈ Y := by
  have hc : c = finZeroElim := Subsingleton.elim c finZeroElim
  subst hc
  have h : (Fin.cons x (Fin.cons y finZeroElim) : Fin (0 + 2) → ℝ) = ![x, y] := by
    funext i; fin_cases i <;> rfl
  rw [h]

theorem pb_exponent_rational (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ) (hPB : WilkiesDesign.CG.PolyBoundedRExp) {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y') (hdom : ∀ R : ℝ, ∃ x y : ℝ, R ≤ x ∧ ![x, y] ∈ Y) (σ C : ℝ) (hC : 1 ≤ C) (hσ : ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → C⁻¹ * x ^ σ ≤ |y| ∧ |y| ≤ C * x ^ σ) : ∃ q : ℚ, σ = q := by
  -- `Y` is `LRc`-definable, hence `RExpExist` (area C0).
  have hYrex : WilkiesDesign.RExpExist Y := WilkiesDesign.CG.C0_rexp_syntax_proved hR Y hY
  -- the graph condition in the shape `hPB` expects, with no parameters
  have hfun' : ∀ (c : Fin 0 → ℝ) (x y y' : ℝ),
      Fin.cons x (Fin.cons y c) ∈ Y → Fin.cons x (Fin.cons y' c) ∈ Y → y = y' := by
    intro c x y y' h1 h2
    rw [cons_cons_fin0_mem_iff c x y] at h1
    rw [cons_cons_fin0_mem_iff c x y'] at h2
    exact hfun x y y' h1 h2
  obtain ⟨Qs, hQs⟩ := hPB 0 Y hYrex hfun'
  obtain hb := hQs (fun i : Fin 0 => i.elim0)
  rcases hb with hb1 | ⟨q, _hqQ, a, ha, hasym⟩
  · -- the "eventually `0`" branch contradicts the lower bound `C⁻¹ x^σ ≤ |y|`
    exfalso
    apply pb_not_eventually_zero hdom σ C hC hσ
    obtain ⟨R0, hR0⟩ := hb1
    exact ⟨R0, fun x y hx hxy =>
      hR0 x y hx ((cons_cons_fin0_mem_iff (fun i : Fin 0 => i.elim0) x y).mpr hxy)⟩
  · -- the asymptotic branch gives `σ = q`
    exact ⟨q, pb_exponent_asymptotic hdom σ C hC hσ ha fun ε hε => by
      obtain ⟨R, hR⟩ := hasym ε hε
      exact ⟨R, fun x y hx hxy =>
        hR x y hx ((cons_cons_fin0_mem_iff (fun i : Fin 0 => i.elim0) x y).mpr hxy)⟩⟩

end Work.WilC4
