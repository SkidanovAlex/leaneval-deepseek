import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.rpow_tail_bound
import Submission.Work.WilC0.Main

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- For `c : Fin 0 → ℝ`, the tuple `Fin.cons x (Fin.cons y c)` is `![x, y]`. -/
private lemma fin_cons_zero_eq_vec (c : Fin 0 → ℝ) (x y : ℝ) :
    Fin.cons x (Fin.cons y c) = ![x, y] := by
  have hc : c = (fun i : Fin 0 => i.elim0) := Subsingleton.elim _ _
  rw [hc]
  rfl

/-- **R-tool 1** (from `hPB` + `C0_rexp_syntax`): a `∅`-definable function on `ℝ` is
polynomially bounded at `+∞`, with an integer exponent.

`Y ⊆ ℝ²` is the graph of a function of the first coordinate.  By `C0_rexp_syntax`
(area C0) it is `RExpExist`, so the polynomial-boundedness hypothesis `hPB` applies to it
(with `k = 0` parameters).  It yields the dichotomy "eventually `0`, or asymptotic to a
monomial `a · x^q` with `q ∈ ℚ`, `a ≠ 0`"; the first case is bounded by `x ^ 0`, and the
second is absorbed into an integer exponent by `rpow_tail_bound`. -/
theorem pb_poly_bound
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y') :
    ∃ n : ℕ, ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → |y| ≤ x ^ n := by
  -- `Y` is `RExpExist` (area C0), so `hPB` applies.
  have hYrex : WilkiesDesign.RExpExist Y :=
    WilkiesDesign.CG.C0_rexp_syntax_proved hR Y hY
  have hcons : ∀ (c : Fin 0 → ℝ) (x y : ℝ), Fin.cons x (Fin.cons y c) = ![x, y] :=
    fun c x y => fin_cons_zero_eq_vec c x y
  -- the graph condition in the shape `hPB` expects (`k = 0` parameters)
  have hfun' : ∀ (c : Fin 0 → ℝ) (x y y' : ℝ),
      Fin.cons x (Fin.cons y c) ∈ Y → Fin.cons x (Fin.cons y' c) ∈ Y → y = y' := by
    intro c x y y' hy hy'
    rw [hcons c x y] at hy
    rw [hcons c x y'] at hy'
    exact hfun x y y' hy hy'
  obtain ⟨Qs, hQs⟩ := hPB 0 Y hYrex hfun'
  let c₀ : Fin 0 → ℝ := fun i => i.elim0
  have he : ∀ x y : ℝ, Fin.cons x (Fin.cons y c₀) ∈ Y ↔ ![x, y] ∈ Y :=
    fun x y => by rw [hcons c₀ x y]
  rcases hQs c₀ with ⟨R0, hR0⟩ | ⟨q, _hqQs, a, ha, haε⟩
  · -- branch 1: the function is eventually `0`
    exact ⟨0, R0, fun x y hx hy => by
      have h0 : y = 0 := hR0 x y hx ((he x y).mpr hy)
      rw [h0]
      simp⟩
  · -- branch 2: `y` is asymptotic to `a · x ^ q`, `a ≠ 0`
    have habs_pos : 0 < |a| := abs_pos.mpr ha
    obtain ⟨R₁, hR₁⟩ := haε (|a| / 2) (by positivity)
    refine rpow_tail_bound (q := q) (a := a) ha (R₁ := R₁)
      (P := fun x y => ![x, y] ∈ Y) ?_
    intro x y hx hy
    exact hR₁ x y hx ((he x y).mpr hy)

end Work.WilC4
