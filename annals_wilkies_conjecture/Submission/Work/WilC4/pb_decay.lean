import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC0.Main

namespace Work.WilC4

open WilkiesDesign

/-- **Polynomial decay of a definable one-variable function with limsup `≤ 0`.**

`Y` is a `LRc`-definable graph of a function `x ↦ y` (over `ℝ_rexp`), polynomially bounded in the
sense of `PolyBoundedRExp`, and `y` is eventually `< ε` for every `ε > 0` (i.e. `limsup_{x→∞} y ≤ 0`).

Then `y` is eventually bounded above by `β · x^{-η}` for some rational `η > 0` and `β > 0`.

The proof applies `PolyBoundedRExp` to the (parameter-free) family `Y`, obtaining a finite set `Qs`
of exponents with `y = 0` eventually, or `y / x^q → a ≠ 0` for some `q ∈ Qs`.  If `q < 0` this is
already the required decay.  If `q ≥ 0`: a positive limit `a` is incompatible with `y → 0` (the two
estimates hold on the same nonempty tail, giving a contradiction, so the bound is vacuous); a
negative limit makes `y` eventually negative, hence below the (positive) bound `x^{-1}`. -/
theorem pb_decay (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ) (hPB : WilkiesDesign.CG.PolyBoundedRExp) {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y') (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → y < ε) : ∃ (η : ℚ) (β : ℝ), 0 < η ∧ 0 < β ∧ ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → y ≤ β * x ^ (-(η : ℝ)) := by
  -- `Fin.cons x (Fin.cons y c) = ![x, y]` for the unique `c : Fin 0 → ℝ`
  have hcons : ∀ (c : Fin 0 → ℝ) (x y : ℝ), Fin.cons x (Fin.cons y c) = ![x, y] := by
    intro c x y; funext i; fin_cases i <;> rfl
  -- every `LRc`-definable set is rexp-existential (area C0)
  have hrex : WilkiesDesign.RExpExist Y := WilkiesDesign.CG.C0_rexp_syntax_proved hR Y hY
  -- polynomial boundedness of the parameter-free family `Y`
  obtain ⟨Qs, hQs⟩ := hPB 0 Y hrex (by
    intro c x y y' h1 h2
    exact hfun x y y' ((hcons c x y).symm ▸ h1) ((hcons c x y').symm ▸ h2))
  let c0 : Fin 0 → ℝ := fun i => i.elim0
  rcases hQs c0 with ⟨R0, hR0⟩ | ⟨q, hqQs, a, ha, hlim⟩
  · -- `y = 0` eventually
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    refine ⟨max R0 1, ?_⟩
    intro x y hx hmem
    have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hy : y = 0 := hR0 x y (le_trans (le_max_left _ _) hx) ((hcons c0 x y).symm ▸ hmem)
    rw [hy]
    have : 0 < x ^ (-(1:ℚ):ℝ) := Real.rpow_pos_of_pos hx0 _
    nlinarith [this]
  · by_cases hq : q < 0
    · -- negative exponent: `|y| ≤ (|a|+1) · x^q` is the required decay
      refine ⟨-q, |a| + 1, by exact neg_pos.mpr hq, by positivity, ?_⟩
      obtain ⟨R1, hR1⟩ := hlim 1 (by norm_num)
      refine ⟨max R1 1, ?_⟩
      intro x y hx hmem
      have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hxq : 0 < x ^ (q:ℝ) := Real.rpow_pos_of_pos hx0 _
      have hm := hR1 x y (le_trans (le_max_left _ _) hx) ((hcons c0 x y).symm ▸ hmem)
      have hb : |y / x ^ (q:ℝ)| ≤ |a| + 1 := by
        have h := abs_add_le a (y / x^(q:ℝ) - a)
        rw [add_sub_cancel] at h
        linarith
      have hkey : |y| = |y / x^(q:ℝ)| * x^(q:ℝ) := by
        rw [abs_div, abs_of_pos hxq, div_mul_cancel₀ _ hxq.ne']
      have hcast : -((-q : ℚ) : ℝ) = (q:ℝ) := by push_cast; ring
      rw [hcast]
      calc y ≤ |y| := le_abs_self y
        _ = |y / x^(q:ℝ)| * x^(q:ℝ) := hkey
        _ ≤ (|a| + 1) * x^(q:ℝ) := mul_le_mul_of_nonneg_right hb hxq.le
    · have hq0 : (0:ℚ) ≤ q := not_lt.mp hq
      by_cases ha0 : a < 0
      · -- negative limit: `y` is eventually negative, hence below `x^{-1}`
        refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
        have hapos : 0 < |a| / 2 := by have := abs_pos.mpr ha; linarith
        obtain ⟨R1, hR1⟩ := hlim (|a|/2) hapos
        refine ⟨max R1 1, ?_⟩
        intro x y hx hmem
        have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
        have hxq : 0 < x^(q:ℝ) := Real.rpow_pos_of_pos hx0 _
        have hm := hR1 x y (le_trans (le_max_left _ _) hx) ((hcons c0 x y).symm ▸ hmem)
        have hlt : y / x^(q:ℝ) < a/2 := by
          have h1 := (abs_lt.mp hm).2
          have h2 : |a| = -a := abs_of_neg ha0
          linarith
        have hyneg : y < 0 := by
          have h3 : y < (a/2) * x^(q:ℝ) := (div_lt_iff₀ hxq).mp hlt
          have h4 : (a/2) * x^(q:ℝ) < 0 := by
            apply mul_neg_of_neg_of_pos _ hxq; linarith
          linarith
        have : 0 < x ^ (-(1:ℚ):ℝ) := Real.rpow_pos_of_pos hx0 _
        linarith
      · -- positive limit: incompatible with `y → 0` on the common tail, so the bound is vacuous
        have ha0' : 0 < a := lt_of_le_of_ne (not_lt.mp ha0) (Ne.symm ha)
        refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
        obtain ⟨R1, hR1⟩ := hlim (a/2) (by linarith)
        obtain ⟨R2, hR2⟩ := hdec (a/4) (by linarith)
        refine ⟨max (max R1 R2) 1, ?_⟩
        intro x y hx hmem
        exfalso
        have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
        have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
        have hxq : 0 < x^(q:ℝ) := Real.rpow_pos_of_pos hx0 _
        have hxq1 : 1 ≤ x^(q:ℝ) := Real.one_le_rpow hx1 (by exact_mod_cast hq0)
        have hm1 := hR1 x y
          (le_trans (le_trans (le_max_left R1 R2) (le_max_left (max R1 R2) 1)) hx)
          ((hcons c0 x y).symm ▸ hmem)
        have hm2 := hR2 x y
          (le_trans (le_trans (le_max_right R1 R2) (le_max_left (max R1 R2) 1)) hx)
          ((hcons c0 x y).symm ▸ hmem)
        have hgt : y > a/2 := by
          have h1 := (abs_lt.mp hm1).1
          have h2 : a/2 < y / x^(q:ℝ) := by linarith
          have h3 : (a/2) * x^(q:ℝ) < y := (lt_div_iff₀ hxq).mp h2
          nlinarith [hxq1, ha0']
        linarith

end Work.WilC4
