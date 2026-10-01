import Mathlib
import Submission.Work.ZeroFreeTables.HB8Defs
import Submission.Work.ZeroFreeTables.HBLemma8_1_q
import Submission.Work.LinnikAreas.DhRepel.dhTrianglePtH
import Submission.Work.LinnikAreas.DhCapped.SiegelSimple
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.log_unbounded_nat
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.ZeroFreeTables.Table4.HB82

namespace Work.ZeroFreeTables

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-! ## Small real-analysis helpers for the §8.1 arithmetic -/

/-- `s - 1 ≤ 2 log s` for `1 ≤ s ≤ 2`. -/
lemma hb81_sub_one_le_two_log (s : ℝ) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    s - 1 ≤ 2 * Real.log s := by
  have hs : 0 < s := lt_of_lt_of_le one_pos h1
  have hlog : (s - 1) / s ≤ Real.log s := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < s⁻¹ by positivity)
    rw [Real.log_inv] at h
    have he : s⁻¹ - 1 = -((s - 1) / s) := by
      rw [inv_eq_one_div]
      field_simp <;> ring
    rw [he] at h
    linarith
  have h3 : (s - 1) ≤ 2 * ((s - 1) / s) := by
    have hle : (1:ℝ) ≤ 2 / s := by rw [le_div_iff₀ hs]; linarith
    have h4 : (s - 1) * 1 ≤ (s - 1) * (2 / s) := mul_le_mul_of_nonneg_left hle (by linarith)
    have he : (s - 1) * (2 / s) = 2 * ((s - 1) / s) := by ring
    rw [mul_one, he] at h4
    exact h4
  linarith

/-! ## Covering `[4e, ∞)` by dyadic cells -/

/-- The dyadic cells `[4e·2^k, 4e·2^{k+1}]` (`k < K`) together with the tail `[4e·2^K, ∞)`
cover `[4e, ∞)`. -/
theorem HB81_cover (a : ℝ) (ha : 4 * Real.exp 1 ≤ a) (K : ℕ) :
    (∃ k : ℕ, k < K ∧ 4 * Real.exp 1 * 2 ^ k ≤ a ∧ a ≤ 4 * Real.exp 1 * 2 ^ (k + 1)) ∨
      4 * Real.exp 1 * 2 ^ K ≤ a := by
  induction K with
  | zero => exact Or.inr (by simpa using ha)
  | succ K ih =>
    rcases ih with ⟨k, hk, h1, h2⟩ | hK
    · exact Or.inl ⟨k, Nat.lt_succ_of_lt hk, h1, h2⟩
    · by_cases h : 4 * Real.exp 1 * 2 ^ (K + 1) ≤ a
      · exact Or.inr h
      · exact Or.inl ⟨K, Nat.lt_succ_self K, hK, le_of_lt (not_le.mp h)⟩

/-! ## The §8.1 arithmetic of the repulsion -/

/-- The bounded-range arithmetic of HB's §8.1. -/
theorem HB81_cell_arith (ε₀ ec : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ ≤ 2) (hec : 0 ≤ ec)
    (hsmall : 4 * (2 - ε₀) * ec ≤ ε₀) (X : ℝ) (hX : 4 * Real.exp 1 ≤ X)
    (lam₀ lam₁ : ℝ) (hXle : X ≤ lam₀) (h2X : lam₀ ≤ 2 * X) (hlam₁ : 0 < lam₁)
    (hb : Real.log (1 / lam₁)
      ≤ (1 / 2 + 1 / X + 2 * ec) * lam₀ + Real.log (4 * X / lam₀ ^ 2)) :
    (2 - ε₀) * Real.log (1 / lam₁) ≤ lam₀ := by
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hX
  have hlam0pos : 0 < lam₀ := lt_of_lt_of_le hXpos hXle
  have hτ0 : 0 ≤ 2 - ε₀ := by linarith
  by_cases hL : Real.log (1 / lam₁) ≤ 0
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hτ0 hL) hlam0pos.le
  · push_neg at hL
    have hτec : 2 * (2 - ε₀) * ec - ε₀ / 2 ≤ 0 := by linarith [hsmall]
    have hs1 : 1 ≤ lam₀ / X := by rw [le_div_iff₀ hXpos]; linarith
    have hs2 : lam₀ / X ≤ 2 := by rw [div_le_iff₀ hXpos]; linarith
    have hlog4div : Real.log (4 / X) ≤ -1 := by
      have h4X : 4 / X ≤ 1 / Real.exp 1 := by
        rw [div_le_iff₀ hXpos, show (1:ℝ) / Real.exp 1 * X = X / Real.exp 1 by ring,
          le_div_iff₀ (Real.exp_pos 1)]
        linarith [hX]
      have h := Real.log_le_log (by positivity : (0:ℝ) < 4 / X) h4X
      rw [one_div, Real.log_inv, Real.log_exp] at h
      linarith
    have hlogAX : Real.log (4 * X / lam₀ ^ 2) = Real.log (4 / X) - 2 * Real.log (lam₀ / X) := by
      rw [show 4 * X / lam₀ ^ 2 = (4 / X) / (lam₀ / X) ^ 2 by field_simp <;> ring]
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    have hid : (1 / 2 + 1 / X + 2 * ec) * lam₀ + Real.log (4 * X / lam₀ ^ 2)
        = lam₀ / 2 + 2 * ec * lam₀ + Real.log (4 / X)
          + (lam₀ / X - 2 * Real.log (lam₀ / X)) := by
      rw [hlogAX]; ring
    have hb1 : lam₀ / X - 2 * Real.log (lam₀ / X) ≤ 1 := by
      have := hb81_sub_one_le_two_log (lam₀ / X) hs1 hs2; linarith
    have hkey2 : (1 / 2 + 1 / X + 2 * ec) * lam₀ + Real.log (4 * X / lam₀ ^ 2)
        ≤ lam₀ / 2 + 2 * ec * lam₀ := by
      rw [hid]; linarith [hb1, hlog4div]
    have hfinal : (2 - ε₀) * (lam₀ / 2 + 2 * ec * lam₀) ≤ lam₀ := by
      have he : (2 - ε₀) * (lam₀ / 2 + 2 * ec * lam₀)
          = lam₀ * (1 - ε₀ / 2 + 2 * (2 - ε₀) * ec) := by ring
      rw [he]
      exact mul_le_of_le_one_right hlam0pos.le (by linarith [hτec])
    have hkey : (2 - ε₀) * ((1 / 2 + 1 / X + 2 * ec) * lam₀ + Real.log (4 * X / lam₀ ^ 2)) ≤ lam₀ :=
      le_trans (mul_le_mul_of_nonneg_left hkey2 hτ0) hfinal
    exact le_trans (mul_le_mul_of_nonneg_left hb hτ0) hkey

/-- The unbounded-range arithmetic of HB's §8.1. -/
theorem HB81_tail_arith (ε₀ ec : ℝ) (hε₀ : 0 < ε₀) (hε₀2 : ε₀ ≤ 2) (hec : 0 ≤ ec)
    (hsmall : 8 * (2 - ε₀) * ec ≤ ε₀) (X : ℝ) (hX : 4 * Real.exp 1 ≤ X)
    (hXbig : 4 * (2 - ε₀) / ε₀ ≤ X)
    (lam₀ lam₁ : ℝ) (hXle : X ≤ lam₀) (hlam₁ : 0 < lam₁)
    (hb : Real.log (1 / lam₁)
      ≤ (1 / 2 + 1 / X + 2 * ec) * lam₀ + Real.log (4 * X / lam₀ ^ 2)) :
    (2 - ε₀) * Real.log (1 / lam₁) ≤ lam₀ := by
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hX
  have hlam0pos : 0 < lam₀ := lt_of_lt_of_le hXpos hXle
  have hτ0 : 0 ≤ 2 - ε₀ := by linarith
  by_cases hL : Real.log (1 / lam₁) ≤ 0
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hτ0 hL) hlam0pos.le
  · push_neg at hL
    have hcoef : (2 - ε₀) * (1 / 2 + 1 / X + 2 * ec) ≤ 1 := by
      have h1 : (2 - ε₀) / X ≤ ε₀ / 4 := by
        rw [div_le_iff₀ hXpos]
        have h := mul_le_mul_of_nonneg_left hXbig (by positivity : (0:ℝ) ≤ ε₀ / 4)
        have he : ε₀ / 4 * (4 * (2 - ε₀) / ε₀) = 2 - ε₀ := by field_simp <;> ring
        rw [he] at h; linarith [h]
      have h4 : 2 * (2 - ε₀) * ec ≤ ε₀ / 4 := by linarith [hsmall]
      have hthis : (2 - ε₀) * (1 / 2 + 1 / X + 2 * ec)
          = (2 - ε₀) / 2 + (2 - ε₀) / X + 2 * (2 - ε₀) * ec := by ring
      have h2 : (2 - ε₀) / 2 = 1 - ε₀ / 2 := by ring
      rw [hthis, h2]; linarith [h1, h4]
    have hexp1 : (1:ℝ) ≤ Real.exp 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
    have h4' : (4:ℝ) ≤ lam₀ := by nlinarith [hX, hXle, hexp1]
    have hlogle : Real.log (4 * X / lam₀ ^ 2) ≤ 0 := by
      apply Real.log_nonpos (by positivity)
      rw [div_le_one (by positivity)]
      nlinarith [h4', hXle, hXpos]
    have hkey : (2 - ε₀) * ((1 / 2 + 1 / X + 2 * ec) * lam₀ + Real.log (4 * X / lam₀ ^ 2)) ≤ lam₀ := by
      have h1 : (2 - ε₀) * ((1 / 2 + 1 / X + 2 * ec) * lam₀) ≤ lam₀ := by
        have h := mul_le_mul_of_nonneg_right hcoef hlam0pos.le
        linarith [h]
      have h2 : (2 - ε₀) * Real.log (4 * X / lam₀ ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hτ0 hlogle
      nlinarith [h1, h2]
    exact le_trans (mul_le_mul_of_nonneg_left hb hτ0) hkey

/-! ## The `L52Hyp` provider with tunable slack -/

/-- A non-principal character of level `N` has level at least `3`. -/
private theorem hb81_three_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN2 : N ≤ 2 := by omega
  have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
    intro hh
    exact hχ (MulChar.ext hh)
  push Not at hχne
  rcases hχne with ⟨a, hne⟩
  have hs : Subsingleton (ZMod N)ˣ := by
    interval_cases N <;> infer_instance
  have ha : a = 1 := Subsingleton.elim a 1
  subst a
  simp at hne

/-- For a real character the primitive character inducing it is again real. -/
private theorem hb81_primitive_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
      (χ.primitiveCharacter ^ 2) = 1 := by
    rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h]
  exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
    (by rw [hmap, DirichletCharacter.changeLevel_one])

/-- HB Lemma 3.1 (`φ = 1/4`) with a **tunable** slack, in `L52Hyp` form. -/
theorem HB81_l52_shift (εs : ℝ) (hεs : 0 < εs) (εL : ℝ) (hεL : 0 < εL) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → χ ^ 2 = 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ (1 / 8 + εs - εL / 4) εL δ := by
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ := Work.LinnikAreas.l31free.lemma3_1_free_gen_real
    (φ := (1:ℝ)/4) (by norm_num) (ε := εs) hεs
    (fun k hk ε' hε' => Table4.quarterBoundReal_aux k hk hε')
  refine ⟨δ, hδ0, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ1 hχ2
  intro s hs1 hs2 hs3
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hlogNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hχstar : χ.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ hχ1
  have hcon : 3 ≤ χ.conductor := hb81_three_le χ.primitiveCharacter hχstar
  have hsq : χ.primitiveCharacter ^ 2 = 1 := hb81_primitive_sq_one χ hχ2
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hsq
    (L := Real.log (q : ℝ)) hL₀le hlogNle s hs1 hs2 hs3
  refine hmain'.trans ?_
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  exact mul_le_mul_of_nonneg_right (le_of_eq (by ring)) hlogq


/-! ## Bridging the frozen contract to the §6 triangle of Heath-Brown -/

/-- The divisor of the completed `L`-function at a point of the disc equals `zeroMult`. -/
private theorem hb81_divisor_eq_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hχ : χ ≠ 1) {ρ : ℂ} {R : ℝ} (hmem : ρ ∈ Metric.closedBall (0:ℂ) R) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) R)) ρ = (Work.LinnikContract.zeroMult χ ρ : ℤ) := by
  have hpc : χ.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ hχ
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) :=
    DirichletCharacter.differentiable_completedLFunction hpc
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) R) := fun z _ => hdiff.analyticAt z
  have hmer : MeromorphicOn (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0:ℂ) R) := han.meromorphicOn
  have hAn : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ :=
    hdiff.analyticAt ρ
  have htop : analyticOrderAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ ≠ ⊤ :=
    Work.LinnikAreas.OtherCharRepel.completedLFunction_analyticOrderAt_ne_top
      χ.primitiveCharacter hpc ρ
  rw [MeromorphicOn.divisor_apply hmer hmem, hAn.meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt htop, ENat.map_natCast, WithTop.untop₀_coe]
  rfl

/-- Box maximality of `ρ₀` among the `zeroMult`-zeros of `χ₁` transfers to the `L`-function
maximality hypothesis of the §6 triangle. -/
private theorem hb81_max_of_min {q : ℕ} [NeZero q] (hq2 : 2 ≤ q)
    (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] {ρ₁ ρ₀ : ℂ} {Hb : ℝ}
    (hχ₁ : χ₁ ≠ 1) (him1 : ρ₁.im = 0) (hρ0re : 0 < ρ₀.re)
    (hmax : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb →
      u = ρ₁ ∨ Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) :
    ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ Hb →
      u = ((ρ₁.re : ℝ) : ℂ) ∨ u.re ≤ ρ₀.re := by
  have hρ1eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him1]
  have hχstar : χ₁.primitiveCharacter ≠ 1 :=
    Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ₁
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  intro u hu him
  by_cases hu1 : u = ((ρ₁.re : ℝ) : ℂ)
  · exact Or.inl hu1
  · refine Or.inr ?_
    by_cases hre : u.re ≤ 0
    · linarith
    · push_neg at hre
      have hγ : χ₁.primitiveCharacter.gammaFactor u ≠ 0 :=
        Work.LinnikAreas.OtherCharRepel.gammaFactor_ne_zero_of_re_pos χ₁.primitiveCharacter hre
      have hu0 : u ≠ 0 := by rintro rfl; simp at hre
      have hcomp : DirichletCharacter.completedLFunction χ₁.primitiveCharacter u = 0 := by
        rw [Work.LinnikAreas.OtherCharRepel.completedLFunction_eq_LFunction_mul_gammaFactor
          χ₁.primitiveCharacter u (Or.inl hu0) hγ, hu, zero_mul]
      have hstrip : u.re < 1 :=
        (Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hχstar
          (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hcomp).2
      have hzmu : Work.LinnikContract.zeroMult χ₁ u ≠ 0 :=
        (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₁ hχ₁).2.2 u hu hre hstrip
      rcases hmax u hzmu him with h | h
      · exact absurd (h.trans hρ1eq) hu1
      · rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
        nlinarith [h, hlogq]

/-- **HB's `§8.1` triangle inequality** in the vocabulary of the frozen contract: for every width
`x`, slack `εL`, window radius `δ`, constant `c` and **box height `Hb`** there is a threshold
beyond which the §6 triangle inequality of HB's Lemma 8.1 holds for every real `χ₁` with a real
exceptional zero `ρ₁` and every other `zeroMult`-zero `ρ₀` that is `λ`-minimal in the box
`|Im| ≤ Hb` and satisfies `|ρ₀.im| + δ ≤ Hb` (so that its `δ`-window is inside the box) and
`|ρ₀.im| ≤ 10 log q` (the height up to which the log-derivative input `L52Hyp` applies).
(The threshold `q₀` does *not* depend on `Hb`: `dhTrianglePtH` takes the box height as a
hypothesis, not as a quantifier.) -/
theorem HB81_triangle_local (x : ℝ) (hx : 0 < x) (εL : ℝ) (hεL : 0 < εL)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (c : ℝ) (Hb : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q)
      [NeZero χ₁.conductor] (ρ₁ ρ₀ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → ρ₀ ≠ ρ₁ →
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb → u ≠ ρ₁ →
        Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) →
      |ρ₀.im| + δ ≤ Hb → |ρ₀.im| ≤ 10 * Real.log (q : ℝ) →
      Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 100 →
      Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamMax q →
      Commons.NumberTheory.Linnik.L52Hyp χ₁ c εL δ →
      0 ≤ 2 * (∫ t in (0:ℝ)..x, Real.exp (Work.LinnikContract.lamOf q ρ₀ * t) * (x - t))
        - 2 * (∫ t in (0:ℝ)..x,
            Real.exp ((Work.LinnikContract.lamOf q ρ₀ - Work.LinnikContract.lamOf q ρ₁) * t) * (x - t))
        - x ^ 2 / 2 + (2 * c + 4 * εL) * x := by
  obtain ⟨qT, hT⟩ := Work.LinnikAreas.DhRepel.dhTrianglePtH x hx εL hεL δ hδ0 hδ1 c
  obtain ⟨qS, hS⟩ := Work.LinnikAreas.DhCapped.siegelZeroSimple'
  obtain ⟨qL, hL⟩ := Work.LinnikAreas.log_unbounded_nat
    (max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))))
  refine ⟨max (max qT qS) (max qL 3), ?_⟩
  intro q hq _inst χ₁ _instc ρ₁ ρ₀ hmin hsq him hzm0 hne hmax0 hHb hγ10 h100 hcap H
  have hqT : qT ≤ q :=
    le_trans (le_max_left qT qS) (le_trans (le_max_left (max qT qS) (max qL 3)) hq)
  have hqS : qS ≤ q :=
    le_trans (le_max_right qT qS) (le_trans (le_max_left (max qT qS) (max qL 3)) hq)
  have hqL : qL ≤ q :=
    le_trans (le_max_left qL 3) (le_trans (le_max_right (max qT qS) (max qL 3)) hq)
  have hq3 : 3 ≤ q :=
    le_trans (le_max_right qL 3) (le_trans (le_max_right (max qT qS) (max qL 3)) hq)
  have hq2 : 2 ≤ q := by omega
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hB1 : (100:ℝ) ≤ max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))) := le_max_left _ _
  have hB2 : 1 / (100 * δ) ≤ max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hB3 : 4 / (9 * δ ^ 2) ≤ max 100 (max (1 / (100 * δ)) (4 / (9 * δ ^ 2))) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hlogq100 : (100:ℝ) ≤ Real.log (q:ℝ) := le_trans hB1 (hL q hqL)
  have hlogqδ : 1 / (100 * δ) ≤ Real.log (q:ℝ) := le_trans hB2 (hL q hqL)
  have hlogqδ2 : 4 / (9 * δ ^ 2) ≤ Real.log (q:ℝ) := le_trans hB3 (hL q hqL)
  have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
  have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
  obtain ⟨hρ1re0, hρ1re1, -⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
  obtain ⟨hρ0re0, hρ0re1, -⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm0
  have hρ1eq : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hSie : Work.LinnikContract.zeroMult χ₁ ((ρ₁.re : ℝ) : ℂ) = 1 :=
    hS q hqS χ₁ ρ₁.re hχ1 hsq hρ1re1
      (by rw [← hρ1eq]; exact hzm1) (by rw [← hρ1eq]; exact h100)
  have hmem1 : ((ρ₁.re : ℝ) : ℂ) ∈ Metric.closedBall (0:ℂ) (|ρ₀.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [abs_nonneg ρ₀.im, hρ1re0, hρ1re1]
  have hmem0 : ρ₀ ∈ Metric.closedBall (0:ℂ) (|ρ₀.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im ρ₀) ?_
    have hre : |ρ₀.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hρ0re0, hρ0re1]
    linarith [abs_nonneg ρ₀.im, hre]
  have hdiv1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₀.im| + 2))) ((ρ₁.re : ℝ) : ℂ) ≠ 0 := by
    rw [hb81_divisor_eq_zeroMult χ₁ hχ1 hmem1, hSie]; norm_num
  have hdiv0 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₀.im| + 2))) ρ₀ ≠ 0 := by
    rw [hb81_divisor_eq_zeroMult χ₁ hχ1 hmem0]; exact_mod_cast hzm0
  have hmult1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₀.im| + 2))) ((ρ₁.re : ℝ) : ℂ) = 1 := by
    rw [hb81_divisor_eq_zeroMult χ₁ hχ1 hmem1, hSie]; norm_num
  have hne' : ρ₀ ≠ ((ρ₁.re : ℝ) : ℂ) := by rw [hρ1eq] at hne; exact hne
  have hmaxL : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 → |u.im| ≤ Hb →
      u = ((ρ₁.re : ℝ) : ℂ) ∨ u.re ≤ ρ₀.re :=
    hb81_max_of_min hq2 χ₁ hχ1 him hρ0re0 (by
      intro u hzu himu
      by_cases h : u = ρ₁
      · exact Or.inl h
      · exact Or.inr (hmax0 u hzu himu h))
  have hrect1 : Work.LinnikContract.lamOf q ((ρ₁.re : ℝ) : ℂ) ≤ Work.LinnikContract.lamMax q := by
    rw [← hρ1eq]
    have hb : (4:ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have he4 : Real.exp 4 = (Real.exp 1)^4 := by
        rw [show (4:ℝ) = ((4:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [he4]
      calc (Real.exp 1)^4 ≤ 3^4 := pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_three) 4
        _ ≤ 100 := by norm_num
    have hd : (1:ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    have ha : Real.log 100 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlogq100
    have hc : Real.log 4 ≤ Real.log (Real.log (Real.log (q:ℝ))) :=
      Real.log_le_log (by norm_num) (by linarith only [ha, hb])
    have h1 : (1/100:ℝ) ≤ Work.LinnikContract.lamMax q := by
      rw [Work.LinnikContract.lamMax]; linarith only [hc, hd]
    linarith [h100, h1]
  have hβ1 : |1 - ρ₁.re| ≤ δ := by
    have hlt : 0 < 1 - ρ₁.re := by linarith [hρ1re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq, div_le_iff₀ hlogq]
    have h2 : 1 ≤ Real.log (q:ℝ) * (100 * δ) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 100 * δ)] at hlogqδ; linarith [hlogqδ]
    nlinarith [h100, h2]
  have hLLL : Real.log (Real.log (Real.log (q:ℝ))) ≤ 2 * Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have hz0 : (0:ℝ) ≤ Real.log (Real.log (q:ℝ)) := by
      apply Real.log_nonneg; linarith [hlogq100]
    have h := Real.log_le_rpow_div hz0 (show (0:ℝ) < (1:ℝ)/2 by norm_num)
    have h2 : (Real.log (Real.log (q:ℝ)))^((1:ℝ)/2) / ((1:ℝ)/2)
        = 2 * Real.sqrt (Real.log (Real.log (q:ℝ))) := by
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, show ((1:ℝ)/2)⁻¹ = (2:ℝ) by norm_num, mul_comm]
    linarith [h, h2.le, h2.ge]
  have hβ0 : |1 - ρ₀.re| ≤ δ := by
    have hlt : 0 < 1 - ρ₀.re := by linarith [hρ0re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₀.re = Work.LinnikContract.lamOf q ρ₀ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq, div_le_iff₀ hlogq]
    have h1 : Real.log (Real.log (q:ℝ)) ≤ Real.log (q:ℝ) := Real.log_le_self hlogq.le
    have h2 : Real.sqrt (Real.log (Real.log (q:ℝ))) ≤ Real.sqrt (Real.log (q:ℝ)) :=
      Real.sqrt_le_sqrt h1
    have h3 : 2 * Real.sqrt (Real.log (q:ℝ)) ≤ 3 * δ * Real.log (q:ℝ) := by
      have hs : 2 / (3 * δ) ≤ Real.sqrt (Real.log (q:ℝ)) := by
        rw [Real.le_sqrt (by positivity) hlogq.le]
        rw [show (2 / (3 * δ))^2 = 4 / (9 * δ^2) by field_simp <;> ring]
        exact hlogqδ2
      have hsnn : 0 ≤ Real.sqrt (Real.log (q:ℝ)) := Real.sqrt_nonneg _
      have hs2 : (Real.sqrt (Real.log (q:ℝ)))^2 = Real.log (q:ℝ) := Real.sq_sqrt hlogq.le
      have hkey : 2 ≤ 3 * δ * Real.sqrt (Real.log (q:ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_right hs (by positivity : (0:ℝ) ≤ 3 * δ)
        have he : 2 / (3 * δ) * (3 * δ) = 2 := div_mul_cancel₀ 2 (by positivity : (3:ℝ) * δ ≠ 0)
        nlinarith [hmul, he]
      nlinarith [hkey, hsnn, hs2]
    have hlamMax : Work.LinnikContract.lamMax q ≤ δ * Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamMax]; linarith [hLLL, h2, h3]
    linarith [hcap, hlamMax]
  have hy1 : (1:ℝ) ≤ Real.log (Real.log (q:ℝ)) := by
    have h1 : Real.log 100 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlogq100
    have h2 : (1:ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_three]
    linarith [h1, h2]
  have hs1 : (1/100:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    have h : (1:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.one_le_sqrt.mpr hy1
    linarith [h]
  have hβ1pt : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have hlt : 0 < 1 - ρ₁.re := by linarith [hρ1re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq]
    have h1 : Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) ≤ (1/100) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right h100 hlogq.le
    have h2 : (1/100:ℝ) / Real.log (q:ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right hs1 hlogq.le
    linarith [h1, h2]
  have hρ'pt : |1 - ρ₀.re| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have hlt : 0 < 1 - ρ₀.re := by linarith [hρ0re1]
    rw [abs_of_pos hlt]
    have heq : 1 - ρ₀.re = Work.LinnikContract.lamOf q ρ₀ / Real.log (q:ℝ) := by
      rw [Work.LinnikContract.lamOf]; field_simp
    rw [heq]
    have hsqn : (0:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_nonneg _
    have h2 : Work.LinnikContract.lamMax q ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
      rw [Work.LinnikContract.lamMax]; linarith [hLLL, hsqn]
    have h1 : Work.LinnikContract.lamOf q ρ₀ / Real.log (q:ℝ)
        ≤ Work.LinnikContract.lamMax q / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right hcap hlogq.le
    have h3 : Work.LinnikContract.lamMax q / Real.log (q:ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      div_le_div_of_nonneg_right h2 hlogq.le
    linarith [h1, h3]
  have hres := hT q hqT χ₁ hχ1 hsq (β₁ := ρ₁.re) (ρ' := ρ₀) hβ1 hβ0 hHb hγ10 hβ1pt hρ'pt
    hdiv1 hdiv0 hne' hmult1 hmaxL hrect1 hcap H
  rwa [← hρ1eq] at hres

/-- **HB's Lemma 8.1 in the §6 rectangle, at an arbitrary box height.**  This is the "capped"
form (the second zero `ρ₀` lies in HB's rectangle (6.1), i.e. `λ(ρ₀) ≤ lamMax q`), generalised
from the box `|Im| ≤ 2` of `HB81_capped` to an arbitrary height `Hb`:

* `ρ₀` is `λ`-minimal in the box `|Im| ≤ Hb` (HB's §6 maximality at that height),
* `|ρ₀.im| + 1 ≤ Hb`: `ρ₀` is at least `1` inside the box, so that its whole §6 window (radius
  `δ < 1`) is covered by the maximality,
* `|ρ₀.im| ≤ 10 log q`: the height up to which the log-derivative input `L52Hyp` applies.

The threshold `q₀` does **not** depend on `Hb` (`dhTrianglePtH` takes the box height as a
hypothesis, not as a quantifier).  `Hb = 2` with `ρ₀ ∈ IsZ` recovers `HB81_capped`. -/
theorem HB81_capped_wide (Hb : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → ρ₀ ≠ ρ₁ →
    (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb → u ≠ ρ₁ →
      Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) →
    |ρ₀.im| + 1 ≤ Hb → |ρ₀.im| ≤ 10 * Real.log (q : ℝ) →
    Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 5 → 4 * Real.exp 1 ≤ Work.LinnikContract.lamOf q ρ₀ →
    Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamMax q →
    (2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ Work.LinnikContract.lamOf q ρ₀ := by
  intro ε hε
  by_cases hε2 : 2 ≤ ε
  · refine ⟨2, fun q hq _inst χ₁ ρ₁ ρ₀ hmin hsq him hzm0 hne hmax0 hHb1 hγ10 h15 h4e hcap => ?_⟩
    have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
    have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
    obtain ⟨-, -, hlam1pos⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq hχ1 hzm1
    have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := by linarith [h4e, Real.exp_pos 1]
    have hLpos : 0 < Real.log (1 / Work.LinnikContract.lamOf q ρ₁) := by
      apply Real.log_pos
      rw [one_div, one_lt_inv₀ hlam1pos]
      linarith [h15]
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le) hlam0pos.le
  · push_neg at hε2
    set εs : ℝ := ε / 256 with hεsdef
    set εL : ℝ := ε / 256 with hεLdef
    set ec : ℝ := 2 * εs + 3.5 * εL with hecdef
    have hεs : 0 < εs := by rw [hεsdef]; positivity
    have hεL : 0 < εL := by rw [hεLdef]; positivity
    have hec0 : 0 ≤ ec := by rw [hecdef]; positivity
    have hsmall : 8 * (2 - ε) * ec ≤ ε := by
      rw [hecdef, hεsdef, hεLdef]; nlinarith [hε, hε2.le]
    have hsmall4 : 4 * (2 - ε) * ec ≤ ε := by linarith [hsmall]
    obtain ⟨δ, hδ0, hδ1, qL52, hL52⟩ := HB81_l52_shift εs hεs εL hεL
    obtain ⟨N, hN⟩ := exists_nat_ge (8 / ε)
    set K : ℕ := N + 1 with hKdef
    have hexp1 : (1:ℝ) ≤ Real.exp 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
    have hXK : 4 * (2 - ε) / ε ≤ 4 * Real.exp 1 * 2 ^ K := by
      rw [hKdef]
      have h2 : (N:ℝ) ≤ (2:ℝ)^N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := N)))
      have hmono : (2:ℝ)^N ≤ (2:ℝ)^(N+1) :=
        calc (2:ℝ)^N ≤ (2:ℝ)^N * 2 := le_mul_of_one_le_right (by positivity) (by norm_num)
          _ = (2:ℝ)^(N+1) := by ring
      have h8 : 8 / ε ≤ (2:ℝ)^(N+1) := by linarith [hN, h2, hmono]
      have h4' : 4 * (2 - ε) / ε ≤ 8 / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        nlinarith [hε2.le]
      have hpos : (0:ℝ) < 2 ^ (N + 1) := by positivity
      have hle : 8 / ε ≤ 4 * Real.exp 1 * 2 ^ (N + 1) := by nlinarith [h8, hexp1, hpos]
      linarith [h4', hle]
    let xOf : ℕ → ℝ := fun k => 1 / 2 + 1 / (4 * Real.exp 1 * 2 ^ k) + 2 * ec
    have hxOf : ∀ k, 0 < xOf k := fun k => by simp only [xOf]; positivity
    have hTgen : ∀ k : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] (ρ₁ ρ₀ : ℂ),
          Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
          Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → ρ₀ ≠ ρ₁ →
          (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ Hb → u ≠ ρ₁ →
            Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) →
          |ρ₀.im| + δ ≤ Hb → |ρ₀.im| ≤ 10 * Real.log (q : ℝ) →
          Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 100 →
          Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamMax q →
          Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + εs - εL / 4) εL δ →
          0 ≤ 2 * (∫ t in (0:ℝ)..xOf k, Real.exp (Work.LinnikContract.lamOf q ρ₀ * t) * (xOf k - t))
            - 2 * (∫ t in (0:ℝ)..xOf k, Real.exp ((Work.LinnikContract.lamOf q ρ₀
                - Work.LinnikContract.lamOf q ρ₁) * t) * (xOf k - t))
            - xOf k ^ 2 / 2 + (2 * (1 / 8 + εs - εL / 4) + 4 * εL) * xOf k :=
      fun k => HB81_triangle_local (xOf k) (hxOf k) εL hεL δ hδ0 hδ1 (1 / 8 + εs - εL / 4) Hb
    choose qT hqT using hTgen
    refine ⟨max (Finset.sup (Finset.range (K + 1)) qT) (max qL52 2), ?_⟩
    intro q hq _inst χ₁ ρ₁ ρ₀ hmin hsq him hzm0 hne hmax0 hHb1 hγ10 h15 h4e hcap
    haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    have hχ1 : χ₁ ≠ 1 := hmin.1.1.1
    have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
    have hHb : |ρ₀.im| + δ ≤ Hb := by linarith [hHb1, hδ1]
    have hq2 : 2 ≤ q := by
      have h' : max qL52 2 ≤ q := le_trans (le_max_right _ _) hq
      omega
    obtain ⟨-, -, hlam1pos⟩ := Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ1 hzm1
    have hH : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1 / 8 + εs - εL / 4) εL δ :=
      hL52 q (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hq)) χ₁ hχ1 hsq
    by_cases h100 : Work.LinnikContract.lamOf q ρ₁ < 1 / 100
    · have hLam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := by linarith [h4e, Real.exp_pos 1]
      rcases HB81_cover (Work.LinnikContract.lamOf q ρ₀) h4e K with ⟨k, hkK, hk1, hk2⟩ | hKle
      · have hkk : k < K + 1 := by omega
        have hqk : qT k ≤ q := le_trans (Finset.le_sup (Finset.mem_range.mpr hkk))
          (le_trans (le_max_left _ _) hq)
        have h6 := hqT k q hqk χ₁ ρ₁ ρ₀ hmin hsq him hzm0 hne hmax0 hHb hγ10 h100.le hcap hH
        have hbk := hb81_logBound (x₀ := xOf k) (X := 4 * Real.exp 1 * 2 ^ k)
          (εx := ec) (εc := ec) (C := 2 * (1 / 8 + εs - εL / 4) + 4 * εL)
          (by positivity) hLam0pos hlam1pos hec0 (by simp only [xOf])
          (by rw [hecdef]; ring) le_rfl h6
        have hk2' : Work.LinnikContract.lamOf q ρ₀ ≤ 2 * (4 * Real.exp 1 * 2 ^ k) := by
          have heq : (4:ℝ) * Real.exp 1 * 2 ^ (k + 1) = 2 * (4 * Real.exp 1 * 2 ^ k) := by
            rw [pow_succ]; ring
          linarith [hk2, heq]
        exact HB81_cell_arith ε ec hε hε2.le hec0 hsmall4 (4 * Real.exp 1 * 2 ^ k)
          (by have hk' : (1:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast (Nat.one_le_two_pow (n := k))
              nlinarith [hk', Real.exp_pos 1])
          (Work.LinnikContract.lamOf q ρ₀) (Work.LinnikContract.lamOf q ρ₁)
          hk1 hk2' hlam1pos (by simpa only [xOf] using hbk)
      · have hkk : K < K + 1 := by omega
        have hqk : qT K ≤ q := le_trans (Finset.le_sup (Finset.mem_range.mpr hkk))
          (le_trans (le_max_left _ _) hq)
        have h6 := hqT K q hqk χ₁ ρ₁ ρ₀ hmin hsq him hzm0 hne hmax0 hHb hγ10 h100.le hcap hH
        have hbk := hb81_logBound (x₀ := xOf K) (X := 4 * Real.exp 1 * 2 ^ K)
          (εx := ec) (εc := ec) (C := 2 * (1 / 8 + εs - εL / 4) + 4 * εL)
          (by positivity) hLam0pos hlam1pos hec0 (by simp only [xOf])
          (by rw [hecdef]; ring) le_rfl h6
        exact HB81_tail_arith ε ec hε hε2.le hec0 hsmall (4 * Real.exp 1 * 2 ^ K)
          (by have hk' : (1:ℝ) ≤ (2:ℝ)^K := by exact_mod_cast (Nat.one_le_two_pow (n := K))
              nlinarith [hk', Real.exp_pos 1])
          hXK (Work.LinnikContract.lamOf q ρ₀) (Work.LinnikContract.lamOf q ρ₁)
          hKle hlam1pos (by simpa only [xOf] using hbk)
    · push_neg at h100
      have hLle : Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ Real.log 100 := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hlam1pos]; linarith [h100]
      have hLnn : 0 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₁) := by
        apply Real.log_nonneg
        rw [one_div, one_le_inv₀ hlam1pos]; linarith [h15]
      have h5 : Real.log 100 ≤ 5 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have he5 : Real.exp 5 = (Real.exp 1) ^ 5 := by
          rw [show (5:ℝ) = ((5:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
        rw [he5]
        calc (100:ℝ) ≤ (2.7182818283)^5 := by norm_num
          _ ≤ (Real.exp 1)^5 := pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 5
      have h10 : (10:ℝ) ≤ 4 * Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
      have h1 : (2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ 2 * Real.log 100 := by
        have h2 : (2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁)
            ≤ 2 * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) :=
          mul_le_mul_of_nonneg_right (by linarith [hε]) hLnn
        have h3 : 2 * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ 2 * Real.log 100 :=
          mul_le_mul_of_nonneg_left hLle (by norm_num)
        linarith [h2, h3]
      linarith [h1, h5, h10, h4e]

/-- **The box-`2` case of the triangle engine** (the form used before the strip-provision route):
a zero `ρ₀ ∈ IsZ` of `χ₁`, `λ`-minimal in the box `|Im| ≤ 2`, with `λ₁ ≤ 1/5` and
`4e ≤ λ(ρ₀) ≤ lamMax q`, satisfies `(2-ε) log(1/λ₁) ≤ λ(ρ₀)`. -/
theorem HB81_capped : ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    Work.LinnikContract.IsZ χ₁ ρ₀ → ρ₀ ≠ ρ₁ →
    (∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 2 → u ≠ ρ₁ →
      Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q u) →
    Work.LinnikContract.lamOf q ρ₁ ≤ 1 / 5 → 4 * Real.exp 1 ≤ Work.LinnikContract.lamOf q ρ₀ →
    Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamMax q →
    (2 - ε) * Real.log (1 / Work.LinnikContract.lamOf q ρ₁) ≤ Work.LinnikContract.lamOf q ρ₀ := by
  intro ε hε
  obtain ⟨q₀, hq₀⟩ := HB81_capped_wide 2 ε hε
  obtain ⟨qL, hL⟩ := Work.LinnikAreas.log_unbounded_nat (max 3 (1/10))
  refine ⟨max q₀ (max qL 2), ?_⟩
  intro q hq _inst χ₁ ρ₁ ρ₀ hmin hsq him hZ hne hmax0 h15 h4e hcap
  have hq₀' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hqL : qL ≤ max qL 2 := le_max_left _ _
  have hqL' : qL ≤ q := le_trans hqL (le_trans (le_max_right q₀ (max qL 2)) hq)
  have hq2 : 2 ≤ q :=
    le_trans (le_max_right qL 2) (le_trans (le_max_right q₀ (max qL 2)) hq)
  have hlog3 : (3:ℝ) ≤ Real.log (q:ℝ) :=
    le_trans (le_max_left (3:ℝ) (1/10)) (hL q hqL')
  exact hq₀ q hq₀' χ₁ ρ₁ ρ₀ hmin hsq him hZ.2.1 hne hmax0
    (by linarith [hZ.2.2])
    (by linarith [hZ.2.2, hlog3]) h15 h4e hcap

end

end Work.ZeroFreeTables
