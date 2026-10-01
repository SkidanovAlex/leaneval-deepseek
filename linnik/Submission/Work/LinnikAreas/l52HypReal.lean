import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.LinnikAreas.l31free.hbound_third_real

namespace Work.LinnikAreas

open DirichletCharacter

/-- A non-principal character has level at least `3` (for `N ≤ 2` the unit group is trivial, so
every character is principal). -/
private lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
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
private lemma primitiveCharacter_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
      (χ.primitiveCharacter ^ 2) = 1 := by
    rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h]
  exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
    (by rw [hmap, DirichletCharacter.changeLevel_one])

-- PROOF NOTE (not part of the statement).  This is HB Lemma 3.1 for real characters with the
-- sharp exponent `φ = 1/3`, giving the constant `1/6 + 10⁻⁶` of Lemma 5.2 (the slack is fixed
-- because the statement's own `ε` only enters additively, so one `δ` and one threshold `q₀` serve
-- every `ε ∈ (0,1]`).
--
-- Route (all pieces already proved in this workspace, none depending on the sixth moment for
-- moduli divisible by a cube, which is still in flight elsewhere):
--   * `Work.LinnikAreas.l31free.hbound_third_real`: HB Lemma 2.5 with `φ = 1/3` for characters
--     with `χ ^ 2 = 1`.  HB §2: the cube-free-moduli Burgess bound `cubefree_charSum_all_k`
--     (sorry-free, `Work.LinnikAreas.area1`) plus the cubeful-part order factor
--     `(orderOf χ)^{3/(2k)}` of `burgess_charSum_order_of_cubefree` (at `k = 3` this factor is
--     `√2 ≪ 1` for `orderOf χ ≤ 2`), then the §2 accumulation `(2.2)`–`(2.4)`
--     (`Commons…primitive_LFunction_bound`) and the non-primitive/`σ ≥ 1` reduction.
--   * `Work.LinnikAreas.l31free.lemma3_1_free_gen_real`: HB Lemma 3.1 in the threshold-uniform
--     shape needed by Lemma 5.2 (`|Im s| ≤ 10 log q`), restricted to real characters.
-- The same file also contains `Work.LinnikAreas.l31free.lemma3_1_free_gen` (the unrestricted
-- `φ`-free form) and `Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity` (the `φ = 1/2`
-- L-bound from convexity), which give the same statement with `1/4 + 10⁻⁶` without using the
-- real-character hypothesis at all.
/-- **HB Lemma 3.1 for real characters, in the shape required by Lemma 5.2** (HB (1992) Lemma 3.1, available as `Commons.NumberTheory.Linnik.lemma3_1`; the extra input is the L-function bound of HB Lemma 2.5 near `σ = 1`, supplied by `Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess` (no sorry), used via `Work.LinnikAreas.A5.hH_provider hφ1 hφ2 hε hBurg` with `φ = 1/3`). -/
theorem l52HypReal : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
    χ ≠ 1 → χ ^ 2 = 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      Commons.NumberTheory.Linnik.L52Hyp χ c ε δ := by
  -- HB Lemma 2.5 with exponent `φ = 1/3` and `ε = 1/1000000`, for real characters: the cube-free
  -- Burgess bound together with the order factor `(orderOf χ)^{3/(2k)}` of the cubeful part of the
  -- modulus (HB §2, Lemmas 2.1/2.3/2.4) suffices, so the sixth moment for moduli divisible by a
  -- cube is *not* needed here.
  have hBurg : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/3) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) :=
    fun k hk ε' hε' => l31free.hbound_third_real hε' k hk
  -- HB Lemma 3.1 (threshold-uniform form) with the *fixed* slack `ε = 1/1000000`: the statement's
  -- own `ε` enters only additively in the constant, so this single `δ` serves every `ε ∈ (0,1]`.
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    l31free.lemma3_1_free_gen_real (φ := (1:ℝ)/3) (by norm_num) (ε := 1/1000000) (by norm_num) hBurg
  refine ⟨1/6 + 1/1000000, by norm_num, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ1 hχ2 ε hε _hε1
  refine ⟨δ, hδ0, hδ1, ?_⟩
  intro s hs1 hs2 hs3
  -- thresholds coming from `q₀ = ⌈exp L₀⌉₊ + 3 ≤ q`
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by
      push_cast; linarith
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hlogNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hχstar : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ1
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := three_le_of_char_ne_one χ.primitiveCharacter hχstar
  -- instantiate HB Lemma 3.1 at the primitive character inducing `χ`, with `L = log q`
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (primitiveCharacter_sq_one χ hχ2)
    (L := Real.log (q : ℝ)) hL₀le hlogNle s hs1 hs2 hs3
  refine hmain'.trans ?_
  have hlogq : (0:ℝ) ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  apply mul_le_mul_of_nonneg_right _ hlogq
  linarith only [hε]

end Work.LinnikAreas
