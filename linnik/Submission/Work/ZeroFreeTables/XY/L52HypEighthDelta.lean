/-
# `L52HypEighthDelta` — the repaired spec for Heath-Brown's Lemma 3.1 at the constant `1/8`

`Work.ZeroFreeTables.XY.L52HypEighth` asked for `L52Hyp χ (1/8) ε δ` for *every* `δ ∈ (0,1)`.
That is not what the mathematics provides: the only source of the constant `1/8` is HB Lemma 3.1
with the exponent `φ = 1/4` (HB Lemma 2.5, Burgess), and in that argument the window radius is
*produced*, not prescribed — HB's proof (hb92x.txt, p. 13–15) fixes `δ = min(1/(2k), ε₀/(3c₀k²))`
with `k = 3 + [3φ/(2ε₀)]`, so `δ < R ≤ 1/k ≤ 1/3` and `δ` shrinks with the slack `ε₀`.  Indeed
`L52Hyp_mono` (proved in this workspace) shows the window sum is *monotone* in `δ`, so the
`∀δ ∈ (0,1)` form is equivalent to its `δ → 1` case, where the window sum alone is
`≍ (δ/π)·log q` by Riemann–von Mangoldt while the log-derivative has average `O(1)` — false.

This file lands the positive replacement: the **δ-existential** form, exactly the shape used by
`L52Hyp_ord_le` / `l52HypReal_fixed` / `HB82.l52HypRealQuarter`, but keeping the constant `1/8`
*exactly* (and covering imprimitive `χ`, i.e. stating the bound at the level `q` rather than at the
conductor).  Two forms are provided:

* `L52HypEighth_delta` — for each `ε > 0` there are `δ ∈ (0,1)` and `q₀` with
  `L52Hyp χ (1/8) ε δ` for every real non-principal `χ` mod `q ≥ q₀`;
* `L52HypEighth_fixedDelta` — a *single* `δ` serves the whole range `ε ∈ [1/25000, 1]`, which is
  the form a consumer needs in order to place its zeros inside the window (Xylouris Lemma 3.4).

Both are obtained from `Work.LinnikAreas.l31free.lemma3_1_free_gen_real` with `φ = 1/4` (the
analytic input being the `χ * χ = 1` shape of HB Lemma 2.5, supplied below as
`hbound_quarter_real`), by instantiating its free `L` at `L = log q` so that the region and the
right-hand side are those of `L52Hyp` at level `q`.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.area1
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity

open DirichletCharacter

set_option maxHeartbeats 1000000

namespace Work.ZeroFreeTables.XY

/-! ## Two elementary transfers -/

/-- A non-principal character has level at least `3` (for `N ≤ 2` the unit group is trivial, so
every character is principal). -/
lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN2 : N ≤ 2 := by omega
  have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
    intro hh
    exact hχ (MulChar.ext hh)
  push Not at hχne
  rcases hχne with ⟨a, hne⟩
  have hs : Subsingleton (ZMod N)ˣ := by interval_cases N <;> infer_instance
  have ha : a = 1 := Subsingleton.elim a 1
  subst a
  simp at hne

/-- For a real character the primitive character inducing it is again real. -/
lemma primitiveCharacter_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
      (χ.primitiveCharacter ^ 2) = 1 := by
    rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h]
  exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
    (by rw [hmap, DirichletCharacter.changeLevel_one])

/-! ## HB Lemma 2.5 with `φ = 1/4` for real characters -/

/-- **Heath-Brown Lemma 2.5 with exponent `φ = 1/4` for real characters**, in the shape
`χ ≠ 1 → χ ^ 2 = 1 → …` consumed by `Work.LinnikAreas.l31free.lemma3_1_free_gen_real`.

`Work.LinnikAreas.LBoundSmall_holds` (Burgess character sums, cube-free moduli) supplies this
bound for characters of order `≤ log N`.  A real non-principal character has `orderOf χ = 2`, so
its hypothesis holds once `log N ≥ 2`, i.e. for `N ≥ 8`.  For `N ≤ 7` the hypothesis need not hold,
but there the *same* exponent `φ = 1/4` is recovered from the convexity bound (exponent `1/2`):
on `1 - 1/k ≤ σ` the two exponents differ by `(1/4)(1-σ)(1+1/k)`, which is `≤ 1/9` when `σ ≤ 1`
and `≤ 0` when `σ ≥ 1`; so the convexity bound only has to be divided by a factor
`N^{(1/4)(1-σ)(1+1/k)} ≤ max (1, 7^(1/9))`, absorbed into the constant. -/
theorem hbound_quarter_real :
    ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) := by
  intro k hk ε' hε'
  obtain ⟨C₁, hC₁pos, hb₁⟩ := Work.LinnikAreas.LBoundSmall_holds k hk ε' hε'
  obtain ⟨C₂, hC₂pos, hb₂⟩ :=
    Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity hε' k hk
  refine ⟨max C₁ (C₂ * 7 ^ ((1:ℝ)/9) * 2), lt_max_of_lt_left hC₁pos, ?_⟩
  intro N _inst χ hχ hχ2 σ t hσ hσle
  have hkpos : (0:ℝ) < (k:ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have h : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact_mod_cast h
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith only [hN1]
  by_cases hN : 8 ≤ N
  · -- `N ≥ 8`: the order hypothesis of `LBoundSmall_holds` is available
    have hord2 : orderOf χ ≤ 2 := by
      have hdvd : orderOf χ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hχ2
      exact Nat.le_of_dvd (by norm_num) hdvd
    have hlog8 : (2:ℝ) ≤ Real.log 8 := by
      have h : Real.log (8:ℝ) = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      rw [h]
      have := Real.log_two_gt_d9
      linarith only [this]
    have hlogN : (2:ℝ) ≤ Real.log (N:ℝ) := by
      have h8 : (8:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      exact le_trans hlog8 (Real.log_le_log (by norm_num) h8)
    have hord : (orderOf χ : ℝ) ≤ Real.log (N:ℝ) := by
      have h2 : (orderOf χ : ℝ) ≤ 2 := by exact_mod_cast hord2
      linarith only [hlogN, h2]
    have h := hb₁ χ hχ hord σ t hσ hσle
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  · -- `N ≤ 7`: the convexity bound (exponent `1/2`) is upgraded to the exponent `1/4` by
    -- absorbing the finite factor `N ^ ((1/4)(1-σ)(1+1/k)) ≤ 7 ^ (1/9)` into the constant
    have hNle7 : N ≤ 7 := by omega
    have hNR : (N:ℝ) ≤ 7 := by exact_mod_cast hNle7
    have hk3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h1σ : (1:ℝ) - σ ≤ 1/(k:ℝ) := by linarith only [hσ]
    have hprod : (1 - σ) * (1 + 1/(k:ℝ)) ≤ 4/9 := by
      by_cases hσ1 : 0 ≤ 1 - σ
      · have h2 : (1:ℝ) + 1/(k:ℝ) ≤ 4/3 := by
          have h : 1/(k:ℝ) ≤ 1/3 := by
            rw [div_le_div_iff₀ hkpos (by norm_num : (0:ℝ) < 3)]
            linarith only [hk3]
          linarith only [h]
        have h3 : (1:ℝ)/(k:ℝ) ≤ 1/3 := by
          rw [div_le_div_iff₀ hkpos (by norm_num : (0:ℝ) < 3)]
          linarith only [hk3]
        have hp : (1 - σ) * (1 + 1/(k:ℝ)) ≤ (1/(k:ℝ)) * (4/3) :=
          mul_le_mul h1σ h2 (by positivity) (by positivity)
        linarith only [hp, h3, h2]
      · have h : (1:ℝ) - σ < 0 := by linarith only [hσ1]
        have hpos : (0:ℝ) < 1 + 1/(k:ℝ) := by positivity
        have hneg : (1 - σ) * (1 + 1/(k:ℝ)) < 0 := mul_neg_of_neg_of_pos h hpos
        linarith only [hneg]
    have hE1 : ((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) ≤ 1/9 := by
      linarith only [hprod]
    have hfac : (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))) ≤ (7:ℝ) ^ ((1:ℝ)/9) := by
      have h1 : (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))) ≤ (N:ℝ) ^ ((1:ℝ)/9) :=
        Real.rpow_le_rpow_of_exponent_le hN1 hE1
      have h2 : (N:ℝ) ^ ((1:ℝ)/9) ≤ (7:ℝ) ^ ((1:ℝ)/9) :=
        Real.rpow_le_rpow (le_of_lt hNpos) hNR (by norm_num)
      linarith only [h1, h2]
    have h := hb₂ χ hχ σ t hσ hσle
    have hexp : ((1:ℝ)/2) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'
        = ((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))
          + (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by ring
    rw [hexp, Real.rpow_add hNpos] at h
    have hz : (0:ℝ) ≤ (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
      Real.rpow_nonneg (le_of_lt hNpos) _
    have ht : (0:ℝ) ≤ 1 + |t| := by positivity
    have h7 : (0:ℝ) ≤ (7:ℝ) ^ ((1:ℝ)/9) := Real.rpow_nonneg (by norm_num) _
    have hkey : C₂ * ((N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)))
          * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'))
        ≤ (max C₁ (C₂ * 7 ^ ((1:ℝ)/9) * 2))
          * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by
      have hC₂nn : (0:ℝ) ≤ C₂ := le_of_lt hC₂pos
      calc C₂ * ((N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε'))
          = (C₂ * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ))))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') := by ring
        _ ≤ (C₂ * (7:ℝ) ^ ((1:ℝ)/9))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hC₂nn) hz
        _ ≤ (C₂ * 7 ^ ((1:ℝ)/9) * 2)
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (by linarith only [mul_nonneg hC₂nn h7, hC₂nn, h7]) hz
        _ ≤ (max C₁ (C₂ * 7 ^ ((1:ℝ)/9) * 2))
            * (N:ℝ) ^ (((1:ℝ)/4) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hz
    exact h.trans (mul_le_mul_of_nonneg_right hkey ht)

/-! ## The repaired statements -/

/-- **HB Lemma 3.1 with the constant `1/8` for real characters, in δ-existential form.**
For every `ε > 0` there are `δ ∈ (0,1)` and a threshold `q₀` such that every real non-principal
`χ` mod `q ≥ q₀` satisfies `L52Hyp χ (1/8) ε δ` — i.e. the window radius is *produced* by the
argument (as it must be), while the constant stays exactly `1/8`.  The statement is at the level
`q` (not the conductor), so it applies to imprimitive `χ` as well; the freedom of `L` in
`lemma3_1_free_gen_real` is what transfers it from the conductor to the level. -/
theorem L52HypEighth_delta {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
        χ ≠ 1 → χ * χ = 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/8) ε δ := by
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen_real (φ := (1:ℝ)/4) (by norm_num)
      (ε := ε/8) (by positivity) hbound_quarter_real
  refine ⟨δ, hδ0, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ hreal
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hχ2 : χ ^ 2 = 1 := by rw [pow_two]; exact hreal
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := three_le_of_char_ne_one χ.primitiveCharacter hχ'
  have hconle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith only [hδ0, hδ1]
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith only [h1, h2, h3]
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hlogNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast hconle
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (primitiveCharacter_sq_one χ hχ2)
    (L := Real.log (q : ℝ)) hL₀le hlogNle
  intro s hs1 hs2 hs3
  refine (hmain' s hs1 hs2 hs3).trans ?_
  have hlogq : (0:ℝ) ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply mul_le_mul_of_nonneg_right _ hlogq
  linarith only [hε]

/-- **The same bound with a *single* window radius, uniform on a range of slacks.**
There are `δ ∈ (0,1)` and `q₀` such that every real non-principal `χ` mod `q ≥ q₀` satisfies
`L52Hyp χ (1/8) ε δ` for *all* `ε ∈ [1/25000, 1]`.  A consumer that has to know its window (in
order to locate its zeros inside it, as in Xylouris's Lemma 3.4) can therefore take `δ` once and
cover the whole range of slacks it needs — including the value `ε = 1/10000` used in the `XY`
assembly.  The price is the internal slack `10⁻⁵`, which is `≤ ε/4` exactly on `ε ≥ 1/25000`. -/
theorem L52HypEighth_fixedDelta :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
        χ ≠ 1 → χ * χ = 1 → ∀ ε : ℝ, 1/25000 ≤ ε → ε ≤ 1 →
          Commons.NumberTheory.Linnik.L52Hyp χ (1/8) ε δ := by
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen_real (φ := (1:ℝ)/4) (by norm_num)
      (ε := 1/100000) (by norm_num) hbound_quarter_real
  refine ⟨δ, hδ0, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ hreal ε hεlo hεhi
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hχ2 : χ ^ 2 = 1 := by rw [pow_two]; exact hreal
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := three_le_of_char_ne_one χ.primitiveCharacter hχ'
  have hconle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith only [hδ0, hδ1]
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith only [h1, h2, h3]
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hlogNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast hconle
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (primitiveCharacter_sq_one χ hχ2)
    (L := Real.log (q : ℝ)) hL₀le hlogNle
  intro s hs1 hs2 hs3
  refine (hmain' s hs1 hs2 hs3).trans ?_
  have hlogq : (0:ℝ) ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  apply mul_le_mul_of_nonneg_right _ hlogq
  linarith only [hεlo]

end Work.ZeroFreeTables.XY
