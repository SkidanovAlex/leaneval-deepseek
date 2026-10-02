/-
# `Work.OffAxis.Rect10_3AllReal`

**HB (1992) Lemma 10.3 at rectangle height `L`, the case in which all three characters are
real and the numbered zero `ρ₁` is real** — Heath-Brown's §10 *case 3*, i.e. the `P₃` method
((10.13)/(10.14)), run at rectangle height `L`.

The hypotheses are HB's §6 numbering at height `L` (`IsRectMin L χ₁ ρ₁` and the two successive
minimum conditions), the case-3 character data `χⱼ² = 1`, `χ₁χ₂χ₃ = 1`, and the realness of `ρ₁`
(`ρ₁.im = 0`); the conclusion is `λ₃ ≥ 6/7 - ε`, in the workspace's contradiction form (the
last hypothesis `λ₃ ≤ 6/7 - ε` is what allows the `ρ₃`-term to be dropped).

The mathematical content is the height-`L` transcription of `HBLemma10_3_engine_proof`:
the three single and six pair `P₃`-extractions are the rectangle-height extraction
(`Work.OffAxis.SigmaP3L_extract_at_rect`, its at-the-zero form below), the principal-character
terms come from the height-`3L` principal bound `RectRepPrincipal`, HB's Lemma 3.1 feed at
`φ = 1/4` is `HB95h2.logDerivEighth`, and the rest of the ledger (the `P₃*` collapse, the
fourteen-term weighted combination and HB (10.14)) is height-free and reused verbatim.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.HBLemma10_3_engine_proof
import Submission.Work.ZeroFreeTables.OffAxis.RepHMisc
import Submission.Work.ZeroFreeTables.OffAxis.RepHMaster
import Submission.Work.ZeroFreeTables.OffAxis.RectRepPrincipal
import Submission.Work.ZeroFreeTables.OffAxis.nearP3sum_ge_kept_R

namespace Work.OffAxis

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

open Work.LinnikContract
open Work.ZeroFreeTables (P3 P3R p1014)

set_option maxHeartbeats 4000000

/-! ## The rectangle-height extraction

We prove the height-`L` extraction directly from the height-parametric pieces
`Rep9.masterP3H` (the `P₃` master bound at height `H`), `Rep9.imprimCorrBoundedH` (passage to the
primitive character) and `OffAxis.nearP3sum_ge_kept_R` (the height-`R` dropping rule).  The
rectangle height is taken **before** the engine thresholds precisely because those lemmas carry
the height as a parameter. -/

/-- **The single-zero extraction at height `R`.** -/
theorem shifted_extract_rect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive)
    {a δ c e lam1 lam L τ R : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 0 < L) (ha : 0 < a)
    (hlam1 : 0 ≤ lam1) (hlam : 0 ≤ lam) (haδ : 2 * a ≤ δ * L) (hτ : |τ| ≤ R)
    {ρ : ℂ} (hzero : Work.LinnikContract.zeroMult χ ρ ≠ 0) (him : |ρ.im| ≤ R + 1)
    (hre : ρ.re = 1 - lam / L)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ R + 1 →
      lam1 ≤ (1 - u.re) * L)
    (hm : Work.ZeroFreeTables.SigmaP3L N L χ
        (((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1
      ≤ -Work.ZeroFreeTables.P3NearSumL N L χ
          (((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1 δ
        + (a + lam1) * (c + e)) :
    Work.ZeroFreeTables.SigmaP3L N L χ
        (((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1
      ≤ -(Work.ZeroFreeTables.P3
            ((a + lam1) / (((a + lam : ℝ) : ℂ)
              + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I))).re
        + 8 * (a + lam1) / (δ * L) + (a + lam1) * (c + e) := by
  classical
  set s : ℂ := ((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : s.re = 1 + a / L := by
    rw [hs]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hsim : |s.im| ≤ R := by
    have h : s.im = τ := by
      rw [hs]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [h]; exact hτ
  have hT : ∀ u ∈ ({ρ} : Finset ℂ), Work.LinnikContract.zeroMult χ u ≠ 0 := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    rw [hu]; exact hzero
  have hTim : ∀ u ∈ ({ρ} : Finset ℂ), |u.im| ≤ R + 1 := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    rw [hu]; exact him
  have hkey := Work.ZeroFreeTables.OffAxis.nearP3sum_ge_kept_R χ hχ hL ha hlam1 hδ hδ1 haδ
    hsre hsim hmin ({ρ} : Finset ℂ) hT hTim
  rw [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hkey
  have harg : (a + lam1) / ((s - ρ) * (L : ℂ))
      = (a + lam1) / (((a + lam : ℝ) : ℂ)
          + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I) := by
    congr 1
    have hρ : ρ = ((1 - lam / L : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I := by
      rw [← Complex.re_add_im ρ, hre]
      simp
    have hLne : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL
    conv_lhs => rw [hs, hρ]
    push_cast
    field_simp
    ring
  have hPtTgt : (Work.ZeroFreeTables.P3 ((a + lam1) / ((s - ρ) * (L : ℂ)))).re
      = (Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam : ℝ) : ℂ)
          + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I))).re := by
    rw [harg]
  have hnear : Work.ZeroFreeTables.P3NearSumL N L χ s a lam1 δ
      = Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam1 δ :=
    Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum (s := s) χ hχ hprim hδ hδ1.le a lam1 L
  have h1 : -Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam1 δ
      ≤ -(Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lam : ℝ) : ℂ)
            + (((τ - ρ.im) * L : ℝ) : ℂ) * Complex.I))).re
        + 8 * (a + lam1) / (δ * L) := by
    rw [← hPtTgt]
    linarith [hkey]
  rw [hnear] at hm
  linarith [hm, h1]

/-- **Extraction of a single zero from the `P₃` near-zero sum, rectangle-height form.** -/
theorem SigmaP3L_extract_at_rect_L {a δ e : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (he : 0 < e) :
    ∀ L : ℝ, 1 ≤ L → ∃ Lm Li : ℝ,
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hreal : χ ^ 2 = 1) (ρ : ℂ) (lam1 lamχ τ : ℝ),
      2 ≤ q → Lm ≤ Real.log (q : ℝ) → Li ≤ Real.log (q : ℝ) →
      3 * L ≤ Real.log (q : ℝ) →
      2 * a ≤ δ * Real.log (q : ℝ) →
      (∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), N ≤ q → ψ ≠ 1 → ψ.IsPrimitive →
        ψ ^ 2 = 1 → Work.ZeroFreeTables.LogDerivHyp ψ δ (Real.log (q : ℝ)) (1 / 8 + e / 3)) →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ L → |τ| ≤ 3 * L →
      ρ.re = 1 - lamχ / Real.log (q : ℝ) → 0 ≤ lam1 → lam1 ≤ 1 →
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 * L →
        lam1 ≤ (1 - u.re) * Real.log (q : ℝ)) →
      Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) χ
        (((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1
      ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lamχ : ℝ) : ℂ)
              + (((τ - ρ.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * (a + lam1) / (δ * Real.log (q : ℝ)) + (a + lam1) * (1 / 8 + e) := by
  intro L hL1
  obtain ⟨Lm, hm⟩ := Work.ZeroFreeTables.P9.prim.masterP3H (a := a) (δ := δ)
    (c := 1 / 8 + e / 3) (e := e / 3) (H := 3 * L) ha hδ0 hδ1 (by positivity) 1
  obtain ⟨Li, hi⟩ := Work.ZeroFreeTables.Rep9.imprimCorrBoundedH (a := a) (e := e / 3) (M := 1)
    (H := 3 * L) ha (by positivity) (by norm_num)
  refine ⟨Lm, Li, ?_⟩
  intro q _inst χ hχ hreal ρ lam1 lamχ τ hq2 hLm hLi h3L h2aδ hfeed hρ hρim hτ hre
    hlam1 hlam1le hmin
  have hLpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hconpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcondle : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hlogN : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hconpos) (by exact_mod_cast hcondle)
  have hχ'ne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hχ'sq : χ.primitiveCharacter ^ 2 = 1 := by
    have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
        (χ.primitiveCharacter ^ 2) = 1 := by
      rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, hreal]
    exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
      (by rw [hmap, DirichletCharacter.changeLevel_one])
  have hprim' : (χ.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hLD : Work.ZeroFreeTables.LogDerivHyp χ.primitiveCharacter δ (Real.log (q : ℝ))
      (1 / 8 + e / 3) :=
    hfeed χ.primitiveCharacter hcondle hχ'ne hprim' hχ'sq
  set s : ℂ := ((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : s.re = 1 + a / Real.log (q : ℝ) := by
    rw [hs]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hsim : |s.im| ≤ 3 * L := by
    have h : s.im = τ := by
      rw [hs]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [h]; exact hτ
  have hlogqne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hLpos
  have hρle : lam1 ≤ lamχ := by
    have h := hmin ρ hρ (le_trans hρim (by linarith))
    have hsimp : (1 - (1 - lamχ / Real.log (q : ℝ))) * Real.log (q : ℝ) = lamχ := by
      rw [sub_sub_cancel, div_mul_cancel₀ _ hlogqne]
    rw [hre] at h
    linarith [h, hsimp]
  have hlamχnn : 0 ≤ lamχ := le_trans hlam1 hρle
  have hρimR : |ρ.im| ≤ 3 * L + 1 := by linarith
  have hzero' : Work.LinnikContract.zeroMult χ.primitiveCharacter ρ ≠ 0 := by
    rw [Work.ZeroFreeTables.XY.zeroMult_primitiveCharacter_eq χ ρ]; exact hρ
  have hmin' : ∀ u : ℂ, Work.LinnikContract.zeroMult χ.primitiveCharacter u ≠ 0 →
      |u.im| ≤ 3 * L + 1 → lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [Work.ZeroFreeTables.XY.zeroMult_primitiveCharacter_eq χ u] at hu
    exact hmin u hu (le_trans him (by linarith))
  have hmaster : Work.ZeroFreeTables.SigmaP3L χ.conductor (Real.log (q : ℝ))
        χ.primitiveCharacter s a lam1
      ≤ -Work.ZeroFreeTables.P3NearSumL χ.conductor (Real.log (q : ℝ))
          χ.primitiveCharacter s a lam1 δ
        + (a + lam1) * (1 / 8 + e / 3 + e / 3) := by
    have h := hm χ.primitiveCharacter hχ'ne hprim' (L := Real.log (q : ℝ)) (lam₁ := lam1)
      hLm hlogN hlam1 hlam1le (by linarith) hLD s hsre hsim
    have heq : (a + lam1) * ((1 / 8 + e / 3) + e / 3)
        = (a + lam1) * (1 / 8 + e / 3 + e / 3) := by ring
    linarith [h, heq]
  have hext := shifted_extract_rect (N := χ.conductor) χ.primitiveCharacter hχ'ne hprim'
    (a := a) (δ := δ) (c := 1 / 8 + e / 3) (e := e / 3) (lam1 := lam1) (lam := lamχ)
    (L := Real.log (q : ℝ)) (τ := τ) (R := 3 * L)
    hδ0 hδ1 hLpos ha hlam1 hlamχnn h2aδ hτ hzero' hρimR hre hmin' hmaster
  have himp := hi χ hχ (L := Real.log (q : ℝ)) (lam₁ := lam1)
    hLi le_rfl hlam1 hlam1le s hsre hsim
  have hring : (a + lam1) * (1 / 8 + e / 3 + e / 3) + (a + lam1) * (e / 3)
      = (a + lam1) * (1 / 8 + e) := by ring
  linarith [himp, hext, hring]

/-- **Extraction at the zero's own point**, rectangle-height form. -/
theorem SigmaP3L_extract_at_zero_rect_L {a δ e : ℝ} (ha : 0 < a) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (he : 0 < e) :
    ∀ L : ℝ, 1 ≤ L → ∃ Lm Li : ℝ,
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hreal : χ ^ 2 = 1) (ρ : ℂ) (lam1 lamχ : ℝ),
      2 ≤ q → Lm ≤ Real.log (q : ℝ) → Li ≤ Real.log (q : ℝ) →
      3 * L ≤ Real.log (q : ℝ) →
      2 * a ≤ δ * Real.log (q : ℝ) →
      (∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), N ≤ q → ψ ≠ 1 → ψ.IsPrimitive →
        ψ ^ 2 = 1 → Work.ZeroFreeTables.LogDerivHyp ψ δ (Real.log (q : ℝ)) (1 / 8 + e / 3)) →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ L →
      ρ.re = 1 - lamχ / Real.log (q : ℝ) → 0 ≤ lam1 → lam1 ≤ 1 →
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 * L →
        lam1 ≤ (1 - u.re) * Real.log (q : ℝ)) →
      Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) χ
        (((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) a lam1
      ≤ -P3R ((a + lam1) / (a + lamχ))
        + 8 * (a + lam1) / (δ * Real.log (q : ℝ)) + (a + lam1) * (1 / 8 + e) := by
  intro L hL1
  obtain ⟨Lm, Li, h⟩ :=
    SigmaP3L_extract_at_rect_L (a := a) (δ := δ) (e := e) ha hδ0 hδ1 he L hL1
  refine ⟨Lm, Li, ?_⟩
  intro q _inst χ hχ hreal ρ lam1 lamχ hq2 hLm hLi h3L h2a hfeed hρ hρim hre hlam1
    hlam1le hmin
  have key := h χ hχ hreal ρ lam1 lamχ ρ.im hq2 hLm hLi h3L h2a hfeed hρ hρim
    (le_trans hρim (by linarith)) hre hlam1 hlam1le hmin
  have harg : ((((ρ.im - ρ.im) * Real.log (q : ℝ)) : ℝ) : ℂ) = 0 := by
    rw [sub_self, zero_mul, Complex.ofReal_zero]
  simp only [harg, zero_mul, add_zero] at key
  have hnum : ((a : ℂ) + (lam1 : ℂ)) = ((a + lam1 : ℝ) : ℂ) := by push_cast; ring
  rw [hnum] at key
  rw [Work.ZeroFreeTables.P3_ofReal_div_eq_P3R] at key
  exact key

/-! ## The case-3 engine at rectangle height `L` -/

/-- **HB (10.13)/(10.14) in case 3 at rectangle height `L`**: the `P₃` combination of the
three real characters at the §6 numbering of height `L` forces `0 ≤ p1014 (λ₁/(6/7)) ε`. -/
theorem Rect10_3AllReal_engine (ε' : ℝ) (hε' : 0 < ε') :
    ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ρ₁.im = 0 →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₃ ^ 2 = 1 → χ₁ * χ₂ * χ₃ = 1 →
      Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      0 < Work.LinnikContract.lamOf q ρ₃ → Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
      0 ≤ Work.ZeroFreeTables.p1014 (Work.LinnikContract.lamOf q ρ₁ / (6/7)) ε' := by
  intro L hL1
  -- the two budgets
  set e1 : ℝ := ε' / 100 with he1def
  have he1pos : 0 < e1 := by rw [he1def]; linarith
  have he13pos : 0 < e1 / 3 := by linarith
  -- HB Lemma 3.1 at `φ = 1/4` with `e = e1/3`
  obtain ⟨L0, δ, hδ0, hδ1, hfeed0⟩ :=
    Work.ZeroFreeTables.HB95h2.logDerivEighth (e := e1 / 3) he13pos
  -- the extractions, with the engine thresholds
  obtain ⟨Lm, Li, hpair⟩ :=
    SigmaP3L_extract_at_rect_L (a := 18/7) (δ := δ) (e := e1) (by norm_num)
      hδ0 hδ1 he1pos L hL1
  obtain ⟨Lz, Lzi, hsingle⟩ :=
    SigmaP3L_extract_at_zero_rect_L (a := 18/7) (δ := δ) (e := e1) (by norm_num)
      hδ0 hδ1 he1pos L hL1
  -- the principal-character bound at height `3L`
  obtain ⟨qP, hP⟩ := Work.ZeroFreeTables.OffAxis.RectRepPrincipal (a := 18/7) (e := e1)
    (M := 1) (H := L) (by norm_num) he1pos (by norm_num) hL1
  -- the joint threshold
  set Lthr : ℝ := max (max L0 (max Lm Lz))
    (max (max Li Lzi) (max (3 * L) (max (48 / (δ * (ε' / 10))) (2 * (18 / 7) / δ))))
    with hLthr
  refine ⟨max 2 (max qP (Nat.ceil (Real.exp Lthr) + 1)), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm hρ₁im hsq1 hsq2 hsq3 hprod hZ2 hZ3
    hχ₂a hχ₂b hχ₃a hχ₃b hχ₃c hχ₃d hlam2le3 hlam3pos hlam3le
  have hq2 : 2 ≤ q := by omega
  have hqP : qP ≤ q := by omega
  have hqE : Nat.ceil (Real.exp Lthr) + 1 ≤ q := by omega
  have hLthrle : Lthr ≤ Real.log (q : ℝ) := by
    have hexp : Real.exp Lthr ≤ (q : ℝ) := by
      have h1 : Real.exp Lthr ≤ ((Nat.ceil (Real.exp Lthr) : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((Nat.ceil (Real.exp Lthr) : ℕ) : ℝ) ≤ (q : ℝ) := by
        have h3 : Nat.ceil (Real.exp Lthr) ≤ q := by omega
        exact_mod_cast h3
      linarith
    have h := Real.log_le_log (Real.exp_pos Lthr) hexp
    rwa [Real.log_exp] at h
  have hcopy := hLthrle
  rw [hLthr] at hcopy
  have hA : max L0 (max Lm Lz) ≤ Real.log (q : ℝ) :=
    le_trans (le_max_left _ _) hcopy
  have hB : max (max Li Lzi) (max (3 * L) (max (48 / (δ * (ε' / 10))) (2 * (18 / 7) / δ)))
      ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hcopy
  have hL0 : L0 ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hA
  have hLm : Lm ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA
  have hLz : Lz ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
  have hLi : Li ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hLzi : Lzi ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hQ : max (3 * L) (max (48 / (δ * (ε' / 10))) (2 * (18 / 7) / δ))
      ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hB
  have h3L : 3 * L ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hQ
  have hR : max (48 / (δ * (ε' / 10))) (2 * (18 / 7) / δ) ≤ Real.log (q : ℝ) :=
    le_trans (le_max_right _ _) hQ
  have hD : 48 / (δ * (ε' / 10)) ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hR
  have h2a : 2 * (18 / 7) / δ ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hR
  have hLpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hLpos
  have hLle : L ≤ Real.log (q : ℝ) := le_trans (by linarith) h3L
  have h2aδ : 2 * (18 / 7 : ℝ) ≤ δ * Real.log (q : ℝ) := by
    have h := (div_le_iff₀ hδ0).mp h2a
    rw [mul_comm (Real.log (q : ℝ)) δ] at h
    exact h
  have hbud : 48 / (δ * Real.log (q : ℝ)) ≤ ε' / 10 := by
    have h' : 48 ≤ Real.log (q : ℝ) * (δ * (ε' / 10)) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < δ * (ε' / 10))).mp hD
    rw [div_le_iff₀ (mul_pos hδ0 hLpos)]
    linarith only [h']
  -- ### the setting: the three `λ`'s
  set lam1 : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlam1def
  set lam2 : ℝ := Work.LinnikContract.lamOf q ρ₂ with hlam2def
  set lam3 : ℝ := Work.LinnikContract.lamOf q ρ₃ with hlam3def
  have hz₁ : Work.ZeroFreeTables.IsZAt L χ₁ ρ₁ := hm.1
  have hz₂ : Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ := hZ2
  have hz₃ : Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ := hZ3
  have hlam10 : 0 ≤ lam1 := by
    rw [hlam1def]
    exact Work.ZeroFreeTables.lamOf_nonneg_of_re_le_one
      (le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hz₁.2.1))
  have hlam20 : 0 ≤ lam2 := by
    rw [hlam2def]
    exact Work.ZeroFreeTables.lamOf_nonneg_of_re_le_one
      (le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₂ hz₂.2.1))
  have hlam30 : 0 ≤ lam3 := by
    rw [hlam3def]
    exact Work.ZeroFreeTables.lamOf_nonneg_of_re_le_one
      (le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₃ hz₃.2.1))
  have hlam12 : lam1 ≤ lam2 := by
    rw [hlam1def, hlam2def]
    exact hm.2 χ₂ ρ₂ ⟨hz₂.1, hz₂.2.1, le_trans hz₂.2.2 (by linarith)⟩
  have hlam13 : lam1 ≤ lam3 := by
    rw [hlam1def, hlam3def]
    exact hm.2 χ₃ ρ₃ ⟨hz₃.1, hz₃.2.1, le_trans hz₃.2.2 (by linarith)⟩
  have hlam23 : lam2 ≤ lam3 := by rw [hlam2def, hlam3def]; exact hlam2le3
  have hlam367 : lam3 ≤ 6 / 7 := by rw [hlam3def]; exact hlam3le
  have hlam267 : lam2 ≤ 6 / 7 := le_trans hlam23 hlam367
  have hlam167 : lam1 ≤ 6 / 7 := le_trans hlam13 hlam367
  have hlam11 : lam1 ≤ 1 := le_trans hlam167 (by norm_num)
  have hlam3pos' : 0 < lam3 := by rw [hlam3def]; exact hlam3pos
  -- the real parts at the zeros
  have hρre1 : ρ₁.re = 1 - lam1 / Real.log (q : ℝ) := by
    rw [hlam1def, Work.LinnikContract.lamOf]; field_simp [hLne]; ring
  have hρre2 : ρ₂.re = 1 - lam2 / Real.log (q : ℝ) := by
    rw [hlam2def, Work.LinnikContract.lamOf]; field_simp [hLne]; ring
  have hρre3 : ρ₃.re = 1 - lam3 / Real.log (q : ℝ) := by
    rw [hlam3def, Work.LinnikContract.lamOf]; field_simp [hLne]; ring
  -- the minimality windows
  have hmin₁ : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 10 * L →
      lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [hlam1def]
    exact hm.2 χ₁ u ⟨hz₁.1, hu, him⟩
  have hmin₂ : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₂ u ≠ 0 → |u.im| ≤ 10 * L →
      lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [hlam1def]
    exact hm.2 χ₂ u ⟨hz₂.1, hu, him⟩
  have hmin₃ : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₃ u ≠ 0 → |u.im| ≤ 10 * L →
      lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [hlam1def]
    exact hm.2 χ₃ u ⟨hz₃.1, hu, him⟩
  -- the HB Lemma 3.1 feed at the single scale `log q`
  have hfeed : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), N ≤ q → ψ ≠ 1 →
      ψ.IsPrimitive → ψ ^ 2 = 1 →
      Work.ZeroFreeTables.LogDerivHyp ψ δ (Real.log (q : ℝ)) (1 / 8 + e1 / 3) := by
    intro N _iN ψ hN h1 h2 h3
    have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hlogN : Real.log (N : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hN)
    exact hfeed0 ψ h1 h2 h3 hL0 hlogN
  -- ### the three single extractions
  have hb1 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) χ₁
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ₁.im : ℂ) * Complex.I) (18 / 7) lam1
      ≤ -P3R (((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam1))
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) :=
    hsingle χ₁ hz₁.1 hsq1 ρ₁ lam1 lam1 hq2 hLz hLzi h3L h2aδ hfeed hz₁.2.1 hz₁.2.2
      hρre1 hlam10 hlam11 hmin₁
  have hb2 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) χ₂
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ₂.im : ℂ) * Complex.I) (18 / 7) lam1
      ≤ -P3R (((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam2))
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) :=
    hsingle χ₂ hz₂.1 hsq2 ρ₂ lam1 lam2 hq2 hLz hLzi h3L h2aδ hfeed hz₂.2.1 hz₂.2.2
      hρre2 hlam10 hlam11 hmin₂
  have hb3 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) χ₃
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ₃.im : ℂ) * Complex.I) (18 / 7) lam1
      ≤ -P3R (((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam3))
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) :=
    hsingle χ₃ hz₃.1 hsq3 ρ₃ lam1 lam3 hq2 hLz hLzi h3L h2aδ hfeed hz₃.2.1 hz₃.2.2
      hρre3 hlam10 hlam11 hmin₃
  -- ### the six pair extractions
  have hτa : |ρ₁.im + ρ₂.im| ≤ 3 * L := by
    have h := abs_add_le ρ₁.im ρ₂.im
    have h1 : |ρ₁.im| ≤ L := hz₁.2.2
    have h2 : |ρ₂.im| ≤ L := hz₂.2.2
    linarith
  have hp1 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₂)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im + ρ₂.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam3 : ℝ) : ℂ)
            + (((ρ₂.im - ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₃ hz₃.1 hsq3 ρ₃ lam1 lam3 (ρ₁.im + ρ₂.im) hq2 hLm hLi h3L h2aδ
      hfeed hz₃.2.1 hz₃.2.2 hτa hρre3 hlam10 hlam11 hmin₃
    have harg : ((ρ₁.im + ρ₂.im) - ρ₃.im) * Real.log (q : ℝ)
        = (ρ₂.im - ρ₃.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    rw [← (Work.ZeroFreeTables.char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).1] at h
    exact h
  have hτb : |ρ₁.im - ρ₂.im| ≤ 3 * L := by
    have h1 := abs_le.mp hz₁.2.2
    have h2 := abs_le.mp hz₂.2.2
    rw [abs_le]; constructor <;> linarith
  have hp2 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₂⁻¹)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im - ρ₂.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam3 : ℝ) : ℂ)
            + (((-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₃ hz₃.1 hsq3 ρ₃ lam1 lam3 (ρ₁.im - ρ₂.im) hq2 hLm hLi h3L h2aδ
      hfeed hz₃.2.1 hz₃.2.2 hτb hρre3 hlam10 hlam11 hmin₃
    have harg : ((ρ₁.im - ρ₂.im) - ρ₃.im) * Real.log (q : ℝ)
        = (-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    have hchar : χ₁ * χ₂⁻¹ = χ₃ := by
      rw [Work.ZeroFreeTables.inv_eq_self_of_sq_eq_one hsq2]
      exact (Work.ZeroFreeTables.char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).1
    rw [← hchar] at h
    exact h
  have hτc : |ρ₁.im + ρ₃.im| ≤ 3 * L := by
    have h := abs_add_le ρ₁.im ρ₃.im
    have h1 : |ρ₁.im| ≤ L := hz₁.2.2
    have h2 : |ρ₃.im| ≤ L := hz₃.2.2
    linarith
  have hp3 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₃)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im + ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam2 : ℝ) : ℂ)
            + (((ρ₃.im - ρ₂.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₂ hz₂.1 hsq2 ρ₂ lam1 lam2 (ρ₁.im + ρ₃.im) hq2 hLm hLi h3L h2aδ
      hfeed hz₂.2.1 hz₂.2.2 hτc hρre2 hlam10 hlam11 hmin₂
    have harg : ((ρ₁.im + ρ₃.im) - ρ₂.im) * Real.log (q : ℝ)
        = (ρ₃.im - ρ₂.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    rw [← (Work.ZeroFreeTables.char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.1] at h
    exact h
  have hτd : |ρ₁.im - ρ₃.im| ≤ 3 * L := by
    have h1 := abs_le.mp hz₁.2.2
    have h2 := abs_le.mp hz₃.2.2
    rw [abs_le]; constructor <;> linarith
  have hp4 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₃⁻¹)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im - ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam2 : ℝ) : ℂ)
            + (((-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₂ hz₂.1 hsq2 ρ₂ lam1 lam2 (ρ₁.im - ρ₃.im) hq2 hLm hLi h3L h2aδ
      hfeed hz₂.2.1 hz₂.2.2 hτd hρre2 hlam10 hlam11 hmin₂
    have harg : ((ρ₁.im - ρ₃.im) - ρ₂.im) * Real.log (q : ℝ)
        = (-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    have hchar : χ₁ * χ₃⁻¹ = χ₂ := by
      rw [Work.ZeroFreeTables.inv_eq_self_of_sq_eq_one hsq3]
      exact (Work.ZeroFreeTables.char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.1
    rw [← hchar] at h
    exact h
  have hτe : |ρ₂.im + ρ₃.im| ≤ 3 * L := by
    have h := abs_add_le ρ₂.im ρ₃.im
    have h1 : |ρ₂.im| ≤ L := hz₂.2.2
    have h2 : |ρ₃.im| ≤ L := hz₃.2.2
    linarith
  have hp5 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) (χ₂ * χ₃)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam1 : ℝ) : ℂ)
            + (((ρ₂.im + ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₁ hz₁.1 hsq1 ρ₁ lam1 lam1 (ρ₂.im + ρ₃.im) hq2 hLm hLi h3L h2aδ
      hfeed hz₁.2.1 hz₁.2.2 hτe hρre1 hlam10 hlam11 hmin₁
    have harg : ((ρ₂.im + ρ₃.im) - ρ₁.im) * Real.log (q : ℝ)
        = (ρ₂.im + ρ₃.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    rw [← (Work.ZeroFreeTables.char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.2] at h
    exact h
  have hτf : |ρ₂.im - ρ₃.im| ≤ 3 * L := by
    have h1 := abs_le.mp hz₂.2.2
    have h2 := abs_le.mp hz₃.2.2
    rw [abs_le]; constructor <;> linarith
  have hp6 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) (χ₂ * χ₃⁻¹)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₂.im - ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam1 : ℝ) : ℂ)
            + (((ρ₂.im - ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₁ hz₁.1 hsq1 ρ₁ lam1 lam1 (ρ₂.im - ρ₃.im) hq2 hLm hLi h3L h2aδ
      hfeed hz₁.2.1 hz₁.2.2 hτf hρre1 hlam10 hlam11 hmin₁
    have harg : ((ρ₂.im - ρ₃.im) - ρ₁.im) * Real.log (q : ℝ)
        = (ρ₂.im - ρ₃.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    have hchar : χ₂ * χ₃⁻¹ = χ₁ := by
      rw [Work.ZeroFreeTables.inv_eq_self_of_sq_eq_one hsq3]
      exact (Work.ZeroFreeTables.char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.2
    rw [← hchar] at h
    exact h
  -- ### the five principal-character bounds
  have hpole : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)) (18 / 7) lam1
      ≤ P3R (((18 / 7 : ℝ) + lam1) / (18 / 7)) + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hsre : (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)).re
        = 1 + (18 / 7) / Real.log (q : ℝ) := Complex.ofReal_re _
    have hsim : |(((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)).im| ≤ 3 * L := by
      simp only [Complex.ofReal_im, abs_zero]; linarith
    have h := hP q hqP hlam10 hlam11 hLle (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ))
      hsre hsim
    rw [Work.ZeroFreeTables.P3_pole_eq_push (a := (18 / 7 : ℝ)) (lam := lam1)
      (L := Real.log (q : ℝ)) (by norm_num) hLne] at h
    simpa [zero_add] using h
  have hprinc : ∀ τ : ℝ, |τ| ≤ 3 * L →
      Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) 1
        (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I) (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((τ * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * e1 := by
    intro τ hτ
    have hsre : (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re
        = 1 + (18 / 7) / Real.log (q : ℝ) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have hsim : |(((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I).im|
        ≤ 3 * L := by
      have h2 : (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I).im = τ := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [h2]; exact hτ
    have h := hP q hqP hlam10 hlam11 hLle
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I) hsre hsim
    rw [Work.ZeroFreeTables.P3_pole_shift_eq_push (a := (18 / 7 : ℝ)) (lam := lam1)
      (L := Real.log (q : ℝ)) (τ := τ) hLne] at h
    exact h
  have hq1 : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)
        + ((ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I) (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₂.im + ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) = ((ρ₂.im + ρ₃.im : ℝ) : ℂ) := by
      have h1 : ρ₁.im + ρ₂.im + ρ₃.im = ρ₂.im + ρ₃.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₂.im + ρ₃.im| ≤ 3 * L := by
      have h := abs_add_le ρ₂.im ρ₃.im
      have h1 : |ρ₂.im| ≤ L := hz₂.2.2
      have h2 : |ρ₃.im| ≤ L := hz₃.2.2
      linarith
    simpa [zero_add] using hprinc (ρ₂.im + ρ₃.im) hτ
  have hq2' : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)
        + ((ρ₁.im + ρ₂.im - ρ₃.im : ℝ) : ℂ) * Complex.I) (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₂.im - ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((ρ₁.im + ρ₂.im - ρ₃.im : ℝ) : ℂ) = ((ρ₂.im - ρ₃.im : ℝ) : ℂ) := by
      have h1 : ρ₁.im + ρ₂.im - ρ₃.im = ρ₂.im - ρ₃.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₂.im - ρ₃.im| ≤ 3 * L := by
      have h1 := abs_le.mp hz₂.2.2
      have h2 := abs_le.mp hz₃.2.2
      rw [abs_le]; constructor <;> linarith
    simpa [zero_add] using hprinc (ρ₂.im - ρ₃.im) hτ
  have hq3' : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)
        + ((ρ₁.im - ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I) (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₃.im - ρ₂.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((ρ₁.im - ρ₂.im + ρ₃.im : ℝ) : ℂ) = ((ρ₃.im - ρ₂.im : ℝ) : ℂ) := by
      have h1 : ρ₁.im - ρ₂.im + ρ₃.im = ρ₃.im - ρ₂.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₃.im - ρ₂.im| ≤ 3 * L := by
      have h1 := abs_le.mp hz₂.2.2
      have h2 := abs_le.mp hz₃.2.2
      rw [abs_le]; constructor <;> linarith
    simpa [zero_add] using hprinc (ρ₃.im - ρ₂.im) hτ
  have hq4' : Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)
        + ((-ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I) (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₂.im + ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((-ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) = ((ρ₂.im + ρ₃.im : ℝ) : ℂ) := by
      have h1 : -ρ₁.im + ρ₂.im + ρ₃.im = ρ₂.im + ρ₃.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₂.im + ρ₃.im| ≤ 3 * L := by
      have h := abs_add_le ρ₂.im ρ₃.im
      have h1 : |ρ₂.im| ≤ L := hz₂.2.2
      have h2 : |ρ₃.im| ≤ L := hz₃.2.2
      linarith
    simpa [zero_add] using hprinc (ρ₂.im + ρ₃.im) hτ
  -- ### the side condition of `P₃*`
  have hside : 1 / (18 / 7 : ℝ) ^ 3
      ≤ 1 / ((18 / 7 : ℝ) + lam1) ^ 3 + 1 / ((18 / 7 : ℝ) + lam2) ^ 3
        + 1 / ((18 / 7 : ℝ) + lam3) ^ 3 := by
    have ht1 : (27 / 64) / (18 / 7 : ℝ) ^ 3 ≤ 1 / ((18 / 7 : ℝ) + lam1) ^ 3 := by
      have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam1 := by linarith only [hlam10]
      have h4 : (18 / 7 : ℝ) + lam1 ≤ (4 / 3) * (18 / 7 : ℝ) := by linarith only [hlam167]
      have h1 : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) ≤ 1 / ((18 / 7 : ℝ) + lam1) ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hpos 3) (pow_le_pow_left₀ (le_of_lt hpos) h4 3)
      have heq : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) = (27 / 64) / (18 / 7 : ℝ) ^ 3 := by
        norm_num
      linarith only [h1, heq]
    have ht2 : (27 / 64) / (18 / 7 : ℝ) ^ 3 ≤ 1 / ((18 / 7 : ℝ) + lam2) ^ 3 := by
      have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam2 := by linarith only [hlam20]
      have h4 : (18 / 7 : ℝ) + lam2 ≤ (4 / 3) * (18 / 7 : ℝ) := by linarith only [hlam267]
      have h1 : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) ≤ 1 / ((18 / 7 : ℝ) + lam2) ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hpos 3) (pow_le_pow_left₀ (le_of_lt hpos) h4 3)
      have heq : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) = (27 / 64) / (18 / 7 : ℝ) ^ 3 := by
        norm_num
      linarith only [h1, heq]
    have ht3 : (27 / 64) / (18 / 7 : ℝ) ^ 3 ≤ 1 / ((18 / 7 : ℝ) + lam3) ^ 3 := by
      have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam3 := by linarith only [hlam30]
      have h4 : (18 / 7 : ℝ) + lam3 ≤ (4 / 3) * (18 / 7 : ℝ) := by linarith only [hlam367]
      have h1 : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) ≤ 1 / ((18 / 7 : ℝ) + lam3) ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hpos 3) (pow_le_pow_left₀ (le_of_lt hpos) h4 3)
      have heq : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) = (27 / 64) / (18 / 7 : ℝ) ^ 3 := by
        norm_num
      linarith only [h1, heq]
    have hkey : 1 / (18 / 7 : ℝ) ^ 3 ≤ (27 / 64) / (18 / 7 : ℝ) ^ 3 * 3 := by norm_num
    linarith only [ht1, ht2, ht3, hkey]
  -- ### the ten-term collapse
  set eS : ℝ := 24 / (δ * Real.log (q : ℝ)) + 3 * e1 + 4 * e1 with heSdef
  have hPstar := Work.P10.Pstar_collapse χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃
    (a := (18 / 7 : ℝ)) (lam1 := lam1) (lam2 := lam2) (lam3 := lam3) (δ := δ)
    (L := Real.log (q : ℝ)) (e1 := e1) (e2 := e1) (e3 := e1) (e4 := e1) (e5 := e1) (e6 := e1)
    (e7 := e1) (e8 := e1) (e9 := e1) (e10 := e1) (eS := eS)
    (by norm_num) hδ0 hLpos hlam10 hlam12 hlam23 hρ₁im hsq1 hsq2 hsq3 hprod hside
    (le_of_lt he1pos) (le_of_lt he1pos) (le_of_lt he1pos) (le_of_lt he1pos)
    (by rw [heSdef]; ring_nf; linarith)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hp1)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hp2)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hp3)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hp4)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hp5)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hp6)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hq1)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hq2')
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hq3')
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hq4')
  -- ### the weighted combination
  have hpos14 : ∀ n : ℕ, 0 ≤ Work.ZeroFreeTables.P10.comb14Raw q χ₁ χ₂ χ₃
      (Real.log (q : ℝ)) (1 + (18 / 7) / Real.log (q : ℝ)) ρ₁.im ρ₂.im ρ₃.im
      (18 / 7) lam1 n := by
    intro n
    exact Work.ZeroFreeTables.HB103.Comb14Positivity χ₁ χ₂ χ₃ (Real.log (q : ℝ))
      (1 + (18 / 7) / Real.log (q : ℝ)) ρ₁.im ρ₂.im ρ₃.im (18 / 7) lam1
      (by norm_num) hLpos hlam10 hsq1 hsq2 hsq3 hprod n
  have hcomb := Work.ZeroFreeTables.case3_weighted_combination_engine (N := q) χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃
    (hpos0 := hpos14)
    (a := (18 / 7 : ℝ)) (lam1 := lam1) (lam2 := lam2) (lam3 := lam3) (δ := δ)
    (L := Real.log (q : ℝ)) (e1 := e1) (e2 := e1) (e3 := e1) (eP := e1) (eS := eS)
    (eps := 6 * e1 + 5 * e1 + 48 / (δ * Real.log (q : ℝ)))
    (by norm_num) hδ0 hδ1 hLpos hlam10 hlam12 hlam13 (le_of_lt he1pos) (by rw [heSdef]; positivity)
    (by rw [heSdef]; ring_nf; linarith)
    hsq1 hsq2 hsq3 hprod hb1 hb2 hb3 hpole
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hPstar)
  -- ### HB (10.14)
  refine Work.ZeroFreeTables.p1014_of_bridge_eps (δ := lam1 / (6 / 7))
    (X₁ := ((18 / 7 : ℝ) + lam1) / (18 / 7))
    (X₂ := ((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam2))
    (X₃ := ((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam3))
    (eps := 6 * e1 + 5 * e1 + 48 / (δ * Real.log (q : ℝ))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · positivity
  · field_simp
    ring
  · have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam2 := by linarith only [hlam20]
    rw [le_div_iff₀ hpos, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hδ : lam1 / (6 / 7) = 7 * lam1 / 6 := by ring
    rw [hδ]
    nlinarith only [mul_nonneg hlam10 (sub_nonneg.mpr hlam267), hlam267, hlam10]
  · have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam3 := by linarith only [hlam30]
    rw [le_div_iff₀ hpos, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hδ : lam1 / (6 / 7) = 7 * lam1 / 6 := by ring
    rw [hδ]
    nlinarith only [mul_nonneg hlam10 (sub_nonneg.mpr hlam367), hlam367, hlam10]
  · exact le_of_lt hε'
  · rw [he1def]
    linarith [hbud, hε']
  · have h6 : (6 / 7 : ℝ) * (lam1 / (6 / 7)) = lam1 := by ring_nf
    rw [h6]
    exact hcomb

/-! ## The target statement -/

/-- **HB Lemma 10.3 at rectangle height `L`, all characters real and `ρ₁` real.** -/
theorem Rect10_3AllReal : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ρ₁.im = 0 →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₃ ^ 2 = 1 → χ₁ * χ₂ * χ₃ = 1 →
      Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
      (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u) →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε →
      6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε L hL
  obtain ⟨qE, hE⟩ := Rect10_3AllReal_engine (1 / 1000) (by norm_num) L hL
  refine ⟨max qE 2, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him hsq1 hsq2 hsq3 hprod hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hmin2 hmin3 hlam23 hlam3
  have hqE' : qE ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hl3pos : 0 < Work.LinnikContract.lamOf q ρ₃ := by
    have hre : ρ₃.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₃ hZ3.2.1
    have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    rw [Work.LinnikContract.lamOf]
    exact mul_pos (by linarith) hlog
  have hl10 : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.ZeroFreeTables.lamOf_nonneg_of_re_le_one
      (le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hm.1.2.1))
  have hl36 : Work.LinnikContract.lamOf q ρ₃ ≤ 6 / 7 := by linarith
  have hl16 : Work.LinnikContract.lamOf q ρ₁ ≤ 6 / 7 :=
    le_trans (hm.2 χ₃ ρ₃ ⟨hZ3.1, hZ3.2.1, le_trans hZ3.2.2 (by linarith)⟩) hl36
  have hδ0 : 0 ≤ Work.LinnikContract.lamOf q ρ₁ / (6 / 7) := div_nonneg hl10 (by norm_num)
  have hδ1 : Work.LinnikContract.lamOf q ρ₁ / (6 / 7) ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 6/7), one_mul]
    exact hl16
  have hcontra := hE q hqE' χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm him hsq1 hsq2 hsq3 hprod hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hlam23 hl3pos hl36
  exact absurd (Work.ZeroFreeTables.p1014_neg_of_le_cert hδ0 hδ1 le_rfl)
    (not_lt.mpr hcontra)

end

end Work.OffAxis
