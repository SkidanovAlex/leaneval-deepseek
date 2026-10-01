import Mathlib
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero
import Submission.Work.LinnikAreas.log_unbounded_nat
import Submission.Work.LinnikAreas.turanAux2.lMultMassRect
import Submission.Work.LinnikAreas.BGTZ.ZFRSupport.SiegelRepel
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_repelOwnFinal
import Submission.Work.LinnikAreas.OtherCharRepel.twoRealCharRepel
import Submission.Work.LinnikAreas.siegelZeroFreeRegion
import Submission.Work.LinnikAreas.siegelZetaZeroFree
import Submission.Work.A7.exists_isMin1
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.LinnikAreas.BGTZ

open Work.LinnikContract

set_option maxHeartbeats 1000000

noncomputable section

/-! ## A compact-height zero-free strip for `ζ`

For every fixed height `T > 0` the Riemann zeta function has no zeros in the strip
`1 - ε ≤ Re s ≤ 2`, `|Im s| ≤ T`, for some `ε > 0` depending on `T`: the zeros of `ζ` in
the compact box `[1/2,2] × [-T,T]` are finitely many and all have real part `< 1`
(`IsCompact.inter_riemannZetaZeros_finite`, `riemannZeta_ne_zero_of_one_le_re`). -/
theorem zetaZeroFreeCompactWidth_aux (T : ℝ) (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t σ : ℝ), |t| ≤ T → 1 - ε ≤ σ → σ ≤ 2 →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  classical
  let S : Set ℂ := (fun p : ℝ × ℝ => ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-T) T)
  have hSc : IsCompact S := by
    refine (IsCompact.prod isCompact_Icc isCompact_Icc).image ?_
    fun_prop
  let Z : Set ℂ := S ∩ riemannZetaZeros
  have hZfin : Z.Finite := hSc.inter_riemannZetaZeros_finite
  rcases Z.eq_empty_or_nonempty with hZ0 | hZne
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro t σ ht hσ1 hσ2 hz
    have hmem : ((σ : ℂ) + Complex.I * (t : ℂ)) ∈ Z := by
      refine ⟨?_, ?_⟩
      · refine ⟨(σ, t), ?_, rfl⟩
        exact ⟨⟨by linarith, hσ2⟩, by rw [Set.mem_Icc]; exact abs_le.mp ht⟩
      · simpa [riemannZetaZeros] using hz
    rw [hZ0] at hmem
    exact hmem
  · have hne : hZfin.toFinset.Nonempty := hZfin.toFinset_nonempty.mpr hZne
    obtain ⟨z₀, hz₀F, hz₀max⟩ := Finset.exists_max_image hZfin.toFinset (fun z => z.re) hne
    have hz₀mem : z₀ ∈ Z := by simpa using hz₀F
    have hz₀zero : riemannZeta z₀ = 0 := by
      have h := hz₀mem.2
      simpa [riemannZetaZeros] using h
    have hz₀re : z₀.re < 1 :=
      lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz₀zero
    refine ⟨min (1 / 2) ((1 - z₀.re) / 2), lt_min (by norm_num) (by linarith), ?_⟩
    intro t σ ht hσ1 hσ2 hz
    have hzmem : ((σ : ℂ) + Complex.I * (t : ℂ)) ∈ Z := by
      refine ⟨?_, ?_⟩
      · refine ⟨(σ, t), ?_, rfl⟩
        exact ⟨⟨by linarith [min_le_left (1 / 2 : ℝ) ((1 - z₀.re) / 2)], hσ2⟩,
          by rw [Set.mem_Icc]; exact abs_le.mp ht⟩
      · simpa [riemannZetaZeros] using hz
    have hle : ((σ : ℂ) + Complex.I * (t : ℂ)).re ≤ z₀.re :=
      hz₀max _ (by simpa using hzmem)
    have hσle : σ ≤ z₀.re := by simpa using hle
    have hmin : min (1 / 2) ((1 - z₀.re) / 2) ≤ (1 - z₀.re) / 2 := min_le_right _ _
    linarith

/-- `c ≤ C / 2` and `ℓ ≤ 2 L` (all positive) give `c / L ≤ C / ℓ`. -/
private lemma div_le_div_of_le_two {c C L ℓ : ℝ} (hc : 0 < c) (hL : 0 < L) (hℓ : 0 < ℓ)
    (h : ℓ ≤ 2 * L) (hle : c ≤ C / 2) : c / L ≤ C / ℓ := by
  have hC : 0 ≤ C := by
    have h1 : 0 < C / 2 := lt_of_lt_of_le hc hle
    linarith
  have h1 : c / L ≤ (C / 2) / L := by
    rw [div_le_div_iff₀ hL hL]
    exact mul_le_mul_of_nonneg_right hle hL.le
  have h2 : (C / 2) / L = C / (2 * L) := by ring
  have h3 : 1 / (2 * L) ≤ 1 / ℓ := one_div_le_one_div_of_le hℓ h
  calc c / L ≤ (C / 2) / L := h1
    _ = C / (2 * L) := h2
    _ ≤ C / ℓ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using h3) hC

/-! ## The main assembly -/

/-- **`ZFRInput` from the Deuring--Heilbronn repulsion.**

Given the pair-form Deuring--Heilbronn repulsion `Siegel.RepulsionInput` (Heath-Brown 1992,
Principle 2: every zero other than the exceptional pair `(χ₁,β₁)` of any character modulo `q`
satisfies `λ(ρ) ≥ c·log(1/λ(β₁))`), the uniform zero-free region holds with an absolute constant:

* for a zero `ρ` with `|Im ρ| ≤ 1`: if `χ` is non-principal the repulsion gives
  `λ(ρ) ≥ c·log(1/λ(β₁)) ≥ c·log 10` (as `λ(β₁) < 1/10`), and if `χ` is principal the `ζ`-region
  `siegelZetaZeroFree` gives `λ(ρ) ≥ c_ζ`;
* for a zero with `|Im ρ| > 1`: for non-principal `χ` the uniform off-axis region gives
  `1 - Re ρ ≥ c_off/log(conductor·(|Im ρ| + 2)) ≫ 1/log(q·max 4 |Im ρ|)`, and for the principal
  character the `ζ`-regions (`zeta_zeroFreeRegion_largeHeight` for large `|Im ρ|` and the
  compact-height strip `zetaZeroFreeCompactWidth_aux` for bounded `|Im ρ|`) apply.

The passage from `λ(ρ) ≥ c` to `cZ/log(q·max 4 |Im ρ|) ≤ 1 - Re ρ` is the elementary
`λ(ρ) = (1 - Re ρ)·log q` bookkeeping. -/
def PairRepelNonPrin : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ 1 → zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ¬(χ = χ₁ ∧ ρ = ((β₁ : ℝ) : ℂ)) →
      c * Real.log (1 / lamOf q (β₁ : ℂ)) ≤ lamOf q ρ

/-- **`ZFRInput` from the pair repulsion.** -/
theorem ZFRInput_of_repulsion (hRep : PairRepelNonPrin) :
    ∃ cZ : ℝ, 0 < cZ ∧ ZFRInput cZ := by
  obtain ⟨cOff, hcOffpos, hOff⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨cZeta, hcZetapos, hZeta⟩ := Work.LinnikAreas.siegelZetaZeroFree
  obtain ⟨c₀, T₀, hc₀pos, hT₀pos, hLarge⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight
  obtain ⟨ε, hεpos, hε⟩ := zetaZeroFreeCompactWidth_aux T₀ hT₀pos
  obtain ⟨cRep, hcReppos, qRep, hRep'⟩ := hRep
  have hlog10pos : 0 < Real.log 10 := Real.log_pos (by norm_num)
  set cA : ℝ := min cZeta (cRep * Real.log 10) with hcAdef
  have hcApos : 0 < cA := lt_min hcZetapos (mul_pos hcReppos hlog10pos)
  set cZ : ℝ := min (min cA (cOff / 2)) (c₀ / 2) with hcZdef
  have hcZpos : 0 < cZ := by
    rw [hcZdef]
    exact lt_min (lt_min hcApos (by positivity)) (by positivity)
  have hcZ_cA : cZ ≤ cA := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcZ_off : cZ ≤ cOff / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcZ_c0 : cZ ≤ c₀ / 2 := min_le_right _ _
  obtain ⟨qBig, hqBig⟩ := Work.LinnikAreas.log_unbounded_nat (cZ / ε + Real.log 4)
  refine ⟨cZ, hcZpos, ?_⟩
  refine ⟨max (max qRep 2) qBig, ?_⟩
  intro q hq hqne χ₁ β₁ hχ₁ hsq hβ₁ hz₁ hβ₁' χ ρ hzm hre hne
  haveI : NeZero q := hqne
  have hqRep : qRep ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2 : 2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqBig' : qBig ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlog4qpos : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by nlinarith)
  -- `cZ / log (4q) ≤ ε`
  have hε_to : cZ / Real.log (4 * (q : ℝ)) ≤ ε := by
    have hsplit : Real.log (4 * (q : ℝ)) = Real.log 4 + Real.log (q : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hle : cZ / ε ≤ Real.log (4 * (q : ℝ)) := by
      have h := hqBig q hqBig'
      rw [hsplit]
      linarith
    rw [div_le_iff₀ hlog4qpos, mul_comm ε]
    exact (div_le_iff₀ hεpos).mp hle
  -- `λ(β₁) < 1/10`, hence `≤ 1/2` and `> 0`
  have hlam1 : Work.LinnikContract.lamOf q (β₁ : ℂ) < 1 / 10 := by
    have h1 : 1 - β₁ < 1 / (10 * Real.log (q : ℝ)) := by linarith [hβ₁']
    have h2 : (1 - β₁) * Real.log (q : ℝ)
        < (1 / (10 * Real.log (q : ℝ))) * Real.log (q : ℝ) :=
      mul_lt_mul_of_pos_right h1 hlogq
    have h3 : (1 / (10 * Real.log (q : ℝ))) * Real.log (q : ℝ) = 1 / 10 := by
      field_simp
    rw [h3] at h2
    rw [Work.LinnikContract.lamOf]
    simpa using h2
  have hlam1pos : 0 < Work.LinnikContract.lamOf q (β₁ : ℂ) := by
    rw [Work.LinnikContract.lamOf]
    have h : ((β₁ : ℂ)).re = β₁ := Complex.ofReal_re β₁
    rw [h]
    exact mul_pos (by linarith) hlogq
  have hlam1le : Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ 1 / 2 := by linarith
  by_cases him : |ρ.im| ≤ 1
  · -- ================= Case A: `|Im ρ| ≤ 1` =================
    have hA : cA ≤ Work.LinnikContract.lamOf q ρ := by
      by_cases hχ1 : χ = 1
      · have h := hZeta (q := q) hq2 ρ (by rw [← hχ1]; exact hzm) him
        exact le_trans (min_le_left _ _) h
      · have hnex : ¬ (χ = χ₁ ∧ ρ = ((β₁ : ℝ) : ℂ)) := by
          rintro ⟨-, h2⟩
          exact hne h2
        have h := hRep' q hqRep χ₁ β₁ hχ₁ hsq hβ₁ hz₁ hlam1le χ ρ hχ1 hzm him hnex
        have hlog : Real.log 10 ≤ Real.log (1 / Work.LinnikContract.lamOf q (β₁ : ℂ)) := by
          apply Real.log_le_log (by norm_num)
          rw [le_div_iff₀ hlam1pos]
          linarith [hlam1]
        have h2 : cRep * Real.log 10 ≤ Work.LinnikContract.lamOf q ρ :=
          le_trans (mul_le_mul_of_nonneg_left hlog hcReppos.le) h
        exact le_trans (min_le_right _ _) h2
    have h1mre : 0 < 1 - ρ.re := by
      have h := hA
      rw [Work.LinnikContract.lamOf] at h
      exact pos_of_mul_pos_left (lt_of_lt_of_le hcApos h) hlogq.le
    have hmax : max 4 |ρ.im| = 4 := max_eq_left (by linarith)
    have hlog4qpos' : 0 < Real.log ((q : ℝ) * 4) := by
      rw [mul_comm (q : ℝ) 4]; exact hlog4qpos
    rw [hmax, div_le_iff₀ hlog4qpos']
    have hA' : cA ≤ (1 - ρ.re) * Real.log (q : ℝ) := by
      rwa [Work.LinnikContract.lamOf] at hA
    have hlog4 : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * 4) := by
      apply Real.log_le_log (by positivity); nlinarith
    calc cZ ≤ cA := hcZ_cA
      _ ≤ (1 - ρ.re) * Real.log (q : ℝ) := hA'
      _ ≤ (1 - ρ.re) * Real.log ((q : ℝ) * 4) := mul_le_mul_of_nonneg_left hlog4 h1mre.le
  · -- ================= Case B: `1 < |Im ρ|` =================
    push Not at him
    set M : ℝ := max 4 |ρ.im| with hMdef
    have hM4 : 4 ≤ M := le_max_left _ _
    have hMt : |ρ.im| ≤ M := le_max_right _ _
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM4
    have hlogqM : 0 < Real.log ((q : ℝ) * M) := Real.log_pos (by nlinarith)
    by_cases hχ1 : χ = 1
    · -- ---- the principal character: `ζ` ----
      have hzm' : Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) ρ ≠ 0 := by
        rw [← hχ1]; exact hzm
      have hz : completedRiemannZeta ρ = 0 := by
        have h := Work.LinnikAreas.zeroMult_principal_eq q ρ
        rw [h] at hzm'
        exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm'
      have hρ0 : ρ ≠ 0 := by
        intro h0
        rw [h0] at hre
        simp at hre
        linarith
      have hζ : riemannZeta ρ = 0 := by
        rw [riemannZeta_def_of_ne_zero hρ0, hz, zero_div]
      have hζ' : riemannZeta ((ρ.re : ℂ) + Complex.I * (ρ.im : ℂ)) = 0 := by
        rw [mul_comm Complex.I ((ρ.im : ℂ)), Complex.re_add_im]
        exact hζ
      have hre_lt1 : ρ.re < 1 :=
        lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
      by_cases hbig : T₀ ≤ |ρ.im|
      · -- large height
        have hcon := hLarge ρ.im hbig ρ.re
        have hlt : ρ.re < 1 - c₀ / Real.log (|ρ.im| + 3) := by
          by_contra hle
          push Not at hle
          exact hcon hle hζ'
        have hℓpos : 0 < Real.log (|ρ.im| + 3) := Real.log_pos (by linarith [abs_nonneg ρ.im])
        have hℓle : Real.log (|ρ.im| + 3) ≤ 2 * Real.log ((q : ℝ) * M) := by
          have h1 : |ρ.im| + 3 ≤ 2 * M := by
            rw [hMdef]
            by_cases h3 : (4 : ℝ) ≤ |ρ.im|
            · rw [max_eq_right h3]
              linarith
            · push Not at h3
              rw [max_eq_left (by linarith : |ρ.im| ≤ (4 : ℝ))]
              linarith [abs_nonneg ρ.im]
          have h2 : Real.log (|ρ.im| + 3) ≤ Real.log (2 * M) :=
            Real.log_le_log (by linarith [abs_nonneg ρ.im]) h1
          have h3 : Real.log (2 * M) ≤ 2 * Real.log ((q : ℝ) * M) := by
            rw [Real.log_mul (by norm_num) (by positivity)]
            have h4 : Real.log M ≤ Real.log ((q : ℝ) * M) :=
              Real.log_le_log hMpos (by nlinarith)
            have h5 : Real.log 2 ≤ Real.log ((q : ℝ) * M) :=
              Real.log_le_log (by norm_num) (by nlinarith)
            linarith
          linarith
        exact le_of_lt (lt_of_le_of_lt
          (div_le_div_of_le_two hcZpos hlogqM hℓpos hℓle hcZ_c0) (by linarith [hlt]))
      · -- bounded height: the compact strip
        push Not at hbig
        have heps : ε ≤ 1 - ρ.re := by
          by_contra hlt
          push Not at hlt
          exact hε ρ.im ρ.re (le_of_lt hbig) (by linarith) (by linarith) hζ'
        have h4q : 4 * (q : ℝ) ≤ (q : ℝ) * M := by nlinarith
        have hlog4qM : Real.log (4 * (q : ℝ)) ≤ Real.log ((q : ℝ) * M) :=
          Real.log_le_log (by positivity) h4q
        have hcmp : cZ / Real.log ((q : ℝ) * M) ≤ cZ / Real.log (4 * (q : ℝ)) :=
          div_le_div_of_nonneg_left hcZpos.le hlog4qpos hlog4qM
        linarith [hcmp, hε_to, heps]
    · -- ---- the off-axis region ----
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hLψ : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 :=
        Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero χ hχ1 hzm
      have hLψ' : DirichletCharacter.LFunction χ.primitiveCharacter
          ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I) = 0 := by
        rw [Complex.re_add_im]; exact hLψ
      have hprim : χ.primitiveCharacter.IsPrimitive :=
        DirichletCharacter.primitiveCharacter_isPrimitive χ
      have hψne : χ.primitiveCharacter ≠ 1 := by
        intro h1
        refine hχ1 ?_
        rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1,
          DirichletCharacter.changeLevel_one χ.conductor_dvd_level]
      have himne : ρ.im ≠ 0 := by
        intro h0
        have h1 : (1 : ℝ) < |ρ.im| := him
        rw [h0] at h1
        norm_num at h1
      have hcon := hOff (N := χ.conductor) χ.primitiveCharacter hprim hψne ρ.re ρ.im himne
      have hlt : ρ.re < 1 - cOff / Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) := by
        by_contra hle
        push Not at hle
        exact hcon hle hLψ'
      have hNpos : 0 < (χ.conductor : ℝ) := by
        have h := χ.conductor_ne_zero
        positivity
      have hN2 : 2 ≤ χ.conductor := by
        have h0 : χ.conductor ≠ 0 := χ.conductor_ne_zero
        have h1 : χ.conductor ≠ 1 := fun h =>
          hχ1 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
        omega
      have hNdvd : χ.conductor ≤ q :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
      have hNle : (χ.conductor : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNdvd
      have hN2' : (2 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast hN2
      have hargpos : 0 < (χ.conductor : ℝ) * (|ρ.im| + 2) :=
        mul_pos hNpos (by linarith [abs_nonneg ρ.im])
      have hbound : Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2))
          ≤ 2 * Real.log ((q : ℝ) * M) := by
        have harg3 : |ρ.im| + 2 ≤ 3 * |ρ.im| := by linarith [abs_pos.mpr himne, him]
        have h1 : (χ.conductor : ℝ) * (|ρ.im| + 2) ≤ 3 * ((q : ℝ) * M) := by
          have h2 : (χ.conductor : ℝ) * (|ρ.im| + 2) ≤ (q : ℝ) * (3 * |ρ.im|) :=
            mul_le_mul hNle harg3 (by linarith [abs_nonneg ρ.im]) (by positivity)
          have h3 : (q : ℝ) * (3 * |ρ.im|) ≤ (q : ℝ) * (3 * M) :=
            mul_le_mul_of_nonneg_left (by linarith [hMt]) (by positivity)
          have h4 : (q : ℝ) * (3 * M) = 3 * ((q : ℝ) * M) := by ring
          linarith [h2, h3, h4]
        have h2 : Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2))
            ≤ Real.log (3 * ((q : ℝ) * M)) := Real.log_le_log hargpos h1
        have h3 : Real.log (3 * ((q : ℝ) * M)) ≤ 2 * Real.log ((q : ℝ) * M) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
          have h5 : Real.log 3 ≤ Real.log ((q : ℝ) * M) :=
            Real.log_le_log (by norm_num) (by nlinarith)
          linarith
        linarith
      have hℓpos : 0 < Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) :=
        Real.log_pos (by nlinarith [hargpos, hNpos, abs_nonneg ρ.im, hN2'])
      have hcmp : cZ / Real.log ((q : ℝ) * M)
          ≤ cOff / Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) := by
        have h1 : cZ / Real.log ((q : ℝ) * M)
            ≤ (cOff / 2) / Real.log ((q : ℝ) * M) := by
          rw [div_le_div_iff₀ hlogqM hlogqM]
          exact mul_le_mul_of_nonneg_right hcZ_off hlogqM.le
        have h2 : (cOff / 2) / Real.log ((q : ℝ) * M)
            = cOff / (2 * Real.log ((q : ℝ) * M)) := by ring
        have h3 : 1 / (2 * Real.log ((q : ℝ) * M))
            ≤ 1 / Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) :=
          one_div_le_one_div_of_le hℓpos hbound
        calc cZ / Real.log ((q : ℝ) * M) ≤ (cOff / 2) / Real.log ((q : ℝ) * M) := h1
          _ = cOff / (2 * Real.log ((q : ℝ) * M)) := h2
          _ ≤ cOff / Real.log ((χ.conductor : ℝ) * (|ρ.im| + 2)) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_left (by simpa [one_div] using h3) hcOffpos.le
      exact le_of_lt (lt_of_le_of_lt hcmp (by linarith [hlt]))

/-- **The single-character mass bound**, spelled out as a `Prop` (this is the statement of
`Work.LinnikAreas.MassBounds.singleMass`; it is the analytic input of the other-character
Deuring--Heilbronn repulsion `otherCharRepelSiegel_of_mass`). -/
def MassBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (w : ℂ),
    (3 / 2 : ℝ) ≤ w.re →
    Summable (fun u : ℂ => ((Work.LinnikAreas.TuranOther.multZeta u : ℝ)
        + (Work.LinnikAreas.TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2) ∧
    (∑' u : ℂ, ((Work.LinnikAreas.TuranOther.multZeta u : ℝ)
        + (Work.LinnikAreas.TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2)
      ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2)

/-! ## The pair repulsion for non-principal characters

The Deuring--Heilbronn phenomenon in the form in which the main proof consumes it: the given
exceptional pair `(χ₁, β₁)` repels every *other* pair `(χ, ρ)` of a non-principal character.
This is assembled here from the workspace's proven pieces:

* `Work.LinnikAreas.otherCharRepelSiegel_of_mass` (Heath-Brown §8) applied to the mass bound
  `MassBounds.singleMass` — the repulsion at the *minimal* pair in the Siegel regime
  `λ(ρ₀) ≤ 1/100`, for `χ ≠ χ₀`, `χ ≠ 1`, `ρ ≠ ρ₀`;
* `Work.LinnikAreas.repelOwnFinal` (the Turán/power-sum route) — the same-character repulsion at
  the minimal pair, `λ(ρ₀) ≤ 1/2`;
* `Work.LinnikAreas.OtherCharRepel.twoRealCharRepel` (Landau) — two distinct real characters
  cannot both have a real zero with small `λ` (the shared-point case);
* `Work.LinnikAreas.siegelZeroFreeRegion` — the uniform zero-free region, which removes every
  zero that is not a real zero of a real character, and in particular handles the shared-point
  cases with a complex character (there the point `ρ₀` is a real zero of a character `χ` with
  `χ² ≠ 1`, so `λ(ρ₀) ≥ c_zf`).

The passage from the *given* pair `(χ₁, β₁)` (with `λ(β₁) ≤ 1/2`) to the globally minimal pair
`(χ₀, ρ₀)` (`Work.A7.exists_isMin1`) is the same reduction as in
`Work.LinnikAreas.Siegel.repulsionInput_of`, only with the principal character excluded (the main
proof treats `χ = 1` by the `ζ`-region `siegelZetaZeroFree`). -/

/-- `log (1/b) ≤ log (1/a)` for `0 < a ≤ b`. -/
private lemma log_inv_le_log_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ b) :
    Real.log (1 / b) ≤ Real.log (1 / a) := by
  apply Real.log_le_log (by positivity)
  rw [one_div, one_div, inv_le_inv₀ hb ha]
  exact h

/-- Products: `c ≤ m/K` and `Λ ≤ K` (with `0 ≤ Λ`) give `c·Λ ≤ m`. -/
private lemma mul_le_of_le_div {c m K Λ : ℝ} (hc0 : 0 < c) (hK : 0 < K) (hc : c ≤ m / K)
    (hΛ0 : 0 ≤ Λ) (hΛK : Λ ≤ K) : c * Λ ≤ m := by
  have hmK : 0 < m / K := lt_of_lt_of_le hc0 hc
  calc c * Λ ≤ (m / K) * Λ := mul_le_mul_of_nonneg_right hc hΛ0
    _ ≤ (m / K) * K := mul_le_mul_of_nonneg_left hΛK hmK.le
    _ = m := by field_simp

/-- The "repulsion in logarithmic form": `c ≤ A`, `A·log(1/λ₀) ≤ x` and `log(1/λ₁) ≤ log(1/λ₀)`
give `c·log(1/λ₁) ≤ x`. -/
private lemma mul_log_le_of_le {c A lam1 lam0 x : ℝ} (hc0 : 0 < c) (hA0 : 0 < A) (hc : c ≤ A)
    (h0 : 0 ≤ Real.log (1 / lam0)) (hle : Real.log (1 / lam1) ≤ Real.log (1 / lam0))
    (hx : A * Real.log (1 / lam0) ≤ x) : c * Real.log (1 / lam1) ≤ x := by
  calc c * Real.log (1 / lam1) ≤ c * Real.log (1 / lam0) := mul_le_mul_of_nonneg_left hle hc0.le
    _ ≤ A * Real.log (1 / lam0) := mul_le_mul_of_nonneg_right hc h0
    _ ≤ x := hx

/-- The "self-repulsion" arithmetic: if the exceptional zero `β₁` is repelled by the minimal pair,
`c₁·log(1/λ₀) ≤ λ₁`, and `λ₁ ≤ 1/2`, then `λ₀` is bounded below by `exp(-1/(2c₁))`, so that
`2c₁·exp(-1/(2c₁))·log(1/λ₁) ≤ λ₀`. -/
private lemma self_repel {c c₁ lam0 lam1 : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁)
    (hδ : c ≤ 2 * c₁ * Real.exp (-(1 / (2 * c₁))))
    (hlam0 : 0 < lam0) (hle : lam0 ≤ lam1) (hlam1le : lam1 ≤ 1 / 2)
    (hbound : c₁ * Real.log (1 / lam0) ≤ lam1) : c * Real.log (1 / lam1) ≤ lam0 := by
  have hlam1pos : 0 < lam1 := lt_of_lt_of_le hlam0 hle
  have hK : Real.log (1 / lam0) ≤ 1 / (2 * c₁) := by
    have h1 : c₁ * Real.log (1 / lam0) ≤ 1 / 2 := le_trans hbound hlam1le
    have h2 : Real.log (1 / lam0) ≤ (1 / 2) / c₁ := by
      rw [le_div_iff₀ hc₁]
      linarith
    have h3 : (1 / 2) / c₁ = 1 / (2 * c₁) := by ring
    linarith
  have hlog : Real.log (1 / lam1) ≤ 1 / (2 * c₁) :=
    le_trans (log_inv_le_log_inv hlam0 hlam1pos hle) hK
  have hexp : Real.exp (-(1 / (2 * c₁))) ≤ lam0 := by
    have h2 : 1 / lam0 ≤ Real.exp (1 / (2 * c₁)) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 1 / lam0)]
      exact Real.exp_le_exp.mpr hK
    have h3 : (Real.exp (1 / (2 * c₁)))⁻¹ ≤ lam0 := by
      rw [inv_le_comm₀ (Real.exp_pos _) hlam0]
      rw [one_div] at h2
      exact h2
    rwa [← Real.exp_neg] at h3
  have h1 : c * Real.log (1 / lam1) ≤ c * (1 / (2 * c₁)) := mul_le_mul_of_nonneg_left hlog hc.le
  have h2 : c * (1 / (2 * c₁)) ≤ (2 * c₁ * Real.exp (-(1 / (2 * c₁)))) * (1 / (2 * c₁)) :=
    mul_le_mul_of_nonneg_right hδ (by positivity)
  have h3 : (2 * c₁ * Real.exp (-(1 / (2 * c₁)))) * (1 / (2 * c₁))
      = Real.exp (-(1 / (2 * c₁))) := by field_simp
  linarith [h1, h2, h3, hexp]

/-- **`PairRepelNonPrin` from the mass bound.** -/
theorem PairRepelNonPrin_of_mass (hMass : MassBoundStatement) : PairRepelNonPrin := by
  obtain ⟨cSig, hcSigpos, qSig, hSig⟩ := Work.LinnikAreas.otherCharRepelSiegel_of_mass hMass
  obtain ⟨cOwn, hcOwnpos, qOwn, hOwn⟩ := Work.LinnikAreas.repelOwnFinal
  obtain ⟨cLand, hcLandpos, qLand, hLand⟩ := Work.LinnikAreas.OtherCharRepel.twoRealCharRepel
  obtain ⟨czf, hczfpos, qzf, hzf⟩ := Work.LinnikAreas.siegelZeroFreeRegion
  have hlog100pos : 0 < Real.log 100 := Real.log_pos (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the constants
  set cz' : ℝ := min czf (1 / 2) with hcz'def
  have hcz'pos : 0 < cz' := lt_min hczfpos (by norm_num)
  have hcz'le : cz' ≤ 1 / 2 := min_le_right _ _
  have hcz'le_zf : cz' ≤ czf := min_le_left _ _
  have hlogcz' : 0 < Real.log (1 / cz') := by
    apply Real.log_pos
    rw [one_div, one_lt_inv₀ hcz'pos]
    linarith
  set cL' : ℝ := min cLand (1 / 2) with hcL'def
  have hcL'pos : 0 < cL' := lt_min hcLandpos (by norm_num)
  have hcL'le : cL' ≤ 1 / 2 := min_le_right _ _
  have hcL'le_land : cL' ≤ cLand := min_le_left _ _
  have hlogcL' : 0 < Real.log (1 / cL') := by
    apply Real.log_pos
    rw [one_div, one_lt_inv₀ hcL'pos]
    linarith
  -- the constant of the "self-repulsion" arithmetic
  set cBig : ℝ := min cSig cOwn with hcBigdef
  have hcBigpos : 0 < cBig := lt_min hcSigpos hcOwnpos
  have hcBig_sig : cBig ≤ cSig := min_le_left _ _
  have hcBig_own : cBig ≤ cOwn := min_le_right _ _
  set c₁ : ℝ := min cBig ((1 / 100) / Real.log 100) with hc₁def
  have hc₁pos : 0 < c₁ := lt_min hcBigpos (by positivity)
  have hc₁_big : c₁ ≤ cBig := min_le_left _ _
  have hc₁_100 : c₁ ≤ (1 / 100) / Real.log 100 := min_le_right _ _
  set δ : ℝ := Real.exp (-(1 / (2 * c₁))) with hδdef
  have hδpos : 0 < δ := Real.exp_pos _
  -- the final constant
  set c : ℝ := min (min (cz' / Real.log (1 / cz')) cBig)
      (min ((1 / 100) / Real.log 100)
        (min (cL' / Real.log (1 / cL')) (2 * c₁ * δ))) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    refine lt_min (lt_min (div_pos hcz'pos hlogcz') hcBigpos) ?_
    refine lt_min (div_pos (by norm_num) hlog100pos) ?_
    exact lt_min (div_pos hcL'pos hlogcL') (mul_pos (by positivity) hδpos)
  have hc_cz : c ≤ cz' / Real.log (1 / cz') := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc_big : c ≤ cBig := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc_100 : c ≤ (1 / 100) / Real.log 100 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hc_L : c ≤ cL' / Real.log (1 / cL') :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc_δ : c ≤ 2 * c₁ * δ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨c, hcpos, max (max (max qSig qOwn) (max qLand qzf)) 2, ?_⟩
  intro q hq hqne χ₁ β₁ hχ₁ hsq hβ₁ hz₁ hlam1le χ ρ hχ1 hzm him hnex
  haveI : NeZero q := hqne
  have hqSig : qSig ≤ q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hq
  have hqOwn : qOwn ≤ q := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hq
  have hqLand : qLand ≤ q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) hq
  have hqzf : qzf ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hq)
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hlam1pos : 0 < lamOf q (β₁ : ℂ) := by
    rw [lamOf]
    have h : ((β₁ : ℂ)).re = β₁ := Complex.ofReal_re β₁
    rw [h]
    exact mul_pos (by linarith) hlogq
  -- the minimal pair
  have hZ1 : IsZ χ₁ ((β₁ : ℝ) : ℂ) := ⟨hχ₁, hz₁, by simp⟩
  obtain ⟨χ₀, ρ₀, hmin⟩ := Work.A7.exists_isMin1 ⟨χ₁, ((β₁ : ℝ) : ℂ), hZ1⟩
  have hZ0 : IsZ χ₀ ρ₀ := hmin.1
  have hlam0le1 : lamOf q ρ₀ ≤ lamOf q ((β₁ : ℝ) : ℂ) := hmin.2 χ₁ _ hZ1
  have hlam0pos : 0 < lamOf q ρ₀ := by
    letI : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
    have hre := (Work.A7.isZ_LFunction_zero χ₀ hZ0).2.2
    rw [lamOf]
    exact mul_pos (by linarith) hlogq
  have hloglam : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (1 / lamOf q ρ₀) :=
    log_inv_le_log_inv hlam0pos hlam1pos hlam0le1
  have hloglam0nn : 0 ≤ Real.log (1 / lamOf q ρ₀) := by
    apply Real.log_nonneg
    rw [one_div, one_le_inv₀ hlam0pos]
    linarith
  have hloglam1nn : 0 ≤ Real.log (1 / lamOf q (β₁ : ℂ)) := by
    apply Real.log_nonneg
    rw [one_div, one_le_inv₀ hlam1pos]
    linarith [hlam1le]
  -- the two cases for the minimal pair
  by_cases hcase : cz' ≤ lamOf q ρ₀
  · -- the minimal pair is *not* in the Siegel regime: minimality alone suffices.
    have hlamρ : cz' ≤ lamOf q ρ :=
      le_trans hcase (hmin.2 χ ρ ⟨hχ1, hzm, him⟩)
    have hK : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (1 / cz') :=
      log_inv_le_log_inv hcz'pos hlam1pos (le_trans hcase hlam0le1)
    exact le_trans (mul_le_of_le_div hcpos hlogcz' hc_cz hloglam1nn hK) hlamρ
  · -- the Siegel regime: the minimal pair is a real zero of a real character.
    push Not at hcase
    have hlam0lt : lamOf q ρ₀ < cz' := hcase
    have hreal0 : χ₀ ^ 2 = 1 ∧ ρ₀.im = 0 := by
      by_contra hc
      have hcond : χ₀ ^ 2 ≠ 1 ∨ ρ₀.im ≠ 0 := by
        by_cases h : χ₀ ^ 2 = 1
        · exact Or.inr fun h2 => hc ⟨h, h2⟩
        · exact Or.inl h
      have hz := hzf q hqzf χ₀ ρ₀ hZ0.2.1 hZ0.2.2 hZ0.1 hcond
      exact absurd (le_trans hcz'le_zf hz) (not_le.mpr hlam0lt)
    have hlam0le12 : lamOf q ρ₀ ≤ 1 / 2 := le_trans (le_of_lt hlam0lt) hcz'le
    by_cases hpair : χ = χ₀ ∧ ρ = ρ₀
    · -- ===== the pair under consideration is the minimal pair =====
      obtain ⟨hχχ₀, hρρ₀⟩ := hpair
      have hne0 : ¬ (χ₁ = χ₀ ∧ ((β₁ : ℝ) : ℂ) = ρ₀) := by
        rintro ⟨h1, h2⟩
        exact hnex ⟨by rw [hχχ₀, h1], by rw [hρρ₀, h2]⟩
      have key : c * Real.log (1 / lamOf q (β₁ : ℂ)) ≤ lamOf q ρ₀ := by
        by_cases hχ10 : χ₁ = χ₀
        · -- the same character: `β₁` is another real zero of `χ₀`
          have hpoint : ((β₁ : ℝ) : ℂ) ≠ ρ₀ := fun h => hne0 ⟨hχ10, h⟩
          have hzm' : zeroMult χ₀ ((β₁ : ℝ) : ℂ) ≠ 0 := by rw [← hχ10]; exact hz₁
          have hb : c₁ * Real.log (1 / lamOf q ρ₀) ≤ lamOf q ((β₁ : ℝ) : ℂ) := by
            have h := hOwn q hqOwn χ₀ ρ₀ hmin hreal0.1 hreal0.2 hlam0le12 ((β₁ : ℝ) : ℂ)
              hzm' (by simp) hpoint
            exact le_trans (mul_le_mul_of_nonneg_right (le_trans hc₁_big hcBig_own) hloglam0nn) h
          exact self_repel hcpos hc₁pos hc_δ hlam0pos hlam0le1 hlam1le hb
        · -- different characters
          by_cases hpoint : ((β₁ : ℝ) : ℂ) = ρ₀
          · -- the two pairs share the point: Landau's repulsion bounds `λ₀` from below
            have hL := hLand q hqLand χ₀ ρ₀ χ₁ ((β₁ : ℝ) : ℂ) hZ0.1 hreal0.1 hreal0.2 hZ0.2.1
              hχ₁ hsq (by rw [hpoint]; exact hreal0.2) hz₁ hχ10
            rw [show lamOf q ((β₁ : ℝ) : ℂ) = lamOf q ρ₀ from by rw [hpoint], max_self] at hL
            have hle : cL' ≤ lamOf q ρ₀ := le_trans hcL'le_land hL
            have hK : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (1 / cL') := by
              rw [show lamOf q (β₁ : ℂ) = lamOf q ρ₀ from by rw [hpoint]]
              exact log_inv_le_log_inv hcL'pos hlam0pos hle
            exact le_trans (mul_le_of_le_div hcpos hlogcL' hc_L hloglam1nn hK) hle
          · -- distinct points: the Siegel-regime repulsion, or minimality for large `λ₀`
            by_cases hsmall : lamOf q ρ₀ ≤ 1 / 100
            · have h := hSig q hqSig χ₀ ρ₀ hmin hreal0.1 hreal0.2 hsmall χ₁ ((β₁ : ℝ) : ℂ)
                hχ10 hχ₁ hz₁ (by simp) hpoint
              have hb : c₁ * Real.log (1 / lamOf q ρ₀) ≤ lamOf q ((β₁ : ℝ) : ℂ) :=
                le_trans (mul_le_mul_of_nonneg_right (le_trans hc₁_big hcBig_sig) hloglam0nn) h
              exact self_repel hcpos hc₁pos hc_δ hlam0pos hlam0le1 hlam1le hb
            · push Not at hsmall
              have hb : c₁ * Real.log (1 / lamOf q ρ₀) ≤ lamOf q ((β₁ : ℝ) : ℂ) := by
                have h2 : Real.log (1 / lamOf q ρ₀) ≤ Real.log 100 := by
                  apply Real.log_le_log (by positivity)
                  rw [div_le_iff₀ hlam0pos]
                  linarith
                have h3 : ((1 / 100) / Real.log 100) * Real.log (1 / lamOf q ρ₀) ≤ 1 / 100 := by
                  rw [div_mul_eq_mul_div, div_le_iff₀ hlog100pos]
                  nlinarith [h2, hlog100pos]
                have h4 : (1 / 100 : ℝ) ≤ lamOf q ((β₁ : ℝ) : ℂ) := le_trans hsmall.le hlam0le1
                exact le_trans (mul_le_mul_of_nonneg_right hc₁_100 hloglam0nn) (le_trans h3 h4)
              exact self_repel hcpos hc₁pos hc_δ hlam0pos hlam0le1 hlam1le hb
      simpa [hρρ₀] using key
    · -- ===== the pair under consideration is *not* the minimal pair =====
      by_cases hχχ₀ : χ = χ₀
      · -- the same character, another zero
        have hzm' : zeroMult χ₀ ρ ≠ 0 := by rw [← hχχ₀]; exact hzm
        have hρρ₀ : ρ ≠ ρ₀ := fun h => hpair ⟨hχχ₀, h⟩
        have h := hOwn q hqOwn χ₀ ρ₀ hmin hreal0.1 hreal0.2 hlam0le12 ρ hzm' him hρρ₀
        exact mul_log_le_of_le hcpos hcOwnpos (le_trans hc_big hcBig_own) hloglam0nn hloglam h
      · -- a different character
        by_cases hρρ₀ : ρ = ρ₀
        · -- the shared point: minimality is useless; Landau or the zero-free region
          have hzmp : zeroMult χ ρ₀ ≠ 0 := by rw [← hρρ₀]; exact hzm
          by_cases hχsq : χ ^ 2 = 1
          · have hL := hLand q hqLand χ₀ ρ₀ χ ρ₀ hZ0.1 hreal0.1 hreal0.2 hZ0.2.1
              hχ1 hχsq hreal0.2 hzmp hχχ₀
            rw [max_self] at hL
            have hle : cL' ≤ lamOf q ρ₀ := le_trans hcL'le_land hL
            have hK : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (1 / cL') :=
              le_trans hloglam (log_inv_le_log_inv hcL'pos hlam0pos hle)
            have h1 : c * Real.log (1 / lamOf q (β₁ : ℂ)) ≤ cL' :=
              mul_le_of_le_div hcpos hlogcL' hc_L hloglam1nn hK
            simpa [hρρ₀] using le_trans h1 hle
          · have hz := hzf q hqzf χ ρ₀ hzmp (by rw [hreal0.2]; norm_num) hχ1 (Or.inl hχsq)
            have hle : cz' ≤ lamOf q ρ₀ := le_trans hcz'le_zf hz
            have hK : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (1 / cz') :=
              le_trans hloglam (log_inv_le_log_inv hcz'pos hlam0pos hle)
            have h1 : c * Real.log (1 / lamOf q (β₁ : ℂ)) ≤ cz' :=
              mul_le_of_le_div hcpos hlogcz' hc_cz hloglam1nn hK
            simpa [hρρ₀] using le_trans h1 hle
        · -- distinct points and characters
          by_cases hsmall : lamOf q ρ₀ ≤ 1 / 100
          · have h := hSig q hqSig χ₀ ρ₀ hmin hreal0.1 hreal0.2 hsmall χ ρ hχχ₀ hχ1 hzm him hρρ₀
            exact mul_log_le_of_le hcpos hcSigpos (le_trans hc_big hcBig_sig) hloglam0nn hloglam h
          · push Not at hsmall
            have hlamρ : lamOf q ρ₀ ≤ lamOf q ρ := hmin.2 χ ρ ⟨hχ1, hzm, him⟩
            have hK : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log 100 := by
              refine le_trans hloglam ?_
              apply Real.log_le_log (by positivity)
              rw [div_le_iff₀ hlam0pos]
              linarith
            have h1 : c * Real.log (1 / lamOf q (β₁ : ℂ)) ≤ 1 / 100 :=
              mul_le_of_le_div hcpos hlog100pos hc_100 hloglam1nn hK
            exact le_trans h1 (le_trans hsmall.le hlamρ)

theorem ZFRInput_exists : ∃ cZ : ℝ, 0 < cZ ∧ Work.LinnikAreas.BGTZ.ZFRInput cZ := by
  exact ZFRInput_of_repulsion (PairRepelNonPrin_of_mass Work.LinnikAreas.turanAux2.lMultMassRect)

end

end Work.LinnikAreas.BGTZ
