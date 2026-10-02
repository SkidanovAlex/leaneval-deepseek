/-
# LinnikContract2 — Area 4, `(D2)`: Heath-Brown's Table 13 via Lemma 12.1

This is the heart of the round-2 `(D2)`: given a modulus `q` at which **every** non-principal
character of height `≤ 50` has a zero-free level `λ ≥ lam1`, the number of characters of the
working region carrying a zero of level `≤ lam` is at most `N0`, whenever the Table-13 certificate
`rowCert lam lam1 N0` holds.

The proof is Heath-Brown (1992), §12:
* enumerate the `N = N(λ)` characters `χ^(j)` and their box zeros `ρ^(j) = β₁ + iγ^(j)`
  (`β₁ = 1 - λ₁/𝓛`, `𝓛 = log q`), `exists_enum`;
* apply the `K`-bounds of HB Lemma 5.2 (non-principal `χ`, imprimitive included) at `s = β₁+iγ^(j)`
  and at `s = β₁ + i(γ^(j)-γ^(k))` for `j ≠ k` (`KboundGenShape`, `Ksum_le_self_of_L52_phi`), and
  HB Lemma 5.3 for the principal character (`Ksum_principal_le`);
* Cauchy–Schwarz (`hb_lemma12_1`) with the §7 test function, whose two numerical side conditions
  at `ε = 0` are the content of `sideCond` (certified row by row in `T13Side*`/`T13Cert`).
-/
import Mathlib
import Submission.Work.LinnikAreas2.D2Aux
import Submission.Work.LinnikAreas2.T13Cert
import Submission.Work.LinnikAreas2.exists_eps_side
import Submission.Work.LinnikContract2.A7.WindowAssembly

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-- The `K`-bound supplied by `Kbound_gen` (HB Lemma 5.2 at a zero of an arbitrary non-principal
character, with the zero-free input at height `2`; `Kbound_gen` derives it from `Area1`). -/
def KboundGenShape : Prop :=
  ∀ (eps0 lam1 : ℝ), 0 < eps0 → 0 ≤ lam1 →
  ∀ (theta lamhat : ℝ), 0 < lamhat → Real.pi / 2 < theta → theta < Real.pi →
    ∃ q0 : ℕ, ∀ q : ℕ, q0 ≤ q → ∀ [NeZero q] (chi : DirichletCharacter ℂ q) (rho : ℂ),
      chi ≠ 1 → Work.LinnikContract2.IsZ chi rho →
      Work.LinnikContract2.lamOf q rho ≤ Work.LinnikContract2.lamMax q →
      (∀ (chi' : DirichletCharacter ℂ q) (rho' : ℂ), chi' ≠ 1 →
          Work.LinnikContract2.zeroMult chi' rho' ≠ 0 → |rho'.im| ≤ 2 →
          lam1 ≤ Work.LinnikContract2.lamOf q rho') →
      Work.LinnikAreas.Density4.Kgen q (Real.log q) (1 - lam1 / Real.log q) rho.im
          (Work.LinnikAreas.Density4.fT theta lamhat) chi
        ≤ -Real.log q * Work.LinnikAreas.Density4.Lapl
            (2 * Work.LinnikAreas.Density4.gammaT theta lamhat)
            (Work.LinnikAreas.Density4.fT theta lamhat)
            (Work.LinnikContract2.lamOf q rho - lam1)
          + Work.LinnikAreas.Density4.fT theta lamhat 0 * ((1/6 : ℝ) + eps0) * Real.log q

/-- **HB §12 for one Table-13 row.** -/
theorem d2_row (h1 : Work.LinnikContract2.Area1) (hKb : KboundGenShape)
    {lam lam1 : ℝ} {N0 : ℕ}
    (hlam : 0 < lam) (hlam1 : 0 ≤ lam1) (hlamle : lam ≤ 2) (hlam1le : lam1 ≤ 1)
    (hθ1 : Real.pi / 2 < theta13 lam lam1) (hθ2 : theta13 lam lam1 < Real.pi)
    (hside : sideCond lam lam1)
    (hbnd : bnd13 lam lam1 < (N0 : ℝ) + 1) :
    ∃ q0 : ℕ, ∀ q : ℕ, q0 ≤ q → ∀ [NeZero q],
      (∀ (chi : DirichletCharacter ℂ q) (rho : ℂ), Work.LinnikContract2.IsZH 50 chi rho →
        lam1 ≤ Work.LinnikContract2.lamOf q rho) →
      Work.LinnikContract2.Ncount q lam ≤ N0 := by
  classical
  set th : ℝ := theta13 lam lam1 with hth
  set x0 : ℝ := 2 * gammaT th lam with hx0def
  set ff : ℝ → ℝ := fT th lam with hff
  have hx0 : 0 < x0 := by
    rw [hx0def]
    have h := gammaT_pos hθ1 hθ2 hlam; linarith only [h]
  obtain ⟨hcontT, hf0T, hf2T, B, hBnn, hBndT⟩ := fTregular (θ := th) (lam := lam) hθ1 hθ2 hlam
  have hnnT : ∀ t, 0 ≤ ff t := by
    intro t; rw [hff]; exact fT_nonneg th lam hθ1 hθ2 hlam t
  have hsupT : ∀ t, x0 ≤ t → ff t = 0 := by
    intro t ht
    rw [hff]
    exact fT_eq_zero_of_two_gammaT_le th lam hθ1 hθ2 hlam t (by rw [hx0def] at ht; exact ht)
  have hcond2T := fTcond2 (θ := th) (lam := lam) hθ1 hθ2 hlam
  have hf0 : 0 < ff 0 := by rw [hff]; exact hf0T
  have hcontF : ContinuousOn ff (Set.Ici 0) := by rw [hff]; exact hcontT
  have hApos : 0 < Lapl x0 ff (-lam1) := lapl_neg_arg_pos hx0 hcontF hnnT hf0 lam1
  have hFanti : ∀ a b : ℝ, a ≤ b → Lapl x0 ff b ≤ Lapl x0 ff a :=
    fun a b hab => lapl_antitone_on hx0.le hcontF hnnT hab
  -- ### the two side conditions at `eps = 0` (in the `FT` shape of `sideCond`/`bnd13`)
  have hpos0 : ff 0 * ((1:ℝ)/6) < FT (theta13 lam lam1) lam (lam - lam1) := by
    have h := hside.1
    have h2 : ff 0 * ((1:ℝ)/6) = fT (theta13 lam lam1) lam 0 / 6 := by rw [hff, hth]; ring
    rwa [h2]
  have hden0 : ff 0 * ((1:ℝ)/6) * FT (theta13 lam lam1) lam (-lam1)
      < (FT (theta13 lam lam1) lam (lam - lam1) - ff 0 * ((1:ℝ)/6))^2 := by
    have h := hside.2
    have h2 : ff 0 * ((1:ℝ)/6) = fT (theta13 lam lam1) lam 0 / 6 := by rw [hff, hth]; ring
    rw [h2]
    linarith only [h, mul_comm (fT (theta13 lam lam1) lam 0 / 6) (FT (theta13 lam lam1) lam (-lam1))]
  have hbnd0 : FT (theta13 lam lam1) lam (-lam1)
        * (FT (theta13 lam lam1) lam (-lam1) - fT (theta13 lam lam1) lam 0 / 6)
        / ((FT (theta13 lam lam1) lam (lam - lam1) - fT (theta13 lam lam1) lam 0 / 6)^2
          - FT (theta13 lam lam1) lam (-lam1) * (fT (theta13 lam lam1) lam 0 / 6))
      < (N0 : ℝ) + 1 := by
    have h := hbnd
    unfold bnd13 at h
    convert h using 1
    ring
  obtain ⟨eps, heps, hposE, hdenE, hbndE⟩ := exists_eps_side hf0 hApos hpos0 hden0 hbnd0
  -- ### thresholds
  obtain ⟨qK, hqK⟩ := hKb eps lam1 heps hlam1 th lam hlam hθ1 hθ2
  obtain ⟨L₀, δ, hδ0, hδ1, h31⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1:ℝ)/3) (by norm_num) (ε := eps/4) (by positivity) h1.1
  obtain ⟨qS, hqS⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi
    (x₀ := x0) (B := B) (c := (1:ℝ)/6) hx0 hBnn hcontF hsupT hf2T hBndT hf0 hcond2T
    heps hδ0 hδ1
  obtain ⟨qP, hqP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le
    (x₀ := x0) (B := B) hx0 hBnn hcontF hsupT hf2T hBndT heps hf0
  obtain ⟨Q1, hQ1⟩ := exists_threshold_lamMax lam hlam.le
  obtain ⟨Q2, hQ2⟩ := exists_threshold_loglog
  refine ⟨qK + qS + qP + (Nat.ceil (Real.exp L₀) + 3) + Q1 + Q2 + 3, ?_⟩
  intro q hq _inst hzero
  have hqK' : qK ≤ q := by omega
  have hqS' : qS ≤ q := by omega
  have hqP' : qP ≤ q := by omega
  have hQ1' : Q1 ≤ q := by omega
  have hQ2' : Q2 ≤ q := by omega
  have hQ3' : Nat.ceil (Real.exp L₀) + 3 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hqpos : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hLpos : 0 < Real.log (q:ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast (by omega : 1 < q)
  have hL1 : 1 ≤ Real.log (q:ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by
      have h1 : Real.exp 1 ≤ (q:ℝ) := by
        have h2 : Real.exp 1 ≤ (3:ℝ) := le_of_lt Real.exp_one_lt_three
        have h3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq3
        linarith only [h2, h3]
      linarith only [h1])
  have hL₀le : L₀ ≤ Real.log (q:ℝ) := by
    have h1 : Real.exp L₀ ≤ (q:ℝ) := by
      have h2 : Real.exp L₀ ≤ (Nat.ceil (Real.exp L₀) : ℝ) := Nat.le_ceil _
      have h3 : (Nat.ceil (Real.exp L₀) : ℝ) ≤ (q:ℝ) := by
        have : Nat.ceil (Real.exp L₀) ≤ q := by omega
        exact_mod_cast this
      linarith only [h2, h3]
    calc L₀ = Real.log (Real.exp L₀) := (Real.log_exp L₀).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos L₀) h1
  have hlamMax : lam ≤ Work.LinnikContract2.lamMax q := hQ1 q hQ1'
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) :=
    Real.one_le_sqrt.mpr (hQ2 q hQ2')
  have hsqrt : lam1 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := le_trans hlam1le hsqrt1
  -- ### the enumeration
  set S : Finset (DirichletCharacter ℂ q) := Finset.univ.filter (fun chi =>
      ∃ rho, Work.LinnikContract2.IsZ chi rho ∧ Work.LinnikContract2.lamOf q rho ≤ lam) with hSdef
  have hScard : S.card = Work.LinnikContract2.Ncount q lam := rfl
  rcases Nat.eq_zero_or_pos S.card with h0 | hSp
  · rw [← hScard, h0]
    exact Nat.zero_le _
  · obtain ⟨chi, rho, hchi_inj, hrhoZ, hrhole⟩ := exists_enum lam S (fun chi hchi => by
      have hchi' : chi ∈ Finset.univ.filter (fun chi =>
          ∃ rho, Work.LinnikContract2.IsZ chi rho ∧ Work.LinnikContract2.lamOf q rho ≤ lam) := by
        rwa [← hSdef]
      exact (Finset.mem_filter.mp hchi').2)
    -- ### the `K`-bounds
    have hK1 : ∀ j : Fin S.card,
        Kgen q (Real.log q) (1 - lam1 / Real.log q) ((rho j).im) ff (chi j)
          ≤ -(Real.log q * Lapl x0 ff (Work.LinnikContract2.lamOf q (rho j) - lam1))
            + ff 0 * (1/6 + eps) * Real.log q := by
      intro j
      have h := hqK q hqK' (chi j) (rho j) (Work.LinnikContract2.isZ_ne_one (hrhoZ j)) (hrhoZ j)
        (le_trans (hrhole j) hlamMax)
        (fun chi' rho' h1' h2' h3' => hzero chi' rho' ⟨h1', h2', by linarith only [hδ0, hδ1, h3']⟩)
      rw [neg_mul] at h
      exact h
    have hK2 : Kgen q (Real.log q) (1 - lam1 / Real.log q) 0 ff 1
        ≤ Real.log q * Lapl x0 ff (-lam1) + ff 0 * eps * Real.log q := by
      rw [Kgen_real_eq]
      have h := hqP (q := q) hqP' (β := 1 - lam1 / Real.log q) (lam := lam1) (by
          rw [show (1:ℝ) - (1 - lam1 / Real.log (q:ℝ)) = lam1 / Real.log (q:ℝ) by ring]
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hLpos)])
        (by
          rw [show (1 - lam1 / Real.log (q:ℝ)) - 1 = -(lam1 / Real.log (q:ℝ)) by ring, abs_neg,
            abs_div, abs_of_pos hLpos, abs_of_nonneg hlam1]
          exact div_le_div_of_nonneg_right hsqrt hLpos.le)
      rw [integral_exp_mul_eq_lapl] at h
      exact h
    have hK3 : ∀ j k : Fin S.card, j ≠ k →
        Kgen q (Real.log q) (1 - lam1 / Real.log q) ((rho j).im - (rho k).im)
          ff (chi j * (chi k)⁻¹)
        ≤ ff 0 * (1/6 + eps) * Real.log q := by
      intro j k hjk
      rw [Kgen_complex_eq]
      set s : ℂ := ((1 - lam1 / Real.log q : ℝ) : ℂ)
        + (((rho j).im - (rho k).im : ℝ) : ℂ) * Complex.I with hsdef
      have hχne : chi j * (chi k)⁻¹ ≠ 1 := by
        intro h
        exact hjk (hchi_inj (mul_inv_eq_one.mp h))
      haveI : NeZero (chi j * (chi k)⁻¹).conductor := ⟨(chi j * (chi k)⁻¹).conductor_ne_zero⟩
      have hχs : (chi j * (chi k)⁻¹).primitiveCharacter ≠ 1 := by
        intro h
        apply hχne
        rw [← DirichletCharacter.changeLevel_primitiveCharacter (chi j * (chi k)⁻¹), h]
        exact DirichletCharacter.changeLevel_one (chi j * (chi k)⁻¹).conductor_dvd_level
      have hcon : 3 ≤ (chi j * (chi k)⁻¹).conductor := three_le_conductor _ hχne
      have hlogc : Real.log (((chi j * (chi k)⁻¹).conductor : ℕ) : ℝ) ≤ Real.log (q:ℝ) := by
        refine Real.log_le_log ?_ ?_
        · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
        · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
            (chi j * (chi k)⁻¹).conductor_dvd_level
      have hsre : s.re = 1 - lam1 / Real.log (q:ℝ) := by
        rw [hsdef]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      have hsim : s.im = (rho j).im - (rho k).im := by
        rw [hsdef]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
      have hsim2 : |s.im| ≤ 2 := by
        rw [hsim]
        have h6 := Work.LinnikContract2.isZ_im_le_one (hrhoZ j)
        have h7 := Work.LinnikContract2.isZ_im_le_one (hrhoZ k)
        calc |(rho j).im - (rho k).im| = |(rho j).im + -((rho k).im)| := by
              rw [sub_eq_add_neg]
          _ ≤ |(rho j).im| + |-((rho k).im)| := abs_add_le _ _
          _ = |(rho j).im| + |(rho k).im| := by rw [abs_neg]
          _ ≤ 2 := by linarith only [h6, h7]
      have hH : Commons.NumberTheory.Linnik.L52Hyp (chi j * (chi k)⁻¹) (1/6) eps δ := by
        intro s' hs1 hs2 hs3
        have h := h31 (N := (chi j * (chi k)⁻¹).conductor) hcon
          ((chi j * (chi k)⁻¹).primitiveCharacter) hχs
          (DirichletCharacter.primitiveCharacter_isPrimitive _)
          (L := Real.log (q:ℝ)) hL₀le hlogc s' hs1 hs2 hs3
        convert h using 1
        ring
      have hzw : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction
            (chi j * (chi k)⁻¹).primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
          ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
        intro u hdu hwu
        have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction
            (chi j * (chi k)⁻¹).primitiveCharacter) (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
          fun z _ => (DirichletCharacter.differentiable_completedLFunction hχs).analyticAt z
        have hu_ball : u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := by
          by_contra hu
          have h0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction
              (chi j * (chi k)⁻¹).primitiveCharacter)
              (Metric.closedBall (0:ℂ) (|s.im| + 2)) u = 0 := by
            rw [MeromorphicOn.divisor_def, if_neg]
            exact fun hc => hu hc.2
          exact hdu h0
        have hu_an : analyticOrderNatAt (DirichletCharacter.completedLFunction
            (chi j * (chi k)⁻¹).primitiveCharacter) u ≠ 0 := by
          have h := hdu
          rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu_ball] at h
          exact_mod_cast h
        have hzu : Work.LinnikContract2.zeroMult (chi j * (chi k)⁻¹) u ≠ 0 := by
          simpa [Work.LinnikContract2.zeroMult] using hu_an
        have huim : |u.im| ≤ 3 := by
          have h1 : |s.im - u.im| ≤ δ := by
            have h2 : ((1:ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
            calc |s.im - u.im| = |((1:ℂ) + (s.im : ℂ) * Complex.I - u).im| := by rw [h2]
              _ ≤ ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ := Complex.abs_im_le_norm _
              _ ≤ δ := hwu
          have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
            calc |u.im| = |s.im + (u.im - s.im)| := by rw [add_sub_cancel]
              _ ≤ |s.im| + |u.im - s.im| := abs_add_le _ _
              _ = |s.im| + |s.im - u.im| := by rw [abs_sub_comm]
          linarith only [h3, hsim2, h1, hδ1]
        have hu := hzero _ u ⟨hχne, hzu, by linarith only [hδ0, hδ1, huim]⟩
        rw [Work.LinnikContract2.lamOf] at hu
        rw [hsre]
        have h2 : lam1 / Real.log (q:ℝ) ≤ 1 - u.re := by rw [div_le_iff₀ hLpos]; linarith only [hu]
        linarith only [h2]
      have h := hqS (q := q) hqS' (chi j * (chi k)⁻¹) hχne (s := s)
        (by
          rw [hsre, show (1 - lam1 / Real.log (q:ℝ)) - 1 = -(lam1 / Real.log (q:ℝ)) by ring,
            abs_neg, abs_div, abs_of_pos hLpos, abs_of_nonneg hlam1]
          exact div_le_div_of_nonneg_right hsqrt hLpos.le)
        (by linarith only [hsim2, hL1, hδ0, hδ1])
        (by
          rw [hsre]
          have h2 : lam1 / Real.log (q:ℝ) ≤ Real.sqrt (Real.log (Real.log (q:ℝ)))
              / Real.log (q:ℝ) := div_le_div_of_nonneg_right hsqrt hLpos.le
          linarith only [h2])
        hH hzw
      exact h
    -- ### Cauchy–Schwarz
    have key := hb_lemma12_1 (q := q) (Real.log (q:ℝ)) hLpos (x₀ := x0) hx0
      (f := ff) hnnT hsupT hf0 heps.le (lam₁ := lam1) (lam := lam) hSp
      (χ := chi) (γ := fun j => (rho j).im) (lamv := fun j => Work.LinnikContract2.lamOf q (rho j))
      hK1 hK2 hK3 (fun j => hrhole j) hFanti hApos hposE hdenE
    have hlt : ((Work.LinnikContract2.Ncount q lam : ℕ) : ℝ) < (N0 : ℝ) + 1 := by
      rw [← hScard]
      exact lt_of_le_of_lt key hbndE
    exact Work.LinnikAreas.Density4.Ncount_le_of_lt hlt


/-- **`(D2)`, from the K-bound shape and the Table-13 certificates** (this is the round-2 `(D2)`:
`d2_of_area1` in `Area4Main` instantiates `hKb := Kbound_gen h1`). -/
theorem d2_of_area1_aux (h1 : Work.LinnikContract2.Area1) (hKb : KboundGenShape) :
    Work.LinnikContract2.D2 := by
  intro e he
  fin_cases he
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_0).1 (rowCert_0).2.1 (rowCert_0).2.2.1 (rowCert_0).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_1).1 (rowCert_1).2.1 (rowCert_1).2.2.1 (rowCert_1).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_2).1 (rowCert_2).2.1 (rowCert_2).2.2.1 (rowCert_2).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_3).1 (rowCert_3).2.1 (rowCert_3).2.2.1 (rowCert_3).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_4).1 (rowCert_4).2.1 (rowCert_4).2.2.1 (rowCert_4).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_5).1 (rowCert_5).2.1 (rowCert_5).2.2.1 (rowCert_5).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_6).1 (rowCert_6).2.1 (rowCert_6).2.2.1 (rowCert_6).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_7).1 (rowCert_7).2.1 (rowCert_7).2.2.1 (rowCert_7).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_8).1 (rowCert_8).2.1 (rowCert_8).2.2.1 (rowCert_8).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_9).1 (rowCert_9).2.1 (rowCert_9).2.2.1 (rowCert_9).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_10).1 (rowCert_10).2.1 (rowCert_10).2.2.1 (rowCert_10).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_11).1 (rowCert_11).2.1 (rowCert_11).2.2.1 (rowCert_11).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_12).1 (rowCert_12).2.1 (rowCert_12).2.2.1 (rowCert_12).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_13).1 (rowCert_13).2.1 (rowCert_13).2.2.1 (rowCert_13).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_14).1 (rowCert_14).2.1 (rowCert_14).2.2.1 (rowCert_14).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_15).1 (rowCert_15).2.1 (rowCert_15).2.2.1 (rowCert_15).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_16).1 (rowCert_16).2.1 (rowCert_16).2.2.1 (rowCert_16).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_17).1 (rowCert_17).2.1 (rowCert_17).2.2.1 (rowCert_17).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_18).1 (rowCert_18).2.1 (rowCert_18).2.2.1 (rowCert_18).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_19).1 (rowCert_19).2.1 (rowCert_19).2.2.1 (rowCert_19).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_20).1 (rowCert_20).2.1 (rowCert_20).2.2.1 (rowCert_20).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_21).1 (rowCert_21).2.1 (rowCert_21).2.2.1 (rowCert_21).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_22).1 (rowCert_22).2.1 (rowCert_22).2.2.1 (rowCert_22).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_23).1 (rowCert_23).2.1 (rowCert_23).2.2.1 (rowCert_23).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_24).1 (rowCert_24).2.1 (rowCert_24).2.2.1 (rowCert_24).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_25).1 (rowCert_25).2.1 (rowCert_25).2.2.1 (rowCert_25).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_26).1 (rowCert_26).2.1 (rowCert_26).2.2.1 (rowCert_26).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_27).1 (rowCert_27).2.1 (rowCert_27).2.2.1 (rowCert_27).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_28).1 (rowCert_28).2.1 (rowCert_28).2.2.1 (rowCert_28).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_29).1 (rowCert_29).2.1 (rowCert_29).2.2.1 (rowCert_29).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_30).1 (rowCert_30).2.1 (rowCert_30).2.2.1 (rowCert_30).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_31).1 (rowCert_31).2.1 (rowCert_31).2.2.1 (rowCert_31).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_32).1 (rowCert_32).2.1 (rowCert_32).2.2.1 (rowCert_32).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_33).1 (rowCert_33).2.1 (rowCert_33).2.2.1 (rowCert_33).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_34).1 (rowCert_34).2.1 (rowCert_34).2.2.1 (rowCert_34).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_35).1 (rowCert_35).2.1 (rowCert_35).2.2.1 (rowCert_35).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_36).1 (rowCert_36).2.1 (rowCert_36).2.2.1 (rowCert_36).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_37).1 (rowCert_37).2.1 (rowCert_37).2.2.1 (rowCert_37).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_38).1 (rowCert_38).2.1 (rowCert_38).2.2.1 (rowCert_38).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_39).1 (rowCert_39).2.1 (rowCert_39).2.2.1 (rowCert_39).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_40).1 (rowCert_40).2.1 (rowCert_40).2.2.1 (rowCert_40).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_41).1 (rowCert_41).2.1 (rowCert_41).2.2.1 (rowCert_41).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_42).1 (rowCert_42).2.1 (rowCert_42).2.2.1 (rowCert_42).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_43).1 (rowCert_43).2.1 (rowCert_43).2.2.1 (rowCert_43).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_44).1 (rowCert_44).2.1 (rowCert_44).2.2.1 (rowCert_44).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_45).1 (rowCert_45).2.1 (rowCert_45).2.2.1 (rowCert_45).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_46).1 (rowCert_46).2.1 (rowCert_46).2.2.1 (rowCert_46).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_47).1 (rowCert_47).2.1 (rowCert_47).2.2.1 (rowCert_47).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_48).1 (rowCert_48).2.1 (rowCert_48).2.2.1 (rowCert_48).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_49).1 (rowCert_49).2.1 (rowCert_49).2.2.1 (rowCert_49).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_50).1 (rowCert_50).2.1 (rowCert_50).2.2.1 (rowCert_50).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_51).1 (rowCert_51).2.1 (rowCert_51).2.2.1 (rowCert_51).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_52).1 (rowCert_52).2.1 (rowCert_52).2.2.1 (rowCert_52).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_53).1 (rowCert_53).2.1 (rowCert_53).2.2.1 (rowCert_53).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_54).1 (rowCert_54).2.1 (rowCert_54).2.2.1 (rowCert_54).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_55).1 (rowCert_55).2.1 (rowCert_55).2.2.1 (rowCert_55).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_56).1 (rowCert_56).2.1 (rowCert_56).2.2.1 (rowCert_56).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_57).1 (rowCert_57).2.1 (rowCert_57).2.2.1 (rowCert_57).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_58).1 (rowCert_58).2.1 (rowCert_58).2.2.1 (rowCert_58).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_59).1 (rowCert_59).2.1 (rowCert_59).2.2.1 (rowCert_59).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_60).1 (rowCert_60).2.1 (rowCert_60).2.2.1 (rowCert_60).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_61).1 (rowCert_61).2.1 (rowCert_61).2.2.1 (rowCert_61).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_62).1 (rowCert_62).2.1 (rowCert_62).2.2.1 (rowCert_62).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_63).1 (rowCert_63).2.1 (rowCert_63).2.2.1 (rowCert_63).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_64).1 (rowCert_64).2.1 (rowCert_64).2.2.1 (rowCert_64).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_65).1 (rowCert_65).2.1 (rowCert_65).2.2.1 (rowCert_65).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_66).1 (rowCert_66).2.1 (rowCert_66).2.2.1 (rowCert_66).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_67).1 (rowCert_67).2.1 (rowCert_67).2.2.1 (rowCert_67).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_68).1 (rowCert_68).2.1 (rowCert_68).2.2.1 (rowCert_68).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_69).1 (rowCert_69).2.1 (rowCert_69).2.2.1 (rowCert_69).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_70).1 (rowCert_70).2.1 (rowCert_70).2.2.1 (rowCert_70).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_71).1 (rowCert_71).2.1 (rowCert_71).2.2.1 (rowCert_71).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_72).1 (rowCert_72).2.1 (rowCert_72).2.2.1 (rowCert_72).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_73).1 (rowCert_73).2.1 (rowCert_73).2.2.1 (rowCert_73).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_74).1 (rowCert_74).2.1 (rowCert_74).2.2.1 (rowCert_74).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_75).1 (rowCert_75).2.1 (rowCert_75).2.2.1 (rowCert_75).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_76).1 (rowCert_76).2.1 (rowCert_76).2.2.1 (rowCert_76).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_77).1 (rowCert_77).2.1 (rowCert_77).2.2.1 (rowCert_77).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_78).1 (rowCert_78).2.1 (rowCert_78).2.2.1 (rowCert_78).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_79).1 (rowCert_79).2.1 (rowCert_79).2.2.1 (rowCert_79).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_80).1 (rowCert_80).2.1 (rowCert_80).2.2.1 (rowCert_80).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_81).1 (rowCert_81).2.1 (rowCert_81).2.2.1 (rowCert_81).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_82).1 (rowCert_82).2.1 (rowCert_82).2.2.1 (rowCert_82).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_83).1 (rowCert_83).2.1 (rowCert_83).2.2.1 (rowCert_83).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_84).1 (rowCert_84).2.1 (rowCert_84).2.2.1 (rowCert_84).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_85).1 (rowCert_85).2.1 (rowCert_85).2.2.1 (rowCert_85).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_86).1 (rowCert_86).2.1 (rowCert_86).2.2.1 (rowCert_86).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_87).1 (rowCert_87).2.1 (rowCert_87).2.2.1 (rowCert_87).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_88).1 (rowCert_88).2.1 (rowCert_88).2.2.1 (rowCert_88).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_89).1 (rowCert_89).2.1 (rowCert_89).2.2.1 (rowCert_89).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_90).1 (rowCert_90).2.1 (rowCert_90).2.2.1 (rowCert_90).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_91).1 (rowCert_91).2.1 (rowCert_91).2.2.1 (rowCert_91).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_92).1 (rowCert_92).2.1 (rowCert_92).2.2.1 (rowCert_92).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_93).1 (rowCert_93).2.1 (rowCert_93).2.2.1 (rowCert_93).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_94).1 (rowCert_94).2.1 (rowCert_94).2.2.1 (rowCert_94).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_95).1 (rowCert_95).2.1 (rowCert_95).2.2.1 (rowCert_95).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_96).1 (rowCert_96).2.1 (rowCert_96).2.2.1 (rowCert_96).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_97).1 (rowCert_97).2.1 (rowCert_97).2.2.1 (rowCert_97).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_98).1 (rowCert_98).2.1 (rowCert_98).2.2.1 (rowCert_98).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_99).1 (rowCert_99).2.1 (rowCert_99).2.2.1 (rowCert_99).2.2.2
  · exact d2_row h1 hKb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (rowCert_100).1 (rowCert_100).2.1 (rowCert_100).2.2.1 (rowCert_100).2.2.2

end Work.LinnikAreas2
