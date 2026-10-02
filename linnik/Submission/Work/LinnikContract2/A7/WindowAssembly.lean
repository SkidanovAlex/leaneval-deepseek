import Mathlib
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.Bridge
import Submission.Work.LinnikContract2.Numbering
import Submission.Work.LinnikContract2.A7.WindowCert
import Submission.Work.LinnikContract2.A7.Area7
import Submission.Work.LinnikContract2.A7.sec15_caseB
import Submission.Work.LinnikContract2.A7.table13_col_le
import Submission.Work.A7.sec15_uniform
import Submission.Work.A7.sec14_uniform
import Submission.Work.A7.box_api7
import Submission.Work.A7.chi1_inv_api
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace Work.LinnikContract2.A7

/-! ## Bookkeeping (copies of the private helpers of `A7/area7_of_isZ_or_large.lean`) -/

/-- The per-entry thresholds of the round-2 `(D2)` can be replaced by a single one, by taking the
(finite) maximum over `table13`. -/
private lemma exists_d2_uniform'
    (hD2 : ∀ e ∈ table13, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → e.2.1 ≤ lamOf q ρ) →
      Ncount q e.1 ≤ e.2.2) :
    ∃ q₀ : ℕ, ∀ e ∈ table13, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → e.2.1 ≤ lamOf q ρ) →
      Ncount q e.1 ≤ e.2.2 := by
  classical
  let f : ℝ × ℝ × ℕ → ℕ := fun e => if h : e ∈ table13 then Classical.choose (hD2 e h) else 0
  have hne : table13.toFinset.Nonempty :=
    ⟨((8:ℝ)/10, (348:ℝ)/1000, 8), List.mem_toFinset.mpr List.mem_cons_self⟩
  refine ⟨table13.toFinset.sup' hne f, ?_⟩
  intro e he q hq _
  have hle : f e ≤ table13.toFinset.sup' hne f := Finset.le_sup' f (List.mem_toFinset.mpr he)
  have hfe : f e = Classical.choose (hD2 e he) := by simp only [f]; rw [dif_pos he]
  rw [hfe] at hle
  exact (Classical.choose_spec (hD2 e he)) q (le_trans hle hq)

/-- If `q ≥ ⌈e^{e^{e^{3R}}}⌉ + 2` then `R ≤ log q` and `R ≤ lamMax q = log log log q / 3`. -/
private lemma R_le_log_and_lamMax' {q : ℕ} (_hq : 2 ≤ q) {R : ℝ} (hR : 0 < R)
    (h : Nat.ceil (Real.exp (Real.exp (Real.exp (3 * R)))) + 2 ≤ q) :
    R ≤ Real.log (q : ℝ) ∧ R ≤ lamMax q := by
  have hx : Real.exp (Real.exp (Real.exp (3 * R))) ≤ (q : ℝ) := by
    have h1 := Nat.le_ceil (Real.exp (Real.exp (Real.exp (3 * R))))
    have h2 : (Nat.ceil (Real.exp (Real.exp (Real.exp (3 * R)))) : ℝ) + 2 ≤ (q : ℝ) := by
      exact_mod_cast h
    linarith
  have hlogq : Real.exp (Real.exp (3 * R)) ≤ Real.log (q : ℝ) := by
    have h2 := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h2
  have hexp3 : R ≤ Real.exp (Real.exp (3 * R)) := by
    have h1 : 3 * R + 1 ≤ Real.exp (3 * R) := by
      simpa using Real.add_one_le_exp (3 * R)
    have h2 : Real.exp (3 * R) + 1 ≤ Real.exp (Real.exp (3 * R)) := Real.add_one_le_exp _
    linarith
  have hRlogq : R ≤ Real.log (q : ℝ) := le_trans hexp3 hlogq
  have hllq : Real.exp (3 * R) ≤ Real.log (Real.log (q : ℝ)) := by
    have h2 := Real.log_le_log (Real.exp_pos (Real.exp (3 * R))) hlogq
    rwa [Real.log_exp] at h2
  have h3 : 3 * R ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    have h2 := Real.log_le_log (Real.exp_pos (3 * R)) hllq
    rwa [Real.log_exp] at h2
  exact ⟨hRlogq, by rw [lamMax]; linarith⟩

/-! ## The narrow pivot in the branch `¬ IsZ χ₁ ρ₁`

If the wide minimiser `ρ₁` does **not** lie in the working region, then every working-region
minimiser has `λ ≥ 695/1000`.  Indeed `(Z3)` bounds by `0.701` all working-region zeros
outside the two characters `χ₁, χ₁⁻¹` (`Lam2Bound`), and bounds by `0.695` all working-region
zeros of `χ₁` other than `ρ₁` and [`χ₁` real] `conj ρ₁` (`Lam0Bound`); the two exceptions are
outside the working region because `|Im ρ₁| > 1`, and the `χ₁⁻¹`-zeros are the conjugates of
the `χ₁`-zeros. -/

private lemma narrow_min_ge695 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : Work.LinnikContract2.IsMin1 χ₁ ρ₁)
    (hnZ : ¬ Work.LinnikContract2.IsZ χ₁ ρ₁)
    (hLam0 : Work.LinnikContract2.Lam0Bound χ₁ ρ₁ ((695:ℝ)/1000))
    (hLam2 : Work.LinnikContract2.Lam2Bound χ₁ ((701:ℝ)/1000))
    {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ} (hminN : Work.LinnikContract2.IsMin1N χ₀ ρ₀) :
    (695:ℝ)/1000 ≤ Work.LinnikContract2.lamOf q ρ₀ := by
  have hZ0 : Work.LinnikContract2.IsZ χ₀ ρ₀ := hminN.1
  by_cases hχ : χ₀ = χ₁
  · -- `χ₀ = χ₁`: `ρ₀` is a working-region zero of `χ₁`, and it is neither `ρ₁` nor `conj ρ₁`
    have hZ0' : Work.LinnikContract2.IsZ χ₁ ρ₀ := hχ ▸ hZ0
    exact hLam0.2 ρ₀ hZ0'
      (fun h => hnZ (h ▸ hZ0'))
      (fun _ hconj =>
        hnZ ⟨hmin.1.1, hmin.1.2.1, by
          have h2 : |ρ₀.im| ≤ 1 := hZ0'.2.2
          rw [hconj] at h2
          rw [Work.A7.abs_im_star ρ₁] at h2
          exact h2⟩)
  · by_cases hχ' : χ₀ = χ₁⁻¹
    · -- `χ₀ = χ₁⁻¹`: conjugate back to a working-region zero of `χ₁`
      have hZinv : Work.LinnikContract2.IsZ χ₁⁻¹ ρ₀ := hχ' ▸ hZ0
      have hZ1 : Work.LinnikContract2.IsZ χ₁ ((starRingEnd ℂ) ρ₀) := Work.A7.isZ_star_inv hZinv
      have h5 : (695:ℝ)/1000 ≤ Work.LinnikContract2.lamOf q ((starRingEnd ℂ) ρ₀) :=
        hLam0.2 ((starRingEnd ℂ) ρ₀) hZ1
          (fun hconj =>
            hnZ ⟨hmin.1.1, hmin.1.2.1, by
              have h2 : |((starRingEnd ℂ) ρ₀).im| ≤ 1 := hZ1.2.2
              rw [hconj] at h2
              exact h2⟩)
          (fun hsq hconj => by
            have hρ : ρ₀ = ρ₁ := by
              have hc := congrArg (starRingEnd ℂ) hconj
              simpa using hc
            have hinv : χ₁⁻¹ = χ₁ :=
              (inv_eq_iff_mul_eq_one).2 (by rw [← pow_two]; exact hsq)
            exact hnZ (hρ ▸ (hinv ▸ hZinv)))
      simpa [Work.LinnikContract2.lamOf] using h5
    · -- `χ₀ ∉ {χ₁, χ₁⁻¹}`: apply `Lam2Bound`
      have h := hLam2 χ₀ ρ₀ hZ0 hχ hχ'
      linarith

/-! ## The assembly -/

theorem area7_window :
    Work.LinnikContract2.ZeroFreeCert → Work.LinnikContract2.DensityCert →
      Work.LinnikContract2.PerCharCert →
      ∀ lamS : ℝ, 0 < lamS → ∃ η : ℝ, 0 < η ∧ ∀ R : ℝ, 0 < R → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        ∀ [NeZero q], ¬ Work.LinnikContract2.SiegelZero q lamS → ∀ a : ℕ, a.Coprime q →
        (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
            ((starRingEnd ℂ) (χ a) * Work.LinnikContract2.boxSum q (11/2) (3/10) R χ).re) <
          (3/10 : ℝ)^2 - η := by
  classical
  intro hZF hDen hPC lamS hlamS
  refine ⟨min (1/5000) (lamS/200), lt_min (by norm_num) (by positivity), ?_⟩
  intro R hR
  set ηf : ℝ := min (1/5000) (lamS/200) with hηfdef
  set η : ℝ := min (1/100000000) (lamS/10) with hηdef
  have hη0 : 0 ≤ η := by rw [hηdef]; exact (lt_min (by norm_num) (by positivity)).le
  have hηpow : 0 < η := by rw [hηdef]; exact lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1/100000000 := by rw [hηdef]; exact min_le_left _ _
  have hη2 : η ≤ lamS/10 := by rw [hηdef]; exact min_le_right _ _
  have hfin1 : ηf ≤ 1/5000 := by rw [hηfdef]; exact min_le_left _ _
  have hfin2 : ηf ≤ lamS/200 := by rw [hηfdef]; exact min_le_right _ _
  obtain ⟨qD1, hD1⟩ := hDen.1 (1/1000) (by norm_num)
  obtain ⟨qD2, hD2⟩ := exists_d2_uniform' hDen.2
  obtain ⟨qPC, hPCq⟩ := hPC (3/10) (by norm_num) (by norm_num) R hR η hηpow
  obtain ⟨qZF, hZFq⟩ := hZF lamS hlamS
  set qTail : ℕ := Nat.ceil (Real.exp (Real.exp (Real.exp (3 * R)))) + 2 with hqTaildef
  refine ⟨max 2 (max qD1 (max qD2 (max qPC (max qZF qTail)))), ?_⟩
  intro q hq _ hnotSiegel a ha
  have hqe2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hA : max qD1 (max qD2 (max qPC (max qZF qTail))) ≤ q := le_trans (le_max_right _ _) hq
  have hB : max qD2 (max qPC (max qZF qTail)) ≤ q := le_trans (le_max_right _ _) hA
  have hC : max qPC (max qZF qTail) ≤ q := le_trans (le_max_right _ _) hB
  have hD : max qZF qTail ≤ q := le_trans (le_max_right _ _) hC
  have hqD1 : qD1 ≤ q := le_trans (le_max_left _ _) hA
  have hqD2 : qD2 ≤ q := le_trans (le_max_left _ _) hB
  have hqPC : qPC ≤ q := le_trans (le_max_left _ _) hC
  have hqZF : qZF ≤ q := le_trans (le_max_left _ _) hD
  have hqTail' : Nat.ceil (Real.exp (Real.exp (Real.exp (3 * R)))) + 2 ≤ q :=
    le_trans (le_max_right _ _) hD
  obtain ⟨hRlog, hRmax⟩ := R_le_log_and_lamMax' hqe2 hR hqTail'
  have hsigned := Work.A7.signed_sum_le_WBox (q := q) (R := R) a
  have hK : ((3:ℝ)/10)^2 = (9:ℝ)/100 := by norm_num
  rw [hK]
  refine lt_of_le_of_lt hsigned ?_
  by_cases hAe : Work.LinnikAreas.A7.Aset q R = ∅
  · have h0 : (0:ℝ) < (9:ℝ)/100 - ηf := by linarith
    simpa [hAe] using h0
  · obtain ⟨χa, hχa⟩ := Finset.nonempty_iff_ne_empty.mpr hAe
    obtain ⟨hχane, ρa, hρabox, hρazm⟩ := Work.LinnikAreas.A7.mem_Aset.mp hχa
    have hZa : IsZ χa ρa := Work.A7.box_api7_p1 hqe2 hRlog hχane hρazm hρabox
    -- the §6 numbering: the wide minimiser exists (`Area0`, proved)
    obtain ⟨χ₁, ρ₁, hmin⟩ := area0 q ⟨χa, ρa, IsZ.toIsZW hZa⟩
    set lam₁ : ℝ := lamOf q ρ₁ with hlam₁def
    have hlam₁ : lamOf q ρ₁ = lam₁ := hlam₁def.symm
    obtain ⟨hZ1, hZ2, hZ3, hZ4, hZ5a, hZ5b⟩ := hZFq q hqZF χ₁ ρ₁ hmin
    have hZ2' : χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 → ((56:ℝ)/100) ≤ lamOf q ρ₁ := by
      intro h1 h2
      have h := hZ2 h1 h2
      have hc : (0.56 : ℝ) = (56:ℝ)/100 := by norm_num
      exact hc ▸ h
    have hZ3' : Lam0Bound χ₁ ρ₁ ((695:ℝ)/1000) ∧ Lam2Bound χ₁ ((701:ℝ)/1000) ∧
        Lam3Bound χ₁ ((856:ℝ)/1000) := by
      unfold Z3 at hZ3
      have hc : (0.695 : ℝ) = (695:ℝ)/1000 := by norm_num
      have hc2 : (0.701 : ℝ) = (701:ℝ)/1000 := by norm_num
      have hc3 : (0.856 : ℝ) = (856:ℝ)/1000 := by norm_num
      rw [hc, hc2, hc3] at hZ3
      exact hZ3
    have hZ5b' : lamS ≤ lamOf q ρ₁ → lamOf q ρ₁ < 2/10 →
        Lam0Bound χ₁ ρ₁ ((99/100) * Real.log (1 / lamOf q ρ₁)) ∧
        Lam2Bound χ₁ ((99/100) * Real.log (1 / lamOf q ρ₁)) := by
      intro h1 h2
      have hc : (0.2 : ℝ) = 2/10 := by norm_num
      rw [← hc] at h2
      exact hZ5b h1 h2
    let hS : Finset (DirichletCharacter ℂ q) :=
      Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q)
    have hSiff : ∀ χ : DirichletCharacter ℂ q, χ ∈ hS ↔ ∃ ρ : ℂ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q := by
      intro χ
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    have hD1' : ∑ χ ∈ hS, wHB (lamChar χ) ≤ (67:ℝ)/6 + 1/1000 := by
      simpa only [hS] using hD1 q hqD1
    have hPC' : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam' : ℝ, 0 ≤ lam' → lam' ≤ R →
        (∀ ρ : ℂ, IsZ χ ρ → lam' ≤ lamOf q ρ) →
        boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam' + η) := by
      intro χ hχ lam' h0 hle hsec
      have h := hPCq q hqPC χ hχ lam' h0 hle hsec
      have hK2 : ((3:ℝ)/10)^2 = (9:ℝ)/100 := by norm_num
      rwa [hK2] at h
    by_cases hIsZ : IsZ χ₁ ρ₁
    · -- ## Case A: the wide minimiser lies in the working region
      have hD2narrow : ∀ e ∈ table13,
          (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
          Ncount q e.1 ≤ e.2.2 :=
        fun e he hn => hD2 e he q hqD2
          (d2_hyp_of_isMin1 hmin (hn χ₁ ρ₁ hIsZ))
      have hminN : Work.LinnikContract.IsMin1 χ₁ ρ₁ := IsMin1.toRound1 hmin hIsZ
      by_cases h348 : ((348:ℝ)/1000) ≤ lam₁
      · -- ### §15
        have h15 := Work.A7.sec15_uniform (q := q) (R := R) (η := η) (εw := 1/1000)
          (lam₁ := lam₁) (χ₁ := χ₁) (ρ₁ := ρ₁)
          hqe2 hR hRlog hRmax hη0 (by norm_num) le_rfl hminN hlam₁ h348 hZ2'
          hZ3' hZ4 hD2narrow hS hSiff hD1' hPC'
        refine lt_of_le_of_lt h15 ?_
        have hb : (9:ℝ)/100*η*1000 ≤ (9:ℝ)/100*(1/100000000)*1000 := by linarith only [hη0, hη1]
        have hc : (9:ℝ)/100*((9968:ℝ)/10000) + (9:ℝ)/100*(1/100000000)*1000
            < (9:ℝ)/100 - 1/5000 := by norm_num
        linarith
      · -- ### §14
        have h348lt : lam₁ < (348:ℝ)/1000 := lt_of_not_ge h348
        have hc348 : (0.348 : ℝ) = (348:ℝ)/1000 := by norm_num
        unfold Z1 at hZ1
        rw [hc348] at hZ1
        have hZ1' : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ zeroMult χ₁ ρ₁ = 1 ∧
            (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) →
              (348:ℝ)/1000 ≤ lamOf q ρ) :=
          hZ1 (by rw [hlam₁]; exact h348lt)
        have hSle : lamS ≤ lam₁ := by
          rw [← hlam₁]
          refine Work.A7.box_api7_p4 hmin.1.1 hZ1'.1 hZ1'.2.1 hZ1'.2.2.1 hnotSiegel hqe2 ?_
          show lamOf q ρ₁ < 1
          rw [hlam₁]; linarith
        have h14 := Work.A7.sec14_uniform (q := q) (R := R) (lamS := lamS) (η := η)
          (εw := 1/1000) (lam₁ := lam₁) (χ₁ := χ₁) (ρ₁ := ρ₁)
          hqe2 hR hRlog hRmax hη0 hη1 hη2 (by norm_num) le_rfl hlamS hnotSiegel
          hminN hlam₁ h348lt hZ1 hZ5a hZ5b' hS hSiff hD1' hPC'
        refine lt_of_le_of_lt h14 ?_
        have hpos : 0 < lam₁ := lt_of_lt_of_le hlamS hSle
        have hlt : ηf < lam₁/100 := by
          have h1 : ηf ≤ lam₁/200 := by linarith
          linarith
        linarith
    · -- ## Case B: `¬ IsZ χ₁ ρ₁` — either `29/50 ≤ λ₁` (two-pivot §15) or the window
      by_cases h29 : (29:ℝ)/50 ≤ lamOf q ρ₁
      · -- ### Case B.1: `29/50 ≤ λ₁`
        have hlarge : (29:ℝ)/50 ≤ lamOf q ρ₁ := h29
        -- the narrow (`IsMin1N`) minimiser exists, and its parameter is `≥ 695/1000`
        obtain ⟨χn, ρn, hminN⟩ :=
          isMin1H_exists (H := 1) ⟨χa, ρa, IsZH_one_iff_IsZ.mpr hZa⟩
        have h695 : (695:ℝ)/1000 ≤ lamOf q ρn :=
          narrow_min_ge695 hmin hIsZ hZ3'.1 hZ3'.2.1 hminN
        -- the two-pivot `§15` argument
        have hD2wide : ∀ e ∈ table13,
            (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → e.2.1 ≤ lamOf q ρ) →
            Ncount q e.1 ≤ e.2.2 :=
          fun e he hw => hD2 e he q hqD2 hw
        have hB := sec15_caseB (q := q) (R := R) (η := η) (εw := 1/1000)
          (χ₁ := χ₁) (ρ₁ := ρ₁) (χ₀ := χn) (ρ₀ := ρn)
          hqe2 hR hRlog hRmax hη0 (by norm_num) le_rfl hmin hZ3 hminN h695 hlarge
          hS hSiff hD1' hPC' hD2wide
        refine lt_of_le_of_lt hB ?_
        have hb : (9:ℝ)/100*η*1000 ≤ (9:ℝ)/100*(1/100000000)*1000 := by linarith only [hη0, hη1]
        have hc : (9:ℝ)/100*((9968:ℝ)/10000) + (9:ℝ)/100*(1/100000000)*1000
            < (9:ℝ)/100 - 1/5000 := by norm_num
        linarith

      · -- ### Case B.2 (the window): `348/1000 ≤ λ₁ < 29/50`
        have h29lt : lam₁ < (29:ℝ)/50 := by
          by_contra hcon
          exact h29 (le_of_not_gt hcon)
        -- `(Z1)` forces `λ₁ ≥ 348/1000`: below that `ρ₁` is real, hence a working-region zero
        have h348le : ((348:ℝ)/1000) ≤ lam₁ := by
          by_contra hcon
          have hlt : lam₁ < (348:ℝ)/1000 := lt_of_not_ge hcon
          have hZ1' : χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ zeroMult χ₁ ρ₁ = 1 ∧
              (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) →
                (348:ℝ)/1000 ≤ lamOf q ρ) := by
            have hc348 : (0.348 : ℝ) = (348:ℝ)/1000 := by norm_num
            unfold Z1 at hZ1
            rw [hc348] at hZ1
            exact hZ1 (by rw [hlam₁]; exact hlt)
          exact hIsZ ⟨hmin.1.1, hmin.1.2.1, by rw [hZ1'.2.1]; norm_num⟩
        -- the narrow (working-region) minimiser, a round-1 minimal pair
        obtain ⟨χ₀, ρ₀, hminN0⟩ := isMin1H_exists (H := 1) ⟨χa, ρa, IsZH_one_iff_IsZ.mpr hZa⟩
        have hnarrow : Work.LinnikContract.IsMin1 χ₀ ρ₀ := hminN0
        have hwideraw : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 →
            Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 50 →
            Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
          fun χ u h1 h2 h3 => hmin.2 χ u ⟨h1, h2, h3⟩
        have hgeA : ∀ χ ∈ Work.LinnikAreas.A7.Aset q R,
            Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamChar χ := by
          intro χ hχ
          obtain ⟨ρ, hZ, -⟩ := Work.A7.exists_isZ_le_R_of_mem_Aset hqe2 hRlog hχ
          exact Work.A7.isMin1_lamOf_le_lamChar hnarrow ⟨ρ, hZ⟩
        have hA_sub_hS : Work.LinnikAreas.A7.Aset q R ⊆ hS := by
          intro χ hχ
          rw [hSiff]
          obtain ⟨ρ, hZ, hle⟩ := Work.A7.exists_isZ_le_R_of_mem_Aset hqe2 hRlog hχ
          exact ⟨ρ, hZ, le_trans hle hRmax⟩
        have hD2win : ∀ e ∈ table13, e.2.1 ≤ lam₁ →
            (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
            Ncount q e.1 ≤ e.2.2 :=
          fun e he hcol _ => hD2 e he q hqD2
            (fun χ ρ hw => le_trans hcol (le_trans (by rw [hlam₁]) (hmin.2 χ ρ hw)))
        have hrow : ∀ (lo hi c0 c2 c3 : ℝ), ((lo, hi, c0, c2, c3) ∈ rows15) →
            lo ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ hi →
            Lam0Bound χ₁ ρ₁ c0 ∧ Lam2Bound χ₁ c2 ∧ Lam3Bound χ₁ c3 :=
          fun lo hi c0 c2 c3 hmem h1 h2 => hZ4 (lo, hi, c0, c2, c3) hmem h1 h2
        have hw0 : ∀ {c c' : ℝ}, c' ≤ c → Lam0Bound χ₁ ρ₁ c → Lam0Bound χ₁ ρ₁ c' := by
          intro c c' hcc h
          exact ⟨fun h2 => le_trans hcc (h.1 h2), fun ρ hZ h1 h2 => le_trans hcc (h.2 ρ hZ h1 h2)⟩
        have hw2 : ∀ {c c' : ℝ}, c' ≤ c → Lam2Bound χ₁ c → Lam2Bound χ₁ c' :=
          fun {c c'} hcc h χ ρ hZ h1 h2 => le_trans hcc (h χ ρ hZ h1 h2)
        have hw3 : ∀ {c c' : ℝ}, c' ≤ c → Lam3Bound χ₁ c → Lam3Bound χ₁ c' := by
          intro c c' hcc h
          obtain ⟨χ₂, hχ₂⟩ := h
          exact ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 => le_trans hcc (hχ₂ χ ρ hZ h1 h2 h3 h4)⟩
        -- the two numeric bounds used when every box character lies above `Λ`
        have hnumF : ∀ Λ' : ℝ, (6:ℝ)/5 ≤ Λ' →
            (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ') * ((67:ℝ)/6 + 1/1000) ≤ (9968:ℝ)/10000 ∧
            (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ') * ((67:ℝ)/6 + 1/1000)
              ≤ 1000 := by
          intro Λ' hΛ'
          have hWnn : (0:ℝ) ≤ (67:ℝ)/6 + 1/1000 := by norm_num
          constructor
          · have h1 : Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                ≤ Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5) :=
              Work.A7.PhiWf_antitone (by norm_num) hΛ'
            have h2 : (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5))
                * ((67:ℝ)/6 + 1/1000) ≤ ((14885014367:ℝ)/24088887000) :=
              Work.A7.tail_le (L := ((6:ℝ)/5)) (εw := 1/1000) (PU := ((444289:ℝ)/100000000))
                (WL := ((8029629:ℝ)/100000000)) (r := ((14885014367:ℝ)/24088887000))
                (by norm_num) (by norm_num) (by norm_num) (Work.LinnikAreas.A7.v_6_5).1 (Work.LinnikAreas.A7.v_6_5).2.2.2.1 (by norm_num) (by norm_num)
            calc (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ') * ((67:ℝ)/6 + 1/1000)
                ≤ (Work.LinnikAreas.A7.Phi ((6:ℝ)/5) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5))
                    * ((67:ℝ)/6 + 1/1000) := mul_le_mul_of_nonneg_right h1 hWnn
              _ ≤ ((14885014367:ℝ)/24088887000) := h2
              _ ≤ (9968:ℝ)/10000 := by norm_num
          · have h1 : Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'
                ≤ Real.exp (-(Work.LinnikAreas.A7.ac * ((6:ℝ)/5))) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5) := by
              simpa only [Work.LinnikAreas.A7.ac] using Work.A7.ExpWf_antitone (by norm_num) hΛ'
            have h2 : (Real.exp (-(Work.LinnikAreas.A7.ac * ((6:ℝ)/5))) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5))
                * ((67:ℝ)/6 + 1/1000) ≤ (1000:ℝ) := by
              have h := Work.A7.etab_le (L := ((6:ℝ)/5)) (εw := 1/1000) (E := ((279479:ℝ)/100000000))
                (WL := ((8029629:ℝ)/100000000)) (N0 := (0:ℝ))
                (by norm_num) (by norm_num) (by norm_num) ?_ (Work.LinnikAreas.A7.v_6_5).2.2.2.1 (by norm_num) (by norm_num)
              · linarith
              · rw [show Work.LinnikAreas.A7.ac = (49:ℝ)/10 from rfl]
                exact Work.LinnikAreas.A7.exF_a_6_5
            calc (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ') * ((67:ℝ)/6 + 1/1000)
                ≤ (Real.exp (-(Work.LinnikAreas.A7.ac * ((6:ℝ)/5))) / Work.LinnikAreas.A7.Wf ((6:ℝ)/5))
                    * ((67:ℝ)/6 + 1/1000) := mul_le_mul_of_nonneg_right h1 hWnn
              _ ≤ 1000 := h2
        have hfincmp : (9:ℝ)/100 * ((9968:ℝ)/10000) + (9:ℝ)/100 * η * 1000 < (9:ℝ)/100 - ηf := by
          have hb : (9:ℝ)/100*η*1000 ≤ (9:ℝ)/100*(1/100000000)*1000 := by linarith only [hη0, hη1]
          have hc : (9:ℝ)/100*((9968:ℝ)/10000) + (9:ℝ)/100*(1/100000000)*1000
              < (9:ℝ)/100 - 1/5000 := by norm_num
          linarith
        -- if every box character lies above `Λ` the plain tail bound suffices
        have hcheap : ∀ Λ' : ℝ, (6:ℝ)/5 ≤ Λ' → Λ' < Work.LinnikContract.lamOf q ρ₀ →
            (∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
              ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by
          intro Λ' hΛ' hlt
          have hΛ'pos : (0:ℝ) < Λ' := by linarith
          obtain ⟨hn1, hn2⟩ := hnumF Λ' hΛ'
          have hpoint : ∀ χ ∈ Work.LinnikAreas.A7.Aset q R,
              Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
                ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by
            intro χ hχ
            have h1 := Work.A7.WBox_le_Phi hqe2 hRlog hPC' hχ
            have hltχ : Λ' < Work.LinnikContract.lamChar χ := lt_of_lt_of_le hlt (hgeA χ hχ)
            have h2 : Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
                + η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))
                ≤ (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) :=
              Work.A7.Phi_exp_le_Wf_hi hΛ'pos hη0 hltχ.le
            calc Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
                ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi (Work.LinnikContract.lamChar χ)
                    + η * Real.exp (-(Work.LinnikAreas.A7.ac * Work.LinnikContract.lamChar χ))) := h1
              _ ≤ ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) :=
                  mul_le_mul_of_nonneg_left h2 (by norm_num)
              _ = ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := by ring
          have hsum1 : (∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
              ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * (∑ χ ∈ Work.LinnikAreas.A7.Aset q R,
                      Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) := by
            calc (∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
                ≤ ∑ χ ∈ Work.LinnikAreas.A7.Aset q R, ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ) := Finset.sum_le_sum hpoint
              _ = ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * (∑ χ ∈ Work.LinnikAreas.A7.Aset q R,
                      Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) := by
                  rw [Finset.mul_sum]
          have hsum2 : (∑ χ ∈ Work.LinnikAreas.A7.Aset q R,
              Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) ≤ (67:ℝ)/6 + 1/1000 :=
            le_trans (Finset.sum_le_sum_of_subset_of_nonneg hA_sub_hS
              (fun χ _ _ => Work.A7.Wf_nonneg_of_nonneg (Work.A7.lamChar_nonneg_of_hq hqe2 χ))) hD1'
          have hCnn : (0:ℝ) ≤ Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ') := by
            have hWf : 0 < Work.LinnikAreas.A7.Wf Λ' := Work.A7.Wf_pos hΛ'pos
            have h1 : 0 ≤ Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ' :=
              div_nonneg (Work.A7.Phi_pos hΛ'pos).le hWf.le
            have h2 : 0 ≤ η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ') :=
              mul_nonneg hη0 (div_nonneg (Real.exp_pos _).le hWf.le)
            linarith
          have hsplit : ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
              * ((67:ℝ)/6 + 1/1000)
              = ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ') * ((67:ℝ)/6 + 1/1000))
                + ((9:ℝ)/100) * η * ((Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ')
                    * ((67:ℝ)/6 + 1/1000)) := by ring
          calc (∑ χ ∈ Work.LinnikAreas.A7.Aset q R, Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ)
              ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * (∑ χ ∈ Work.LinnikAreas.A7.Aset q R,
                      Work.LinnikAreas.A7.Wf (Work.LinnikContract.lamChar χ)) := hsum1
            _ ≤ ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ'
                    + η * (Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ'))
                  * ((67:ℝ)/6 + 1/1000) :=
                mul_le_mul_of_nonneg_left hsum2 (mul_nonneg (by norm_num) hCnn)
            _ = ((9:ℝ)/100) * ((Work.LinnikAreas.A7.Phi Λ' / Work.LinnikAreas.A7.Wf Λ') * ((67:ℝ)/6 + 1/1000))
                + ((9:ℝ)/100) * η * ((Real.exp (-(Work.LinnikAreas.A7.ac * Λ')) / Work.LinnikAreas.A7.Wf Λ')
                    * ((67:ℝ)/6 + 1/1000)) := hsplit
            _ ≤ ((9:ℝ)/100) * ((9968:ℝ)/10000) + ((9:ℝ)/100) * η * 1000 := by linarith only [hn1, mul_le_mul_of_nonneg_left hn2 hη0]
        by_cases hb1 : lam₁ < (2:ℝ)/5
        · -- G1: rows `[0.348,0.40)`, `Λ = 6/5`
          have hG : Lam0Bound χ₁ ρ₁ ((1195:ℝ)/1000) ∧ Lam2Bound χ₁ ((870:ℝ)/1000) ∧
              Lam3Bound χ₁ ((1134:ℝ)/1000) := by
            by_cases hr0 : lam₁ < ((36:ℝ)/100)
            · obtain ⟨hL0, hL2, hL3⟩ := hrow ((348:ℝ)/1000) ((36:ℝ)/100) ((1308:ℝ)/1000) ((902:ℝ)/1000) ((1229:ℝ)/1000)

                (List.getElem_mem (l := rows15) (n := 0) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
              exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
            by_cases hr1 : lam₁ < ((38:ℝ)/100)
            · obtain ⟨hL0, hL2, hL3⟩ := hrow ((36:ℝ)/100) ((38:ℝ)/100) ((1249:ℝ)/1000) ((886:ℝ)/1000) ((1180:ℝ)/1000)

                (List.getElem_mem (l := rows15) (n := 1) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
              exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
            obtain ⟨hL0, hL2, hL3⟩ := hrow ((38:ℝ)/100) ((4:ℝ)/10) ((1195:ℝ)/1000) ((870:ℝ)/1000) ((1134:ℝ)/1000)
              (List.getElem_mem (l := rows15) (n := 2) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
            exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
          obtain ⟨hL0, hL2, hL3⟩ := hG
          by_cases hlamNΛ : Work.LinnikContract.lamOf q ρ₀ ≤ ((6:ℝ)/5)
          · have hcert := win_g1 (q := q) (R := R) (η := η) (εw := 1/1000) (lam₁ := lam₁)
              (lamN := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₁) (ρ₁ := ρ₁) (χ₀ := χ₀) (ρ₀ := ρ₀)
              hqe2 hR hRlog hRmax hη0 (by norm_num) (by norm_num) hwideraw hlam₁ h348le hIsZ
              hL0 hL2 hL3 hnarrow rfl hlamNΛ hS hSiff hD1' hPC' hD2win
            exact lt_of_le_of_lt hcert hfincmp
          · exact lt_of_le_of_lt (hcheap ((6:ℝ)/5) (by norm_num) (lt_of_not_ge hlamNΛ)) hfincmp
        by_cases hb2 : lam₁ < (11:ℝ)/25
        · -- G2: rows `[0.40,0.44)`, `Λ = 6/5`
          have hG : Lam0Bound χ₁ ρ₁ ((1098:ℝ)/1000) ∧ Lam2Bound χ₁ ((841:ℝ)/1000) ∧
              Lam3Bound χ₁ ((1054:ℝ)/1000) := by
            by_cases hr0 : lam₁ < ((42:ℝ)/100)
            · obtain ⟨hL0, hL2, hL3⟩ := hrow ((4:ℝ)/10) ((42:ℝ)/100) ((1144:ℝ)/1000) ((855:ℝ)/1000) ((1093:ℝ)/1000)

                (List.getElem_mem (l := rows15) (n := 3) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
              exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
            obtain ⟨hL0, hL2, hL3⟩ := hrow ((42:ℝ)/100) ((44:ℝ)/100) ((1098:ℝ)/1000) ((841:ℝ)/1000) ((1054:ℝ)/1000)
              (List.getElem_mem (l := rows15) (n := 4) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
            exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
          obtain ⟨hL0, hL2, hL3⟩ := hG
          by_cases hlamNΛ : Work.LinnikContract.lamOf q ρ₀ ≤ ((6:ℝ)/5)
          · have hcert := win_g2 (q := q) (R := R) (η := η) (εw := 1/1000) (lam₁ := lam₁)
              (lamN := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₁) (ρ₁ := ρ₁) (χ₀ := χ₀) (ρ₀ := ρ₀)
              hqe2 hR hRlog hRmax hη0 (by norm_num) (by norm_num) hwideraw hlam₁ (not_lt.mp hb1) hIsZ
              hL0 hL2 hL3 hnarrow rfl hlamNΛ hS hSiff hD1' hPC' hD2win
            exact lt_of_le_of_lt hcert hfincmp
          · exact lt_of_le_of_lt (hcheap ((6:ℝ)/5) (by norm_num) (lt_of_not_ge hlamNΛ)) hfincmp
        by_cases hb3 : lam₁ < (1:ℝ)/2
        · -- G3: rows `[0.44,0.50)`, `Λ = 49/40`
          have hG : Lam0Bound χ₁ ρ₁ ((976:ℝ)/1000) ∧ Lam2Bound χ₁ ((401:ℝ)/500) ∧
              Lam3Bound χ₁ ((951:ℝ)/1000) := by
            by_cases hr0 : lam₁ < ((46:ℝ)/100)
            · obtain ⟨hL0, hL2, hL3⟩ := hrow ((44:ℝ)/100) ((46:ℝ)/100) ((1054:ℝ)/1000) ((828:ℝ)/1000) ((1017:ℝ)/1000)

                (List.getElem_mem (l := rows15) (n := 5) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
              exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
            by_cases hr1 : lam₁ < ((48:ℝ)/100)
            · obtain ⟨hL0, hL2, hL3⟩ := hrow ((46:ℝ)/100) ((48:ℝ)/100) ((1014:ℝ)/1000) ((815:ℝ)/1000) ((983:ℝ)/1000)

                (List.getElem_mem (l := rows15) (n := 6) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
              exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
            obtain ⟨hL0, hL2, hL3⟩ := hrow ((48:ℝ)/100) ((5:ℝ)/10) ((976:ℝ)/1000) ((802:ℝ)/1000) ((951:ℝ)/1000)
              (List.getElem_mem (l := rows15) (n := 7) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
            exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
          obtain ⟨hL0, hL2, hL3⟩ := hG
          by_cases hlamNΛ : Work.LinnikContract.lamOf q ρ₀ ≤ ((49:ℝ)/40)
          · have hcert := win_g3 (q := q) (R := R) (η := η) (εw := 1/1000) (lam₁ := lam₁)
              (lamN := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₁) (ρ₁ := ρ₁) (χ₀ := χ₀) (ρ₀ := ρ₀)
              hqe2 hR hRlog hRmax hη0 (by norm_num) (by norm_num) hwideraw hlam₁ (not_lt.mp hb2) hIsZ
              hL0 hL2 hL3 hnarrow rfl hlamNΛ hS hSiff hD1' hPC' hD2win
            exact lt_of_le_of_lt hcert hfincmp
          · exact lt_of_le_of_lt (hcheap ((49:ℝ)/40) (by norm_num) (lt_of_not_ge hlamNΛ)) hfincmp
        -- G4: rows `[0.50,0.58)`, `Λ = 5/4`
        have hG : Lam0Bound χ₁ ρ₁ ((844:ℝ)/1000) ∧ Lam2Bound χ₁ ((379:ℝ)/500) ∧
            Lam3Bound χ₁ ((856:ℝ)/1000) := by
          by_cases hr0 : lam₁ < ((52:ℝ)/100)
          · obtain ⟨hL0, hL2, hL3⟩ := hrow ((5:ℝ)/10) ((52:ℝ)/100) ((940:ℝ)/1000) ((790:ℝ)/1000) ((921:ℝ)/1000)

              (List.getElem_mem (l := rows15) (n := 8) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
            exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
          by_cases hr1 : lam₁ < ((54:ℝ)/100)
          · obtain ⟨hL0, hL2, hL3⟩ := hrow ((52:ℝ)/100) ((54:ℝ)/100) ((906:ℝ)/1000) ((779:ℝ)/1000) ((892:ℝ)/1000)

              (List.getElem_mem (l := rows15) (n := 9) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
            exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
          by_cases hr2 : lam₁ < ((56:ℝ)/100)
          · obtain ⟨hL0, hL2, hL3⟩ := hrow ((54:ℝ)/100) ((56:ℝ)/100) ((874:ℝ)/1000) ((768:ℝ)/1000) ((865:ℝ)/1000)

              (List.getElem_mem (l := rows15) (n := 10) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
            exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
          obtain ⟨hL0, hL2, hL3⟩ := hrow ((56:ℝ)/100) ((58:ℝ)/100) ((844:ℝ)/1000) ((758:ℝ)/1000) ((856:ℝ)/1000)
            (List.getElem_mem (l := rows15) (n := 11) (by decide)) (by rw [hlam₁]; linarith) (by rw [hlam₁]; linarith)
          exact ⟨hw0 (by norm_num) hL0, hw2 (by norm_num) hL2, hw3 (by norm_num) hL3⟩
        obtain ⟨hL0, hL2, hL3⟩ := hG
        by_cases hlamNΛ : Work.LinnikContract.lamOf q ρ₀ ≤ ((5:ℝ)/4)
        · have hcert := win_g4 (q := q) (R := R) (η := η) (εw := 1/1000) (lam₁ := lam₁)
            (lamN := Work.LinnikContract.lamOf q ρ₀) (χ₁ := χ₁) (ρ₁ := ρ₁) (χ₀ := χ₀) (ρ₀ := ρ₀)
            hqe2 hR hRlog hRmax hη0 (by norm_num) (by norm_num) hwideraw hlam₁ (not_lt.mp hb3) hIsZ
            hL0 hL2 hL3 hnarrow rfl hlamNΛ hS hSiff hD1' hPC' hD2win
          exact lt_of_le_of_lt hcert hfincmp
        · exact lt_of_le_of_lt (hcheap ((5:ℝ)/4) (by norm_num) (lt_of_not_ge hlamNΛ)) hfincmp

  end Work.LinnikContract2.A7
