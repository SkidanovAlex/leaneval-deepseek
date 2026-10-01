/-
# LinnikContract2 — AREA 7 from the disjunctive numbering hypothesis

The hypothesis of this file's theorem is *weaker* than `A7/Area7.lean`'s `area7_of_isZ`:

    hcase : IsMin1 χ₁ ρ₁ → IsZ χ₁ ρ₁ ∨ 43/40 ≤ λ(ρ₁),

i.e. the wide minimiser of HB §6 is either a zero of the working region `|Im| ≤ 1`, or has
`λ₁ ≥ 43/40 = 1.075`.  The two cases are exactly the two regimes in which the §14/§15 numerics
are available in the workspace:

* **Case A (`IsZ χ₁ ρ₁`).**  Then `IsMin1.toRound1` turns the round-2 wide minimiser into a round-1
  narrow minimiser, and round 1's `sec14_uniform` / `sec15_uniform` apply verbatim — this is the
  body of `A7/Area7.lean` (`area7_of_isZ`).
* **Case B (`43/40 ≤ λ₁`).**  The crude global bound `Work.A7.sec15_crude` (round 1's "Region V")
  needs only `λ₁ ≥ 43/40` and `λ₁ ≤ λ_χ` for every `χ ∈ Aset`; the wrapper
  `A7/sec15_caseB_large` packages it, with the *narrow* minimal pair supplied by
  `isMin1H_exists` at height `1` (the branch runs only when `Aset q R ≠ ∅`, and then a
  working-region zero exists, so the narrow minimiser exists).

Both cases end with the same numerical bound
`(9/100)·(9968/10000) + (9/100)·η·1000 < 9/100 − ηf`, so the assembly closes with the same
`linarith` as in `A7/Area7.lean`.
-/
import Mathlib
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Numbering
import Submission.Work.LinnikContract2.Bridge
import Submission.Work.LinnikContract2.A7.Area7
import Submission.Work.LinnikContract2.A7.sec15_caseB_large
import Submission.Work.A7.sec15_uniform
import Submission.Work.A7.sec14_uniform
import Submission.Work.A7.signed_sum_le_WBox
import Submission.Work.A7.box_api7
import Submission.Work.LinnikAreas.A7.Basic7
import Submission.Work.LinnikAreas.A7.WBox

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2.A7

/-! ## Bookkeeping (copies of the private helpers of `A7/Area7.lean`) -/

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

/-! ## The assembly -/

theorem area7_of_isZ_or_large
    (hcase : ∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.LinnikContract2.IsMin1 χ₁ ρ₁ →
        Work.LinnikContract2.IsZ χ₁ ρ₁ ∨ (43:ℝ)/40 ≤ Work.LinnikContract2.lamOf q ρ₁) :
    Work.LinnikContract2.Area7 := by
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
  · obtain ⟨χ₀, hχ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hAe
    obtain ⟨hχ₀ne, ρ₀, hρ₀box, hρ₀zm⟩ := Work.LinnikAreas.A7.mem_Aset.mp hχ₀
    have hZ₀ : IsZ χ₀ ρ₀ := Work.A7.box_api7_p1 hqe2 hRlog hχ₀ne hρ₀zm hρ₀box
    -- the §6 numbering: the wide minimiser exists (`Area0`, proved)
    obtain ⟨χ₁, ρ₁, hmin⟩ := area0 q ⟨χ₀, ρ₀, IsZ.toIsZW hZ₀⟩
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
    rcases hcase q χ₁ ρ₁ hmin with hIsZ | hlarge
    · -- ## Case A: the wide minimiser is a working-region zero
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
        have hb : (9:ℝ)/100*η*1000 ≤ (9:ℝ)/100*(1/100000000)*1000 := by nlinarith [hη0, hη1]
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
    · -- ## Case B: the wide minimiser has `λ₁ ≥ 43/40`
      have hnarrow : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsMin1N χ ρ :=
        isMin1H_exists (H := 1) ⟨χ₀, ρ₀, IsZH_one_iff_IsZ.mpr hZ₀⟩
      have hD2wide : ∀ e ∈ table13,
          (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → e.2.1 ≤ lamOf q ρ) →
          Ncount q e.1 ≤ e.2.2 :=
        fun e he hw => hD2 e he q hqD2 hw
      have hB := sec15_caseB_large (q := q) (R := R) (η := η) (εw := 1/1000)
        (χ₁ := χ₁) (ρ₁ := ρ₁)
        hqe2 hR hRlog hRmax hη0 (by norm_num) (by norm_num)
        hmin hlarge hnarrow hS hSiff hD1' hPC' hD2wide
      refine lt_of_le_of_lt hB ?_
      have hb : (9:ℝ)/100*η*1000 ≤ (9:ℝ)/100*(1/100000000)*1000 := by nlinarith [hη0, hη1]
      have hc : (9:ℝ)/100*((9968:ℝ)/10000) + (9:ℝ)/100*(1/100000000)*1000
          < (9:ℝ)/100 - 1/5000 := by norm_num
      linarith

end Work.LinnikContract2.A7
