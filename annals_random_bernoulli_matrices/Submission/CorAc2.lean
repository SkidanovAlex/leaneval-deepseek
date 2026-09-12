import Mathlib
import Submission.CorAc
import Submission.SlabBridge
import Submission.Sec3Core
open scoped BigOperators
open Submission.IntFun
open Submission.Ell2Update
open Submission.Anticoncent
open Submission.Averaging
open Submission.Sec3Tower
open Submission.ProdCount
open Submission.Admissible
open Submission.PropRefineExport
open Submission.Sec3
open Submission.Threshold
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

namespace Submission.CorAc2

/-- integer-center window weight: total Bernoulli mass of the subsets whose
integer sum is within `A` of `t`. -/
noncomputable def intWeight {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (A : ℝ) (t : ℤ) : ℝ :=
  ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
    (fun B : Finset (Fin n) => (|t + Sec3.subSum x B| : ℝ) ≤ A)), Sec3.wB n p B

/-- the real-center weight supremum is at most the integer-center window-weight
supremum, once `R + 1/2 ≤ A`. -/
lemma weightSup_real_le_intWeight {n : ℕ} (p : unitInterval) (x : Fin n → ℤ)
    {R A : ℝ} (hRA : R + 1 / 2 ≤ A) :
    sSup (Set.range (fun lam : ℝ => SlabBridge.slabWeight p x lam R)) ≤
      sSup (Set.range (fun t : ℤ => intWeight p x A t)) := by
  classical
  have h := Submission.CorAc.weight_sup_real_le_int (p := p) x hRA
  simpa [intWeight, SlabBridge.slabWeight, SlabBridge.goodSubsets] using h

/-- the integer-center window weight function is bounded above by 1. -/
lemma intWeight_bddAbove {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (A : ℝ) :
    BddAbove (Set.range (fun t : ℤ => intWeight p x A t)) := by
  classical
  have h := Submission.CorAc.good_weight_bdd (p := p) (x := x) (A := A)
  simpa [intWeight] using h

/-- lower bound of the `esup` of the kernel level by the integer-center window
weight at radius `√n + 1`. -/
lemma lvl_fk_sup_lower_intWeight {n : ℕ} (hn : 1 ≤ n) (p : unitInterval)
    (x : Fin n → ℤ) :
    ((Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ)) *
        sSup (Set.range (fun t : ℤ =>
          intWeight p x (Real.sqrt (n : ℝ) + 1) t)) ≤
      esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x) := by
  classical
  have h := Submission.CorAc.lvl_fk_sup_lower hn p x
  simpa [intWeight] using h


/-- **concentration ≤ universal-constant × √n × level-supremum**: the full
`cfP`-to-`esup` link of cor: anticoncentration. -/
lemma cfP_le_ofReal_esup {n : ℕ} (hn : 1 ≤ n) (p : unitInterval) (x : Fin n → ℤ) :
    cfP (n := n) p (fun i : Fin n => (x i : ℝ)) (Real.sqrt (n : ℝ)) ≤
      ENNReal.ofReal ((16 / Real.log 2) * Real.sqrt (n : ℝ) *
        esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x)) := by
  classical
  let a : ℝ := (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  let E : ℝ := esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x)
  have hcf1 := SlabBridge.cfP_le_ofReal_weightSup p x (Real.sqrt (n : ℝ))
  have hW : sSup (Set.range (fun lam : ℝ => SlabBridge.slabWeight p x lam (Real.sqrt (n : ℝ)))) ≤
      sSup (Set.range (fun t : ℤ => intWeight p x (Real.sqrt (n : ℝ) + 1) t)) := by
    exact weightSup_real_le_intWeight p x (R := Real.sqrt (n : ℝ))
      (A := Real.sqrt (n : ℝ) + 1) (by linarith)
  have hL := lvl_fk_sup_lower_intWeight hn p x
  have hWsupI_le : sSup (Set.range (fun t : ℤ => intWeight p x (Real.sqrt (n : ℝ) + 1) t)) ≤
      E / a := by
    have h1 : a * sSup (Set.range (fun t : ℤ => intWeight p x (Real.sqrt (n : ℝ) + 1) t)) ≤ E := by
      simpa [a, E] using hL
    have h1' : sSup (Set.range (fun t : ℤ => intWeight p x (Real.sqrt (n : ℝ) + 1) t)) * a ≤ E := by
      simpa [mul_comm] using h1
    exact (le_div_iff₀ ha).mpr h1'
  calc
    cfP (n := n) p (fun i : Fin n => (x i : ℝ)) (Real.sqrt (n : ℝ))
        ≤ ENNReal.ofReal (sSup (Set.range (fun lam : ℝ => SlabBridge.slabWeight p x lam (Real.sqrt (n : ℝ))))) := hcf1
    _ ≤ ENNReal.ofReal (sSup (Set.range (fun t : ℤ => intWeight p x (Real.sqrt (n : ℝ) + 1) t))) :=
          ENNReal.ofReal_le_ofReal hW
    _ ≤ ENNReal.ofReal (E / a) := ENNReal.ofReal_le_ofReal hWsupI_le
    _ = ENNReal.ofReal ((16 / Real.log 2) * Real.sqrt (n : ℝ) * E) := by
          congr 1
          dsimp [E, a]
          field_simp [hsqrtpos.ne', hlog2.ne']


/-- universal constant `16 / log 2` appearing in the `cfP ≤ const·√n·esup`
chain. -/
noncomputable def cAC : ℝ := 16 / Real.log 2

/-- `cAC > 0`. -/
lemma cAC_pos : 0 < cAC := by
  dsimp [cAC]
  positivity

/-- the level-supremum threshold `L/(N·√n)` (matches `averaging`'s filter). -/
noncomputable def lvlThresh (L : ℝ) (N : ℕ) (n : ℕ) : ℝ := L / ((N : ℝ) * Real.sqrt (n : ℝ))

/-- count of lattice points whose (real) concentration at `√n` is at least
`LAC/N`.  (`classical` body: forces the `DecidablePred` instance to
`Classical.propDecidable`, uniform with all proof-context elaborations). -/
noncomputable def cfCount (LAC : ℝ) (N n : ℕ) (p : unitInterval)
    (A : Fin n → Finset ℤ) : ℕ := by
  classical
  exact ((prodFinset n A).filter (fun x : Fin n → ℤ =>
    ENNReal.ofReal (LAC / (N : ℝ)) ≤
      cfP (n := n) p (fun i : Fin n => (x i : ℝ)) (Real.sqrt (n : ℝ)))).card

/-- count of lattice points whose kernel level-supremum exceeds
`L/(N·√n)` (the `th: averaging` event). -/
noncomputable def levelCount (L : ℝ) (N n : ℕ) (p : unitInterval)
    (A : Fin n → Finset ℤ) : ℕ := by
  classical
  exact ((prodFinset n A).filter (fun x : Fin n → ℤ =>
    L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
      esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x))).card

/-- cor: anticoncentration (counting form, law-only, `LAC` independent of
`M`): for `(N,n,δ)`-admissible origin-symmetric integer families `A` with
radius `≤ n·N`, at most `e^{−Mn}·|A|` lattice points have
`cfP(Σ b·x, √n) ≥ LAC/N`. -/
theorem cor_anticoncentration {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁₂ : δ ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) (hεp : ε < (p : ℝ)) :
    ∃ (LAC : ℝ), 0 < LAC ∧
      ∀ (M : ℝ) (hM : 1 ≤ M), ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧ 1 ≤ n₀ ∧
      ∀ (n : ℕ) (hn₀ : n₀ ≤ n), ∀ (N : ℕ) (hN1 : 1 ≤ N),
        (N : ℝ) ≤ (1 / (1 - (p : ℝ) + ε)) ^ n →
        ∀ (A : Fin n → Finset ℤ)
          (hAdm : Admissible N n n δ A)
          (hrad : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
          (hsym : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → -a ∈ A j),
          (cfCount LAC N n p A : ℝ) ≤
            Real.exp (-M * (n : ℝ)) * (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) := by
  classical
  rcases Submission.CorAc.corac_averaged hp₀ hp₁ hδ₀ hδ₁₂ hε₀ hεp with ⟨L, hL, hUnif⟩
  let LAC : ℝ := 2 * cAC * L
  have hLACpos : 0 < LAC := by
    dsimp [LAC]
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) cAC_pos) hL
  refine ⟨LAC, hLACpos, ?_⟩
  · intro M hM
    rcases hUnif M hM with ⟨η, n₀, hη, hn₀1, hBody⟩
    let n₀' : ℕ := max n₀ (Nat.ceil (1 / η ^ 2))
    refine ⟨η, n₀', hη, ?_, ?_⟩
    · dsimp [n₀']
      have h1 : (1 : ℕ) ≤ n₀ := hn₀1
      omega
    · intro n hn₀' N hN1 hNa A hAdm hrad hsym
      have hn₀ : n₀ ≤ n := by
        exact le_trans (le_max_left n₀ (Nat.ceil (1 / η ^ 2))) hn₀'
      have hceil : Nat.ceil (1 / η ^ 2) ≤ n := by
        exact le_trans (le_max_right n₀ (Nat.ceil (1 / η ^ 2))) hn₀'
      have hηR : 1 / η ^ 2 ≤ (n : ℝ) := eta_real_of_ceil hceil
      have hn1 : 1 ≤ n := by
        have h : (1 : ℕ) ≤ n₀ := hn₀1
        omega
      have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
      have hr : 0 < 1 / Real.sqrt (n : ℝ) := by positivity
      have hfpos : ∀ t : ℤ, 0 ≤ fk (1 / Real.sqrt (n : ℝ)) t := fk_nonneg hr
      have hfsum : Summable (fk (1 / Real.sqrt (n : ℝ))) := summable_fk hr
      -- hBody: level-filter card ≤ bound (level = hBody's own filter)
      have hLevBound : (((prodFinset n A).filter (fun x : Fin n → ℤ =>
          L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
            esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x))).card : ℝ) ≤
          Real.exp (-M * (n : ℝ)) * (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) := by
        exact hBody n hn₀ N hN1 hNa A hAdm hrad hsym
      -- 1) cf-large count ≤ level-large count (membership chain)
      have hsubC : cfCount LAC N n p A ≤ levelCount L N n p A := by
        dsimp [cfCount, levelCount]
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        rcases hx with ⟨hxA, hP1⟩
        constructor
        · exact hxA
        · -- cfP ≤ ofReal(cAC·√n·E) ⟹ E > L/(N√n)
          have hcf := cfP_le_ofReal_esup (n := n) hn1 p x
          have hLe : ENNReal.ofReal (LAC / (N : ℝ)) ≤
              ENNReal.ofReal ((16 / Real.log 2) * Real.sqrt (n : ℝ) *
                esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x)) :=
            le_trans hP1 hcf
          have hNpos : (0 : ℝ) < (N : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le (by norm_num) hN1)
          have hx0 : 0 ≤ LAC / (N : ℝ) := by
            have hLAC0 : 0 ≤ LAC := le_of_lt hLACpos
            exact div_nonneg hLAC0 (le_of_lt hNpos)
          have hE0 : 0 ≤ esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x) := by
            exact esup_nonneg (f := lvl (fk (1 / Real.sqrt (n : ℝ))) p n x)
              (by intro t; exact lvl_nonneg n x hfpos t)
              (lvl_summable n x hfsum)
          have hy0 : 0 ≤ (16 / Real.log 2) * Real.sqrt (n : ℝ) *
              esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x) := by
            have hcpos : 0 ≤ (16 / Real.log 2) * Real.sqrt (n : ℝ) := by positivity
            exact mul_nonneg hcpos hE0
          have hTo : (ENNReal.ofReal (LAC / (N : ℝ))).toReal ≤
              (ENNReal.ofReal ((16 / Real.log 2) * Real.sqrt (n : ℝ) *
                esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x))).toReal :=
            (ENNReal.toReal_le_toReal (ENNReal.ofReal_ne_top) (ENNReal.ofReal_ne_top)).mpr hLe
          rw [ENNReal.toReal_ofReal hx0, ENNReal.toReal_ofReal hy0] at hTo
          have hc : 0 < (16 / Real.log 2) * Real.sqrt (n : ℝ) := by positivity
          have hdiv : (LAC / (N : ℝ)) / ((16 / Real.log 2) * Real.sqrt (n : ℝ)) ≤
              esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x) := by
            exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hTo)
          have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hN1))
          have hnum : 2 * lvlThresh L N n =
              (LAC / (N : ℝ)) / ((16 / Real.log 2) * Real.sqrt (n : ℝ)) := by
            dsimp [lvlThresh, LAC, cAC]
            field_simp [hN0, hsqrtpos.ne', (show (Real.log 2 : ℝ) ≠ 0 by positivity)]
          have hE2 : 2 * lvlThresh L N n ≤
              esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x) := by
            rw [hnum]
            exact hdiv
          have hLpos : 0 < lvlThresh L N n := by
            dsimp [lvlThresh]
            have hNn : (0 : ℝ) < (N : ℝ) * Real.sqrt (n : ℝ) := by positivity
            positivity
          exact lt_of_lt_of_le (lt_two_mul_self hLpos) hE2
      -- 2) level-large count ≤ hBody's filter card (def-vs-inline bridge)
      have hLevEq : levelCount L N n p A ≤
          ((prodFinset n A).filter (fun x : Fin n → ℤ =>
            L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
              esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x))).card := by
        dsimp [levelCount]
        rfl
      -- 3) assemble
      have hfin : (cfCount LAC N n p A : ℝ) ≤
          Real.exp (-M * (n : ℝ)) * (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) := by
        calc
          (cfCount LAC N n p A : ℝ) ≤ (levelCount L N n p A : ℝ) := by exact_mod_cast hsubC
          _ ≤ ((((prodFinset n A).filter (fun x : Fin n → ℤ =>
                L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
                  esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x))).card : ℕ) : ℝ) := by
                exact_mod_cast hLevEq
          _ ≤ Real.exp (-M * (n : ℝ)) * (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) := hLevBound
      exact hfin

