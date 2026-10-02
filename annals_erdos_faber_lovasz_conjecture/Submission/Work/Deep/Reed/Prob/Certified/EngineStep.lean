import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.Certified.Defs
import Submission.Work.Deep.Reed.Prob.Certified.Slice
import Submission.Work.Deep.Reed.Prob.Certified.js_lambda
import Submission.Work.Deep.Reed.Prob.Certified.exp_rpow_mul_le
import Submission.Work.Deep.Reed.Prob.Certified.assembly_sum
import Submission.Work.Deep.Reed.Prob.Certified.engine_equiv
import Submission.Work.Deep.Reed.Prob.Certified.pi_prob_option
import Submission.Work.Deep.Reed.Prob.Certified.pi_exp_option

/-!
# The induction step of Talagrand's convex distance inequality

This file proves Talagrand's convex distance inequality `Engine` by induction on
the number of coordinates, in the `Option`-splitting formulation: the induction
step is `engine_option` and the reindexing step is `engine_equiv` (proved
separately).  The main ingredients are

* the slicing estimate `cdsq_option_le` / `cdsq_option_le_succ`;
* the Johnson–Schechtman optimisation `js_lambda`;
* Hölder's inequality `exp_rpow_mul_le`;
* the Fubini identities `pi_prob_option` / `pi_exp_option`;
* the arithmetic assembly `assembly_sum`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

section Helpers

variable {ι : Type*}

lemma fullSupport_pi {Ω : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Ω i)]
    {μ : ∀ i, FinProb (Ω i)} (h : ∀ i x, 0 < (μ i).wt x) (f : ∀ i, Ω i) :
    0 < (FinProb.pi μ).wt f := by
  rw [FinProb.pi_wt]
  exact Finset.prod_pos fun i _ => h i (f i)

lemma prob_pos_of_fullSupport {Ω : Type*} [Fintype Ω] (ν : FinProb Ω)
    (h : ∀ x, 0 < ν.wt x) {A : Set Ω} (hA : A.Nonempty) : 0 < ν.prob A := by
  classical
  obtain ⟨x, hx⟩ := hA
  have hle : ν.wt x ≤ ν.prob A := by
    rw [FinProb.prob]
    have := Finset.single_le_sum (f := fun y => if y ∈ A then ν.wt y else 0)
      (fun y _ => by by_cases hy : y ∈ A <;> simp [hy, le_of_lt (h y)]) (Finset.mem_univ x)
    simpa [hx] using this
  linarith [h x]

lemma exp_quarter_lt_two : Real.exp (1/4 : ℝ) < 2 := by
  have h2 : Real.exp (1/4 : ℝ) ^ 2 = Real.exp (1/2 : ℝ) := by
    rw [pow_two, ← Real.exp_add]; norm_num
  have h3 : Real.exp (1/2 : ℝ) < (2:ℝ) ^ 2 := by
    have hlt : Real.exp (1/2 : ℝ) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith [Real.exp_one_lt_three]
  nlinarith [Real.exp_pos (1/4 : ℝ), h2, h3]

end Helpers

section Base

/-- The base case of the induction: a product over an empty index type. -/
theorem engine_pempty : Engine PEmpty := by
  intro Ω _ μ hpos A
  classical
  have hcd : ∀ f : ∀ i : PEmpty, Ω i, cdsq A f = 0 := by
    intro f
    have hsub : sqnorm '' Vset A f ⊆ {0} := by
      rintro q ⟨p, hp, rfl⟩
      simp [sqnorm]
    refine le_antisymm ?_ cdsq_nonneg
    by_cases h : (sqnorm '' Vset A f).Nonempty
    · obtain ⟨q, hq⟩ := h
      have hq0 : q = 0 := by simpa using hsub hq
      calc cdsq A f ≤ q := csInf_le (bddBelow_sqnorm_Vset A f) hq
        _ = 0 := hq0
    · have hge : sqnorm '' Vset A f = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [cdsq, hge, Real.sInf_empty]
  have hexp : (FinProb.pi μ).exp (fun f => Real.exp (cdsq A f / 4)) = 1 := by
    rw [FinProb.exp]
    simp [hcd, FinProb.wt_sum]
  rw [hexp, mul_one]
  exact FinProb.prob_le_one _ _

end Base

section Combine

/-- Alternating combination of real powers. -/
lemma rpow_combine {b c ju iv lam : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hju : 0 ≤ ju) (hiv : 0 ≤ iv) :
    (c * ju) ^ lam * ((b * iv) ^ (1 - lam)) * ((b / c) ^ lam)
      = b * (ju ^ lam * iv ^ (1 - lam)) := by
  rw [Real.mul_rpow (le_of_lt hc) hju, Real.mul_rpow (le_of_lt hb) hiv,
      Real.div_rpow (le_of_lt hb) (le_of_lt hc)]
  have h1 : (b : ℝ) ^ (1 - lam) * b ^ lam = b := by
    rw [← Real.rpow_add hb]
    ring_nf
    rw [Real.rpow_one]
  have h2 : c ^ lam / c ^ lam = 1 := by
    rw [div_self (ne_of_gt (Real.rpow_pos_of_pos hc lam))]
  have expand : c ^ lam * ju ^ lam * (b ^ (1 - lam) * iv ^ (1 - lam)) * (b ^ lam / c ^ lam)
      = (ju ^ lam * iv ^ (1 - lam)) * (b ^ (1 - lam) * b ^ lam) * (c ^ lam / c ^ lam) := by
    ring
  rw [expand, h2, h1, mul_one]
  ring

end Combine

universe u v

section Step

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma glue_self {Ω : Option α → Type*} [∀ o, Fintype (Ω o)] (y : ∀ o, Ω o) :
    glue (y none) (fun a => y (some a)) = y := by
  funext o; cases o <;> rfl

theorem engine_option {α : Type u} [Fintype α] [DecidableEq α]
    (hα : Engine.{u, v} α) : Engine.{u, v} (Option α) := by
  intro Ω _ μ hpos A
  classical
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · rw [hA, FinProb.prob_empty]
    simp
  · set K : Ω none → Set (∀ a : α, Ω (some a)) := fun ω => {x | glue ω x ∈ A} with hK
    set B : Set (∀ a : α, Ω (some a)) := {x | ∃ ω : Ω none, glue ω x ∈ A} with hB
    set P' : FinProb (∀ a : α, Ω (some a)) := FinProb.pi (fun a => μ (some a)) with hP'
    have hP'full : ∀ x, 0 < P'.wt x := by
      intro x
      rw [hP', FinProb.pi_wt]
      exact Finset.prod_pos fun a _ => hpos (some a) (x a)
    have hBne : B.Nonempty := by
      obtain ⟨y, hy⟩ := hA
      refine ⟨fun a => y (some a), ?_⟩
      rw [hB]
      exact ⟨y none, by rw [glue_self]; exact hy⟩
    have hBpos : 0 < P'.prob B := prob_pos_of_fullSupport P' hP'full hBne
    have hα' := hα (fun a : α => Ω (some a)) (fun a => μ (some a))
      (fun a x => hpos (some a) x)
    have hprobA : (FinProb.pi μ).prob A = ∑ ω : Ω none, (μ none).wt ω * P'.prob (K ω) := by
      rw [Work.Deep.Reed.Prob.Certified.pi_prob_option (Ω := Ω) μ A, ← hP']
      refine Finset.sum_congr rfl fun ω _ => ?_
      congr 1
    have hexpA : (FinProb.pi μ).exp (fun f => Real.exp (cdsq A f / 4))
        = ∑ ω : Ω none, (μ none).wt ω *
            P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4)) := by
      have h := Work.Deep.Reed.Prob.Certified.pi_exp_option (Ω := Ω) μ
        (fun f => Real.exp (cdsq A f / 4))
      rw [h, ← hP']
      refine Finset.sum_congr rfl fun ω _ => ?_
      congr 1
    have hper : ∀ ω : Ω none, P'.prob B * P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
        ≤ 2 - P'.prob (K ω) / P'.prob B := by
      intro ω
      by_cases hKne : (K ω).Nonempty
      · have hKpos : 0 < P'.prob (K ω) := prob_pos_of_fullSupport P' hP'full hKne
        have hsub : K ω ⊆ B := by
          intro x hx
          rw [hK] at hx
          rw [hB]
          exact ⟨ω, hx⟩
        have hle1 : P'.prob (K ω) / P'.prob B ≤ 1 := by
          rw [div_le_one hBpos]
          exact FinProb.prob_mono P' hsub
        have hratpos : 0 < P'.prob (K ω) / P'.prob B := div_pos hKpos hBpos
        obtain ⟨lam, hlam0, hlam1, hjs⟩ :=
          Work.Deep.Reed.Prob.Certified.js_lambda (r := P'.prob (K ω) / P'.prob B) hratpos hle1
        have hslice : ∀ x : ∀ a, Ω (some a),
            cdsq A (glue ω x) ≤ lam * cdsq (K ω) x + (1 - lam) * cdsq B x + (1 - lam) ^ 2 := by
          intro x
          refine cdsq_option_le (A := A) (ω := ω) (x := x) ?_ hlam0 hlam1
          rw [hK] at hKne
          exact Uset_nonempty hKne
        have hpoint : ∀ x : ∀ a, Ω (some a),
            Real.exp (cdsq A (glue ω x) / 4)
              ≤ Real.exp ((1 - lam) ^ 2 / 4) * (Real.exp (cdsq (K ω) x / 4)) ^ lam
                  * (Real.exp (cdsq B x / 4)) ^ (1 - lam) := by
          intro x
          have h1 : Real.exp (cdsq A (glue ω x) / 4)
              ≤ Real.exp ((lam * cdsq (K ω) x + (1 - lam) * cdsq B x + (1 - lam) ^ 2) / 4) := by
            apply Real.exp_le_exp.mpr
            linarith [hslice x]
          have h2 : Real.exp ((lam * cdsq (K ω) x + (1 - lam) * cdsq B x + (1 - lam) ^ 2) / 4)
              = Real.exp ((1 - lam) ^ 2 / 4) * (Real.exp (cdsq (K ω) x / 4)) ^ lam
                  * (Real.exp (cdsq B x / 4)) ^ (1 - lam) := by
            rw [show (lam * cdsq (K ω) x + (1 - lam) * cdsq B x + (1 - lam) ^ 2) / 4
                = (1 - lam) ^ 2 / 4 + (cdsq (K ω) x / 4) * lam
                    + (cdsq B x / 4) * (1 - lam) from by ring]
            rw [Real.exp_add, Real.exp_add, Real.exp_mul, Real.exp_mul]
          exact h1.trans (le_of_eq h2)
        have hIle : P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
            ≤ Real.exp ((1 - lam) ^ 2 / 4) *
              P'.exp (fun x => (Real.exp (cdsq (K ω) x / 4)) ^ lam
                * (Real.exp (cdsq B x / 4)) ^ (1 - lam)) := by
          rw [FinProb.exp, FinProb.exp, Finset.mul_sum]
          refine Finset.sum_le_sum fun x _ => ?_
          calc P'.wt x * Real.exp (cdsq A (glue ω x) / 4)
              ≤ P'.wt x * (Real.exp ((1 - lam) ^ 2 / 4) * (Real.exp (cdsq (K ω) x / 4)) ^ lam
                  * (Real.exp (cdsq B x / 4)) ^ (1 - lam)) :=
                mul_le_mul_of_nonneg_left (hpoint x) (le_of_lt (hP'full x))
            _ = Real.exp ((1 - lam) ^ 2 / 4) * (P'.wt x * ((Real.exp (cdsq (K ω) x / 4)) ^ lam
                  * (Real.exp (cdsq B x / 4)) ^ (1 - lam))) := by ring
        have hholder := Work.Deep.Reed.Prob.Certified.exp_rpow_mul_le P'
          (u := fun x : ∀ a, Ω (some a) => Real.exp (cdsq (K ω) x / 4))
          (v := fun x : ∀ a, Ω (some a) => Real.exp (cdsq B x / 4))
          (fun x => le_of_lt (Real.exp_pos _)) (fun x => le_of_lt (Real.exp_pos _)) hlam0 hlam1
        have hIle2 : P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
            ≤ Real.exp ((1 - lam) ^ 2 / 4)
              * (P'.exp (fun x => Real.exp (cdsq (K ω) x / 4))) ^ lam
              * (P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam) := by
          refine hIle.trans ?_
          calc Real.exp ((1 - lam) ^ 2 / 4) *
                P'.exp (fun x => (Real.exp (cdsq (K ω) x / 4)) ^ lam
                  * (Real.exp (cdsq B x / 4)) ^ (1 - lam))
              ≤ Real.exp ((1 - lam) ^ 2 / 4) *
                ((P'.exp (fun x => Real.exp (cdsq (K ω) x / 4))) ^ lam
                  * (P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam)) :=
                mul_le_mul_of_nonneg_left hholder (le_of_lt (Real.exp_pos _))
            _ = _ := by ring
        have hIH1 : P'.prob (K ω) * P'.exp (fun x => Real.exp (cdsq (K ω) x / 4)) ≤ 1 := by
          simpa [hP'] using hα' (K ω)
        have hIH2 : P'.prob B * P'.exp (fun x => Real.exp (cdsq B x / 4)) ≤ 1 := by
          simpa [hP'] using hα' B
        have hJu : 0 ≤ P'.exp (fun x => Real.exp (cdsq (K ω) x / 4)) :=
          FinProb.exp_nonneg P' (fun x => le_of_lt (Real.exp_pos _))
        have hIv : 0 ≤ P'.exp (fun x => Real.exp (cdsq B x / 4)) :=
          FinProb.exp_nonneg P' (fun x => le_of_lt (Real.exp_pos _))
        have hcombine : P'.prob B * P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
            ≤ Real.exp ((1 - lam) ^ 2 / 4) * (P'.prob B / P'.prob (K ω)) ^ lam := by
          calc P'.prob B * P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
              ≤ P'.prob B * (Real.exp ((1 - lam) ^ 2 / 4)
                  * (P'.exp (fun x => Real.exp (cdsq (K ω) x / 4))) ^ lam
                  * (P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam)) :=
                mul_le_mul_of_nonneg_left hIle2 (le_of_lt hBpos)
            _ = Real.exp ((1 - lam) ^ 2 / 4) * (P'.prob B
                  * (P'.exp (fun x => Real.exp (cdsq (K ω) x / 4))) ^ lam
                  * (P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam)) := by ring
            _ = Real.exp ((1 - lam) ^ 2 / 4) *
                ((P'.prob (K ω) * P'.exp (fun x => Real.exp (cdsq (K ω) x / 4))) ^ lam
                  * (P'.prob B * P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam)
                  * (P'.prob B / P'.prob (K ω)) ^ lam) := by
                rw [rpow_combine hBpos hKpos hJu hIv]
                ring
            _ ≤ Real.exp ((1 - lam) ^ 2 / 4)
                  * (1 ^ lam * 1 ^ (1 - lam) * (P'.prob B / P'.prob (K ω)) ^ lam) := by
                refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
                have h1 : (P'.prob (K ω) * P'.exp (fun x => Real.exp (cdsq (K ω) x / 4))) ^ lam ≤ 1 :=
                  Real.rpow_le_one (mul_nonneg (le_of_lt hKpos) hJu) hIH1 hlam0
                have h2 : (P'.prob B * P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam) ≤ 1 :=
                  Real.rpow_le_one (mul_nonneg (le_of_lt hBpos) hIv) hIH2 (by linarith)
                have hB' : (0:ℝ) ≤ (P'.prob B * P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam) :=
                  Real.rpow_nonneg (mul_nonneg (le_of_lt hBpos) hIv) (1 - lam)
                have h3 : (0:ℝ) ≤ (P'.prob B / P'.prob (K ω)) ^ lam :=
                  Real.rpow_nonneg (by positivity) lam
                calc (P'.prob (K ω) * P'.exp (fun x => Real.exp (cdsq (K ω) x / 4))) ^ lam
                      * (P'.prob B * P'.exp (fun x => Real.exp (cdsq B x / 4))) ^ (1 - lam)
                      * (P'.prob B / P'.prob (K ω)) ^ lam
                    ≤ (1 * 1) * (P'.prob B / P'.prob (K ω)) ^ lam :=
                      mul_le_mul (mul_le_mul h1 h2 hB' (by norm_num)) le_rfl h3 (by norm_num)
                    _ = 1 ^ lam * 1 ^ (1 - lam) * (P'.prob B / P'.prob (K ω)) ^ lam := by
                      rw [Real.one_rpow, Real.one_rpow]
            _ = Real.exp ((1 - lam) ^ 2 / 4) * (P'.prob B / P'.prob (K ω)) ^ lam := by
                rw [Real.one_rpow, Real.one_rpow, one_mul, one_mul]
        have hrpow : (P'.prob B / P'.prob (K ω)) ^ lam
            = (P'.prob (K ω) / P'.prob B) ^ (-lam) := by
          rw [Real.div_rpow (le_of_lt hBpos) (le_of_lt hKpos),
            Real.div_rpow (le_of_lt hKpos) (le_of_lt hBpos),
            Real.rpow_neg (le_of_lt hKpos) lam, Real.rpow_neg (le_of_lt hBpos) lam]
          field_simp
        calc P'.prob B * P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
            ≤ Real.exp ((1 - lam) ^ 2 / 4) * (P'.prob B / P'.prob (K ω)) ^ lam := hcombine
          _ = Real.exp ((1 - lam) ^ 2 / 4) * (P'.prob (K ω) / P'.prob B) ^ (-lam) := by rw [hrpow]
          _ ≤ 2 - P'.prob (K ω) / P'.prob B := hjs
      · have hKempty : K ω = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
        have hπ0 : P'.prob (K ω) = 0 := by rw [hKempty, FinProb.prob_empty]
        have hIle : P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
            ≤ Real.exp (1/4) * P'.exp (fun x => Real.exp (cdsq B x / 4)) := by
          rw [FinProb.exp, FinProb.exp, Finset.mul_sum]
          refine Finset.sum_le_sum fun x _ => ?_
          have hs := cdsq_option_le_succ (A := A) (ω := ω) (x := x)
            (by rw [← hB]; exact Uset_nonempty hBne)
          have hpt : Real.exp (cdsq A (glue ω x) / 4) ≤ Real.exp (1/4) * Real.exp (cdsq B x / 4) := by
            have h1 : Real.exp (cdsq A (glue ω x) / 4) ≤ Real.exp ((cdsq B x + 1) / 4) := by
              apply Real.exp_le_exp.mpr
              linarith [hs]
            refine h1.trans (le_of_eq ?_)
            rw [show (cdsq B x + 1) / 4 = 1/4 + cdsq B x / 4 from by ring, Real.exp_add]
          calc P'.wt x * Real.exp (cdsq A (glue ω x) / 4)
              ≤ P'.wt x * (Real.exp (1/4) * Real.exp (cdsq B x / 4)) :=
                mul_le_mul_of_nonneg_left hpt (le_of_lt (hP'full x))
            _ = Real.exp (1/4) * (P'.wt x * Real.exp (cdsq B x / 4)) := by ring
        have hIH2 : P'.prob B * P'.exp (fun x => Real.exp (cdsq B x / 4)) ≤ 1 := by
          simpa [hP'] using hα' B
        calc P'.prob B * P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4))
            ≤ P'.prob B * (Real.exp (1/4) * P'.exp (fun x => Real.exp (cdsq B x / 4))) :=
              mul_le_mul_of_nonneg_left hIle (le_of_lt hBpos)
          _ = Real.exp (1/4) * (P'.prob B * P'.exp (fun x => Real.exp (cdsq B x / 4))) := by ring
          _ ≤ Real.exp (1/4) * 1 := mul_le_mul_of_nonneg_left hIH2 (le_of_lt (Real.exp_pos _))
          _ ≤ 2 - P'.prob (K ω) / P'.prob B := by
              rw [mul_one, hπ0, zero_div, sub_zero]
              linarith [exp_quarter_lt_two]
    rw [hexpA]
    refine Work.Deep.Reed.Prob.Certified.assembly_sum (fun ω : Ω none => (μ none).wt ω)
      (fun ω => P'.prob (K ω))
      (fun ω => P'.exp (fun x => Real.exp (cdsq A (glue ω x) / 4)))
      (P'.prob B) ((FinProb.pi μ).prob A)
      (fun ω => (μ none).wt_nonneg ω) (μ none).wt_sum hBpos
      (FinProb.prob_nonneg _ _) (le_of_eq hprobA) hper

end Step

section All

theorem engine_all_aux : ∀ n : ℕ, ∀ (α : Type u) [Fintype α] [DecidableEq α],
    Fintype.card α = n → Engine.{u, v} α := by
  intro n
  induction n with
  | zero =>
      intro α _ _ hcard
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hcard
      exact Work.Deep.Reed.Prob.Certified.engine_equiv (Equiv.equivPEmpty α).symm engine_pempty.{u, v}
  | succ n ih =>
      intro α _ _ hcard
      have hpos : 0 < Fintype.card α := by rw [hcard]; exact Nat.succ_pos n
      obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
      have hcard' : Fintype.card {y : α // y ≠ x} = n := by
        have h1 : Fintype.card (Option {y : α // y ≠ x}) = n + 1 := by
          rw [Fintype.card_congr (Equiv.optionSubtypeNe x), hcard]
        rw [Fintype.card_option] at h1
        omega
      have hα' : Engine.{u, v} {y : α // y ≠ x} := ih _ hcard'
      have hopt : Engine.{u, v} (Option {y : α // y ≠ x}) := engine_option hα'
      exact Work.Deep.Reed.Prob.Certified.engine_equiv (Equiv.optionSubtypeNe x) hopt

/-- **Talagrand's convex distance inequality** (for full-support product measures). -/
theorem engine_all (ι : Type u) [Fintype ι] [DecidableEq ι] : Engine.{u, v} ι :=
  engine_all_aux (Fintype.card ι) ι rfl

end All

end Work.Deep.Reed.Prob
