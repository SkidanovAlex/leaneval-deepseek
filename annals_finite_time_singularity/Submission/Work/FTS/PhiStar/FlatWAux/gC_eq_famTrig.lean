import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Computability.Reduce
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.LinvFlatAux.linv_abs_le_four
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongPersist.Star6
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Trig =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

open Set Filter MeasureTheory

/-! ## Elementary calculus helpers -/

lemma abs_cos_le_one' (x : ℝ) : |Real.cos x| ≤ 1 := by
  have h := Real.abs_sin_le_one (x + Real.pi / 2)
  rwa [Real.sin_add_pi_div_two] at h

lemma hasDerivAt_cos_affine (a c θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (a * θ' + c)) (-(Real.sin (a * θ + c)) * a) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => a * θ' + c) a θ := by
    have h0 : HasDerivAt (fun θ' : ℝ => a * θ') (a * 1) θ :=
      (hasDerivAt_id θ).const_mul a
    simpa using h0.add_const c
  have h2 := (Real.hasDerivAt_cos (a * θ + c)).comp θ h1
  simpa only [Function.comp_def] using h2

lemma differentiableAt_cos_affine (a c θ : ℝ) :
    DifferentiableAt ℝ (fun θ' : ℝ => Real.cos (a * θ' + c)) θ :=
  (hasDerivAt_cos_affine a c θ).differentiableAt

lemma deriv_const_add' (c : ℝ) (g : ℝ → ℝ) (θ : ℝ) (hg : DifferentiableAt ℝ g θ) :
    deriv (fun θ' : ℝ => c + g θ') θ = deriv g θ := by
  have h : deriv ((fun _ : ℝ => c) + g) θ = deriv (fun _ : ℝ => c) θ + deriv g θ :=
    deriv_add (differentiableAt_const c) hg
  rw [show ((fun _ : ℝ => c) + g) = fun θ' : ℝ => c + g θ' from rfl, deriv_const] at h
  linarith [h]

lemma deriv_two_mul' (g : ℝ → ℝ) (θ : ℝ) (hg : DifferentiableAt ℝ g θ) :
    deriv (fun θ' : ℝ => 2 * g θ') θ = 2 * deriv g θ :=
  deriv_const_mul 2 hg

lemma differentiableAt_sum_of (g : ℕ → ℝ → ℝ) :
    ∀ (s : Finset ℕ) (θ : ℝ), (∀ i ∈ s, DifferentiableAt ℝ (g i) θ) →
      DifferentiableAt ℝ (fun θ' : ℝ => ∑ i ∈ s, g i θ') θ := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro θ _
      simpa using differentiableAt_const (0 : ℝ)
  | insert a s ha ih =>
      intro θ hg
      have hstep : (fun θ' : ℝ => ∑ i ∈ insert a s, g i θ')
          = fun θ' : ℝ => g a θ' + ∑ i ∈ s, g i θ' := by
        funext θ'
        rw [Finset.sum_insert ha]
      rw [hstep]
      exact (hg a (Finset.mem_insert_self a s)).add
        (ih θ (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

lemma deriv_sum_of (g : ℕ → ℝ → ℝ) (g' : ℕ → ℝ) :
    ∀ (s : Finset ℕ) (θ : ℝ), (∀ i ∈ s, HasDerivAt (g i) (g' i) θ) →
      deriv (fun θ' : ℝ => ∑ i ∈ s, g i θ') θ = ∑ i ∈ s, g' i := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro θ _
      simp
  | insert a s ha ih =>
      intro θ hg
      have hstep : (fun θ' : ℝ => ∑ i ∈ insert a s, g i θ')
          = g a + fun θ' : ℝ => ∑ i ∈ s, g i θ' := by
        funext θ'
        rw [Finset.sum_insert ha]
        rfl
      rw [hstep]
      have hd : DifferentiableAt ℝ (fun θ' : ℝ => ∑ i ∈ s, g i θ') θ :=
        differentiableAt_sum_of g s θ
          (fun i hi => (hg i (Finset.mem_insert_of_mem hi)).differentiableAt)
      rw [deriv_add (hg a (Finset.mem_insert_self a s)).differentiableAt hd,
        (hg a (Finset.mem_insert_self a s)).deriv,
        ih θ (fun i hi => hg i (Finset.mem_insert_of_mem hi)),
        Finset.sum_insert ha]

/-! ## The Dirichlet-type kernel and its iterated derivatives -/

/-- `Kern t θ = 1 + 2 Σ_{i<t} cos (2(i+1)θ)`. -/
def Kern (t : ℕ) (θ : ℝ) : ℝ :=
  1 + 2 * ∑ i ∈ Finset.range t, Real.cos (2 * ((i : ℝ) + 1) * θ)

lemma iteratedDeriv_cos_affine (a c : ℝ) (l : ℕ) :
    iteratedDeriv l (fun θ : ℝ => Real.cos (a * θ + c))
      = fun θ : ℝ => a ^ l * Real.cos (a * θ + c + (l : ℝ) * (Real.pi / 2)) := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [iteratedDeriv_succ, ih]
      funext θ
      have hd : DifferentiableAt ℝ
          (fun θ' : ℝ => Real.cos (a * θ' + (c + (l : ℝ) * (Real.pi / 2)))) θ :=
        differentiableAt_cos_affine a (c + (l : ℝ) * (Real.pi / 2)) θ
      rw [show (fun θ : ℝ => a ^ l * Real.cos (a * θ + c + (l : ℝ) * (Real.pi / 2)))
            = fun θ : ℝ => a ^ l * Real.cos (a * θ + (c + (l : ℝ) * (Real.pi / 2))) from by
        funext θ; ring_nf]
      rw [deriv_const_mul _ hd,
        (hasDerivAt_cos_affine a (c + (l : ℝ) * (Real.pi / 2)) θ).deriv]
      have hcos : Real.cos (a * θ + c + (((l + 1 : ℕ)) : ℝ) * (Real.pi / 2))
          = -Real.sin (a * θ + (c + (l : ℝ) * (Real.pi / 2))) := by
        rw [show a * θ + c + (((l + 1 : ℕ)) : ℝ) * (Real.pi / 2)
              = (a * θ + (c + (l : ℝ) * (Real.pi / 2))) + Real.pi / 2 from by
          push_cast
          ring,
          Real.cos_add_pi_div_two]
      rw [hcos]
      ring

lemma iteratedDeriv_Kern (l t : ℕ) :
    iteratedDeriv l (Kern t)
      = fun θ : ℝ => (if l = 0 then (1 : ℝ) else 0) + 2 * ∑ i ∈ Finset.range t,
          (2 * ((i : ℝ) + 1)) ^ l
            * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2)) := by
  induction l with
  | zero =>
      funext θ
      rw [iteratedDeriv_zero]
      simp [Kern]
  | succ l ih =>
      rw [iteratedDeriv_succ, ih]
      funext θ
      have hg : DifferentiableAt ℝ (fun θ' : ℝ => 2 * ∑ i ∈ Finset.range t,
          (2 * ((i : ℝ) + 1)) ^ l
            * Real.cos (2 * ((i : ℝ) + 1) * θ' + (l : ℝ) * (Real.pi / 2))) θ :=
        (differentiableAt_sum_of _ _ θ (fun i _ =>
          (differentiableAt_cos_affine _ _ _).const_mul _)).const_mul 2
      rw [deriv_const_add' _ _ _ hg]
      rw [deriv_two_mul' _ _ (differentiableAt_sum_of _ _ θ (fun i _ =>
        (differentiableAt_cos_affine _ _ _).const_mul _))]
      rw [deriv_sum_of (fun i θ' => (2 * ((i : ℝ) + 1)) ^ l
          * Real.cos (2 * ((i : ℝ) + 1) * θ' + (l : ℝ) * (Real.pi / 2)))
        (fun i => (2 * ((i : ℝ) + 1)) ^ l
          * (-(Real.sin (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2)))
              * (2 * ((i : ℝ) + 1))))
        (Finset.range t) θ (fun i _ => (hasDerivAt_cos_affine _ _ _).const_mul _)]
      rw [show (if (l + 1) = 0 then (1 : ℝ) else 0) = 0 from by
        rw [if_neg (Nat.succ_ne_zero l)]]
      rw [zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show (2 * ((i : ℝ) + 1)) ^ l
            * (-(Real.sin (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2)))
                * (2 * ((i : ℝ) + 1)))
          = (2 * ((i : ℝ) + 1)) ^ (l + 1)
            * Real.cos (2 * ((i : ℝ) + 1) * θ + (((l + 1 : ℕ)) : ℝ) * (Real.pi / 2)) from by
        rw [show 2 * ((i : ℝ) + 1) * θ + (((l + 1 : ℕ)) : ℝ) * (Real.pi / 2)
              = (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2)) + Real.pi / 2 from by
          push_cast
          ring,
          Real.cos_add_pi_div_two]
        ring]

lemma Kern_bound (l t : ℕ) (θ : ℝ) :
    |iteratedDeriv l (Kern t) θ| ≤ 2 ^ (2 * l + 2) * (2 * (t : ℝ) + 1) ^ (l + 1) := by
  have hexp : iteratedDeriv l (Kern t) θ
      = (if l = 0 then (1 : ℝ) else 0) + 2 * ∑ i ∈ Finset.range t,
          (2 * ((i : ℝ) + 1)) ^ l
            * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2)) := by
    rw [iteratedDeriv_Kern]
  rw [hexp]
  clear hexp
  have h1 : |(if l = 0 then (1 : ℝ) else 0) + 2 * ∑ i ∈ Finset.range t,
        (2 * ((i : ℝ) + 1)) ^ l
          * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))|
      ≤ 1 + 2 * ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l := by
    have h2 : |(if l = 0 then (1 : ℝ) else 0) + 2 * ∑ i ∈ Finset.range t,
          (2 * ((i : ℝ) + 1)) ^ l
            * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))|
        ≤ |(if l = 0 then (1 : ℝ) else 0)|
          + |2 * ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l
              * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))| :=
      abs_add_le _ _
    have h2' : |(if l = 0 then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    have h3 : |2 * ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l
          * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))|
        ≤ 2 * ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h4 : |∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l
            * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))|
          ≤ ∑ i ∈ Finset.range t,
              |(2 * ((i : ℝ) + 1)) ^ l
                * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))| :=
        Finset.abs_sum_le_sum_abs _ _
      have h5 : ∑ i ∈ Finset.range t,
              |(2 * ((i : ℝ) + 1)) ^ l
                * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))|
            ≤ ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one' _)
      linarith [h4, h5]
    linarith [h2, h2', h3]
  have h6 : ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l
      ≤ (t : ℝ) * (2 * (t : ℝ)) ^ l := by
    calc ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l
        ≤ ∑ i ∈ Finset.range t, (2 * (t : ℝ)) ^ l := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : (i : ℝ) + 1 ≤ (t : ℝ) := by
            have : i + 1 ≤ t := Finset.mem_range.mp hi
            exact_mod_cast this
          apply pow_le_pow_left₀ (by positivity)
          linarith
      _ = (t : ℝ) * (2 * (t : ℝ)) ^ l := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hA : (1 : ℝ) ≤ 2 ^ (l + 1) * (2 * (t : ℝ) + 1) ^ (l + 1) := by
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have h1' : (1 : ℝ) ≤ 2 ^ (l + 1) := one_le_pow₀ (by norm_num)
    have h2' : (1 : ℝ) ≤ (2 * (t : ℝ) + 1) ^ (l + 1) := one_le_pow₀ (by linarith)
    nlinarith [h1', h2']
  have hB : 2 * ((t : ℝ) * (2 * (t : ℝ)) ^ l)
      ≤ 2 ^ (l + 1) * (2 * (t : ℝ) + 1) ^ (l + 1) := by
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have h3 : 2 * ((t : ℝ) * (2 * (t : ℝ)) ^ l) = 2 ^ (l + 1) * (t : ℝ) ^ (l + 1) := by
      rw [mul_pow]
      ring
    rw [h3]
    have hle : (t : ℝ) ^ (l + 1) ≤ (2 * (t : ℝ) + 1) ^ (l + 1) := by
      apply pow_le_pow_left₀
      · exact ht0
      · linarith
    have h2p : (0 : ℝ) ≤ 2 ^ (l + 1) := by positivity
    exact mul_le_mul_of_nonneg_left hle h2p
  have hD : (2 : ℝ) ^ (l + 2) = 2 * 2 ^ (l + 1) := by
    rw [show l + 2 = l + 1 + 1 from by ring, pow_succ]
    ring
  calc |(if l = 0 then (1 : ℝ) else 0) + 2 * ∑ i ∈ Finset.range t,
        (2 * ((i : ℝ) + 1)) ^ l
          * Real.cos (2 * ((i : ℝ) + 1) * θ + (l : ℝ) * (Real.pi / 2))|
      ≤ 1 + 2 * ∑ i ∈ Finset.range t, (2 * ((i : ℝ) + 1)) ^ l := h1
    _ ≤ 1 + 2 * ((t : ℝ) * (2 * (t : ℝ)) ^ l) := by linarith [h6]
    _ ≤ 2 * (2 ^ (l + 1) * (2 * (t : ℝ) + 1) ^ (l + 1)) := by linarith [hA, hB]
    _ = 2 ^ (l + 2) * (2 * (t : ℝ) + 1) ^ (l + 1) := by rw [hD]; ring
    _ ≤ 2 ^ (2 * l + 2) * (2 * (t : ℝ) + 1) ^ (l + 1) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)

/-! ## The shift identity and the telescoping identity -/

lemma cos_shift_eq (m j : ℕ) (θ : ℝ) :
    Real.cos ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2 - θ))
      = Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2))
        * Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * θ) := by
  have hzero : Real.cos ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2)) = 0 := by
    have h1 : (2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2)
        = (((j : ℤ) - (m : ℤ) - 1 : ℤ) : ℝ) * Real.pi + Real.pi / 2 := by
      push_cast
      ring
    rw [h1, Real.cos_add_pi_div_two, Real.sin_int_mul_pi, neg_zero]
  rw [show (2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2 - θ)
        = (2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * (Real.pi / 2)
          - (2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * θ from by ring]
  rw [Real.cos_sub, hzero, zero_mul, zero_add]

lemma Kern_eq_sin_div (t : ℕ) {θ : ℝ} (h : Real.sin θ ≠ 0) :
    Real.sin ((2 * (t : ℝ) + 1) * θ) / Real.sin θ = Kern t θ := by
  induction t with
  | zero =>
      rw [Kern, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      rw [show (2 * ((0 : ℕ) : ℝ) + 1) * θ = θ from by norm_num]
      exact div_self h
  | succ t ih =>
      have hcast : (((t + 1 : ℕ)) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
      have hrec : Real.sin ((2 * ((t : ℝ) + 1) + 1) * θ)
          = Real.sin ((2 * (t : ℝ) + 1) * θ)
            + 2 * Real.cos (2 * ((t : ℝ) + 1) * θ) * Real.sin θ := by
        have h2 : Real.sin ((2 * ((t : ℝ) + 1)) * θ + θ)
            - Real.sin ((2 * ((t : ℝ) + 1)) * θ - θ)
            = 2 * Real.cos ((2 * ((t : ℝ) + 1)) * θ) * Real.sin θ := by
          rw [Real.sin_add, Real.sin_sub]
          ring
        have e1 : (2 * ((t : ℝ) + 1)) * θ + θ = (2 * ((t : ℝ) + 1) + 1) * θ := by ring
        have e2 : (2 * ((t : ℝ) + 1)) * θ - θ = (2 * (t : ℝ) + 1) * θ := by ring
        rw [e1, e2] at h2
        linarith
      rw [hcast]
      rw [hrec, add_div, ih]
      simp only [Kern]
      rw [Finset.sum_range_succ]
      have hc : (2 * Real.cos (2 * ((t : ℝ) + 1) * θ) * Real.sin θ) / Real.sin θ
          = 2 * Real.cos (2 * ((t : ℝ) + 1) * θ) := by
        field_simp
      rw [hc]
      ring

lemma sin_div_sin_Kern (m j : ℕ) {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    Real.sin ((2 * (j : ℝ) - (2 * (m : ℝ) + 1)) * θ) / Real.sin θ
      = (if j ≤ m then -(1 : ℝ) else 1) * Kern (if j ≤ m then m - j else j - m - 1) θ := by
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  split_ifs with hjm
  · have hq : 2 * (j : ℝ) - (2 * (m : ℝ) + 1) = -((2 * ((m - j : ℕ) : ℝ) + 1)) := by
      have hcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
        rw [Nat.cast_sub hjm]
      rw [hcast]
      ring
    rw [hq, show -((2 * ((m - j : ℕ) : ℝ) + 1)) * θ
          = -(((2 * ((m - j : ℕ) : ℝ) + 1)) * θ) from by ring, Real.sin_neg, neg_div,
      Kern_eq_sin_div (m - j) hsin]
    ring
  · have hjm' : m + 1 ≤ j := by omega
    have hq : 2 * (j : ℝ) - (2 * (m : ℝ) + 1) = 2 * ((j - m - 1 : ℕ) : ℝ) + 1 := by
      have hcast : ((j - m - 1 : ℕ) : ℝ) = (j : ℝ) - (m : ℝ) - 1 := by
        rw [show j - m - 1 = (j - m) - 1 from by omega,
          Nat.cast_sub (show 1 ≤ j - m by omega),
          Nat.cast_sub (show m ≤ j by omega), Nat.cast_one]
      rw [hcast]
      ring
    rw [hq, Kern_eq_sin_div (j - m - 1) hsin]
    ring

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.gC_eq_famTrig =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-! ## The values of `famC` at `0` and `1` -/

/-- `famC` of a natural number, in product form. -/
private lemma gtrig_famC_nat (n : ℕ) :
    famC (((n : ℕ)) : ℤ)
      = (∏ i ∈ Finset.range n, ((3 : ℝ) / 2 + (i : ℝ))) / (((n.factorial : ℕ)) : ℝ) := by
  rw [show famC (((n : ℕ)) : ℤ)
      = (if (0 : ℤ) ≤ (((n : ℕ)) : ℤ) then
          (∏ i ∈ Finset.range (((n : ℕ)) : ℤ).toNat, ((3 : ℝ) / 2 + i))
            / (((Nat.factorial (((n : ℕ)) : ℤ).toNat : ℕ)) : ℝ)
        else 0) from rfl,
    if_pos (Int.natCast_nonneg n), Int.toNat_natCast]

private lemma gtrig_famC_zero : famC (0 : ℤ) = 1 := by
  have h := gtrig_famC_nat 0
  simpa [Finset.prod_range_zero] using h

private lemma gtrig_famC_one : famC (1 : ℤ) = 3 / 2 := by
  have h := gtrig_famC_nat 1
  simpa [Finset.prod_range_one] using h

/-! ## The two base cases -/

private lemma gtrig_famTrig_zero (ψ : ℝ) : famTrig 0 ψ = 1 := by
  unfold famTrig
  rw [Finset.sum_range_one]
  simp [gtrig_famC_zero]

private lemma gtrig_famTrig_one (ψ : ℝ) : famTrig 1 ψ = 3 * Real.cos ψ := by
  have h : famTrig 1 ψ = (3 : ℝ) / 2 * Real.cos ψ + (3 : ℝ) / 2 * Real.cos ψ := by
    unfold famTrig
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [gtrig_famC_zero, gtrig_famC_one]
    norm_num
  rw [h]
  ring

/-! ## The recurrence satisfied by `famTrig` -/

/-- The pointwise contiguity relation of `famC` in the index form used below. -/
private lemma gtrig_coeff_nat (n j : ℕ) (hj : j ≤ n + 2) :
    ((n : ℝ) + 2) * famC (j : ℤ) * famC ((n : ℤ) + 2 - (j : ℤ))
      - ((2 * (n : ℝ) + 5) / 2) * (famC (j : ℤ) * famC ((n : ℤ) + 1 - (j : ℤ))
          + famC ((j : ℤ) - 1) * famC ((n : ℤ) + 2 - (j : ℤ)))
      + ((n : ℝ) + 3) * famC ((j : ℤ) - 1) * famC ((n : ℤ) + 1 - (j : ℤ)) = 0 := by
  have hc := famC_coeff_int n (j : ℤ) ((n : ℤ) + 2 - (j : ℤ)) (Int.natCast_nonneg j)
    (by omega) (by ring)
  rw [show ((n : ℤ) + 2 - (j : ℤ)) - 1 = (n : ℤ) + 1 - (j : ℤ) from by ring] at hc
  exact hc

/-- The termwise identity behind the recurrence. -/
private lemma gtrig_rec_term (n j : ℕ) (ψ : ℝ) (hj : j ≤ n + 2) :
    ((n : ℝ) + 2)
        * (famC (j : ℤ) * famC ((n : ℤ) + 2 - (j : ℤ))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ))
      + ((n : ℝ) + 3)
        * (famC ((j : ℤ) - 1) * famC ((n : ℤ) + 1 - (j : ℤ))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ))
      - (2 * (n : ℝ) + 5)
        * ((famC (j : ℤ) * famC ((n : ℤ) + 1 - (j : ℤ))
              + famC ((j : ℤ) - 1) * famC ((n : ℤ) + 2 - (j : ℤ)))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ) / 2) = 0 := by
  have hc := gtrig_coeff_nat n j hj
  linear_combination hc * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ)

/-- The three-term recurrence of the trigonometric Gegenbauer family. -/
private lemma gtrig_rec (n : ℕ) (ψ : ℝ) :
    ((n : ℝ) + 2) * famTrig (n + 2) ψ
      = (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
        - ((n : ℝ) + 3) * famTrig n ψ := by
  have hD : famTrig (n + 2) ψ
      = ∑ j ∈ Finset.range (n + 3), famC (j : ℤ) * famC ((n : ℤ) + 2 - (j : ℤ))
          * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ) := by
    simp only [famTrig]
    refine Finset.sum_congr ?_ (fun j _ => ?_)
    · exact congrArg Finset.range (by omega)
    · push_cast
      ring
  have h0 : ((n : ℝ) + 2) * famTrig (n + 2) ψ + ((n : ℝ) + 3) * famTrig n ψ
      - (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ = 0 := by
    rw [hD, famTrig_shift n ψ]
    rw [show (2 * (n : ℝ) + 5) * Real.cos ψ * famTrig (n + 1) ψ
          = (2 * (n : ℝ) + 5) * (Real.cos ψ * famTrig (n + 1) ψ) from by ring,
      famTrig_cos_step n ψ]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    have hjle : j ≤ n + 2 := by
      have : j < n + 3 := Finset.mem_range.mp hj
      omega
    exact gtrig_rec_term n j ψ hjle
  linear_combination h0

/-! ## The main theorem -/

theorem gC_eq_famTrig (n : ℕ) (ψ : ℝ) :
    Work.FTS.PhiStar.Gegenbauer.gC n (Real.cos ψ) = Work.FTS.PhiStar.famTrig n ψ := by
  induction n using Nat.twoStepInduction with
  | zero => exact (gtrig_famTrig_zero ψ).symm
  | one => exact (gtrig_famTrig_one ψ).symm
  | more n ih1 ih2 =>
    have hmain : ((n : ℝ) + 2) * Work.FTS.PhiStar.Gegenbauer.gC (n + 2) (Real.cos ψ)
        = ((n : ℝ) + 2) * famTrig (n + 2) ψ := by
      rw [Work.FTS.PhiStar.Gegenbauer.gC_rec n (Real.cos ψ), ih1, ih2, gtrig_rec n ψ]
    exact mul_left_cancel₀ (by positivity : ((n : ℝ) + 2) ≠ 0) hmain

end Work.FTS.PhiStar.FlatWAux
end
end
