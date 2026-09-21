import Mathlib
import Submission.Work.OddCurve.LowSlope.sol_deriv_formulas
import Submission.Work.OddCurve.LowSlope.second_deriv_numeric
import Submission.Work.OddCurve.LowSlope.radial_first_coeff

noncomputable section

open Filter Topology Set
open scoped Topology ContDiff

namespace Work.OddCurve.LowSlope

/-- `(x^m)^{1/m} = x` for `x ≥ 0`, `m ≠ 0`. -/
lemma rpow_natCast_inv_eq (x : ℝ) (hx : 0 ≤ x) {m : ℕ} (hm : m ≠ 0) :
    (x ^ m) ^ (((m : ℕ) : ℝ)⁻¹) = x := by
  rw [← Real.rpow_natCast x m, ← Real.rpow_mul hx]
  rw [show ((m : ℕ) : ℝ) * (((m : ℕ) : ℝ))⁻¹ = 1 by
    rw [mul_inv_cancel₀ (by positivity)], Real.rpow_one]

/-! ### The two second-order identities from the system, and the resulting formula for `R''` -/

lemma three_le_top : (((3 : ℕ) : WithTop ℕ∞)) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞) := by
  change ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

lemma three_ne_top : (((3 : ℕ) : WithTop ℕ∞)) ≠ (((⊤ : ℕ∞)) : WithTop ℕ∞) := by
  intro h
  have h2 := WithTop.coe_eq_coe.mp h
  simp at h2

/-- Differentiating `R^{2n+2} + r^{2n+2} = 2 + A` twice. -/
lemma second_order_one (n : ℕ) {A R r : ℝ → ℝ} {α : ℝ}
    (hR : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R α)
    (hr : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r α)
    (hA : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α)
    (hsys : ∀ᶠ β in nhds α, R β ^ (2 * n + 2) + r β ^ (2 * n + 2) = 2 + A β) :
    ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (deriv R α) ^ 2
      + ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * deriv (deriv R) α
      + ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (deriv r α) ^ 2
      + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv (deriv r) α
      - deriv (deriv A) α = 0 := by
  obtain ⟨uW, huW, hWu⟩ := hsys.exists_mem
  obtain ⟨uR, huR, hRu⟩ := hR.contDiffOn (m := ((3 : ℕ) : WithTop ℕ∞)) three_le_top
    (fun h => absurd h three_ne_top)
  obtain ⟨ur, hur, hru⟩ := hr.contDiffOn (m := ((3 : ℕ) : WithTop ℕ∞)) three_le_top
    (fun h => absurd h three_ne_top)
  obtain ⟨uA, huA, hAu⟩ := hA.contDiffOn (m := ((3 : ℕ) : WithTop ℕ∞)) three_le_top
    (fun h => absurd h three_ne_top)
  obtain ⟨vW, hvW, hoW, hαW⟩ := mem_nhds_iff.mp huW
  obtain ⟨vR, hvR, hoR, hαR⟩ := mem_nhds_iff.mp huR
  obtain ⟨vr, hvr, hor, hαr⟩ := mem_nhds_iff.mp hur
  obtain ⟨vA, hvA, hoA, hαA⟩ := mem_nhds_iff.mp huA
  have hinter : (vW ∩ vR ∩ vr ∩ vA) ∈ nhds α :=
    Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem (hoW.mem_nhds hαW) (hoR.mem_nhds hαR)) (hor.mem_nhds hαr))
      (hoA.mem_nhds hαA)
  obtain ⟨t, ht, hto, hαt⟩ := mem_nhds_iff.mp hinter
  have ht4 : ∀ β ∈ t, β ∈ vW ∧ β ∈ vR ∧ β ∈ vr ∧ β ∈ vA := by
    intro β hβ
    have h := ht hβ
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have htR : t ⊆ vR := fun β hβ => (ht4 β hβ).2.1
  have htr : t ⊆ vr := fun β hβ => (ht4 β hβ).2.2.1
  have htA : t ⊆ vA := fun β hβ => (ht4 β hβ).2.2.2
  have hRcdt : ContDiffOn ℝ (((3 : ℕ) : WithTop ℕ∞)) R t := hRu.mono (htR.trans hvR)
  have hrcdt : ContDiffOn ℝ (((3 : ℕ) : WithTop ℕ∞)) r t := hru.mono (htr.trans hvr)
  have hAcdt : ContDiffOn ℝ (((3 : ℕ) : WithTop ℕ∞)) A t := hAu.mono (htA.trans hvA)
  have hdR_cd : ContDiffOn ℝ (((2 : ℕ) : WithTop ℕ∞)) (deriv R) t :=
    hRcdt.deriv_of_isOpen hto (by norm_num)
  have hdr_cd : ContDiffOn ℝ (((2 : ℕ) : WithTop ℕ∞)) (deriv r) t :=
    hrcdt.deriv_of_isOpen hto (by norm_num)
  have hdA_cd : ContDiffOn ℝ (((2 : ℕ) : WithTop ℕ∞)) (deriv A) t :=
    hAcdt.deriv_of_isOpen hto (by norm_num)
  have hG0 : (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2)))
        - (fun β => 2 + A β)) =ᶠ[nhds α] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsys] with β hβ
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith [hβ]
  have hEt : ∀ β ∈ t,
      deriv (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2)))
        - (fun β => 2 + A β)) β
      = (((fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) * deriv R)
        + ((fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) * deriv r)
        - deriv A) β := by
    intro β hβ
    have hRβ : DifferentiableAt ℝ R β :=
      (hRcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hrβ : DifferentiableAt ℝ r β :=
      (hrcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hAβ : DifferentiableAt ℝ A β :=
      (hAcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hdRβ : DifferentiableAt ℝ (deriv R) β :=
      (hdR_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hdrβ : DifferentiableAt ℝ (deriv r) β :=
      (hdr_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hb1 : DifferentiableAt ℝ (fun β => R β ^ (2 * n + 2)) β := hRβ.fun_pow _
    have hb2 : DifferentiableAt ℝ (fun β => r β ^ (2 * n + 2)) β := hrβ.fun_pow _
    have hb3 : DifferentiableAt ℝ (fun β => (2 : ℝ) + A β) β :=
      (differentiableAt_const (c := (2 : ℝ))).add hAβ
    have hc1 : DifferentiableAt ℝ (fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) β :=
      (hRβ.fun_pow (2 * n + 1)).const_mul _
    have hc2 : DifferentiableAt ℝ (fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) β :=
      (hrβ.fun_pow (2 * n + 1)).const_mul _
    rw [deriv_sub (hb1.add hb2) hb3, deriv_add hb1 hb2, deriv_const_add (c := (2 : ℝ)),
      deriv_fun_pow hRβ (2 * n + 2), deriv_fun_pow hrβ (2 * n + 2)]
    rw [show (2 * n + 2 - 1 : ℕ) = 2 * n + 1 from by omega]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  have hderivG : deriv (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2)))
        - (fun β => 2 + A β))
      =ᶠ[nhds α] (((fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) * deriv R)
        + ((fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) * deriv r)
        - deriv A) :=
    Filter.eventuallyEq_of_mem (hto.mem_nhds hαt) (fun β hβ => hEt β hβ)
  have hzero : deriv (deriv (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2)))
      - (fun β => 2 + A β))) α = 0 := by
    have h1 : deriv (((fun β => R β ^ (2 * n + 2)) + (fun β => r β ^ (2 * n + 2)))
        - (fun β => 2 + A β)) =ᶠ[nhds α] (fun _ : ℝ => (0 : ℝ)) := by
      have h := hG0.deriv
      rwa [deriv_const'] at h
    rw [h1.deriv_eq, deriv_const]
  have hExp : deriv (((fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) * deriv R)
        + ((fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) * deriv r) - deriv A) α
      = ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (deriv R α) ^ 2
        + ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 1) * deriv (deriv R) α
        + ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (deriv r α) ^ 2
        + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1) * deriv (deriv r) α
        - deriv (deriv A) α := by
    have hRα : DifferentiableAt ℝ R α :=
      (hRcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hrα : DifferentiableAt ℝ r α :=
      (hrcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hdRα : DifferentiableAt ℝ (deriv R) α :=
      (hdR_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hdrα : DifferentiableAt ℝ (deriv r) α :=
      (hdr_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hdAα : DifferentiableAt ℝ (deriv A) α :=
      (hdA_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hc1 : DifferentiableAt ℝ (fun β => ((2 * n + 2 : ℕ) : ℝ) * R β ^ (2 * n + 1)) α :=
      (hRα.fun_pow (2 * n + 1)).const_mul _
    have hc2 : DifferentiableAt ℝ (fun β => ((2 * n + 2 : ℕ) : ℝ) * r β ^ (2 * n + 1)) α :=
      (hrα.fun_pow (2 * n + 1)).const_mul _
    rw [deriv_sub ((hc1.mul hdRα).add (hc2.mul hdrα)) hdAα, deriv_add (hc1.mul hdRα) (hc2.mul hdrα),
      deriv_mul hc1 hdRα, deriv_mul hc2 hdrα, deriv_const_mul _ (hRα.fun_pow (2 * n + 1)),
      deriv_const_mul _ (hrα.fun_pow (2 * n + 1)), deriv_fun_pow hRα (2 * n + 1),
      deriv_fun_pow hrα (2 * n + 1)]
    rw [show (2 * n + 1 - 1 : ℕ) = 2 * n from by omega]
    ring
  have h0 := hderivG.deriv_eq
  rw [hzero] at h0
  rw [← hExp]
  exact h0.symm

/-- Differentiating `R^{2n+1} - r^{2n+1} = B` twice. -/
lemma second_order_two (n : ℕ) {B R r : ℝ → ℝ} {α : ℝ}
    (hR : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R α)
    (hr : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r α)
    (hB : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α)
    (hsys : ∀ᶠ β in nhds α, R β ^ (2 * n + 1) - r β ^ (2 * n + 1) = B β) :
    ((2 * n + 1 : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * (deriv R α) ^ 2
      + ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv (deriv R) α
      - ((2 * n + 1 : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * (deriv r α) ^ 2
      - ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv (deriv r) α
      - deriv (deriv B) α = 0 := by
  obtain ⟨uW, huW, hWu⟩ := hsys.exists_mem
  obtain ⟨uR, huR, hRu⟩ := hR.contDiffOn (m := ((3 : ℕ) : WithTop ℕ∞)) three_le_top
    (fun h => absurd h three_ne_top)
  obtain ⟨ur, hur, hru⟩ := hr.contDiffOn (m := ((3 : ℕ) : WithTop ℕ∞)) three_le_top
    (fun h => absurd h three_ne_top)
  obtain ⟨uB, huB, hBu⟩ := hB.contDiffOn (m := ((3 : ℕ) : WithTop ℕ∞)) three_le_top
    (fun h => absurd h three_ne_top)
  obtain ⟨vW, hvW, hoW, hαW⟩ := mem_nhds_iff.mp huW
  obtain ⟨vR, hvR, hoR, hαR⟩ := mem_nhds_iff.mp huR
  obtain ⟨vr, hvr, hor, hαr⟩ := mem_nhds_iff.mp hur
  obtain ⟨vB, hvB, hoB, hαB⟩ := mem_nhds_iff.mp huB
  have hinter : (vW ∩ vR ∩ vr ∩ vB) ∈ nhds α :=
    Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem (hoW.mem_nhds hαW) (hoR.mem_nhds hαR)) (hor.mem_nhds hαr))
      (hoB.mem_nhds hαB)
  obtain ⟨t, ht, hto, hαt⟩ := mem_nhds_iff.mp hinter
  have ht4 : ∀ β ∈ t, β ∈ vW ∧ β ∈ vR ∧ β ∈ vr ∧ β ∈ vB := by
    intro β hβ
    have h := ht hβ
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have htR : t ⊆ vR := fun β hβ => (ht4 β hβ).2.1
  have htr : t ⊆ vr := fun β hβ => (ht4 β hβ).2.2.1
  have htB : t ⊆ vB := fun β hβ => (ht4 β hβ).2.2.2
  have hRcdt : ContDiffOn ℝ (((3 : ℕ) : WithTop ℕ∞)) R t := hRu.mono (htR.trans hvR)
  have hrcdt : ContDiffOn ℝ (((3 : ℕ) : WithTop ℕ∞)) r t := hru.mono (htr.trans hvr)
  have hBcdt : ContDiffOn ℝ (((3 : ℕ) : WithTop ℕ∞)) B t := hBu.mono (htB.trans hvB)
  have hdR_cd : ContDiffOn ℝ (((2 : ℕ) : WithTop ℕ∞)) (deriv R) t :=
    hRcdt.deriv_of_isOpen hto (by norm_num)
  have hdr_cd : ContDiffOn ℝ (((2 : ℕ) : WithTop ℕ∞)) (deriv r) t :=
    hrcdt.deriv_of_isOpen hto (by norm_num)
  have hdB_cd : ContDiffOn ℝ (((2 : ℕ) : WithTop ℕ∞)) (deriv B) t :=
    hBcdt.deriv_of_isOpen hto (by norm_num)
  have hG0 : (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1)))
        - B) =ᶠ[nhds α] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsys] with β hβ
    simp only [Pi.sub_apply]
    linarith [hβ]
  have hEt : ∀ β ∈ t,
      deriv (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1))) - B) β
      = (((fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) * deriv R)
        - ((fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) * deriv r)
        - deriv B) β := by
    intro β hβ
    have hRβ : DifferentiableAt ℝ R β :=
      (hRcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hrβ : DifferentiableAt ℝ r β :=
      (hrcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hBβ : DifferentiableAt ℝ B β :=
      (hBcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hβ)
    have hb1 : DifferentiableAt ℝ (fun β => R β ^ (2 * n + 1)) β := hRβ.fun_pow _
    have hb2 : DifferentiableAt ℝ (fun β => r β ^ (2 * n + 1)) β := hrβ.fun_pow _
    have hc1 : DifferentiableAt ℝ (fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) β :=
      (hRβ.fun_pow (2 * n)).const_mul _
    have hc2 : DifferentiableAt ℝ (fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) β :=
      (hrβ.fun_pow (2 * n)).const_mul _
    rw [deriv_sub (hb1.sub hb2) hBβ, deriv_sub hb1 hb2,
      deriv_fun_pow hRβ (2 * n + 1), deriv_fun_pow hrβ (2 * n + 1)]
    rw [show (2 * n + 1 - 1 : ℕ) = 2 * n from by omega]
    simp only [Pi.sub_apply, Pi.mul_apply]
  have hderivG : deriv (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1))) - B)
      =ᶠ[nhds α] (((fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) * deriv R)
        - ((fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) * deriv r)
        - deriv B) :=
    Filter.eventuallyEq_of_mem (hto.mem_nhds hαt) (fun β hβ => hEt β hβ)
  have hzero : deriv (deriv (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1))) - B)) α
      = 0 := by
    have h1 : deriv (((fun β => R β ^ (2 * n + 1)) - (fun β => r β ^ (2 * n + 1))) - B)
        =ᶠ[nhds α] (fun _ : ℝ => (0 : ℝ)) := by
      have h := hG0.deriv
      rwa [deriv_const'] at h
    rw [h1.deriv_eq, deriv_const]
  have hExp : deriv (((fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) * deriv R)
        - ((fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) * deriv r) - deriv B) α
      = ((2 * n + 1 : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ) * R α ^ (2 * n - 1) * (deriv R α) ^ 2
        + ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * deriv (deriv R) α
        - ((2 * n + 1 : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ) * r α ^ (2 * n - 1) * (deriv r α) ^ 2
        - ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * deriv (deriv r) α
        - deriv (deriv B) α := by
    have hRα : DifferentiableAt ℝ R α :=
      (hRcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hrα : DifferentiableAt ℝ r α :=
      (hrcdt.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hdRα : DifferentiableAt ℝ (deriv R) α :=
      (hdR_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hdrα : DifferentiableAt ℝ (deriv r) α :=
      (hdr_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hdBα : DifferentiableAt ℝ (deriv B) α :=
      (hdB_cd.differentiableOn (by norm_num)).differentiableAt (hto.mem_nhds hαt)
    have hc1 : DifferentiableAt ℝ (fun β => ((2 * n + 1 : ℕ) : ℝ) * R β ^ (2 * n)) α :=
      (hRα.fun_pow (2 * n)).const_mul _
    have hc2 : DifferentiableAt ℝ (fun β => ((2 * n + 1 : ℕ) : ℝ) * r β ^ (2 * n)) α :=
      (hrα.fun_pow (2 * n)).const_mul _
    rw [deriv_sub ((hc1.mul hdRα).sub (hc2.mul hdrα)) hdBα,
      deriv_sub (hc1.mul hdRα) (hc2.mul hdrα), deriv_mul hc1 hdRα, deriv_mul hc2 hdrα,
      deriv_const_mul _ (hRα.fun_pow (2 * n)), deriv_const_mul _ (hrα.fun_pow (2 * n)),
      deriv_fun_pow hRα (2 * n), deriv_fun_pow hrα (2 * n)]
    rw [show (2 * n - 1 : ℕ) = 2 * n - 1 from rfl]
    ring
  have h0 := hderivG.deriv_eq
  rw [hzero] at h0
  rw [← hExp]
  exact h0.symm

/-- **The second-order identity for `R`**: solving the two differentiated system equations. -/
theorem sol_deriv2_R_formula_aux (n : ℕ) (hn : 1 ≤ n) {A B R r : ℝ → ℝ} {α : ℝ}
    (hR : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R α)
    (hr : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r α)
    (hA : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α)
    (hB : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α)
    (hRpos : 0 < R α) (hrpos : 0 < r α)
    (hsys : ∀ᶠ β in nhds α, R β ^ (2 * n + 2) + r β ^ (2 * n + 2) = 2 + A β ∧
      R β ^ (2 * n + 1) - r β ^ (2 * n + 1) = B β) :
    deriv (deriv R) α
      = deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
        + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
        - (deriv R α) ^ 2 * ((((2 * n + 2 : ℕ) : ℝ) - 1) - r α / (R α + r α)) / R α
        - (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α) := by
  have h1 := second_order_one n hR hr hA (hsys.mono fun β h => h.1)
  have h2 := second_order_two n hR hr hB (hsys.mono fun β h => h.2)
  have hC : ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * r α ^ (2 * n)
      * (R α + r α) ≠ 0 := by
    have h1' : (0 : ℝ) < (((2 * n + 2 : ℕ) : ℝ)) := by positivity
    have h2' : (0 : ℝ) < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
    have h3' : (0 : ℝ) < R α ^ (2 * n) := pow_pos hRpos _
    have h4' : (0 : ℝ) < r α ^ (2 * n) := pow_pos hrpos _
    have h5' : (0 : ℝ) < R α + r α := by linarith
    positivity
  have hkey : ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * r α ^ (2 * n)
        * (R α + r α) * deriv (deriv R) α
      = ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)
          * (deriv (deriv A) α - ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ)
              * (R α ^ (2 * n) * (deriv R α) ^ 2 + r α ^ (2 * n) * (deriv r α) ^ 2))
        + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1)
          * (deriv (deriv B) α - ((2 * n + 1 : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ)
              * (R α ^ (2 * n - 1) * (deriv R α) ^ 2 - r α ^ (2 * n - 1) * (deriv r α) ^ 2)) := by
    linear_combination (((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)) * h1
      + (((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1)) * h2
  have hN : ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * r α ^ (2 * n)
        * (R α + r α)
        * (deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
          + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
          - (deriv R α) ^ 2 * ((((2 * n + 2 : ℕ) : ℝ) - 1) - r α / (R α + r α)) / R α
          - (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α))
      = ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)
          * (deriv (deriv A) α - ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ)
              * (R α ^ (2 * n) * (deriv R α) ^ 2 + r α ^ (2 * n) * (deriv r α) ^ 2))
        + ((2 * n + 2 : ℕ) : ℝ) * r α ^ (2 * n + 1)
          * (deriv (deriv B) α - ((2 * n + 1 : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ)
              * (R α ^ (2 * n - 1) * (deriv R α) ^ 2 - r α ^ (2 * n - 1) * (deriv r α) ^ 2)) := by
    rw [pow_sub₀ (R α) (ne_of_gt hRpos) (show 1 ≤ 2 * n by omega),
      pow_sub₀ (r α) (ne_of_gt hrpos) (show 1 ≤ 2 * n by omega), div_pow]
    field_simp
    push_cast
    ring
  exact mul_left_cancel₀ hC (hkey.trans hN.symm)


set_option maxHeartbeats 4000000 in
/-- The two derivative bounds of the low-slope odd two-power radial system. -/
theorem deriv_bounds_generic (n : ℕ) (hn : 1 ≤ n) {A B R r : ℝ → ℝ} {σ δ α : ℝ}
    (hσ : 0 < σ) (hσ' : σ ≤ 1 / 2) (hδ : 0 < δ)
    (hRc : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) R α)
    (hrc : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) r α)
    (hAcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A α)
    (hBcd : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) B α)
    (hRpos : 0 < R α) (hrpos : 0 < r α)
    (hsys : ∀ᶠ β in nhds α, R β ^ (2 * n + 2) + r β ^ (2 * n + 2) = 2 + A β ∧
      R β ^ (2 * n + 1) - r β ^ (2 * n + 1) = B β)
    (ha1 : 3 / 8 ≤ R α ^ (2 * n + 2)) (ha2 : R α ^ (2 * n + 2) ≤ 15 / 8)
    (hb1 : 3 / 8 ≤ r α ^ (2 * n + 2)) (hb2 : r α ^ (2 * n + 2) ≤ 15 / 8)
    (hAval : |A α| ≤ σ) (hBval : |B α| ≤ σ)
    (hA1 : |deriv A α| ≤ Real.sqrt (2 * δ * (σ - |A α|)))
    (hB1 : |deriv B α| ≤ Real.sqrt (2 * δ * (σ - |B α|)))
    (hA2 : |deriv (deriv A) α| ≤ δ) (hB2 : |deriv (deriv B) α| ≤ δ) :
    |deriv R α| ≤ (Real.log (1 + σ) + 1 + δ) / ((n : ℝ) + 1) ∧
      |deriv (deriv R) α| ≤ (Real.log (1 + σ) + 1 + 2 * δ) / ((n : ℝ) + 1) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hP2 : ((2 * n + 2 : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by push_cast; ring
  obtain ⟨hmα, hvα⟩ := hsys.self_of_nhds
  obtain ⟨hR', hr'⟩ := sol_deriv_formulas n hRc hrc hAcd hBcd hRpos hrpos hsys
  have hAeq : A α = R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2 := by linarith [hmα]
  have hBeq : B α = R α ^ (2 * n + 1) - r α ^ (2 * n + 1) := by linarith [hvα]
  have hA1' : |deriv A α| ≤
      Real.sqrt (2 * δ * (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|)) := by
    rw [← hAeq]; exact hA1
  have hB1' : |deriv B α| ≤
      Real.sqrt (2 * δ * (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) := by
    rw [← hBeq]; exact hB1
  have hm_le : |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2| ≤ σ := by
    rw [← hAeq]; exact hAval
  have hv_le : |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)| ≤ σ := by
    rw [← hBeq]; exact hBval
  have hlog : 0 ≤ Real.log (1 + σ) := Real.log_nonneg (by linarith)
  constructor
  · -- ================= the first derivative =================
    have hDpos : 0 < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n)
        * (R α + r α) := by
      have h1 : (0 : ℝ) < R α ^ (2 * n) := pow_pos hRpos _
      have h2 : (0 : ℝ) < R α + r α := by linarith
      positivity
    have hfr := radial_first_coeff n hn ha1 ha2 hb1 hb2
    rw [rpow_natCast_inv_eq (R α) (le_of_lt hRpos) (by omega : 2 * n + 2 ≠ 0),
      rpow_natCast_inv_eq (r α) (le_of_lt hrpos) (by omega : 2 * n + 2 ≠ 0)] at hfr
    dsimp only at hfr
    rw [show 2 * (n : ℝ) + 2 = ((2 * n + 2 : ℕ) : ℝ) by push_cast; ring,
      show 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring] at hfr
    have hXeq : R α ^ 2 / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n + 2) * (R α + r α))
        + R α ^ 2 * r α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n + 2) * (R α + r α))
        = (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α)
          / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
      have hR : R α ≠ 0 := ne_of_gt hRpos
      field_simp
      push_cast
      ring
    rw [hXeq] at hfr
    have hcoef : (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α)
        / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
        ≤ 3 / (2 * ((n : ℝ) + 1)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))]
      linarith [hfr]
    have hcoef' : (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α)
        ≤ (3 / (2 * ((n : ℝ) + 1)))
          * (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
      have h := mul_le_mul_of_nonneg_right hcoef hDpos.le
      have hYD : (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α)
            / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
            * (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))
          = (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α) := by
        have hne : (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n)
            * (R α + r α)) ≠ 0 := ne_of_gt hDpos
        field_simp
      rw [hYD] at h
      exact h
    have hnum1 : |((2 * n + 1 : ℕ) : ℝ) * deriv A α + ((2 * n + 2 : ℕ) : ℝ) * r α * deriv B α|
        ≤ (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α) * Real.sqrt (2 * δ * σ) := by
      have h1 : |deriv A α| ≤ Real.sqrt (2 * δ * σ) :=
        le_trans hA1' (Real.sqrt_le_sqrt (by
          nlinarith only [abs_nonneg (R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2), hδ.le, hσ.le]))
      have h2 : |deriv B α| ≤ Real.sqrt (2 * δ * σ) :=
        le_trans hB1' (Real.sqrt_le_sqrt (by
          nlinarith only [abs_nonneg (R α ^ (2 * n + 1) - r α ^ (2 * n + 1)), hδ.le, hσ.le]))
      have hQ : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by positivity
      have hPn : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * r α := by positivity
      rw [abs_le] at h1 h2
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have ha := mul_le_mul_of_nonneg_left h1.1 hQ
        have hb := mul_le_mul_of_nonneg_left h2.1 hPn
        nlinarith only [ha, hb]
      · have ha := mul_le_mul_of_nonneg_left h1.2 hQ
        have hb := mul_le_mul_of_nonneg_left h2.2 hPn
        nlinarith only [ha, hb]
    have hsq_le : Real.sqrt (2 * δ * σ) ≤ Real.sqrt δ :=
      Real.sqrt_le_sqrt (by nlinarith only [hδ.le, hσ'])
    have h3half : (3 / 2 : ℝ) * Real.sqrt δ ≤ Real.log (1 + σ) + 1 + δ := by
      have hsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
      have hkey : (3 / 2 : ℝ) * Real.sqrt δ ≤ 1 + δ := by
        nlinarith only [sq_nonneg (Real.sqrt δ - 3 / 4), hsq]
      linarith [hkey, hlog]
    rw [hR', abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos, div_mul_eq_mul_div, le_div_iff₀ hn1]
    calc |((2 * n + 1 : ℕ) : ℝ) * deriv A α + ((2 * n + 2 : ℕ) : ℝ) * r α * deriv B α|
            * ((n : ℝ) + 1)
        ≤ (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α) * Real.sqrt (2 * δ * σ)
            * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hnum1 (by positivity)
      _ ≤ (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α) * Real.sqrt δ
            * ((n : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsq_le (by positivity)
      _ = (((2 * n + 1 : ℕ) : ℝ) + ((2 * n + 2 : ℕ) : ℝ) * r α)
            * ((n : ℝ) + 1) * Real.sqrt δ := by ring
      _ ≤ (3 / (2 * ((n : ℝ) + 1))
            * (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)))
            * ((n : ℝ) + 1) * Real.sqrt δ := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg δ)
          exact mul_le_mul_of_nonneg_right hcoef' (by positivity)
      _ = (3 / 2) * Real.sqrt δ
            * (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
          field_simp
      _ ≤ (Real.log (1 + σ) + 1 + δ)
            * (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) :=
          mul_le_mul_of_nonneg_right h3half (by positivity)
  · -- ================= the second derivative =================
    have hD1 : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α) := by
      have h1 : (0 : ℝ) < R α ^ (2 * n) := pow_pos hRpos _
      have h2 : (0 : ℝ) < R α + r α := by linarith
      positivity
    have hD2 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α) := by
      have h1 : (0 : ℝ) < R α ^ (2 * n) := pow_pos hRpos _
      have h2 : (0 : ℝ) < R α + r α := by linarith
      positivity
    have hD1Q : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n)
        * (R α + r α) := by
      have h1 : (0 : ℝ) < R α ^ (2 * n) := pow_pos hRpos _
      have h2 : (0 : ℝ) < R α + r α := by linarith
      positivity
    have hD2Q : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n)
        * (R α + r α) := by
      have h1 : (0 : ℝ) < r α ^ (2 * n) := pow_pos hrpos _
      have h2 : (0 : ℝ) < R α + r α := by linarith
      positivity
    have hD3 : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 4)
        * (R α + r α) ^ 2 := by
      have h1 : (0 : ℝ) < R α ^ (4 * n + 4) := pow_pos hRpos _
      have h2 : (0 : ℝ) < (R α + r α) ^ 2 := by positivity
      positivity
    have hD4 : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R α * r α) ^ (2 * n)
        * (R α + r α) ^ 3 := by
      have h1 : (0 : ℝ) < (R α * r α) ^ (2 * n) := pow_pos (by positivity) _
      have h2 : (0 : ℝ) < (R α + r α) ^ 3 := by positivity
      positivity
    have hD5 : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n)
        * (R α + r α) ^ 2 := by
      have h1 : (0 : ℝ) < R α ^ (4 * n) := pow_pos hRpos _
      have h2 : (0 : ℝ) < (R α + r α) ^ 2 := by positivity
      positivity
    have hD6 : (0 : ℝ) < ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * r α ^ (4 * n)
        * (R α + r α) ^ 2 := by
      have h1 : (0 : ℝ) < r α ^ (4 * n) := pow_pos hrpos _
      have h2 : (0 : ℝ) < (R α + r α) ^ 2 := by positivity
      positivity
    -- squared first-derivative bounds
    have hRsq : (deriv R α) ^ 2
        ≤ 2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2
          / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n) * (R α + r α) ^ 2) := by
      have hnum : |((2 * n + 1 : ℕ) : ℝ) * deriv A α + ((2 * n + 2 : ℕ) : ℝ) * r α * deriv B α|
          ≤ Real.sqrt (2 * δ) * ((((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|))) := by
        have h1 : |deriv A α| ≤ Real.sqrt (2 * δ)
            * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) := by
          rw [← Real.sqrt_mul (by positivity)]; exact hA1'
        have h2 : |deriv B α| ≤ Real.sqrt (2 * δ)
            * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|) := by
          rw [← Real.sqrt_mul (by positivity)]; exact hB1'
        have hQ : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by positivity
        have hPn : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * r α := by positivity
        rw [abs_le] at h1 h2
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have ha := mul_le_mul_of_nonneg_left h1.1 hQ
          have hb := mul_le_mul_of_nonneg_left h2.1 hPn
          nlinarith only [ha, hb]
        · have ha := mul_le_mul_of_nonneg_left h1.2 hQ
          have hb := mul_le_mul_of_nonneg_left h2.2 hPn
          nlinarith only [ha, hb]
      have hbdd : |deriv R α| ≤ Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
        rw [hR', abs_div, abs_of_pos hD1Q, div_le_div_iff_of_pos_right hD1Q]
        exact hnum
      have hnn : 0 ≤ Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by positivity
      have h2 : (deriv R α) ^ 2 ≤ (Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) ^ 2 := by
        have h1 := abs_le.mp hbdd
        nlinarith only [h1.1, h1.2, hnn]
      rwa [show (Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) ^ 2 = 2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n) * (R α + r α) ^ 2) from by
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * δ)]
        field_simp
        ring] at h2
    have hrsq : (deriv r α) ^ 2
        ≤ 2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2
          / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * r α ^ (4 * n) * (R α + r α) ^ 2) := by
      have hnum : |((2 * n + 1 : ℕ) : ℝ) * deriv A α - ((2 * n + 2 : ℕ) : ℝ) * R α * deriv B α|
          ≤ Real.sqrt (2 * δ) * ((((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|))) := by
        have h1 : |deriv A α| ≤ Real.sqrt (2 * δ)
            * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) := by
          rw [← Real.sqrt_mul (by positivity)]; exact hA1'
        have h2 : |deriv B α| ≤ Real.sqrt (2 * δ)
            * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|) := by
          rw [← Real.sqrt_mul (by positivity)]; exact hB1'
        have hQ : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by positivity
        have hPR : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) * R α := by positivity
        rw [abs_le] at h1 h2
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have ha := mul_le_mul_of_nonneg_left h1.1 hQ
          have hb := mul_le_mul_of_nonneg_left h2.2 hPR
          nlinarith only [ha, hb]
        · have ha := mul_le_mul_of_nonneg_left h1.2 hQ
          have hb := mul_le_mul_of_nonneg_left h2.1 hPR
          nlinarith only [ha, hb]
      have hbdd : |deriv r α| ≤ Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (R α + r α)) := by
        rw [hr', abs_div, abs_of_pos hD2Q, div_le_div_iff_of_pos_right hD2Q]
        exact hnum
      have hnn : 0 ≤ Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (R α + r α)) := by positivity
      have h2 : (deriv r α) ^ 2 ≤ (Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (R α + r α))) ^ 2 := by
        have h1 := abs_le.mp hbdd
        nlinarith only [h1.1, h1.2, hnn]
      rwa [show (Real.sqrt (2 * δ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * r α ^ (2 * n) * (R α + r α))) ^ 2 = 2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * r α ^ (4 * n) * (R α + r α) ^ 2) from by
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * δ)]
        field_simp
        ring] at h2
    have hform := sol_deriv2_R_formula_aux n hn hRc hrc hAcd hBcd hRpos hrpos hsys
    have hcpos : 0 ≤ ((((2 * n + 2 : ℕ) : ℝ) - 1) - r α / (R α + r α)) := by
      have hPQ : ((2 * n + 2 : ℕ) : ℝ) - 1 = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hPQ, sub_nonneg, div_le_iff₀ (by linarith : (0 : ℝ) < R α + r α)]
      have hQ1 : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ 2 * n + 1 := by omega
        exact_mod_cast this
      nlinarith only [hrpos, hRpos, hQ1]
    have hT1 : |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| ≤ δ / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
      rw [abs_div, abs_of_pos hD1, div_le_div_iff_of_pos_right hD1]
      exact hA2
    have hT2 : |r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| ≤ r α * δ / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) := by
      rw [abs_div, abs_of_pos hD2, abs_mul, abs_of_pos hrpos, div_le_div_iff_of_pos_right hD2]
      exact mul_le_mul_of_nonneg_left hB2 (le_of_lt hrpos)
    have hT3 : |(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α| ≤ 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ := by
      have hcnn : (0 : ℝ) ≤ ((((2 * n + 2 : ℕ) : ℝ) - 1) - r α / (R α + r α)) := hcpos
      have hc : ((((2 * n + 2 : ℕ) : ℝ) - 1) - r α / (R α + r α)) ≤ (((2 * n + 2 : ℕ) : ℝ) - 1) := by
        have hnn : 0 ≤ r α / (R α + r α) := by positivity
        linarith [hnn]
      have ht3nn : 0 ≤ (deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α :=
        div_nonneg (mul_nonneg (sq_nonneg _) hcnn) (le_of_lt hRpos)
      rw [abs_of_nonneg ht3nn]
      have hstep1 : (deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α ≤ (deriv R α) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / R α := by
        rw [div_le_div_iff_of_pos_right hRpos]
        exact mul_le_mul_of_nonneg_left hc (sq_nonneg (deriv R α))
      have hstep2 : (deriv R α) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / R α ≤ 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ := by
        have hP1 : (0 : ℝ) ≤ (((2 * n + 2 : ℕ) : ℝ) - 1) := by
          have h2 : (1 : ℕ) ≤ 2 * n + 2 := by omega
          have h3 : (1 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by exact_mod_cast h2
          linarith
        have h4 := mul_le_mul_of_nonneg_right hRsq (div_nonneg hP1 (le_of_lt hRpos))
        have hid : (2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n) * (R α + r α) ^ 2)) * (((((2 * n + 2 : ℕ) : ℝ) - 1) / R α)) = 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ := by
          field_simp
          push_cast
          ring
        calc (deriv R α) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / R α
            = (deriv R α) ^ 2 * ((((2 * n + 2 : ℕ) : ℝ) - 1) / R α) := by ring
          _ ≤ (2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n) * (R α + r α) ^ 2)) * (((((2 * n + 2 : ℕ) : ℝ) - 1) / R α)) := h4
          _ = 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ := hid
      exact hstep1.trans hstep2
    have hT4 : |(r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)| ≤ 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3) * δ := by
      have ht4nn : 0 ≤ (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α) := by positivity
      rw [abs_of_nonneg ht4nn]
      have h4 := mul_le_mul_of_nonneg_left hrsq (by positivity : (0 : ℝ) ≤ (r α / R α) ^ (2 * n))
      have hid : (r α / R α) ^ (2 * n) * (2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * r α ^ (4 * n) * (R α + r α) ^ 2)) / (R α + r α) = 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3) * δ := by
        rw [div_pow, show 4 * n = 2 * n + 2 * n by ring, pow_add]
        field_simp
        push_cast
        ring
      calc (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)
          = (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α) := rfl
        _ ≤ (r α / R α) ^ (2 * n) * (2 * δ * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * r α ^ (4 * n) * (R α + r α) ^ 2)) / (R α + r α) :=
            div_le_div_of_nonneg_right h4 (by linarith : (0 : ℝ) ≤ R α + r α)
        _ = 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3) * δ := hid
    have hY : |deriv (deriv R) α| ≤ δ * (1 / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (r α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3)))) := by
      rw [hform]
      have h3 : |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) - (deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α - (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)|
          ≤ |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α| + |(r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)| := by
        have h := abs_sub (deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) ((deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α + (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α))
        have h1 := abs_add_le (deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) (r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)))
        have h2 := abs_add_le ((deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α) ((r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α))
        calc |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) - (deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α - (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)|
            = |(deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) - ((deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α + (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α))| := by ring_nf
          _ ≤ |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α + (r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)| := h
          _ ≤ (|deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))|) + (|(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α| + |(r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)|) := add_le_add h1 h2
          _ = |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α| + |(r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)| := by ring
      have hsum4 : |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α| + |(r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)|
          ≤ δ / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * δ / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3) * δ) := by
        have h12 := add_le_add hT1 hT2
        have h34 := add_le_add hT3 hT4
        calc |deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α| + |(r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)|
            = (|deriv (deriv A) α / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))| + |r α * deriv (deriv B) α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))|) + (|(deriv R α) ^ 2 * (((((2 * n + 2 : ℕ) : ℝ)) - 1) - r α / (R α + r α)) / R α| + |(r α / R α) ^ (2 * n) * (deriv r α) ^ 2 / (R α + r α)|) := by ring
          _ ≤ (δ / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * δ / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α))) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3) * δ) := add_le_add h12 h34
          _ = δ / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * δ / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3) * δ) := by ring
      have hfinal : δ / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + r α * δ / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) * δ + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3) * δ) = δ * (1 / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (r α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3)))) := by
        field_simp
        push_cast
        ring
      exact h3.trans (hsum4.trans (le_of_eq hfinal))
    have hZX : (1 / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (r α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3)))) = ((1 + r α * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R α ^ 2 / (R α ^ (2 * n + 2) * (R α + r α)) + 2 * ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * R α ^ 3 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 4) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R α * r α) ^ (2 * n) * (R α + r α) ^ 3)) / (((2 * n + 2 : ℕ) : ℝ)) := by
      rw [show R α ^ (4 * n + 4) = R α ^ (4 * n + 1) * R α ^ 3 by ring,
        show (R α * r α) ^ (2 * n) = R α ^ (2 * n) * r α ^ (2 * n) by rw [mul_pow]]
      field_simp
      push_cast
      ring
    have hnum : ((1 + r α * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R α ^ 2 / (R α ^ (2 * n + 2) * (R α + r α)) + 2 * ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * R α ^ 3 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 4) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R α * r α) ^ (2 * n) * (R α + r α) ^ 3)) ≤ 4 :=
      second_deriv_numeric n hn hσ hσ' hRpos hrpos ha1 ha2 hb1 hb2 hm_le hv_le
    have hfin : |deriv (deriv R) α| ≤ 4 * δ / (((2 * n + 2 : ℕ) : ℝ)) := by
      have hstep : δ * (1 / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (r α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3)))) ≤ δ / (((2 * n + 2 : ℕ) : ℝ)) * 4 := by
        rw [hZX]
        have h2 : δ * ((((1 + r α * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R α ^ 2 / (R α ^ (2 * n + 2) * (R α + r α)) + 2 * ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * R α ^ 3 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 4) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R α * r α) ^ (2 * n) * (R α + r α) ^ 3)) / (((2 * n + 2 : ℕ) : ℝ)))) ≤ δ / (((2 * n + 2 : ℕ) : ℝ)) * 4 := by
          have := mul_le_mul_of_nonneg_left hnum (by positivity : (0 : ℝ) ≤ δ / (((2 * n + 2 : ℕ) : ℝ)))
          calc δ * ((((1 + r α * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R α ^ 2 / (R α ^ (2 * n + 2) * (R α + r α)) + 2 * ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * R α ^ 3 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 4) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R α * r α) ^ (2 * n) * (R α + r α) ^ 3)) / (((2 * n + 2 : ℕ) : ℝ)))) = δ / (((2 * n + 2 : ℕ) : ℝ)) * ((1 + r α * ((2 * n + 2 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * R α ^ 2 / (R α ^ (2 * n + 2) * (R α + r α)) + 2 * ((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * R α ^ 3 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 4) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (R α * r α) ^ (2 * n) * (R α + r α) ^ 3)) := by ring
            _ ≤ δ / (((2 * n + 2 : ℕ) : ℝ)) * 4 := this
        exact h2
      calc |deriv (deriv R) α| ≤ δ * (1 / (((2 * n + 2 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (r α / (((2 * n + 1 : ℕ) : ℝ) * R α ^ (2 * n) * (R α + r α)) + (2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * r α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 * (((2 * n + 2 : ℕ) : ℝ) - 1) / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (4 * n + 1) * (R α + r α) ^ 2) + 2 * (((2 * n + 1 : ℕ) : ℝ) * Real.sqrt (σ - |R α ^ (2 * n + 2) + r α ^ (2 * n + 2) - 2|) + ((2 * n + 2 : ℕ) : ℝ) * R α * Real.sqrt (σ - |R α ^ (2 * n + 1) - r α ^ (2 * n + 1)|)) ^ 2 / (((2 * n + 2 : ℕ) : ℝ) ^ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ 2 * R α ^ (2 * n) * r α ^ (2 * n) * (R α + r α) ^ 3)))) := hY
        _ ≤ δ / (((2 * n + 2 : ℕ) : ℝ)) * 4 := hstep
        _ = 4 * δ / (((2 * n + 2 : ℕ) : ℝ)) := by ring
    rw [hP2] at hfin
    rw [show 4 * δ / (2 * ((n : ℝ) + 1)) = 2 * δ / ((n : ℝ) + 1) by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring] at hfin
    calc |deriv (deriv R) α| ≤ 2 * δ / ((n : ℝ) + 1) := hfin
      _ ≤ (Real.log (1 + σ) + 1 + 2 * δ) / ((n : ℝ) + 1) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hn1)
          linarith [hlog]
end Work.OddCurve.LowSlope