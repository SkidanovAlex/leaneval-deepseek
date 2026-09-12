import Submission.MarkovSHelper

noncomputable section

open scoped Real BigOperators
open Polynomial Filter

namespace Submission

namespace MarkovSValue

open MarkovSHelper

lemma TPoly_sin_wave {n m : ℕ} (hm : m ≤ n) (θ : ℝ) :
    TPoly n (fun _ : ℕ => 0) (fun k => if k = m then 1 else 0) θ = Real.sin ((m : ℝ) * θ) := by
  unfold TPoly
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hm'
    have : m ∈ Finset.range (n + 1) := by simp [Nat.lt_succ_of_le hm]
    exact (hm' this).elim

lemma TPoly_cos_shift (n : ℕ) (β : ℝ) (θ : ℝ) :
    TPoly n (fun k => if k = n then Real.cos β else 0)
      (fun k => if k = n then Real.sin β else 0) θ = Real.cos ((n : ℝ) * θ - β) := by
  let aC : ℕ → ℝ := fun k => if k = n then Real.cos β else 0
  let bC : ℕ → ℝ := fun k => if k = n then Real.sin β else 0
  change TPoly n aC bC θ = Real.cos ((n : ℝ) * θ - β)
  have hc : TPoly n aC (fun _ : ℕ => 0) θ = Real.cos β * Real.cos ((n : ℝ) * θ) := by
    have hfun1 : aC = fun k => Real.cos β * (if k = n then 1 else 0) := by
      funext k
      by_cases hk : k = n <;> simp [aC, hk]
    rw [hfun1]
    simpa [TPoly_cos_wave] using
      (TPoly_smul n (Real.cos β) (fun k => if k = n then 1 else 0) (fun _ : ℕ => 0) θ)
  have hs : TPoly n (fun _ : ℕ => 0) bC θ = Real.sin β * Real.sin ((n : ℝ) * θ) := by
    have hfun2 : bC = fun k => Real.sin β * (if k = n then 1 else 0) := by
      funext k
      by_cases hk : k = n <;> simp [bC, hk]
    rw [hfun2]
    simpa [TPoly_sin_wave] using
      (TPoly_smul n (Real.sin β) (fun _ : ℕ => 0) (fun k => if k = n then 1 else 0) θ)
  calc
    TPoly n aC bC θ = TPoly n aC (fun _ : ℕ => 0) θ + TPoly n (fun _ : ℕ => 0) bC θ := by
      simpa using (TPoly_add n aC (fun _ : ℕ => 0) (fun _ : ℕ => 0) bC θ)
    _ = Real.cos β * Real.cos ((n : ℝ) * θ) + Real.sin β * Real.sin ((n : ℝ) * θ) := by
      rw [hc, hs]
    _ = Real.cos ((n : ℝ) * θ - β) := by
      rw [Real.cos_sub]
      ring

lemma cos_sub_one_mul_pi (m : ℕ) :
    Real.cos (((m : ℝ) - 1) * π) = if Even m then -1 else 1 := by
  have hrew : (((m : ℝ) - 1) * π) = (m : ℝ) * π - π := by ring
  rw [hrew, Real.cos_sub_pi]
  have hcos : Real.cos ((m : ℝ) * π) = (-1 : ℝ) ^ m := by
    simpa using (Real.cos_add_nat_mul_pi (0 : ℝ) m)
  rw [hcos, neg_one_pow_eq_ite]
  by_cases hm : Even m <;> simp [hm]

lemma differentiable_TPoly (n : ℕ) (a b : ℕ → ℝ) (η : ℝ) :
    DifferentiableAt ℝ (TPoly n a b) η := by
  have hfun : TPoly n a b =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * x) + b k * Real.sin ((k : ℝ) * x)) := by rfl
  rw [hfun]
  fun_prop

lemma value_form_case1 {n : ℕ} (hn : 1 ≤ n) (a b : ℕ → ℝ)
    (hstrict : ∀ θ : ℝ, |TPoly n a b θ| < 1) (η : ℝ) :
    ¬ (n : ℝ) * Real.sin (Real.arccos (TPoly n a b η)) < deriv (TPoly n a b) η := by
  intro hgt
  let c : ℝ := TPoly n a b η
  let γ : ℝ := Real.arccos c
  have hc_abs : |c| < 1 := by simpa [c] using hstrict η
  have hcm1 : -1 < c := (abs_lt.mp hc_abs).1
  have hc1 : c < 1 := (abs_lt.mp hc_abs).2
  have hγ0 : 0 < γ := (Real.arccos_pos).2 hc1
  have hγπ : γ < π := (Real.arccos_lt_pi).2 hcm1
  have hcosγ : Real.cos γ = c := Real.cos_arccos (le_of_lt hcm1) (le_of_lt hc1)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt hn0
  let β : ℝ := (n : ℝ) * η + γ
  let W : ℝ → ℝ := fun θ => TPoly n a b θ - Real.cos ((n : ℝ) * θ - β)
  let aw : ℕ → ℝ := fun k => a k - (if k = n then Real.cos β else 0)
  let bw : ℕ → ℝ := fun k => b k - (if k = n then Real.sin β else 0)
  let t : ℕ → ℝ := fun m => η + (γ + ((m : ℝ) - 1) * π) / (n : ℝ)
  have hgtγ : (n : ℝ) * Real.sin γ < deriv (TPoly n a b) η := by
    simpa [γ, c] using hgt
  -- W = TPoly n aw bw
  have hWTPoly : ∀ θ : ℝ, TPoly n aw bw θ = W θ := by
    intro θ
    dsimp [W, aw, bw]
    rw [TPoly_sub]
    congr 1
    exact TPoly_cos_shift n β θ
  -- derivative of the cosine part at η is n * sin γ
  have hlin : HasDerivAt (fun x : ℝ => (n : ℝ) * x - β) (n : ℝ) η := by
    simpa using (((hasDerivAt_id η).const_mul (n : ℝ)).sub_const β)
  have hG : HasDerivAt (fun x : ℝ => Real.cos ((n : ℝ) * x - β)) ((n : ℝ) * Real.sin γ) η := by
    have hraw : HasDerivAt (fun x : ℝ => Real.cos ((n : ℝ) * x - β))
        (-Real.sin ((n : ℝ) * η - β) * (n : ℝ)) η := by
      simpa [Function.comp_def] using ((Real.hasDerivAt_cos ((n : ℝ) * η - β)).comp η hlin)
    convert hraw using 1
    have hnηβ : (n : ℝ) * η - β = -γ := by dsimp [β]; ring
    rw [hnηβ]
    simp [Real.sin_neg]
    ring
  have hF : HasDerivAt (TPoly n a b) (deriv (TPoly n a b) η) η :=
    (differentiable_TPoly n a b η).hasDerivAt
  have hWder : HasDerivAt W (deriv (TPoly n a b) η - (n : ℝ) * Real.sin γ) η := by
    dsimp [W]
    exact hF.sub hG
  have hderW : deriv W η = deriv (TPoly n a b) η - (n : ℝ) * Real.sin γ := hWder.deriv
  have hderWpos : 0 < deriv W η := by
    rw [hderW]
    linarith
  -- W vanishes at η
  have hWη0 : W η = 0 := by
    dsimp [W]
    have hnηβ : (n : ℝ) * η - β = -γ := by dsimp [β]; ring
    rw [hnηβ, Real.cos_neg]
    have hcγ : Real.cos γ = TPoly n a b η := by simpa [c] using hcosγ
    rw [hcγ]
    ring
  have hWη0' : TPoly n aw bw η = 0 := by
    rw [hWTPoly η]
    exact hWη0
  have hderWTPoly : 0 < deriv (TPoly n aw bw) η := by
    have hfun : TPoly n aw bw = W := funext hWTPoly
    rw [hfun]
    exact hderWpos
  have hWnz : ∃ θ, TPoly n aw bw θ ≠ 0 := by
    by_contra hnone
    have hd0 : deriv (TPoly n aw bw) η = 0 := by
      have hzero : TPoly n aw bw = fun _ : ℝ => 0 := by
        funext x
        by_contra hx
        exact hnone ⟨x, hx⟩
      rw [hzero]
      simp
    linarith
  -- position of the sample points
  have hstep (m : ℕ) : t m < t (m + 1) := by
    have hdiff : t (m + 1) - t m = π / (n : ℝ) := by
      dsimp [t]
      field_simp [hnz]
      push_cast
      ring
    have hpi : 0 < π / (n : ℝ) := div_pos Real.pi_pos hn0
    linarith
  have hmono : ∀ m, m < 2 * n → t m < t (m + 1) := by
    intro m _
    exact hstep m
  have hhend : t (2 * n) = t 0 + 2 * π := by
    dsimp [t]
    field_simp [hnz]
    push_cast
    ring
  have ht0η : t 0 < η := by
    dsimp [t]
    have hnum : γ + ((0 : ℝ) - 1) * π < 0 := by
      have hrew : ((0 : ℝ) - 1) * π = -π := by ring
      rw [hrew]
      linarith
    have hq : (γ + ((0 : ℝ) - 1) * π) / (n : ℝ) < 0 := div_neg_of_neg_of_pos hnum hn0
    linarith
  have hηt1 : η < t 1 := by
    dsimp [t]
    have hnum : 0 < γ + ((1 : ℝ) - 1) * π := by
      have hrew : ((1 : ℝ) - 1) * π = 0 := by ring
      rw [hrew]
      linarith
    have hq : 0 < (γ + ((1 : ℝ) - 1) * π) / (n : ℝ) := div_pos hnum hn0
    linarith
  -- values of W at sample points
  have hntm (m : ℕ) : (n : ℝ) * t m - β = ((m : ℝ) - 1) * π := by
    dsimp [t, β]
    field_simp [hnz]
    ring
  have hWtm (m : ℕ) : TPoly n aw bw (t m) = TPoly n a b (t m) - Real.cos (((m : ℝ) - 1) * π) := by
    rw [hWTPoly]
    dsimp [W]
    rw [hntm m]
  have hWtm_pos (m : ℕ) (hm : Even m) : 0 < TPoly n aw bw (t m) := by
    rw [hWtm m]
    have hcosp : Real.cos (((m : ℝ) - 1) * π) = -1 := by
      rw [cos_sub_one_mul_pi m, if_pos hm]
    rw [hcosp]
    have habs : -1 < TPoly n a b (t m) := (abs_lt.mp (hstrict (t m))).1
    linarith
  have hWtm_neg (m : ℕ) (hm : Odd m) : TPoly n aw bw (t m) < 0 := by
    rw [hWtm m]
    have hcosp : Real.cos (((m : ℝ) - 1) * π) = 1 := by
      rw [cos_sub_one_mul_pi m]
      have hne : ¬ Even m := Nat.not_even_iff_odd.mpr hm
      rw [if_neg hne]
    rw [hcosp]
    have habs : TPoly n a b (t m) < 1 := (abs_lt.mp (hstrict (t m))).2
    linarith
  have hpos : 0 < TPoly n aw bw (t 0) := by
    exact hWtm_pos 0 (by simp)
  have halt : ∀ m, m < 2 * n → (TPoly n aw bw (t m)) * (TPoly n aw bw (t (m + 1))) < 0 := by
    intro m _
    by_cases hm : Even m
    · have h1 : 0 < TPoly n aw bw (t m) := hWtm_pos m hm
      have h2 : TPoly n aw bw (t (m + 1)) < 0 := by
        have hodd : Odd (m + 1) := by
          rw [Nat.odd_add_one]
          exact Nat.not_odd_iff_even.mpr hm
        exact hWtm_neg (m + 1) hodd
      exact mul_neg_of_pos_of_neg h1 h2
    · have hodd : Odd m := Nat.not_even_iff_odd.mp hm
      have h1 : TPoly n aw bw (t m) < 0 := hWtm_neg m hodd
      have h2 : 0 < TPoly n aw bw (t (m + 1)) := by
        have hev : Even (m + 1) := by
          rw [Nat.even_add_one]
          exact Nat.not_even_iff_odd.mpr hodd
        exact hWtm_pos (m + 1) hev
      exact mul_neg_of_neg_of_pos h1 h2
  exact alternation_contradiction hn hWnz hpos halt hmono hhend ht0η hηt1 hWη0' hderWTPoly

lemma strict_value_form {n : ℕ} (hn : 1 ≤ n) (a b : ℕ → ℝ)
    (hstrict : ∀ θ : ℝ, |TPoly n a b θ| < 1) (η : ℝ) :
    |deriv (TPoly n a b) η| ≤ (n : ℝ) * Real.sin (Real.arccos (TPoly n a b η)) := by
  by_contra h
  let c : ℝ := TPoly n a b η
  let d : ℝ := deriv (TPoly n a b) η
  have hgt : (n : ℝ) * Real.sin (Real.arccos c) < |d| := by
    have hh := lt_of_not_ge h
    simpa [c, d] using hh
  by_cases hdn : d < 0
  · have hdneg : d ≤ 0 := le_of_lt hdn
    have hdabs : |d| = -d := abs_of_neg hdn
    have hgt2 : (n : ℝ) * Real.sin (Real.arccos c) < -d := by
      simpa [hdabs] using hgt
    let a' : ℕ → ℝ := fun k => - a k
    let b' : ℕ → ℝ := fun k => - b k
    have hstrict' : ∀ θ : ℝ, |TPoly n a' b' θ| < 1 := by
      intro θ
      simpa [a', b', TPoly_neg] using hstrict θ
    have hc1 := value_form_case1 (n := n) hn a' b' hstrict' η
    have hderneg : deriv (TPoly n a' b') η = -d := by
      have hfun : TPoly n a' b' = fun x : ℝ => - TPoly n a b x := by
        funext x
        exact TPoly_neg n a b x
      rw [hfun]
      simp [d]
    have hsin : Real.sin (Real.arccos (TPoly n a' b' η)) = Real.sin (Real.arccos c) := by
      have hU : TPoly n a' b' η = -c := by
        dsimp [a', b']
        simpa [c] using TPoly_neg n a b η
      rw [hU]
      rw [Real.sin_arccos, Real.sin_arccos]
      congr 1
      ring
    have hc1' : ¬ (n : ℝ) * Real.sin (Real.arccos c) < -d := by
      simpa [hsin, hderneg] using hc1
    exact hc1' hgt2
  · have hdnonneg : 0 ≤ d := le_of_not_gt hdn
    have hdabs : |d| = d := abs_of_nonneg hdnonneg
    have hgt2 : (n : ℝ) * Real.sin (Real.arccos c) < d := by
      simpa [hdabs] using hgt
    have hc1 := value_form_case1 hn a b hstrict η
    exact hc1 (by simpa [c, d] using hgt2)

end MarkovSValue

end Submission
