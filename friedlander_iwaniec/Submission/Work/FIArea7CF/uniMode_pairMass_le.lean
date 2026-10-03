/-
# `Submission.Work.FIArea7.uniMode_pairMass_le`

The weighted non-coprime pair mass of the coprimality-guard removal
(`Work.FIArea7.uniMode_pairMass`, defined in `UniPairMassDefs`) is estimated by
`≪ (Pz⁻¹ + X⁻¹)N²log⁵N`.

The mechanism is the one of *FI* §17 ("trivial estimation using (5.8)"): a pair of the support that
is not coprime shares a Gaussian prime `π`, and (5.8) (`NoSmallPrimes`) says `gnorm π > Pz`; the
`π`-sublattice of the box is smaller by `√(gnorm π)`, so the two-sided density of the non-coprime
pairs carries the saving `Pz⁻¹`, while the congruence `4be ∣ |Δ|` is counted by the fibre bound
`card_gBox_filter_dvd_absDelta` (via `card_piDvd_filter_dvd_absDelta_le`).

The structural inputs are separate lemmas:

* `uniMode_pairInner_le_sum_pairPi` — covering the non-coprime pairs by the common prime;
* `pairPi_le_massW_rhoPi` — the per-`π` fibre bound;
* `sum_massW_le` — `∑_π massW(π) ≤ (∑‖β‖²)·4log(N+2)`, the only place where (5.8) is used;
* `sum_be_bound` — the `(b,e)`-summation;
* `uniMode_pairMass_le_of_pieces` — the assembly, and `uniMode_pairMass_le` on top of it.
-/
import Mathlib
import Submission.Work.FIArea7.UniPairMassDefs
import Submission.Work.FIArea7.PiPairDefs
import Submission.Work.FIArea7.PiPairAux
import Submission.Work.FIArea7.PiPairSum
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.isCoprime_coords_of_squarefree_gnorm
import Submission.Work.FIArea7.pairTheta_le
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7CF.card_piDvd_filter_dvd_absDelta_le
import Submission.Work.FIArea7CF.uniMode_pairInner_le_sum_pairPi
import Submission.Work.FIArea7CF.pairPi_le_massW_rhoPi
import Submission.Work.FIArea7.SumMassDefs
import Submission.Work.FIArea7.params_theta_le_quarter
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul
import Submission.Work.FITop4.Defs6

set_option maxHeartbeats 2000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) :=
    le_of_lt ((Real.lt_log_iff_exp_lt hxpos).mpr (lt_of_lt_of_le Real.exp_one_lt_three hx3))
  have hA' : (0 : ℝ) ≤ Pa.A' := by linarith [Pa.hA, Pa.hA']
  rw [Pa.hθ]
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by linarith)

lemma radN_le (Pa : Work.FITop.Params) :
    (Work.FITop.radN Pa : ℝ) ≤ 2 * Real.sqrt Pa.N + 1 := by
  have hN : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have h4N : (0 : ℝ) < 4 * Pa.N := by linarith
  have h1 : (Work.FITop.radN Pa : ℝ) < Real.sqrt (4 * Pa.N) + 1 := by
    rw [Work.FITop.radN]
    have := Nat.ceil_lt_add_one (le_of_lt (Real.sqrt_pos_of_pos h4N))
    simpa using this
  have h3 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4 : ℝ) * Pa.N = 2 ^ 2 * Pa.N by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2) _, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  linarith

/-- `uniB Pa ≤ 6N`. -/
lemma uniB_le (Pa : Work.FITop.Params) : (uniB Pa : ℝ) ≤ 6 * (Pa.N : ℝ) := by
  have hθ := theta_le_one Pa
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4 := by
    have h1 : (0 : ℝ) < Pa.θ := Pa.hθ0
    have h2 : (0 : ℝ) < (Pa.N : ℝ) := hNpos
    have h3 : (0 : ℝ) < 1 + Pa.θ := by linarith
    have h4 : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have hx : 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4 ≤ 4 * (Pa.N : ℝ) := by
    have hθ0' : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
    have hθ1 : 1 + Pa.θ ≤ 2 := by linarith
    have h2 : Pa.θ * (1 + Pa.θ) ≤ 2 := by
      calc Pa.θ * (1 + Pa.θ) ≤ 1 * 2 := mul_le_mul hθ hθ1 (by linarith) (by norm_num)
        _ = 2 := by norm_num
    have h3 : Real.pi < 4 := Real.pi_lt_four
    have h4 : 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4
        = (Real.pi / 2) * (Pa.θ * (1 + Pa.θ)) * Pa.N := by ring
    rw [h4]
    calc (Real.pi / 2) * (Pa.θ * (1 + Pa.θ)) * Pa.N
        ≤ (Real.pi / 2) * 2 * Pa.N := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hNpos)
          exact mul_le_mul_of_nonneg_left h2 (by linarith [Real.pi_pos])
      _ ≤ 4 * Pa.N := by
          have h5 : (Real.pi / 2) * 2 = Real.pi := by ring
          rw [h5]
          exact mul_le_mul_of_nonneg_right (le_of_lt h3) (le_of_lt hNpos)
  have hceil : ((Nat.ceil (2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4) : ℕ) : ℝ)
      < 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4 + 1 := Nat.ceil_lt_add_one hx0
  rw [uniB]
  push_cast
  linarith

/-- **The weighted non-coprime pair mass is `≪ (Pz⁻¹ + X⁻¹)N²log⁵N`.** -/
theorem uniMode_pairMass_le_of_pieces
    (H5 : ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (b e : ℕ), 1 ≤ b → 1 ≤ e →
      Work.FIArea7.uniMode_pairInner Pa b e β
        ≤ ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π)
    (H6 : ∀ (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (π : GaussianInt),
      1 ≤ b → 1 ≤ e → π ∈ Work.FIArea7.bigPi Pa (4 * b * e) →
      Work.FIArea7.pairPi Pa b e β π
        ≤ Work.FIArea7.massW Pa β π (4 * b * e)
            * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
                * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)))
    (H7 : ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (m : ℕ),
      ∑ π ∈ Work.FIArea7.bigPi Pa m, Work.FIArea7.massW Pa β π m
        ≤ (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
            * (4 * Real.log (Pa.N + 2))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (X : ℕ),
        1 ≤ X → (X : ℝ) ^ 9 ≤ Pa.N →
        ((((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ)
            ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)) →
        ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
            ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3) →
        Work.FIArea7.uniMode_pairMass Pa X β
          ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * (Real.log (Pa.N + 2)) ^ 5 := by
  refine ⟨100000000, by norm_num, ?_⟩
  intro Pa φ z0 β hβ X hX1 hX9 hcard hmass
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hNnn : (0 : ℝ) ≤ (Pa.N : ℝ) := le_of_lt hNpos
  set L : ℝ := Real.log (Pa.N + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h3 : (3 : ℝ) ≤ Pa.N + 2 := by linarith
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    exact le_trans (le_of_lt hlog3) (Real.log_le_log (by norm_num) h3)
  have hLpos : (0 : ℝ) < L := by linarith
  -- **1. the `L²`-mass of the coefficient**
  have hmass' : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
      ≤ 3000 * (Pa.N : ℝ) * L ^ 3 := by
    have h := hmass
    have hlog : Real.log (2 + (Pa.N : ℝ)) = L := by rw [hLdef]; ring_nf
    rw [hlog] at h
    have hθ := theta_le_one Pa
    have hsqrt : Real.sqrt (Pa.N : ℝ) ≤ (Pa.N : ℝ) := by
      nlinarith [Real.sq_sqrt hNnn, Real.sqrt_nonneg (Pa.N : ℝ), hN1]
    have hkey : Pa.θ * (Pa.N : ℝ) + Real.sqrt (Pa.N : ℝ) + 1 ≤ 3 * (Pa.N : ℝ) := by
      have h1 : Pa.θ * (Pa.N : ℝ) ≤ (Pa.N : ℝ) := by nlinarith
      linarith
    calc (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
        ≤ 1000 * (Pa.θ * (Pa.N : ℝ) + Real.sqrt (Pa.N : ℝ) + 1) * L ^ 3 := h
      _ ≤ 1000 * (3 * (Pa.N : ℝ)) * L ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by norm_num))
            (by positivity)
      _ = 3000 * (Pa.N : ℝ) * L ^ 3 := by ring
  -- **2. the uniform `ρ`**
  set rho : ℝ := (rhoBar Pa : ℝ) with hrhodef
  have hrho0 : 0 ≤ rho := by positivity
  have hPzR : (0 : ℝ) < (Pa.Pz : ℝ) := by exact_mod_cast Pz_pos Pa
  have hPz1 : (1 : ℝ) ≤ (Pa.Pz : ℝ) := by
    exact_mod_cast (by have := Pa.hP2; omega : 1 ≤ Pa.Pz)
  have hrho_le : rho ≤ 12 * Real.sqrt (Pa.N / Pa.Pz) + 1 := by
    have hR : (Work.FITop.radN Pa : ℝ) ≤ 2 * Real.sqrt (Pa.N : ℝ) + 1 := radN_le Pa
    have hfl : ((Nat.floor ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)) : ℕ) : ℝ)
        ≤ (Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ) := by
      apply Nat.floor_le
      have hR0 : (0 : ℝ) ≤ (Work.FITop.radN Pa : ℝ) := by
        rw [Work.FITop.radN]; positivity
      positivity
    have hsN1 : (1 : ℝ) ≤ Real.sqrt (Pa.N : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
    have hR3 : (Work.FITop.radN Pa : ℝ) ≤ 3 * Real.sqrt (Pa.N : ℝ) := by linarith
    have hs2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hspz1 : (1 : ℝ) ≤ Real.sqrt (Pa.Pz : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hPz1
    have hsqrtdiv : Real.sqrt (Pa.N : ℝ) / Real.sqrt (Pa.Pz : ℝ) = Real.sqrt (Pa.N / Pa.Pz) :=
      (Real.sqrt_div hNnn _).symm
    have hx : (Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)
        ≤ 6 * Real.sqrt (Pa.N / Pa.Pz) := by
      have h1 : (Work.FITop.radN Pa : ℝ) * Real.sqrt 2 ≤ (3 * Real.sqrt (Pa.N : ℝ)) * 2 :=
        mul_le_mul hR3 hs2 (Real.sqrt_nonneg 2) (by positivity)
      have h2 : (6 * (Real.sqrt (Pa.N : ℝ) / Real.sqrt (Pa.Pz : ℝ))) * Real.sqrt (Pa.Pz : ℝ)
          = 6 * Real.sqrt (Pa.N : ℝ) := by
        field_simp
      rw [← hsqrtdiv, div_le_iff₀ (Real.sqrt_pos_of_pos hPzR), h2]
      linarith
    calc rho = 2 * ((Nat.floor ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2
            / Real.sqrt (Pa.Pz : ℝ)) : ℕ) : ℝ) + 1 := by
          rw [hrhodef, rhoBar]; push_cast; ring
      _ ≤ 2 * ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)) + 1 := by
          linarith [hfl]
      _ ≤ 2 * (6 * Real.sqrt (Pa.N / Pa.Pz)) + 1 := by linarith [hx]
      _ = 12 * Real.sqrt (Pa.N / Pa.Pz) + 1 := by ring
  have hrho_sq : rho ^ 2 ≤ 200 * (Pa.N / Pa.Pz + 1) := by
    have hu0 : (0 : ℝ) ≤ Real.sqrt (Pa.N / Pa.Pz) := Real.sqrt_nonneg _
    have husq : (Real.sqrt (Pa.N / Pa.Pz)) ^ 2 = Pa.N / Pa.Pz :=
      Real.sq_sqrt (by positivity)
    have h1 : rho ^ 2 ≤ (12 * Real.sqrt (Pa.N / Pa.Pz) + 1) ^ 2 :=
      pow_le_pow_left₀ hrho0 hrho_le 2
    nlinarith [h1, hu0, husq]
  -- **3. the `(b,e)`-summation**
  have hsum := sum_be_bound (uniB Pa) X rho hrho0
  -- **4. the logarithms**
  have hlogX : 1 + Real.log X ≤ 2 * L := by
    have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
    have hX9' : (X : ℝ) ^ 9 ≤ (Pa.N : ℝ) := hX9
    have hXleN : (X : ℝ) ≤ (Pa.N : ℝ) := by
      have h1 : (X : ℝ) ≤ (X : ℝ) ^ 9 := by
        simpa using pow_le_pow_right₀ hX1R (by norm_num : (1 : ℕ) ≤ 9)
      linarith
    have hlogN : Real.log (X : ℝ) ≤ Real.log (Pa.N : ℝ) :=
      Real.log_le_log (by linarith) hXleN
    have hlogN2 : Real.log (Pa.N : ℝ) ≤ Real.log (Pa.N + 2) :=
      Real.log_le_log hNpos (by linarith)
    have hlogX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1R
    rw [hLdef]
    linarith
  have hlogB : 1 + Real.log (uniB Pa) ≤ 3 * L := by
    have hub : (uniB Pa : ℝ) ≤ 6 * (Pa.N : ℝ) := uniB_le Pa
    have hubpos : (0 : ℝ) < (uniB Pa : ℝ) := by
      have : 0 < uniB Pa := by
        rw [uniB]; omega
      exact_mod_cast this
    have hlogB' : Real.log (uniB Pa) ≤ Real.log (6 * (Pa.N : ℝ)) :=
      Real.log_le_log hubpos hub
    have h6N : Real.log (6 * (Pa.N : ℝ)) ≤ 2 * Real.log (Pa.N + 2) := by
      have h6 : (6 * (Pa.N : ℝ)) ≤ (Pa.N + 2) ^ 2 := by nlinarith
      have h := Real.log_le_log (by positivity) h6
      rw [Real.log_pow] at h
      norm_num at h
      exact h
    rw [hLdef]
    linarith
  -- **5. the chain of estimates**
  have hlogX0 : 0 ≤ 1 + Real.log X := by
    have : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX1)
    linarith
  have hlogB0 : 0 ≤ 1 + Real.log (uniB Pa) := by
    have : 0 ≤ Real.log (uniB Pa) := by
      apply Real.log_nonneg
      have : 0 < uniB Pa := by rw [uniB]; omega
      exact_mod_cast (by omega : 1 ≤ uniB Pa)
    linarith
  have stepA : Work.FIArea7.uniMode_pairMass Pa X β
      ≤ ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
          (1 / (b : ℝ)) * ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
            Work.FIArea7.pairPi Pa b e β π := by
    rw [Work.FIArea7.uniMode_pairMass]
    refine Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun e he => ?_))
    exact mul_le_mul_of_nonneg_left
      (H5 hβ b e (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp he).1) (by positivity)
  have stepB : ∀ b ∈ Finset.Icc 1 (uniB Pa), ∀ e ∈ Finset.Icc 1 X,
      (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π)
        ≤ (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.massW Pa β π (4 * b * e))
            * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1)) := by
    intro b hb e he
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
    have hc : (0 : ℝ) < 4 * (b : ℝ) * (e : ℝ) := by positivity
    calc (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π)
        ≤ ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.massW Pa β π (4 * b * e)
            * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
                * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)) :=
          Finset.sum_le_sum (fun π hπ => H6 Pa b e β π hb1 he1 hπ)
      _ ≤ ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.massW Pa β π (4 * b * e)
            * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1)) := by
          refine Finset.sum_le_sum (fun π hπ => ?_)
          apply mul_le_mul_of_nonneg_left _
            (by rw [Work.FIArea7.massW]; positivity)
          have hρ : (Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) ≤ rho := by
            rw [hrhodef]; exact_mod_cast rhoPi_le_rhoBar hπ
          have hρ0 : (0 : ℝ) ≤ (Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) := by positivity
          apply mul_le_mul hρ _ (by positivity) (by linarith)
          apply add_le_add _ le_rfl
          exact div_le_div_of_nonneg_right hρ (le_of_lt hc)
      _ = (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.massW Pa β π (4 * b * e))
            * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1)) := by
          rw [Finset.sum_mul]
  have stepC : ∀ b ∈ Finset.Icc 1 (uniB Pa), ∀ e ∈ Finset.Icc 1 X,
      (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.massW Pa β π (4 * b * e))
            * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1))
        ≤ ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) * (4 * L))
            * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1)) := by
    intro b hb e he
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
    have hfac : 0 ≤ rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1) := by
      have : 0 ≤ rho / (4 * (b : ℝ) * (e : ℝ)) := div_nonneg hrho0 (by positivity)
      positivity
    apply mul_le_mul_of_nonneg_right _ hfac
    have h := H7 hβ (4 * b * e)
    have hlog : Real.log (Pa.N + 2) = L := hLdef
    linarith [h]
  have hmain : Work.FIArea7.uniMode_pairMass Pa X β
      ≤ (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) * (4 * L)
          * (rho ^ 2 * (1 + Real.log X) / 2 + rho * (1 + Real.log (uniB Pa)) * X) := by
    have s2 : ∀ b ∈ Finset.Icc 1 (uniB Pa), ∀ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π
          ≤ (1 / (b : ℝ)) * (((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
              * (4 * L)) * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1))) := by
      intro b hb e he
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_trans (stepB b hb e he) (stepC b hb e he)
    have hfactor : (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
          (1 / (b : ℝ)) * (((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
            * (4 * L)) * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1))))
        = ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) * (4 * L))
            * (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
                (1 / (b : ℝ)) * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      ring
    calc Work.FIArea7.uniMode_pairMass Pa X β
        ≤ ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (1 / (b : ℝ)) * ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
              Work.FIArea7.pairPi Pa b e β π := stepA
      _ ≤ ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
            (1 / (b : ℝ)) * (((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
              * (4 * L)) * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1))) :=
          Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun e he => s2 b hb e he))
      _ = ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) * (4 * L))
            * (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
                (1 / (b : ℝ)) * (rho * (rho / (4 * (b : ℝ) * (e : ℝ)) + 1))) := hfactor
      _ ≤ ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) * (4 * L))
            * (rho ^ 2 * (1 + Real.log X) / 2 + rho * (1 + Real.log (uniB Pa)) * X) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)

  -- **6. the final numerical comparison**
  have hub : (0 : ℝ) ≤ (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) := by positivity
  have h4L : (0 : ℝ) ≤ 4 * L := by linarith
  have h1 : rho ^ 2 * (1 + Real.log X) / 2 ≤ 200 * (Pa.N / Pa.Pz + 1) * L := by
    have h := mul_le_mul hrho_sq hlogX hlogX0 (by positivity)
    have h2L : 200 * (Pa.N / Pa.Pz + 1) * (2 * L) / 2 = 200 * (Pa.N / Pa.Pz + 1) * L := by ring
    linarith [h, h2L]
  have h2 : rho * (1 + Real.log (uniB Pa)) * X ≤ (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X := by
    have h3 : Real.sqrt (Pa.N / Pa.Pz) ≤ Real.sqrt (Pa.N : ℝ) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ hPzR]; nlinarith [hNpos]
    have hb : rho ≤ 12 * Real.sqrt (Pa.N) + 1 := by linarith [hrho_le, h3]
    have hb0 : (0 : ℝ) ≤ 12 * Real.sqrt (Pa.N : ℝ) + 1 := by positivity
    have hInner : rho * (1 + Real.log (uniB Pa)) ≤ (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) :=
      mul_le_mul hb hlogB hlogB0 hb0
    have hX0 : (0 : ℝ) ≤ X := by positivity
    exact mul_le_mul_of_nonneg_right hInner hX0
  have hstep : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) * (4 * L)
        * (rho ^ 2 * (1 + Real.log X) / 2 + rho * (1 + Real.log (uniB Pa)) * X)
      ≤ (3000 * (Pa.N : ℝ) * L ^ 3) * (4 * L)
        * (200 * (Pa.N / Pa.Pz + 1) * L + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X) := by
    have hsum1 : rho ^ 2 * (1 + Real.log X) / 2 + rho * (1 + Real.log (uniB Pa)) * X
        ≤ 200 * (Pa.N / Pa.Pz + 1) * L + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X :=
      add_le_add h1 h2
    exact mul_le_mul (mul_le_mul hmass' le_rfl h4L (by positivity)) hsum1
      (by positivity) (by positivity)
  have hid : (3000 * (Pa.N : ℝ) * L ^ 3) * (4 * L)
        * (200 * (Pa.N / Pa.Pz + 1) * L + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X)
      = 2400000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 / (Pa.Pz : ℝ))
        + 2400000 * ((Pa.N : ℝ) * L ^ 5) + 36000 * ((Pa.N : ℝ) * L ^ 5 * X)
        + 432000 * ((Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * X) := by
    field_simp
    ring
  have hkey : Work.FIArea7.uniMode_pairMass Pa X β
      ≤ 2400000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 / (Pa.Pz : ℝ))
        + 2400000 * ((Pa.N : ℝ) * L ^ 5) + 36000 * ((Pa.N : ℝ) * L ^ 5 * X)
        + 432000 * ((Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * X) := by
    rw [← hid]
    exact le_trans hmain hstep
  -- the four comparisons
  have hXsq : (X : ℝ) ^ 2 ≤ Real.sqrt (Pa.N : ℝ) := by
    have hX4 : (X : ℝ) ^ 4 ≤ (Pa.N : ℝ) := by
      have hX1' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
      have h1 : (X : ℝ) ^ 4 ≤ (X : ℝ) ^ 9 := pow_le_pow_right₀ hX1' (by norm_num)
      linarith
    have hsq : (Real.sqrt (Pa.N : ℝ)) ^ 2 = (Pa.N : ℝ) := Real.sq_sqrt hNnn
    have hs0 : (0 : ℝ) ≤ Real.sqrt (Pa.N : ℝ) := Real.sqrt_nonneg _
    have hX20 : (0 : ℝ) ≤ (X : ℝ) ^ 2 := by positivity
    nlinarith [hX4, hsq, hs0, hX20]
  have hXleN : (X : ℝ) ≤ (Pa.N : ℝ) := by
    have hX1' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
    have h1 : (X : ℝ) ≤ (X : ℝ) ^ 9 := by
      simpa using pow_le_pow_right₀ hX1' (by norm_num : (1 : ℕ) ≤ 9)
    linarith
  have hXinv : (0 : ℝ) < (X : ℝ)⁻¹ := by
    apply inv_pos.mpr; exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hX1)
  have hNin : (1 : ℝ) ≤ (Pa.N : ℝ) := hN1
  have c1 : 2400000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 / (Pa.Pz : ℝ))
      ≤ 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (Pa.Pz : ℝ)⁻¹) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hNX : (Pa.N : ℝ) * L ^ 5 ≤ (Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹ := by
    rw [show (Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹ = (Pa.N : ℝ) ^ 2 * L ^ 5 / X by
      rw [div_eq_mul_inv]]
    rw [le_div_iff₀ (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hX1))]
    calc (Pa.N : ℝ) * L ^ 5 * X ≤ (Pa.N : ℝ) * L ^ 5 * (Pa.N : ℝ) :=
          mul_le_mul_of_nonneg_left hXleN (by positivity)
      _ = (Pa.N : ℝ) ^ 2 * L ^ 5 := by ring
  have c2 : 2400000 * ((Pa.N : ℝ) * L ^ 5)
      ≤ 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹) :=
    le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2400000:ℝ) ≤ 30000000)
      (by positivity)) (mul_le_mul_of_nonneg_left hNX (by norm_num))
  have hXsqN : (X : ℝ) ^ 2 ≤ (Pa.N : ℝ) := by
    nlinarith [hXsq, Real.sq_sqrt hNnn, Real.sqrt_nonneg (Pa.N : ℝ), hN1]
  have hXN : (Pa.N : ℝ) * L ^ 5 * X ≤ (Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹ := by
    rw [show (Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹ = (Pa.N : ℝ) ^ 2 * L ^ 5 / X by
      rw [div_eq_mul_inv]]
    rw [le_div_iff₀ (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hX1))]
    calc (Pa.N : ℝ) * L ^ 5 * X * X = (Pa.N : ℝ) * L ^ 5 * (X ^ 2) := by ring
      _ ≤ (Pa.N : ℝ) * L ^ 5 * (Pa.N : ℝ) :=
          mul_le_mul_of_nonneg_left hXsqN (by positivity)
      _ = (Pa.N : ℝ) ^ 2 * L ^ 5 := by ring
  have c3 : 36000 * ((Pa.N : ℝ) * L ^ 5 * X)
      ≤ 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹) :=
    le_trans (mul_le_mul_of_nonneg_right (by norm_num : (36000:ℝ) ≤ 30000000)
      (by positivity)) (mul_le_mul_of_nonneg_left hXN (by norm_num))
  have hXN2 : (Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * X
      ≤ (Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹ := by
    rw [show (Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹ = (Pa.N : ℝ) ^ 2 * L ^ 5 / X by
      rw [div_eq_mul_inv]]
    rw [le_div_iff₀ (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hX1))]
    have hs0 : (0 : ℝ) ≤ Real.sqrt (Pa.N : ℝ) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) = (Pa.N : ℝ) := by
      rw [← sq]; exact Real.sq_sqrt hNnn
    calc (Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * X * X
        = (Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * (X ^ 2) := by ring
      _ ≤ (Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * Real.sqrt (Pa.N : ℝ) :=
          mul_le_mul_of_nonneg_left hXsq (by positivity)
      _ = (Pa.N : ℝ) * (Real.sqrt (Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ)) * L ^ 5 := by ring
      _ = (Pa.N : ℝ) ^ 2 * L ^ 5 := by rw [hsq]; ring
  have c4 : 432000 * ((Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * X)
      ≤ 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹) :=
    le_trans (mul_le_mul_of_nonneg_right (by norm_num : (432000:ℝ) ≤ 30000000)
      (by positivity)) (mul_le_mul_of_nonneg_left hXN2 (by norm_num))
  calc Work.FIArea7.uniMode_pairMass Pa X β
      ≤ 2400000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 / (Pa.Pz : ℝ)) + 2400000 * ((Pa.N : ℝ) * L ^ 5)
        + 36000 * ((Pa.N : ℝ) * L ^ 5 * X)
        + 432000 * ((Pa.N : ℝ) * Real.sqrt (Pa.N : ℝ) * L ^ 5 * X) := hkey
    _ ≤ 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (Pa.Pz : ℝ)⁻¹)
        + 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹)
        + 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹)
        + 30000000 * ((Pa.N : ℝ) ^ 2 * L ^ 5 * (X : ℝ)⁻¹) := by linarith [c1, c2, c3, c4]
    _ ≤ 100000000 * (((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * ((Pa.N : ℝ) ^ 2 * L ^ 5)) := by
        nlinarith [show (0:ℝ) ≤ (Pa.N : ℝ)^2 * L^5 * (Pa.Pz:ℝ)⁻¹ by positivity,
          show (0:ℝ) ≤ (Pa.N : ℝ)^2 * L^5 * (X:ℝ)⁻¹ by positivity]
    _ = 100000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * (Real.log (Pa.N + 2)) ^ 5 := by
        rw [← hLdef]; ring

end

end Work.FIArea7