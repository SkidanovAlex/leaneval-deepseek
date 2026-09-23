import Mathlib
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz
import Submission.Commons.Analysis.ODE.eqOn_of_hasDerivAt_of_locallyLipschitz_of_mem_Ioo

namespace Commons.Analysis.ODE

open Set Metric Filter
open scoped Topology

theorem flow_semigroup_of_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {O : Set E} {α : E → ℝ → E} {ρ : ℝ} (hρ : 0 < ρ)
    (h0 : ∀ p ∈ O, α p 0 = p)
    (hode : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ → HasDerivAt (α p) (f (α p t)) t)
    (hloc : ∀ p ∈ O, ∀ t : ℝ, |t| ≤ ρ →
      ∃ K : NNReal, ∃ U ∈ nhds (α p t), LipschitzOnWith K f U)
    {p : E} (hp : p ∈ O) {s t : ℝ} (hps : α p s ∈ O)
    (hs : |s| ≤ ρ) (ht : |t| ≤ ρ) (hst : |s + t| ≤ ρ) :
    α (α p s) t = α p (s + t) := by
  set u : ℝ → E := fun r => α (α p s) r with hu
  set v : ℝ → E := fun r => α p (s + r) with hv
  have h0eq : u 0 = v 0 := by
    simp only [hu, hv]
    rw [h0 (α p s) hps, add_zero]
  rcases le_total (0 : ℝ) t with ht0 | ht0
  · -- Case `0 ≤ t`: uniqueness on `Icc 0 t` with the initial condition at `0`.
    have htle : t ≤ ρ := (abs_le.mp ht).2
    have huode : ∀ r ∈ Icc (0 : ℝ) t, HasDerivAt u (f (u r)) r := by
      intro r hr
      have hrρ : |r| ≤ ρ := by
        rw [abs_of_nonneg hr.1]; linarith [hr.2, htle]
      have h : HasDerivAt (α (α p s)) (f (α (α p s) r)) r := hode (α p s) hps r hrρ
      simpa only [hu] using h
    have hvode : ∀ r ∈ Icc (0 : ℝ) t, HasDerivAt v (f (v r)) r := by
      intro r hr
      have hsrr : |s + r| ≤ ρ := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · linarith [neg_abs_le s, hs, hr.1]
        · linarith [le_abs_self (s + t), hst, hr.2]
      have h : HasDerivAt (fun x : ℝ => α p (s + x)) (f (α p (s + r))) r :=
        (hode p hp (s + r) hsrr).comp_const_add s r
      simpa only [hv] using h
    have hlocode : ∀ r ∈ Icc (0 : ℝ) t, ∃ K : NNReal, ∃ U ∈ nhds (u r), LipschitzOnWith K f U := by
      intro r hr
      have hrρ : |r| ≤ ρ := by
        rw [abs_of_nonneg hr.1]; linarith [hr.2, htle]
      have h := hloc (α p s) hps r hrρ
      simpa only [hu] using h
    have hEq := eqOn_of_hasDerivAt_of_locallyLipschitz (f := f) (u := u) (v := v)
      (a := 0) (b := t) ht0 huode hvode hlocode h0eq
    have hthis : u t = v t := hEq ⟨ht0, le_rfl⟩
    simpa only [hu, hv] using hthis
  · -- Case `t < 0`: uniqueness on `Icc t 0` with the initial condition at `0`.
    have htle : t ≤ 0 := ht0
    have htabs : |t| = -t := abs_of_nonpos ht0
    have huode : ∀ r ∈ Icc t (0 : ℝ), HasDerivAt u (f (u r)) r := by
      intro r hr
      have hrρ : |r| ≤ ρ := by
        rw [abs_of_nonpos hr.2]
        linarith [hr.1, htabs ▸ ht]
      have h : HasDerivAt (α (α p s)) (f (α (α p s) r)) r := hode (α p s) hps r hrρ
      simpa only [hu] using h
    have hvode : ∀ r ∈ Icc t (0 : ℝ), HasDerivAt v (f (v r)) r := by
      intro r hr
      have hsrr : |s + r| ≤ ρ := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · linarith [neg_abs_le (s + t), hst, hr.1]
        · linarith [le_abs_self s, hs, hr.2]
      have h : HasDerivAt (fun x : ℝ => α p (s + x)) (f (α p (s + r))) r :=
        (hode p hp (s + r) hsrr).comp_const_add s r
      simpa only [hv] using h
    have hlocode : ∀ r ∈ Icc t (0 : ℝ), ∃ K : NNReal, ∃ U ∈ nhds (u r), LipschitzOnWith K f U := by
      intro r hr
      have hrρ : |r| ≤ ρ := by
        rw [abs_of_nonpos hr.2]
        linarith [hr.1, htabs ▸ ht]
      have h := hloc (α p s) hps r hrρ
      simpa only [hu] using h
    have hEq := eqOn_of_hasDerivAt_of_locallyLipschitz_right (f := f) (u := u) (v := v)
      (a := t) (b := 0) htle huode hvode hlocode h0eq
    have hthis : u t = v t := hEq ⟨le_rfl, htle⟩
    simpa only [hu, hv] using hthis

end Commons.Analysis.ODE
