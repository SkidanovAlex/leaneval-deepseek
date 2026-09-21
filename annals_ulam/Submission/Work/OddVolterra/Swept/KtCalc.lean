import Submission.Work.OddVolterra.SweptDefs
import Submission.Work.OddVolterra.Swept.Pder
import Submission.Work.OddVolterra.Swept.rpow_ident
import Submission.Work.OddVolterra.Swept.KsCalc

/-!
# Calculus of the shifted family `kt`

The shifted kernel `kt A p j u τ = ks A p j u (u + τ)` (the Leibniz expansion in the variable
`τ = σ - u`) satisfies the same differentiability facts: its `u`- and `τ`-partial derivatives are
`ks A p (j+1) u (u+τ) + tkt A p j u τ` and `tkt A p j u τ`, and it tends to `0` as `τ → 0⁺`
when `j < p`.
-/

noncomputable section

namespace Work.OddVolterra.Swept

open Work.OddVolterra
open Filter
open scoped Topology

variable {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}

theorem hasFDerivAt_uncurried_kt (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u τ : ℝ}
    (huτ : (u, u + τ) ∈ O) (hτ : 0 < τ) :
    HasFDerivAt (fun q : ℝ × ℝ => kt A p j q.1 q.2)
      ((ks A p (j + 1) u (u + τ) + tkt A p j u τ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u τ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, τ) := by
  have hσ : u < u + τ := by linarith
  have hK := hasFDerivAt_uncurried_ks (p := p) (j := j) hO hA huτ hσ
  have hφ : HasFDerivAt (fun q : ℝ × ℝ => (q.1, q.1 + q.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)) (u, τ) :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)).hasFDerivAt
  have hcomp := hK.comp (u, τ) hφ
  have hfun : ((fun q : ℝ × ℝ => ks A p j q.1 q.2) ∘ fun q : ℝ × ℝ => (q.1, q.1 + q.2))
      = fun q : ℝ × ℝ => kt A p j q.1 q.2 := by
    funext q
    simp only [Function.comp_apply]
    rw [kt_eq_ks]
  rw [hfun] at hcomp
  refine hcomp.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp [smul_eq_mul, mul_comm]
  ring

theorem hasDerivAt_kt_fst (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u τ : ℝ}
    (huτ : (u, u + τ) ∈ O) (hτ : 0 < τ) :
    HasDerivAt (fun x : ℝ => kt A p j x τ) (ks A p (j + 1) u (u + τ) + tkt A p j u τ) u := by
  have hK := hasFDerivAt_uncurried_kt (p := p) (j := j) hO hA huτ hτ
  have hcurve : HasDerivAt (fun x : ℝ => (x, τ)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u τ)
  have hcomp := hK.comp_hasDerivAt u hcurve
  have hcomp' : HasDerivAt (fun x : ℝ => kt A p j x τ)
      (((ks A p (j + 1) u (u + τ) + tkt A p j u τ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u τ) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hcomp
  simpa using hcomp'

theorem hasDerivAt_kt_snd (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u τ : ℝ}
    (huτ : (u, u + τ) ∈ O) (hτ : 0 < τ) :
    HasDerivAt (fun y : ℝ => kt A p j u y) (tkt A p j u τ) τ := by
  have hK := hasFDerivAt_uncurried_kt (p := p) (j := j) hO hA huτ hτ
  have hcurve : HasDerivAt (fun y : ℝ => (u, y)) ((0:ℝ),(1:ℝ)) τ :=
    (hasDerivAt_const τ u).prodMk (hasDerivAt_id τ)
  have hcomp := hK.comp_hasDerivAt τ hcurve
  have hcomp' : HasDerivAt (fun y : ℝ => kt A p j u y)
      (((ks A p (j + 1) u (u + τ) + tkt A p j u τ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u τ) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((0:ℝ),(1:ℝ))) τ := by
    simpa [Function.comp_def] using hcomp
  simpa using hcomp'

/-- The shifted kernel tends to `0` at `τ = 0⁺` when `j < p`. -/
theorem tendsto_kt_zero (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u : ℝ}
    (hjp : (j : ℝ) < p) (hu : (u, u) ∈ O) :
    Tendsto (fun τ : ℝ => kt A p j u τ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpos : ∀ i ∈ Finset.range (j + 1), 0 < p - i := by
    intro i hi
    have hi' : (i : ℝ) ≤ j := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    linarith
  have hterm : ∀ i ∈ Finset.range (j + 1),
      Tendsto (fun τ : ℝ => lcoef j i p * τ ^ (p - i) * pder A (j - i) u (u + τ))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
    intro i hi
    have h1 : Tendsto (fun τ : ℝ => τ ^ (p - i)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
      have hc := Real.continuousAt_rpow_const (0:ℝ) (p - i) (Or.inr (le_of_lt (hpos i hi)))
      have ht : Tendsto (fun τ : ℝ => τ ^ (p - i)) (𝓝 (0:ℝ)) (𝓝 (0 ^ (p - i))) := hc
      rw [Real.zero_rpow (ne_of_gt (hpos i hi))] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun τ : ℝ => pder A (j - i) u (u + τ)) (𝓝[>] (0:ℝ))
        (𝓝 (pder A (j - i) u u)) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => pder A (j - i) q.1 q.2) (u, u) :=
        ((contDiffOn_uncurried_pder hO hA (j - i)).continuousOn).continuousAt (hO.mem_nhds hu)
      have hpath : Tendsto (fun τ : ℝ => (u, u + τ)) (𝓝[>] (0:ℝ)) (𝓝 (u, u)) := by
        have hc : ContinuousAt (fun τ : ℝ => (u, u + τ)) 0 := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      exact hcont.tendsto.comp hpath
    have hprod := (h1.const_mul (lcoef j i p)).mul h2
    simpa using hprod
  have hsum := tendsto_finsetSum _ hterm
  have hfun : (fun τ : ℝ => ∑ i ∈ Finset.range (j + 1),
      lcoef j i p * τ ^ (p - i) * pder A (j - i) u (u + τ)) = fun τ : ℝ => kt A p j u τ := by
    funext τ; simp only [kt]
  rw [hfun] at hsum
  simpa using hsum

/-- The shifted kernel tends to `0` at `τ = 0` (two-sided) when `j < p`. -/
theorem tendsto_kt_zero' (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u : ℝ}
    (hjp : (j : ℝ) < p) (hu : (u, u) ∈ O) :
    Tendsto (fun τ : ℝ => kt A p j u τ) (𝓝 (0:ℝ)) (𝓝 0) := by
  have hpos : ∀ i ∈ Finset.range (j + 1), 0 < p - i := by
    intro i hi
    have hi' : (i : ℝ) ≤ j := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    linarith
  have hterm : ∀ i ∈ Finset.range (j + 1),
      Tendsto (fun τ : ℝ => lcoef j i p * τ ^ (p - i) * pder A (j - i) u (u + τ))
        (𝓝 (0:ℝ)) (𝓝 0) := by
    intro i hi
    have h1 : Tendsto (fun τ : ℝ => τ ^ (p - i)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      have hc := Real.continuousAt_rpow_const (0:ℝ) (p - i) (Or.inr (le_of_lt (hpos i hi)))
      have ht : Tendsto (fun τ : ℝ => τ ^ (p - i)) (𝓝 (0:ℝ)) (𝓝 (0 ^ (p - i))) := hc
      rwa [Real.zero_rpow (ne_of_gt (hpos i hi))] at ht
    have h2 : Tendsto (fun τ : ℝ => pder A (j - i) u (u + τ)) (𝓝 (0:ℝ))
        (𝓝 (pder A (j - i) u u)) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => pder A (j - i) q.1 q.2) (u, u) :=
        ((contDiffOn_uncurried_pder hO hA (j - i)).continuousOn).continuousAt (hO.mem_nhds hu)
      have hpath : Tendsto (fun τ : ℝ => (u, u + τ)) (𝓝 (0:ℝ)) (𝓝 (u, u)) := by
        have hc : ContinuousAt (fun τ : ℝ => (u, u + τ)) 0 := by fun_prop
        simpa using hc.tendsto
      exact hcont.tendsto.comp hpath
    have hprod := (h1.const_mul (lcoef j i p)).mul h2
    simpa using hprod
  have hsum := tendsto_finsetSum _ hterm
  have hfun : (fun τ : ℝ => ∑ i ∈ Finset.range (j + 1),
      lcoef j i p * τ ^ (p - i) * pder A (j - i) u (u + τ)) = fun τ : ℝ => kt A p j u τ := by
    funext τ; simp only [kt]
  rw [hfun] at hsum
  simpa using hsum

end Work.OddVolterra.Swept
