import Submission.Work.OddVolterra.SweptDefs
import Submission.Work.OddVolterra.Swept.Pder
import Submission.Work.OddVolterra.Swept.rpow_ident

/-!
# Calculus of the Leibniz expansion `ks`

We prove that on the region `u < σ` the function `(u,σ) ↦ ks A p j u σ` is differentiable, and
that its two partial derivatives are `ks A p (j+1) u σ` (in `u`) and `tkt A p j u (σ - u)`
(in `σ`).
-/

noncomputable section

namespace Work.OddVolterra.Swept

open Work.OddVolterra
open Filter
open scoped Topology

variable {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}

/-- The slice `y ↦ A y σ` is smooth at `u` when `(u,σ)` is a smoothness point of `A`. -/
theorem contDiffAt_slice_snd (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {u σ : ℝ} (huσ : (u, σ) ∈ O) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => A y σ) u := by
  have h4 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => (y, σ)) u := by fun_prop
  have h5 := hA.contDiffAt (hO.mem_nhds huσ)
  have h6 := h5.comp u h4
  simpa [Function.comp_def] using h6

/-- One-variable differentiability of the slice `x ↦ ks A p j x σ`. -/
theorem hasDerivAt_ks_fst (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) (hσ : u < σ) :
    HasDerivAt (fun x : ℝ => ks A p j x σ) (ks A p (j + 1) u σ) u := by
  have hslice : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => (σ - y) ^ p * A y σ) u := by
    have h1 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => y ^ p) (σ - u) :=
      Real.contDiffAt_rpow_const_of_ne (sub_ne_zero.mpr (ne_of_lt hσ).symm)
    have h2 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => σ - y) u := by fun_prop
    exact (h1.comp u h2).mul (contDiffAt_slice_snd hO hA huσ)
  have hdiff : DifferentiableAt ℝ (iteratedDeriv j (fun y : ℝ => (σ - y) ^ p * A y σ)) u := by
    have hcw : ContDiffWithinAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => (σ - y) ^ p * A y σ) Set.univ u :=
      hslice.contDiffWithinAt
    have huniq : UniqueDiffOn ℝ (insert u (Set.univ : Set ℝ)) := by
      rw [Set.insert_eq_of_mem (Set.mem_univ u)]; exact uniqueDiffOn_univ
    have hlt : ((j : ℕ∞) : WithTop ℕ∞) < (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [WithTop.coe_lt_coe]
      exact WithTop.coe_lt_top j
    have h := hcw.differentiableWithinAt_iteratedDerivWithin (s := Set.univ) (m := j) hlt huniq
    simpa [iteratedDerivWithin_univ, differentiableWithinAt_univ] using h
  have hmain : HasDerivAt (iteratedDeriv j (fun y : ℝ => (σ - y) ^ p * A y σ))
      (ks A p (j + 1) u σ) u := by
    have h := hdiff.hasDerivAt
    have hval : iteratedDeriv (j + 1) (fun y : ℝ => (σ - y) ^ p * A y σ) u = ks A p (j+1) u σ :=
      iteratedDeriv_rpow_mul hσ (hA.contDiffAt (hO.mem_nhds huσ))
    have hder : deriv (iteratedDeriv j (fun y : ℝ => (σ - y) ^ p * A y σ)) u
        = iteratedDeriv (j + 1) (fun y : ℝ => (σ - y) ^ p * A y σ) u := by
      rw [iteratedDeriv_succ]
    rw [hder, hval] at h
    exact h
  refine hmain.congr_of_eventuallyEq ?_
  have hOnb : {x : ℝ | (x, σ) ∈ O} ∈ 𝓝 u :=
    (hO.preimage (by fun_prop : Continuous fun x : ℝ => (x, σ))).mem_nhds huσ
  filter_upwards [hOnb, isOpen_Iio.mem_nhds hσ] with x hx hxlt
  exact (iteratedDeriv_rpow_mul hxlt (hA.contDiffAt (hO.mem_nhds hx))).symm

/-- One-variable differentiability of the slice `y ↦ ks A p j u y`, with the explicit derivative
`tkt A p j u (σ - u)` (the second half of the Leibniz expansion is the `σ`-derivative). -/
theorem hasDerivAt_ks_snd (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) (hσ : u < σ) :
    HasDerivAt (fun y : ℝ => ks A p j u y) (tkt A p j u (σ - u)) σ := by
  have hsub : (σ - u) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hσ).symm
  have hterm : ∀ i ∈ Finset.range (j + 1),
      HasDerivAt (fun y : ℝ => lcoef j i p * (y - u) ^ (p - i) * pder A (j - i) u y)
        (lcoef j i p * ((p - i) * (σ - u) ^ (p - i - 1) * pder A (j - i) u σ
          + (σ - u) ^ (p - i) * qder A (j - i) u σ)) σ := by
    intro i hi
    have hpow : HasDerivAt (fun y : ℝ => (y - u) ^ (p - i)) ((p - i) * (σ - u) ^ (p - i - 1)) σ := by
      have h1 : HasDerivAt (fun y : ℝ => y - u) 1 σ := (hasDerivAt_id σ).sub_const u
      have h2 : HasDerivAt (fun x : ℝ => x ^ (p - i)) ((p - i) * (σ - u) ^ (p - i - 1))
          (σ - u) := Real.hasDerivAt_rpow_const (Or.inl hsub)
      simpa [Function.comp_def] using h2.comp σ h1
    have hpder : HasDerivAt (fun y : ℝ => pder A (j - i) u y) (qder A (j - i) u σ) σ :=
      hasDerivAt_pder_snd hO hA huσ
    have hprod := hpow.mul hpder
    have hres := hprod.const_mul (lcoef j i p)
    simpa [Pi.mul_apply, mul_assoc] using hres
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (fun y : ℝ => ∑ i ∈ Finset.range (j + 1),
        lcoef j i p * (y - u) ^ (p - i) * pder A (j - i) u y) = fun y : ℝ => ks A p j u y := by
    funext y; simp only [ks]
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  simp only [tkt]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show u + (σ - u) = σ from by ring]

/-- The uncurried `ks` function is differentiable on the region `u < σ`. -/
theorem differentiableAt_uncurried_ks (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) (hσ : u < σ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u, σ) := by
  have hsub : (σ - u) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hσ).symm
  rw [show (fun q : ℝ × ℝ => ks A p j q.1 q.2)
      = (∑ i ∈ Finset.range (j+1), fun q : ℝ × ℝ => lcoef j i p * (q.2 - q.1) ^ (p - i) * pder A (j - i) q.1 q.2) from by
    funext q; simp only [ks, Finset.sum_apply]]
  refine DifferentiableAt.sum fun i hi => ?_
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.mul (differentiableAt_const _) ?_
    have h1 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => x ^ (p - i)) (σ - u) :=
      Real.contDiffAt_rpow_const_of_ne hsub
    have h2 : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => q.2 - q.1) (u, σ) := by fun_prop
    exact ((h1.comp (u, σ) h2).differentiableAt (by simp))
  · exact ((contDiffOn_uncurried_pder hO hA (j - i)).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)

/-- The Fréchet derivative of the uncurried `ks`, with the two partial derivatives exhibited. -/
theorem hasFDerivAt_uncurried_ks (hO : IsOpen O)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) (hσ : u < σ) :
    HasFDerivAt (fun q : ℝ × ℝ => ks A p j q.1 q.2)
      ((ks A p (j + 1) u σ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u (σ - u)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, σ) := by
  have hdiff := differentiableAt_uncurried_ks (p := p) (j := j) hO hA huσ hσ
  have hfd := hdiff.hasFDerivAt
  have hcurve1 : HasDerivAt (fun x : ℝ => (x, σ)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u σ)
  have hcurve2 : HasDerivAt (fun y : ℝ => (u, y)) ((0:ℝ),(1:ℝ)) σ :=
    (hasDerivAt_const σ u).prodMk (hasDerivAt_id σ)
  have hcomp1 : HasDerivAt (fun x : ℝ => ks A p j x σ)
      ((fderiv ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hfd.comp_hasDerivAt u hcurve1
  have hcomp2 : HasDerivAt (fun y : ℝ => ks A p j u y)
      ((fderiv ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))) σ := by
    simpa [Function.comp_def] using hfd.comp_hasDerivAt σ hcurve2
  have h1 : (fderiv ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))
      = ks A p (j+1) u σ := hcomp1.unique (hasDerivAt_ks_fst hO hA huσ hσ)
  have h2 : (fderiv ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))
      = tkt A p j u (σ - u) := hcomp2.unique (hasDerivAt_ks_snd hO hA huσ hσ)
  have hL : (fderiv ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u,σ))
      = ((ks A p (j + 1) u σ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u (σ - u)) • ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, h1, h2]
    simp [smul_eq_mul, mul_comm]
  rw [← hL]
  exact hfd

end Work.OddVolterra.Swept
