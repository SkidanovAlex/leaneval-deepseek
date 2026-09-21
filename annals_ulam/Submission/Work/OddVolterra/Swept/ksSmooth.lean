import Mathlib
import Submission.Work.OddVolterra.SweptDefs

/-!
# Smooth-level calculus of the Leibniz expansion `ks`, `kt`, `tkt` and the partials `pder`, `qder`

The same body of facts as in `Swept.Pder`, `Swept.rpow_ident`, `Swept.KsCalc`, `Swept.KtCalc`,
but for `A` assumed only **smooth** (`C^∞`) on the open set `O` rather than analytic.  This is the
level at which the swept-integral statements assume their kernel.
-/

noncomputable section

namespace Work.OddVolterra.Swept.Smooth

open Work.OddVolterra
open Filter
open scoped Topology ContDiff

variable {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}










variable {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}

/-- The uncurried version of `A` is smooth on `O`, hence so is every iterated first-variable
partial derivative. -/
theorem contDiffOn_uncurried_pder_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) (m : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => pder A m q.1 q.2) O := by
  induction m with
  | zero => simpa [pder] using hA
  | succ m ih =>
    obtain ⟨hdiff, hf⟩ := (contDiffOn_infty_iff_fderiv_of_isOpen hO).1 ih
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((1:ℝ),(0:ℝ))) O :=
      hf.clm_apply contDiffOn_const
    refine h1.congr fun q hq => ?_
    have hq' : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q :=
      hdiff.differentiableAt (hO.mem_nhds hq)
    have hcurve : HasDerivAt (fun x : ℝ => (x, q.2)) ((1:ℝ),(0:ℝ)) q.1 :=
      (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
    have hcomp := hq'.hasFDerivAt.comp_hasDerivAt q.1 hcurve
    have h1eq : deriv (fun x : ℝ => pder A m x q.2) q.1
        = (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((1:ℝ),(0:ℝ)) := hcomp.deriv
    rw [← h1eq]
    simp only [pder, iteratedDeriv_succ]

/-- Derivative of `x ↦ pder A m x σ` is `pder A (m+1) · σ`. -/
theorem hasDerivAt_pder_fst_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {m : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) :
    HasDerivAt (fun x : ℝ => pder A m x σ) (pder A (m + 1) u σ) u := by
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ) :=
    ((contDiffOn_uncurried_pder_smooth hO hA m).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)
  have hcurve : HasDerivAt (fun x : ℝ => (x, σ)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u σ)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt u hcurve
  have hcomp' : HasDerivAt (fun x : ℝ => pder A m x σ)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hcomp
  have hval : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))
      = pder A (m + 1) u σ := by
    rw [← hcomp'.deriv]; simp only [pder, iteratedDeriv_succ]
  exact hcomp'.congr_deriv hval

/-- Derivative of `y ↦ pder A m u y` is `qder A m ·`. -/
theorem hasDerivAt_pder_snd_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {m : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) :
    HasDerivAt (fun y : ℝ => pder A m u y) (qder A m u σ) σ := by
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ) :=
    ((contDiffOn_uncurried_pder_smooth hO hA m).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)
  have hcurve : HasDerivAt (fun y : ℝ => (u, y)) ((0:ℝ),(1:ℝ)) σ :=
    (hasDerivAt_const σ u).prodMk (hasDerivAt_id σ)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt σ hcurve
  have hcomp' : HasDerivAt (fun y : ℝ => pder A m u y)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))) σ := by
    simpa [Function.comp_def] using hcomp
  have hval : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))
      = qder A m u σ := by
    rw [← hcomp'.deriv]; rfl
  exact hcomp'.congr_deriv hval

/-- The Fréchet derivative of the uncurried `m`-th first-variable partial of `A`. -/
theorem hasFDerivAt_uncurried_pder_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {m : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) :
    HasFDerivAt (fun q : ℝ × ℝ => pder A m q.1 q.2)
      ((pder A (m + 1) u σ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (qder A m u σ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, σ) := by
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ) :=
    ((contDiffOn_uncurried_pder_smooth hO hA m).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)
  have hfd := hdiff.hasFDerivAt
  have hcurve1 : HasDerivAt (fun x : ℝ => (x, σ)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u σ)
  have hcurve2 : HasDerivAt (fun y : ℝ => (u, y)) ((0:ℝ),(1:ℝ)) σ :=
    (hasDerivAt_const σ u).prodMk (hasDerivAt_id σ)
  have hcomp1 : HasDerivAt (fun x : ℝ => pder A m x σ)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hcurve1
  have hcomp2 : HasDerivAt (fun y : ℝ => pder A m u y)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))) σ := by
    simpa [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt σ hcurve2
  have h1 : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((1:ℝ),(0:ℝ))
      = pder A (m+1) u σ := by
    rw [← hcomp1.deriv]; simp only [pder, iteratedDeriv_succ]
  have h2 : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))
      = qder A m u σ := by
    rw [← hcomp2.deriv]; rfl
  have hL : (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) (u,σ))
      = ((pder A (m + 1) u σ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (qder A m u σ) • ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • ((1:ℝ),(0:ℝ)) + v.2 • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, h1, h2]
    simp [smul_eq_mul, mul_comm]
  rw [← hL]
  exact hfd

/-- The uncurried version of `qder A m` is smooth wherever `A` is. -/
theorem contDiffOn_uncurried_qder_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) (m : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => qder A m q.1 q.2) O := by
  obtain ⟨hdiff, hf⟩ := (contDiffOn_infty_iff_fderiv_of_isOpen hO).1
    (contDiffOn_uncurried_pder_smooth hO hA m)
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((0:ℝ),(1:ℝ))) O :=
    hf.clm_apply contDiffOn_const
  refine hfd.congr fun q hq => ?_
  have hq' : DifferentiableAt ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q :=
    hdiff.differentiableAt (hO.mem_nhds hq)
  have hcurve : HasDerivAt (fun y : ℝ => (q.1, y)) ((0:ℝ),(1:ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hcomp := hq'.hasFDerivAt.comp_hasDerivAt q.2 hcurve
  have hcomp' : HasDerivAt (fun y : ℝ => pder A m q.1 y)
      ((fderiv ℝ (fun q : ℝ × ℝ => pder A m q.1 q.2) q) ((0:ℝ),(1:ℝ))) q.2 := by
    simpa [Function.comp_def] using hcomp
  exact hcomp'.deriv











/-- The `i`-th iterated derivative of `x ↦ (σ - x)^p` away from `x = σ`. -/
theorem iteratedDeriv_const_sub_rpow_smooth (p : ℝ) (i : ℕ) {σ u : ℝ} (hu : u ≠ σ) :
    iteratedDeriv i (fun x : ℝ => (σ - x) ^ p) u
      = (-1 : ℝ) ^ i * rff p i * (σ - u) ^ (p - i) := by
  induction i generalizing u with
  | zero => simp [rff]
  | succ i ih =>
    rw [iteratedDeriv_succ]
    have hfuneq : iteratedDeriv i (fun x : ℝ => (σ - x) ^ p) =ᶠ[𝓝 u]
        (fun x : ℝ => (-1 : ℝ) ^ i * rff p i * (σ - x) ^ (p - i)) := by
      filter_upwards [isOpen_ne.mem_nhds hu] with x hx
      exact ih hx
    rw [Filter.EventuallyEq.deriv_eq hfuneq]
    have hsub : (σ - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have hrpow : HasDerivAt (fun y : ℝ => y ^ (p - i)) ((p - i) * (σ - u) ^ (p - i - 1))
        (σ - u) := Real.hasDerivAt_rpow_const (Or.inl hsub)
    have hinner : HasDerivAt (fun x : ℝ => σ - x) (-1) u := (hasDerivAt_id u).const_sub σ
    have hcomp : HasDerivAt (fun x : ℝ => (σ - x) ^ (p - i))
        (((p - i) * (σ - u) ^ (p - i - 1)) * (-1)) u := hrpow.comp u hinner
    have hmain : HasDerivAt (fun x : ℝ => (-1 : ℝ) ^ i * rff p i * (σ - x) ^ (p - i))
        ((-1 : ℝ) ^ i * rff p i * (((p - i) * (σ - u) ^ (p - i - 1)) * (-1))) u :=
      hcomp.const_mul ((-1 : ℝ) ^ i * rff p i)
    rw [hmain.deriv, rff_succ]
    have hexp : p - (i : ℝ) - 1 = p - ((i + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hexp, pow_succ]
    ring

/-- **The Leibniz expansion of the iterated derivative of `(σ - ·)^p · A · σ`.** -/
theorem iteratedDeriv_rpow_mul_smooth {A : ℝ → ℝ → ℝ} {p : ℝ} {j : ℕ} {u σ : ℝ}
    (hσ : u < σ) (hA : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) (u, σ)) :
    iteratedDeriv j (fun x : ℝ => (σ - x) ^ p * A x σ) u = ks A p j u σ := by
  have hne : u ≠ σ := ne_of_lt hσ
  have hsub : (σ - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hf : ContDiffAt ℝ (j : ℕ∞) (fun x : ℝ => (σ - x) ^ p) u := by
    have h1 : ContDiffAt ℝ (j : ℕ∞) (fun y : ℝ => y ^ p) (σ - u) :=
      Real.contDiffAt_rpow_const (Or.inl hsub)
    have h2 : ContDiffAt ℝ (j : ℕ∞) (fun x : ℝ => σ - x) u := by fun_prop
    have h3 := h1.comp u h2
    simpa [Function.comp_def] using h3
  have hg : ContDiffAt ℝ (j : ℕ∞) (fun x : ℝ => A x σ) u := by
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (x, σ)) u := by fun_prop
    have h3 := hA.comp u h2
    have h4 : ContDiffAt ℝ (⊤ : ℕ∞) ((fun q : ℝ × ℝ => A q.1 q.2) ∘ fun x : ℝ => (x, σ)) u := h3
    simpa [Function.comp_def] using h4.of_le (by exact_mod_cast le_top)
  have hfun : (fun x : ℝ => (σ - x) ^ p * A x σ)
      = (fun x : ℝ => (σ - x) ^ p) * (fun x : ℝ => A x σ) := by
    funext x; rfl
  rw [hfun, iteratedDeriv_mul hf hg]
  rw [ks]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiter : iteratedDeriv i (fun x : ℝ => (σ - x) ^ p) u
      = (-1 : ℝ) ^ i * rff p i * (σ - u) ^ (p - i) := iteratedDeriv_const_sub_rpow_smooth p i hne
  have hiter2 : iteratedDeriv (j - i) (fun x : ℝ => A x σ) u = pder A (j - i) u σ := rfl
  rw [hiter, hiter2, lcoef]
  ring













variable {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}

/-- The slice `y ↦ A y σ` is smooth at `u` when `(u,σ)` is a smoothness point of `A`. -/
theorem contDiffAt_slice_snd_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {u σ : ℝ} (huσ : (u, σ) ∈ O) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => A y σ) u := by
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (y, σ)) u := by fun_prop
  have h5 := hA.contDiffAt (hO.mem_nhds huσ)
  have h6 := h5.comp u h4
  simpa [Function.comp_def] using h6

/-- One-variable differentiability of the slice `x ↦ ks A p j x σ`. -/
theorem hasDerivAt_ks_fst_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) (hσ : u < σ) :
    HasDerivAt (fun x : ℝ => ks A p j x σ) (ks A p (j + 1) u σ) u := by
  have hslice : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (σ - y) ^ p * A y σ) u := by
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ p) (σ - u) :=
      Real.contDiffAt_rpow_const_of_ne (sub_ne_zero.mpr (ne_of_lt hσ).symm)
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => σ - y) u := by fun_prop
    exact (h1.comp u h2).mul (contDiffAt_slice_snd_smooth hO hA huσ)
  have hdiff : DifferentiableAt ℝ (iteratedDeriv j (fun y : ℝ => (σ - y) ^ p * A y σ)) u := by
    have hcw : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun y : ℝ => (σ - y) ^ p * A y σ) Set.univ u :=
      hslice.contDiffWithinAt
    have huniq : UniqueDiffOn ℝ (insert u (Set.univ : Set ℝ)) := by
      rw [Set.insert_eq_of_mem (Set.mem_univ u)]; exact uniqueDiffOn_univ
    have h := hcw.differentiableWithinAt_iteratedDerivWithin (s := Set.univ) (m := j)
      (by exact_mod_cast lt_top_iff_ne_top.mpr (by simp)) huniq
    simpa [iteratedDerivWithin_univ, differentiableWithinAt_univ] using h
  have hmain : HasDerivAt (iteratedDeriv j (fun y : ℝ => (σ - y) ^ p * A y σ))
      (ks A p (j + 1) u σ) u := by
    have h := hdiff.hasDerivAt
    have hval : iteratedDeriv (j + 1) (fun y : ℝ => (σ - y) ^ p * A y σ) u = ks A p (j+1) u σ :=
      iteratedDeriv_rpow_mul_smooth hσ (hA.contDiffAt (hO.mem_nhds huσ))
    have hder : deriv (iteratedDeriv j (fun y : ℝ => (σ - y) ^ p * A y σ)) u
        = iteratedDeriv (j + 1) (fun y : ℝ => (σ - y) ^ p * A y σ) u := by
      rw [iteratedDeriv_succ]
    rw [hder, hval] at h
    exact h
  refine hmain.congr_of_eventuallyEq ?_
  have hOnb : {x : ℝ | (x, σ) ∈ O} ∈ 𝓝 u :=
    (hO.preimage (by fun_prop : Continuous fun x : ℝ => (x, σ))).mem_nhds huσ
  filter_upwards [hOnb, isOpen_Iio.mem_nhds hσ] with x hx hxlt
  exact (iteratedDeriv_rpow_mul_smooth hxlt (hA.contDiffAt (hO.mem_nhds hx))).symm

/-- One-variable differentiability of the slice `y ↦ ks A p j u y`, with the explicit derivative
`tkt A p j u (σ - u)` (the second half of the Leibniz expansion is the `σ`-derivative). -/
theorem hasDerivAt_ks_snd_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
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
      hasDerivAt_pder_snd_smooth hO hA huσ
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
theorem differentiableAt_uncurried_ks_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) (hσ : u < σ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u, σ) := by
  have hsub : (σ - u) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hσ).symm
  rw [show (fun q : ℝ × ℝ => ks A p j q.1 q.2)
      = (∑ i ∈ Finset.range (j+1), fun q : ℝ × ℝ => lcoef j i p * (q.2 - q.1) ^ (p - i) * pder A (j - i) q.1 q.2) from by
    funext q; simp only [ks, Finset.sum_apply]]
  refine DifferentiableAt.sum fun i hi => ?_
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.mul (differentiableAt_const _) ?_
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ (p - i)) (σ - u) :=
      Real.contDiffAt_rpow_const_of_ne hsub
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2 - q.1) (u, σ) := by fun_prop
    exact ((h1.comp (u, σ) h2).differentiableAt (by simp))
  · exact ((contDiffOn_uncurried_pder_smooth hO hA (j - i)).differentiableOn (by norm_num)).differentiableAt
      (hO.mem_nhds huσ)

/-- The Fréchet derivative of the uncurried `ks`, with the two partial derivatives exhibited. -/
theorem hasFDerivAt_uncurried_ks_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u σ : ℝ}
    (huσ : (u, σ) ∈ O) (hσ : u < σ) :
    HasFDerivAt (fun q : ℝ × ℝ => ks A p j q.1 q.2)
      ((ks A p (j + 1) u σ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u (σ - u)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, σ) := by
  have hdiff := differentiableAt_uncurried_ks_smooth (p := p) (j := j) hO hA huσ hσ
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
      = ks A p (j+1) u σ := hcomp1.unique (hasDerivAt_ks_fst_smooth hO hA huσ hσ)
  have h2 : (fderiv ℝ (fun q : ℝ × ℝ => ks A p j q.1 q.2) (u,σ)) ((0:ℝ),(1:ℝ))
      = tkt A p j u (σ - u) := hcomp2.unique (hasDerivAt_ks_snd_smooth hO hA huσ hσ)
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













variable {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}

theorem hasFDerivAt_uncurried_kt_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u τ : ℝ}
    (huτ : (u, u + τ) ∈ O) (hτ : 0 < τ) :
    HasFDerivAt (fun q : ℝ × ℝ => kt A p j q.1 q.2)
      ((ks A p (j + 1) u (u + τ) + tkt A p j u τ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u τ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, τ) := by
  have hσ : u < u + τ := by linarith
  have hK := hasFDerivAt_uncurried_ks_smooth (p := p) (j := j) hO hA huτ hσ
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

theorem hasDerivAt_kt_fst_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u τ : ℝ}
    (huτ : (u, u + τ) ∈ O) (hτ : 0 < τ) :
    HasDerivAt (fun x : ℝ => kt A p j x τ) (ks A p (j + 1) u (u + τ) + tkt A p j u τ) u := by
  have hK := hasFDerivAt_uncurried_kt_smooth (p := p) (j := j) hO hA huτ hτ
  have hcurve : HasDerivAt (fun x : ℝ => (x, τ)) ((1:ℝ),(0:ℝ)) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u τ)
  have hcomp := hK.comp_hasDerivAt u hcurve
  have hcomp' : HasDerivAt (fun x : ℝ => kt A p j x τ)
      (((ks A p (j + 1) u (u + τ) + tkt A p j u τ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u τ) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ),(0:ℝ))) u := by
    simpa [Function.comp_def] using hcomp
  simpa using hcomp'

theorem hasDerivAt_kt_snd_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u τ : ℝ}
    (huτ : (u, u + τ) ∈ O) (hτ : 0 < τ) :
    HasDerivAt (fun y : ℝ => kt A p j u y) (tkt A p j u τ) τ := by
  have hK := hasFDerivAt_uncurried_kt_smooth (p := p) (j := j) hO hA huτ hτ
  have hcurve : HasDerivAt (fun y : ℝ => (u, y)) ((0:ℝ),(1:ℝ)) τ :=
    (hasDerivAt_const τ u).prodMk (hasDerivAt_id τ)
  have hcomp := hK.comp_hasDerivAt τ hcurve
  have hcomp' : HasDerivAt (fun y : ℝ => kt A p j u y)
      (((ks A p (j + 1) u (u + τ) + tkt A p j u τ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (tkt A p j u τ) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((0:ℝ),(1:ℝ))) τ := by
    simpa [Function.comp_def] using hcomp
  simpa using hcomp'

/-- The shifted kernel tends to `0` at `τ = 0⁺` when `j < p`. -/
theorem tendsto_kt_zero_smooth (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) {p : ℝ} {j : ℕ} {u : ℝ}
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
        ((contDiffOn_uncurried_pder_smooth hO hA (j - i)).continuousOn).continuousAt (hO.mem_nhds hu)
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



end Work.OddVolterra.Swept.Smooth
