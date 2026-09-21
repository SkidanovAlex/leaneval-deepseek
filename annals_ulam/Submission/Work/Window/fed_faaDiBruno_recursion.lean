import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.Rnu_spec
import Submission.Work.Geometry.Ulam.ulam_faa_j
import Submission.Work.OddVolterra.Kernel.Diag

/-!
# The Faà-di-Bruno recursion for `faaDiBrunoJ`, and its use for the manifest numerator `J1M`

This file proves `Work.Window.fed_faaDiBruno_recursion`:

* part (1): the Faà-di-Bruno polynomial `faaDiBrunoJ m ν 0 v` satisfies the classical recursion
  `F_{m+1}(v) = v 0 · (∇F_m)(v ∘ castSucc) · (v ∘ succ) + (ν-m) · v 1 · F_m(v ∘ castSucc)`;
* part (2): consequently `J1M = Rnu (n+1/2) h 1 (n+1)` equals `faaDiBrunoJ (n+1) (n+1/2) 0`
  applied to the `a`-jet of `Zrad h (·,σ,t)`, for **all** `a σ t` (no order condition).

## The strategy

The recursive object is materialised twice:

* `bellR ν Z m : ℝ → ℝ` is the classical recursion `R_{m+1} = Z·R_m' + (ν-m)·Z'·R_m`,
  `R_0 = 1`, in the *base-point* variable.  For `0 < Z s` one shows
  `bellR ν Z m s = (∂^m (Z^ν))(s) · Z s ^ (m-ν)` by induction, which combined with
  `faaDiBrunoJ_spec` identifies `bellR ν Z m s` with `faaDiBrunoJ m ν 0` at the jet of `Z` at `s`
  whenever `Z s > 0`.
* `bellP ν m` is the same recursion in the *jet* variable.

The chain rule (`HasFDerivAt.comp_hasDerivAt`) plus the fact that the derivative of the jet curve
is the shift of the jet (`fed_hasDerivAt_jet`) shows `bellP ν m (jet Z s) = bellR ν Z m s` for every
smooth `Z` and every `s`; hence, realising any jet vector by its Taylor polynomial,
`bellP ν m v = faaDiBrunoJ m ν 0 v` for every `v` with `v 0 > 0`.  Homogeneity (`bellP_smul` and
`faaDiBrunoJ_smul`) covers `v 0 < 0`, and continuity of both sides covers `v 0 = 0`.  Part (1) is
then just `bellP_succ_eq`.

Part (2) follows since `Rnu ν h 1 m (·,σ,t)` satisfies the same recursion as
`bellR ν (Zrad h (·,σ,t)) m` (that is `KernelExt.Rnu_succ_apply`).
-/

namespace Work.Window

open Finset Filter
open scoped Topology ContDiff

noncomputable section

/-! ## 1. Homogeneity of the Faà-di-Bruno polynomial -/

/-- The Faà-di-Bruno polynomial is homogeneous of degree `m` in the jet variable. -/
lemma faaDiBrunoJ_smul (m : ℕ) (α s c : ℝ) (v : Fin (m + 1) → ℝ) :
    Commons.Geometry.Ulam.faaDiBrunoJ m α s (fun i => c * v i)
      = c ^ m * Commons.Geometry.Ulam.faaDiBrunoJ m α s v := by
  unfold Commons.Geometry.Ulam.faaDiBrunoJ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hprod : (∏ j : Fin d.length,
        (fun i => c * v i) ⟨d.partSize j, Nat.lt_succ_of_le (d.partSize_le j)⟩)
      = c ^ d.length * ∏ j : Fin d.length,
          v ⟨d.partSize j, Nat.lt_succ_of_le (d.partSize_le j)⟩ := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpow : (c * v 0) ^ (m - d.length) = c ^ (m - d.length) * v 0 ^ (m - d.length) := by
    rw [mul_pow]
  rw [hprod, hpow]
  have hkl : d.length + (m - d.length) = m := Nat.add_sub_of_le d.length_le
  calc (Polynomial.eval α (descPochhammer ℝ d.length) *
          (c ^ d.length * ∏ j : Fin d.length,
            v ⟨d.partSize j, Nat.lt_succ_of_le (d.partSize_le j)⟩) *
          (c ^ (m - d.length) * v 0 ^ (m - d.length)))
      = (Polynomial.eval α (descPochhammer ℝ d.length) *
          (∏ j : Fin d.length,
            v ⟨d.partSize j, Nat.lt_succ_of_le (d.partSize_le j)⟩) *
          v 0 ^ (m - d.length)) * (c ^ d.length * c ^ (m - d.length)) := by ring
    _ = (Polynomial.eval α (descPochhammer ℝ d.length) *
          (∏ j : Fin d.length,
            v ⟨d.partSize j, Nat.lt_succ_of_le (d.partSize_le j)⟩) *
          v 0 ^ (m - d.length)) * c ^ m := by rw [← pow_add, hkl]
    _ = c ^ m * (Polynomial.eval α (descPochhammer ℝ d.length) *
          (∏ j : Fin d.length,
            v ⟨d.partSize j, Nat.lt_succ_of_le (d.partSize_le j)⟩) *
          v 0 ^ (m - d.length)) := by ring

/-! ## 2. Scaling of the derivative of a homogeneous function -/

/-- The Fréchet derivative of a homogeneous function of degree `m` scales as `c ^ m`. -/
lemma fderiv_smul_apply {k : ℕ} {F : (Fin k → ℝ) → ℝ} {m : ℕ} {c : ℝ}
    (hd : ∀ x, DifferentiableAt ℝ F x)
    (h : ∀ v : Fin k → ℝ, F (fun i => c * v i) = c ^ m * F v) (x w : Fin k → ℝ) :
    (fderiv ℝ F (fun i => c * x i)) (fun i => c * w i) = c ^ m * (fderiv ℝ F x) w := by
  set φ : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) := c • ContinuousLinearMap.id ℝ (Fin k → ℝ) with hφdef
  have hφ : ∀ v : Fin k → ℝ, φ v = fun i => c * v i := by
    intro v; funext i
    rw [hφdef, smul_apply, ContinuousLinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  have hfun : (fun v : Fin k → ℝ => F (φ v)) = fun v => c ^ m * F v := by
    funext v; rw [hφ v]; exact h v
  have h1 : fderiv ℝ (fun v : Fin k → ℝ => F (φ v)) x = (fderiv ℝ F (φ x)).comp φ := by
    have hc := fderiv_comp (𝕜 := ℝ) (f := ⇑φ) (g := F) x (hd (φ x)) φ.differentiableAt
    simp only [ContinuousLinearMap.fderiv, Function.comp_def] at hc
    exact hc
  have h2 : fderiv ℝ (fun v : Fin k → ℝ => F (φ v)) x = c ^ m • fderiv ℝ F x := by
    rw [hfun, fderiv_const_mul (hd x)]
  have hcomp : (fderiv ℝ F (φ x)).comp φ = c ^ m • fderiv ℝ F x := h1 ▸ h2
  have hw := congrFun (congrArg DFunLike.coe hcomp) w
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul] at hw
  rw [hφ w] at hw
  exact hw

/-! ## 3. The constant term `F_0 = 1` -/

lemma faaDiBrunoJ_zero (ν : ℝ) (v : Fin 1 → ℝ) :
    Commons.Geometry.Ulam.faaDiBrunoJ 0 ν 0 v = 1 := by
  have hterm : ∀ c : OrderedFinpartition 0,
      Polynomial.eval ν (descPochhammer ℝ c.length) *
        (∏ j : Fin c.length, v ⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩) *
        v 0 ^ (0 - c.length) = 1 := by
    intro c
    have hc : c.length = 0 := Nat.eq_zero_of_le_zero c.length_le
    have hprod : (∏ j : Fin c.length,
        v ⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      exact absurd (lt_of_lt_of_le j.2 c.length_le) (Nat.not_lt_zero _)
    rw [hprod, mul_one, hc]
    simp
  rw [Commons.Geometry.Ulam.faaDiBrunoJ, Finset.sum_congr rfl (fun c _ => hterm c)]
  simp

/-! ## 4. Realising a jet vector by a Taylor polynomial -/

/-- The Taylor polynomial attached to a jet vector: it turns `(v 0, …, v (N-1))` into the jet at
`0` of `x ↦ Σᵢ vᵢ x^i / i!`. -/
noncomputable def fedTaylor (N : ℕ) (v : Fin N → ℝ) : ℝ → ℝ :=
  fun x => ∑ i : Fin N, (v i / (i.1.factorial : ℝ)) * x ^ i.1

lemma fedTaylor_contDiff (N : ℕ) (v : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fedTaylor N v) := by
  unfold fedTaylor
  fun_prop

/-- The `k`-th derivative at `0` of the Taylor polynomial of `v` is `v k`. -/
lemma fedTaylor_iteratedDeriv (N : ℕ) (v : Fin N → ℝ) (k : Fin N) :
    iteratedDeriv k.1 (fedTaylor N v) 0 = v k := by
  unfold fedTaylor
  rw [iteratedDeriv_fun_sum]
  · rw [Finset.sum_eq_single k]
    · rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      simp only [if_true]
      exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    · intro i _ hik
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      have hne : k.1 ≠ i.1 := fun h => hik (Fin.ext h).symm
      simp [hne]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · intro i _
    exact contDiffAt_const.mul (contDiffAt_id.pow _)

/-! ## 5. The derivative of the jet curve is the shift of the jet -/

/-- The `x`-derivative of the jet curve of a smooth function is the shift of the jet. -/
theorem fed_hasDerivAt_jet {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fun i : Fin k => iteratedDeriv i.1 f y)
      (fun i : Fin k => iteratedDeriv (i.1 + 1) f x) x := by
  rw [hasDerivAt_pi]
  intro i
  have hCd : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv i.1 f) := by
    rw [iteratedDeriv_eq_iterate]
    exact hf.iterate_deriv i.1
  have hdiff : Differentiable ℝ (iteratedDeriv i.1 f) := hCd.differentiable (by simp)
  have h := (hdiff.differentiableAt (x := x)).hasDerivAt
  have hsucc : deriv (iteratedDeriv i.1 f) x = iteratedDeriv (i.1 + 1) f x := by
    rw [iteratedDeriv_succ]
  rwa [hsucc] at h

/-! ## 6. The Bell recursion in the base-point variable -/

/-- The classical Bell recursion `R_{m+1} = Z·R_m' + (ν-m)·Z'·R_m`, `R_0 = 1`, as a function of
the base point. -/
noncomputable def bellR (ν : ℝ) (Z : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | (m + 1) => fun s => Z s * deriv (bellR ν Z m) s + (ν - (m : ℝ)) * deriv Z s * bellR ν Z m s

@[simp] lemma bellR_zero_eq (ν : ℝ) (Z : ℝ → ℝ) (s : ℝ) : bellR ν Z 0 s = 1 := rfl

lemma bellR_succ_eq (ν : ℝ) (Z : ℝ → ℝ) (m : ℕ) (s : ℝ) :
    bellR ν Z (m + 1) s =
      Z s * deriv (bellR ν Z m) s + (ν - (m : ℝ)) * deriv Z s * bellR ν Z m s := rfl

/-- `bellR` is smooth whenever `Z` is. -/
lemma bellR_contDiff (ν : ℝ) {Z : ℝ → ℝ} (hZ : ContDiff ℝ (⊤ : ℕ∞) Z) :
    ∀ m, ContDiff ℝ (⊤ : ℕ∞) (bellR ν Z m) := by
  intro m
  induction m with
  | zero => rw [show bellR ν Z 0 = fun _ : ℝ => (1:ℝ) from rfl]; exact contDiff_const
  | succ m ih =>
    rw [show bellR ν Z (m + 1) = fun s : ℝ =>
      Z s * deriv (bellR ν Z m) s + (ν - (m : ℝ)) * deriv Z s * bellR ν Z m s from rfl]
    have hdR : ContDiff ℝ (⊤ : ℕ∞) (deriv (bellR ν Z m)) := by
      simpa only [Function.iterate_one] using ih.iterate_deriv 1
    have hdZ : ContDiff ℝ (⊤ : ℕ∞) (deriv Z) := by
      simpa only [Function.iterate_one] using hZ.iterate_deriv 1
    exact (hZ.mul hdR).add ((contDiff_const.mul hdZ).mul ih)

/-- The elementary `rpow` identity behind the induction step of `bellR_rpow_spec`. -/
lemma bell_rpow_step (m : ℕ) (ν x A B D : ℝ) (hx : 0 < x) :
    x * A + (ν - (m : ℝ)) * D * B
      = (A * x ^ (ν - (m : ℝ)) + B * (D * (ν - (m : ℝ)) * x ^ (ν - (m : ℝ) - 1)))
          * x ^ ((m : ℝ) + 1 - ν) := by
  have h1 : x ^ (ν - (m:ℝ)) * x ^ ((m:ℝ) + 1 - ν) = x := by
    rw [← Real.rpow_add hx, show ν - (m:ℝ) + ((m:ℝ) + 1 - ν) = 1 from by ring, Real.rpow_one]
  have h2 : x ^ (ν - (m:ℝ) - 1) * x ^ ((m:ℝ) + 1 - ν) = 1 := by
    rw [← Real.rpow_add hx, show ν - (m:ℝ) - 1 + ((m:ℝ) + 1 - ν) = 0 from by ring, Real.rpow_zero]
  calc x * A + (ν - (m:ℝ)) * D * B
      = A * x + B * (D * (ν - (m:ℝ))) := by ring
    _ = A * (x ^ (ν - (m:ℝ)) * x ^ ((m:ℝ)+1-ν))
          + B * (D * (ν - (m:ℝ))) * (x ^ (ν - (m:ℝ)-1) * x ^ ((m:ℝ)+1-ν)) := by
          rw [h1, h2]; ring
    _ = (A * x ^ (ν - (m:ℝ)) + B * (D * (ν - (m:ℝ)) * x ^ (ν - (m:ℝ)-1))) * x ^ ((m:ℝ)+1-ν) := by
          ring

/-- **The defining property of the Bell recursion.**  Where the radicand is positive, `bellR`
computes the `m`-th derivative of `Z^ν` times `Z^(m-ν)`. -/
theorem bellR_rpow_spec (ν : ℝ) {Z : ℝ → ℝ} (hZ : ContDiff ℝ (⊤ : ℕ∞) Z) :
    ∀ m s, 0 < Z s → bellR ν Z m s = iteratedDeriv m (fun z => Z z ^ ν) s * Z s ^ ((m:ℝ) - ν) := by
  intro m
  induction m with
  | zero =>
    intro s hs
    rw [bellR_zero_eq, iteratedDeriv_zero]
    rw [show (((0:ℕ)):ℝ) - ν = -ν from by ring, Real.rpow_neg (le_of_lt hs)]
    exact (mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hs ν))).symm
  | succ m ih =>
    intro s hs
    rw [bellR_succ_eq, iteratedDeriv_succ]
    have hmem : ∀ᶠ y in 𝓝 s, 0 < Z y :=
      (isOpen_lt continuous_const hZ.continuous).mem_nhds hs
    have heq : iteratedDeriv m (fun z => Z z ^ ν) =ᶠ[𝓝 s]
        fun y => bellR ν Z m y * Z y ^ (ν - (m:ℝ)) := by
      filter_upwards [hmem] with y hy
      rw [ih y hy, mul_assoc, ← Real.rpow_add hy,
        show ((m:ℝ) - ν) + (ν - (m:ℝ)) = 0 from by ring, Real.rpow_zero, mul_one]
    have hderiv : deriv (iteratedDeriv m (fun z => Z z ^ ν)) s
        = deriv (fun y => bellR ν Z m y * Z y ^ (ν - (m:ℝ))) s :=
      Filter.EventuallyEq.deriv_eq heq
    rw [hderiv]
    have hdR : DifferentiableAt ℝ (bellR ν Z m) s :=
      ((bellR_contDiff ν hZ m).differentiable (by simp)).differentiableAt
    have hdZ : DifferentiableAt ℝ Z s := (hZ.differentiable (by simp)).differentiableAt
    have h1 : HasDerivAt (bellR ν Z m) (deriv (bellR ν Z m) s) s := hdR.hasDerivAt
    have h2 : HasDerivAt (fun y => Z y ^ (ν - (m:ℝ)))
        (deriv Z s * (ν - (m:ℝ)) * Z s ^ (ν - (m:ℝ) - 1)) s :=
      hdZ.hasDerivAt.rpow_const (Or.inl (ne_of_gt hs))
    have hprod : deriv (fun y => bellR ν Z m y * Z y ^ (ν - (m:ℝ))) s
        = deriv (bellR ν Z m) s * Z s ^ (ν - (m:ℝ))
          + bellR ν Z m s * (deriv Z s * (ν - (m:ℝ)) * Z s ^ (ν - (m:ℝ) - 1)) := by
      have hh := (h1.mul h2).deriv
      rw [show (bellR ν Z m * fun y : ℝ => Z y ^ (ν - (m:ℝ)))
          = fun y => bellR ν Z m y * Z y ^ (ν - (m:ℝ)) from rfl] at hh
      exact hh
    rw [hprod]
    rw [show (((m+1 : ℕ)):ℝ) - ν = (m:ℝ) + 1 - ν from by push_cast; ring]
    exact bell_rpow_step m ν (Z s) (deriv (bellR ν Z m) s) (bellR ν Z m s) (deriv Z s) hs

/-- Where `Z s > 0`, `bellR ν Z m s` is the Faà-di-Bruno polynomial evaluated at the jet of `Z`
at `s`. -/
lemma bellR_eq_faaDiBrunoJ (ν : ℝ) {Z : ℝ → ℝ} (hZ : ContDiff ℝ (⊤ : ℕ∞) Z) (m : ℕ) (s : ℝ)
    (hs : 0 < Z s) :
    bellR ν Z m s = Commons.Geometry.Ulam.faaDiBrunoJ m ν 0
      (fun i : Fin (m + 1) => iteratedDeriv i.1 Z s) := by
  rw [bellR_rpow_spec ν hZ m s hs, Commons.Geometry.Ulam.faaDiBrunoJ_spec m ν Z s hZ hs]
  rw [mul_assoc, ← Real.rpow_add hs, show ν - (m:ℝ) + ((m:ℝ) - ν) = 0 from by ring,
    Real.rpow_zero, mul_one]
  rfl

/-! ## 7. The Bell recursion in the jet variable -/

/-- The Bell recursion `R_{m+1} = v 0 · ∇R_m(v ∘ castSucc) · (v ∘ succ) + (ν-m)·v 1·R_m(v ∘ castSucc)`
in the jet variable. -/
noncomputable def bellP (ν : ℝ) : (m : ℕ) → (Fin (m + 1) → ℝ) → ℝ
  | 0 => fun _ => 1
  | (m + 1) => fun v =>
      v 0 * (fderiv ℝ (bellP ν m) (fun i : Fin (m + 1) => v i.castSucc))
              (fun i : Fin (m + 1) => v i.succ)
        + (ν - (m : ℝ)) * v 1 * bellP ν m (fun i : Fin (m + 1) => v i.castSucc)

@[simp] lemma bellP_zero_eq (ν : ℝ) (v : Fin 1 → ℝ) : bellP ν 0 v = 1 := rfl

lemma bellP_succ_eq (ν : ℝ) (m : ℕ) (v : Fin (m + 2) → ℝ) :
    bellP ν (m + 1) v =
      v 0 * (fderiv ℝ (bellP ν m) (fun i : Fin (m + 1) => v i.castSucc))
              (fun i : Fin (m + 1) => v i.succ)
        + (ν - (m : ℝ)) * v 1 * bellP ν m (fun i : Fin (m + 1) => v i.castSucc) := rfl

/-- `bellP ν m` is a smooth function of the jet. -/
theorem bellP_contDiff (ν : ℝ) : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (bellP ν m) := by
  intro m
  induction m with
  | zero => rw [show bellP ν 0 = fun _ : Fin 1 → ℝ => (1:ℝ) from rfl]; exact contDiff_const
  | succ m ih =>
    rw [show bellP ν (m + 1) = fun v : Fin (m + 2) → ℝ =>
      v 0 * (fderiv ℝ (bellP ν m) (fun i : Fin (m + 1) => v i.castSucc))
              (fun i : Fin (m + 1) => v i.succ)
        + (ν - (m : ℝ)) * v 1 * bellP ν m (fun i : Fin (m + 1) => v i.castSucc) from rfl]
    refine ContDiff.add
      (ContDiff.mul (contDiff_apply ℝ ℝ (0 : Fin (m + 2))) ?_)
      (ContDiff.mul (ContDiff.mul contDiff_const (contDiff_apply ℝ ℝ (1 : Fin (m + 2)))) ?_)
    · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
          fderiv ℝ (bellP ν m) p.1 p.2) := ih.contDiff_fderiv_apply (by simp)
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun v : Fin (m + 2) → ℝ =>
          ((fun i : Fin (m + 1) => v i.castSucc), (fun i : Fin (m + 1) => v i.succ))) := by
        refine ContDiff.prodMk ?_ ?_
        · rw [contDiff_pi]; intro i; exact contDiff_apply ℝ ℝ _
        · rw [contDiff_pi]; intro i; exact contDiff_apply ℝ ℝ _
      exact h1.comp h2
    · exact ih.comp (by rw [contDiff_pi]; intro i; exact contDiff_apply ℝ ℝ _)

/-- `bellP` is homogeneous of degree `m` in the jet. -/
theorem bellP_smul (ν : ℝ) : ∀ m (c : ℝ) (v : Fin (m + 1) → ℝ),
    bellP ν m (fun i => c * v i) = c ^ m * bellP ν m v := by
  intro m
  induction m with
  | zero => intro c v; rw [show bellP ν 0 = fun _ : Fin 1 → ℝ => (1:ℝ) from rfl]; simp
  | succ m ih =>
    intro c v
    have hf : (fun i : Fin (m + 1) => (fun j : Fin (m + 2) => c * v j) i.castSucc)
        = (fun i : Fin (m + 1) => c * ((fun j : Fin (m + 1) => v j.castSucc) i)) := rfl
    have hg : (fun i : Fin (m + 1) => (fun j : Fin (m + 2) => c * v j) i.succ)
        = (fun i : Fin (m + 1) => c * ((fun j : Fin (m + 1) => v j.succ) i)) := rfl
    rw [bellP_succ_eq, hf, hg, bellP_succ_eq]
    have hd : ∀ x : Fin (m+1) → ℝ, DifferentiableAt ℝ (bellP ν m) x :=
      fun x => ((bellP_contDiff ν m).differentiable (by simp)).differentiableAt
    have hhom : ∀ w : Fin (m+1) → ℝ, bellP ν m (fun i => c * w i) = c^m * bellP ν m w := ih c
    rw [fderiv_smul_apply (F := bellP ν m) (m := m) (c := c) hd hhom
      (fun j : Fin (m+1) => v j.castSucc) (fun j : Fin (m+1) => v j.succ),
      ih c (fun j : Fin (m+1) => v j.castSucc)]
    rw [pow_succ']
    ring

/-- **The jet recursion computes `bellR`.**  For every smooth `Z`, evaluating the jet recursion
`bellP` at the jet of `Z` gives the base-point recursion `bellR`. -/
theorem bellP_jet (ν : ℝ) : ∀ (m : ℕ) {Z : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) Z → ∀ s : ℝ,
    bellP ν m (fun i : Fin (m + 1) => iteratedDeriv i.1 Z s) = bellR ν Z m s := by
  intro m
  induction m with
  | zero => intro Z hZ s; rw [show bellP ν 0 = fun _ : Fin 1 → ℝ => (1:ℝ) from rfl, bellR_zero_eq]
  | succ m ih =>
    intro Z hZ s
    rw [show bellP ν (m + 1) (fun i : Fin (m + 2) => iteratedDeriv i.1 Z s) =
        (fun i : Fin (m + 2) => iteratedDeriv i.1 Z s) 0 *
          (fderiv ℝ (bellP ν m) (fun i : Fin (m + 1) =>
              (fun j : Fin (m + 2) => iteratedDeriv j.1 Z s) i.castSucc))
          (fun i : Fin (m + 1) =>
              (fun j : Fin (m + 2) => iteratedDeriv j.1 Z s) i.succ)
        + (ν - (m : ℝ)) * (fun i : Fin (m + 2) => iteratedDeriv i.1 Z s) 1 *
          bellP ν m (fun i : Fin (m + 1) =>
              (fun j : Fin (m + 2) => iteratedDeriv j.1 Z s) i.castSucc) from rfl]
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_one,
      iteratedDeriv_zero, iteratedDeriv_one]
    have hjet := fed_hasDerivAt_jet hZ (m + 1) s
    have hdiff : DifferentiableAt ℝ (bellP ν m)
        (fun i : Fin (m + 1) => iteratedDeriv i.1 Z s) :=
      ((bellP_contDiff ν m).differentiable (by simp)).differentiableAt
    have hchain : (fderiv ℝ (bellP ν m) (fun i : Fin (m + 1) => iteratedDeriv i.1 Z s))
        (fun i : Fin (m + 1) => iteratedDeriv (i.1 + 1) Z s)
          = deriv (fun y : ℝ => bellP ν m (fun i : Fin (m + 1) => iteratedDeriv i.1 Z y)) s := by
      have hF : HasFDerivAt (bellP ν m)
          ((fderiv ℝ (bellP ν m)) (fun i : Fin (m + 1) => iteratedDeriv i.1 Z s))
          (fun i : Fin (m + 1) => iteratedDeriv i.1 Z s) := hdiff.hasFDerivAt
      have h := (hF.comp_hasDerivAt s hjet).deriv
      simp only [Function.comp_def] at h
      exact h.symm
    have hfun : (fun y : ℝ => bellP ν m (fun i : Fin (m + 1) => iteratedDeriv i.1 Z y))
        = bellR ν Z m := funext (fun y => ih hZ y)
    rw [hchain, hfun, ih hZ s, bellR_succ_eq]

/-! ## 8. `bellP` agrees with the Faà-di-Bruno polynomial -/

/-- **The jet recursion is the Faà-di-Bruno polynomial**, for every jet vector. -/
theorem bellP_eq_faaDiBrunoJ (ν : ℝ) : ∀ m (v : Fin (m + 1) → ℝ),
    bellP ν m v = Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 v := by
  intro m
  -- the case of a positive first coordinate
  have hpos_case : ∀ v : Fin (m + 1) → ℝ, 0 < v 0 →
      bellP ν m v = Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 v := by
    intro v hv
    have hjet : (fun i : Fin (m + 1) => iteratedDeriv i.1 (fedTaylor (m + 1) v) 0) = v :=
      funext (fun i => fedTaylor_iteratedDeriv (m + 1) v i)
    have hZ0 : 0 < fedTaylor (m + 1) v 0 := by
      rw [show fedTaylor (m + 1) v 0 = v 0 from fedTaylor_iteratedDeriv (m + 1) v 0]
      exact hv
    calc bellP ν m v
        = bellP ν m (fun i : Fin (m + 1) => iteratedDeriv i.1 (fedTaylor (m + 1) v) 0) := by
          rw [hjet]
      _ = bellR ν (fedTaylor (m + 1) v) m 0 := bellP_jet ν m (fedTaylor_contDiff (m + 1) v) 0
      _ = Commons.Geometry.Ulam.faaDiBrunoJ m ν 0
            (fun i : Fin (m + 1) => iteratedDeriv i.1 (fedTaylor (m + 1) v) 0) :=
          bellR_eq_faaDiBrunoJ ν (fedTaylor_contDiff (m + 1) v) m 0 hZ0
      _ = Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 v := by rw [hjet]
  intro v
  rcases lt_trichotomy (v 0) 0 with hlt | heq | hgt
  · -- negative first coordinate: reduce to `-v` by homogeneity
    have hpos : 0 < (fun i : Fin (m + 1) => - v i) 0 := by
      simpa using neg_pos.mpr hlt
    have ihv := hpos_case (fun i : Fin (m + 1) => - v i) hpos
    have h1 : bellP ν m (fun i : Fin (m + 1) => - v i) = (-1:ℝ) ^ m * bellP ν m v := by
      simpa using bellP_smul ν m (-1 : ℝ) v
    have h2 : Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 (fun i : Fin (m + 1) => - v i)
        = (-1:ℝ) ^ m * Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 v := by
      simpa using faaDiBrunoJ_smul m ν 0 (-1 : ℝ) v
    have key : (-1:ℝ) ^ m * bellP ν m v =
        (-1:ℝ) ^ m * Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 v := by
      rw [← h1, ihv, h2]
    exact mul_left_cancel₀ (pow_ne_zero m (by norm_num)) key
  · -- zero first coordinate: continuity
    have hcont1 : Continuous fun v : Fin (m + 1) → ℝ => bellP ν m v :=
      (bellP_contDiff ν m).continuous
    have hcont2 : Continuous fun v : Fin (m + 1) → ℝ =>
        Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 v :=
      (Work.OddVolterra.faaDiBrunoJ_contDiff_poly m ν 0).continuous
    have hclosed : IsClosed {u : Fin (m + 1) → ℝ |
        bellP ν m u = Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 u} :=
      isClosed_eq hcont1 hcont2
    let w : ℕ → (Fin (m + 1) → ℝ) :=
      fun n i => if i = 0 then v 0 + (1 / ((n : ℝ) + 1)) else v i
    have hw_pos : ∀ n, 0 < (w n) 0 := by
      intro n
      have h1 : (w n) 0 = v 0 + (1 / ((n : ℝ) + 1)) := by simp [w]
      rw [h1, heq, zero_add]
      positivity
    have hw_mem : ∀ n, w n ∈ {u : Fin (m + 1) → ℝ |
        bellP ν m u = Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 u} :=
      fun n => hpos_case (w n) (hw_pos n)
    have hw_tend : Tendsto w atTop (𝓝 v) := by
      rw [tendsto_pi_nhds]
      intro i
      by_cases hi : i = 0
      · subst hi
        have h1 : Tendsto (fun n : ℕ => v 0 + (1:ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (v 0 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [w] using h1
      · have : (fun n : ℕ => w n i) = fun _ => v i := by
          funext n; simp [w, hi]
        rw [this]; exact tendsto_const_nhds
    exact hclosed.mem_of_tendsto hw_tend (Eventually.of_forall hw_mem)
  · exact hpos_case v hgt

/-! ## 9. Part (1): the Faà-di-Bruno recursion -/

theorem faaDiBrunoJ_recursion (m : ℕ) (ν : ℝ) (v : Fin (m + 2) → ℝ) :
    Commons.Geometry.Ulam.faaDiBrunoJ (m + 1) ν 0 v =
      v 0 * (fderiv ℝ (fun u : Fin (m + 1) → ℝ => Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 u)
              (fun i : Fin (m + 1) => v i.castSucc)) (fun i : Fin (m + 1) => v i.succ)
      + (ν - (m : ℝ)) * v 1 * Commons.Geometry.Ulam.faaDiBrunoJ m ν 0
          (fun i : Fin (m + 1) => v i.castSucc) := by
  have hP : bellP ν m
      = fun u : Fin (m + 1) → ℝ => Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 u :=
    funext (fun u => bellP_eq_faaDiBrunoJ ν m u)
  rw [← bellP_eq_faaDiBrunoJ ν (m + 1) v, bellP_succ_eq]
  simp only [hP, bellP_eq_faaDiBrunoJ ν m (fun i : Fin (m + 1) => v i.castSucc)]

/-! ## 10. Part (2): the manifest numerator `J1M` -/

/-- The recursion in the base-point variable attached to `Rnu`.  Same content as
`KernelExt.Rnu_succ_apply`, re-derived here to avoid importing the window layer. -/
lemma Rnu_recursion (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (a σ t : ℝ) :
    Work.OddVolterra.KernelExt.Rnu ν h init (m + 1) (a, σ, t) =
      Work.OddVolterra.KernelExt.Zrad h (a, σ, t) *
        deriv (fun a' : ℝ => Work.OddVolterra.KernelExt.Rnu ν h init m (a', σ, t)) a
      + (ν - (m : ℝ)) *
        deriv (fun a' : ℝ => Work.OddVolterra.KernelExt.Zrad h (a', σ, t)) a *
        Work.OddVolterra.KernelExt.Rnu ν h init m (a, σ, t) := by
  have hF : DifferentiableAt ℝ (Work.OddVolterra.KernelExt.Rnu ν h init m) (a, σ, t) :=
    (((Work.OddVolterra.KernelExt.Rnu_contDiff_aux ν hh hinit m).contDiffAt).differentiableAt
      (by simp))
  have hZ : DifferentiableAt ℝ (Work.OddVolterra.KernelExt.Zrad h) (a, σ, t) :=
    (((Work.OddVolterra.KernelExt.Zrad_contDiff_aux hh).contDiffAt).differentiableAt (by simp))
  rw [Work.OddVolterra.KernelExt.Rnu]
  beta_reduce
  rw [← (Work.OddVolterra.KernelExt.hasDerivAt_section (a, σ, t) hF).deriv,
    ← (Work.OddVolterra.KernelExt.hasDerivAt_section (a, σ, t) hZ).deriv]

/-- **`Rnu` with `init ≡ 1` is the Faà-di-Bruno polynomial at the jet of the radicand**,
for *every* `a σ t` (no order condition). -/
theorem Rnu_eq_faaDiBrunoJ_jet (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ∀ m (a σ t : ℝ),
      Work.OddVolterra.KernelExt.Rnu ν h (fun _ => (1 : ℝ)) m (a, σ, t) =
        Commons.Geometry.Ulam.faaDiBrunoJ m ν 0
          (fun i : Fin (m + 1) =>
            iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a) := by
  intro m
  induction m with
  | zero =>
    intro a σ t
    rw [show Work.OddVolterra.KernelExt.Rnu ν h (fun _ => (1:ℝ)) 0 (a, σ, t) = 1 from rfl,
      faaDiBrunoJ_zero]
  | succ m ih =>
    intro a σ t
    have hZs : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) :=
      (Work.OddVolterra.KernelExt.Zrad_contDiff_aux hh).comp (by fun_prop)
    rw [Rnu_recursion ν hh contDiff_const m a σ t]
    -- replace the `a`-section of `Rnu … m` by `bellP ν m ∘ jet`
    have hsec : (fun s : ℝ => Work.OddVolterra.KernelExt.Rnu ν h (fun _ => (1:ℝ)) m (s, σ, t))
        = fun s : ℝ => bellP ν m
            (fun i : Fin (m + 1) =>
              iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) s) := by
      funext s
      rw [ih s σ t, bellP_eq_faaDiBrunoJ ν m]
    rw [hsec]
    -- chain rule: the derivative of `bellP ν m ∘ jet` is `fderiv` applied to the shifted jet
    have hjet := fed_hasDerivAt_jet hZs (m + 1) a
    have hdiff : DifferentiableAt ℝ (bellP ν m)
        (fun i : Fin (m + 1) =>
          iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a) :=
      ((bellP_contDiff ν m).differentiable (by simp)).differentiableAt
    have hchain : deriv (fun s : ℝ => bellP ν m
          (fun i : Fin (m + 1) =>
            iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) s)) a
        = (fderiv ℝ (bellP ν m)
            (fun i : Fin (m + 1) =>
              iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a))
          (fun i : Fin (m + 1) =>
            iteratedDeriv (i.1 + 1) (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a) := by
      have hF : HasFDerivAt (bellP ν m)
          ((fderiv ℝ (bellP ν m))
            (fun i : Fin (m + 1) =>
              iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a))
          (fun i : Fin (m + 1) =>
            iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a) :=
        hdiff.hasFDerivAt
      exact (hF.comp_hasDerivAt a hjet).deriv
    rw [hchain]
    have hRm : Work.OddVolterra.KernelExt.Rnu ν h (fun _ => (1:ℝ)) m (a, σ, t)
        = bellP ν m (fun i : Fin (m + 1) =>
            iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a) := by
      rw [ih a σ t, bellP_eq_faaDiBrunoJ ν m]
    have hZ0 : Work.OddVolterra.KernelExt.Zrad h (a, σ, t)
        = iteratedDeriv 0 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a := by
      rw [iteratedDeriv_zero]
    have hZ1 : deriv (fun a' : ℝ => Work.OddVolterra.KernelExt.Zrad h (a', σ, t)) a
        = iteratedDeriv 1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a := by
      rw [iteratedDeriv_one]
    rw [hRm, hZ0, hZ1, ← bellP_eq_faaDiBrunoJ ν (m + 1),
      bellP_succ_eq ν m (fun i : Fin (m + 2) =>
        iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a)]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_castSucc, Fin.val_succ]

/-! ## 11. The main theorem -/

/-- **The Faà-di-Bruno recursion for `faaDiBrunoJ`, plus its use for the manifest numerator
`J1M`.**

Part (1): the Faà-di-Bruno polynomial `faaDiBrunoJ m ν 0 v` of `Commons.Geometry.Ulam` satisfies the
classical recursion, as a polynomial identity in the jet vector `v : Fin (m+2) → ℝ`:

`faaDiBrunoJ (m+1) ν 0 v =
   v 0 * (fderiv ℝ (fun u : Fin (m+1) → ℝ => faaDiBrunoJ m ν 0 u) (fun i => v i.castSucc))
            (fun i => v i.succ)
   + (ν - m) * v 1 * faaDiBrunoJ m ν 0 (fun i => v i.castSucc)`

Part (2): consequently, for every `n`, every smooth `h`, and *all* `a σ t : ℝ` (no order
condition),

`J1M n h a σ t = faaDiBrunoJ (n+1) ((n:ℝ)+1/2) 0 (fun i : Fin (n+2) =>
   iteratedDeriv i.1 (fun x : ℝ => KernelExt.Zrad h (x, σ, t)) a)`. -/
theorem fed_faaDiBruno_recursion (m : ℕ) (ν : ℝ) (v : Fin (m + 2) → ℝ) :
    (Commons.Geometry.Ulam.faaDiBrunoJ (m + 1) ν 0 v =
      v 0 * (fderiv ℝ (fun u : Fin (m + 1) → ℝ => Commons.Geometry.Ulam.faaDiBrunoJ m ν 0 u)
              (fun i : Fin (m + 1) => v i.castSucc)) (fun i : Fin (m + 1) => v i.succ)
      + (ν - (m : ℝ)) * v 1 * Commons.Geometry.Ulam.faaDiBrunoJ m ν 0
          (fun i : Fin (m + 1) => v i.castSucc)) ∧
    (∀ (n : ℕ) (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (a σ t : ℝ),
      Work.OddVolterra.KernelExt.J1M n h a σ t =
        Commons.Geometry.Ulam.faaDiBrunoJ (n + 1) ((n : ℝ) + 1 / 2) 0
          (fun i : Fin (n + 2) =>
            iteratedDeriv i.1 (fun x : ℝ => Work.OddVolterra.KernelExt.Zrad h (x, σ, t)) a)) := by
  refine ⟨faaDiBrunoJ_recursion m ν v, fun n h hh a σ t => ?_⟩
  exact Rnu_eq_faaDiBrunoJ_jet ((n : ℝ) + 1 / 2) hh (n + 1) a σ t

end

end Work.Window
