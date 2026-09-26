/-
# The location of the poles of the kernels (CKMRV Theorem 4.9(1))

Theorem 4.9(1) of CKMRV states that, for fixed `z`, the poles of `τ ↦ K_±(τ,z)` are simple
and *contained in the `SL(2,ℤ)`-orbit of `z`*.  The containment half is the statement that
`τ ↦ K_±(τ,z)` is holomorphic at every `τ₀` with `j(τ₀) ≠ j(z)` (and `j(τ₀) = j(z)` is
equivalent to `τ₀ ∈ SL(2,ℤ)·z`).  This file proves exactly that, for `K_±`, `K` and `K̂`, in
*both* variables:

* `Work.Residues.mdifferentiableAt_Kfun_fst`, `..._Kfun_snd` : `τ ↦ K^{(d)}(τ,z)` (resp.
  `ζ ↦ K^{(d)}(z,ζ)`) is holomorphic at every point with `j ≠ j`;
* the same for `KPlus`, `KMinus` and `Khat`.

The proof is the algebraic identity `K = K^{Clear}/(Δ(w)Δ(v)^e (j(w)-j(v)))` off the diagonal
(`Work.Kernels.ClearLink.KPlusClear_eq_smul`) together with the holomorphy of the *cleared*
kernel in each variable (`Work.Kernels.KernelGrowth.KPlusClear_growth_tau/_growth_z`) and the
non-vanishing of `Δ`.  Together with the residue computations of
`Work.Residues.ResidueKernel`/`ResidueTheorem`/`ResidueSecondVariable` (which show that the
points of the orbit *are* poles with the stated residues) this is the pole statement of
Theorem 4.9(1); the converse ("every orbit point carries a pole") is the non-vanishing of the
cleared kernel at the diagonal, available for the shifts `T`, `S` and `TS` from
`Work.Residues.KPlusClear_T/TS/diag`.
-/
import Mathlib
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Residues.ResidueOrbit

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-- `j` is holomorphic. -/
lemma mdifferentiableAt_jInvariantFun (τ : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) jInvariantFun τ := by
  have h : jInvariantFun = fun σ : ℍ => E4Fun σ ^ 3 / DeltaFun σ := rfl
  rw [h]
  exact ((ClassicalFacts.E4Fun_mem_InP.1 τ).pow 3).div
    (ClassicalFacts.DeltaFun_mem_InP.1 τ) (ClassicalFacts.DeltaFun_ne_zero τ)

/-- `j` is continuous. -/
lemma continuous_jInvariantFun : Continuous jInvariantFun := by
  have h : jInvariantFun = fun σ : ℍ => E4Fun σ ^ 3 / DeltaFun σ := rfl
  rw [h]
  exact (ClassicalFacts.E4Fun_mem_InP.1.continuous).pow 3 |>.div
    ClassicalFacts.DeltaFun_mem_InP.1.continuous (fun w => ClassicalFacts.DeltaFun_ne_zero w)

/-! ## The kernels divided by their cleared forms -/

/-- Off the diagonal, `K_+` is the cleared kernel divided by `Δ(w)Δ(v)^e(j(w)-j(v))`. -/
lemma KPlus_eq_clear_div (d : ℕ) (hd : d = 8 ∨ d = 24) {w v : ℍ}
    (h : jInvariantFun w ≠ jInvariantFun v) :
    KPlus d w v = KPlusClear d w v
      / (DeltaFun w * DeltaFun v ^ dpow d * (jInvariantFun w - jInvariantFun v)) := by
  have hD : DeltaFun w * DeltaFun v ^ dpow d * (jInvariantFun w - jInvariantFun v) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero w)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero v))) (sub_ne_zero.mpr h)
  rw [ClearLink.KPlusClear_eq_smul d hd w v h, growthPrefactor, eq_div_iff]
  · simp only [dpow]
    ring
  · exact hD

/-- Off the diagonal, `K_-` is the cleared kernel divided by `Δ(w)Δ(v)^e(j(w)-j(v))`. -/
lemma KMinus_eq_clear_div (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) {w v : ℍ}
    (h : jInvariantFun w ≠ jInvariantFun v) :
    KMinus ℓ d w v = KMinusClear ℓ d w v
      / (DeltaFun w * DeltaFun v ^ dpow d * (jInvariantFun w - jInvariantFun v)) := by
  have hD : DeltaFun w * DeltaFun v ^ dpow d * (jInvariantFun w - jInvariantFun v) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero w)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero v))) (sub_ne_zero.mpr h)
  rw [ClearLink.KMinusClear_eq_smul ℓ d hd w v h, growthPrefactor, eq_div_iff]
  · simp only [dpow]
    ring
  · exact hD

/-! ## Holomorphy off the diagonal -/

/-- **The poles of `τ ↦ K_+^{(d)}(τ,z)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_KPlus_fst (d : ℕ) (hd : d = 8 ∨ d = 24) (z τ₀ : ℍ)
    (h : jInvariantFun τ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => KPlus d τ z) τ₀ := by
  have hne : ∀ᶠ τ in 𝓝 τ₀, jInvariantFun τ - jInvariantFun z ≠ 0 :=
    ((continuous_jInvariantFun.sub continuous_const).continuousAt.tendsto.eventually_ne
      (sub_ne_zero.mpr h))
  have hcongr : (fun τ : ℍ => KPlus d τ z) =ᶠ[𝓝 τ₀]
      (fun τ : ℍ => KPlusClear d τ z
        / (DeltaFun τ * DeltaFun z ^ dpow d * (jInvariantFun τ - jInvariantFun z))) := by
    filter_upwards [hne] with τ hτ
    exact KPlus_eq_clear_div d hd (sub_ne_zero.mp hτ)
  refine hcongr.mdifferentiableAt_iff.mpr ?_
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => KPlusClear d τ z) τ₀ :=
    (KernelGrowth.KPlusClear_growth_tau d hd z).1 τ₀
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => DeltaFun τ * DeltaFun z ^ dpow d
        * (jInvariantFun τ - jInvariantFun z)) τ₀ :=
    ((ClassicalFacts.DeltaFun_mem_InP.1 τ₀).mul mdifferentiableAt_const).mul
      ((mdifferentiableAt_jInvariantFun τ₀).sub mdifferentiableAt_const)
  exact h1.div h2 (by
    exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ₀)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))) (sub_ne_zero.mpr h))

/-- **The poles of `ζ ↦ K_+^{(d)}(z,ζ)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_KPlus_snd (d : ℕ) (hd : d = 8 ∨ d = 24) (z ζ₀ : ℍ)
    (h : jInvariantFun ζ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => KPlus d z ζ) ζ₀ := by
  have hne : ∀ᶠ ζ in 𝓝 ζ₀, jInvariantFun z - jInvariantFun ζ ≠ 0 :=
    ((continuous_const.sub continuous_jInvariantFun).continuousAt.tendsto.eventually_ne
      (sub_ne_zero.mpr h.symm))
  have hcongr : (fun ζ : ℍ => KPlus d z ζ) =ᶠ[𝓝 ζ₀]
      (fun ζ : ℍ => KPlusClear d z ζ
        / (DeltaFun z * DeltaFun ζ ^ dpow d * (jInvariantFun z - jInvariantFun ζ))) := by
    filter_upwards [hne] with ζ hζ
    exact KPlus_eq_clear_div d hd (w := z) (v := ζ) (sub_ne_zero.mp hζ)
  refine hcongr.mdifferentiableAt_iff.mpr ?_
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => KPlusClear d z ζ) ζ₀ :=
    (KernelGrowth.KPlusClear_growth_z d hd z).1 ζ₀
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun ζ : ℍ => DeltaFun z * DeltaFun ζ ^ dpow d
        * (jInvariantFun z - jInvariantFun ζ)) ζ₀ :=
    (mdifferentiableAt_const.mul ((ClassicalFacts.DeltaFun_mem_InP.1 ζ₀).pow _)).mul
      (mdifferentiableAt_const.sub (mdifferentiableAt_jInvariantFun ζ₀))
  exact h1.div h2 (by
    exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero ζ₀))) (sub_ne_zero.mpr h.symm))

/-- **The poles of `τ ↦ K_-^{(d)}(τ,z)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_KMinus_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z τ₀ : ℍ) (h : jInvariantFun τ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => KMinus ℓ d τ z) τ₀ := by
  have hne : ∀ᶠ τ in 𝓝 τ₀, jInvariantFun τ - jInvariantFun z ≠ 0 :=
    ((continuous_jInvariantFun.sub continuous_const).continuousAt.tendsto.eventually_ne
      (sub_ne_zero.mpr h))
  have hcongr : (fun τ : ℍ => KMinus ℓ d τ z) =ᶠ[𝓝 τ₀]
      (fun τ : ℍ => KMinusClear ℓ d τ z
        / (DeltaFun τ * DeltaFun z ^ dpow d * (jInvariantFun τ - jInvariantFun z))) := by
    filter_upwards [hne] with τ hτ
    exact KMinus_eq_clear_div ℓ d hd (sub_ne_zero.mp hτ)
  refine hcongr.mdifferentiableAt_iff.mpr ?_
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => KMinusClear ℓ d τ z) τ₀ :=
    (KernelGrowth.KMinusClear_growth_tau ℓ d hd z).1 τ₀
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => DeltaFun τ * DeltaFun z ^ dpow d
        * (jInvariantFun τ - jInvariantFun z)) τ₀ :=
    ((ClassicalFacts.DeltaFun_mem_InP.1 τ₀).mul mdifferentiableAt_const).mul
      ((mdifferentiableAt_jInvariantFun τ₀).sub mdifferentiableAt_const)
  exact h1.div h2 (by
    exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ₀)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))) (sub_ne_zero.mpr h))

/-- **The poles of `ζ ↦ K_-^{(d)}(z,ζ)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_KMinus_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z ζ₀ : ℍ) (h : jInvariantFun ζ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => KMinus ℓ d z ζ) ζ₀ := by
  have hne : ∀ᶠ ζ in 𝓝 ζ₀, jInvariantFun z - jInvariantFun ζ ≠ 0 :=
    ((continuous_const.sub continuous_jInvariantFun).continuousAt.tendsto.eventually_ne
      (sub_ne_zero.mpr h.symm))
  have hcongr : (fun ζ : ℍ => KMinus ℓ d z ζ) =ᶠ[𝓝 ζ₀]
      (fun ζ : ℍ => KMinusClear ℓ d z ζ
        / (DeltaFun z * DeltaFun ζ ^ dpow d * (jInvariantFun z - jInvariantFun ζ))) := by
    filter_upwards [hne] with ζ hζ
    exact KMinus_eq_clear_div ℓ d hd (w := z) (v := ζ) (sub_ne_zero.mp hζ)
  refine hcongr.mdifferentiableAt_iff.mpr ?_
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => KMinusClear ℓ d z ζ) ζ₀ :=
    (KernelGrowth.KMinusClear_growth_z ℓ d hd z).1 ζ₀
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun ζ : ℍ => DeltaFun z * DeltaFun ζ ^ dpow d
        * (jInvariantFun z - jInvariantFun ζ)) ζ₀ :=
    (mdifferentiableAt_const.mul ((ClassicalFacts.DeltaFun_mem_InP.1 ζ₀).pow _)).mul
      (mdifferentiableAt_const.sub (mdifferentiableAt_jInvariantFun ζ₀))
  exact h1.div h2 (by
    exact mul_ne_zero (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero z)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero ζ₀))) (sub_ne_zero.mpr h.symm))

/-- **The poles of `τ ↦ K^{(d)}(τ,z)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_Kfun_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z τ₀ : ℍ) (h : jInvariantFun τ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Kfun ℓ d τ z) τ₀ := by
  have h1 := mdifferentiableAt_KPlus_fst d hd z τ₀ h
  have h2 := mdifferentiableAt_KMinus_fst ℓ d hd z τ₀ h
  have hfun : (fun τ : ℍ => Kfun ℓ d τ z)
      = (fun τ : ℍ => (1 / 2 : ℂ) * KPlus d τ z)
        + (fun τ : ℍ => (1 / 2 : ℂ) * KMinus ℓ d τ z) := by
    funext τ; rw [Kfun_eq]; simp only [Pi.add_apply]; ring
  rw [hfun]
  exact (mdifferentiableAt_const.mul h1).add (mdifferentiableAt_const.mul h2)

/-- **The poles of `ζ ↦ K^{(d)}(z,ζ)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_Kfun_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z ζ₀ : ℍ) (h : jInvariantFun ζ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => Kfun ℓ d z ζ) ζ₀ := by
  have h1 := mdifferentiableAt_KPlus_snd d hd z ζ₀ h
  have h2 := mdifferentiableAt_KMinus_snd ℓ d hd z ζ₀ h
  have hfun : (fun ζ : ℍ => Kfun ℓ d z ζ)
      = (fun ζ : ℍ => (1 / 2 : ℂ) * KPlus d z ζ)
        + (fun ζ : ℍ => (1 / 2 : ℂ) * KMinus ℓ d z ζ) := by
    funext ζ; rw [Kfun_eq]; simp only [Pi.add_apply]; ring
  rw [hfun]
  exact (mdifferentiableAt_const.mul h1).add (mdifferentiableAt_const.mul h2)

/-- **The poles of `τ ↦ K̂^{(d)}(τ,z)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_Khat_fst (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z τ₀ : ℍ) (h : jInvariantFun τ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Khat ℓ d τ z) τ₀ := by
  have h1 := mdifferentiableAt_KPlus_fst d hd z τ₀ h
  have h2 := mdifferentiableAt_KMinus_fst ℓ d hd z τ₀ h
  have hfun : (fun τ : ℍ => Khat ℓ d τ z)
      = (fun τ : ℍ => (1 / 2 : ℂ) * KPlus d τ z)
        + (fun τ : ℍ => (-(1 / 2) : ℂ) * KMinus ℓ d τ z) := by
    funext τ; rw [Khat_eq]; simp only [Pi.add_apply]; ring
  rw [hfun]
  exact (mdifferentiableAt_const.mul h1).add (mdifferentiableAt_const.mul h2)

/-- **The poles of `ζ ↦ K̂^{(d)}(z,ζ)` are contained in `{j = j(z)}`.** -/
theorem mdifferentiableAt_Khat_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z ζ₀ : ℍ) (h : jInvariantFun ζ₀ ≠ jInvariantFun z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => Khat ℓ d z ζ) ζ₀ := by
  have h1 := mdifferentiableAt_KPlus_snd d hd z ζ₀ h
  have h2 := mdifferentiableAt_KMinus_snd ℓ d hd z ζ₀ h
  have hfun : (fun ζ : ℍ => Khat ℓ d z ζ)
      = (fun ζ : ℍ => (1 / 2 : ℂ) * KPlus d z ζ)
        + (fun ζ : ℍ => (-(1 / 2) : ℂ) * KMinus ℓ d z ζ) := by
    funext ζ; rw [Khat_eq]; simp only [Pi.add_apply]; ring
  rw [hfun]
  exact (mdifferentiableAt_const.mul h1).add (mdifferentiableAt_const.mul h2)

/-! ## The orbit points *are* poles

The residue theorems show that at `τ = δz` the slashed kernel has residue proportional to
`φ_±`.  Taking the group-algebra element `single δ`, so that
`slash k (single δ · single δ⁻¹) = slash k 1 = id`, identifies the residue of the kernel
`K_±(·,z)` itself at `δz`, and a holomorphic function has residue `0`: hence every `δz` with
`φ_±(δ) ≠ 0` is a genuine pole.  Together with the containment theorems above this is
Theorem 4.9(1) for `K_±` in the `τ`-variable. -/

/-- `single δ * single δ⁻¹ = 1`. -/
lemma single_mul_single_inv (δ : SL(2,ℤ)) :
    MonoidAlgebra.single δ (1 : ℂ) * MonoidAlgebra.single δ⁻¹ (1 : ℂ) = (1 : R) := by
  rw [MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul, ← MonoidAlgebra.one_def]

/-- **The orbit point `δz` is a pole of `K_+` whenever `φ_+(δ) ≠ 0`.** -/
theorem not_mdifferentiableAt_KPlus_orbit (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ)
    (hne : jprime z ≠ 0) (δ : SL(2,ℤ))
    (hφ : phiPlus (MonoidAlgebra.single δ (1 : ℂ)) ≠ 0) :
    ¬ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => KPlus d τ z) (δ • z) := by
  intro hdiff
  have h0 : HasResidue (fun τ : ℍ => KPlus d τ z) (δ • z) 0 :=
    hasResidue_of_mdifferentiableAt hdiff
  have h1 := hasResidue_slash_KPlus_orbit d hd z hne δ (MonoidAlgebra.single δ (1 : ℂ))
  rw [single_mul_single_inv, slash_one] at h1
  have hC : (1 : ℂ) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero one_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hval : (jFun δ (z : ℂ)) ^ ((d : ℤ) / 2 - 2)
      * (-(1 / (2 * Real.pi)) * phiPlus (MonoidAlgebra.single δ (1 : ℂ))) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (jFun_ne_zero δ z)) (mul_ne_zero (neg_ne_zero.mpr hC) hφ)
  exact hval (h0.unique h1).symm

/-- **The orbit point `δz` is a pole of `K_-` whenever `φ_-(δ) ≠ 0`.** -/
theorem not_mdifferentiableAt_KMinus_orbit (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : ℍ) (hne : jprime z ≠ 0) (δ : SL(2,ℤ))
    (hφ : phiMinus (MonoidAlgebra.single δ (1 : ℂ)) ≠ 0) :
    ¬ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => KMinus ℓ d τ z) (δ • z) := by
  intro hdiff
  have h0 : HasResidue (fun τ : ℍ => KMinus ℓ d τ z) (δ • z) 0 :=
    hasResidue_of_mdifferentiableAt hdiff
  have h1 := hasResidue_slash_KMinus_orbit ℓ d hd z hne δ (MonoidAlgebra.single δ (1 : ℂ))
  rw [single_mul_single_inv, slash_one] at h1
  have hC : (1 : ℂ) / (2 * Real.pi) ≠ 0 :=
    div_ne_zero one_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hval : (jFun δ (z : ℂ)) ^ ((d : ℤ) / 2 - 2)
      * (-(1 / (2 * Real.pi)) * phiMinus (MonoidAlgebra.single δ (1 : ℂ))) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (jFun_ne_zero δ z)) (mul_ne_zero (neg_ne_zero.mpr hC) hφ)
  exact hval (h0.unique h1).symm

end Work.Residues
