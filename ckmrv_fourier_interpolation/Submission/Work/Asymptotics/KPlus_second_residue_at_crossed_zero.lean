/-
# The second-variable residue of `K_+` at the crossed orbit points is zero

For `d = 8, 24` and `τ` in the funnel (`3 ≤ Im τ`), the function

  `ζ ↦ K_+^{(d)}((T*S) • τ, ζ)`

has residue `0` at `ζ = τ - 1`, and `ζ ↦ K_+^{(d)}((T⁻¹*S) • τ, ζ)` has residue `0` at
`ζ = τ + 1`.  These are the two "crossed" translate poles of CKMRV §5.2 (the pairs
`(F₂|^τ TS, TS)` and `(F₂|^τ T⁻¹S, T⁻¹S)`), whose removability is what makes the contour shift
residue-free.

The proof does *not* compute the second-variable functional.  Instead it uses the two
`HasResidue`-formulae

  `Res_{τ'=w} K_+(τ',z) = AfunPlus d z w / j'(w)`  (`hasResidue_of_cleared`, first variable),
  `Res_{ζ=z} K_+(w,ζ) = -AfunPlus d z w / j'(z)` (`hasResidue_of_cleared`, second variable),

so that both residues are multiples of the same number `AfunPlus d z w`, together with the
first-variable *orbit* residue theorem `hasResidue_slash_KPlus_orbit'`: for `δ • z = w` the
first-variable residue equals `j(δ,z)^{d/2-2} · (-(1/2π)) · φ_+(single δ 1)`.  Hence it
suffices that `φ_+` vanishes on the crossed elements `T*S*T` resp. `T⁻¹*S*T⁻¹`, which is the
group-algebra statement `Work.Residues.phiPlus_crossed_translates_eq_zero`.
-/
import Mathlib
import Submission.Work.Residues.ResidueOrbit
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Residues.phiPlus_crossed_translates_eq_zero
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc

noncomputable section

open UpperHalfPlane ModularGroup Matrix Filter
open scoped MatrixGroups Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## Elementary translations -/

lemma one_vadd_neg_one_vadd' (z : ℍ) : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z := by
  rw [← add_vadd, add_neg_cancel, zero_vadd]

lemma E4Fun_vadd_neg_one' (z : ℍ) : E4Fun ((-1 : ℝ) +ᵥ z) = E4Fun z := by
  have h := KernelFacts.E4Fun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [one_vadd_neg_one_vadd'] at h
  exact h.symm

lemma E6Fun_vadd_neg_one' (z : ℍ) : E6Fun ((-1 : ℝ) +ᵥ z) = E6Fun z := by
  have h := KernelFacts.E6Fun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [one_vadd_neg_one_vadd'] at h
  exact h.symm

lemma jInvariantFun_vadd_neg_one' (z : ℍ) :
    jInvariantFun ((-1 : ℝ) +ᵥ z) = jInvariantFun z := by
  have h := KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ z)
  rw [one_vadd_neg_one_vadd'] at h
  exact h.symm

/-! ## Non-vanishing of `j'` at the four orbit points -/

lemma E4Fun_ne_zero_of_three_le_im (τ : ℍ) (hτ : 3 ≤ τ.im) : E4Fun τ ≠ 0 := by
  intro h
  have hb := Work.FunnelNumerics.E4_funnel_bounds.2 τ hτ
  rw [h, norm_zero] at hb
  norm_num at hb

lemma E6Fun_ne_zero_of_three_le_im (τ : ℍ) (hτ : 3 ≤ τ.im) : E6Fun τ ≠ 0 :=
  SpikeCircle.E6Fun_ne_zero_im τ (by linarith)

lemma jprime_ne_zero_of_three_le_im (τ : ℍ) (hτ : 3 ≤ τ.im) :
    Work.Residues.jprime τ ≠ 0 := by
  rw [Work.Residues.jprime_ne_zero_iff]
  exact mul_ne_zero (E4Fun_ne_zero_of_three_le_im τ hτ) (E6Fun_ne_zero_of_three_le_im τ hτ)

/-- `E₄` is a modular form of weight `4`: `E₄(T•(S•z)) = z⁴ E₄ z`. -/
lemma E4Fun_TS_smul (z : ℍ) :
    E4Fun ((ModularGroup.T * ModularGroup.S) • z) = (z : ℂ) ^ 4 * E4Fun z := by
  rw [mul_smul, UpperHalfPlane.modular_T_smul, KernelFacts.E4Fun_vadd_one,
    Work.Residues.E4Fun_S_smul]

lemma E6Fun_TS_smul (z : ℍ) :
    E6Fun ((ModularGroup.T * ModularGroup.S) • z) = (z : ℂ) ^ 6 * E6Fun z := by
  rw [mul_smul, UpperHalfPlane.modular_T_smul, KernelFacts.E6Fun_vadd_one,
    Work.Residues.E6Fun_S_smul]

lemma E4Fun_TinvS_smul (z : ℍ) :
    E4Fun ((ModularGroup.T⁻¹ * ModularGroup.S) • z) = (z : ℂ) ^ 4 * E4Fun z := by
  rw [mul_smul, Work.Residues.T_inv_smul_eq, E4Fun_vadd_neg_one', Work.Residues.E4Fun_S_smul]

lemma E6Fun_TinvS_smul (z : ℍ) :
    E6Fun ((ModularGroup.T⁻¹ * ModularGroup.S) • z) = (z : ℂ) ^ 6 * E6Fun z := by
  rw [mul_smul, Work.Residues.T_inv_smul_eq, E6Fun_vadd_neg_one', Work.Residues.E6Fun_S_smul]

lemma jprime_TS_smul_ne_zero (τ : ℍ) (hτ : 3 ≤ τ.im) :
    Work.Residues.jprime ((ModularGroup.T * ModularGroup.S) • τ) ≠ 0 := by
  rw [Work.Residues.jprime_ne_zero_iff, E4Fun_TS_smul, E6Fun_TS_smul]
  have hz : (τ : ℂ) ≠ 0 := τ.ne_zero
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ hz) (E4Fun_ne_zero_of_three_le_im τ hτ))
    (mul_ne_zero (pow_ne_zero _ hz) (E6Fun_ne_zero_of_three_le_im τ hτ))

lemma jprime_TinvS_smul_ne_zero (τ : ℍ) (hτ : 3 ≤ τ.im) :
    Work.Residues.jprime ((ModularGroup.T⁻¹ * ModularGroup.S) • τ) ≠ 0 := by
  rw [Work.Residues.jprime_ne_zero_iff, E4Fun_TinvS_smul, E6Fun_TinvS_smul]
  have hz : (τ : ℂ) ≠ 0 := τ.ne_zero
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ hz) (E4Fun_ne_zero_of_three_le_im τ hτ))
    (mul_ne_zero (pow_ne_zero _ hz) (E6Fun_ne_zero_of_three_le_im τ hτ))

/-! ## The residue at an orbit point of the base point, in the second variable -/

/-- **The crossed residue vanishes whenever `φ_+` does.**  Let `δ • z = w` and suppose that
`j'` does not vanish at `z` or at `w`, that `j w = j z`, and that `φ_+(single δ 1) = 0`.  Then
the second-variable residue of `K_+^{(d)}(w, ·)` at `z` vanishes.

Indeed, the first-variable orbit theorem gives
`Res_{τ'=w} K_+(τ',z) = j(δ,z)^{d/2-2}·(-(1/2π))·φ_+(single δ 1) = 0`, while the cleared
identities of `Work.Residues.hasResidue_of_cleared` express that same residue as
`AfunPlus d z w / j'(w)` and the second-variable residue as `-AfunPlus d z w / j'(z)`; hence
both vanish. -/
theorem hasResidue_KPlus_second_of_orbit_eq_zero (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z w : ℍ) (δ : SL(2,ℤ)) (hδ : δ • z = w) (hz : Work.Residues.jprime z ≠ 0)
    (hw : Work.Residues.jprime w ≠ 0) (hj : jInvariantFun w = jInvariantFun z)
    (hphi : Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ)) = 0) :
    Work.Residues.HasResidue (fun ζ : ℍ => KPlus d w ζ) z 0 := by
  -- Step 1: the first-variable orbit residue theorem
  have horb : Work.Residues.HasResidue (fun τ' : ℍ => KPlus d τ' z) w 0 := by
    have h := Work.Residues.hasResidue_slash_KPlus_orbit' d hd z hz δ (1 : R)
    have hval : (jFun δ (z : ℂ)) ^ ((d : ℤ) / 2 - 2) *
        (-(1 / (2 * Real.pi)) * Work.Residues.phiPlus ((1 : R) *
          MonoidAlgebra.single δ (1 : ℂ))) = 0 := by
      rw [one_mul, hphi]
      ring
    simpa only [slash_one, hval, hδ] using h
  -- Step 2: identify the first-variable residue with `AfunPlus d z w / j' w`
  have hclear₁ : Work.Residues.HasResidue (fun τ' : ℍ => KPlus d τ' z) w
      (Work.Residues.AfunPlus d z w / Work.Residues.jprime w) := by
    refine Work.Residues.hasResidue_of_cleared (f := fun τ' : ℍ => KPlus d τ' z)
      (A := Work.Residues.AfunPlus d z) (z := z) (z₀ := w) (c := Work.Residues.jprime w)
      (Work.Residues.mdifferentiableAt_AfunPlus d hd z w) hj
      (Work.Residues.tendsto_slope_jprime w) hw ?_
    filter_upwards [self_mem_nhdsWithin,
      (Work.Residues.tendsto_slope_jprime w).eventually (eventually_ne_nhds hw)]
      with τ' hτ' hτ'ne
    have hslope : (jInvariantFun τ' - jInvariantFun w) / ((τ' : ℂ) - (w : ℂ)) ≠ 0 := hτ'ne
    have hne : jInvariantFun τ' - jInvariantFun w ≠ 0 := by
      intro h0
      exact hslope (by rw [h0, zero_div])
    have hne' : jInvariantFun τ' - jInvariantFun z ≠ 0 := by
      simpa only [hj] using hne
    exact Work.Residues.mul_slope_eq_AfunPlus d hd z τ' (sub_ne_zero.mp hne')
  -- Step 3: hence `AfunPlus d z w = 0`
  have hA0 : Work.Residues.AfunPlus d z w = 0 := by
    have h := (horb.unique hclear₁).symm
    rcases div_eq_zero_iff.mp h with h0 | h0
    · exact h0
    · exact absurd h0 hw
  -- Step 4: the second-variable residue is `-AfunPlus d z w / j' z = 0`
  have hmain : Work.Residues.HasResidue (fun ζ : ℍ => KPlus d w ζ) z
      ((-Work.Residues.AfunPlus d z w) / Work.Residues.jprime z) := by
    refine Work.Residues.hasResidue_of_cleared (f := fun ζ : ℍ => KPlus d w ζ)
      (A := fun ζ : ℍ => -Work.Residues.AfunPlus d ζ w) (z := w) (z₀ := z)
      (c := Work.Residues.jprime z)
      ((Work.Residues.mdifferentiableAt_AfunPlus_snd d hd w z).neg) hj.symm
      (Work.Residues.tendsto_slope_jprime z) hz ?_
    filter_upwards [self_mem_nhdsWithin,
      (Work.Residues.tendsto_slope_jprime z).eventually (eventually_ne_nhds hz)]
      with ζ hζ hζne
    have hslope : (jInvariantFun ζ - jInvariantFun z) / ((ζ : ℂ) - (z : ℂ)) ≠ 0 := hζne
    have hne : jInvariantFun ζ - jInvariantFun z ≠ 0 := by
      intro h0
      exact hslope (by rw [h0, zero_div])
    have hne' : jInvariantFun ζ - jInvariantFun w ≠ 0 := by
      rw [hj]
      exact hne
    exact Work.Residues.mul_slope_eq_AfunPlus_snd d hd w ζ (sub_ne_zero.mp hne')
  have hgoal : (-Work.Residues.AfunPlus d z w) / Work.Residues.jprime z = 0 := by
    rw [hA0]
    simp
  rwa [hgoal] at hmain

/-! ## The two crossed translates -/

/-- The crossed orbit point for `γ = T*S`: `T*S*T` maps `τ - 1` to `(T*S) • τ`. -/
lemma TST_smul_neg_one_vadd (τ : ℍ) :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T) • ((-1 : ℝ) +ᵥ τ)
      = (ModularGroup.T * ModularGroup.S) • τ := by
  rw [← Work.Residues.T_inv_smul_eq τ, ← mul_smul]
  congr 1
  group

/-- The crossed orbit point for `γ = T⁻¹*S`: `T⁻¹*S*T⁻¹` maps `τ + 1` to `(T⁻¹*S) • τ`. -/
lemma TinvSTinv_smul_one_vadd (τ : ℍ) :
    (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹) • ((1 : ℝ) +ᵥ τ)
      = (ModularGroup.T⁻¹ * ModularGroup.S) • τ := by
  rw [← UpperHalfPlane.modular_T_smul τ, ← mul_smul]
  congr 1
  group

/-! ## The main theorem -/

theorem KPlus_second_residue_at_crossed_zero (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : 3 ≤ τ.im) :
    Work.Residues.HasResidue
        (fun ζ : UpperHalfPlane => Work.Kernels.KPlus d
          ((ModularGroup.T * ModularGroup.S) • τ) ζ) ((-1 : ℝ) +ᵥ τ) 0
      ∧ Work.Residues.HasResidue
        (fun ζ : UpperHalfPlane => Work.Kernels.KPlus d
          ((ModularGroup.T⁻¹ * ModularGroup.S) • τ) ζ) ((1 : ℝ) +ᵥ τ) 0 := by
  have hjt : Work.Residues.jprime τ ≠ 0 := jprime_ne_zero_of_three_le_im τ hτ
  have hphi := Work.Residues.phiPlus_crossed_translates_eq_zero
  constructor
  · refine hasResidue_KPlus_second_of_orbit_eq_zero d hd ((-1 : ℝ) +ᵥ τ)
      ((ModularGroup.T * ModularGroup.S) • τ)
      (ModularGroup.T * ModularGroup.S * ModularGroup.T)
      (TST_smul_neg_one_vadd τ) ?_ (jprime_TS_smul_ne_zero τ hτ) ?_ ?_
    · rw [Work.Residues.jprime_vadd_neg_one]
      exact hjt
    · have h1 : jInvariantFun ((ModularGroup.T * ModularGroup.S) • τ) = jInvariantFun τ := by
        rw [mul_smul, UpperHalfPlane.modular_T_smul, KernelFacts.jInvariantFun_vadd_one,
          KernelFacts.jInvariantFun_S_smul]
      have h2 : jInvariantFun ((-1 : ℝ) +ᵥ τ) = jInvariantFun τ :=
        jInvariantFun_vadd_neg_one' τ
      rw [h1, h2]
    · have h : MonoidAlgebra.single
            (ModularGroup.T * ModularGroup.S * ModularGroup.T) (1 : ℂ)
          = Work.Kernels.R_T * Work.Kernels.R_S * Work.Kernels.R_T := by
        simp only [Work.Kernels.R_T, Work.Kernels.R_S, MonoidAlgebra.single_mul_single, mul_one]
      rw [h]
      exact hphi.1
  · refine hasResidue_KPlus_second_of_orbit_eq_zero d hd ((1 : ℝ) +ᵥ τ)
      ((ModularGroup.T⁻¹ * ModularGroup.S) • τ)
      (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹)
      (TinvSTinv_smul_one_vadd τ) ?_ (jprime_TinvS_smul_ne_zero τ hτ) ?_ ?_
    · rw [Work.Residues.jprime_vadd_one]
      exact hjt
    · have h1 : jInvariantFun ((ModularGroup.T⁻¹ * ModularGroup.S) • τ)
          = jInvariantFun τ := by
        rw [mul_smul, Work.Residues.T_inv_smul_eq, jInvariantFun_vadd_neg_one',
          KernelFacts.jInvariantFun_S_smul]
      have h2 : jInvariantFun ((1 : ℝ) +ᵥ τ) = jInvariantFun τ :=
        KernelFacts.jInvariantFun_vadd_one τ
      rw [h1, h2]
    · exact hphi.2

end Work.Asymptotics
