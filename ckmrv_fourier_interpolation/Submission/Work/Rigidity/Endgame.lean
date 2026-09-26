/-
# The endgame of the weight-four rigidity lemma `lem:noPsolutions`

This file proves `Work.Rigidity.Endgame`: a holomorphic function `f` of moderate growth
(`f ∈ 𝒫 = Work.Kernels.InP`) that is

* annihilated by `(T - I)²` (`Work.Rigidity.AnnT2`),
* an eigenfunction of the weight-`4` slash action of `S` with eigenvalue `1`
  (`Work.Rigidity.SlashEigen 4 1`),
* `o(1)` along the strip `-1 ≤ Re τ ≤ 1` (`Work.Rigidity.StripDecay 0`),
* `T`-invariant in the strong form `fstDiff f = 0`,

must vanish.

The hypothesis `fstDiff f = 0` says exactly that `f(τ+1) = f(τ)`, i.e. that `f` is periodic
of period one (it is the missing input `Work.Rigidity.tdef_eq_zero_aux` of
`Submission/Work/Rigidity/AnnMinusWeightFour.lean`, supplied here by the caller).  With it the
argument is short:

* periodicity plus moderate growth gives boundedness at the cusp (`boundedAtImInfty_of_periodic_inP`);
* the strip decay, transported along integer translates, gives vanishing at the cusp: every
  `τ` may be translated by an integer into the strip, where the decay hypothesis applies;
* periodicity and `S`-invariance make `f` invariant under all of `SL(2,ℤ)` at weight `4`
  (`SlashInvariantForm.slash_action_generators_SL2Z`), so `f` is the underlying function of a
  modular form `g` of weight `4` for `SL(2,ℤ)` (`Work.Modular.modularForm_of_slash_invariant`);
* vanishing at the cusp says that `g` is a cusp form, i.e. `g ∈ CuspForm 𝒮ℒ 4`; the space of
  weight-`4` cusp forms is zero-dimensional (`CuspForm.rank_eq_zero_of_weight_lt_twelve`, since
  `4 < 12`), so `g = 0` and hence `f = 0`.
-/
import Mathlib
import Submission.Work.Rigidity.Diff
import Submission.Work.Rigidity.boundedAtImInfty_of_periodic_inP
import Submission.Work.Modular.modularForm_of_slash_invariant
import Submission.Work.Modular.E4_tendsto_atImInfty

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Rigidity

/-! ## Translation invariance from the vanishing first difference -/

/-- `fstDiff f = 0` is exactly the statement `f(τ+1) = f(τ)`. -/
lemma endgame_vadd_one_of_fstDiff_eq_zero {f : ℍ → ℂ} (h : fstDiff f = 0) (τ : ℍ) :
    f ((1 : ℝ) +ᵥ τ) = f τ := by
  have h' := congrFun h τ
  simp only [fstDiff, Pi.zero_apply] at h'
  linear_combination h'

/-- A function invariant under `τ ↦ τ + 1` is invariant under every natural translation. -/
lemma endgame_vadd_nat {f : ℍ → ℂ} (h : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (n : ℕ) (τ : ℍ) :
    f ((n : ℝ) +ᵥ τ) = f τ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (((n + 1 : ℕ) : ℝ)) +ᵥ τ = (1 : ℝ) +ᵥ ((n : ℝ) +ᵥ τ) by
      ext <;> simp [UpperHalfPlane.coe_vadd]
      ring]
    rw [h, ih]

/-- A function invariant under `τ ↦ τ + 1` is invariant under every integer translation. -/
lemma endgame_vadd_int {f : ℍ → ℂ} (h : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ) (n : ℤ) (τ : ℍ) :
    f ((n : ℝ) +ᵥ τ) = f τ := by
  rcases n with n | n
  · exact endgame_vadd_nat h n τ
  · have hcast : ((Int.negSucc n : ℤ) : ℝ) = -(((n + 1 : ℕ)) : ℝ) := by push_cast; ring
    rw [hcast]
    have hv : (((n + 1 : ℕ) : ℝ) +ᵥ ((-(((n + 1 : ℕ)) : ℝ)) +ᵥ τ) : ℍ) = τ := by
      rw [← add_vadd]
      norm_num
    have key := endgame_vadd_nat h (n + 1) ((-(((n + 1 : ℕ)) : ℝ)) +ᵥ τ)
    rw [hv] at key
    exact key.symm

/-! ## The strip and integer translates -/

/-- Every point of `ℍ` is an integer translate of a point of the strip `-1 ≤ Re τ ≤ 1`. -/
lemma endgame_exists_int_vadd_mem_strip (τ : ℍ) : ∃ n : ℤ, InStrip ((n : ℝ) +ᵥ τ) := by
  refine ⟨-(⌊τ.re⌋), ?_, ?_⟩
  · have h : ((((-(⌊τ.re⌋) : ℤ) : ℝ) +ᵥ τ : ℍ)).re = τ.re - ((⌊τ.re⌋ : ℤ) : ℝ) := by
      rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
      simp only [Complex.add_re, Complex.ofReal_re]
      rw [UpperHalfPlane.coe_re]
      push_cast
      ring
    rw [h]
    have := Int.floor_le τ.re
    linarith
  · have h : ((((-(⌊τ.re⌋) : ℤ) : ℝ) +ᵥ τ : ℍ)).re = τ.re - ((⌊τ.re⌋ : ℤ) : ℝ) := by
      rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]
      simp only [Complex.add_re, Complex.ofReal_re]
      rw [UpperHalfPlane.coe_re]
      push_cast
      ring
    rw [h]
    have := Int.lt_floor_add_one τ.re
    linarith

/-- The imaginary part of a real translate. -/
lemma endgame_im_vadd (x : ℝ) (τ : ℍ) : (((x +ᵥ τ : ℍ))).im = τ.im := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd, ← UpperHalfPlane.coe_im,
    Complex.add_im, Complex.ofReal_im, zero_add]

/-! ## The slash action of `T` -/

/-- The slash action of `T` at any weight is translation by `1`. -/
lemma endgame_slash_T_apply (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[k] ModularGroup.T) τ = F ((1 : ℝ) +ᵥ τ) := by
  rw [Work.Kernels.slash_apply', UpperHalfPlane.modular_T_smul]
  have h1 : Work.Kernels.jFun ModularGroup.T (τ : ℂ) = 1 := by
    rw [Work.Kernels.jFun_apply]
    have h10 : (ModularGroup.T : SL(2, ℤ)) 1 0 = 0 := by decide
    have h11 : (ModularGroup.T : SL(2, ℤ)) 1 1 = 1 := by decide
    rw [h10, h11]; ring
  rw [h1]
  simp

/-! ## The endgame -/

theorem Endgame {f : UpperHalfPlane → ℂ} (hP : Work.Kernels.InP f) (hT2 : Work.Rigidity.AnnT2 f)
    (hS : Work.Rigidity.SlashEigen 4 (1 : ℂ) f) (hdec : Work.Rigidity.StripDecay 0 f)
    (hu : Work.Rigidity.fstDiff f = 0) : f = 0 := by
  have hf_hol : MDiff f := hP.1
  -- `f` is periodic of period one
  have hshift : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ :=
    fun τ => endgame_vadd_one_of_fstDiff_eq_zero hu τ
  obtain ⟨φ, hφ, hφb⟩ := hdec
  -- the decay function is eventually `≤ 1`
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ y : ℝ, A ≤ y → φ y ≤ 1 := by
    obtain ⟨A, hA⟩ := Metric.tendsto_atTop.1 hφ 1 zero_lt_one
    refine ⟨A, fun y hy => ?_⟩
    have hy' := hA y hy
    rw [Real.dist_eq, sub_zero] at hy'
    linarith [abs_lt.1 hy']
  -- boundedness at the cusp `i∞`
  have hbdd : IsBoundedAtImInfty f :=
    Work.Rigidity.boundedAtImInfty_of_periodic_inP hP hshift
  -- vanishing at the cusp `i∞`, from the strip decay
  have hzero : IsZeroAtImInfty f := by
    rw [UpperHalfPlane.isZeroAtImInfty_iff]
    intro ε hε
    obtain ⟨A', hA'⟩ : ∃ A' : ℝ, ∀ y : ℝ, A' ≤ y → φ y < ε := by
      obtain ⟨A', hA'⟩ := Metric.tendsto_atTop.1 hφ ε hε
      refine ⟨A', fun y hy => ?_⟩
      have hy' := hA' y hy
      rw [Real.dist_eq, sub_zero, abs_lt] at hy'
      exact hy'.2
    refine ⟨A', fun τ hτ => ?_⟩
    obtain ⟨n, hn⟩ := endgame_exists_int_vadd_mem_strip τ
    have hval := endgame_vadd_int hshift n τ
    rw [← hval]
    have hb := hφb _ hn
    have hexp : Real.exp (-(2 * Real.pi * 0 * (((n : ℝ) +ᵥ τ : ℍ)).im)) = 1 := by norm_num
    rw [hexp, mul_one] at hb
    exact le_of_lt (lt_of_le_of_lt hb (hA' _ (by rw [endgame_im_vadd]; exact hτ)))
  -- `S`-invariance as an equation of functions
  have hS' : f ∣[(4 : ℤ)] ModularGroup.S = f := by
    funext τ
    simpa using hS τ
  -- `T`-invariance
  have hT : f ∣[(4 : ℤ)] ModularGroup.T = f := by
    funext τ
    rw [endgame_slash_T_apply]
    exact hshift τ
  -- full `SL(2,ℤ)`-invariance
  have hper : ∀ γ : SL(2, ℤ), f ∣[(4 : ℤ)] γ = f :=
    SlashInvariantForm.slash_action_generators_SL2Z hS' hT
  -- `f` is the underlying function of a modular form of weight `4`
  obtain ⟨g, hg⟩ := Work.Modular.modularForm_of_slash_invariant hper hf_hol hbdd
  -- its constant `q`-coefficient vanishes
  have hperab : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    let F : SlashInvariantForm 𝒮ℒ (4 : ℤ) :=
      { toFun := f
        slash_action_eq' := by
          rintro γ ⟨δ, rfl⟩
          exact hper δ }
    have := SlashInvariantFormClass.periodic_comp_ofComplex (f := F) (k := (4 : ℤ)) (Γ := 𝒮ℒ)
      one_mem_strictPeriods_SL
    simpa [F] using this
  have hana : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperab hf_hol hbdd
  have hc0 : (UpperHalfPlane.qExpansion 1 f).coeff 0 = 0 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero one_pos hana hperab,
      UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero hzero]
  have hc0' : (UpperHalfPlane.qExpansion 1 (⇑g)).coeff 0 = 0 := by
    rw [hg]
    exact hc0
  -- no weight-four cusp forms
  have hrank : Module.rank ℂ (CuspForm 𝒮ℒ (4 : ℤ)) = 0 :=
    CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)
  have hcf : ModularForm.toCuspForm g hc0' = 0 :=
    rank_zero_iff_forall_zero.mp hrank _
  have hg0 : ⇑g = 0 := by
    have h1 : (ModularForm.toCuspForm g hc0' : ℍ → ℂ) = 0 := by rw [hcf]; rfl
    funext z
    rw [← ModularForm.toCuspForm_apply g hc0' z]
    exact congrFun h1 z
  rw [← hg]
  exact hg0

end Work.Rigidity
