import Mathlib
import Submission.Work.RPB.B5.SqrtGenDefs
import Submission.Work.RPB.B5.SqrtGen.branch_fderiv_pos
import Submission.Work.RPB.B5.SqrtGen.branch_fderiv_neg

/-!
# `Work.RPB.B5.sqrtPowSmooth`

`z ↦ z.2 ^ j • ψ (z.1, √z.2)` (`z.2 ≥ 0`) / `z ↦ z.2 ^ j • ψ (z.1, √(-z.2))` (`z.2 < 0`) is `C^j`
for `ψ : X × ℝ → E` smooth, with `X` an arbitrary real normed space.

This is the general-domain version of `Work.RPB.B3.sqrt_pow_contDiff` (there `X = ℝ`).  The proof
is the same induction on the number of derivatives: with `GG ψ n` the level-`n` piecewise function,
`pdX`/`pdU` the two partial derivatives of `ψ`, `ThetaG ψ n = n • ψ + ½ • (s • ∂₂ψ)` and `dG ψ n`
the explicit Fréchet derivative of `GG ψ (n+1)`, the induction is driven by
`contDiff_succ_iff_hasFDerivAt`.

Because the `X`-partial derivative `pdX ψ = (fderiv ψ) ∘ inl` takes values in the function space
`X →L[ℝ] F`, whose universe is `max (universe of X) (universe of F)`, the induction is carried out
for `X` and the target space in a *common* universe (so that `X →L F` stays in that universe).
The general statement -- with `X` and `E` in arbitrary universes -- is then obtained by lifting
both along `ULift` (`sqrtGen_mainProp_lift`).
-/

open scoped ContDiff
open Filter

namespace Work.RPB.B5.SqrtGen

section Aux

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative `pdX ψ = (fderiv ψ) ∘ inl` is smooth when `ψ` is. -/
theorem contDiff_pdX (ψ : X × ℝ → E) (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (pdX ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (le_refl ∞)
  change ContDiff ℝ ∞ (fun z : X × ℝ => (fderiv ℝ ψ z) ∘SL
    (ContinuousLinearMap.inl ℝ X ℝ))
  exact ContDiff.clm_comp (g := fderiv ℝ ψ)
    (f := fun _ : X × ℝ => (ContinuousLinearMap.inl ℝ X ℝ)) hd contDiff_const

/-- The partial derivative `pdU ψ` is smooth when `ψ` is. -/
theorem contDiff_pdU (ψ : X × ℝ → E) (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (pdU ψ) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (le_refl ∞)
  change ContDiff ℝ ∞ (fun z : X × ℝ => (fderiv ℝ ψ z) (0, 1))
  exact hd.clm_apply contDiff_const

/-- `ThetaG ψ n` is smooth when `ψ` is. -/
theorem contDiff_ThetaG (ψ : X × ℝ → E) (hψ : ContDiff ℝ ∞ ψ) (n : ℕ) :
    ContDiff ℝ ∞ (ThetaG ψ n) := by
  have h2 : ContDiff ℝ ∞ (pdU ψ) := contDiff_pdU ψ hψ
  have h1 : ContDiff ℝ ∞ (fun z : X × ℝ => n • ψ z) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hψ.const_smul (n : ℝ)
  have h3 : ContDiff ℝ ∞ (fun z : X × ℝ => (1 / 2 : ℝ) • (z.2 • pdU ψ z)) :=
    ContDiff.const_smul (1 / 2) (contDiff_snd.smul h2)
  change ContDiff ℝ ∞ (fun z : X × ℝ => n • ψ z + (1 / 2 : ℝ) • (z.2 • pdU ψ z))
  exact h1.add h3

/-- `GG ψ 0` is continuous when `ψ` is. -/
theorem contDiff_GG_zero (ψ : X × ℝ → E) (hψ : Continuous ψ) : ContDiff ℝ 0 (GG ψ 0) := by
  rw [contDiff_zero, ← continuousOn_univ]
  have hcov : ({z : X × ℝ | 0 ≤ z.2} ∪ {z : X × ℝ | z.2 ≤ 0}) = Set.univ := by
    ext z; simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_total 0 z.2
  rw [← hcov]
  apply ContinuousOn.union_of_isClosed
  · have h1 : Continuous (fun z : X × ℝ => ψ (z.1, Real.sqrt z.2)) :=
      hψ.comp (by fun_prop)
    refine ContinuousOn.congr (f := fun z : X × ℝ => ψ (z.1, Real.sqrt z.2))
      h1.continuousOn ?_
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp only [GG, ite_eq_left hz, pow_zero, one_smul]
  · have h2 : Continuous (fun z : X × ℝ => ψ (z.1, Real.sqrt (-z.2))) :=
      hψ.comp (by fun_prop)
    refine ContinuousOn.congr (f := fun z : X × ℝ => ψ (z.1, Real.sqrt (-z.2)))
      h2.continuousOn ?_
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    rcases lt_or_eq_of_le hz with hlt | heq
    · simp only [GG, ite_eq_right (not_le.mpr hlt), pow_zero, one_smul]
    · have hGz : GG ψ 0 z = ψ (z.1, Real.sqrt z.2) := by
        simp only [GG, ite_eq_left (le_of_eq heq.symm), pow_zero, one_smul]
      rw [hGz]
      show ψ (z.1, Real.sqrt z.2) = ψ (z.1, Real.sqrt (-z.2))
      rw [heq, neg_zero, Real.sqrt_zero]
  · exact isClosed_le continuous_const continuous_snd
  · exact isClosed_le continuous_snd continuous_const

/-- **Boundary (base) derivative.**  If `g` is continuous at `z` with `z.2 = 0`, then
`w ↦ w.2 • g w` is differentiable at `z` with derivative `w ↦ w.2 • g z`. -/
theorem hasFDerivAt_proj_smul (g : X × ℝ → E) (z : X × ℝ) (hz : z.2 = 0)
    (hg : ContinuousAt g z) :
    HasFDerivAt (fun w : X × ℝ => w.2 • g w)
      ((ContinuousLinearMap.snd ℝ X ℝ).smulRight (g z)) z := by
  rw [hasFDerivAt_iff_isLittleO]
  have h1 : (fun x' : X × ℝ => x'.2 • g x' - z.2 • g z
      - ((ContinuousLinearMap.snd ℝ X ℝ).smulRight (g z)) (x' - z))
      = (fun x' : X × ℝ => x'.2 • (g x' - g z)) := by
    funext x'
    rw [ContinuousLinearMap.smulRight_apply]
    rw [show (ContinuousLinearMap.snd ℝ X ℝ) (x' - z) = x'.2 by simp [hz]]
    rw [hz, zero_smul, sub_zero, smul_sub]
  rw [h1]
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  have htend : ∀ᶠ x' in nhds z, ‖g x' - g z‖ < c := by
    have h2 : ∀ᶠ y in nhds (0 : E), ‖y‖ < c := by
      have hb : Metric.ball (0 : E) c ∈ nhds 0 := Metric.ball_mem_nhds 0 hc
      exact Filter.mem_of_superset hb (fun y hy => by
        rw [Metric.mem_ball, dist_eq_norm] at hy; simpa using hy)
    have ht : Tendsto (fun x' : X × ℝ => g x' - g z) (nhds z) (nhds 0) := by
      have hgz : Tendsto (fun _ : X × ℝ => g z) (nhds z) (nhds (g z)) := tendsto_const_nhds
      have := hg.tendsto.sub hgz
      simpa using this
    exact ht.eventually h2
  filter_upwards [htend] with x' hx'
  rw [norm_smul]
  have hle : ‖x'.2‖ ≤ ‖x' - z‖ := by
    have := norm_snd_le (x' - z)
    simpa [hz] using this
  have hx'nn : 0 ≤ ‖g x' - g z‖ := norm_nonneg _
  calc ‖x'.2‖ * ‖g x' - g z‖ ≤ ‖x' - z‖ * c :=
        mul_le_mul hle (le_of_lt hx') hx'nn (norm_nonneg _)
    _ = c * ‖x' - z‖ := by ring

/-- `dG ψ n` is `C^n` as soon as its two `GG`-ingredients are. -/
theorem contDiff_dG (ψ : X × ℝ → E) (n : ℕ)
    (h1 : ContDiff ℝ n (GG (pdX ψ) n)) (h2 : ContDiff ℝ n (GG (ThetaG ψ (n + 1)) n)) :
    ContDiff ℝ n (dG ψ n) := by
  have hF : ContDiff ℝ n (fun z : X × ℝ => z.2 • GG (pdX ψ) n z) := contDiff_snd.smul h1
  have ht1 : ContDiff ℝ n (fun z : X × ℝ =>
      (z.2 • GG (pdX ψ) n z).comp (ContinuousLinearMap.fst ℝ X ℝ)) :=
    ContDiff.clm_comp (g := fun z : X × ℝ => z.2 • GG (pdX ψ) n z)
      (f := fun _ : X × ℝ => ContinuousLinearMap.fst ℝ X ℝ) hF contDiff_const
  have ht2 : ContDiff ℝ n (fun z : X × ℝ =>
      (ContinuousLinearMap.snd ℝ X ℝ).smulRight (GG (ThetaG ψ (n + 1)) n z)) :=
    ((ContinuousLinearMap.smulRightL ℝ (X × ℝ) E)
      (ContinuousLinearMap.snd ℝ X ℝ)).contDiff.comp h2
  change ContDiff ℝ n (fun z : X × ℝ =>
    (z.2 • GG (pdX ψ) n z) ∘SL (ContinuousLinearMap.fst ℝ X ℝ)
      + (ContinuousLinearMap.snd ℝ X ℝ).smulRight (GG (ThetaG ψ (n + 1)) n z))
  exact ht1.add ht2

/-- The successor relation for the derivatives (product rule for the factor `z.2`). -/
theorem hasFDerivAt_GG_succ (ψ : X × ℝ → E) (n : ℕ) (z : X × ℝ)
    (h : HasFDerivAt (GG ψ (n + 1)) (dG ψ n z) z) :
    HasFDerivAt (GG ψ (n + 2)) (dG ψ (n + 1) z) z := by
  have hG : GG ψ (n + 2) = (fun w : X × ℝ => w.2) • GG ψ (n + 1) := by
    funext w
    exact GG_smul_succ_apply ψ (n + 1) w
  have h1 : HasFDerivAt (fun w : X × ℝ => w.2) (ContinuousLinearMap.snd ℝ X ℝ) z :=
    hasFDerivAt_snd
  have hprod := h1.smul h
  rw [← hG] at hprod
  rw [dG_succ_eq ψ n z]
  simpa only [add_comm] using hprod

end Aux

section Induction

universe u

variable {X₀ : Type u} [NormedAddCommGroup X₀] [NormedSpace ℝ X₀]

/-- **The induction**, carried out with `X` and the target space in a common universe `u` (so that
`X →L F`, the target of `pdX ψ`, stays in that universe).

Assuming the two one-sided derivative lemmas, level `n` of `GG` is `C^n` and `dG ψ n` is the
derivative of level `n+1`, for every smooth `ψ`. -/
theorem sqrtGen_mainProp (n : ℕ) :
    (∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (ψ : X₀ × ℝ → F), ContDiff ℝ ∞ ψ → ContDiff ℝ n (GG ψ n)) ∧
    (∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (ψ : X₀ × ℝ → F), ContDiff ℝ ∞ ψ →
      ∀ z, HasFDerivAt (GG ψ (n + 1)) (dG ψ n z) z) := by
  induction n with
  | zero =>
    constructor
    · intro F _ _ ψ hψ
      exact contDiff_GG_zero ψ hψ.continuous
    · intro F _ _ ψ hψ z
      rcases lt_trichotomy z.2 0 with hlt | heq | hgt
      · refine (branch_fderiv_neg ψ 0 z hψ hlt).congr_of_eventuallyEq ?_
        have hev : ∀ᶠ w in nhds z, w.2 < 0 :=
          (isOpen_Iio.preimage continuous_snd).mem_nhds hlt
        filter_upwards [hev] with w hw
        simp only [GG, ite_eq_right (not_le.mpr hw)]
      · have hcont : ContinuousAt (GG ψ 0) z :=
          (contDiff_GG_zero ψ hψ.continuous).continuous.continuousAt
        have hb := hasFDerivAt_proj_smul (GG ψ 0) z heq hcont
        have hdg : dG ψ 0 z = (ContinuousLinearMap.snd ℝ X₀ ℝ).smulRight (GG ψ 0 z) := by
          simp only [dG, GG, ThetaG, heq, le_refl, reduceIte, pow_zero, one_smul, zero_smul]
          simp
        rw [show GG ψ 1 = (fun w : X₀ × ℝ => w.2 • GG ψ 0 w) from GG_smul_succ ψ 0, hdg]
        exact hb
      · refine (branch_fderiv_pos ψ 0 z hψ hgt).congr_of_eventuallyEq ?_
        have hev : ∀ᶠ w in nhds z, 0 ≤ w.2 := by
          have hset : ∀ᶠ w in nhds z, (0 : ℝ) < w.2 :=
            (isOpen_Ioi.preimage continuous_snd).mem_nhds hgt
          exact hset.mono (fun w hw => le_of_lt hw)
        filter_upwards [hev] with w hw
        simp only [GG, ite_eq_left hw]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · intro F _ _ ψ hψ
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 from by
        rw [Nat.cast_add, Nat.cast_one]]
      rw [contDiff_succ_iff_hasFDerivAt]
      exact ⟨dG ψ n,
        contDiff_dG ψ n (ih1 (F := X₀ →L[ℝ] F) (pdX ψ) (contDiff_pdX ψ hψ))
          (ih1 (ThetaG ψ (n + 1)) (contDiff_ThetaG ψ hψ (n + 1))),
        fun z => ih2 ψ hψ z⟩
    · intro F _ _ ψ hψ z
      exact hasFDerivAt_GG_succ ψ n z (ih2 ψ hψ z)

end Induction

section Lift

universe u v

/-- The general statement with `X` and `E` in arbitrary universes, obtained from the same-universe
induction `sqrtGen_mainProp` by lifting both `X` and `E` to the common universe `max u v` along
`ULift` (which is an isometry, so `C^n`-regularity transports). -/
theorem sqrtGen_mainProp_lift {X : Type u} {E : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) (ψ : X × ℝ → E) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ j (GG ψ j) := by
  -- `ULift`-equivalences, as continuous linear maps.
  let downX : ULift.{max u v, u} X →L[ℝ] X :=
    (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := X)).toContinuousLinearMap
  let upX : X →L[ℝ] ULift.{max u v, u} X :=
    (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := X)).symm.toContinuousLinearMap
  let downE : ULift.{max u v, v} E →L[ℝ] E :=
    (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := E)).toContinuousLinearMap
  let upE : E →L[ℝ] ULift.{max u v, v} E :=
    (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := E)).symm.toContinuousLinearMap
  -- `U : (ULift X) × ℝ → X × ℝ`, `(x,t) ↦ (x.down, t)`
  let U : (ULift.{max u v, u} X × ℝ) →L[ℝ] (X × ℝ) :=
    ((downX.comp (ContinuousLinearMap.fst ℝ (ULift.{max u v, u} X) ℝ)).prod
      (ContinuousLinearMap.snd ℝ (ULift.{max u v, u} X) ℝ))
  -- `T : X × ℝ → (ULift X) × ℝ`, `(x,t) ↦ (ULift.up x, t)`
  let T : (X × ℝ) →L[ℝ] (ULift.{max u v, u} X × ℝ) :=
    ((upX.comp (ContinuousLinearMap.fst ℝ X ℝ)).prod
      (ContinuousLinearMap.snd ℝ X ℝ))
  have hU : ∀ w : ULift.{max u v, u} X × ℝ, U w = (w.1.down, w.2) := fun w => rfl
  have hT : ∀ z : X × ℝ, T z = (ULift.up z.1, z.2) := fun z => rfl
  -- the lifted function
  let ψ' : (ULift.{max u v, u} X × ℝ) → ULift.{max u v, v} E := fun w => upE (ψ (U w))
  have hψ' : ContDiff ℝ ∞ ψ' := by
    have h1 : ContDiff ℝ ∞ (fun w : ULift.{max u v, u} X × ℝ => ψ (U w)) :=
      hψ.comp U.contDiff
    have h2 : ContDiff ℝ ∞ (fun w => upE (ψ (U w))) := upE.contDiff.comp h1
    simpa only [ψ'] using h2
  have hGG' : ContDiff ℝ j (GG ψ' j) :=
    (sqrtGen_mainProp (X₀ := ULift.{max u v, u} X) j).1 ψ' hψ'
  -- restrict to the image of `T`
  have hcomp : ContDiff ℝ j (fun z : X × ℝ => GG ψ' j (T z)) :=
    hGG'.comp T.contDiff
  -- identify `GG ψ' j ∘ T` with `upE ∘ GG ψ j`
  have hgen : ∀ (x : X) (s : ℝ), ψ' (ULift.up x, s) = upE (ψ (x, s)) := by
    intro x s
    rfl
  have hpt : ∀ z : X × ℝ, GG ψ' j (T z) = upE (GG ψ j z) := by
    intro z
    simp only [hT z, GG, hgen]
    by_cases h : 0 ≤ z.2
    · rw [if_pos h, ← map_smul, if_pos h]
    · rw [if_neg h, ← map_smul, if_neg h]
  have hcomp' : ContDiff ℝ j (fun z : X × ℝ => upE (GG ψ j z)) := by
    simpa only [hpt] using hcomp
  have hfinal : ContDiff ℝ j (fun z : X × ℝ => downE (upE (GG ψ j z))) :=
    downE.contDiff.comp hcomp'
  have hcancel : (fun z : X × ℝ => downE (upE (GG ψ j z))) = GG ψ j := by
    funext z
    simp [downE, upE]
  rw [hcancel] at hfinal
  exact hfinal

end Lift

end Work.RPB.B5.SqrtGen

namespace Work.RPB.B5

open Work.RPB.B5.SqrtGen

theorem sqrtPowSmooth {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : X → ℝ → E) (j : ℕ)
    (hψ : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : X × ℝ => ψ z.1 z.2)) :
    ContDiff ℝ j (fun z : X × ℝ =>
      if 0 ≤ z.2 then z.2 ^ j • ψ z.1 (Real.sqrt z.2)
      else z.2 ^ j • ψ z.1 (Real.sqrt (-z.2))) := by
  have h := sqrtGen_mainProp_lift (X := X) (E := E) j
    (fun z : X × ℝ => ψ z.1 z.2) hψ
  exact h

end Work.RPB.B5
