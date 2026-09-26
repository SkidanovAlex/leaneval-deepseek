import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B7Bound_proof
import Submission.Work.Asymptotics.KhatE1Core.KPlusSumRefQExp
import Submission.Work.Asymptotics.KhatE1Core.KPlusQ1
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Split
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.K24FAtoms

/-!
# The `K₊`-reference remainder of order `>= 6`

`KPlus24Ref = -(c·z²)·KPlusSumRef` is the reference part of the `K₊`-group of the
`Sh`-cleared `d = 24` bracket, and `KPlusSumRef_qexp` gives `KPlusSumRef` as a polynomial in
`q = qParamFun z = (Ept z)²` with explicit `τ`-atom coefficients.  Here we split that polynomial
as

  `KPlusSumRefTail = KPS0 + q · KPSrest`

(`KPS0` is the `q⁰`-coefficient, `KPSrest` the remaining ones shifted down by one) and prove

  `‖KPSrest τ z‖ ≤ C ‖q(τ)‖⁻¹ (scale τ)^N (1+t)^M`.

The point is that the `j(τ)`-atoms inside `KPSrest` — the `j(τ)²r₁(τ)`-monomials — are rewritten
with `Δ(τ)j(τ)² = E₄(τ)³j(τ)`, i.e. `j(τ)²r₁ = j(τ)·R₀`, which keeps the `j`-degree at one and
hence the `‖q(τ)‖⁻¹` weight.

Consequently

  `KPlus24Ref - (-(c z²))(KPlusQ1·q + KPS0·q²) = -(c z²)·q³·KPSrest`,

the part of the `K₊`-reference of `E`-degree `>= 6`, and it is
`O(‖q(τ)‖⁻¹ (scale τ)^N (1+t)^M ‖Ept z‖⁶)` — the `K₊` summand of the remainder (iv) of
`Bracket24ExpansionHold`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-! ## `BoundQ` helpers -/

private theorem BoundQ.addc {f g : ℍ → ℍ → ℂ} {m n k : ℤ} (hm : k ≤ m) (hn : k ≤ n)
    (hf : BoundQ f m) (hg : BoundQ g n) : BoundQ (fun τ z => f τ z + g τ z) k :=
  (hf.add hg).mono (le_min hm hn)

private theorem BoundQ.mulc {f g : ℍ → ℍ → ℂ} {m n k : ℤ} (hk : k ≤ m + n)
    (hf : BoundQ f m) (hg : BoundQ g n) : BoundQ (fun τ z => f τ z * g τ z) k :=
  (hf.mul hg).mono hk

private theorem BoundQ.mul0 {f g : ℍ → ℍ → ℂ} (hf : BoundQ f 0) (hg : BoundQ g 0) :
    BoundQ (fun τ z => f τ z * g τ z) 0 := by
  have h := hf.mul hg
  rw [add_zero] at h
  exact h

private theorem BoundQ.cmul0 (c : ℂ) {f : ℍ → ℍ → ℂ} (hf : BoundQ f 0) :
    BoundQ (fun τ z => c * f τ z) 0 := BoundQ.const_mul c hf

/-- `BoundQ` at index `-1` from a product of two factors. -/
private theorem BoundQ.mulM {f g : ℍ → ℍ → ℂ} {m n : ℤ} (hf : BoundQ f m) (hg : BoundQ g n)
    (hk : (-1 : ℤ) ≤ m + n) : BoundQ (fun τ z => f τ z * g τ z) (-1) := (hf.mul hg).mono hk

/-- `BoundQ` at index `-1` from a single factor at index `≤ -1`. -/
private theorem BoundQ.monoM {f : ℍ → ℍ → ℂ} {n : ℤ} (hf : BoundQ f n) (h : (-1 : ℤ) ≤ n) :
    BoundQ f (-1) := hf.mono h

/-- `BoundQ` at index `-1` from a sum of two factors at index `-1`. -/
private theorem BoundQ.addM {f g : ℍ → ℍ → ℂ} (hf : BoundQ f (-1)) (hg : BoundQ g (-1)) :
    BoundQ (fun τ z => f τ z + g τ z) (-1) := (hf.add hg).mono (le_min le_rfl le_rfl)

/-! ## The `τ`- and `z`-atoms of `KPlusSumRef` -/

private theorem BoundQ_r0 : BoundQ (fun (τ : ℍ) (_ : ℍ) => Work.Asymptotics.K24F.r0 τ) 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one] using (hb τ hF).1

private theorem BoundQ_r1 : BoundQ (fun (τ : ℍ) (_ : ℍ) => Work.Asymptotics.K24F.r1 τ) 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one] using (hb τ hF).2.2.2.1

private theorem BoundQ_r2 : BoundQ (fun (τ : ℍ) (_ : ℍ) => Work.Asymptotics.K24F.r2 τ) 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one] using (hb τ hF).2.1

private theorem BoundQ_R0 : BoundQ (fun (τ : ℍ) (_ : ℍ) => Work.Asymptotics.K24F.R0 τ) 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one] using (hb τ hF).2.2.1

private theorem BoundQ_Q1 :
    BoundQ (fun (τ : ℍ) (z : ℍ) => Work.Asymptotics.K24F.Q1 τ z) 0 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.K24Fsm.q1_le
  refine ⟨C, 1, 0, hC, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one] using hb τ z hF hz3

private theorem BoundQ_Th0 :
    BoundQ (fun (τ : ℍ) (z : ℍ) => Work.Asymptotics.K24F.Th0 τ z) 0 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.K24Fsm.th0_le
  refine ⟨C, 1, 0, hC, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one] using hb τ z hF hz3

private theorem BoundQ_Phiref :
    BoundQ (fun (τ : ℍ) (z : ℍ) => Work.Asymptotics.K24F.Phiref τ z) 0 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.K24Fsm.phiref_le
  refine ⟨C, 1, 0, hC, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one] using hb τ z hF hz3

private theorem BoundQ_S0 :
    BoundQ (fun (_ : ℍ) (z : ℍ) => Work.Asymptotics.K24F.S0 z) 0 := by
  refine ⟨3, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_zero, mul_one] using Work.Asymptotics.K24F.zS0_norm z hz1'

/-! ## The `j²r₁`-rewriting -/

private theorem BoundQ_S02 : BoundQ (fun (_ : ℍ) (z : ℍ) => Work.Asymptotics.K24F.S0 z ^ 2) 0 :=
  (BoundQ.mul0 BoundQ_S0 BoundQ_S0).congr (fun _ z => by ring)

/-! ## The `j²r₁`-rewriting -/

private lemma j2r1_eq (τ : ℍ) : Work.Kernels.jInvariantFun τ ^ 2 * Work.Asymptotics.K24F.r1 τ
    = Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.R0 τ := by
  have h := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  rw [Work.Asymptotics.K24F.r1, Work.Asymptotics.K24F.R0]
  calc Work.Kernels.jInvariantFun τ ^ 2
        * (Work.Asymptotics.Compact.phi1 τ * Work.Kernels.DeltaFun τ)
      = Work.Asymptotics.Compact.phi1 τ
          * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
          * Work.Kernels.jInvariantFun τ := by ring
    _ = Work.Asymptotics.Compact.phi1 τ * Work.Kernels.E4Fun τ ^ 3
          * Work.Kernels.jInvariantFun τ := by rw [h]
    _ = Work.Kernels.jInvariantFun τ
          * (Work.Asymptotics.Compact.phi1 τ * Work.Kernels.E4Fun τ ^ 3) := by ring

/-! ## The coefficient blocks -/


noncomputable def KPS0 (τ z : ℍ) : ℂ :=
      ((-313113600 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((-41320046592 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((-6054912 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((-61461504 : ℂ)) * (Work.Asymptotics.K24F.R0 τ) + ((-17280 : ℂ)) * (Work.Asymptotics.K24F.Q1 τ z) + ((9504 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r2 τ) + ((87257088 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((9504 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r0 τ) + ((24 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.Th0 τ z) + ((-252 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.Phiref τ z) + ((-19008 : ℂ)) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) + ((-642816 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r2 τ) + ((-873256992768 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ) + ((-891648 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r0 τ) + ((67433472 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.R0 τ) + ((864 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r2 τ) + ((555185664 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((864 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r0 τ) + ((-1728 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) + ((-309795840 : ℂ)) * (Work.Asymptotics.K24F.S0 z) ^ 2 * (Work.Asymptotics.K24F.r0 τ)

noncomputable def KPSb1 (τ z : ℍ) : ℂ :=
      ((-31115290752 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((6480585584640 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((-1846675584 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((13066665984 : ℂ)) * (Work.Asymptotics.K24F.R0 τ) + ((-4302720 : ℂ)) * (Work.Asymptotics.K24F.Q1 τ z) + ((-20736 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r2 τ) + ((-9403174656 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-20736 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r0 τ) + ((-252 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.Th0 τ z) + ((41472 : ℂ)) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) + ((-169827840 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r2 τ) + ((-221521732485120 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ) + ((-169827840 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r0 τ) + ((141296762880 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.R0 τ) + ((461495024640 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-29262643200 : ℂ)) * (Work.Asymptotics.K24F.S0 z) ^ 2 * (Work.Asymptotics.K24F.r0 τ)

noncomputable def KPSb2 (τ z : ℍ) : ℂ :=
      ((-866897593344 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((3789324416286720 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((-197729620992 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((-1946760044544 : ℂ)) * (Work.Asymptotics.K24F.R0 τ) + ((-406425600 : ℂ)) * (Work.Asymptotics.K24F.Q1 τ z) + ((-31104 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r2 τ) + ((-10712069793792 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-31104 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r0 τ) + ((62208 : ℂ)) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) + ((-18348871680 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r2 τ) + ((69048683749048320 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ) + ((-18348871680 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r0 τ) + ((4525019873280 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.R0 τ) + ((-230415754567680 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-669159014400 : ℂ)) * (Work.Asymptotics.K24F.S0 z) ^ 2 * (Work.Asymptotics.K24F.r0 τ)

noncomputable def KPSb3 (τ z : ℍ) : ℂ :=
      ((-12901309655040 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((-1703225054430167040 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((-7096556759040 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((-82440390574080 : ℂ)) * (Work.Asymptotics.K24F.R0 τ) + ((-9293875200 : ℂ)) * (Work.Asymptotics.K24F.Q1 τ z) + ((5511848782417920 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-685731225600 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r2 τ) + ((35064508057052774400 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ) + ((-685731225600 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r0 τ) + ((11609505792000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.R0 τ) + ((1371462451200 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-5804752896000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) ^ 2 * (Work.Asymptotics.K24F.r0 τ)

noncomputable def KPSb4 (τ z : ℍ) : ℂ :=
      ((-120551280721920 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((-847593621691493253120 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((-103137022033920 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((-229442532802560 : ℂ)) * (Work.Asymptotics.K24F.R0 τ) + ((-80621568000 : ℂ)) * (Work.Asymptotics.K24F.Q1 τ z) + ((16798850610462720 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-10932284620800 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r2 τ) + ((4521132461396223590400 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ) + ((-10932284620800 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r0 τ) + ((34828517376000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.R0 τ) + ((21864569241600 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-17414258688000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) ^ 2 * (Work.Asymptotics.K24F.r0 τ)

noncomputable def KPSb5 (τ z : ℍ) : ℂ :=
      ((-574944650035200 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((-111040851154239199641600 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((-574944650035200 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((-241864704000 : ℂ)) * (Work.Asymptotics.K24F.Q1 τ z) + ((1149889300070400 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-78364164096000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r2 τ) + ((177018003362145632256000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ) + ((-78364164096000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r0 τ) + ((156728328192000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ)

noncomputable def KPSb6 (τ z : ℍ) : ℂ :=
      ((-24379962163200 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((-4573988896581020653977600 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((-24379962163200 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((48759924326400 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((-208971104256000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r2 τ) + ((2873979162172871147520000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ) + ((-208971104256000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r0 τ) + ((417942208512000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ)

noncomputable def KPSb7 (τ z : ℍ) : ℂ :=
      ((7836416409600000 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((-81720846598237417635840000 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((7836416409600000 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((-15672832819200000 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((20790330604794905886720000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ)

noncomputable def KPSb8 (τ z : ℍ) : ℂ :=
      ((7522959753216000 : ℂ)) * (Work.Asymptotics.K24F.r2 τ) + ((-705894449357811326386176000 : ℂ)) * (Work.Asymptotics.K24F.r1 τ) + ((7522959753216000 : ℂ)) * (Work.Asymptotics.K24F.r0 τ) + ((-15045919506432000 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.r1 τ) + ((55738314164283805532160000 : ℂ)) * (Work.Asymptotics.K24F.S0 z) * (Work.Asymptotics.K24F.r1 τ)

noncomputable def KPSb9 (τ z : ℍ) : ℂ :=
      ((-2834623343488044556615680000 : ℂ)) * (Work.Asymptotics.K24F.r1 τ)

noncomputable def KPSb10 (τ z : ℍ) : ℂ :=
      ((-4013158619828433998315520000 : ℂ)) * (Work.Asymptotics.K24F.r1 τ)

noncomputable def KPSrest (τ z : ℍ) : ℂ :=
      KPSb1 τ z + KPSb2 τ z * (Work.Kernels.qParamFun z) ^ 1 + KPSb3 τ z * (Work.Kernels.qParamFun z) ^ 2 + KPSb4 τ z * (Work.Kernels.qParamFun z) ^ 3 + KPSb5 τ z * (Work.Kernels.qParamFun z) ^ 4 + KPSb6 τ z * (Work.Kernels.qParamFun z) ^ 5 + KPSb7 τ z * (Work.Kernels.qParamFun z) ^ 6 + KPSb8 τ z * (Work.Kernels.qParamFun z) ^ 7 + KPSb9 τ z * (Work.Kernels.qParamFun z) ^ 8 + KPSb10 τ z * (Work.Kernels.qParamFun z) ^ 9

private theorem bound_KPSb1 : BoundQ (fun τ z => KPSb1 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-31115290752 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((6480585584640 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((-1846675584 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((13066665984 : ℂ)) (BoundQ.monoM BoundQ_R0 (by norm_num))
  have h5 := BoundQ.const_mul ((-4302720 : ℂ)) (BoundQ.monoM BoundQ_Q1 (by norm_num))
  have h6 := BoundQ.const_mul ((-20736 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r2 (by norm_num))
  have h7 := BoundQ.const_mul ((-9403174656 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h8 := BoundQ.const_mul ((-20736 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r0 (by norm_num))
  have h9 := BoundQ.const_mul ((-252 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_Th0 (by norm_num))
  have h10 := BoundQ.const_mul ((41472 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_R0 (by norm_num))
  have h11 := BoundQ.const_mul ((-169827840 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r2 (by norm_num))
  have h12 := BoundQ.const_mul ((-221521732485120 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  have h13 := BoundQ.const_mul ((-169827840 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r0 (by norm_num))
  have h14 := BoundQ.const_mul ((141296762880 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_R0 (by norm_num))
  have h15 := BoundQ.const_mul ((461495024640 : ℂ)) (BoundQ.mulM (BoundQ.mulM (BoundQ_S0) BoundQ.jInvariantFun (by norm_num)) BoundQ_r1 (by norm_num))
  have h16 := BoundQ.const_mul ((-29262643200 : ℂ)) (BoundQ.mulM (BoundQ_S02) BoundQ_r0 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16).congr (fun τ z => by
    have hspec : ((41472 : ℂ)) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) = ((41472 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.R0 τ) := by
      calc ((41472 : ℂ)) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) = ((41472 : ℂ)) * (Work.Kernels.jInvariantFun τ ^ 2 * Work.Asymptotics.K24F.r1 τ) := by ring
        _ = ((41472 : ℂ)) * (Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.R0 τ) := by rw [j2r1_eq τ]
        _ = ((41472 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.R0 τ) := by ring
    simp only [KPSb1]
    rw [hspec]
    ring)

private theorem bound_KPSb2 : BoundQ (fun τ z => KPSb2 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-866897593344 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((3789324416286720 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((-197729620992 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((-1946760044544 : ℂ)) (BoundQ.monoM BoundQ_R0 (by norm_num))
  have h5 := BoundQ.const_mul ((-406425600 : ℂ)) (BoundQ.monoM BoundQ_Q1 (by norm_num))
  have h6 := BoundQ.const_mul ((-31104 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r2 (by norm_num))
  have h7 := BoundQ.const_mul ((-10712069793792 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h8 := BoundQ.const_mul ((-31104 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r0 (by norm_num))
  have h9 := BoundQ.const_mul ((62208 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_R0 (by norm_num))
  have h10 := BoundQ.const_mul ((-18348871680 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r2 (by norm_num))
  have h11 := BoundQ.const_mul ((69048683749048320 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  have h12 := BoundQ.const_mul ((-18348871680 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r0 (by norm_num))
  have h13 := BoundQ.const_mul ((4525019873280 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_R0 (by norm_num))
  have h14 := BoundQ.const_mul ((-230415754567680 : ℂ)) (BoundQ.mulM (BoundQ.mulM (BoundQ_S0) BoundQ.jInvariantFun (by norm_num)) BoundQ_r1 (by norm_num))
  have h15 := BoundQ.const_mul ((-669159014400 : ℂ)) (BoundQ.mulM (BoundQ_S02) BoundQ_r0 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15).congr (fun τ z => by
    have hspec : ((62208 : ℂ)) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) = ((62208 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.R0 τ) := by
      calc ((62208 : ℂ)) * (Work.Kernels.jInvariantFun τ) ^ 2 * (Work.Asymptotics.K24F.r1 τ) = ((62208 : ℂ)) * (Work.Kernels.jInvariantFun τ ^ 2 * Work.Asymptotics.K24F.r1 τ) := by ring
        _ = ((62208 : ℂ)) * (Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.R0 τ) := by rw [j2r1_eq τ]
        _ = ((62208 : ℂ)) * (Work.Kernels.jInvariantFun τ) * (Work.Asymptotics.K24F.R0 τ) := by ring
    simp only [KPSb2]
    rw [hspec]
    ring)

private theorem bound_KPSb3 : BoundQ (fun τ z => KPSb3 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-12901309655040 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((-1703225054430167040 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((-7096556759040 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((-82440390574080 : ℂ)) (BoundQ.monoM BoundQ_R0 (by norm_num))
  have h5 := BoundQ.const_mul ((-9293875200 : ℂ)) (BoundQ.monoM BoundQ_Q1 (by norm_num))
  have h6 := BoundQ.const_mul ((5511848782417920 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h7 := BoundQ.const_mul ((-685731225600 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r2 (by norm_num))
  have h8 := BoundQ.const_mul ((35064508057052774400 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  have h9 := BoundQ.const_mul ((-685731225600 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r0 (by norm_num))
  have h10 := BoundQ.const_mul ((11609505792000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_R0 (by norm_num))
  have h11 := BoundQ.const_mul ((1371462451200 : ℂ)) (BoundQ.mulM (BoundQ.mulM (BoundQ_S0) BoundQ.jInvariantFun (by norm_num)) BoundQ_r1 (by norm_num))
  have h12 := BoundQ.const_mul ((-5804752896000 : ℂ)) (BoundQ.mulM (BoundQ_S02) BoundQ_r0 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12).congr (fun τ z => by simp only [KPSb3] <;> ring)

private theorem bound_KPSb4 : BoundQ (fun τ z => KPSb4 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-120551280721920 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((-847593621691493253120 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((-103137022033920 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((-229442532802560 : ℂ)) (BoundQ.monoM BoundQ_R0 (by norm_num))
  have h5 := BoundQ.const_mul ((-80621568000 : ℂ)) (BoundQ.monoM BoundQ_Q1 (by norm_num))
  have h6 := BoundQ.const_mul ((16798850610462720 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h7 := BoundQ.const_mul ((-10932284620800 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r2 (by norm_num))
  have h8 := BoundQ.const_mul ((4521132461396223590400 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  have h9 := BoundQ.const_mul ((-10932284620800 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r0 (by norm_num))
  have h10 := BoundQ.const_mul ((34828517376000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_R0 (by norm_num))
  have h11 := BoundQ.const_mul ((21864569241600 : ℂ)) (BoundQ.mulM (BoundQ.mulM (BoundQ_S0) BoundQ.jInvariantFun (by norm_num)) BoundQ_r1 (by norm_num))
  have h12 := BoundQ.const_mul ((-17414258688000 : ℂ)) (BoundQ.mulM (BoundQ_S02) BoundQ_r0 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12).congr (fun τ z => by simp only [KPSb4] <;> ring)

private theorem bound_KPSb5 : BoundQ (fun τ z => KPSb5 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-574944650035200 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((-111040851154239199641600 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((-574944650035200 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((-241864704000 : ℂ)) (BoundQ.monoM BoundQ_Q1 (by norm_num))
  have h5 := BoundQ.const_mul ((1149889300070400 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h6 := BoundQ.const_mul ((-78364164096000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r2 (by norm_num))
  have h7 := BoundQ.const_mul ((177018003362145632256000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  have h8 := BoundQ.const_mul ((-78364164096000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r0 (by norm_num))
  have h9 := BoundQ.const_mul ((156728328192000 : ℂ)) (BoundQ.mulM (BoundQ.mulM (BoundQ_S0) BoundQ.jInvariantFun (by norm_num)) BoundQ_r1 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5) h6) h7) h8) h9).congr (fun τ z => by simp only [KPSb5] <;> ring)

private theorem bound_KPSb6 : BoundQ (fun τ z => KPSb6 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-24379962163200 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((-4573988896581020653977600 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((-24379962163200 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((48759924326400 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h5 := BoundQ.const_mul ((-208971104256000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r2 (by norm_num))
  have h6 := BoundQ.const_mul ((2873979162172871147520000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  have h7 := BoundQ.const_mul ((-208971104256000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r0 (by norm_num))
  have h8 := BoundQ.const_mul ((417942208512000 : ℂ)) (BoundQ.mulM (BoundQ.mulM (BoundQ_S0) BoundQ.jInvariantFun (by norm_num)) BoundQ_r1 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5) h6) h7) h8).congr (fun τ z => by simp only [KPSb6] <;> ring)

private theorem bound_KPSb7 : BoundQ (fun τ z => KPSb7 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((7836416409600000 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((-81720846598237417635840000 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((7836416409600000 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((-15672832819200000 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h5 := BoundQ.const_mul ((20790330604794905886720000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5).congr (fun τ z => by simp only [KPSb7] <;> ring)

private theorem bound_KPSb8 : BoundQ (fun τ z => KPSb8 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((7522959753216000 : ℂ)) (BoundQ.monoM BoundQ_r2 (by norm_num))
  have h2 := BoundQ.const_mul ((-705894449357811326386176000 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  have h3 := BoundQ.const_mul ((7522959753216000 : ℂ)) (BoundQ.monoM BoundQ_r0 (by norm_num))
  have h4 := BoundQ.const_mul ((-15045919506432000 : ℂ)) (BoundQ.mulM (BoundQ.jInvariantFun) BoundQ_r1 (by norm_num))
  have h5 := BoundQ.const_mul ((55738314164283805532160000 : ℂ)) (BoundQ.mulM (BoundQ_S0) BoundQ_r1 (by norm_num))
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (h1) h2) h3) h4) h5).congr (fun τ z => by simp only [KPSb8] <;> ring)

private theorem bound_KPSb9 : BoundQ (fun τ z => KPSb9 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-2834623343488044556615680000 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  exact (h1).congr (fun τ z => by simp only [KPSb9] <;> ring)

private theorem bound_KPSb10 : BoundQ (fun τ z => KPSb10 τ z) (-1) := by
  have h1 := BoundQ.const_mul ((-4013158619828433998315520000 : ℂ)) (BoundQ.monoM BoundQ_r1 (by norm_num))
  exact (h1).congr (fun τ z => by simp only [KPSb10] <;> ring)


private theorem bound_KPSrest : BoundQ (fun τ z => KPSrest τ z) (-1) := by
  have hb1 := bound_KPSb1
  have hb2 := bound_KPSb2
  have hb3 := bound_KPSb3
  have hb4 := bound_KPSb4
  have hb5 := bound_KPSb5
  have hb6 := bound_KPSb6
  have hb7 := bound_KPSb7
  have hb8 := bound_KPSb8
  have hb9 := bound_KPSb9
  have hb10 := bound_KPSb10
  have hqc2 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 1) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    simpa only [norm_pow, pow_one, zpow_zero, Real.rpow_zero, mul_one] using hq1
  have hqc3 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 2) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have hqc4 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 3) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have hqc5 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 4) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 4 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have hqc6 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 5) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 5 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have hqc7 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 6) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 6 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have hqc8 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 7) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 7 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have hqc9 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 8) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 8 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have hqc10 : BoundQ (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z) ^ 9) 0 := by
    refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      rw [hzim]; nlinarith [Real.pi_pos, hF.2]
    have h0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    have hp : ‖Work.Kernels.qParamFun z‖ ^ 9 ≤ 1 := pow_le_one₀ h0 hq1
    simpa only [norm_pow, zpow_zero, Real.rpow_zero, mul_one] using hp
  have g2 : BoundQ (fun τ z => KPSb2 τ z * (Work.Kernels.qParamFun z) ^ 1) (-1) := BoundQ.mulM hb2 hqc2 (by norm_num)
  have g3 : BoundQ (fun τ z => KPSb3 τ z * (Work.Kernels.qParamFun z) ^ 2) (-1) := BoundQ.mulM hb3 hqc3 (by norm_num)
  have g4 : BoundQ (fun τ z => KPSb4 τ z * (Work.Kernels.qParamFun z) ^ 3) (-1) := BoundQ.mulM hb4 hqc4 (by norm_num)
  have g5 : BoundQ (fun τ z => KPSb5 τ z * (Work.Kernels.qParamFun z) ^ 4) (-1) := BoundQ.mulM hb5 hqc5 (by norm_num)
  have g6 : BoundQ (fun τ z => KPSb6 τ z * (Work.Kernels.qParamFun z) ^ 5) (-1) := BoundQ.mulM hb6 hqc6 (by norm_num)
  have g7 : BoundQ (fun τ z => KPSb7 τ z * (Work.Kernels.qParamFun z) ^ 6) (-1) := BoundQ.mulM hb7 hqc7 (by norm_num)
  have g8 : BoundQ (fun τ z => KPSb8 τ z * (Work.Kernels.qParamFun z) ^ 7) (-1) := BoundQ.mulM hb8 hqc8 (by norm_num)
  have g9 : BoundQ (fun τ z => KPSb9 τ z * (Work.Kernels.qParamFun z) ^ 8) (-1) := BoundQ.mulM hb9 hqc9 (by norm_num)
  have g10 : BoundQ (fun τ z => KPSb10 τ z * (Work.Kernels.qParamFun z) ^ 9) (-1) := BoundQ.mulM hb10 hqc10 (by norm_num)
  exact (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (BoundQ.addM (hb1) g2) g3) g4) g5) g6) g7) g8) g9) g10).congr (fun τ z => by simp only [KPSrest] <;> ring)
/-! ## The split of `KPlusSumRefTail` -/

/-- `KPlusSumRefTail = KPS0 + q · KPSrest`. -/
theorem KPlusSumRefTail_split (τ z : ℍ) :
    KPlusSumRefTail τ z = KPS0 τ z + Work.Kernels.qParamFun z * KPSrest τ z := by
  simp only [KPlusSumRefTail, KPS0, KPSrest, KPSb1, KPSb2, KPSb3, KPSb4, KPSb5, KPSb6,
    KPSb7, KPSb8, KPSb9, KPSb10]
  ring

/-! ## The `K₊`-reference remainder -/

/-- **The `K₊`-reference remainder of `E`-degree `>= 6`.** -/
theorem KPlus24Ref_high_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖KPlus24Ref ℓ τ z
            - (-(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2))
              * (KPlusQ1 τ z * Work.Kernels.qParamFun z
                  + KPS0 τ z * (Work.Kernels.qParamFun z) ^ 2)‖
          ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ‖Work.Residues.Ept z‖ ^ 6 := by
  obtain ⟨Cb, Nb, Mb, hCb, hNb, hMb, hb⟩ := bound_KPSrest
  refine ⟨‖Work.Asymptotics.K24F.c‖ * Cb + 1, Nb, Mb + 2, by positivity, hNb, by positivity,
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hkey : KPlus24Ref ℓ τ z
        - (-(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2))
          * (KPlusQ1 τ z * Work.Kernels.qParamFun z
              + KPS0 τ z * (Work.Kernels.qParamFun z) ^ 2)
      = (-(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2))
        * ((Work.Kernels.qParamFun z) ^ 3 * KPSrest τ z) := by
    rw [KPlus24Ref, KPlusSumRef_E2 τ z, KPlusSumRefTail_split τ z]
    ring
  rw [hkey]
  have ht0 : (0 : ℝ) ≤ t := by have := hF.2; linarith
  have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have hzn : ‖(z : ℂ)‖ ≤ 1 + t := by
    have hre : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, hz1⟩
    have him : |z.im| ≤ t := by rw [hzim]; exact le_of_eq (abs_of_nonneg ht0)
    have h := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    linarith [h, hre, him]
  have hzt : ‖(z : ℂ)‖ ^ 2 ≤ (1 + t) ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖(z:ℂ)‖ := norm_nonneg _
    nlinarith [hzn, h0, ht0]
  have hq1z : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    rw [hzim]; nlinarith [Real.pi_pos, ht0]
  have hE : ‖Work.Kernels.qParamFun z‖ ^ 3 = ‖Work.Residues.Ept z‖ ^ 6 := by
    rw [Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, hzim]
    rw [show Real.exp (-(2 * Real.pi * t)) = (Real.exp (-(Real.pi * t))) ^ 2 by
      rw [sq, ← Real.exp_add]; congr 1; ring]
    ring
  have hb' := hb τ z t hF ht hz0 hz1 hzim
  rw [zpow_neg_one] at hb'
  have hc0 : (0:ℝ) ≤ ‖Work.Asymptotics.K24F.c‖ := norm_nonneg _
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hqinv0 : (0:ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ := inv_nonneg.mpr hq0
  have hs0 : (0:ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have h1 : ‖(-(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2))
        * ((Work.Kernels.qParamFun z) ^ 3 * KPSrest τ z)‖
      = ‖Work.Asymptotics.K24F.c‖ * ‖(z : ℂ)‖ ^ 2
        * (‖Work.Kernels.qParamFun z‖ ^ 3 * ‖KPSrest τ z‖) := by
    rw [norm_mul, norm_neg, norm_mul, norm_pow, norm_mul, norm_pow] <;> ring
  rw [h1, hE]
  have h2 : ‖Work.Asymptotics.K24F.c‖ * ‖(z : ℂ)‖ ^ 2
        * (‖Work.Residues.Ept z‖ ^ 6 * ‖KPSrest τ z‖)
      ≤ ‖Work.Asymptotics.K24F.c‖ * (1 + t) ^ 2
        * (‖Work.Residues.Ept z‖ ^ 6
            * (Cb * (‖Work.Kernels.qParamFun τ‖)⁻¹
                * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ Mb)) := by
    have hE6 : (0:ℝ) ≤ ‖Work.Residues.Ept z‖ ^ 6 := by positivity
    refine mul_le_mul (mul_le_mul le_rfl hzt (by positivity) (by positivity)) ?_ (by positivity)
      (by positivity)
    exact mul_le_mul_of_nonneg_left hb' hE6
  refine le_trans h2 ?_
  have h3 : ‖Work.Asymptotics.K24F.c‖ * (1 + t) ^ 2
        * (‖Work.Residues.Ept z‖ ^ 6
            * (Cb * (‖Work.Kernels.qParamFun τ‖)⁻¹
                * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ Mb))
      ≤ (‖Work.Asymptotics.K24F.c‖ * Cb + 1) * (‖Work.Kernels.qParamFun τ‖)⁻¹
        * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ (Mb + 2) * ‖Work.Residues.Ept z‖ ^ 6 := by
    have hU : (1 : ℝ) ≤ 1 + t := by linarith
    have h2t : (1 + t) ^ (2 : ℝ) ≤ (1 + t) ^ (Mb + 2) :=
      Real.rpow_le_rpow_of_exponent_le hU (by linarith)
    have h2t' : (1 + t) ^ 2 ≤ (1 + t) ^ (Mb + 2) := by
      have := Real.rpow_two (1 + t)
      rw [← this]; exact h2t
    have hse : (Work.Kernels.scale τ) ^ Nb ≤ (Work.Kernels.scale τ) ^ Nb := le_rfl
    have hE6 : (0:ℝ) ≤ ‖Work.Residues.Ept z‖ ^ 6 := by positivity
    have hK : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖⁻¹ * (Work.Kernels.scale τ) ^ Nb :=
      mul_nonneg hqinv0 (Real.rpow_nonneg hs0 _)
    calc ‖Work.Asymptotics.K24F.c‖ * (1 + t) ^ 2
          * (‖Work.Residues.Ept z‖ ^ 6
              * (Cb * (‖Work.Kernels.qParamFun τ‖)⁻¹
                  * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ Mb))
        = (‖Work.Asymptotics.K24F.c‖ * Cb)
            * ((1 + t) ^ 2 * (1 + t) ^ Mb)
            * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nb)
            * ‖Work.Residues.Ept z‖ ^ 6 := by ring
      _ ≤ (‖Work.Asymptotics.K24F.c‖ * Cb)
            * ((1 + t) ^ (Mb + 2))
            * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nb)
            * ‖Work.Residues.Ept z‖ ^ 6 := by
          have hpow : (1 + t) ^ 2 * (1 + t) ^ Mb = (1 + t) ^ (Mb + 2) := by
            rw [show (1 + t) ^ (2 : ℕ) = (1 + t) ^ (2 : ℝ) by rw [Real.rpow_two]]
            rw [← Real.rpow_add (by linarith : (0:ℝ) < 1 + t)]
            rw [show (2 : ℝ) + Mb = Mb + 2 by ring]
          rw [hpow]
      _ ≤ (‖Work.Asymptotics.K24F.c‖ * Cb + 1) * (‖Work.Kernels.qParamFun τ‖)⁻¹
            * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ (Mb + 2)
            * ‖Work.Residues.Ept z‖ ^ 6 := by
          have hU0 : (0:ℝ) ≤ (1 + t) ^ (Mb + 2) :=
            Real.rpow_nonneg (by linarith) _
          have hbase : (0:ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹
              * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ (Mb + 2)
              * ‖Work.Residues.Ept z‖ ^ 6 := by positivity
          have hCC : ‖Work.Asymptotics.K24F.c‖ * Cb ≤ ‖Work.Asymptotics.K24F.c‖ * Cb + 1 := by
            linarith
          have hstep : (‖Work.Asymptotics.K24F.c‖ * Cb)
                * ((1 + t) ^ (Mb + 2)
                    * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nb)
                    * ‖Work.Residues.Ept z‖ ^ 6)
              ≤ (‖Work.Asymptotics.K24F.c‖ * Cb + 1)
                * ((1 + t) ^ (Mb + 2)
                    * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nb)
                    * ‖Work.Residues.Ept z‖ ^ 6) :=
            mul_le_mul_of_nonneg_right hCC (by positivity)
          linarith [hstep]
      _ = (‖Work.Asymptotics.K24F.c‖ * Cb + 1) * (‖Work.Kernels.qParamFun τ‖)⁻¹
            * (Work.Kernels.scale τ) ^ Nb * (1 + t) ^ (Mb + 2)
            * ‖Work.Residues.Ept z‖ ^ 6 := by ring
  exact h3

end

end Work.Asymptotics.KhatE1Core
