import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.RopGen.sliceSecNonposBochner
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.wt_bddAbove_of_compact
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.weakSliceZContinuousAe
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Uop_PhiTs_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set MeasureTheory

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts about `StarPkg` and about the angular functions

The estimates of the target lemma are obtained from `StarPkg` (which bounds `∂_θ𝒰`,
`ℛ` and `𝒱` in the weighted-`L∞` norms) together with

* the pointwise identity `tan θ · 𝒰 = 𝒱 - ℛ` (which converts the `ℛ, 𝒱`-bounds into a
  bound on the *radial* derivatives of `𝒰` — this is where the factor `cos θ/ sin θ`,
  hence `sin(2θ)` for `θ ≥ π/4`, comes from);
* the mean-value theorems in the `θ`-direction (using the `Tendsto` hypothesis) and in
  the `z`-direction (using the vanishing of the `z = 0` slice and the `C^∞`-smoothness
  of the slices on the open quadrant);
* the structural fact that `D_θ^a 𝒰` for `a ≥ 1` carries a factor `sin(2θ)`. -/



/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≤ 1`. -/
theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _





/-! ## Differentiability in `z` of the iterated `z`-derivatives of a smooth slice -/

theorem differentiableAt_pzIter_slice_smooth {h : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi (-1)))
    (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := by
  have hgen : ∀ j : ℕ, ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' => Work.Spaces.pzIter j h z' θ) (Set.Ioi (-1)) := by
    intro j
    induction j with
    | zero => simpa using hsm
    | succ j ih =>
      have h' : ContDiffOn ℝ Work.Stability.smoothOrder
          (deriv (fun z' => Work.Spaces.pzIter j h z' θ)) (Set.Ioi (-1)) :=
        ih.deriv_of_isOpen isOpen_Ioi (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
      simpa [Work.Spaces.pzIter_succ, Work.Spaces.pz] using h'
  have hz' : z ∈ Set.Ioi (-1 : ℝ) := by
    have := Set.mem_Ioi.mp hz
    exact Set.mem_Ioi.mpr (by linarith)
  exact ((hgen k).contDiffAt (isOpen_Ioi.mem_nhds hz')).differentiableAt
    (by simp)

/-! ## The differentiated form of the identity `tan θ · 𝒰 = 𝒱 - ℛ`

`ℛ(Ψ) - 𝒱(Ψ) = tan θ·(3Ψ + αz∂_zΨ) = - tan θ·𝒰(Ψ)` (`Work.FTS.Nonlinear.Pieces.Rl1.
Rop_sub_Vop_eq_tan`), so `tan θ·𝒰 = 𝒱 - ℛ`.  Differentiating `k` times in `z` gives the
bounds on `∂_z^k𝒰` that the estimates need, since `∂_z^k𝒱` and `∂_z^kℛ` are `𝒲^{4,∞}`-bounded
by `StarPkg`. -/


/-! ## The Stirling-weighted sum bound -/









end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_bad_hi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `row15_bad_hi`: the "bad" angular endpoint for the `N₂^{ss}` row, higher-derivative branch

Row 15 of the nonlinear estimates is about `N₂^{ss} = -2·U(Φ̃_*)·∂_θF_*`.  The companion lemma
`row15_bad` rules out the case in which `θ ↦ U(Φ̃_*)(z,θ)` is bounded away from `0` near
`θ = 0`: there `|N₂^{ss}|` itself blows up like `θ^{α/3-1}` and the `i = 0` slot of
`HkIntegrand α 4 (N₂^{ss})` is not integrable.

The present lemma covers the *higher-derivative* branch: if some `k`-th `z`-derivative
(`1 ≤ k ≤ 4`) of `U(Φ̃_*)` is bounded away from `0` near `θ = 0⁺` while all the lower ones tend
to `0`, then still `θ ↦ HkIntegrand α 4 (N₂^{ss}) z θ` is not integrable on `Iθ`.

The mathematics is the same one-sided blow-up test, one slot further up in the pure-`D_z`
block of the integrand.  With `U := Uop α (PhiTs α Φs)` and `P := ∂_θF_*`:

* `∂_θF_*` factorizes as `α(Γ'(θ)/c)·2z/(1+z)²`, so every `D_z^m P` is a `z`-dependent
  constant times `∂_θF_*` itself (`PthFstar_DzIter_le` below), while
  `|∂_θF_*| ≥ c·θ^{α/3-1}` near `0` (`pth_Fstar_lower`);
* the Leibniz rule `D_z^k (U·P) = Σ_b C(k,b) D_z^b U · D_z^{k-b} P` and the Stirling expansion
  `D_z^k = Σ_{j≤k} S(k,j) z^j ∂_z^j` convert the hypothesis on `∂_z^k U` into
  `|D_z^k U| ≥ ρ > 0` eventually and `D_z^b U → 0` for `b < k`
  (`DzIter_k_bounded_below`, `DzIter_low_vanish`), so the top term of the sum dominates
  (`DzIter_sum_lower_bound`);
* hence `|D_z^k (N₂^{ss})(z,θ)| ≳ θ^{α/3-1}`, and the `i = k` slot of the pure-`D_z` block of
  the integrand carries the weight `sin(2θ)^{-η}`, giving
  `HkIntegrand α 4 (N₂^{ss})(z,θ) ≳ θ^{2α/3-2-η}`.  Since `2α/3-2-η ≤ -7/3 < -1`, that power is
  not integrable at `0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## Linear behaviour of `D_z^j` under multiplication by a factor depending only on `θ` -/

/-- A multiplier depending on the angle only passes through the radial iterates `D_z^j`:
`D_z^j (c(θ)·g)(z,θ) = c(θ)·D_z^j g (z,θ)`. -/
private theorem DzIter_theta_mul (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c θ * g z θ) z θ
      = c θ * Work.Spaces.DzIter j g z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ n ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter n (fun z θ => c θ * g z θ) z' θ) z
      = c θ * (z * deriv (fun z' => Work.Spaces.DzIter n g z' θ) z)
    rw [show (fun z' => Work.Spaces.DzIter n (fun z θ => c θ * g z θ) z' θ)
          = (fun z' => c θ * Work.Spaces.DzIter n g z' θ) from funext fun z' => ih z' θ,
      deriv_const_mul_field]
    ring


/-- Multiplication by a constant passes through the radial iterates. -/
private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.DzIter j f z θ :=
  DzIter_theta_mul (fun _ => c) f j z θ

/-- `D_z^j` of a function of `z` alone does not depend on the angle. -/
private theorem DzIter_radial_indep (G : ℝ → ℝ) (j : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter j (fun z _ => G z) z θ = Work.Spaces.DzIter j (fun z _ => G z) z θ' := by
  induction j generalizing z θ θ' with
  | zero => rfl
  | succ n ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ) z
      = z * deriv (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ') z
    rw [show (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ)
          = (fun z' => Work.Spaces.DzIter n (fun z _ => G z) z' θ')
        from funext fun z' => ih z' θ θ']

/-- The Stirling number of the second kind on the diagonal: `S(n,n) = 1`. -/
private theorem scoef_self (n : ℕ) : Work.Spaces.scoef n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 1) * Work.Spaces.scoef n (n + 1) + Work.Spaces.scoef n n = 1
    rw [Work.Spaces.scoef_succ_self_eq_zero n, ih]
    simp


/-! ## The `θ`-only factorization of `∂_θ F_*` and its higher `D_z`-iterates -/


/-! ## The Stirling bridge from `∂_z^j` to `D_z^j` -/




/-! ## The elementary `Finset` estimate isolating the top term -/



end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.Top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof
  galFam GlobalODEExistence IsDynGSolWith)

set_option autoImplicit false
set_option linter.unusedVariables false






end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.DensN0Pointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem DensN0Pointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ C₀ B : ℝ} {g : Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.K θ * |Work.Construction.N0 α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ|
          ≤ C * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
  obtain ⟨CL, hCLpos, hCL⟩ := L12XnBound
  obtain ⟨CFs, hCFspos, hCFs⟩ := FstarSlotBounds
  have hCL0 : 0 ≤ CL := hCLpos.le
  have hCFs0 : 0 ≤ CFs := hCFspos.le
  refine ⟨14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8, ?_, ?_⟩
  · have h2 : 0 < 14 * CL * (CFs + 1) := by nlinarith
    linarith
  intro α hαIoc ρ Φs E ε τ C₀ B g Maj hDec hClass hXn hXn6 s hs θ hθ
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hs0 : (0 : ℝ) < s := hs
  obtain ⟨hMaj0, hMaj1, -, hSlot1, -⟩ := hDec
  -- ## the projected slice `f` and the full profile `F = F_* + f`
  set f : ℝ → ℝ → ℝ := slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hfdef
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ with hFdef
  have hF : ∀ z θ : ℝ, F z θ = Work.Construction.Fstar α z θ + f z θ := by
    intro z θ; rw [hFdef, hfdef]; rfl
  -- ## the two size constants are nonnegative
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith [hX, hXn, pow_pos hα 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  have hA1 : 1 ≤ (1 + C₀) * (1 + B) := by nlinarith
  have h1C : 0 ≤ 1 + C₀ := by linarith
  have h1B : 0 ≤ 1 + B := by linarith
  -- ## the angular facts
  obtain ⟨hKnn, hKcos, hcos0, -, -, -, -, -⟩ := AngFacts
  -- ## abbreviations
  set H : ℝ := s / (1 + s) ^ 2 with hHdef
  have hH0 : 0 ≤ H := by rw [hHdef]; exact div_nonneg hs0.le (sq_nonneg _)
  set Q : ℝ := Maj s + H with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact add_nonneg (hMaj0 s) hH0
  have hHQ : H ≤ Q := by rw [hQdef]; linarith [hMaj0 s]
  have hMQ : Maj s ≤ Q := by rw [hQdef]; linarith [hH0]
  -- ## the slot bounds for `f`
  have hf0 : |f s θ| ≤ Maj s := by
    simpa using hSlot1 s hs θ 0 0 (by norm_num)
  have hDthf : |Work.Spaces.Dth f s θ| ≤ Maj s := by
    simpa using hSlot1 s hs θ 0 1 (by norm_num)
  have hDzf : |Work.Spaces.Dz f s θ| ≤ Maj s := by
    simpa using hSlot1 s hs θ 1 0 (by norm_num)
  -- ## the `F_*`-slot bounds
  obtain ⟨hFa, hs2pthFa, hDzFa, hKpthFa, -⟩ :=
    hCFs (α := α) (z := s) (θ := θ) hαIoc hs0 hθ
  have hL12Fa : Work.Construction.L12 (Work.Construction.Fstar α) s = 2 * α / (1 + s) :=
    Work.Construction.L12_Fstar_eq hα hα1 hs0.le
  have hL12Fa_abs : |Work.Construction.L12 (Work.Construction.Fstar α) s| ≤ 2 * α / (1 + s) :=
    le_of_eq (by rw [hL12Fa, abs_of_nonneg (by positivity)])
  -- ## the `L₁₂(f)`-size
  have hqo : Work.FTS.VocabO.HQo α 4 f :=
    ⟨hClass.reg, Work.FTS.OpenPkg.HkMem_mono_open hClass.reg 4 (by norm_num) hClass.mem⟩
  have hl : |Work.Construction.L12 f s| ≤ CL * (C₀ * α ^ 2) :=
    le_trans (hCL α hα f hqo s hs0.le) (mul_le_mul_of_nonneg_left hXn hCL0)
  -- ## the combined slot bound `CFs H + Maj s ≤ (CFs+1) Q`
  have hWle : CFs * H + Maj s ≤ (CFs + 1) * Q := by
    have h1 : CFs * H ≤ CFs * Q := mul_le_mul_of_nonneg_left hHQ hCFs0
    have h2 : CFs * Q + Maj s ≤ CFs * Q + Q := add_le_add_right hMQ (CFs * Q)
    have h3 : (CFs + 1) * Q = CFs * Q + Q := by ring
    linarith [h1, h2, h3]
  rcases eq_or_lt_of_le hθ.1 with hθz | hθz
  · -- the endpoint `θ = 0`: `K 0 = 0`
    subst hθz
    have hKz : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
    rw [hKz, zero_mul, Real.cos_zero, mul_one]
    have hCpos : 0 < 14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8 := by
      have h2 : 0 < 14 * CL * (CFs + 1) := by nlinarith
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hCpos.le h1C) h1B) hQ0
  · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
    · -- the endpoint `θ = π/2`: `K (π/2) = 0` and `cos (π/2) = 0`
      subst hθp
      have hKp : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hKp, zero_mul, Real.cos_pi_div_two, mul_zero]
    · -- ## the interior of `Iθ`
      have hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθz, hθp⟩
      have hK0 : 0 ≤ Work.Spaces.K θ := hKnn θ hθ
      have hKle : Work.Spaces.K θ ≤ 2 * Real.cos θ := hKcos θ hθ
      have hc0 : 0 ≤ Real.cos θ := hcos0 θ hθ
      -- ## the `θ`- and `z`-slices of `f` are differentiable (for the split of `Dz F`, `pth F`)
      have hfdθ : DifferentiableAt ℝ (fun θ' : ℝ => f s θ') θ :=
        ((hClass.reg.curry_θ hs0).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθi)
      have hfdz : DifferentiableAt ℝ (fun z' : ℝ => f z' θ) s :=
        (hClass.reg.hasDerivAt_slice hθi hs0).differentiableAt
      have hpthF : |Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ|
          ≤ |Work.Spaces.pth f s θ| := by
        have h := abs_deriv_add_sub_le (fun t : ℝ => Work.Construction.Fstar α s t)
          (fun t : ℝ => f s t) hfdθ
        have hcongr : (fun t : ℝ => Work.Construction.Fstar α s t + f s t) = fun t => F s t := by
          funext t; rw [hF s t]
        rw [hcongr] at h
        simpa only [Work.Spaces.pth] using h
      have hpzF : |Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ|
          ≤ |Work.Spaces.pz f s θ| := by
        have h := abs_deriv_add_sub_le (fun t : ℝ => Work.Construction.Fstar α t θ)
          (fun t : ℝ => f t θ) hfdz
        have hcongr : (fun t : ℝ => Work.Construction.Fstar α t θ + f t θ) = fun t => F t θ := by
          funext t; rw [hF t θ]
        rw [hcongr] at h
        simpa only [Work.Spaces.pz] using h
      -- ## the combined slot bounds for `F = F_* + f`
      have hs2pthF : |Real.sin (2 * θ) * Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
        have hsplit : Real.sin (2 * θ) * Work.Spaces.pth F s θ
            = Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ
              + Real.sin (2 * θ)
                * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ) := by
          ring
        rw [hsplit]
        have h2 : |Real.sin (2 * θ)
            * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ)|
            ≤ |Work.Spaces.Dth f s θ| := by
          rw [abs_mul]
          calc |Real.sin (2 * θ)| * |Work.Spaces.pth F s θ
                - Work.Spaces.pth (Work.Construction.Fstar α) s θ|
              ≤ |Real.sin (2 * θ)| * |Work.Spaces.pth f s θ| :=
                mul_le_mul_of_nonneg_left hpthF (abs_nonneg _)
            _ = |Work.Spaces.Dth f s θ| := by rw [Work.Spaces.Dth, abs_mul]
        have h3 : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ
              + Real.sin (2 * θ)
                * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ)|
            ≤ CFs * H + Maj s := by
          have h1 := abs_add_le
            (Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ)
            (Real.sin (2 * θ)
              * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ))
          linarith [h1, hs2pthFa, h2, hDthf]
        linarith [h3, hWle]
      have hDzF : |Work.Spaces.Dz F s θ| ≤ (CFs + 1) * Q := by
        have hsplit : Work.Spaces.Dz F s θ
            = Work.Spaces.Dz (Work.Construction.Fstar α) s θ
              + (Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ) := by
          ring
        rw [hsplit]
        have h2 : |Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ|
            ≤ |Work.Spaces.Dz f s θ| := by
          have h3 : Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ
              = s * (Work.Spaces.pz F s θ
                  - Work.Spaces.pz (Work.Construction.Fstar α) s θ) := by
            rw [Work.Spaces.Dz, Work.Spaces.Dz]; ring
          have h4 : |s * (Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ)|
              = s * |Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ| := by
            rw [abs_mul, abs_of_pos hs0]
          rw [h3, h4]
          calc s * |Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ|
              ≤ s * |Work.Spaces.pz f s θ| := mul_le_mul_of_nonneg_left hpzF hs0.le
            _ = |Work.Spaces.Dz f s θ| := by rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0]
        have h4 : |Work.Spaces.Dz (Work.Construction.Fstar α) s θ
              + (Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ)|
            ≤ CFs * H + Maj s := by
          have h1 := abs_add_le (Work.Spaces.Dz (Work.Construction.Fstar α) s θ)
            (Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ)
          linarith [h1, hDzFa, h2, hDzf]
        linarith [h4, hWle]
      -- ## `|c2m θ| ≤ 2`
      have hc2m : |Work.Construction.c2m θ| ≤ 2 := by
        have h1 : Work.Construction.c2m θ = Real.cos (2 * θ) - Real.sin θ ^ 2 := rfl
        rw [h1, abs_le]
        have hsin0 : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
        constructor
        · nlinarith [Real.neg_one_le_cos (2 * θ), sq_nonneg (Real.sin θ), Real.sin_le_one θ, hsin0]
        · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]
      -- ## the ratio bound `2α/(1+s) ≤ 2`
      have hrat : 2 * α / (1 + s) ≤ 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + s)]
        nlinarith [hα.le]
      -- ## T1
      set T1 : ℝ := (3 / (2 * α)) * Real.sin (2 * θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) s
        * Work.Spaces.pth (Work.Construction.Fstar α) s θ with hT1def
      set T2 : ℝ := Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) s
        * Work.Spaces.Dz (Work.Construction.Fstar α) s θ with hT2def
      set T3 : ℝ := (1 / α) * Work.Construction.L12 f s * f s θ with hT3def
      set T4 : ℝ := (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 f s
        * Work.Spaces.pth F s θ with hT4def
      set T5 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 f s
        * Work.Spaces.Dz F s θ with hT5def
      set T6 : ℝ := Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) s
        * Work.Spaces.Dz f s θ with hT6def
      have hT1fac : |T1| ≤ 3 * CFs * H := by
        have h0 : |T1| ≤ |3 / (2 * α)| * |Real.sin (2 * θ)|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.pth (Work.Construction.Fstar α) s θ| := by
          rw [hT1def]
          exact abs_mul4_le _ _ _ _
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))] at h0
        have h3 : 3 / (2 * α) * |Real.sin (2 * θ)|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.pth (Work.Construction.Fstar α) s θ|
            = 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) s|
              * (|Real.sin (2 * θ)| * |Work.Spaces.pth (Work.Construction.Fstar α) s θ|) := by
          ring
        rw [h3] at h0
        have h4 : |Real.sin (2 * θ)| * |Work.Spaces.pth (Work.Construction.Fstar α) s θ|
            = |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ| := by
          rw [abs_mul]
        rw [h4] at h0
        have h6 : 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ|
            ≤ 3 / (2 * α) * (2 * α / (1 + s)) * (CFs * H) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL12Fa_abs (by positivity)) hs2pthFa
            (abs_nonneg _) (by positivity)
        have h5 : 3 / (2 * α) * (2 * α / (1 + s)) * (CFs * H) = 3 * CFs * H / (1 + s) := by
          field_simp
        have hnn : 0 ≤ 3 * CFs * H := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hH0
        have h7 : 3 * CFs * H / (1 + s) ≤ 3 * CFs * H := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + s)]
          have h8 : 0 ≤ 3 * CFs * H * s := mul_nonneg hnn hs0.le
          linarith
        linarith [h0, h6, h5, h7]
      have hT1 : Work.Spaces.K θ * |T1| ≤ 6 * CFs * Q * Real.cos θ := by
        have hX0 : 0 ≤ 3 * CFs * H := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hH0
        have h1 : Work.Spaces.K θ * |T1| ≤ Work.Spaces.K θ * (3 * CFs * H) :=
          mul_le_mul_of_nonneg_left hT1fac hK0
        have h2 : Work.Spaces.K θ * (3 * CFs * H) ≤ (2 * Real.cos θ) * (3 * CFs * H) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have hXQ0 : 0 ≤ 3 * CFs * Q := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hQ0
        have h3 : (2 * Real.cos θ) * (3 * CFs * H) ≤ (2 * Real.cos θ) * (3 * CFs * Q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHQ (by positivity)) (by positivity)
        have h4 : (2 * Real.cos θ) * (3 * CFs * Q) = 6 * CFs * Q * Real.cos θ := by ring
        linarith [h1, h2, h3, h4]
      have hT2fac : |T2| ≤ 4 * CFs * H := by
        have h0 : |T2| ≤ |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz (Work.Construction.Fstar α) s θ| := by
          rw [hT2def]
          exact abs_mul3_le _ _ _
        have h3 : |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|
            ≤ 2 * (2 * α / (1 + s)) * (CFs * H) :=
          mul_le_mul (mul_le_mul hc2m hL12Fa_abs (abs_nonneg _) (by norm_num)) hDzFa
            (abs_nonneg _) (by positivity)
        have hnn : 0 ≤ CFs * H := mul_nonneg hCFs0 hH0
        have h5 : 2 * (2 * α / (1 + s)) ≤ 4 := by linarith [hrat]
        have h6 := mul_le_mul_of_nonneg_right h5 hnn
        have h4 : 2 * (2 * α / (1 + s)) * (CFs * H) ≤ 4 * CFs * H := by linarith [h6]
        linarith [h0, h3, h4]
      have hT2 : Work.Spaces.K θ * |T2| ≤ 8 * CFs * Q * Real.cos θ := by
        have hX0 : 0 ≤ 4 * CFs * H := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hH0
        have h1 : Work.Spaces.K θ * |T2| ≤ Work.Spaces.K θ * (4 * CFs * H) :=
          mul_le_mul_of_nonneg_left hT2fac hK0
        have h2 : Work.Spaces.K θ * (4 * CFs * H) ≤ (2 * Real.cos θ) * (4 * CFs * H) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h3 : (2 * Real.cos θ) * (4 * CFs * H) ≤ (2 * Real.cos θ) * (4 * CFs * Q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHQ (by positivity)) (by positivity)
        have h4 : (2 * Real.cos θ) * (4 * CFs * Q) = 8 * CFs * Q * Real.cos θ := by ring
        linarith [h1, h2, h3, h4]
      have hT3fac : |T3| ≤ CL * C₀ * Q := by
        have h0 : |T3| ≤ |1 / α| * |Work.Construction.L12 f s| * |f s θ| := by
          rw [hT3def]
          exact abs_mul3_le _ _ _
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)] at h0
        have h3 : 1 / α * |Work.Construction.L12 f s| * |f s θ|
            ≤ 1 / α * (CL * (C₀ * α ^ 2)) * Maj s :=
          mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity)) hf0
            (abs_nonneg _) (by positivity)
        have h5 : 1 / α * (CL * (C₀ * α ^ 2)) * Maj s = CL * C₀ * α * Maj s := by
          field_simp
        have hnn : 0 ≤ CL * C₀ := mul_nonneg hCL0 hC₀0
        have h7 : CL * C₀ * α ≤ CL * C₀ * 1 := mul_le_mul_of_nonneg_left hα1 hnn
        have h8 : CL * C₀ * α * Maj s ≤ CL * C₀ * Maj s := by
          have h9 := mul_le_mul_of_nonneg_right h7 (hMaj0 s)
          linarith [h9]
        have h10 : CL * C₀ * Maj s ≤ CL * C₀ * Q := mul_le_mul_of_nonneg_left hMQ hnn
        have h6 : CL * C₀ * α * Maj s ≤ CL * C₀ * Q := by linarith [h8, h10]
        linarith [h0, h3, h5, h6]
      have hT3 : Work.Spaces.K θ * |T3| ≤ 2 * CL * (1 + C₀) * Q * Real.cos θ := by
        have hX0 : 0 ≤ CL * C₀ * Q := mul_nonneg (mul_nonneg hCL0 hC₀0) hQ0
        have h1 : Work.Spaces.K θ * |T3| ≤ Work.Spaces.K θ * (CL * C₀ * Q) :=
          mul_le_mul_of_nonneg_left hT3fac hK0
        have h2 : Work.Spaces.K θ * (CL * C₀ * Q) ≤ (2 * Real.cos θ) * (CL * C₀ * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h5 : CL * C₀ ≤ CL * (1 + C₀) := mul_le_mul_of_nonneg_left (by linarith) hCL0
        have h6 : CL * C₀ * Q ≤ CL * (1 + C₀) * Q := mul_le_mul_of_nonneg_right h5 hQ0
        have h3 : (2 * Real.cos θ) * (CL * C₀ * Q) ≤ (2 * Real.cos θ) * (CL * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        have h4 : (2 * Real.cos θ) * (CL * (1 + C₀) * Q)
            = 2 * CL * (1 + C₀) * Q * Real.cos θ := by ring
        linarith [h1, h2, h3, h4]
      have hT4fac : |T4| ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by
        have h0 : |T4| ≤ |3 / (2 * α)| * |Real.sin (2 * θ)|
            * |Work.Construction.L12 f s| * |Work.Spaces.pth F s θ| := by
          rw [hT4def]
          exact abs_mul4_le _ _ _ _
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))] at h0
        have h3 : 3 / (2 * α) * |Real.sin (2 * θ)| * |Work.Construction.L12 f s|
            * |Work.Spaces.pth F s θ|
            = 3 / (2 * α) * |Work.Construction.L12 f s|
              * (|Real.sin (2 * θ)| * |Work.Spaces.pth F s θ|) := by ring
        rw [h3] at h0
        have h4 : |Real.sin (2 * θ)| * |Work.Spaces.pth F s θ|
            = |Real.sin (2 * θ) * Work.Spaces.pth F s θ| := by rw [abs_mul]
        rw [h4] at h0
        have h6 : 3 / (2 * α) * |Work.Construction.L12 f s|
            * |Real.sin (2 * θ) * Work.Spaces.pth F s θ|
            ≤ 3 / (2 * α) * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity)) hs2pthF
            (abs_nonneg _) (by positivity)
        have h8 : 3 / (2 * α) * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q)
            = 3 / 2 * CL * C₀ * α * ((CFs + 1) * Q) := by field_simp
        have hZ0 : 0 ≤ (CFs + 1) * Q := by positivity
        have hnn : 0 ≤ CL * C₀ := mul_nonneg hCL0 hC₀0
        have h11 : CL * C₀ * α ≤ CL * C₀ := by
          have h12 := mul_le_mul_of_nonneg_left hα1 hnn
          linarith [h12]
        have h13 : CL * C₀ * α * ((CFs + 1) * Q) ≤ CL * C₀ * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right h11 hZ0
        have h14 : CL * C₀ * ((CFs + 1) * Q) ≤ CL * (1 + C₀) * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCL0) hZ0
        have h15 : CL * C₀ * α * ((CFs + 1) * Q) ≤ CL * (1 + C₀) * ((CFs + 1) * Q) := by
          linarith [h13, h14]
        have h16 : 3 / 2 * (CL * C₀ * α * ((CFs + 1) * Q))
            ≤ 3 / 2 * (CL * (1 + C₀) * ((CFs + 1) * Q)) :=
          mul_le_mul_of_nonneg_left h15 (by norm_num)
        have hD0 : 0 ≤ CL * (1 + C₀) * ((CFs + 1) * Q) := by positivity
        have h18 : 3 / 2 * (CL * (1 + C₀) * ((CFs + 1) * Q))
            ≤ 3 * (CL * (1 + C₀) * ((CFs + 1) * Q)) := by linarith [hD0]
        have h19 : 3 * (CL * (1 + C₀) * ((CFs + 1) * Q))
            = 3 * CL * (CFs + 1) * (1 + C₀) * Q := by ring
        have hfinal : 3 / 2 * CL * C₀ * α * ((CFs + 1) * Q)
            ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by
          calc 3 / 2 * CL * C₀ * α * ((CFs + 1) * Q)
              = 3 / 2 * (CL * C₀ * α * ((CFs + 1) * Q)) := by ring
            _ ≤ 3 / 2 * (CL * (1 + C₀) * ((CFs + 1) * Q)) := h16
            _ ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by linarith [h18, h19]
        linarith [h0, h6, h8, hfinal]
      have hT4 : Work.Spaces.K θ * |T4| ≤ 6 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by
        have hX0 : 0 ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by positivity
        have h1 : Work.Spaces.K θ * |T4|
            ≤ Work.Spaces.K θ * (3 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_left hT4fac hK0
        have h2 : Work.Spaces.K θ * (3 * CL * (CFs + 1) * (1 + C₀) * Q)
            ≤ (2 * Real.cos θ) * (3 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h4 : (2 * Real.cos θ) * (3 * CL * (CFs + 1) * (1 + C₀) * Q)
            = 6 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by ring
        linarith [h1, h2, h4]
      have hT5fac : |T5| ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by
        have h0 : |T5| ≤ |Work.Construction.c2m θ| * |Work.Construction.L12 f s|
            * |Work.Spaces.Dz F s θ| := by
          rw [hT5def]
          exact abs_mul3_le _ _ _
        have h3 : |Work.Construction.c2m θ| * |Work.Construction.L12 f s|
            * |Work.Spaces.Dz F s θ| ≤ 2 * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul hc2m hl (abs_nonneg _) (by norm_num)) hDzF
            (abs_nonneg _) (by positivity)
        have hZ0 : 0 ≤ (CFs + 1) * Q := by positivity
        have hnn : 0 ≤ CL * C₀ := mul_nonneg hCL0 hC₀0
        have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα1, hα.le]
        have h9 : CL * C₀ * α ^ 2 ≤ CL * C₀ := by
          have h10 := mul_le_mul_of_nonneg_left hα2 hnn
          linarith [h10]
        have h10 : CL * C₀ * α ^ 2 * ((CFs + 1) * Q) ≤ CL * C₀ * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right h9 hZ0
        have h11 : CL * C₀ * ((CFs + 1) * Q) ≤ CL * (1 + C₀) * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCL0) hZ0
        have h13 : CL * (1 + C₀) * ((CFs + 1) * Q) = CL * (CFs + 1) * (1 + C₀) * Q := by ring
        have h15 : 2 * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q)
            = 2 * (CL * C₀ * α ^ 2 * ((CFs + 1) * Q)) := by ring
        have hfinal : 2 * (CL * C₀ * α ^ 2 * ((CFs + 1) * Q))
            ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by
          have hx : 0 ≤ CL * (CFs + 1) * (1 + C₀) * Q := by positivity
          calc 2 * (CL * C₀ * α ^ 2 * ((CFs + 1) * Q))
              ≤ 2 * (CL * C₀ * ((CFs + 1) * Q)) := by linarith [h10]
            _ ≤ 2 * (CL * (1 + C₀) * ((CFs + 1) * Q)) := by linarith [h11]
            _ = 2 * CL * (CFs + 1) * (1 + C₀) * Q := by rw [h13]; ring_nf
            _ ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by linarith [hx]
        linarith [h0, h3, h15, hfinal]
      have hT5 : Work.Spaces.K θ * |T5| ≤ 8 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by
        have hX0 : 0 ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by positivity
        have h1 : Work.Spaces.K θ * |T5|
            ≤ Work.Spaces.K θ * (4 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_left hT5fac hK0
        have h2 : Work.Spaces.K θ * (4 * CL * (CFs + 1) * (1 + C₀) * Q)
            ≤ (2 * Real.cos θ) * (4 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h4 : (2 * Real.cos θ) * (4 * CL * (CFs + 1) * (1 + C₀) * Q)
            = 8 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by ring
        linarith [h1, h2, h4]
      have hT6fac : |T6| ≤ 4 * Q := by
        have h0 : |T6| ≤ |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz f s θ| := by
          rw [hT6def]
          exact abs_mul3_le _ _ _
        have h3 : |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz f s θ| ≤ 2 * (2 * α / (1 + s)) * Maj s :=
          mul_le_mul (mul_le_mul hc2m hL12Fa_abs (abs_nonneg _) (by norm_num)) hDzf
            (abs_nonneg _) (by positivity)
        have h5 : 2 * (2 * α / (1 + s)) ≤ 4 := by linarith [hrat]
        have h6 : 2 * (2 * α / (1 + s)) * Maj s ≤ 4 * Maj s :=
          mul_le_mul_of_nonneg_right h5 (hMaj0 s)
        have h7 : 4 * Maj s ≤ 4 * Q := mul_le_mul_of_nonneg_left hMQ (by norm_num)
        linarith [h0, h3, h6, h7]
      have hT6 : Work.Spaces.K θ * |T6| ≤ 8 * Q * Real.cos θ := by
        have hX0 : 0 ≤ 4 * Q := by linarith [hQ0]
        have h1 : Work.Spaces.K θ * |T6| ≤ Work.Spaces.K θ * (4 * Q) :=
          mul_le_mul_of_nonneg_left hT6fac hK0
        have h2 : Work.Spaces.K θ * (4 * Q) ≤ (2 * Real.cos θ) * (4 * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h4 : (2 * Real.cos θ) * (4 * Q) = 8 * Q * Real.cos θ := by ring
        linarith [h1, h2, h4]
      -- ## assembly
      have hexp : Work.Construction.N0 α F f s θ = T1 + (-T2) + T3 + T4 + (-T5) + (-T6) := by
        rw [hT1def, hT2def, hT3def, hT4def, hT5def, hT6def]
        simp only [Work.Construction.N0, Work.Construction.s2]
        ring
      rw [hexp]
      have hsumabs : |T1 + -T2 + T3 + T4 + -T5 + -T6|
          ≤ |T1| + |T2| + |T3| + |T4| + |T5| + |T6| := by
        simpa only [abs_neg] using abs_six_le T1 (-T2) T3 T4 (-T5) (-T6)
      have hXX : Work.Spaces.K θ * (|T1| + |T2| + |T3| + |T4| + |T5| + |T6|)
          = Work.Spaces.K θ * |T1| + Work.Spaces.K θ * |T2| + Work.Spaces.K θ * |T3|
            + Work.Spaces.K θ * |T4| + Work.Spaces.K θ * |T5| + Work.Spaces.K θ * |T6| := by
        ring
      have hmain : Work.Spaces.K θ * |T1 + -T2 + T3 + T4 + -T5 + -T6|
          ≤ (14 * CFs + 2 * CL * (1 + C₀) + 14 * CL * (CFs + 1) * (1 + C₀) + 8) * Q
            * Real.cos θ := by
        have h1 : Work.Spaces.K θ * |T1 + -T2 + T3 + T4 + -T5 + -T6|
            ≤ Work.Spaces.K θ * (|T1| + |T2| + |T3| + |T4| + |T5| + |T6|) :=
          mul_le_mul_of_nonneg_left hsumabs hK0
        linarith [h1, hXX, hT1, hT2, hT3, hT4, hT5, hT6]
      -- ## the final scalar comparison
      have hsc : 14 * CFs + 2 * CL * (1 + C₀) + 14 * CL * (CFs + 1) * (1 + C₀) + 8
          ≤ (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * (1 + C₀) * (1 + B) := by
        have hA0 : 0 ≤ 14 * CFs := by linarith
        have hB0' : 0 ≤ 14 * CL * (CFs + 1) := by positivity
        have hC0' : 0 ≤ 2 * CL := by linarith
        have h1 : 14 * CFs ≤ 14 * CFs * ((1 + C₀) * (1 + B)) := by
          have h := mul_le_mul_of_nonneg_left hA1 hA0
          linarith [h]
        have h1B1 : (1 : ℝ) ≤ 1 + B := by linarith
        have h2 : 1 + C₀ ≤ (1 + C₀) * (1 + B) := by
          have h := mul_le_mul_of_nonneg_left h1B1 h1C
          linarith [h]
        have h3 : 2 * CL * (1 + C₀) ≤ 2 * CL * ((1 + C₀) * (1 + B)) :=
          mul_le_mul_of_nonneg_left h2 hC0'
        have h4 : 14 * CL * (CFs + 1) * (1 + C₀)
            ≤ 14 * CL * (CFs + 1) * ((1 + C₀) * (1 + B)) := by
          have h := mul_le_mul_of_nonneg_left h2 hB0'
          linarith [h]
        have h5 : 8 ≤ 8 * ((1 + C₀) * (1 + B)) := by
          have h := mul_le_mul_of_nonneg_left hA1 (by norm_num : (0 : ℝ) ≤ 8)
          linarith [h]
        have h6 : (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * ((1 + C₀) * (1 + B))
            = 14 * CFs * ((1 + C₀) * (1 + B))
              + 14 * CL * (CFs + 1) * ((1 + C₀) * (1 + B))
              + 2 * CL * ((1 + C₀) * (1 + B)) + 8 * ((1 + C₀) * (1 + B)) := by ring
        have h7 : (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * (1 + C₀) * (1 + B)
            = (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * ((1 + C₀) * (1 + B)) := by ring
        linarith [h1, h3, h4, h5, h6, h7]
      have hfin : (14 * CFs + 2 * CL * (1 + C₀) + 14 * CL * (CFs + 1) * (1 + C₀) + 8) * Q
            * Real.cos θ
          ≤ (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * (1 + C₀) * (1 + B) * Q
            * Real.cos θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsc hQ0) hc0
      linarith [hmain, hfin]

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular weight `wTheta` is increasing in `α` -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `γ(α) = 1 + α/10` is increasing. -/
theorem gam_le_gam {α : ℝ} (hα : 1 ≤ α) : Work.Spaces.gam 1 ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam, Work.Spaces.gam]
  linarith

/-- **`wTheta` is increasing in `α`** on `Iθ`. -/
theorem wTheta_le_of_one_le {α : ℝ} (hα : 1 ≤ α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.wTheta 1 θ ≤ Work.Spaces.wTheta α θ := by
  have hgam := gam_le_gam hα
  rcases (sin_two_nonneg_Iθ' hθ).lt_or_eq with hs | hs
  · rw [Work.Spaces.wTheta, Work.Spaces.wTheta]
    refine Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one _) ?_
    linarith
  · have hs0 : Real.sin (2 * θ) = 0 := hs.symm
    have h1 : (-(Work.Spaces.gam 1 / 2)) ≠ 0 := by rw [Work.Spaces.gam]; norm_num
    have h2 : (-(Work.Spaces.gam α / 2)) ≠ 0 := by
      rw [Work.Spaces.gam]
      intro h
      linarith [hα]
    rw [Work.Spaces.wTheta, Work.Spaces.wTheta, hs0, Real.zero_rpow h1, Real.zero_rpow h2]

/-- `w ≥ 0`. -/
theorem w_nonneg' (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ## The pointwise comparison of the `ℋ^k`-integrands -/

/-- **The `ℋ^k`-integrand is increasing in `α`**: for `α ≥ 1` and `θ ∈ Iθ`,
`HkIntegrand 1 k g z θ ≤ HkIntegrand α k g z θ`. -/
theorem HkIntegrand_one_le {α : ℝ} (hα : 1 ≤ α) (k : ℕ) {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand 1 k g z θ ≤ Work.Spaces.HkIntegrand α k g z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  refine add_le_add (le_refl _) ?_
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  split_ifs with h
  · have hw0 : (0 : ℝ) ≤ Work.Spaces.w z := w_nonneg' z
    have hle : Work.Spaces.Wt 1 z θ ≤ Work.Spaces.Wt α z θ := by
      rw [Work.Spaces.Wt, Work.Spaces.Wt]
      exact mul_le_mul_of_nonneg_left (wTheta_le_of_one_le hα hθ) hw0
    have h1nn : 0 ≤ Work.Spaces.Wt 1 z θ := by
      rw [Work.Spaces.Wt]
      exact mul_nonneg hw0 (Real.rpow_nonneg (sin_two_nonneg_Iθ' hθ) _)
    have h2nn : 0 ≤ Work.Spaces.Wt α z θ := le_trans h1nn hle
    have habs : |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ|
        ≤ |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg h1nn, abs_of_nonneg h2nn]
      exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    have h2 : |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ| ^ 2
        ≤ |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ| ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    calc (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ) ^ 2
        = |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt 1 z θ| ^ 2 :=
          (sq_abs _).symm
      _ ≤ |Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ| ^ 2 := h2
      _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := sq_abs _
  · exact le_rfl

/-! ## The comparison of `HkMem` -/

/-- **`HkMem α k g → HkMem 1 k g` for `α ≥ 1`.** -/
theorem HkMem_one_of {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem 1 k g := by
  refine Work.Blocks.HkMem_of_majorant_aesm 1 k
    (M := fun z θ => Work.Spaces.HkIntegrand α k g z θ) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ => Work.Spaces.HkIntegrand 1 k g 0 θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        simp only [Work.Blocks.Half.HkIntegrand_zero_z]
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
        (hsm.continuousOn_HkIntegrand 1 k) hpos
  · have hjoint := Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand 1 k g p.1 p.2)
      (hsm.continuousOn_HkIntegrand 1 k)
    exact hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
  · intro z hz
    exact hmem.1 z hz
  · exact hmem.2
  · intro z hz θ hθ
    exact HkIntegrand_one_le hα k hθ

/-! ## The comparison of `HkSq` -/

/-- **`HkSq 1 k g ≤ HkSq α k g` for `α ≥ 1`.** -/
theorem HkSq_one_le {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) : Work.Spaces.HkSq 1 k g ≤ Work.Spaces.HkSq α k g := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hmem.2 ?_
  · filter_upwards with z
    exact integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg 1 k g z θ)
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg 1 k g z θ))
      (hmem.1 z hz) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => HkIntegrand_one_le hα k hθ)

/-! ## The comparison of `BdryTraces` -/

/-- **`BdryTraces α k g → BdryTraces 1 k g` for `α ≥ 1`.** -/
theorem bdryTraces_one_of {α : ℝ} (hα : 1 ≤ α) {k : ℕ} {g : ℝ → ℝ → ℝ}
    (htr : Work.FTS.Nonlin.BdryTraces α k g) : Work.FTS.Nonlin.BdryTraces 1 k g := by
  intro a b hab
  obtain ⟨h1, h2⟩ := htr a b hab
  refine ⟨h1, fun z hz => ?_⟩
  obtain ⟨h3, h4⟩ := h2 z hz
  have hgam : Work.Spaces.gam 1 ≤ Work.Spaces.gam α := gam_le_gam hα
  constructor
  · refine squeeze_zero' ?_ ?_ h3
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)
  · refine squeeze_zero' ?_ ?_ h4
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _)
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact Real.rpow_le_rpow_of_exponent_ge
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
        (Real.sin_le_one _) (by linarith)

/-! ## The class and norm comparisons -/

/-- **`ClassC α g → ClassC 1 g` for `α ≥ 1`.** -/
theorem classC_one_of {α : ℝ} (hα : 1 ≤ α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) : Work.FTS.ClassC.ClassC 1 g :=
  ⟨hg.norm, hg.reg, HkMem_one_of hα hg.reg hg.mem, HkMem_one_of hα hg.reg hg.mem8,
    HkMem_one_of hα hg.reg hg.mem10,
    bdryTraces_one_of hα hg.tr, bdryTraces_one_of hα hg.tr7, hg.fsm, hg.axis, hg.l12,
    thetaTraces_one_of hα hg.thTr⟩

/-- **`Xn6 1 g ≤ Xn6 α g` for `α ≥ 1`** on the class `ClassC α`. -/
theorem Xn6_one_le {α : ℝ} (hα : 1 ≤ α) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) :
    Work.FTS.StrongGlobal.Xn6 1 g ≤ Work.FTS.StrongGlobal.Xn6 α g := by
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  show Work.Spaces.HkNorm 1 6 g ≤ Work.Spaces.HkNorm α 6 g
  rw [Work.Spaces.HkNorm]
  exact Real.sqrt_le_sqrt (HkSq_one_le hα hmem6)

end Work.FTS_EllLimOK.ThetaJets
end
