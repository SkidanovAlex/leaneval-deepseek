import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta
import Submission.Work.FTS.EllipticEst.Auxiliary.Lzero_self_form_fts
import Submission.Work.FTS.EllipticEst.Auxiliary.zIBP1_fts
import Submission.Work.FTS.EllipticEst.Auxiliary.sliceCont_mul_fts
import Submission.Work.FTS.EllipticEst.Auxiliary.divCosSq_integrable_fts
import Submission.Work.FTS.EllipticEst.Auxiliary.Lzero_self_integrable_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

/-! # The truncated `θ`-energy identity at `C^∞` smoothness

`Work.FTS.EllipticEst.Aux.thetaEnergy1_dev` demands `ContDiff ℝ ⊤ W`, i.e. *analyticity*
of the cutoff; with `HasCompactSupport W` that forces `W = 0`, so the identity is only
available for the trivial cutoff.  Here the same identity is proved with the correct
smoothness hypothesis `ContDiff ℝ ∞ W` (`∞ = (⊤ : ℕ∞) : ℕ∞ω`), which is what the
cutoff families of the `E1`/`E2`/`ZpzEst` estimates satisfy. -/

namespace Work.FTS.EllipticEst.InfDev

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

/-! ## Small helpers -/

/-- The `θ`-slice of a `SmoothNbhd` function is smooth on the closed angular interval. -/
theorem contDiffOn_theta_slice_top {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ ⊤ (fun θ => f z θ) (Set.Icc 0 (π / 2)) := by
  have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Icc 0 (π / 2))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun θ hθ =>
    ⟨hz, by constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]⟩
  have hlin : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Icc 0 (π / 2)) := by fun_prop
  have hcomp := h.comp hlin hmap
  simpa [Function.comp_def, Function.uncurry] using hcomp

/-- The `θ`-slice of a `SmoothNbhd` function is `C²` on the closed angular interval. -/
theorem contDiffOn_theta_slice_two {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ 2 (fun θ => f z θ) (Set.Icc 0 (π / 2)) :=
  (contDiffOn_theta_slice_top h hz).of_le (by norm_num)

/-- A continuous function on `[0,R]` vanishing on `[R,∞)`, times a continuous function on
`[0,R]`, is integrable over `Iz = [0,∞)`. -/
theorem integrableOn_Iz_mul_of_continuousOn_Icc {ψ X : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hψc : ContinuousOn ψ (Set.Icc 0 R)) (hXc : ContinuousOn X (Set.Icc 0 R))
    (hψ0 : ∀ z, R ≤ z → ψ z = 0) :
    IntegrableOn (fun z => ψ z * X z) Work.Spaces.Iz := by
  have hcont : ContinuousOn (fun z => ψ z * X z) (Set.Icc 0 R) := hψc.mul hXc
  have h1 : IntegrableOn (fun z => ψ z * X z) (Set.Icc 0 R) :=
    hcont.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun z => ψ z * X z) (Set.Ioi R) :=
    (integrableOn_zero (s := Set.Ioi R)).congr_fun
      (fun z hz => by rw [Set.mem_Ioi] at hz; rw [hψ0 z hz.le, zero_mul])
      measurableSet_Ioi
  have h3 := h1.union h2
  rw [show Set.Icc 0 R ∪ Set.Ioi R = Work.Spaces.Iz from by
    ext z
    constructor
    · rintro (h | h)
      · exact h.1
      · exact le_of_lt (lt_of_le_of_lt hR h)
    · intro hz
      rcases le_or_gt z R with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr h] at h3
  exact h3

/-- `deriv` of the first parametric slice integral: `d/ds ∫_θ Ψ(s,θ)² = 2 ∫_θ ∂_zΨ(s,θ)Ψ(s,θ)`. -/
theorem hasDerivAt_sliceIntegral_sq (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ∀ z ∈ Set.Ioi (-1),
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, (Ψ s θ) ^ 2)
        (2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Ψ z θ) z := by
  intro z hz
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pzIter k Ψ p.1 p.2 * Ψ p.1 p.2)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := by
    intro k
    have h1 : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k Ψ) :=
      Work.Spaces.smoothNbhd_pzIter hsm k
    have hsub : Set.Ioi (-1 : ℝ) ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U :=
      Set.prod_mono subset_rfl fun θ hθ =>
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have ha : ContinuousOn (Function.uncurry (Work.Spaces.pzIter k Ψ))
        (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := (h1.mono hsub).continuousOn
    have hb : ContinuousOn (Function.uncurry Ψ) (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
      (hsm.mono hsub).continuousOn
    exact (ha.mul hb).congr fun p _ => rfl
  have hkey := Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
    (g := fun s θ => (Ψ s θ) ^ 2)
    (g' := fun s θ => 2 * (Work.Spaces.pz Ψ s θ * Ψ s θ))
    isOpen_Ioi hz ?_ ?_ ?_
  · rw [integral_const_mul] at hkey
    exact hkey
  · have hsub : Set.Ioi (-1 : ℝ) ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U :=
      Set.prod_mono subset_rfl fun θ hθ =>
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    exact ((hsm.mono hsub).continuousOn.pow 2).congr fun p _ => rfl
  · exact (continuousOn_const.mul (hcont 1)).congr fun p _ => rfl
  · intro θ hθ s hs
    have h := Work.Spaces.hardyZ_hasDerivAt_slice Ψ hsm hθ hs
    have hp := h.pow 2
    convert hp using 1
    ring

/-- `deriv` of the second parametric slice integral:
`d/ds ∫_θ ∂_zΨ(s,θ)Ψ(s,θ) = ∫_θ (∂_zzΨ(s,θ)Ψ(s,θ) + ∂_zΨ(s,θ)²)`. -/
theorem hasDerivAt_sliceIntegral_mixed (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ∀ z ∈ Set.Ioi (-1),
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ s θ * Ψ s θ)
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ * Ψ z θ
          + Work.Spaces.pz Ψ z θ * Work.Spaces.pz Ψ z θ)) z := by
  intro z hz
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pzIter k Ψ p.1 p.2)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) := by
    intro k
    have h1 : Work.Spaces.SmoothNbhd (Work.Spaces.pzIter k Ψ) :=
      Work.Spaces.smoothNbhd_pzIter hsm k
    have hsub : Set.Ioi (-1 : ℝ) ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.U :=
      Set.prod_mono subset_rfl fun θ hθ =>
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    exact (h1.mono hsub).continuousOn
  refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
    (g := fun s θ => Work.Spaces.pz Ψ s θ * Ψ s θ)
    (g' := fun s θ => Work.Spaces.pzIter 2 Ψ s θ * Ψ s θ
      + Work.Spaces.pz Ψ s θ * Work.Spaces.pz Ψ s θ)
    isOpen_Ioi hz ?_ ?_ ?_
  · exact ((hcont 1).mul (hcont 0)).congr fun p _ => rfl
  · exact (((hcont 2).mul (hcont 0)).add ((hcont 1).mul (hcont 1))).congr fun p _ => rfl
  · intro θ hθ s hs
    have h1 := Work.Spaces.hardyZ_hasDerivAt_slice Ψ hsm hθ hs
    have h2 := Work.Spaces.hardyZ_hasDerivAt_slice (Work.Spaces.pz Ψ)
      (Work.Spaces.SmoothNbhd.pz hsm) hθ hs
    have hd : deriv (fun s' => Work.Spaces.pz Ψ s' θ * Ψ s' θ) s
        = Work.Spaces.pzIter 2 Ψ s θ * Ψ s θ
          + Work.Spaces.pz Ψ s θ * Work.Spaces.pz Ψ s θ := by
      have hfun : (fun s' : ℝ => Work.Spaces.pz Ψ s' θ * Ψ s' θ)
          = (fun z => Work.Spaces.pz Ψ z θ) * (fun z => Ψ z θ) := rfl
      rw [hfun, deriv_mul h2.differentiableAt h1.differentiableAt, h2.deriv, h1.deriv]
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
    rw [← hd]
    exact (h2.differentiableAt.mul h1.differentiableAt).hasDerivAt


set_option maxHeartbeats 4000000 in
theorem devInf : ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (W : ℝ → ℝ),
    Work.Spaces.SmoothNbhd Ψ → (∀ z, Ψ z 0 = 0) → (∀ z, Ψ z (π / 2) = 0) →
    ContDiff ℝ ∞ W → HasCompactSupport W → (∀ z, 0 ≤ W z) → (∀ z, W z ≠ 0 → 0 < z) →
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.bslOp α Ψ z θ * Ψ z θ * (W z) ^ 2)
      = α ^ 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          z ^ 2 * (W z) ^ 2 * (Work.Spaces.pz Ψ z θ) ^ 2)
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            deriv (fun z => deriv (fun z => z ^ 2 * (W z) ^ 2) z) z * (Ψ z θ) ^ 2)
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            deriv (fun z => z * (W z) ^ 2) z * (Ψ z θ) ^ 2)
        + (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (W z) ^ 2 * (Work.Spaces.pth Ψ z θ) ^ 2)
        + (1 / 2) * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (W z) ^ 2 * (Ψ z θ / Real.cos θ) ^ 2)
        - 6 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (W z) ^ 2 * (Ψ z θ) ^ 2) := by
  intro α Ψ W hsm h0 h1 hW hWc hWnn hWpos
  -- ## Setup: `W` is supported in `[0,R]`
  have hW0 : W 0 = 0 := by
    by_contra hne
    exact absurd (hWpos 0 hne) (lt_irrefl 0)
  obtain ⟨b, hb⟩ := hWc.bddAbove
  set R : ℝ := max b 0 + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith [le_max_right b 0]
  have hR : 0 ≤ R := hRpos.le
  have hbR : b < R := by rw [hRdef]; linarith [le_max_left b 0]
  have hWzero : ∀ z, R ≤ z → W z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport W := subset_tsupport W hne
    have h1 : z ≤ b := hb hmem
    linarith
  have hUopen : IsOpen (tsupport W)ᶜ := (isClosed_tsupport W).isOpen_compl
  have hUmem : ∀ z, R ≤ z → z ∈ (tsupport W)ᶜ := by
    intro z hz hmem
    have h1 : z ≤ b := hb hmem
    have h2 : b < R := hbR
    linarith
  have hUzero : ∀ y ∈ (tsupport W)ᶜ, W y = 0 := by
    intro y hy
    by_contra hne
    exact hy (subset_tsupport W hne)
  have hWev : ∀ y ∈ (tsupport W)ᶜ, W =ᶠ[𝓝 y] 0 := fun y hy =>
    eventually_of_mem (hUopen.mem_nhds hy) hUzero
  -- derivative vanishing machinery for the two radial weights
  have hWd0 : ∀ y ∈ (tsupport W)ᶜ, deriv W y = 0 := by
    intro y hy
    rw [(hWev y hy).deriv_eq]
    simp
  have hg1ev : ∀ y ∈ (tsupport W)ᶜ, (fun x : ℝ => x ^ 2 * (W x) ^ 2) =ᶠ[𝓝 y] 0 := by
    intro y hy
    refine eventually_of_mem (hUopen.mem_nhds hy) fun x hx => ?_
    show x ^ 2 * (W x) ^ 2 = 0
    rw [hUzero x hx]
    ring
  have hg2ev : ∀ y ∈ (tsupport W)ᶜ, (fun x : ℝ => x * (W x) ^ 2) =ᶠ[𝓝 y] 0 := by
    intro y hy
    refine eventually_of_mem (hUopen.mem_nhds hy) fun x hx => ?_
    show x * (W x) ^ 2 = 0
    rw [hUzero x hx]
    ring
  have hg1d : ∀ y ∈ (tsupport W)ᶜ, deriv (fun x : ℝ => x ^ 2 * (W x) ^ 2) y = 0 := by
    intro y hy
    rw [(hg1ev y hy).deriv_eq]
    simp
  have hg2d : ∀ y ∈ (tsupport W)ᶜ, deriv (fun x : ℝ => x * (W x) ^ 2) y = 0 := by
    intro y hy
    rw [(hg2ev y hy).deriv_eq]
    simp
  have hg1dd : ∀ y ∈ (tsupport W)ᶜ,
      deriv (fun x : ℝ => deriv (fun x' : ℝ => x' ^ 2 * (W x') ^ 2) x) y = 0 := by
    intro y hy
    have hev : (fun x : ℝ => deriv (fun x' : ℝ => x' ^ 2 * (W x') ^ 2) x) =ᶠ[𝓝 y] 0 :=
      eventually_of_mem (hUopen.mem_nhds hy) fun x hx => hg1d x hx
    rw [hev.deriv_eq]
    simp
  -- boundary values at `0`
  have hg1_0 : (fun x : ℝ => x ^ 2 * (W x) ^ 2) 0 = 0 := by simp
  have hg2_0 : (fun x : ℝ => x * (W x) ^ 2) 0 = 0 := by simp
  have hg1d_0 : deriv (fun x : ℝ => x ^ 2 * (W x) ^ 2) 0 = 0 := by
    have hev : (fun x : ℝ => x ^ 2 * (W x) ^ 2) =ᶠ[𝓝 0] (fun x : ℝ => (x * W x) ^ 2) := by
      filter_upwards with x
      ring
    rw [hev.deriv_eq]
    have hWd : Differentiable ℝ W := hW.differentiable (by simp)
    have hd : DifferentiableAt ℝ (fun x : ℝ => x * W x) 0 := by fun_prop
    rw [deriv_fun_pow hd 2]
    simp
  -- ## The profiles of `z`
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 with hFdef
  set Q0 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Ψ z θ with hQ0def
  set Q1 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Ψ z θ with hQ1def
  set P : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z θ) ^ 2 with hPdef
  set Th2 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, deriv (fun θ' => Ψ z θ') θ ^ 2 with hTh2def
  set Kc : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 with hKcdef
  have hF' : ∀ z, F z = ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 := fun z => rfl
  have hQ0' : ∀ z, Q0 z = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Ψ z θ := fun z => rfl
  have hQ1' : ∀ z, Q1 z = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Ψ z θ := fun z => rfl
  have hP' : ∀ z, P z = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z θ) ^ 2 := fun z => rfl
  have hTh2' : ∀ z, Th2 z = ∫ θ in Work.Spaces.Iθ, deriv (fun θ' => Ψ z θ') θ ^ 2 := fun z => rfl
  have hKc' : ∀ z, Kc z = ∫ θ in Work.Spaces.Iθ, (Ψ z θ / Real.cos θ) ^ 2 := fun z => rfl
  have hFsq : ∀ z, (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) = F z := fun z => (hF' z).symm
  -- ## Step 1: the angular identity, pointwise in `z`
  have hA : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Ψ z θ)
        = -(α ^ 2 * z ^ 2) * Q1 z - (α * (5 + α) * z) * Q0 z
          + Th2 z + (1 / 2) * Kc z - 6 * F z := by
    intro z hz
    have hz' : z ∈ Set.Ioi (-1) := by
      rw [Work.Spaces.Iz, Set.mem_Ici] at hz
      rw [Set.mem_Ioi]
      linarith
    have hslice_int : ∀ (u : ℝ → ℝ → ℝ), Work.Spaces.SmoothNbhd u →
        IntegrableOn (fun θ => u z θ * Ψ z θ) Work.Spaces.Iθ := by
      intro u hu
      have hcu : ContinuousOn (fun θ => u z θ) Work.Spaces.Iθ :=
        (contDiffOn_theta_slice_top hu hz').continuousOn
      have hcΨ : ContinuousOn (fun θ => Ψ z θ) Work.Spaces.Iθ :=
        (contDiffOn_theta_slice_top hsm hz').continuousOn
      exact (hcu.mul hcΨ).integrableOn_compact Work.Coercivity.isCompact_Itheta
    have hI1 : IntegrableOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ * Ψ z θ) Work.Spaces.Iθ :=
      hslice_int _ (Work.Spaces.smoothNbhd_pzIter hsm 2)
    have hI2 : IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * Ψ z θ) Work.Spaces.Iθ :=
      hslice_int _ (Work.Spaces.SmoothNbhd.pz hsm)
    have hI3 : IntegrableOn (fun θ => Work.Elliptic.Lzero Ψ z θ * Ψ z θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.Auxiliary.Lzero_self_integrable_fts Ψ hsm h1 hz'
    have hsplit : (fun θ => Work.Elliptic.bslOp α Ψ z θ * Ψ z θ)
        = fun θ => (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * Ψ z θ)
            - (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Ψ z θ)
            + Work.Elliptic.Lzero Ψ z θ * Ψ z θ := by
      funext θ
      rw [Work.Elliptic.bslOp_apply]
      ring
    have hIA : IntegrableOn
        (fun θ => (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * Ψ z θ)) Work.Spaces.Iθ :=
      hI1.const_mul _
    have hIB : IntegrableOn
        (fun θ => (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Ψ z θ)) Work.Spaces.Iθ :=
      hI2.const_mul _
    have hIAB : IntegrableOn
        (fun θ => (-(α ^ 2 * z ^ 2)) * (Work.Spaces.pzIter 2 Ψ z θ * Ψ z θ)
          - (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Ψ z θ)) Work.Spaces.Iθ := hIA.sub hIB
    rw [hsplit]
    rw [integral_add hIAB hI3, integral_sub hIA hIB, integral_const_mul, integral_const_mul]
    rw [Work.FTS.EllipticEst.Auxiliary.Lzero_self_form_fts Ψ z (contDiffOn_theta_slice_two hsm hz') (h0 z) (h1 z),
      ← hTh2' z, ← hKc' z, ← hF' z, ← hQ1' z, ← hQ0' z]
    ring
  -- ## Step 2: pull the `θ`-integral out and insert the angular profile
  have hLHS : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.bslOp α Ψ z θ * Ψ z θ * (W z) ^ 2)
      = ∫ z in Work.Spaces.Iz, (-(α ^ 2 * z ^ 2) * Q1 z - (α * (5 + α) * z) * Q0 z
          + Th2 z + (1 / 2) * Kc z - 6 * F z) * (W z) ^ 2 := by
    simp_rw [MeasureTheory.integral_mul_const]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z hz => ?_
    rw [hA z hz]
  -- ## Step 3: the radial weights `g1`, `g2`, the profiles `D1`, `D2`, and their calculus
  have hWd : Differentiable ℝ W := hW.differentiable (by simp)
  have hW2sm : ContDiff ℝ ∞ (fun z : ℝ => (W z) ^ 2) := by fun_prop
  have hW2cont : ContinuousOn (fun z : ℝ => (W z) ^ 2) (Set.Icc 0 R) :=
    hW2sm.continuous.continuousOn
  have hW2zero : ∀ z, R ≤ z → (W z) ^ 2 = 0 := fun z hz => by rw [hWzero z hz]; ring
  set g1 : ℝ → ℝ := fun z => z ^ 2 * (W z) ^ 2 with hg1def
  set g2 : ℝ → ℝ := fun z => z * (W z) ^ 2 with hg2def
  have hg1' : ∀ z, g1 z = z ^ 2 * (W z) ^ 2 := fun z => rfl
  have hg2' : ∀ z, g2 z = z * (W z) ^ 2 := fun z => rfl
  have hg1sm : ContDiff ℝ ∞ g1 := by rw [hg1def]; fun_prop
  have hg2sm : ContDiff ℝ ∞ g2 := by rw [hg2def]; fun_prop
  have hg1deriv : ∀ x ∈ Set.Ioi (-1), HasDerivAt g1 (deriv g1 x) x := fun x _ =>
    (hg1sm.differentiable (by simp)).differentiableAt.hasDerivAt
  have hg2deriv : ∀ x ∈ Set.Ioi (-1), HasDerivAt g2 (deriv g2 x) x := fun x _ =>
    (hg2sm.differentiable (by simp)).differentiableAt.hasDerivAt
  have hg1cont : ContinuousOn g1 (Set.Icc 0 R) := hg1sm.continuous.continuousOn
  have hg2cont : ContinuousOn g2 (Set.Icc 0 R) := hg2sm.continuous.continuousOn
  have hG1sm1 : ContDiff ℝ 1 (deriv g1) := by
    have h := ContDiff.iterate_deriv' 1 1 (hg1sm.of_le (by norm_num))
    simpa [Function.iterate_one] using h
  have hG1deriv : ∀ x ∈ Set.Ioi (-1), HasDerivAt (deriv g1) (deriv (deriv g1) x) x :=
    fun x _ => (hG1sm1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hG1cont : ContinuousOn (deriv g1) (Set.Icc 0 R) :=
    (hg1sm.continuous_deriv (by norm_num)).continuousOn
  have hG2cont : ContinuousOn (deriv g2) (Set.Icc 0 R) :=
    (hg2sm.continuous_deriv (by norm_num)).continuousOn
  have hG1ddcont : ContinuousOn (fun z => deriv (deriv g1) z) (Set.Icc 0 R) := by
    have h := (ContDiff.iterate_deriv' 2 2 (hg1sm.of_le (by norm_num))).continuous
    have h2 : (deriv^[2]) g1 = fun z => deriv (deriv g1) z := by
      funext z; simp [Function.iterate_succ_apply]
    have hcont : Continuous (fun z => deriv (deriv g1) z) := by rwa [h2] at h
    exact hcont.continuousOn
  have hg1zero : ∀ z, R ≤ z → g1 z = 0 := fun z hz => by rw [hg1' z, hWzero z hz]; ring
  have hg2zero : ∀ z, R ≤ z → g2 z = 0 := fun z hz => by rw [hg2' z, hWzero z hz]; ring
  have hG1zero : ∀ z, R ≤ z → deriv g1 z = 0 := fun z hz => hg1d z (hUmem z hz)
  have hG2zero : ∀ z, R ≤ z → deriv g2 z = 0 := fun z hz => hg2d z (hUmem z hz)
  have hG1ddzero : ∀ z, R ≤ z → deriv (deriv g1) z = 0 := fun z hz => hg1dd z (hUmem z hz)
  have hg1_0 : g1 0 = 0 := by simp [hg1']
  have hg2_0 : g2 0 = 0 := by simp [hg2']
  have hG1_0 : deriv g1 0 = 0 := by
    change deriv ((fun x : ℝ => x ^ 2) * (fun x : ℝ => (W x) ^ 2)) 0 = 0
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    simp
  have hG2_0 : deriv g2 0 = 0 := by
    change deriv ((fun x : ℝ => x) * (fun x : ℝ => (W x) ^ 2)) 0 = 0
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    simp [hW0]
  set D1 : ℝ → ℝ := fun z => 2 * Q0 z with hD1def
  set D2 : ℝ → ℝ := fun z => 2 * (Q1 z + P z) with hD2def
  have hD1' : ∀ z, D1 z = 2 * Q0 z := fun z => rfl
  have hD2' : ∀ z, D2 z = 2 * (Q1 z + P z) := fun z => rfl
  have hQ1decomp : ∀ z, Q1 z = D2 z / 2 - P z := by
    intro z; rw [hD2' z]; ring_nf
  -- ## θ-integrability of the two pieces needed for the mixed derivative
  have hslice1 : ∀ x ∈ Set.Ioi (-1),
      IntegrableOn (fun θ => Work.Spaces.pzIter 2 Ψ x θ * Ψ x θ) Work.Spaces.Iθ := by
    intro x hx
    have hcu : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ x θ) Work.Spaces.Iθ :=
      (contDiffOn_theta_slice_top (Work.Spaces.smoothNbhd_pzIter hsm 2) hx).continuousOn
    have hcΨ : ContinuousOn (fun θ => Ψ x θ) Work.Spaces.Iθ :=
      (contDiffOn_theta_slice_top hsm hx).continuousOn
    exact (hcu.mul hcΨ).integrableOn_compact Work.Coercivity.isCompact_Itheta
  have hsliceP : ∀ x ∈ Set.Ioi (-1),
      IntegrableOn (fun θ => Work.Spaces.pz Ψ x θ * Work.Spaces.pz Ψ x θ) Work.Spaces.Iθ := by
    intro x hx
    have hcu : ContinuousOn (fun θ => Work.Spaces.pz Ψ x θ) Work.Spaces.Iθ :=
      (contDiffOn_theta_slice_top (Work.Spaces.SmoothNbhd.pz hsm) hx).continuousOn
    exact (hcu.mul hcu).integrableOn_compact Work.Coercivity.isCompact_Itheta
  -- ## the derivative facts for the profiles
  have hF_deriv : ∀ x ∈ Set.Ioi (-1), HasDerivAt F (D1 x) x := by
    intro x hx
    have hchild := hasDerivAt_sliceIntegral_sq Ψ hsm x hx
    have hfun : F = fun s => ∫ θ in Work.Spaces.Iθ, (Ψ s θ) ^ 2 := rfl
    have hval : D1 x = 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ x θ * Ψ x θ := by
      rw [hD1' x, hQ0' x]
    rw [hfun, hval]
    exact hchild
  have hD1_deriv : ∀ x ∈ Set.Ioi (-1), HasDerivAt D1 (D2 x) x := by
    intro x hx
    have hchild := hasDerivAt_sliceIntegral_mixed Ψ hsm x hx
    have hPx : (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ x θ * Work.Spaces.pz Ψ x θ) = P x := by
      rw [hP' x]
      exact (MeasureTheory.setIntegral_congr_fun Work.Coercivity.measurableSet_Itheta
        (fun θ _ => by ring)).symm
    have hval : 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ x θ * Ψ x θ
        + Work.Spaces.pz Ψ x θ * Work.Spaces.pz Ψ x θ)) = D2 x := by
      rw [integral_add (hslice1 x hx) (hsliceP x hx), hD2' x, hQ1' x, hPx]
    have hfun : D1 = fun s => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ s θ * Ψ s θ) := by
      funext s; rw [hD1' s, hQ0' s]
    rw [hfun, ← hval]
    exact hchild.const_mul 2
  -- ## Step 4: the five summands
  have hsum : (fun z => (-(α ^ 2 * z ^ 2) * Q1 z - (α * (5 + α) * z) * Q0 z
        + Th2 z + (1 / 2) * Kc z - 6 * F z) * (W z) ^ 2)
      = fun z => (-(α ^ 2)) * (g1 z * Q1 z) + (-(α * (5 + α))) * (g2 z * Q0 z)
          + (W z) ^ 2 * Th2 z + (1 / 2) * ((W z) ^ 2 * Kc z)
          + (-6) * ((W z) ^ 2 * F z) := by
    funext z
    simp only [hg1def, hg2def]
    ring
  -- ## continuity of the profiles
  have hmono : ∀ {X : ℝ → ℝ}, ContinuousOn X (Set.Ioi (-1)) → ContinuousOn X (Set.Icc 0 R) :=
    fun hX => hX.mono fun z hz => by
      rw [Set.mem_Icc] at hz
      rw [Set.mem_Ioi]
      linarith [hz.1]
  have hXQ1 : ContinuousOn Q1 (Set.Ioi (-1)) :=
    (Work.FTS.EllipticEst.Auxiliary.sliceCont_mul_fts (Work.Spaces.pzIter 2 Ψ) Ψ
      (Work.Spaces.smoothNbhd_pzIter hsm 2) hsm).congr fun z _ => (hQ1' z).symm
  have hXQ0 : ContinuousOn Q0 (Set.Ioi (-1)) :=
    (Work.FTS.EllipticEst.Auxiliary.sliceCont_mul_fts (Work.Spaces.pz Ψ) Ψ
      (Work.Spaces.SmoothNbhd.pz hsm) hsm).congr fun z _ => (hQ0' z).symm
  have hXP : ContinuousOn P (Set.Ioi (-1)) :=
    (Work.FTS.EllipticEst.Auxiliary.sliceCont_mul_fts (Work.Spaces.pz Ψ) (Work.Spaces.pz Ψ)
      (Work.Spaces.SmoothNbhd.pz hsm) (Work.Spaces.SmoothNbhd.pz hsm)).congr fun z _ => by
        rw [hP' z]
        exact (MeasureTheory.setIntegral_congr_fun Work.Coercivity.measurableSet_Itheta
          (fun θ _ => by ring)).symm
  have hXTh2 : ContinuousOn Th2 (Set.Ioi (-1)) :=
    (Work.FTS.EllipticEst.Auxiliary.sliceCont_mul_fts (Work.Spaces.pth Ψ) (Work.Spaces.pth Ψ)
      (Work.Spaces.SmoothNbhd.pth hsm) (Work.Spaces.SmoothNbhd.pth hsm)).congr fun z _ => by
        rw [hTh2' z]
        exact (MeasureTheory.setIntegral_congr_fun Work.Coercivity.measurableSet_Itheta
          (fun θ _ => by simp only [Work.Spaces.pth]; ring)).symm
  have hXF : ContinuousOn F (Set.Ioi (-1)) :=
    (Work.FTS.EllipticEst.Auxiliary.sliceCont_mul_fts Ψ Ψ hsm hsm).congr fun z _ => by
        rw [hF' z]
        exact (MeasureTheory.setIntegral_congr_fun Work.Coercivity.measurableSet_Itheta
          (fun θ _ => by ring)).symm
  have hXD1 : ContinuousOn D1 (Set.Ioi (-1)) :=
    (hXQ0.const_mul 2).congr fun z _ => (hD1' z).symm
  have hXD2 : ContinuousOn D2 (Set.Ioi (-1)) :=
    ((hXQ1.add hXP).const_mul 2).congr fun z _ => (hD2' z).symm
  have hD1cont : ContinuousOn D1 (Set.Icc 0 R) := hmono hXD1
  have hD2cont : ContinuousOn D2 (Set.Icc 0 R) := hmono hXD2
  have hFcont : ContinuousOn F (Set.Icc 0 R) := hmono hXF
  -- ## integrability of the split summands
  have hInt : ∀ {ψ X : ℝ → ℝ}, ContinuousOn ψ (Set.Icc 0 R) → ContinuousOn X (Set.Icc 0 R) →
      (∀ z, R ≤ z → ψ z = 0) → IntegrableOn (fun z => ψ z * X z) Work.Spaces.Iz :=
    fun h1 h2 h3 => integrableOn_Iz_mul_of_continuousOn_Icc hR h1 h2 h3
  have hIz1 : IntegrableOn (fun z => (-(α ^ 2)) * (g1 z * Q1 z)) Work.Spaces.Iz :=
    (hInt hg1cont (hmono hXQ1) hg1zero).const_mul _
  have hIz2 : IntegrableOn (fun z => (-(α * (5 + α))) * (g2 z * Q0 z)) Work.Spaces.Iz :=
    (hInt hg2cont (hmono hXQ0) hg2zero).const_mul _
  have hIz3 : IntegrableOn (fun z => (W z) ^ 2 * Th2 z) Work.Spaces.Iz :=
    hInt hW2cont (hmono hXTh2) hW2zero
  have hKcPI : IntegrableOn (fun z => (W z) ^ 2 * Kc z) Work.Spaces.Iz :=
    Work.FTS.EllipticEst.Auxiliary.divCosSq_integrable_fts Ψ hsm h1 (fun z => (W z) ^ 2) hR hW2cont hW2zero
  have hIz4 : IntegrableOn (fun z => (1 / 2) * ((W z) ^ 2 * Kc z)) Work.Spaces.Iz :=
    hKcPI.const_mul (1 / 2)
  have hFPI : IntegrableOn (fun z => (W z) ^ 2 * F z) Work.Spaces.Iz :=
    hInt hW2cont hFcont hW2zero
  have hIz5 : IntegrableOn (fun z => (-6) * ((W z) ^ 2 * F z)) Work.Spaces.Iz :=
    hFPI.const_mul (-6)
  have hI12 : IntegrableOn (fun z => (-(α ^ 2)) * (g1 z * Q1 z)
      + (-(α * (5 + α))) * (g2 z * Q0 z)) Work.Spaces.Iz := hIz1.add hIz2
  have hI123 : IntegrableOn (fun z => (-(α ^ 2)) * (g1 z * Q1 z)
      + (-(α * (5 + α))) * (g2 z * Q0 z) + (W z) ^ 2 * Th2 z) Work.Spaces.Iz := hI12.add hIz3
  have hI1234 : IntegrableOn (fun z => (-(α ^ 2)) * (g1 z * Q1 z)
      + (-(α * (5 + α))) * (g2 z * Q0 z) + (W z) ^ 2 * Th2 z
      + (1 / 2) * ((W z) ^ 2 * Kc z)) Work.Spaces.Iz := hI123.add hIz4
  have hQ1PI : IntegrableOn (fun z => g1 z * Q1 z) Work.Spaces.Iz :=
    hInt hg1cont (hmono hXQ1) hg1zero
  have hPPI : IntegrableOn (fun z => g1 z * P z) Work.Spaces.Iz :=
    hInt hg1cont (hmono hXP) hg1zero
  have hD2PI : IntegrableOn (fun z => g1 z * D2 z) Work.Spaces.Iz :=
    hInt hg1cont (hmono hXD2) hg1zero
  have hG1DPI : IntegrableOn (fun z => deriv g1 z * D1 z) Work.Spaces.Iz :=
    hInt hG1cont hD1cont hG1zero
  have hG1ddF : IntegrableOn (fun z => deriv (deriv g1) z * F z) Work.Spaces.Iz :=
    hInt hG1ddcont hFcont hG1ddzero
  have hXD2h : ContinuousOn (fun z => D2 z / 2) (Set.Ioi (-1)) :=
    (hXD2.const_mul (1 / 2)).congr fun z _ => by ring
  have hPsub : IntegrableOn (fun z => g1 z * (D2 z / 2)) Work.Spaces.Iz :=
    hInt hg1cont (hmono hXD2h) hg1zero
  -- ## the two integration-by-parts identities
  have hIBP1 : ∫ z in Work.Spaces.Iz, g1 z * D2 z
      = ∫ z in Work.Spaces.Iz, deriv (deriv g1) z * F z := by
    have hA1 := Work.FTS.EllipticEst.Auxiliary.zIBP1_fts D1 D2 g1 (deriv g1) hR
      hD1_deriv hg1deriv hD1cont hD2cont hg1cont hG1cont hg1zero
      (fun x hx => hG1zero x hx.le) hg1_0
    have hB1 := Work.FTS.EllipticEst.Auxiliary.zIBP1_fts F D1 (deriv g1) (deriv (deriv g1))
      hR hF_deriv hG1deriv hFcont hD1cont hG1cont hG1ddcont hG1zero
      (fun x hx => hG1ddzero x hx.le) hG1_0
    rw [hA1, hB1]
    ring
  have hIBP2 : ∫ z in Work.Spaces.Iz, g2 z * D1 z
      = - ∫ z in Work.Spaces.Iz, deriv g2 z * F z :=
    Work.FTS.EllipticEst.Auxiliary.zIBP1_fts F D1 g2 (deriv g2) hR hF_deriv hg2deriv
      hFcont hD1cont hg2cont hG2cont hg2zero (fun x hx => hG2zero x hx.le) hg2_0
  -- ## Step 5: the pieces
  have hp1 : ∫ z in Work.Spaces.Iz, (-(α ^ 2)) * (g1 z * Q1 z)
      = -(α ^ 2) * ∫ z in Work.Spaces.Iz, g1 z * Q1 z := integral_const_mul _ _
  have hp1b : ∫ z in Work.Spaces.Iz, g1 z * Q1 z
      = (1 / 2) * (∫ z in Work.Spaces.Iz, g1 z * D2 z)
        - ∫ z in Work.Spaces.Iz, g1 z * P z := by
    have h1 : ∫ z in Work.Spaces.Iz, g1 z * Q1 z
        = ∫ z in Work.Spaces.Iz, g1 z * (D2 z / 2) - g1 z * P z :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => by
        rw [hQ1decomp z]; ring
    have h2 : ∫ z in Work.Spaces.Iz, g1 z * (D2 z / 2)
        = (1 / 2) * ∫ z in Work.Spaces.Iz, g1 z * D2 z := by
      rw [← integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => by ring
    rw [h1, integral_sub hPsub hPPI, h2]
  have hp1c : ∫ z in Work.Spaces.Iz, g1 z * D2 z
      = ∫ z in Work.Spaces.Iz, deriv (deriv g1) z * F z := hIBP1
  have hp2 : ∫ z in Work.Spaces.Iz, (-(α * (5 + α))) * (g2 z * Q0 z)
      = -(α * (5 + α)) * ∫ z in Work.Spaces.Iz, g2 z * Q0 z := integral_const_mul _ _
  have hp2b : ∫ z in Work.Spaces.Iz, g2 z * Q0 z
      = (1 / 2) * (∫ z in Work.Spaces.Iz, g2 z * D1 z) := by
    rw [← integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => by
      rw [hD1' z]; ring
  have hp2c : ∫ z in Work.Spaces.Iz, g2 z * D1 z
      = - ∫ z in Work.Spaces.Iz, deriv g2 z * F z := hIBP2
  have hp4 : ∫ z in Work.Spaces.Iz, (1 / 2) * ((W z) ^ 2 * Kc z)
      = (1 / 2) * ∫ z in Work.Spaces.Iz, (W z) ^ 2 * Kc z := integral_const_mul _ _
  have hp5 : ∫ z in Work.Spaces.Iz, (-6) * ((W z) ^ 2 * F z)
      = -6 * ∫ z in Work.Spaces.Iz, (W z) ^ 2 * F z := integral_const_mul _ _
  -- ## Step 6: the radial identity
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.bslOp α Ψ z θ * Ψ z θ * (W z) ^ 2)
      = α ^ 2 * (∫ z in Work.Spaces.Iz, g1 z * P z)
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, deriv (deriv g1) z * F z)
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, deriv g2 z * F z)
        + (∫ z in Work.Spaces.Iz, (W z) ^ 2 * Th2 z)
        + (1 / 2) * (∫ z in Work.Spaces.Iz, (W z) ^ 2 * Kc z)
        - 6 * (∫ z in Work.Spaces.Iz, (W z) ^ 2 * F z) := by
    rw [hLHS, hsum, integral_add hI1234 hIz5, integral_add hI123 hIz4,
      integral_add hI12 hIz3, integral_add hIz1 hIz2, hp1, hp1b, hp1c, hp2, hp2b, hp2c,
      hp4, hp5]
    ring
  -- ## Step 7: identify the six target integrals with the `A`-forms
  have t1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        z ^ 2 * (W z) ^ 2 * (Work.Spaces.pz Ψ z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, g1 z * P z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul, ← hP' z, hg1' z]
  have t2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        deriv (fun z => deriv (fun z => z ^ 2 * (W z) ^ 2) z) z * (Ψ z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, deriv (deriv g1) z * F z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul, ← hF' z]
  have t3 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        deriv (fun z => z * (W z) ^ 2) z * (Ψ z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, deriv g2 z * F z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul, ← hF' z]
  have hpth : ∀ z, (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth Ψ z θ) ^ 2) = Th2 z := fun z =>
    (MeasureTheory.setIntegral_congr_fun Work.Coercivity.measurableSet_Itheta
      (fun θ _ => by simp only [Work.Spaces.pth])).trans (hTh2' z).symm
  have t4 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (W z) ^ 2 * (Work.Spaces.pth Ψ z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, (W z) ^ 2 * Th2 z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul, hpth z]
  have t5 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (W z) ^ 2 * (Ψ z θ / Real.cos θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, (W z) ^ 2 * Kc z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul, ← hKc' z]
  have t6 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (W z) ^ 2 * (Ψ z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, (W z) ^ 2 * F z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [MeasureTheory.integral_const_mul, ← hFsq z]
  rw [t1, t2, t3, t4, t5, t6]
  exact hmain

end

end Work.FTS.EllipticEst.InfDev
