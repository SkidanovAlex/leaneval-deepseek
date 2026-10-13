import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Lzero_orthogonal
import Submission.Work.EllipticEst.ModalSolution.angular_ibp_zero
import Submission.Work.EllipticEst.ModalSolution.box_of_compactSupport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

open MeasureTheory

namespace Work.FTS.H2.ModalSolR

/-!
# `Work.FTS.H2.ModalSolR.angularEigenIdentity`

The `m`-th angular Dirichlet eigenfunction of the `α = 0` Biot–Savart operator

`Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`

is `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`, with eigenvalue `lam m = 2m(2m+5)`
(`Work.FTS.PhiStar.Gegenbauer.eFam_Lzero`).  The pairing of `Lzero` against the weight `cos θ`
is self-adjoint on functions supported away from the endpoints, so for `φ` compactly supported
inside the open quadrant `Q0 = (0,∞) × (0,π/2)` and every `z`

`∫_{Iθ} eFam m θ · (Lzero φ)(z,θ) · cos θ = lam m · ∫_{Iθ} eFam m θ · φ(z,θ) · cos θ`.

The proof localises the `θ`-integral to an interval `[c,d] ⊂ (0,π/2)` outside which the slice
`θ ↦ φ z θ` vanishes (`Work.EllipticEst.ModalSolution.box_of_compactSupport`), applies the
integration by parts identity `Work.EllipticEst.ModalSolution.angular_ibp_zero` there, and
identifies `Lzero (eFam m)` with `lam m · eFam m` pointwise.
-/

/-! ## Auxiliary facts -/

/-- The `θ`-slice of a jointly smooth function is smooth. -/
private lemma contDiff_slice {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) (z : ℝ) (n : ℕ) :
    ContDiff ℝ n (fun θ : ℝ => φ z θ) := by
  have h : ContDiff ℝ n (Function.uncurry φ) := hφ n
  have hs : ContDiff ℝ n (fun θ : ℝ => (z, θ)) :=
    (contDiff_const (c := z)).prodMk contDiff_id
  have hcomp := h.comp hs
  have hfun : (Function.uncurry φ) ∘ (fun θ : ℝ => (z, θ)) = fun θ : ℝ => φ z θ := by
    funext θ
    exact Function.uncurry_apply_pair φ z θ
  rwa [hfun] at hcomp

/-- `eFam m = cos θ · C^{(3/2)}_{2m+1}(sin θ)` is `C²` (indeed smooth). -/
private lemma contDiff_eFam (m : ℕ) :
    ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  have hg : ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) :=
    (Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).of_le (by norm_num)
  exact Real.contDiff_cos.mul (hg.comp Real.contDiff_sin)

/-- An integral over `Iθ` of a function vanishing off `Set.Icc c d ⊆ Iθ` is the integral over
`Set.Icc c d`. -/
private lemma setIntegral_Iθ_eq_Icc {h : ℝ → ℝ} {c d : ℝ} (hc : 0 ≤ c)
    (hd : d ≤ Real.pi / 2) (h0 : ∀ θ : ℝ, θ ∉ Set.Icc c d → h θ = 0) :
    (∫ θ in Work.Spaces.Iθ, h θ) = ∫ θ in Set.Icc c d, h θ :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (fun _ hθ => ⟨hc.trans hθ.1, hθ.2.trans hd⟩) (fun θ hθ => h0 θ hθ.2)

/-- `Lzero`, written with the one-variable derivatives of the slice (restatement of
`Work.Elliptic.Lzero_eq_deriv` with the binder names used below). -/
private lemma Lzero_eq_expanded (φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero φ z θ
      = -deriv (deriv (fun θ' : ℝ => φ z θ')) θ
        + deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ - 6 * φ z θ := by
  first
  | exact Work.Elliptic.Lzero_eq_deriv φ z θ
  | simpa only [] using Work.Elliptic.Lzero_eq_deriv φ z θ

/-- The eigenfunction relation `Lzero (eFam m) = lam m · eFam m`, written with the binder names
used below. -/
private lemma eFam_Lzero_expanded (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) (z : ℝ) :
    -(deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
      + deriv (fun θ' : ℝ => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
      - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have h := Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hθ z
  rw [Work.Elliptic.Lzero_eq_deriv] at h
  first
  | exact h
  | simpa only [] using h

/-- If a slice vanishes identically off `Set.Icc c d` then so does `Lzero` of it: every term of
`Lzero` is a derivative (or the value) of a function which is locally `0` there. -/
private lemma Lzero_eq_zero_of_eq_zero_off_aux {φ : ℝ → ℝ → ℝ} {z c d θ : ℝ}
    (hv : ∀ θ' : ℝ, θ' ∉ Set.Icc c d → φ z θ' = 0) (hθ : θ ∉ Set.Icc c d) :
    Work.Elliptic.Lzero φ z θ = 0 := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, θ' ∉ Set.Icc c d :=
    (isClosed_Icc.isOpen_compl).mem_nhds hθ
  have h2 : deriv (deriv (fun θ' : ℝ => φ z θ')) θ = 0 := by
    have hpt : ∀ θ' : ℝ, θ' ∉ Set.Icc c d → deriv (fun θ'' : ℝ => φ z θ'') θ' = 0 := by
      intro θ' hθ'
      have hev : (fun θ'' : ℝ => φ z θ'') =ᶠ[𝓝 θ'] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds hθ'] with θ'' hθ''
        exact hv θ'' hθ''
      rw [hev.deriv_eq]
      exact deriv_const θ' 0
    have hev2 : (fun θ' : ℝ => deriv (fun θ'' : ℝ => φ z θ'') θ')
        =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with θ' hθ'
      exact hpt θ' hθ'
    rw [show deriv (deriv (fun θ' : ℝ => φ z θ')) θ
        = deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => φ z θ'') θ') θ from rfl,
      hev2.deriv_eq]
    exact deriv_const θ 0
  have h3 : deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ = 0 := by
    have hev3 : (fun θ' : ℝ => Real.tan θ' * φ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with θ' hθ'
      rw [hv θ' hθ', mul_zero]
    rw [hev3.deriv_eq]
    exact deriv_const θ 0
  rw [Work.Elliptic.Lzero_eq_deriv]
  change -deriv (deriv (fun θ' : ℝ => φ z θ')) θ
      + deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ - 6 * φ z θ = 0
  rw [h2, h3, hv θ hθ]
  ring

/-- `θ ↦ Lzero φ z θ` is continuous on any `[c,d]` with `0 < c ≤ d < π/2`: there it is the sum
of the continuous second derivative of the slice, the product `tan θ · (slice)'` (a product
rule expansion), and `-6` times the slice. -/
private lemma Lzero_continuousOn_aux {φ : ℝ → ℝ → ℝ} {z c d : ℝ}
    (h2 : ContDiff ℝ 2 (fun θ : ℝ => φ z θ)) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ContinuousOn (fun θ : ℝ => Work.Elliptic.Lzero φ z θ) (Set.Icc c d) := by
  have h1 : ContDiff ℝ 1 (fun θ : ℝ => φ z θ) := h2.of_le (by norm_num)
  have hdd : Continuous (deriv (deriv (fun θ : ℝ => φ z θ))) :=
    (ContDiff.deriv' (n := 1) h2).continuous_deriv_one
  have hd1 : Continuous (deriv (fun θ : ℝ => φ z θ)) := h1.continuous_deriv_one
  have hcos : ∀ θ ∈ Set.Icc c d, Real.cos θ ≠ 0 := by
    intro θ hθ
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hc, hθ.1]
    · linarith [hd, hθ.2]
  have hprod : ∀ θ ∈ Set.Icc c d, deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ
      = (1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * deriv (fun θ' : ℝ => φ z θ') θ := by
    intro θ hθ
    have hsd : HasDerivAt (fun θ' : ℝ => φ z θ') (deriv (fun θ' : ℝ => φ z θ') θ) θ :=
      ((h1.differentiable (by norm_num)).differentiableAt).hasDerivAt
    have hm := (Real.hasDerivAt_tan (hcos θ hθ)).mul hsd
    have hfun : (Real.tan * fun θ' : ℝ => φ z θ') = fun θ' : ℝ => Real.tan θ' * φ z θ' := by
      funext θ'
      first
      | rfl
      | simp only [Pi.mul_apply]
    rw [hfun] at hm
    exact hm.deriv
  have hcont : ContinuousOn (fun θ : ℝ =>
      -deriv (deriv (fun θ' : ℝ => φ z θ')) θ
        + ((1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * deriv (fun θ' : ℝ => φ z θ') θ)
        - 6 * φ z θ) (Set.Icc c d) := by
    have hA : ContinuousOn (fun θ : ℝ => deriv (deriv (fun θ' : ℝ => φ z θ')) θ)
        (Set.Icc c d) := hdd.continuousOn
    have hB : ContinuousOn (fun θ : ℝ => deriv (fun θ' : ℝ => φ z θ') θ) (Set.Icc c d) :=
      hd1.continuousOn
    have hC : ContinuousOn (fun θ : ℝ => φ z θ) (Set.Icc c d) := h2.continuous.continuousOn
    have hcos2 : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Icc c d) :=
      continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
        (fun θ hθ => pow_ne_zero 2 (hcos θ hθ))
    have htan : ContinuousOn Real.tan (Set.Icc c d) :=
      Real.continuousOn_tan.mono (fun θ hθ => hcos θ hθ)
    exact (((hA.neg).add ((hcos2.mul hC).add (htan.mul hB))).sub
      (continuousOn_const.mul hC))
  refine hcont.congr ?_
  intro θ hθ
  dsimp only
  rw [Lzero_eq_expanded, hprod θ hθ]

/-! ## The main computation -/

/-- The eigen-identity, localised to an interval `[c,d] ⊂ (0,π/2)` outside which the slice of
`φ` vanishes: since `Lzero` is self-adjoint for the weight `cos θ` on functions supported
inside `(0,π/2)` (and `Lzero (eFam m) = lam m · eFam m`), the pairing against `eFam m`
factors out `lam m`. -/
private lemma angularEigenIdentity_of_vanishes {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (m : ℕ) {z c d : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d < Real.pi / 2)
    (hv : ∀ θ : ℝ, θ ∉ Set.Icc c d → φ z θ = 0) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m
        * ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
          * Real.cos θ := by
  have hslice2 : ContDiff ℝ 2 (fun θ : ℝ => φ z θ) := contDiff_slice hφ z 2
  have hfam2 : ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) := contDiff_eFam m
  have hzero : ∀ θ ∈ Set.Icc c d, Real.cos θ ≠ 0 := by
    intro θ hθ
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hc, hθ.1]
    · linarith [hd, hθ.2]
  -- the integration by parts identity on `[c,d]`
  have hIBP := Work.EllipticEst.ModalSolution.angular_ibp_zero
    (f := Work.FTS.PhiStar.Gegenbauer.eFam m) (g := fun θ : ℝ => φ z θ)
    hc hcd hd hfam2.contDiffOn hslice2.contDiffOn (fun θ hθ => hv θ hθ)
  -- the two integrands agree on `[c,d]`
  have hEqOn : Set.EqOn
      (fun θ : ℝ =>
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ *
            (-(deriv (deriv (fun θ' : ℝ => φ z θ')) θ)
              + deriv (fun θ' : ℝ => Real.tan θ' * φ z θ') θ - 6 * φ z θ)
          - (-(deriv (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) θ)
              + deriv (fun θ' : ℝ => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ
              - 6 * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * φ z θ)
          * Real.cos θ)
      (fun θ : ℝ =>
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ
          - Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ)
      (Set.Icc c d) := by
    intro θ hθ
    dsimp only
    rw [Lzero_eq_expanded, eFam_Lzero_expanded m (hzero θ hθ) z]
    ring
  have hKey : (∫ θ in Set.Icc c d,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ
          - Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ) = 0 :=
    (setIntegral_congr_fun measurableSet_Icc hEqOn).symm.trans hIBP
  have hKey' : (∫ θ in Set.Icc c d,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ * Real.cos θ
          - (Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ)) = 0 := by
    rw [← hKey]
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    dsimp only
    ring
  -- integrability on `[c,d]`
  have hInt1 : IntegrableOn
      (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ
        * Real.cos θ) (Set.Icc c d) :=
    (((hfam2.continuous.continuousOn.mul
      (Lzero_continuousOn_aux hslice2 hc hd)).mul
        Real.continuous_cos.continuousOn)).integrableOn_Icc
  have hInt2 : IntegrableOn
      (fun θ : ℝ => (Work.FTS.PhiStar.Gegenbauer.lam m
        * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ) (Set.Icc c d) :=
    (((continuousOn_const.mul
      (hfam2.continuous.continuousOn.mul hslice2.continuous.continuousOn)).mul
        Real.continuous_cos.continuousOn)).integrableOn_Icc
  have hsplit : (∫ θ in Set.Icc c d,
        (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ * Real.cos θ
          - (Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ))
      = (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.Elliptic.Lzero φ z θ * Real.cos θ)
        - ∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ :=
    integral_sub hInt1 hInt2
  have hB : (∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
        * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m
        * (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
            * Real.cos θ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    dsimp only
    ring
  have hA : (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = ∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
        * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ := by
    have h1 : (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Work.Elliptic.Lzero φ z θ * Real.cos θ)
        - ∫ θ in Set.Icc c d, (Work.FTS.PhiStar.Gegenbauer.lam m
          * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ)) * Real.cos θ = 0 := by
      rw [← hsplit]
      first
      | exact hKey'
      | simpa only [] using hKey'
    exact sub_eq_zero.mp h1
  -- transfer both integrals from `Iθ` to `[c,d]`
  have htrans1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = ∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ :=
    setIntegral_Iθ_eq_Icc hc.le hd.le (fun θ hθ => by
      rw [Lzero_eq_zero_of_eq_zero_off_aux hv hθ]
      ring)
  have htrans2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
        * Real.cos θ)
      = ∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ
        * Real.cos θ :=
    setIntegral_Iθ_eq_Icc hc.le hd.le (fun θ hθ => by
      rw [hv θ hθ]
      ring)
  rw [htrans1, htrans2, hA, hB]

/-! ## The eigen-identity -/

theorem angularEigenIdentity {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m
        * ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ * φ z θ * Real.cos θ := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  refine angularEigenIdentity_of_vanishes hφ m hc hcd hd ?_
  intro θ hθ
  by_contra hne
  have hmem : (z, θ) ∈ Set.Ioo a b ×ˢ Set.Ioo c d := by
    by_contra hcon
    exact hne (hbox (z, θ) hcon)
  exact hθ ⟨le_of_lt hmem.2.1, le_of_lt hmem.2.2⟩

end Work.FTS.H2.ModalSolR
