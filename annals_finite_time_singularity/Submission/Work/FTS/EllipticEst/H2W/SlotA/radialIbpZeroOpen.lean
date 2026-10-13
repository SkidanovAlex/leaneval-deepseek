import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.H2W.SlotA.radialDerivPointwiseOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial integration-by-parts identity on the open half-strip

This is the *weak-class* version of `Work.FTS.EllipticEst.H2W.radial_ibp_zero`: the smoothness
hypothesis is `C³` on the **open** half-strip `qd = (0,∞) × (0,π/2)` (only the open quadrant, as
in the almost-everywhere class `H2W.Ae.AeData`) instead of on a neighbourhood of the closed
quadrant, and the conclusion is stated for `θ ∈ (0,π/2)` — which is an almost-everywhere subset
of the full angular interval `Iθ = [0,π/2]`.

For a `C³` function `Φ` on the open half-strip whose `z`-support is contained in a compact
interval `[a,b] ⊂ (0,∞)` (for **every** angle `θ`, hypothesis `hsupp`), and for every
`θ ∈ (0,π/2)`, the integral over `z > 0` of

  `∂_z [ z² · ∂_z Φ(z,θ) · w(z)² · ∂_θ²Φ(z,θ) ] · sin(2θ)^{-η}`

vanishes (with `w(z) = (1+z)²/z²`, `η > 0` arbitrary).

The proof is the one of the sibling file, with the two open sets replaced: the pointwise
identifications `∂_zΦ = ribpPz`, `∂_θ²Φ = ribpPth2` hold on `qd`, which is all the support and
smoothness arguments use.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false

/-! ## The partial derivatives of `Φ` as Fréchet-derivative directions -/

/-- The first `z`-partial derivative `∂_zΦ` on `qd`, as a directional Fréchet derivative. -/
abbrev ribpPz (Φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => (fderiv ℝ (Function.uncurry Φ) y) (1, 0)

/-- The first `θ`-partial derivative `∂_θΦ` on `qd`. -/
abbrev ribpPth (Φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => (fderiv ℝ (Function.uncurry Φ) y) (0, 1)

/-- The second `θ`-partial derivative `∂_θ²Φ` on `qd`. -/
abbrev ribpPth2 (Φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => (fderiv ℝ (ribpPth Φ) y) (0, 1)

/-- The function `G_θ(z) = z² ∂_zΦ(z,θ) w(z)² ∂_θ²Φ(z,θ)` whose `z`-derivative is the
integrand of `radial_ibp_zero_open`. -/
abbrev ribpG (Φ : ℝ → ℝ → ℝ) (θ : ℝ) : ℝ → ℝ :=
  fun z => (z ^ 2 * ribpPz Φ (z, θ) * (Work.Spaces.w z) ^ 2) * ribpPth2 Φ (z, θ)

/-! ## Elementary helpers -/

/-- The `z`-slices of a function that is `C^k` on a product of open sets. -/
lemma ribp_contDiffOn_slice {k : WithTop ℕ∞} {H : ℝ × ℝ → ℝ} {s t W : Set ℝ} {θ : ℝ}
    (hH : ContDiffOn ℝ k H (s ×ˢ t)) (hW : ∀ z ∈ W, (z, θ) ∈ s ×ˢ t) :
    ContDiffOn ℝ k (fun z => H (z, θ)) W := by
  have hf : ContDiffOn ℝ k (fun z : ℝ => (z, θ)) W :=
    ContDiffOn.prodMk contDiffOn_id (contDiffOn_const (c := θ))
  have h := hH.comp hf hW
  simpa [Function.comp_def] using h

/-! ## The smoothness of `pz Φ`, `pth Φ` and `pth² Φ` from the joint `C³` hypothesis -/

lemma ribp_contDiffOn_Pz (Φ : ℝ → ℝ → ℝ)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd) :
    ContDiffOn ℝ 2 (ribpPz Φ) qd :=
  (hsm.fderiv_of_isOpen isOpen_qd (by norm_num)).clm_apply
    (contDiffOn_const (c := ((1, 0) : ℝ × ℝ)))

lemma ribp_contDiffOn_Pth (Φ : ℝ → ℝ → ℝ)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd) :
    ContDiffOn ℝ 2 (ribpPth Φ) qd :=
  (hsm.fderiv_of_isOpen isOpen_qd (by norm_num)).clm_apply
    (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))

lemma ribp_contDiffOn_Pth2 (Φ : ℝ → ℝ → ℝ)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd) :
    ContDiffOn ℝ 1 (ribpPth2 Φ) qd :=
  ((ribp_contDiffOn_Pth Φ hsm).fderiv_of_isOpen isOpen_qd (by norm_num)).clm_apply
    (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))

/-! ## The pointwise identifications of the iterated partial derivatives -/

lemma ribp_pz_eq_Pz (Φ : ℝ → ℝ → ℝ)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd) {z θ : ℝ}
    (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz Φ z θ = ribpPz Φ (z, θ) := by
  have hzθ : (z, θ) ∈ qd := ⟨hz, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry Φ) (z, θ) :=
    (hsm.differentiableOn (by norm_num)).differentiableAt (isOpen_qd.mem_nhds hzθ)
  have h := Work.Spaces.deriv_slice_fst (Function.uncurry Φ) z θ hd
  simpa only [Work.Spaces.pz, Function.uncurry] using h

lemma ribp_pthIter_two_eq_Pth2 (Φ : ℝ → ℝ → ℝ)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd) {z θ : ℝ}
    (hz : z ∈ Set.Ioi 0) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 Φ z θ = ribpPth2 Φ (z, θ) := by
  have hzθ : (z, θ) ∈ qd := ⟨hz, hθ⟩
  have hdiffPth : DifferentiableAt ℝ (ribpPth Φ) (z, θ) :=
    ((ribp_contDiffOn_Pth Φ hsm).differentiableOn (by norm_num)).differentiableAt
      (isOpen_qd.mem_nhds hzθ)
  have hev : (fun θ' => Work.Spaces.pth Φ z θ') =ᶠ[nhds θ] (fun θ' => ribpPth Φ (z, θ')) := by
    have hnb : ∀ᶠ θ' in nhds θ, (z, θ') ∈ qd :=
      (Continuous.prodMk_right z).continuousAt.eventually (isOpen_qd.mem_nhds hzθ)
    filter_upwards [hnb] with θ' hθ'
    have hd : DifferentiableAt ℝ (Function.uncurry Φ) (z, θ') :=
      (hsm.differentiableOn (by norm_num)).differentiableAt (isOpen_qd.mem_nhds hθ')
    have h := Work.Spaces.deriv_slice_snd (Function.uncurry Φ) z θ' hd
    simpa only [Work.Spaces.pth, Function.uncurry] using h
  have h1 : Work.Spaces.pthIter 2 Φ z θ = deriv (fun θ' => Work.Spaces.pth Φ z θ') θ := rfl
  rw [h1, hev.deriv_eq]
  exact Work.Spaces.deriv_slice_snd _ z θ hdiffPth

/-! ## The main statement -/

theorem radial_ibp_zero_open (η : ℝ) (hη : 0 < η) (Φ : ℝ → ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a < b)
    (hsm : ContDiffOn ℝ 3 (Function.uncurry Φ) qd)
    (hsupp : ∀ z θ, z ∉ Set.Icc a b → Φ z θ = 0) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (∫ z in Set.Ioi 0,
        deriv (fun z' => (z' ^ 2 * Work.Spaces.pz Φ z' θ * (Work.Spaces.w z') ^ 2)
            * Work.Spaces.pthIter 2 Φ z' θ) z
          * (Real.sin (2 * θ)) ^ (-η)) = 0 := by
  intro θ hθmem
  -- ### `∂_zΦ(·,θ)` vanishes off the support
  have hpz_zero : ∀ z, z ∈ Set.Ioi 0 → z ∉ Set.Icc a b → Work.Spaces.pz Φ z θ = 0 := by
    intro z hz hzc
    have hnot : z < a ∨ b < z := by
      by_contra hcon
      push Not at hcon
      exact hzc ⟨hcon.1, hcon.2⟩
    rcases hnot with hlt | hgt
    · have hev : (fun z' => Φ z' θ) =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) a from ⟨hz, hlt⟩)]
          with z' hz'
        exact hsupp z' θ (by
          show ¬(a ≤ z' ∧ z' ≤ b)
          rintro ⟨h1, h2⟩
          linarith [hz'.2, h1])
      rw [show Work.Spaces.pz Φ z θ = deriv (fun z' => Φ z' θ) z from rfl, hev.deriv_eq]
      simp
    · have hev : (fun z' => Φ z' θ) =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo b (z + 1) from ⟨hgt, by linarith⟩)]
          with z' hz'
        exact hsupp z' θ (by
          show ¬(a ≤ z' ∧ z' ≤ b)
          rintro ⟨h1, h2⟩
          linarith [hz'.1, h2])
      rw [show Work.Spaces.pz Φ z θ = deriv (fun z' => Φ z' θ) z from rfl, hev.deriv_eq]
      simp
  -- ### `∂_θ²Φ(z,·)` vanishes identically off the support
  have hpth_zero : ∀ z, z ∉ Set.Icc a b → Work.Spaces.pthIter 2 Φ z θ = 0 := by
    intro z hzc
    have hzero : (fun θ' => Φ z θ') = fun _ => (0 : ℝ) := funext (fun θ' => hsupp z θ' hzc)
    have hpth : Work.Spaces.pth Φ z = fun _ => (0 : ℝ) := by
      funext θ'
      rw [show Work.Spaces.pth Φ z θ' = deriv (fun θ'' => Φ z θ'') θ' from rfl, hzero]
      simp
    rw [show Work.Spaces.pthIter 2 Φ z θ = deriv (fun θ' => Work.Spaces.pth Φ z θ') θ from rfl,
      hpth]
    simp
  -- ### `ribpG Φ θ` vanishes off the support
  have hG_supp : ∀ z, 0 < z → (z < a ∨ b < z) → ribpG Φ θ z = 0 := by
    intro z hz0 hc
    have hzI : z ∈ Set.Ioi (0 : ℝ) := hz0
    have hzc : z ∉ Set.Icc a b := by
      show ¬(a ≤ z ∧ z ≤ b)
      rintro ⟨h1, h2⟩
      rcases hc with h | h <;> linarith
    have h1 : ribpPz Φ (z, θ) = 0 := by
      rw [← ribp_pz_eq_Pz Φ hsm hzI hθmem]; exact hpz_zero z hzI hzc
    have h2 : ribpPth2 Φ (z, θ) = 0 := by
      rw [← ribp_pthIter_two_eq_Pth2 Φ hsm hzI hθmem]; exact hpth_zero z hzc
    simp only [ribpG, h1, h2, mul_zero]
  -- ### and so does its derivative
  have hGderiv_supp : ∀ z, 0 < z → (z < a ∨ b < z) → deriv (ribpG Φ θ) z = 0 := by
    intro z hz0 hc
    rcases hc with hlt | hgt
    · have hev : ribpG Φ θ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo (0 : ℝ) a from ⟨hz0, hlt⟩)]
          with z' hz'
        exact hG_supp z' hz'.1 (Or.inl hz'.2)
      rw [hev.deriv_eq]; simp
    · have hev : ribpG Φ θ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo b (z + 1) from ⟨hgt, by linarith⟩)]
          with z' hz'
        exact hG_supp z' (by linarith [hz'.1, hgt, ha, hab]) (Or.inr hz'.1)
      rw [hev.deriv_eq]; simp
  -- ### `ribpG Φ θ` is `C¹` on `(0,∞)`
  have hG1 : ContDiffOn ℝ 1 (ribpG Φ θ) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 1 (fun z : ℝ => z ^ 2) (Set.Ioi 0) := by fun_prop
    have h2 : ContDiffOn ℝ 1 (fun z : ℝ => ribpPz Φ (z, θ)) (Set.Ioi 0) :=
      (ribp_contDiffOn_slice (ribp_contDiffOn_Pz Φ hsm) (W := Set.Ioi (0 : ℝ))
        (fun z hz => ⟨hz, hθmem⟩)).of_le (by norm_num)
    have h3 : ContDiffOn ℝ 1 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
      have hnum : ContDiffOn ℝ 1 (fun z : ℝ => ((1 + z) ^ 2) ^ 2) (Set.Ioi 0) := by fun_prop
      have hden : ContDiffOn ℝ 1 (fun z : ℝ => (z ^ 2) ^ 2) (Set.Ioi 0) := by fun_prop
      have hne : ∀ z ∈ Set.Ioi (0 : ℝ), (z ^ 2) ^ 2 ≠ 0 := fun z hz =>
        pow_ne_zero _ (pow_ne_zero _ (ne_of_gt (show (0 : ℝ) < z from hz)))
      refine (hnum.div hden hne).congr ?_
      intro z _
      simp only [Pi.div_apply, Work.Spaces.w, div_pow]
    have h4 : ContDiffOn ℝ 1 (fun z : ℝ => ribpPth2 Φ (z, θ)) (Set.Ioi 0) :=
      ribp_contDiffOn_slice (ribp_contDiffOn_Pth2 Φ hsm) (W := Set.Ioi (0 : ℝ))
        (fun z hz => ⟨hz, hθmem⟩)
    simpa only [ribpG] using ((h1.mul h2).mul h3).mul h4
  have hsub : Set.Icc (a / 2) (b + 1) ⊆ Set.Ioi (0 : ℝ) := fun z hz => by
    simp only [Set.mem_Ioi]; linarith [hz.1, ha]
  have hGint : IntervalIntegrable (deriv (ribpG Φ θ)) volume (a / 2) (b + 1) :=
    ContinuousOn.intervalIntegrable_of_Icc (by linarith) (hG1.continuousOn_deriv_of_isOpen
      isOpen_Ioi le_rfl |>.mono hsub)
  -- ### the fundamental theorem of calculus on `[a/2, b+1]`
  have hFTC : (∫ x in (a / 2)..(b + 1), deriv (ribpG Φ θ) x) = 0 := by
    have hcont : ContinuousOn (ribpG Φ θ) (Set.Icc (a / 2) (b + 1)) := hG1.continuousOn.mono hsub
    have hdiffOn : DifferentiableOn ℝ (ribpG Φ θ) (Set.Ioi 0) := hG1.differentiableOn (by norm_num)
    have hderiv : ∀ x ∈ Set.Ioo (a / 2) (b + 1),
        HasDerivAt (ribpG Φ θ) (deriv (ribpG Φ θ) x) x := by
      intro x hx
      have hx0 : x ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi]; linarith [hx.1, ha]
      exact (hdiffOn.differentiableAt (isOpen_Ioi.mem_nhds hx0)).hasDerivAt
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show a / 2 ≤ b + 1 by linarith)
      hcont hderiv hGint
    rw [h, hG_supp (b + 1) (by linarith) (Or.inr (by linarith)),
        hG_supp (a / 2) (by linarith) (Or.inl (by linarith))]
    ring
  -- ### translate the improper integral into the interval integral
  have hset : (∫ z in Set.Ioi (0 : ℝ), deriv (ribpG Φ θ) z)
      = ∫ z in (a / 2)..(b + 1), deriv (ribpG Φ θ) z := by
    have h1 : (∫ z in Set.Ioi (0 : ℝ), deriv (ribpG Φ θ) z)
        = ∫ z in Set.Icc (a / 2) (b + 1), deriv (ribpG Φ θ) z :=
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
        (fun x hx => by
          have hc : x < a / 2 ∨ b + 1 < x := by
            by_contra hcon
            push Not at hcon
            exact hx.2 ⟨hcon.1, hcon.2⟩
          have hc' : x < a ∨ b < x := by
            rcases hc with h | h
            · exact Or.inl (by linarith)
            · exact Or.inr (by linarith)
          exact hGderiv_supp x hx.1 hc')
    rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  -- ### the integrand of the statement is `deriv (ribpG Φ θ)`
  have hEqOn : Set.EqOn
      (fun z => deriv (fun z' => (z' ^ 2 * Work.Spaces.pz Φ z' θ * (Work.Spaces.w z') ^ 2)
        * Work.Spaces.pthIter 2 Φ z' θ) z)
      (deriv (ribpG Φ θ)) (Set.Ioi 0) := by
    intro z hz
    have hev : (fun z' => (z' ^ 2 * Work.Spaces.pz Φ z' θ * (Work.Spaces.w z') ^ 2)
          * Work.Spaces.pthIter 2 Φ z' θ) =ᶠ[nhds z] (ribpG Φ θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      have h1 := ribp_pz_eq_Pz Φ hsm hz' hθmem
      have h2 := ribp_pthIter_two_eq_Pth2 Φ hsm hz' hθmem
      simp only [ribpG, h1, h2]
    exact hev.deriv_eq
  rw [MeasureTheory.integral_mul_const,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqOn, hset, hFTC, zero_mul]

end Work.FTS.EllipticEst.H2W.SlotA
