import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.I4SliceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

/-- The derivative of the `I₄` boundary primitive `G`, written in the form that the
algebraic identities `hAlg` of `I4IntervalIdentity` produce: the factor
`deriv (I4P Φ) θ` of the fourth identity is eliminated with the third one. -/
def I4gfun (Φ : ℝ → ℝ) : ℝ → ℝ := fun θ =>
    (Real.sin θ / (Real.cos θ)^3) * I4sig θ * ((Real.cos θ)^2 * deriv (I4psi Φ) θ)
      * (Real.cos θ * (I4b Φ θ + Φ θ))
    + (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2

/-- On an *open* set, a `C^n` function has continuous honest iterated derivatives up to `n`. -/
lemma continuousOn_iteratedDeriv_of_contDiffOn_isOpen {f : ℝ → ℝ} {n : WithTop ℕ∞} {m : ℕ}
    {s : Set ℝ} (hs : IsOpen s) (h : ContDiffOn ℝ n f s) (hmn : (m : WithTop ℕ∞) ≤ n) :
    ContinuousOn (iteratedDeriv m f) s :=
  (h.continuousOn_iteratedDerivWithin hmn hs.uniqueDiffOn).congr
    (fun _ hx => (iteratedDerivWithin_of_isOpen hs hx).symm)

lemma I4II_cos_pos {θ : ℝ} (h : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩

lemma I4II_sin_two_pos {θ : ℝ} (h : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])

lemma contDiffOn_I4psi (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (I4psi Φ) (Set.Ioo 0 (Real.pi / 2)) :=
  hsm.div (Real.contDiff_cos.contDiffOn.of_le le_top)
    (fun _ hx => ne_of_gt (I4II_cos_pos hx))

lemma continuousOn_deriv_I4psi (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun θ => deriv (I4psi Φ) θ) s := by
  have h := continuousOn_iteratedDeriv_of_contDiffOn_isOpen (s := Set.Ioo 0 (Real.pi / 2))
    isOpen_Ioo (contDiffOn_I4psi Φ hsm) (m := 1) (by norm_num)
  rw [iteratedDeriv_one] at h
  exact h.mono hs

/-- **Renamed** to `I4II_continuousOn_deriv_deriv`: the name `continuousOn_deriv_deriv` is
already taken by `Work.FTS.EllipticEst.Honest.SliceMain` (with a different statement), and Lean
rejects any environment containing both declarations, so an unrenamed copy here made it
impossible to import `SliceMain` and `I4IntervalIdentity` into the same module. -/
lemma I4II_continuousOn_deriv_deriv (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    {s : Set ℝ} (hs : s ⊆ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun θ => deriv (deriv Φ) θ) s := by
  have h2 : iteratedDeriv 2 Φ = fun θ => deriv (deriv Φ) θ := by
    funext θ
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h := continuousOn_iteratedDeriv_of_contDiffOn_isOpen (s := Set.Ioo 0 (Real.pi / 2))
    isOpen_Ioo hsm (m := 2) (by norm_num)
  rw [h2] at h
  exact h.mono hs

lemma continuousOn_I4sig {δ θ₁ : ℝ} (hδ : 0 < δ) (hθ₁ : θ₁ < Real.pi / 2) :
    ContinuousOn I4sig (Set.Icc δ θ₁) := by
  have hsub : Set.Icc δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hδ hx.1, lt_of_le_of_lt hx.2 hθ₁⟩
  have hs : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc δ θ₁) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact ContinuousOn.rpow_const (p := -(99 / 100 : ℝ)) hs
    (fun x hx => Or.inl (ne_of_gt (I4II_sin_two_pos (hsub hx))))

theorem I4IntervalIdentity (Φ : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hAlg : (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => Real.tan θ' * Φ θ') θ
          = Real.cos θ * (Φ θ / Real.cos θ)
            + Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ)
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (deriv Φ) θ
          = Real.cos θ * deriv (deriv (fun θ' => Φ θ' / Real.cos θ')) θ
            - 2 * Real.sin θ * deriv (fun θ' => Φ θ' / Real.cos θ') θ
            - Real.cos θ * (Φ θ / Real.cos θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
          = Real.cos θ * (deriv (deriv Φ) θ + Φ θ))
      ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi/2),
        deriv (fun θ' => (1/2) * (Real.sin θ' / (Real.cos θ')^3)
            * (Real.sin (2*θ'))^(-(99/100:ℝ))
            * ((Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ')^2) θ
          = (Real.sin θ / (Real.cos θ)^3) * (Real.sin (2*θ))^(-(99/100:ℝ))
              * ((Real.cos θ)^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ)
              * deriv (fun θ' => (Real.cos θ')^2 * deriv (fun θ'' => Φ θ'' / Real.cos θ'') θ') θ
            + (1/2) * ((1 - 99/100) * (Real.cos θ)^2 + (3 + 99/100) * (Real.sin θ)^2)
              * (Real.sin (2*θ))^(-(99/100:ℝ))
              * (deriv (fun θ' => Φ θ' / Real.cos θ') θ)^2))
    (hGder : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (I4G Φ) (deriv (I4G Φ) θ) θ)
    {δ θ₁ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ₁) (hθ₁ : θ₁ < Real.pi / 2) :
    (∫ θ in δ..θ₁, I4u Φ θ * I4b Φ θ * I4sig θ)
      = (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
        + I4G Φ θ₁ - I4G Φ δ
        - (1 / 2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ) ^ 2)
        - (∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) := by
  obtain ⟨hA1, -, hA3, hA4⟩ := hAlg
  have hIcc : Set.Icc δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hδ hx.1, lt_of_le_of_lt hx.2 hθ₁⟩
  have hIoo : Set.Ioo δ θ₁ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_trans hδ hx.1, lt_trans hx.2 hθ₁⟩
  have hcosne : ∀ x ∈ Set.Icc δ θ₁, Real.cos x ≠ 0 := fun x hx =>
    ne_of_gt (I4II_cos_pos (hIcc hx))
  -- the derivative of `G`, in the algebraic form supplied by `hA3` and `hA4`
  have hg_eq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv (I4G Φ) θ = I4gfun Φ θ := by
    intro θ hθ
    have h3I : deriv (I4P Φ) θ = Real.cos θ * (I4b Φ θ + Φ θ) := hA3 θ hθ
    have h4I : deriv (I4G Φ) θ
        = (Real.sin θ / (Real.cos θ)^3) * I4sig θ * ((Real.cos θ)^2 * deriv (I4psi Φ) θ)
            * deriv (I4P Φ) θ
          + (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2 := hA4 θ hθ
    rw [h4I, h3I]
    simp only [I4gfun, I4b]
  -- the pointwise identity is pure algebra
  have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      I4u Φ θ * I4b Φ θ * I4sig θ
        = Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
          - Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ := by
    intro θ hθ
    have h1I : I4u Φ θ = Real.cos θ * I4psi Φ θ + Real.sin θ * deriv (I4psi Φ) θ := hA1 θ hθ
    have h3I : deriv (I4P Φ) θ = Real.cos θ * (I4b Φ θ + Φ θ) := hA3 θ hθ
    have h4I : deriv (I4G Φ) θ
        = (Real.sin θ / (Real.cos θ)^3) * I4sig θ * ((Real.cos θ)^2 * deriv (I4psi Φ) θ)
            * deriv (I4P Φ) θ
          + (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2 := hA4 θ hθ
    have hc : Real.cos θ ≠ 0 := ne_of_gt (I4II_cos_pos hθ)
    rw [h1I, ← hg_eq θ hθ, h4I, h3I]
    simp only [I4b]
    field_simp
    ring
  -- continuity of the ingredients on the closed interval
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos θ) (Set.Icc δ θ₁) :=
    Real.continuous_cos.continuousOn
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin θ) (Set.Icc δ θ₁) :=
    Real.continuous_sin.continuousOn
  have hdpsi : ContinuousOn (fun θ => deriv (I4psi Φ) θ) (Set.Icc δ θ₁) :=
    continuousOn_deriv_I4psi Φ hsm hIcc
  have hb : ContinuousOn (fun θ => deriv (deriv Φ) θ) (Set.Icc δ θ₁) :=
    I4II_continuousOn_deriv_deriv Φ hsm hIcc
  have hPhi : ContinuousOn Φ (Set.Icc δ θ₁) := hsm.continuousOn.mono hIcc
  have hσ : ContinuousOn I4sig (Set.Icc δ θ₁) := continuousOn_I4sig hδ hθ₁
  have hSig : ContinuousOn I4Sig (Set.Icc δ θ₁) := by
    change ContinuousOn
      (fun θ : ℝ => (1 - 99/100) * (Real.cos θ)^2 + (3 + 99/100) * (Real.sin θ)^2)
      (Set.Icc δ θ₁)
    exact (continuousOn_const.mul (hcos.pow 2)).add (continuousOn_const.mul (hsin.pow 2))
  have hdiv : ContinuousOn (fun θ : ℝ => Real.sin θ / (Real.cos θ)^3) (Set.Icc δ θ₁) :=
    hsin.div (hcos.pow 3) (fun x hx => pow_ne_zero 3 (hcosne x hx))
  have hFAc : ContinuousOn (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
      (Set.Icc δ θ₁) :=
    ((hcos.mul ((contDiffOn_I4psi Φ hsm).continuousOn.mono hIcc)).mul hb).mul hσ
  have hFBc : ContinuousOn (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
      (Set.Icc δ θ₁) :=
    (hSig.mul hσ).mul (hdpsi.pow 2)
  have hFCc : ContinuousOn (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      (Set.Icc δ θ₁) :=
    ((hsin.mul hσ).mul hdpsi).mul hPhi
  have hgc : ContinuousOn (I4gfun Φ) (Set.Icc δ θ₁) := by
    have h3 : ContinuousOn (fun θ => Real.cos θ * (I4b Φ θ + Φ θ)) (Set.Icc δ θ₁) :=
      hcos.mul (hb.add hPhi)
    have h2 : ContinuousOn (fun θ => (Real.cos θ)^2 * deriv (I4psi Φ) θ) (Set.Icc δ θ₁) :=
      (hcos.pow 2).mul hdpsi
    have hmain : ContinuousOn
        (fun θ => (Real.sin θ / (Real.cos θ)^3) * I4sig θ
            * ((Real.cos θ)^2 * deriv (I4psi Φ) θ) * (Real.cos θ * (I4b Φ θ + Φ θ)))
        (Set.Icc δ θ₁) :=
      ((hdiv.mul hσ).mul h2).mul h3
    have hsec : ContinuousOn
        (fun θ => (1/2) * I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2) (Set.Icc δ θ₁) :=
      ((continuousOn_const.mul hSig).mul hσ).mul (hdpsi.pow 2)
    exact hmain.add hsec
  have hGc : ContinuousOn (I4G Φ) (Set.Icc δ θ₁) := by
    have hP : ContinuousOn (fun θ => I4P Φ θ) (Set.Icc δ θ₁) := by
      simp only [I4P]
      exact (hcos.pow 2).mul hdpsi
    exact ((continuousOn_const.mul hdiv).mul hσ).mul (hP.pow 2)
  -- integrability on `δ..θ₁` from continuity on the closed interval
  have huIcc : Set.uIcc δ θ₁ = Set.Icc δ θ₁ := Set.uIcc_of_le hδθ
  have hintB : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc δ θ₁) → IntervalIntegrable f volume δ θ₁ :=
    fun f hf => by rw [← huIcc] at hf; exact hf.intervalIntegrable
  have hFAi : IntervalIntegrable (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
      volume δ θ₁ := hintB _ hFAc
  have hFBi : IntervalIntegrable (fun θ => I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
      volume δ θ₁ := hintB _ hFBc
  have hFCi : IntervalIntegrable (fun θ => Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ)
      volume δ θ₁ := hintB _ hFCc
  have hgi : IntervalIntegrable (I4gfun Φ) volume δ θ₁ := hintB _ hgc
  have h12Bi : IntervalIntegrable
      (fun θ => (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)) volume δ θ₁ :=
    hintB _ (continuousOn_const.mul hFBc)
  -- fundamental theorem of calculus for the primitive `G`
  have hGderiv : ∀ x ∈ Set.Ioo δ θ₁, HasDerivAt (I4G Φ) (I4gfun Φ x) x := by
    intro x hx
    rw [← hg_eq x (hIoo hx)]
    exact hGder x (hIoo hx)
  have hintG : ∫ θ in δ..θ₁, I4gfun Φ θ = I4G Φ θ₁ - I4G Φ δ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδθ hGc hGderiv hgi
  have hcongr : (∫ θ in δ..θ₁, I4u Φ θ * I4b Φ θ * I4sig θ)
      = ∫ θ in δ..θ₁, (Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
          - Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le hδθ] at hθ
    exact hpt θ (hIcc hθ)
  have hsplit : (∫ θ in δ..θ₁, (Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
          - Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ))
      = (∫ θ in δ..θ₁, Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ)
        + (∫ θ in δ..θ₁, I4gfun Φ θ)
        - (1/2) * (∫ θ in δ..θ₁, I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)
        - (∫ θ in δ..θ₁, Real.sin θ * I4sig θ * deriv (I4psi Φ) θ * Φ θ) := by
    have h1 : IntervalIntegrable
        (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ
          - (1/2) * (I4Sig θ * I4sig θ * (deriv (I4psi Φ) θ)^2)) volume δ θ₁ :=
      (hFAi.add hgi).sub h12Bi
    have h2 : IntervalIntegrable
        (fun θ => Real.cos θ * I4psi Φ θ * I4b Φ θ * I4sig θ + I4gfun Φ θ)
        volume δ θ₁ := hFAi.add hgi
    rw [intervalIntegral.integral_sub h1 hFCi, intervalIntegral.integral_sub h2 h12Bi,
      intervalIntegral.integral_add hFAi hgi, intervalIntegral.integral_const_mul]
  rw [hcongr, hsplit, hintG]
  ring

end Work.FTS.EllipticEst.Honest
