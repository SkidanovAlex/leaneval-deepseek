import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Two bookkeeping lemmas for the weighted pairing `IP`

`IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ` is the honest iterated integral of the
angular-weight pairing of `AngSecond/Defs.lean`, and `IPMem g h` is its honesty.  The Step 2
identity `I_identity` below reassembles the five pieces of the paper's computation into the
pairing of the elliptic equation, and needs exactly two facts about `IP`: that it is linear in
its first slot (in finite-sum form), and that it vanishes on functions vanishing in the open
quadrant. -/

/-- **Linearity of the weighted pairing in its first slot, in finite-sum form.**

With `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ` and `IPMem` the honesty of that iterated
integral, a finite linear combination of pairings is the pairing of the linear combination. -/
private theorem IP_sum_left_aux {ι : Type*} [Fintype ι] (c : ι → ℝ) (f : ι → ℝ → ℝ → ℝ)
    (h : ℝ → ℝ → ℝ) (hf : ∀ i, IPMem (f i) h) :
    IP (fun z θ => ∑ i, c i * f i z θ) h = ∑ i, c i * IP (f i) h := by
  simp only [IP]
  have hmid : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (∑ i, c i * f i z θ) * h z θ * w2 z * sig θ)
        = ∑ i, c i * (∫ θ in Work.Spaces.Iθ, f i z θ * h z θ * w2 z * sig θ) := by
    intro z hz
    rw [show (∫ θ in Work.Spaces.Iθ, (∑ i, c i * f i z θ) * h z θ * w2 z * sig θ)
        = ∫ θ in Work.Spaces.Iθ, ∑ i, c i * (f i z θ * h z θ * w2 z * sig θ) from
      setIntegral_congr_fun (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring))]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => MeasureTheory.integral_const_mul (c i) _)
    · intro i _; exact ((hf i).1 z hz).const_mul (c i)
  rw [MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hmid]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact MeasureTheory.integral_const_mul (c i) _
  · intro i _; exact ((hf i).2).const_mul (c i)

/-- **The weighted pairing vanishes on functions vanishing in the open quadrant.**

If `g` vanishes on `(0,∞) × (0,π/2)` then `IP g h = 0`: the complement of the open quadrant
inside `Iz × Iθ` is the null set of the two boundary lines.  No hypothesis on `h` is needed. -/
private theorem IP_eq_zero_of_openQuadrant (g h : ℝ → ℝ → ℝ)
    (hg : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g z θ = 0) :
    IP g h = 0 := by
  simp only [IP]
  have hslice : ∀ z ∈ Work.Spaces.Iz, z ≠ 0 →
      (∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ) = 0 := by
    intro z hz hz0
    rw [show (∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ)
        = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
      setIntegral_congr_ae (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_]
    · simp
    · rw [MeasureTheory.ae_iff]
      refine measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
      · intro θ hθ
        simp only [Set.mem_ofPred_eq] at hθ
        by_contra hbad
        apply hθ
        intro hθI
        have h0 : 0 < θ := lt_of_le_of_ne hθI.1 (fun h => hbad (by rw [h]; simp))
        have h1 : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 (fun h => hbad (by rw [h]; simp))
        have hzpos : 0 < z := lt_of_le_of_ne hz (fun h => hz0 h.symm)
        rw [hg z hzpos θ ⟨h0, h1⟩]; ring
      · rw [show ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} from by
          ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]]
        exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))
  have hae : ∀ᵐ x ∂(volume : MeasureTheory.Measure ℝ), x ∈ Work.Spaces.Iz →
      (∫ θ in Work.Spaces.Iθ, g x θ * h x θ * w2 x * sig θ) = 0 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
    intro z hz
    by_contra hz0
    exact hz (fun hzI => hslice z hzI hz0)
  rw [MeasureTheory.setIntegral_congr_ae
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hae]
  simp

/-- **The Step 2 integral identity** (namespace `Work.FTS.EllipticEst.AngSecond`).

Multiplying the elliptic equation `bslOp α Ψ = F` by `-∂_θθΨ · w²/sin(2θ)^η` and integrating over
the quadrant gives the identity whose five pieces the paper estimates:

  `I₁ + I₂ + I₃ + I₄ + I₅ = - IP F (∂_θθΨ)`

with

  `I₁ = α² · IP (z²∂_zzΨ) (∂_θθΨ)`,  `I₂ = α(5+α) · IP (z∂_zΨ) (∂_θθΨ)`,
  `I₃ = IP (∂_θθΨ) (∂_θθΨ)`,  `I₄ = - IP (∂_θ(tan θ Ψ)) (∂_θθΨ)`,  `I₅ = 6 · IP Ψ (∂_θθΨ)`.

Route: `Work.Elliptic.IsBslSol α F Ψ` gives `bslOp α Ψ = F` pointwise on the open quadrant
(a null set inside `Iz × Iθ`); expand `bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ - ∂_θθΨ
+ ∂_θ(tan θ Ψ) - 6Ψ`, multiply by `-(∂_θθΨ) w²σ` and use additivity of the set integral for the
five honest summands (each `IPMem` hypothesis below is exactly the honesty of the product of that
summand with `∂_θθΨ`).  Nothing analytic is needed: this is bookkeeping for the honest iterated
integral. -/
theorem I_identity (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsol : Work.Elliptic.IsBslSol α F Ψ)
    (hF : IPMem F (Work.Spaces.pthIter 2 Ψ))
    (hQ : IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ))
    (hU : IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ))
    (hG : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hPsi : IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hphi : IPMem (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ)) :
    α ^ 2 * IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      + α * (5 + α) * IP (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      + IP (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ)
      - IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ)
      + 6 * IP Ψ (Work.Spaces.pthIter 2 Ψ)
      = - IP F (Work.Spaces.pthIter 2 Ψ) := by
  -- name the five functions of the pairing (the goal and the hypotheses are written with
  -- exactly these lambdas, so `set` rewrites them all at once)
  set Ph : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hPhdef
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hQdef
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hUdef
  set G : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
    with hGdef
  -- the bracket whose vanishing on the open quadrant *is* the elliptic equation
  set B : ℝ → ℝ → ℝ := fun z θ =>
    F z θ + α ^ 2 * Q z θ + α * (5 + α) * U z θ + Ph z θ - G z θ + 6 * Ψ z θ with hBdef
  -- the six summands and their coefficients, indexed by `Fin 6`
  set c : Fin 6 → ℝ := ![1, α ^ 2, α * (5 + α), 1, -1, 6] with hcdef
  set f : Fin 6 → ℝ → ℝ → ℝ := ![F, Q, U, Ph, G, Ψ] with hfdef
  -- `B` vanishes on the open quadrant: there `F = bslOp α Ψ`
  have hBz : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), B z θ = 0 := by
    intro z hz θ hθ
    have hbs := hsol.1 z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hbs
    simp only [hBdef, hQdef, hUdef, hGdef, hPhdef]
    rw [← hbs]
    ring
  have hzero : IP B Ph = 0 := IP_eq_zero_of_openQuadrant B Ph hBz
  -- `IP B Ph` is the pairing of the linear combination of the six summands
  have hBeq : B = fun z θ => ∑ i : Fin 6, c i * f i z θ := by
    funext z θ
    rw [Fin.sum_univ_six, hcdef, hfdef, hBdef]
    simp
    ring
  have hsum : IP B Ph = ∑ i : Fin 6, c i * IP (f i) Ph := by
    rw [hBeq]
    exact IP_sum_left_aux c f Ph (fun i => by
      fin_cases i <;> simp [hfdef, hF, hQ, hU, hphi, hG, hPsi])
  have hexp : (∑ i : Fin 6, c i * IP (f i) Ph)
      = 1 * IP F Ph + α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + 1 * IP Ph Ph
        + (-1) * IP G Ph + 6 * IP Ψ Ph := by
    rw [Fin.sum_univ_six, hcdef, hfdef]
    simp
  have hsum0 : (∑ i : Fin 6, c i * IP (f i) Ph) = 0 := by
    rw [← hsum]; exact hzero
  -- the left hand side of the goal plus `IP F Ph` is the expanded sum, hence `0`
  have hcomb : α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + IP Ph Ph - IP G Ph
      + 6 * IP Ψ Ph + IP F Ph = 0 := by
    rw [show α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + IP Ph Ph - IP G Ph
        + 6 * IP Ψ Ph + IP F Ph = ∑ i : Fin 6, c i * IP (f i) Ph from by
      rw [hexp]; ring]
    exact hsum0
  rw [eq_neg_iff_add_eq_zero]
  exact hcomb

end Work.FTS.EllipticEst.AngSecond
