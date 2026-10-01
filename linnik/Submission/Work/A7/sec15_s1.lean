/-
# §15 — the `S₁`-term bounds (the characters `χ₁, χ₁⁻¹`)

For the two characters `χ₁`, `χ₁⁻¹` the §15 core uses a *refined* bound, exploiting that the
least zero `ρ` (respectively its conjugate) is isolated with multiplicity one.  This file
packages the three mutually exclusive cases of that argument into lemmas with a single
conclusion shape

  `WBox q (3/10) R χ ≤ (9/100)·(CST + (Φ(Λ)/w(Λ))·w(λ) + η)`.

* `S1_alpha1` — the `α = 1` refinement (`chi1_refined_le`) with fallback to `chi1_second_le`;
* `S1_rc`     — the `α = 2` refinement (`chi1_refined2_le`, `χ` real, `ρ` non-real) with the
               same fallbacks;
* `S1_plain`  — the plain bound (`chi1_plain_le`) used when `c₀` is unavailable.
-/
import Mathlib
import Submission.Work.A7.sec15_helper
import Submission.Work.A7.chi1_refined_le
import Submission.Work.A7.chi1_refined2_le
import Submission.Work.A7.chi1_second_le
import Submission.Work.A7.chi1_plain_le
import Submission.Work.A7.box_api7
import Submission.Work.LinnikAreas.A7.Basic7
import Submission.Work.A7.chi1_inv_api

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
namespace Work.A7

open Work.LinnikContract
open Work.LinnikAreas.A7

/-- Complex conjugation fixes a complex number with vanishing imaginary part. -/
lemma starRingEnd_eq_of_im_eq_zero {ρ : ℂ} (h : ρ.im = 0) : (starRingEnd ℂ) ρ = ρ :=
  Complex.conj_eq_iff_im.mpr h

/-- The `α = 1` bound for a character `χ` (either `χ₁` or `χ₁⁻¹`) whose least zero is `ρ`
(either `ρ₁` or `conj ρ₁`), in the case where `ρ` is not non-real for a real `χ`. -/
lemma S1_alpha1 {q : ℕ} [NeZero q] {R Λ c η lam CST : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hq : 2 ≤ q) (hRlog : R ≤ Real.log q)
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam0 : 0 < lam) (hlamΛ : lam ≤ Λ) (hlamc : lam ≤ c)
    (hLam0 : Lam0Bound χ ρ c) (hZ : IsZ χ ρ) (hlam : lamOf q ρ = lam)
    (hnotrc : χ ^ 2 = 1 → ρ.im = 0)
    (hcert : boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam + η))
    (hrowA : Cf Λ lam - Aref c lam ≤ CST) :
    WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (CST + (Phi Λ / Wf Λ) * wHB lam + η) := by
  by_cases hb : InBox q R ρ ∧ zeroMult χ ρ = 1
  · obtain ⟨hbox, hmult⟩ := hb
    refine chi1_refined_le hΛ hη hlam0 hlamΛ hlamc hbox hmult hlam ?_ hcert hrowA
    intro ρ' hb' hz' hne'
    refine hLam0.2 ρ' (box_api7_p1 hq hRlog hZ.1 hz' hb') hne' (fun hsq => ?_)
    rw [starRingEnd_eq_of_im_eq_zero (hnotrc hsq)]
    exact hne'
  · refine chi1_second_le hΛ hη hlam0 hlamΛ hlamc ?_ hcert hrowA
    intro ρ' hb' hz'
    by_cases hIn : InBox q R ρ
    · have hzm2 : 2 ≤ zeroMult χ ρ := by
        have h1 : zeroMult χ ρ ≠ 1 := fun h => hb ⟨hIn, h⟩
        have h0 : zeroMult χ ρ ≠ 0 := hZ.2.1
        omega
      have hclam : c ≤ lam := by rw [← hlam]; exact hLam0.1 hzm2
      by_cases hρ : ρ' = ρ
      · have h2 : lamOf q ρ' = lam := by rw [hρ, ← hlam]
        rwa [h2]
      · by_cases hρc : ρ' = (starRingEnd ℂ) ρ
        · rw [hρc, lamOf_star, hlam]; exact hclam
        · exact hLam0.2 ρ' (box_api7_p1 hq hRlog hZ.1 hz' hb') hρ (fun _ => hρc)
    · refine hLam0.2 ρ' (box_api7_p1 hq hRlog hZ.1 hz' hb') (fun h => hIn (h ▸ hb')) ?_
      intro _ hconj
      exact hIn (InBox_star.mp (by rw [← hconj]; exact hb'))

/-- The bound for a real character `χ` (`χ² = 1`) whose least zero `ρ` may be non-real: the
`α = 2` refinement when `ρ` is a simple box zero, and the same fallbacks as `S1_alpha1`.
`CST` is assumed to bound both `Cf Λ lam - Aref c lam` and `Cf Λ lam - Aref2 c lam`. -/
lemma S1_rc {q : ℕ} [NeZero q] {R Λ c η lam CST : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hq : 2 ≤ q) (hRlog : R ≤ Real.log q)
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam0 : 0 < lam) (hlamΛ : lam ≤ Λ) (hlamc : lam ≤ c)
    (hLam0 : Lam0Bound χ ρ c) (hZ : IsZ χ ρ) (hlam : lamOf q ρ = lam) (hsq : χ ^ 2 = 1)
    (hcert : boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam + η))
    (hrowA : Cf Λ lam - Aref c lam ≤ CST) (hrowA2 : Cf Λ lam - Aref2 c lam ≤ CST) :
    WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (CST + (Phi Λ / Wf Λ) * wHB lam + η) := by
  by_cases hb : InBox q R ρ ∧ zeroMult χ ρ = 1
  · obtain ⟨hbox, hmult⟩ := hb
    by_cases him : ρ.im = 0
    · refine chi1_refined_le hΛ hη hlam0 hlamΛ hlamc hbox hmult hlam ?_ hcert hrowA
      intro ρ' hb' hz' hne'
      refine hLam0.2 ρ' (box_api7_p1 hq hRlog hZ.1 hz' hb') hne' (fun _ => ?_)
      rw [starRingEnd_eq_of_im_eq_zero him]
      exact hne'
    · have hne : (starRingEnd ℂ) ρ ≠ ρ := fun h => by
        have h2 := congrArg Complex.im h
        simp [Complex.conj_im] at h2
        exact him (by linarith)
      refine chi1_refined2_le hΛ hη hlam0 hlamΛ hlamc hbox ?_ hsq hmult hne hlam ?_ hcert hrowA2
      · rwa [InBox_star]
      · intro ρ' hb' hz' hne' hne2
        exact hLam0.2 ρ' (box_api7_p1 hq hRlog hZ.1 hz' hb') hne' (fun _ => hne2)
  · refine chi1_second_le hΛ hη hlam0 hlamΛ hlamc ?_ hcert hrowA
    intro ρ' hb' hz'
    by_cases hIn : InBox q R ρ
    · have hzm2 : 2 ≤ zeroMult χ ρ := by
        have h1 : zeroMult χ ρ ≠ 1 := fun h => hb ⟨hIn, h⟩
        have h0 : zeroMult χ ρ ≠ 0 := hZ.2.1
        omega
      have hclam : c ≤ lam := by rw [← hlam]; exact hLam0.1 hzm2
      by_cases hρ : ρ' = ρ
      · have h2 : lamOf q ρ' = lam := by rw [hρ, ← hlam]
        rwa [h2]
      · by_cases hρc : ρ' = (starRingEnd ℂ) ρ
        · rw [hρc, lamOf_star, hlam]; exact hclam
        · exact hLam0.2 ρ' (box_api7_p1 hq hRlog hZ.1 hz' hb') hρ (fun _ => hρc)
    · refine hLam0.2 ρ' (box_api7_p1 hq hRlog hZ.1 hz' hb') (fun h => hIn (h ▸ hb')) ?_
      intro _ hconj
      exact hIn (InBox_star.mp (by rw [← hconj]; exact hb'))

/-- The plain bound for a character `χ` all of whose box zeros have `λ ≥ lam`. -/
lemma S1_plain {q : ℕ} [NeZero q] {R Λ c η lam CST1 CST2 : ℝ} {χ : DirichletCharacter ℂ q}
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam0 : 0 < lam) (hlamΛ : lam ≤ Λ)
    (hsecond : ∀ ρ' : ℂ, InBox q R ρ' → zeroMult χ ρ' ≠ 0 → lam ≤ lamOf q ρ')
    (hcert : boxAbs q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam + η))
    (hrowB : Cf Λ lam ≤ CST2) (hcred12 : CST2 ≤ CST1) :
    WBox q ((3:ℝ)/10) R χ ≤ ((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam + η) :=
  chi1_plain_le (c₀ := 0) hΛ hη hlam0 hlamΛ hsecond hcert hrowB hcred12


/-- The generic `S₁`-sum bound: a pointwise bound on the two characters gives the sum bound in the
shape required by `core15`. -/
lemma S1_sum_of {q : ℕ} [NeZero q] {R η lam₁ CST1 Λ : ℝ}
    (S1 : Finset (DirichletCharacter ℂ q))
    (h : ∀ χ ∈ S1, WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam₁ + η)) :
    ∑ χ ∈ S1, WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (S1.card : ℝ) * (CST1 + (Phi Λ / Wf Λ) * wHB lam₁ + η) := by
  calc ∑ χ ∈ S1, WBox q ((3:ℝ)/10) R χ
      ≤ ∑ _χ ∈ S1, ((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam₁ + η) := Finset.sum_le_sum h
    _ = (S1.card : ℝ) * (((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam₁ + η)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((9:ℝ)/100) * (S1.card : ℝ) * (CST1 + (Phi Λ / Wf Λ) * wHB lam₁ + η) := by ring

/-- The `α = 1` refined bound transferred from `χ₁` to `χ₁⁻¹` (via the conjugate zero). -/
lemma S1_inv_bound_alpha1 {q : ℕ} [NeZero q] {R Λ c η lam₁ CST : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hq : 2 ≤ q) (hRlog : R ≤ Real.log q) (hmin : IsMin1 χ₁ ρ₁)
    (hlam1 : lamOf q ρ₁ = lam₁)
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam10 : 0 < lam₁) (hlam1Λ : lam₁ ≤ Λ) (hlam1c : lam₁ ≤ c)
    (hLam0 : Lam0Bound χ₁ ρ₁ c) (hnotrc : χ₁ ^ 2 = 1 → ρ₁.im = 0)
    (hcert : boxAbs q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam₁ + η))
    (hrowA : Cf Λ lam₁ - Aref c lam₁ ≤ CST) :
    WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (CST + (Phi Λ / Wf Λ) * wHB lam₁ + η) := by
  obtain ⟨-, hZ, -, hlam, hLam0', -⟩ := chi1_inv_api hq hmin hLam0
  refine S1_alpha1 (χ := χ₁⁻¹) (ρ := (starRingEnd ℂ) ρ₁) hq hRlog hΛ hη hlam10 hlam1Λ hlam1c
    hLam0' hZ (hlam.trans hlam1) ?_ hcert hrowA
  intro hsq
  have h2 : χ₁ ^ 2 = 1 := by
    simpa using congrArg (fun z : DirichletCharacter ℂ q => z⁻¹) hsq
  have h3 : ρ₁.im = 0 := hnotrc h2
  simp [Complex.conj_im, h3]

/-- The `α = 2` refined bound transferred from `χ₁` to `χ₁⁻¹` (`χ₁` real, so `χ₁⁻¹ = χ₁`). -/
lemma S1_inv_bound_rc {q : ℕ} [NeZero q] {R Λ c η lam₁ CST : ℝ}
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hq : 2 ≤ q) (hRlog : R ≤ Real.log q) (hmin : IsMin1 χ₁ ρ₁)
    (hlam1 : lamOf q ρ₁ = lam₁)
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam10 : 0 < lam₁) (hlam1Λ : lam₁ ≤ Λ) (hlam1c : lam₁ ≤ c)
    (hLam0 : Lam0Bound χ₁ ρ₁ c) (hsq : χ₁ ^ 2 = 1)
    (hcert : boxAbs q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam₁ + η))
    (hrowA : Cf Λ lam₁ - Aref c lam₁ ≤ CST) (hrowA2 : Cf Λ lam₁ - Aref2 c lam₁ ≤ CST) :
    WBox q ((3:ℝ)/10) R χ₁⁻¹ ≤ ((9:ℝ)/100) * (CST + (Phi Λ / Wf Λ) * wHB lam₁ + η) := by
  obtain ⟨-, hZ, -, hlam, hLam0', -⟩ := chi1_inv_api hq hmin hLam0
  have hsq' : χ₁⁻¹ ^ 2 = 1 := by rw [inv_pow, hsq, inv_one]
  exact S1_rc (χ := χ₁⁻¹) (ρ := (starRingEnd ℂ) ρ₁) hq hRlog hΛ hη hlam10 hlam1Λ hlam1c
    hLam0' hZ (hlam.trans hlam1) hsq' hcert hrowA hrowA2

end Work.A7
