import Mathlib
import Submission.Work.Drive.N2C.exists_reparam_unitCircle

/-!
# Sliding between the inverse reparametrisation and the identity

Given a family of maps `h i : ℝ → ℝ` (`i : Fin n`) which are `C^∞`,
1-periodic up to a unit translation (`h i (x+1) = h i x + 1`) and strictly
increasing (they have everywhere positive derivative), we construct a family
`r : ℝ → Fin n → ℝ → ℝ` of reparametrisations with

* `r 0 i = (h i)⁻¹` (the unconditional inverse `Function.invFun (h i)`),
* `r 1 i = id`,
* `(s, x) ↦ r s i x` jointly `C^∞`,
* `r s i (x+1) = r s i x + 1` for every `s`,
* `r s i` strictly increasing for every `s`, with everywhere nonzero derivative.

The construction is the convex combination

  `r s i x = (1 - χ s) * (h i)⁻¹ x + χ s * x`

where `χ = Real.smoothTransition` is the standard smooth step
(`χ = 0` on `(-∞,0]`, `χ = 1` on `[1,∞)`, `0 ≤ χ ≤ 1`).  Both `(h i)⁻¹` and
`id` are increasing bijections of `ℝ` with everywhere positive derivative, so
any convex combination with weights in `[0,1]` summing to `1` is again an
increasing homeomorphism of `ℝ`, and its derivative (a combination of the two
positive derivatives with the same weights) is positive: this is where the
convex combination is used, and it is why the weights are clamped through the
smooth step rather than being the identity in `s`.
-/

namespace Work.Drive.N2C

/-- If `f` is injective, surjective and increases by `1` under `x ↦ x + 1`, then so does its
inverse. -/
lemma invFun_add_one {f : ℝ → ℝ} (hinj : Function.Injective f) (hsurj : Function.Surjective f)
    (hper : ∀ x, f (x + 1) = f x + 1) (x : ℝ) :
    Function.invFun f (x + 1) = Function.invFun f x + 1 := by
  refine hinj ?_
  rw [hper, Function.rightInverse_invFun hsurj x,
    Function.rightInverse_invFun hsurj (x + 1)]

/-- The inverse of a strictly increasing surjection `ℝ → ℝ` is strictly increasing. -/
lemma strictMono_invFun {f : ℝ → ℝ} (hm : StrictMono f) (hsurj : Function.Surjective f) :
    StrictMono (Function.invFun f) := by
  intro x y hxy
  by_contra hle
  push Not at hle
  have h1 : f (Function.invFun f y) ≤ f (Function.invFun f x) := hm.monotone hle
  rw [Function.rightInverse_invFun hsurj x, Function.rightInverse_invFun hsurj y] at h1
  linarith

/-- The inverse of a strictly increasing `C^∞` surjection `ℝ → ℝ` with everywhere nonzero
derivative has everywhere positive derivative (this is the inverse function theorem in the form
of the chain rule applied to `f ∘ f⁻¹ = id`). -/
lemma deriv_invFun_pos {f : ℝ → ℝ} (hm : StrictMono f) (hsurj : Function.Surjective f)
    (hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (h0 : ∀ x, 0 < deriv f x) (y : ℝ) :
    0 < deriv (Function.invFun f) y := by
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.invFun f) :=
    contDiff_invFun_of_strictMono hm hsurj hcd (fun x => ne_of_gt (h0 x))
  have hcomp : (f ∘ Function.invFun f) = id := funext (Function.rightInverse_invFun hsurj)
  have hc : deriv (f ∘ Function.invFun f) y
      = deriv f (Function.invFun f y) * deriv (Function.invFun f) y :=
    deriv_comp (h := Function.invFun f) (h₂ := f) y
      ((hcd.differentiable hn).differentiableAt) ((hg.differentiable hn).differentiableAt)
  have h1 : deriv (f ∘ Function.invFun f) y = 1 := by rw [hcomp]; simp
  rw [h1] at hc
  have hp : 0 < deriv f (Function.invFun f y) := h0 _
  nlinarith [hc, hp]

theorem reparamSlideData {n : ℕ} (h : Fin n → ℝ → ℝ)
    (hcd : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i))
    (hper : ∀ (i : Fin n) (x : ℝ), h i (x + 1) = h i x + 1)
    (hmono : ∀ (i : Fin n) (x : ℝ), 0 < deriv (h i) x) :
    ∃ r : ℝ → Fin n → ℝ → ℝ,
      (∀ (i : Fin n) (x : ℝ), r 0 i x = Function.invFun (h i) x) ∧
      (∀ (i : Fin n) (x : ℝ), r 1 i x = x) ∧
      (∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => r p.1 i p.2)) ∧
      (∀ (i : Fin n) (s x : ℝ), r s i (x + 1) = r s i x + 1) ∧
      (∀ (i : Fin n) (s : ℝ), StrictMono (r s i)) ∧
      (∀ (i : Fin n) (s x : ℝ), deriv (fun y : ℝ => r s i y) x ≠ 0) := by
  have hstr : ∀ i : Fin n, StrictMono (h i) := fun i => strictMono_of_deriv_pos (hmono i)
  have hsurj : ∀ i : Fin n, Function.Surjective (h i) := fun i =>
    surjective_of_continuous_shift (hcd i).continuous one_ne_zero (hper i)
  set g : Fin n → ℝ → ℝ := fun i => Function.invFun (h i) with hgdef
  have hgcd : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i) := fun i =>
    contDiff_invFun_of_strictMono (hstr i) (hsurj i) (hcd i)
      (fun x => ne_of_gt (hmono i x))
  have hgstr : ∀ i : Fin n, StrictMono (g i) := fun i => strictMono_invFun (hstr i) (hsurj i)
  have hgderiv : ∀ (i : Fin n) (y : ℝ), 0 < deriv (g i) y := fun i y =>
    deriv_invFun_pos (hstr i) (hsurj i) (hcd i) (hmono i) y
  have hgper : ∀ (i : Fin n) (y : ℝ), g i (y + 1) = g i y + 1 := fun i y =>
    invFun_add_one (hstr i).injective (hsurj i) (hper i) y
  refine ⟨fun s i x => (1 - Real.smoothTransition s) * g i x + Real.smoothTransition s * x,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    simp only [hgdef]
    simp [Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))]
  · intro i x
    simp [Real.smoothTransition.one_of_one_le (le_refl (1 : ℝ))]
  · intro i
    fun_prop
  · intro i s x
    beta_reduce
    rw [hgper i x]
    ring
  · intro i s
    beta_reduce
    intro x y hxy
    have hgxy : g i x < g i y := hgstr i hxy
    have ha : 0 ≤ 1 - Real.smoothTransition s := by
      linarith [Real.smoothTransition.le_one s]
    have hb : 0 ≤ Real.smoothTransition s := Real.smoothTransition.nonneg s
    rcases lt_or_eq_of_le hb with hbpos | hb0
    · have h2 : Real.smoothTransition s * x < Real.smoothTransition s * y :=
        mul_lt_mul_of_pos_left hxy hbpos
      have h1 : (1 - Real.smoothTransition s) * g i x ≤ (1 - Real.smoothTransition s) * g i y :=
        mul_le_mul_of_nonneg_left (le_of_lt hgxy) ha
      linarith
    · have hma : (1 - Real.smoothTransition s) = 1 := by linarith
      rw [hma, ← hb0]
      simpa using hgxy
  · intro i s x
    beta_reduce
    intro hzero
    have hgd : DifferentiableAt ℝ (g i) x := ((hgcd i).differentiable (by simp)).differentiableAt
    have hd1 : DifferentiableAt ℝ (fun y : ℝ => (1 - Real.smoothTransition s) * g i y) x :=
      hgd.const_mul _
    have hd2 : DifferentiableAt ℝ (fun y : ℝ => Real.smoothTransition s * y) x :=
      differentiableAt_id.const_mul (Real.smoothTransition s)
    have hsplit : (fun y : ℝ => (1 - Real.smoothTransition s) * g i y
          + Real.smoothTransition s * y)
        = (fun y : ℝ => (1 - Real.smoothTransition s) * g i y)
          + fun y : ℝ => Real.smoothTransition s * y := rfl
    have hdid : deriv (fun y : ℝ => Real.smoothTransition s * y) x = Real.smoothTransition s := by
      have h : HasDerivAt (fun y : ℝ => Real.smoothTransition s * y)
          (Real.smoothTransition s) x := by
        simpa using (hasDerivAt_id x).const_mul (Real.smoothTransition s)
      exact h.deriv
    have hd : deriv (fun y : ℝ => (1 - Real.smoothTransition s) * g i y
        + Real.smoothTransition s * y) x
        = (1 - Real.smoothTransition s) * deriv (g i) x + Real.smoothTransition s := by
      rw [hsplit, deriv_add hd1 hd2, deriv_const_mul (1 - Real.smoothTransition s) hgd, hdid]
    rw [hd] at hzero
    have hp : 0 < deriv (g i) x := hgderiv i x
    have ha : 0 ≤ 1 - Real.smoothTransition s := by
      linarith [Real.smoothTransition.le_one s]
    have hb : 0 ≤ Real.smoothTransition s := Real.smoothTransition.nonneg s
    rcases lt_or_eq_of_le hb with hbpos | hb0
    · have hprod : 0 ≤ (1 - Real.smoothTransition s) * deriv (g i) x :=
        mul_nonneg ha (le_of_lt hp)
      linarith
    · have hma : (1 - Real.smoothTransition s) = 1 := by linarith
      have h' : (1 - Real.smoothTransition s) * deriv (g i) x = 0 := by
        rw [← hb0] at hzero
        linarith
      rw [hma, one_mul] at h'
      linarith

end Work.Drive.N2C
