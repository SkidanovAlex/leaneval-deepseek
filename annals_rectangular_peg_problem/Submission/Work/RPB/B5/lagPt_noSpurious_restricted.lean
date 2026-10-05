import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.collar_noSpurious_restricted

/-!
# B5: no spurious `τ_θ`-coincidences of the family `ℓ`, restricted hypotheses

This is the same statement as `Work.RPB.B5.lagPt_noSpurious` but with the embedding hypothesis
`hemb` and the "no spurious" hypothesis `hnosp` assumed only for levels `σ, σ' ≥ 0` and times
`τ ∈ Icc 0 1`.  The argument is unchanged: the only levels ever used in the collision are
`sig x = x²/2 - 1` and `sig x' = (x')²/2 - 1`, which are `≥ 0` precisely in the collar regime
`|x| ≥ √2`, `|x'| ≥ √2` in which that collision occurs.

The proof has two ingredients.

* `K0` is preserved by `Tk` and `tau`, so `K0 (ℓ (x',t')) = K0 (ℓ (x,t))`.
* `K0 (ℓ (x,t)) = -x²/2` for `|x| ≥ √2` (both points then lie on the collar, so that the
  restricted "no spurious" hypothesis `hnosp` applies at the nonnegative levels `sig x`, `sig x'`
  — after absorbing the half-plane `tau π`'s of `lagPt` into the phase, which changes `θ` only by
  `±π`), while `K0 (ℓ (x,t)) > -1` for `|x| < √2` (the chord chart, where `hK` bounds the level
  from below).

Hence `K0 (ℓ (x,t)) > -1` must hold, and then `|x| < √2` and `|x'| < √2`.

The hypotheses `hperΓ`, `hperA`, `hemb` are not used in the argument: the "no spurious"
hypothesis is taken as given.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

open Work.RPV

private lemma sqrt2_pos_r : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)

/-! ## Unfolding `lagPt` and `basePt` in the two half planes -/

/-- On `x ≤ 0` the family is its base half. -/
private lemma lagPt_of_nonpos_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : x ≤ 0) :
    lagPt W Γc Ac rho τ x t = basePt W Γc Ac rho τ x t := by
  rw [lagPt, if_pos hx]

/-- On `x > 0` the family is `τ_π` of the reflected base half. -/
private lemma lagPt_of_pos_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ} (hx : 0 < x) :
    lagPt W Γc Ac rho τ x t =
      Work.RPV.tau Real.pi (basePt W Γc Ac rho τ (-x) (t - Real.pi)) := by
  rw [lagPt, if_neg (not_le.mpr hx)]

/-- Deep on the left, the base half is the collar. -/
private lemma basePt_of_le_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : x ≤ -Real.sqrt 2) :
    basePt W Γc Ac rho τ x t = collarPt Γc Ac τ (sig x) t := by
  rw [basePt, if_pos hx]

/-- On `-√2 < x`, the base half is the chord chart. -/
private lemma basePt_of_gt_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : -Real.sqrt 2 < x) :
    basePt W Γc Ac rho τ x t = W τ t (rho τ x t) := by
  rw [basePt, if_neg (not_le.mpr hx)]

/-- Canonical collar form of `lagPt` for `x ≤ -√2`. -/
private lemma lagPt_collar_neg_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : x ≤ -Real.sqrt 2) :
    lagPt W Γc Ac rho τ x t =
      Work.RPV.levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t) := by
  have hx0 : x ≤ 0 := by linarith [sqrt2_pos_r]
  rw [lagPt_of_nonpos_r W Γc Ac rho hx0, basePt_of_le_r W Γc Ac rho hx, collarPt]

/-- Canonical collar form of `lagPt` for `√2 ≤ x`: here the family is `τ_π` of the collar at
`-x`, and `τ_π` of a `levelPt` is a `levelPt` of the same reduced coordinate and level. -/
private lemma lagPt_collar_pos_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : Real.sqrt 2 ≤ x) :
    lagPt W Γc Ac rho τ x t =
      Work.RPV.tau Real.pi
        (Work.RPV.levelPt (Γc τ (sig x) (t - Real.pi)) (sig x)
          (Ac τ (sig x) (t - Real.pi))) := by
  have hx0 : 0 < x := lt_of_lt_of_le sqrt2_pos_r hx
  have hnx : -x ≤ -Real.sqrt 2 := by linarith
  have hs : sig (-x) = sig x := by simp only [sig]; ring
  rw [lagPt_of_pos_r W Γc Ac rho hx0, basePt_of_le_r W Γc Ac rho hnx, collarPt, hs]

/-! ## `K0` of the family -/

/-- On the collar half, `K0 (ℓ (x,t)) = -x²/2`. -/
private lemma K0_lagPt_of_ge_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (hx : Real.sqrt 2 ≤ |x|) :
    Work.RPV.K0 (lagPt W Γc Ac rho τ x t) = -x ^ 2 / 2 := by
  by_cases hx0 : x ≤ 0
  · have hxs : x ≤ -Real.sqrt 2 := by
      have h := hx; rw [abs_of_nonpos hx0] at h; linarith
    rw [lagPt_collar_neg_r W Γc Ac rho hxs, Work.RPV.K0_levelPt]
    simp only [sig]; ring
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hxs : Real.sqrt 2 ≤ x := by
      have h := hx; rw [abs_of_pos hxpos] at h; exact h
    rw [lagPt_collar_pos_r W Γc Ac rho hxs, Work.RPV.K0_tau, Work.RPV.K0_levelPt]
    simp only [sig]; ring

/-- On the chord-chart half, `K0 (ℓ (x,t)) > -1`, by the hypothesis `hK` on the chart `W`. -/
private lemma one_lt_K0_lagPt_of_lt_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ)
    (hK : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      -1 < Work.RPV.K0 (W τ t (rho τ x t)))
    {τ x t : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hx : |x| < Real.sqrt 2) :
    -1 < Work.RPV.K0 (lagPt W Γc Ac rho τ x t) := by
  by_cases hx0 : x ≤ 0
  · have hgt : -Real.sqrt 2 < x := by
      have h := hx; rw [abs_of_nonpos hx0] at h; linarith
    have hmem : x ∈ Set.Ioc (-Real.sqrt 2) 0 := ⟨hgt, hx0⟩
    rw [lagPt_of_nonpos_r W Γc Ac rho hx0, basePt_of_gt_r W Γc Ac rho hgt]
    exact hK τ hτ x hmem t
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hgt : -Real.sqrt 2 < -x := by
      have h := hx; rw [abs_of_pos hxpos] at h; linarith
    have hmem : -x ∈ Set.Ioc (-Real.sqrt 2) 0 := ⟨hgt, by linarith⟩
    rw [lagPt_of_pos_r W Γc Ac rho hxpos, basePt_of_gt_r W Γc Ac rho hgt, Work.RPV.K0_tau]
    exact hK τ hτ (-x) hmem (t - Real.pi)

/-- Conversely, `-1 < K0 (ℓ (x,t))` forces `|x| < √2`. -/
private lemma lt_sqrt_two_of_K0_r (W : ℝ → ℝ → ℝ → Work.RPV.PS) (Γc : ℝ → ℝ → ℝ → ℂ)
    (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ) {τ x t : ℝ}
    (h : -1 < Work.RPV.K0 (lagPt W Γc Ac rho τ x t)) : |x| < Real.sqrt 2 := by
  by_contra hcon
  have hge : Real.sqrt 2 ≤ |x| := le_of_not_gt hcon
  have hK : Work.RPV.K0 (lagPt W Γc Ac rho τ x t) = -x ^ 2 / 2 :=
    K0_lagPt_of_ge_r W Γc Ac rho hge
  have hx2 : (2 : ℝ) ≤ x ^ 2 := by
    have h1 : (Real.sqrt 2) ^ 2 ≤ |x| ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg 2) hge 2
    rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs] at h1
  rw [hK] at h
  linarith

/-- In the collar regime `√2 ≤ |x|` the attached level `sig x = x²/2 - 1` is nonnegative. -/
private lemma sig_nonneg_r {x : ℝ} (hx : Real.sqrt 2 ≤ |x|) : 0 ≤ sig x := by
  have hx2 : (2 : ℝ) ≤ x ^ 2 := by
    have h1 : (Real.sqrt 2) ^ 2 ≤ |x| ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg 2) hx 2
    rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs] at h1
  simp only [sig]; linarith

/-! ## `θ ± π` are not multiples of `2π` -/

private lemma ne_two_pi_mul_of_mem_r {μ : ℝ} (h1 : 0 < μ) (h2 : μ < 2 * Real.pi) :
    ∀ m : ℤ, μ ≠ 2 * Real.pi * m := by
  intro m hm
  have h2pi : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    rcases lt_trichotomy (m : ℝ) 0 with h | h | h
    · have : 2 * Real.pi * (m : ℝ) < 0 := mul_neg_of_pos_of_neg h2pi h
      linarith [hm]
    · rw [h] at hm
      simp only [mul_zero] at hm
      rw [h]
      linarith
    · exact h
  have hmge : (1 : ℝ) ≤ (m : ℝ) := by
    have h0 : (0 : ℤ) < m := by exact_mod_cast hmpos
    have h1 : (1 : ℤ) ≤ m := by omega
    exact_mod_cast h1
  have hle : 2 * Real.pi ≤ 2 * Real.pi * (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hmge (le_of_lt h2pi)
    simpa using this
  linarith [hm]

private lemma ne_two_pi_mul_of_neg_r {μ : ℝ} (h1 : -Real.pi < μ) (h2 : μ < 0) :
    ∀ m : ℤ, μ ≠ 2 * Real.pi * m := by
  intro m hm
  have hpos : 0 < -μ := by linarith
  have hlt : -μ < 2 * Real.pi := by linarith [Real.pi_pos]
  have hneg : -μ = 2 * Real.pi * ((-m : ℤ) : ℝ) := by
    push_cast
    linarith [hm]
  exact ne_two_pi_mul_of_mem_r hpos hlt (-m) hneg

/-! ## The `τ_π`-conjugation and the collision with the restricted `hnosp` -/

/-- Conjugating by `tau (-η')` turns a `tau η'`-wrapped point on the left into a bare one, at the
price of shifting the angle of the `tau` on the right by `η - η'`. -/
private lemma tau_conj_r (θ η η' : ℝ) (z : Work.RPV.PS) (k : ℤ) :
    Work.RPV.tau (-η') (Work.RPV.Tk k (Work.RPV.tau θ (Work.RPV.tau η z))) =
      Work.RPV.Tk k (Work.RPV.tau (θ + η - η') z) := by
  rw [Work.RPV.tau_add θ η z]
  have h1 : Work.RPV.tau (-η') (Work.RPV.Tk k (Work.RPV.tau (θ + η) z)) =
      Work.RPV.Tk k (Work.RPV.tau (-η') (Work.RPV.tau (θ + η) z)) :=
    (Work.RPV.Tk_tau k (-η') (Work.RPV.tau (θ + η) z)).symm
  rw [h1, Work.RPV.tau_add]
  rw [show -η' + (θ + η) = θ + η - η' by ring]

/-- Both points on the collar at nonnegative levels: the restricted hypothesis `hnosp` kills the
coincidence. -/
private lemma collide_r (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ)
    (hnosp : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ σ' t t' (k : ℤ) (μ : ℝ), 0 ≤ σ → 0 ≤ σ' →
      (∀ m : ℤ, μ ≠ 2 * Real.pi * m) →
      Work.RPV.levelPt (Γc τ σ t) σ (Ac τ σ t) ≠
        Work.RPV.Tk k (Work.RPV.tau μ (Work.RPV.levelPt (Γc τ σ' t') σ' (Ac τ σ' t'))))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) {θ η η' : ℝ} {k : ℤ}
    (hμ : ∀ m : ℤ, θ + η - η' ≠ 2 * Real.pi * m)
    {σ σ' u u' : ℝ} (hσ : 0 ≤ σ) (hσ' : 0 ≤ σ')
    (h : Work.RPV.tau η' (Work.RPV.levelPt (Γc τ σ' u') σ' (Ac τ σ' u')) =
      Work.RPV.Tk k (Work.RPV.tau θ
        (Work.RPV.tau η (Work.RPV.levelPt (Γc τ σ u) σ (Ac τ σ u))))) :
    False := by
  have h2 : Work.RPV.tau (-η')
        (Work.RPV.tau η' (Work.RPV.levelPt (Γc τ σ' u') σ' (Ac τ σ' u'))) =
      Work.RPV.tau (-η') (Work.RPV.Tk k (Work.RPV.tau θ
        (Work.RPV.tau η (Work.RPV.levelPt (Γc τ σ u) σ (Ac τ σ u))))) := by
    rw [h]
  rw [Work.RPV.tau_neg, tau_conj_r] at h2
  exact hnosp τ hτ σ' σ u' u k (θ + η - η') hσ' hσ hμ h2

theorem lagPt_noSpurious_restricted (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ)
    (hK : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      -1 < Work.RPV.K0 (W τ t (rho τ x t)))
    (hperΓ : ∀ τ σ t, Γc τ σ (t + 2 * Real.pi) = Γc τ σ t)
    (hperA : ∀ τ σ t, Ac τ σ (t + 2 * Real.pi) = Ac τ σ t + 2 * Real.pi)
    (hemb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ, 0 ≤ σ →
      (∀ t, deriv (fun s => Γc τ σ s) t ≠ 0) ∧
      (∀ t t', Γc τ σ t = Γc τ σ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m))
    (hnosp : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ σ' t t' (k : ℤ) (μ : ℝ), 0 ≤ σ → 0 ≤ σ' →
      (∀ m : ℤ, μ ≠ 2 * Real.pi * m) →
      Work.RPV.levelPt (Γc τ σ t) σ (Ac τ σ t) ≠
        Work.RPV.Tk k (Work.RPV.tau μ (Work.RPV.levelPt (Γc τ σ' t') σ' (Ac τ σ' t')))) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ θ : ℝ, 0 < θ → θ < Real.pi → ∀ x t x' t' (k : ℤ),
      lagPt W Γc Ac rho τ x' t' = Work.RPV.Tk k (Work.RPV.tau θ (lagPt W Γc Ac rho τ x t)) →
        |x| < Real.sqrt 2 ∧ |x'| < Real.sqrt 2 := by
  intro τ hτ θ hθ0 hθπ x t x' t' k heq
  -- `K0` is preserved by `Tk` and `tau`
  have hK0eq : Work.RPV.K0 (lagPt W Γc Ac rho τ x t) =
      Work.RPV.K0 (lagPt W Γc Ac rho τ x' t') := by
    rw [heq, Work.RPV.K0_Tk, Work.RPV.K0_tau]
  by_cases hA : -1 < Work.RPV.K0 (lagPt W Γc Ac rho τ x t)
  · exact ⟨lt_sqrt_two_of_K0_r W Γc Ac rho hA,
      lt_sqrt_two_of_K0_r W Γc Ac rho (by rw [← hK0eq]; exact hA)⟩
  · -- otherwise both points are on the collar, and `hnosp` gives a contradiction
    exfalso
    have hxA : Real.sqrt 2 ≤ |x| := by
      by_contra hcon
      exact hA (one_lt_K0_lagPt_of_lt_r W Γc Ac rho hK hτ (lt_of_not_ge hcon))
    have hxA' : Real.sqrt 2 ≤ |x'| := by
      by_contra hcon
      exact hA (by
        rw [hK0eq]
        exact one_lt_K0_lagPt_of_lt_r W Γc Ac rho hK hτ (lt_of_not_ge hcon))
    have hsx : 0 ≤ sig x := sig_nonneg_r hxA
    have hsx' : 0 ≤ sig x' := sig_nonneg_r hxA'
    by_cases hx0 : x ≤ 0
    · by_cases hx0' : x' ≤ 0
      · -- `x ≤ -√2`, `x' ≤ -√2`
        have hxle : x ≤ -Real.sqrt 2 := by
          have h := hxA; rw [abs_of_nonpos hx0] at h; linarith
        have hxle' : x' ≤ -Real.sqrt 2 := by
          have h := hxA'; rw [abs_of_nonpos hx0'] at h; linarith
        have hL : lagPt W Γc Ac rho τ x t =
            Work.RPV.levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t) :=
          lagPt_collar_neg_r W Γc Ac rho hxle
        have hL' : lagPt W Γc Ac rho τ x' t' =
            Work.RPV.levelPt (Γc τ (sig x') t') (sig x') (Ac τ (sig x') t') :=
          lagPt_collar_neg_r W Γc Ac rho hxle'
        exact collide_r Γc Ac hnosp hτ
          (θ := θ) (η := 0) (η' := 0) (k := k)
          (by simpa using ne_two_pi_mul_of_mem_r hθ0 (by linarith [hθπ, Real.pi_pos]))
          hsx hsx'
          (by simpa [Work.RPV.tau_zero, hL', hL] using heq)
      · -- `x ≤ -√2`, `√2 ≤ x'`
        have hxpos' : 0 < x' := lt_of_not_ge hx0'
        have hxle : x ≤ -Real.sqrt 2 := by
          have h := hxA; rw [abs_of_nonpos hx0] at h; linarith
        have hxge' : Real.sqrt 2 ≤ x' := by
          have h := hxA'; rw [abs_of_pos hxpos'] at h; exact h
        have hL : lagPt W Γc Ac rho τ x t =
            Work.RPV.levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t) :=
          lagPt_collar_neg_r W Γc Ac rho hxle
        have hL' : lagPt W Γc Ac rho τ x' t' =
            Work.RPV.tau Real.pi
              (Work.RPV.levelPt (Γc τ (sig x') (t' - Real.pi)) (sig x')
                (Ac τ (sig x') (t' - Real.pi))) :=
          lagPt_collar_pos_r W Γc Ac rho hxge'
        exact collide_r Γc Ac hnosp hτ
          (θ := θ) (η := 0) (η' := Real.pi) (k := k)
          (by simpa using ne_two_pi_mul_of_neg_r (by linarith) (by linarith))
          hsx hsx'
          (by simpa [Work.RPV.tau_zero, hL', hL] using heq)
    · -- `√2 ≤ x`
      have hxpos : 0 < x := lt_of_not_ge hx0
      have hxge : Real.sqrt 2 ≤ x := by
        have h := hxA; rw [abs_of_pos hxpos] at h; exact h
      have hL : lagPt W Γc Ac rho τ x t =
          Work.RPV.tau Real.pi
            (Work.RPV.levelPt (Γc τ (sig x) (t - Real.pi)) (sig x)
              (Ac τ (sig x) (t - Real.pi))) :=
        lagPt_collar_pos_r W Γc Ac rho hxge
      by_cases hx0' : x' ≤ 0
      · -- `√2 ≤ x`, `x' ≤ -√2`
        have hxle' : x' ≤ -Real.sqrt 2 := by
          have h := hxA'; rw [abs_of_nonpos hx0'] at h; linarith
        have hL' : lagPt W Γc Ac rho τ x' t' =
            Work.RPV.levelPt (Γc τ (sig x') t') (sig x') (Ac τ (sig x') t') :=
          lagPt_collar_neg_r W Γc Ac rho hxle'
        exact collide_r Γc Ac hnosp hτ
          (θ := θ) (η := Real.pi) (η' := 0) (k := k)
          (by simpa using ne_two_pi_mul_of_mem_r (by linarith) (by linarith [hθπ, Real.pi_pos]))
          hsx hsx'
          (by simpa [Work.RPV.tau_zero, hL', hL] using heq)
      · -- `√2 ≤ x`, `√2 ≤ x'`
        have hxpos' : 0 < x' := lt_of_not_ge hx0'
        have hxge' : Real.sqrt 2 ≤ x' := by
          have h := hxA'; rw [abs_of_pos hxpos'] at h; exact h
        have hL' : lagPt W Γc Ac rho τ x' t' =
            Work.RPV.tau Real.pi
              (Work.RPV.levelPt (Γc τ (sig x') (t' - Real.pi)) (sig x')
                (Ac τ (sig x') (t' - Real.pi))) :=
          lagPt_collar_pos_r W Γc Ac rho hxge'
        exact collide_r Γc Ac hnosp hτ
          (θ := θ) (η := Real.pi) (η' := Real.pi) (k := k)
          (by simpa using ne_two_pi_mul_of_mem_r hθ0 (by linarith [hθπ, Real.pi_pos]))
          hsx hsx'
          (by simpa [hL', hL] using heq)

end Work.RPB.B5
