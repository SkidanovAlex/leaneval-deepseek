import Mathlib
import Submission.Work.Drive.thinCorner_distance_increasing
import Submission.Work.Drive.chordFrame

/-!
# The local radial monotonicity of a knot (the `G` input of the `OFat` thin loop)

The perpendicular connector of the lead's thin loop joins the cut arc point `r (a + la)` to its
perpendicular foot on the chord line `(r a) (r b)`.  The connector is contained in the closed ball of
radius `‖r (a + la) - r a‖` about `r a` (`Work.Drive.norm_thinCombo_le`); to conclude that it meets
the retained arc only at its own endpoint, one has to know that the points of the retained arc *near*
`a` are **farther** from `r a` than `r (a + la)` is.

That is the statement proved here, in its sharp local form: for a curve whose speed is bounded below
by `m > 0`, above by `M`, and whose velocity is `C`-Lipschitz, the function
`s ↦ ‖γ (a + s) - γ a‖` is *strictly increasing* on `[0, δ]`, and so is its mirror image
`s ↦ ‖γ (a - s) - γ a‖`, for `δ` small (`2 * M * C * δ < m ^ 2`).  The two estimates are the
two-term Taylor bound `Work.Drive.thinCorner_shift_sub_le` applied at the base point `a` (forward)
and at the base point `a - t` (backward); no integral is needed.

The ball form `Work.Drive.exists_local_radial_mono` transfers the constants to every knot in a
`C²`-neighbourhood of the reference knot, which is the shape the `E1` of the `OFat` lane consumes.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## 1. The two derivative computations -/

/-- Derivative of the *forward* radial distance squared. -/
lemma deriv_radial_fwd {γ : ℝ → Space} (hγ : Differentiable ℝ γ) (a x : ℝ) :
    deriv (fun s : ℝ => ‖γ (a + s) - γ a‖ ^ 2)
      x = 2 * inner ℝ (γ (a + x) - γ a) (deriv γ (a + x)) := by
  have h1 : HasDerivAt (fun s : ℝ => γ (a + s) - γ a) (deriv γ (a + x)) x :=
    (((hγ (a + x)).hasDerivAt).comp_const_add a x).sub_const (γ a)
  exact (h1.norm_sq).deriv

/-- Derivative of the *backward* radial distance squared. -/
lemma deriv_radial_bwd {γ : ℝ → Space} (hγ : Differentiable ℝ γ) (a x : ℝ) :
    deriv (fun s : ℝ => ‖γ (a - s) - γ a‖ ^ 2)
      x = 2 * inner ℝ (γ (a - x) - γ a) (-(deriv γ (a - x))) := by
  have h1 : HasDerivAt (fun s : ℝ => γ (a - s) - γ a) (-(deriv γ (a - x))) x :=
    (((hγ (a - x)).hasDerivAt).comp_const_sub a x).sub_const (γ a)
  exact (h1.norm_sq).deriv

/-! ## 2. The signs of the two derivatives -/

/-- Elementary: `inner x y ≥ -‖x‖ * ‖y‖`. -/
lemma neg_inner_le_norm (x y : Space) : -(inner ℝ x y) ≤ ‖x‖ * ‖y‖ := by
  have h := real_inner_le_norm (-x) y
  rwa [inner_neg_left, norm_neg] at h

/-- **The forward derivative is positive.** -/
lemma inner_radial_fwd_pos {γ : ℝ → Space} (hγ : Differentiable ℝ γ)
    {m M C δ : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 ≤ C) (hδ : 2 * M * C * δ < m ^ 2)
    (hspd : ∀ t : ℝ, m ≤ ‖deriv γ t‖) (hspdM : ∀ t : ℝ, ‖deriv γ t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖deriv γ t - deriv γ t'‖ ≤ C * |t' - t|)
    {a x : ℝ} (hx0 : 0 < x) (hxδ : x ≤ δ) :
    0 < inner ℝ (γ (a + x) - γ a) (deriv γ (a + x)) := by
  obtain ⟨herr, -, -⟩ := thinCorner_shift_sub_le (r := γ) hγ hC hlip (b := a) (σ := x) hx0.le
  set e : Space := γ (a + x) - γ a - x • deriv γ a with he
  have hdecomp : γ (a + x) - γ a = x • deriv γ a + e := by rw [he]; abel
  have hbound : inner ℝ (deriv γ a) (deriv γ (a + x)) ≥ m ^ 2 - M * (C * x) := by
    have hsplit : inner ℝ (deriv γ a) (deriv γ (a + x))
        = inner ℝ (deriv γ a) (deriv γ a)
          + inner ℝ (deriv γ a) (deriv γ (a + x) - deriv γ a) := by
      rw [← inner_add_right]; congr 1; abel
    have h1 : inner ℝ (deriv γ a) (deriv γ a) = ‖deriv γ a‖ ^ 2 := real_inner_self_eq_norm_sq _
    have h2 : m ^ 2 ≤ ‖deriv γ a‖ ^ 2 := by
      have h := hspd a
      nlinarith [h, hm]
    have hup := real_inner_le_norm (deriv γ a) (deriv γ (a + x) - deriv γ a)
    have hlo := neg_inner_le_norm (deriv γ a) (deriv γ (a + x) - deriv γ a)
    have h5 : ‖deriv γ (a + x) - deriv γ a‖ ≤ C * x := by
      have h6 := hlip (a + x) a
      have h6' : |a - (a + x)| = x := by
        rw [show a - (a + x) = -x from by ring, abs_neg, abs_of_nonneg hx0.le]
      rwa [h6'] at h6
    have h7 : ‖deriv γ a‖ ≤ M := hspdM a
    have h8 : ‖deriv γ a‖ * ‖deriv γ (a + x) - deriv γ a‖ ≤ M * (C * x) := by
      have h9 := mul_le_mul_of_nonneg (a := ‖deriv γ a‖) (b := M)
        (c := ‖deriv γ (a + x) - deriv γ a‖) (d := C * x) h7 h5 (norm_nonneg _) (by positivity)
      linarith [h9]
    rw [hsplit, h1]
    linarith [hup, hlo, h8]
  have herrb : inner ℝ e (deriv γ (a + x)) ≥ -(M * (C * x ^ 2)) := by
    have hup := real_inner_le_norm e (deriv γ (a + x))
    have hlo := neg_inner_le_norm e (deriv γ (a + x))
    have h5 : ‖e‖ ≤ C * x ^ 2 := by rw [he]; exact herr
    have h7 : ‖deriv γ (a + x)‖ ≤ M := hspdM (a + x)
    have h8 : ‖e‖ * ‖deriv γ (a + x)‖ ≤ M * (C * x ^ 2) := by
      have h9 := mul_le_mul_of_nonneg (a := ‖e‖) (b := C * x ^ 2)
        (c := ‖deriv γ (a + x)‖) (d := M) h5 h7 (norm_nonneg _) (by positivity)
      linarith [h9]
    linarith [hup, hlo, h8]
  have hmain : inner ℝ (γ (a + x) - γ a) (deriv γ (a + x))
      = x * inner ℝ (deriv γ a) (deriv γ (a + x)) + inner ℝ e (deriv γ (a + x)) := by
    rw [hdecomp, inner_add_left, inner_smul_left]
    simp
  rw [hmain]
  have hxa : 2 * M * C * x ≤ 2 * M * C * δ :=
    mul_le_mul_of_nonneg_left hxδ (by positivity)
  have hkey : 2 * M * C * x < m ^ 2 := lt_of_le_of_lt hxa hδ
  nlinarith [hbound, herrb, hx0, hkey]

/-- **The backward derivative is negative.** -/
lemma inner_radial_bwd_neg {γ : ℝ → Space} (hγ : Differentiable ℝ γ)
    {m M C δ : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 ≤ C) (hδ : M * C * δ < m ^ 2)
    (hspd : ∀ t : ℝ, m ≤ ‖deriv γ t‖) (hspdM : ∀ t : ℝ, ‖deriv γ t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖deriv γ t - deriv γ t'‖ ≤ C * |t' - t|)
    {a x : ℝ} (hx0 : 0 < x) (hxδ : x ≤ δ) :
    inner ℝ (γ (a - x) - γ a) (deriv γ (a - x)) < 0 := by
  obtain ⟨herr, -, -⟩ :=
    thinCorner_shift_sub_le (r := γ) hγ hC hlip (b := a - x) (σ := x) hx0.le
  set e : Space := γ (a - x + x) - γ (a - x) - x • deriv γ (a - x) with he
  have heq : γ (a - x) - γ a = -(x • deriv γ (a - x) + e) := by
    have h1 : a - x + x = a := by ring
    rw [he, h1]
    abel
  have herrb : inner ℝ e (deriv γ (a - x)) ≥ -(M * (C * x ^ 2)) := by
    have hup := real_inner_le_norm e (deriv γ (a - x))
    have hlo := neg_inner_le_norm e (deriv γ (a - x))
    have h5 : ‖e‖ ≤ C * x ^ 2 := by rw [he]; exact herr
    have h7 : ‖deriv γ (a - x)‖ ≤ M := hspdM (a - x)
    have h8 : ‖e‖ * ‖deriv γ (a - x)‖ ≤ M * (C * x ^ 2) := by
      have h9 := mul_le_mul_of_nonneg (a := ‖e‖) (b := C * x ^ 2)
        (c := ‖deriv γ (a - x)‖) (d := M) h5 h7 (norm_nonneg _) (by positivity)
      linarith [h9]
    linarith [hup, hlo, h8]
  have hmain : inner ℝ (γ (a - x) - γ a) (deriv γ (a - x))
      = -(x * inner ℝ (deriv γ (a - x)) (deriv γ (a - x))
          + inner ℝ e (deriv γ (a - x))) := by
    rw [heq, inner_neg_left, inner_add_left, inner_smul_left]
    simp
  have hnorm : m ^ 2 ≤ ‖deriv γ (a - x)‖ ^ 2 := by
    have h := hspd (a - x)
    nlinarith [h, hm]
  have hxle : M * C * x ≤ M * C * δ :=
    mul_le_mul_of_nonneg_left hxδ (by positivity)
  have hkey : M * C * x < m ^ 2 := lt_of_le_of_lt hxle hδ
  rw [hmain, real_inner_self_eq_norm_sq]
  nlinarith [herrb, hnorm, hx0, hkey]

/-! ## 3. The monotonicity from the speed bounds -/

/-- The smallness of the window chosen below. -/
lemma two_mul_delta_lt {m M C : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 ≤ C) :
    2 * M * C * min 1 (m ^ 2 / (4 * M * C + 1)) < m ^ 2 ∧
      M * C * min 1 (m ^ 2 / (4 * M * C + 1)) < m ^ 2 := by
  have hMC : 0 ≤ M * C := by positivity
  have hden : 0 < 4 * M * C + 1 := by positivity
  have hle : min 1 (m ^ 2 / (4 * M * C + 1)) ≤ m ^ 2 / (4 * M * C + 1) := min_le_right _ _
  have h1 : (2 * M * C) * (m ^ 2 / (4 * M * C + 1)) ≤ (1 / 2) * m ^ 2 := by
    rw [← mul_div_assoc]
    rw [div_le_iff₀ hden]
    nlinarith [hm, hMC]
  have h2 : 2 * M * C * min 1 (m ^ 2 / (4 * M * C + 1))
      ≤ 2 * M * C * (m ^ 2 / (4 * M * C + 1)) :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  have h3 : (M * C) * (m ^ 2 / (4 * M * C + 1)) ≤ (1 / 4) * m ^ 2 := by
    rw [← mul_div_assoc]
    rw [div_le_iff₀ hden]
    nlinarith [hm, hMC]
  have h4 : M * C * min 1 (m ^ 2 / (4 * M * C + 1))
      ≤ M * C * (m ^ 2 / (4 * M * C + 1)) := mul_le_mul_of_nonneg_left hle hMC
  constructor <;> nlinarith [h1, h2, h3, h4, hm]

/-- **Local radial monotonicity at an explicit window.** -/
theorem radial_mono_of_delta {γ : ℝ → Space} (hγ : Differentiable ℝ γ)
    {m M C δ : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 ≤ C)
    (hsmall : 2 * M * C * δ < m ^ 2) (hsmall₂ : M * C * δ < m ^ 2)
    (hspd : ∀ t : ℝ, m ≤ ‖deriv γ t‖) (hspdM : ∀ t : ℝ, ‖deriv γ t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖deriv γ t - deriv γ t'‖ ≤ C * |t' - t|) :
    (∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖γ (a + s) - γ a‖ < ‖γ (a + s') - γ a‖) ∧
    (∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖γ (a - s) - γ a‖ < ‖γ (a - s') - γ a‖) := by
  constructor
  · intro a s s' hs0 hss hsd
    have hcont : ContinuousOn (fun t : ℝ => ‖γ (a + t) - γ a‖ ^ 2) (Set.Icc 0 δ) := by
      have h1 : Continuous (fun t : ℝ => ‖γ (a + t) - γ a‖ ^ 2) :=
        (((hγ.continuous.comp (continuous_const.add continuous_id)).sub
          continuous_const).norm).pow 2
      exact h1.continuousOn
    have hderiv : ∀ x ∈ interior (Set.Icc 0 δ), 0 < deriv (fun t : ℝ => ‖γ (a + t) - γ a‖ ^ 2) x := by
      intro x hx
      rw [interior_Icc] at hx
      rw [deriv_radial_fwd hγ a x]
      have hsign := inner_radial_fwd_pos (a := a) hγ hm hM hC hsmall hspd hspdM hlip hx.1 hx.2.le
      linarith
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont hderiv
    have hs : s ∈ Set.Icc (0 : ℝ) δ := ⟨hs0, by linarith⟩
    have hs' : s' ∈ Set.Icc (0 : ℝ) δ := ⟨by linarith, hsd⟩
    have hlt := hmono hs hs' hss
    have h1 := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h1
  · intro a s s' hs0 hss hsd
    have hcont : ContinuousOn (fun t : ℝ => ‖γ (a - t) - γ a‖ ^ 2) (Set.Icc 0 δ) := by
      have h1 : Continuous (fun t : ℝ => ‖γ (a - t) - γ a‖ ^ 2) :=
        (((hγ.continuous.comp (continuous_const.sub continuous_id)).sub
          continuous_const).norm).pow 2
      exact h1.continuousOn
    have hderiv : ∀ x ∈ interior (Set.Icc 0 δ), 0 < deriv (fun t : ℝ => ‖γ (a - t) - γ a‖ ^ 2) x := by
      intro x hx
      rw [interior_Icc] at hx
      rw [deriv_radial_bwd hγ a x]
      have hsign := inner_radial_bwd_neg (a := a) hγ hm hM hC hsmall₂ hspd hspdM hlip hx.1 hx.2.le
      rw [inner_neg_right]
      linarith
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont hderiv
    have hs : s ∈ Set.Icc (0 : ℝ) δ := ⟨hs0, by linarith⟩
    have hs' : s' ∈ Set.Icc (0 : ℝ) δ := ⟨by linarith, hsd⟩
    have hlt := hmono hs hs' hss
    have h1 := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h1

/-- **Local radial monotonicity from the speed bounds.** -/
theorem radial_mono_of_bounds {γ : ℝ → Space} (hγ : Differentiable ℝ γ)
    {m M C : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 ≤ C)
    (hspd : ∀ t : ℝ, m ≤ ‖deriv γ t‖) (hspdM : ∀ t : ℝ, ‖deriv γ t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖deriv γ t - deriv γ t'‖ ≤ C * |t' - t|) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖γ (a + s) - γ a‖ < ‖γ (a + s') - γ a‖) ∧
      (∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖γ (a - s) - γ a‖ < ‖γ (a - s') - γ a‖) := by
  obtain ⟨h1, h2⟩ := two_mul_delta_lt hm hM hC
  refine ⟨min 1 (m ^ 2 / (4 * M * C + 1)),
    lt_min one_pos (by positivity), ?_, ?_⟩
  · exact (radial_mono_of_delta hγ hm hM hC h1 h2 hspd hspdM hlip).1
  · exact (radial_mono_of_delta hγ hm hM hC h1 h2 hspd hspdM hlip).2

/-! ## 4. Auxiliary: the second derivative of an analytic knot, and the Lipschitz transfer -/

/-- The velocity of an analytic knot is differentiable. -/
lemma differentiable_deriv_of_analytic {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Differentiable ℝ (deriv r) := by
  have hcinf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
  have hderiv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) :=
    ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hcinf).2
  exact hderiv.differentiable (by simp)

/-- **The Lipschitz transfer for the velocity.**  If `r'` is analytic, its second derivative is
`ε`-close to that of `r`, and the velocity of `r` is `C`-Lipschitz, then the velocity of `r'` is
`(C + ε)`-Lipschitz. -/
lemma deriv_lipschitz_of_c2close {r r' : ℝ → Space} (hr : IsSmoothKnot r) (hr' : IsSmoothKnot r')
    {ε C : ℝ} (_hε : 0 ≤ ε) (hC : ∀ t t' : ℝ, ‖deriv r t - deriv r t'‖ ≤ C * |t' - t|)
    (h : ∀ t : ℝ, ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε) :
    ∀ t t' : ℝ, ‖deriv r' t - deriv r' t'‖ ≤ (C + ε) * |t' - t| := by
  intro t t'
  have hgdiff : ∀ s : ℝ, DifferentiableAt ℝ (fun u : ℝ => deriv r' u - deriv r u) s :=
    fun s => ((differentiable_deriv_of_analytic hr' s).hasDerivAt.sub
      (differentiable_deriv_of_analytic hr s).hasDerivAt).differentiableAt
  have hgbd : ∀ s : ℝ, ‖deriv (fun u : ℝ => deriv r' u - deriv r u) s‖ ≤ ε := by
    intro s
    have h1 : deriv (fun u : ℝ => deriv r' u - deriv r u) s
        = deriv (deriv r') s - deriv (deriv r) s := by
      exact deriv_sub (x := s) (differentiable_deriv_of_analytic hr' s)
        (differentiable_deriv_of_analytic hr s)
    rw [h1]
    exact (h s).le
  have hkey : ‖(deriv r' t - deriv r t) - (deriv r' t' - deriv r t')‖ ≤ ε * |t' - t| := by
    have hmm := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun u : ℝ => deriv r' u - deriv r u) (s := Set.univ) (x := t) (y := t') (C := ε)
      (fun s _ => hgdiff s) (fun s _ => hgbd s) convex_univ (Set.mem_univ t) (Set.mem_univ t')
    rw [norm_sub_rev] at hmm
    simpa using hmm
  have hsplit : deriv r' t - deriv r' t'
      = (deriv r t - deriv r t') + ((deriv r' t - deriv r t) - (deriv r' t' - deriv r t')) := by
    abel
  rw [hsplit]
  have h2 : ‖deriv r t - deriv r t'‖ ≤ C * |t' - t| := hC t t'
  have h4 : ‖(deriv r' t - deriv r t) - (deriv r' t' - deriv r t')‖ ≤ ε * |t' - t| := hkey
  have h5 : ‖(deriv r t - deriv r t')
      + ((deriv r' t - deriv r t) - (deriv r' t' - deriv r t'))‖
      ≤ C * |t' - t| + ε * |t' - t| := by
    have h6 := norm_add_le (deriv r t - deriv r t')
      ((deriv r' t - deriv r t) - (deriv r' t' - deriv r t'))
    linarith [h6, h2, h4]
  calc ‖(deriv r t - deriv r t')
        + ((deriv r' t - deriv r t) - (deriv r' t' - deriv r t'))‖
      ≤ C * |t' - t| + ε * |t' - t| := h5
    _ = (C + ε) * |t' - t| := by ring

/-! ## 4. The `C²`-ball form -/

/-- **Local radial monotonicity, uniformly over a `C²`-neighbourhood of the reference knot.** -/
theorem exists_local_radial_mono {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε) →
        (∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖r' (a + s) - r' a‖ < ‖r' (a + s') - r' a‖) ∧
        (∀ a s s' : ℝ, 0 ≤ s → s < s' → s' ≤ δ → ‖r' (a - s) - r' a‖ < ‖r' (a - s') - r' a‖) := by
  obtain ⟨m, M, C, hm, hM, hC, hspd, hspdM, hlip⟩ := exists_knot_c2_bounds hr
  obtain ⟨δr, hδr, hr₁, hr₂⟩ :=
    radial_mono_of_bounds (hr.smooth.differentiable (by simp)) hm hM hC.le hspd hspdM hlip
  -- the ball constants
  set m' : ℝ := m / 2 with hm'def
  set M' : ℝ := M + 1 with hM'def
  set C' : ℝ := C + 1 with hC'def
  have hm' : 0 < m' := by rw [hm'def]; linarith
  have hM' : 0 < M' := by rw [hM'def]; linarith
  have hC' : 0 ≤ C' := by rw [hC'def]; linarith
  obtain ⟨hsm₁, hsm₂⟩ := two_mul_delta_lt hm' hM' hC'
  refine ⟨min (m / 2) 1, min δr (min 1 (m' ^ 2 / (4 * M' * C' + 1))),
    lt_min (by linarith) one_pos, lt_min hδr (lt_min one_pos (by positivity)), ?_⟩
  intro r' hr' hclose
  have hεm : min (m / 2) 1 ≤ m / 2 := min_le_left _ _
  have hε1 : min (m / 2) 1 ≤ 1 := min_le_right _ _
  have hδδr : min δr (min 1 (m' ^ 2 / (4 * M' * C' + 1))) ≤ δr := min_le_left _ _
  have hδδb : min δr (min 1 (m' ^ 2 / (4 * M' * C' + 1)))
      ≤ min 1 (m' ^ 2 / (4 * M' * C' + 1)) := min_le_right _ _
  have hvel : ∀ t : ℝ, ‖velocity r' t - velocity r t‖ < min (m / 2) 1 := fun t => (hclose t).2.1
  have hacc : ∀ t : ℝ, ‖deriv (deriv r') t - deriv (deriv r) t‖ < min (m / 2) 1 :=
    fun t => (hclose t).2.2
  have hdiff : Differentiable ℝ r' := hr'.smooth.differentiable (by simp)
  -- the four hypotheses of `radial_mono_of_delta`, at the ball constants
  have hs1 : ∀ t : ℝ, m' ≤ ‖deriv r' t‖ := by
    intro t
    have h1 : m ≤ ‖deriv r t‖ := hspd t
    have h2 : ‖deriv r' t - deriv r t‖ < min (m / 2) 1 := hvel t
    have h4 : ‖deriv r t‖ ≤ ‖deriv r' t‖ + ‖deriv r' t - deriv r t‖ := by
      have h5 := norm_add_le (deriv r' t) (deriv r t - deriv r' t)
      have h6 : deriv r' t + (deriv r t - deriv r' t) = deriv r t := by abel
      rw [h6, norm_sub_rev] at h5
      exact h5
    rw [hm'def]
    linarith [hεm, h1, h2, h4]
  have hs2 : ∀ t : ℝ, ‖deriv r' t‖ ≤ M' := by
    intro t
    have h1 : ‖deriv r t‖ ≤ M := hspdM t
    have h2 : ‖deriv r' t - deriv r t‖ < min (m / 2) 1 := hvel t
    have h3 : ‖deriv r' t‖ ≤ ‖deriv r t‖ + ‖deriv r' t - deriv r t‖ := by
      have h5 := norm_add_le (deriv r t) (deriv r' t - deriv r t)
      have h6 : deriv r t + (deriv r' t - deriv r t) = deriv r' t := by abel
      rw [h6] at h5
      exact h5
    rw [hM'def]
    linarith [hε1, h1, h2, h3]
  have hs3 : ∀ t t' : ℝ, ‖deriv r' t - deriv r' t'‖ ≤ C' * |t' - t| := by
    have hbase : ∀ t t' : ℝ, ‖deriv r' t - deriv r' t'‖ ≤ (C + min (m / 2) 1) * |t' - t| :=
      deriv_lipschitz_of_c2close hr hr' (le_of_lt (lt_min (by linarith) one_pos)) hlip hacc
    intro t t'
    have h2 := hbase t t'
    have h3 : C + min (m / 2) 1 ≤ C' := by rw [hC'def]; linarith [hε1]
    have h4 : 0 ≤ |t' - t| := abs_nonneg _
    calc ‖deriv r' t - deriv r' t'‖ ≤ (C + min (m / 2) 1) * |t' - t| := h2
      _ ≤ C' * |t' - t| := mul_le_mul_of_nonneg_right h3 h4
  obtain ⟨hb₁, hb₂⟩ := radial_mono_of_delta hdiff hm' hM' hC' hsm₁ hsm₂ hs1 hs2 hs3
  refine ⟨fun a s s' hs0 hss hsd => hb₁ a s s' hs0 hss (le_trans hsd hδδb),
    fun a s s' hs0 hss hsd => hb₂ a s s' hs0 hss (le_trans hsd hδδb)⟩

end Work.Drive
