import Mathlib
import Submission.Work.Drive.chordSweepSmooth

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# One-sided monotonicity of the tangent functional at a non-degenerate point

At a point `θb` where the curve `r` is regular (`velocity r θb ≠ 0`) and not -- locally -- a
straight line (some higher iterated derivative is not parallel to the velocity), the curve crosses
the tangent hyperplane at `θb` transversally and monotonically: there is a normal vector `n`
(perpendicular to the velocity) such that, on a left neighbourhood of `θb`, the function
`θ ↦ ⟪n, r θ⟫` is strictly increasing, and `⟪n, r θb - r θ⟫ > 0`.

The proof is a one-variable Taylor argument.  Let `K ≥ 2` be the *first* order at which the
`K`-th iterated derivative of `r` at `θb` is not parallel to the velocity.  Choosing
`n = (-1)^(K-1) · (component of `r^{(K)}(θb)` orthogonal to the velocity)` gives
`⟪n, r^{(j)}(θb)⟫ = 0` for `1 ≤ j < K` together with `(-1)^(K-1) ⟪n, r^{(K)}(θb)⟫ > 0`.  Hence the
scalar function `U θ = ⟪n, r'(θ)⟫` has a zero of order exactly `K-1` at `θb` with the sign making
it positive on the left, and Taylor's theorem with Lagrange remainder produces the neighbourhood. -/

/-- Iterated derivatives commute with the composition with a continuous linear functional. -/
lemma iteratedDeriv_comp_clm {f : ℝ → Space} (hf : ContDiff ℝ ⊤ f) (L : Space →L[ℝ] ℝ)
    (m : ℕ) (x : ℝ) : iteratedDeriv m (L ∘ f) x = L (iteratedDeriv m f x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_left L hf.contDiffAt (le_top : (m : WithTop ℕ∞) ≤ ⊤)]
  rfl

/-- Given a non-zero vector `w` and a vector `a` not parallel to `w`, there is a non-zero `n`
orthogonal to `w` with a prescribed sign of `⟪n, a⟫` (the sign carried by the parity factor
`(-1)^m`).  Explicitly `n = (-1)^m` times the orthogonal projection of `a` onto `w^⊥`. -/
lemma exists_perp_signed {w a : Space} (hw : w ≠ 0) (m : ℕ)
    (ha : a ∉ Submodule.span ℝ {w}) :
    ∃ n : Space, n ≠ 0 ∧ inner ℝ n w = 0 ∧ 0 < (-1:ℝ)^m * inner ℝ n a := by
  have hw2 : ‖w‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  let b : Space := a - (inner ℝ w a / ‖w‖^2) • w
  have hbperp : inner ℝ w b = 0 := by
    simp only [b, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    rw [div_mul_cancel₀ (inner ℝ w a) hw2, sub_self]
  have hbperp' : inner ℝ b w = 0 := by rw [real_inner_comm]; exact hbperp
  have hbne : b ≠ 0 := by
    intro hb0
    apply ha
    rw [Submodule.mem_span_singleton]
    refine ⟨inner ℝ w a / ‖w‖^2, ?_⟩
    have h1 : a = (inner ℝ w a / ‖w‖^2) • w := by
      have h := hb0
      simp only [b] at h
      rw [sub_eq_zero] at h
      exact h
    exact h1.symm
  refine ⟨(-1:ℝ)^m • b, ?_, ?_, ?_⟩
  · exact smul_ne_zero (pow_ne_zero _ (by norm_num)) hbne
  · rw [real_inner_smul_left, hbperp', mul_zero]
  · have h1 : a - b = (inner ℝ w a / ‖w‖^2) • w := by
      simp only [b]; rw [sub_sub_cancel]
    have hba : inner ℝ b a = ‖b‖^2 := by
      have h2 : inner ℝ b a - inner ℝ b b = inner ℝ b (a - b) := (inner_sub_right b a b).symm
      rw [real_inner_self_eq_norm_sq] at h2
      have h3 : inner ℝ b (a - b) = 0 := by rw [h1, inner_smul_right, hbperp', mul_zero]
      linarith [h2, h3]
    have hna : inner ℝ ((-1:ℝ)^m • b) a = (-1:ℝ)^m * ‖b‖^2 := by
      rw [real_inner_smul_left, hba]
    rw [hna]
    have hs2 : (-1:ℝ)^m * (-1:ℝ)^m = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨m, by ring⟩
    have : (-1:ℝ)^m * ((-1:ℝ)^m * ‖b‖^2) = ((-1:ℝ)^m * (-1:ℝ)^m) * ‖b‖^2 := by ring
    rw [this, hs2, one_mul]
    positivity

/-- **Taylor's theorem with a vanishing tail and a definite one-sided sign.**

If `f : ℝ → ℝ` is smooth, `f^{(j)}(x₀) = 0` for `j < n+1` and `f^{(n+1)}(x₀) ≠ 0`, then on a left
neighbourhood of `x₀` the function `f` has the sign of `f^{(n+1)}(x₀) · (-1)^{n+1}`. -/
lemma taylor_sign_left {f : ℝ → ℝ} {x₀ : ℝ} {n : ℕ}
    (hf : ContDiff ℝ ⊤ f)
    (hzero : ∀ j : ℕ, j < n + 1 → iteratedDeriv j f x₀ = 0)
    (hne : iteratedDeriv (n + 1) f x₀ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, x₀ - ε < x → x < x₀ →
      0 < f x * (iteratedDeriv (n + 1) f x₀ * (-1 : ℝ) ^ (n + 1)) := by
  set c : ℝ := iteratedDeriv (n + 1) f x₀ with hcdef
  have hcne : c ≠ 0 := by rw [hcdef]; exact hne
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  have hcont : ContinuousAt (iteratedDeriv (n + 1) f) x₀ :=
    (hf.continuous_iteratedDeriv (n + 1) le_top).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont ‖c‖ hcpos
  have hδ' : ∀ ξ : ℝ, dist ξ x₀ < δ → 0 < iteratedDeriv (n + 1) f ξ * c := by
    intro ξ hξ
    have hlt : |iteratedDeriv (n + 1) f ξ - c| < |c| := by
      have h := hδ hξ
      rw [Real.dist_eq, ← hcdef, Real.norm_eq_abs] at h
      exact h
    have hh := abs_lt.mp hlt
    rcases le_total 0 c with hcge | hcle
    · have hce : |c| = c := abs_of_nonneg hcge
      have hA : 0 < iteratedDeriv (n + 1) f ξ := by linarith [hh.1, hce]
      exact mul_pos hA (lt_of_le_of_ne hcge (Ne.symm hcne))
    · have hclt : c < 0 := lt_of_le_of_ne hcle hcne
      have hce : |c| = -c := abs_of_neg hclt
      have hA : iteratedDeriv (n + 1) f ξ < 0 := by linarith [hh.2, hce]
      exact mul_pos_of_neg_of_neg hA hclt
  refine ⟨min δ 1, lt_min hδpos one_pos, ?_⟩
  intro x hxlo hxhi
  have hxne : x₀ ≠ x := ne_of_gt hxhi
  have hfOn : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) f (Set.uIcc x₀ x) :=
    (hf.of_le (le_top : ((n : WithTop ℕ∞) + 1) ≤ ⊤)).contDiffOn
  obtain ⟨x', hx'mem, hx'eq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := x) (x₀ := x₀) (n := n) hxne hfOn
  have hx'int : x < x' ∧ x' < x₀ := by
    simp only [Set.uIoo, min_eq_right hxhi.le, max_eq_left hxhi.le] at hx'mem
    exact hx'mem
  have htaylor : taylorWithinEval f n (Set.uIcc x₀ x) x₀ x = f x₀ := by
    rw [taylor_within_apply]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxne)
        (hf.contDiffAt.of_le (le_top : (k : WithTop ℕ∞) ≤ ⊤)) Set.left_mem_uIcc, hzero k hklt]
      simp
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hfx₀ : f x₀ = 0 := by
    have := hzero 0 (Nat.succ_pos n); simpa using this
  have hfx : f x = iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    have h := hx'eq
    rw [htaylor, hfx₀, sub_zero] at h
    exact h
  have hdist : dist x' x₀ < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith [hx'int.2] : x' - x₀ < 0)]
    have hεδ : min δ 1 ≤ δ := min_le_left _ _
    linarith [hx'int.2, hxlo, hεδ]
  have hsign : 0 < iteratedDeriv (n + 1) f x' * c := hδ' x' hdist
  have hxpos : 0 < (x₀ - x) ^ (n + 1) := pow_pos (by linarith) _
  have hfact : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hpow : (x - x₀) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = (x₀ - x) ^ (n + 1) := by
    rw [← mul_pow]; ring_nf
  have hnum : iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) * (c * (-1 : ℝ) ^ (n + 1))
      = (iteratedDeriv (n + 1) f x' * c) * (x₀ - x) ^ (n + 1) := by
    rw [← hpow]; ring
  have hmain : f x * (iteratedDeriv (n + 1) f x₀ * (-1 : ℝ) ^ (n + 1))
      = (iteratedDeriv (n + 1) f x' * c) * (x₀ - x) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
    rw [hfx, ← hcdef, div_mul_eq_mul_div, hnum]
  rw [hmain]
  exact div_pos (mul_pos hsign hxpos) hfact

/-- Restatement of `taylor_sign_left` indexed by the order `m ≥ 1` of the first non-vanishing
derivative. -/
lemma taylor_sign_left' {f : ℝ → ℝ} {x₀ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : ContDiff ℝ ⊤ f)
    (hzero : ∀ j : ℕ, j < m → iteratedDeriv j f x₀ = 0)
    (hne : iteratedDeriv m f x₀ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, x₀ - ε < x → x < x₀ →
      0 < f x * (iteratedDeriv m f x₀ * (-1 : ℝ) ^ m) := by
  have hz : ∀ j : ℕ, j < (m - 1) + 1 → iteratedDeriv j f x₀ = 0 := by
    intro j hj; exact hzero j (by omega)
  have hn : iteratedDeriv ((m - 1) + 1) f x₀ ≠ 0 := by rwa [Nat.sub_add_cancel hm]
  obtain ⟨ε, hε, h⟩ := taylor_sign_left (f := f) (x₀ := x₀) (n := m - 1) hf hz hn
  refine ⟨ε, hε, fun x h1 h2 => ?_⟩
  have hh := h x h1 h2
  rwa [Nat.sub_add_cancel hm] at hh

theorem knot_tangent_monotone_oneSided {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : ContDiff ℝ ⊤ r) {θb : ℝ} (hreg : LeanEval.KnotTheory.Quadrisecant.velocity r θb ≠ 0)
    (hnd : ∃ k : ℕ, 2 ≤ k ∧ iteratedDeriv k r θb ∉ Submodule.span ℝ {LeanEval.KnotTheory.Quadrisecant.velocity r θb}) :
    ∃ n : LeanEval.KnotTheory.Quadrisecant.Space, n ≠ 0 ∧ inner ℝ n (LeanEval.KnotTheory.Quadrisecant.velocity r θb) = 0 ∧
      ∃ ε : ℝ, 0 < ε ∧
        (∀ θ : ℝ, θb - ε < θ → θ < θb → 0 < inner ℝ n (r θb - r θ)) ∧
        (∀ θ₁ θ₂ : ℝ, θb - ε < θ₁ → θ₁ ≤ θ₂ → θ₂ < θb →
          inner ℝ n (r θb - r θ₂) ≤ inner ℝ n (r θb - r θ₁)) := by
  classical
  set K : ℕ := Nat.find hnd with hKdef
  have hK2 : 2 ≤ K := (Nat.find_spec hnd).1
  have hKnot : iteratedDeriv K r θb ∉ Submodule.span ℝ {velocity r θb} := (Nat.find_spec hnd).2
  -- the normal vector with the right one-sided sign
  obtain ⟨n, hnne, hnperp, hsig⟩ := exists_perp_signed hreg (K - 1) hKnot
  -- the scalar function whose derivative is the velocity functional
  set U : ℝ → ℝ := fun θ => inner ℝ n (velocity r θ) with hUdef
  have hUfun : U = (innerSL ℝ n) ∘ (deriv r) := by funext θ; rfl
  have hU_smooth : ContDiff ℝ ⊤ U := by
    rw [hUfun]
    exact (ContinuousLinearMap.contDiff (innerSL ℝ n)).comp (by fun_prop)
  have hderiv_u : ∀ j : ℕ, iteratedDeriv j U θb = inner ℝ n (iteratedDeriv (j + 1) r θb) := by
    intro j
    rw [hUfun, iteratedDeriv_comp_clm (by fun_prop) (innerSL ℝ n) j θb]
    rw [show iteratedDeriv j (deriv r) θb = iteratedDeriv (j + 1) r θb from
      (congrFun (iteratedDeriv_succ' (n := j) (f := r)) θb).symm]
    rfl
  -- `U` has a zero of order exactly `K - 1` at `θb`
  have hu_zero : ∀ j : ℕ, j < K - 1 → iteratedDeriv j U θb = 0 := by
    intro j hj
    rw [hderiv_u j]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      simpa [iteratedDeriv_one, velocity] using hnperp
    · have hjk : j + 1 < K := by omega
      have hj2 : 2 ≤ j + 1 := by omega
      have hmem : iteratedDeriv (j + 1) r θb ∈ Submodule.span ℝ {velocity r θb} := by
        by_contra hc
        exact Nat.find_min hnd (m := j + 1) (by omega) ⟨hj2, hc⟩
      obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hmem
      rw [← hcc, inner_smul_right, hnperp, mul_zero]
  have hu_ne : iteratedDeriv (K - 1) U θb ≠ 0 := by
    rw [hderiv_u (K - 1), Nat.sub_add_cancel (by omega : 1 ≤ K)]
    intro h
    have h2 := hsig
    rw [h, mul_zero] at h2
    exact (lt_irrefl 0) h2
  -- one-sided positivity of `θ ↦ ⟪n, r'(θ)⟫`
  obtain ⟨ε, hε, hsignlem⟩ := taylor_sign_left' (f := U) (x₀ := θb) (m := K - 1)
    (by omega) hU_smooth hu_zero hu_ne
  have hu_pos : ∀ x : ℝ, θb - ε < x → x < θb → 0 < inner ℝ n (velocity r x) := by
    intro x h1 h2
    have h := hsignlem x h1 h2
    have hC : 0 < iteratedDeriv (K - 1) U θb * (-1 : ℝ) ^ (K - 1) := by
      rw [hderiv_u (K - 1), Nat.sub_add_cancel (by omega : 1 ≤ K), mul_comm]
      exact hsig
    exact pos_of_mul_pos_left h hC.le
  -- the derivative of `θ ↦ ⟪n, r θ⟫`
  have hderivA : ∀ x : ℝ, deriv (fun θ : ℝ => inner ℝ n (r θ)) x = inner ℝ n (velocity r x) := by
    intro x
    have hfun : (fun θ : ℝ => inner ℝ n (r θ)) = (innerSL ℝ n) ∘ r := by funext θ; rfl
    rw [hfun, ← iteratedDeriv_one, iteratedDeriv_comp_clm hr (innerSL ℝ n) 1 x,
      show iteratedDeriv 1 r x = deriv r x from congrFun (iteratedDeriv_one (f := r)) x]
    rfl
  have hmono : StrictMonoOn (fun θ : ℝ => inner ℝ n (r θ)) (Set.Icc (θb - ε) θb) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc (θb - ε) θb) ?_ ?_
    · exact (continuous_const.inner hr.continuous).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      rw [hderivA x]
      exact hu_pos x hx.1 hx.2
  refine ⟨n, hnne, hnperp, ε, hε, ?_, ?_⟩
  · intro θ h1 h2
    have hm : θ ∈ Set.Icc (θb - ε) θb := ⟨le_of_lt h1, le_of_lt h2⟩
    have hθb : θb ∈ Set.Icc (θb - ε) θb := ⟨by linarith, le_rfl⟩
    have hlt : inner ℝ n (r θ) < inner ℝ n (r θb) := hmono hm hθb h2
    rw [inner_sub_right]
    linarith
  · intro θ₁ θ₂ h1 hle h2
    have hm1 : θ₁ ∈ Set.Icc (θb - ε) θb := ⟨le_of_lt h1, by linarith⟩
    have hm2 : θ₂ ∈ Set.Icc (θb - ε) θb := ⟨by linarith, le_of_lt h2⟩
    have hle' : inner ℝ n (r θ₁) ≤ inner ℝ n (r θ₂) := hmono.monotoneOn hm1 hm2 hle
    rw [inner_sub_right, inner_sub_right]
    linarith

end Work.Drive
