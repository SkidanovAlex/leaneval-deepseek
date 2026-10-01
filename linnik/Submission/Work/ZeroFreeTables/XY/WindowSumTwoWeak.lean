import Mathlib

namespace Work.ZeroFreeTables.XY

open scoped Classical BigOperators

/-- **Two-term window bound, weak form.**  If the only divisor-nonzero points `u` of `Λ(·,χ)` in
the window `‖1 + i·Im s - u‖ ≤ δ` with `Re u > Re s` are `ρ` and `ρ'`, then the (multiplicity
weighted) sum of the two window terms at `ρ` and `ρ'` is at most the full window sum over the
divisor of `Λ(·,χ)`.  Every other window point has `Re u ≤ Re s`, hence a non-negative kernel term
by Condition 2 (`hF`), while a point outside the window contributes the value `0`; the two retained
points are therefore the only ones that can pull the sum down. -/
theorem WindowSumTwoWeak (x₀ L : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {f : ℝ → ℝ} {s ρ ρ' : ℂ} {δ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0)
    (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ' ≠ 0)
    (hne : ρ ≠ ρ')
    (hρ : s.re < ρ.re) (hρ' : s.re < ρ'.re)
    (hzw : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → s.re < u.re → u = ρ ∨ u = ρ') :
    (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
          (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      else 0)
      + (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
          (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
        else 0)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0) := by
  classical
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) u with hDdef
  set Fv : ℂ → ℝ := fun u =>
      (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re with hFvdef
  have hDval : ∀ u : ℂ, D u = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) u := fun u => rfl
  have hFval : ∀ u : ℂ, Fv u =
      (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re :=
    fun u => rfl
  set G : ℂ → ℝ := fun u => ((D u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then Fv u else 0) with hGdef
  have hGval : ∀ u : ℂ, G u = ((D u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then Fv u else 0) := fun u => rfl
  -- the divisor of an entire completed `L`-function is non-negative on the ball
  have hDnn : ∀ u : ℂ, (0:ℝ) ≤ ((D u : ℤ) : ℝ) := by
    intro u
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    have hz := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
    rw [hDval u]
    exact_mod_cast hz
  -- every *other* window point lies to the left of `s`
  have hzwnn : ∀ u : ℂ, D u ≠ 0 → ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ →
      u ≠ ρ → u ≠ ρ' → u.re ≤ s.re := by
    intro u hdu hw hu hu'
    by_contra hle
    have hlt : s.re < u.re := lt_of_not_ge hle
    rcases hzw u (by rw [← hDval u]; exact hdu) hw hlt with h | h
    · exact hu h
    · exact hu' h
  have hGnn : ∀ u : ℂ, u ≠ ρ → u ≠ ρ' → 0 ≤ G u := by
    intro u hu hu'
    by_cases hDu : D u = 0
    · rw [hGval u, hDu]; simp
    · by_cases hc : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [hGval u, hFval u, if_pos hc]
        have hre : u.re ≤ s.re := hzwnn u hDu hc hu hu'
        have hznn : 0 ≤ (((s - u) * L : ℂ)).re := by
          rw [Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          have : 0 ≤ (s - u).re := by rw [Complex.sub_re]; linarith
          exact mul_nonneg this hL
        exact mul_nonneg (hDnn u) (hF ((s - u) * L) hznn)
      · rw [hGval u, if_neg hc]; simp
  have hDfin : (Function.support (fun u : ℂ => D u)).Finite := by
    have hmer : MeromorphicOn (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
      fun z _ => ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z).meromorphicAt
    have h := MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall (0:ℂ) (|s.im| + 2))
      (V := Metric.closedBall (0:ℂ) (|s.im| + 2))
      hmer (isCompact_closedBall 0 (|s.im| + 2)) (subset_refl _)
    simpa [hDdef] using h
  have hGfin : Function.HasFiniteSupport G := hDfin.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [hGval u]; simp [h0]))
  -- split off the two retained points: `H₂ = G` away from `ρ, ρ'`, and `0` at them
  set H₂ : ℂ → ℝ := fun u => G u -
      ((if u = ρ then G ρ else 0) + (if u = ρ' then G ρ' else 0)) with hH₂def
  have hH₂nn : ∀ u : ℂ, 0 ≤ H₂ u := by
    intro u
    by_cases h1 : u = ρ
    · subst h1
      rw [hH₂def]
      simp only [if_true, if_neg hne, add_zero, sub_self, le_refl]
    · by_cases h2 : u = ρ'
      · subst h2
        rw [hH₂def]
        simp only [if_true, if_neg (Ne.symm hne), zero_add, sub_self, le_refl]
      · rw [hH₂def]
        simp only [if_neg h1, if_neg h2, add_zero, sub_zero]
        exact hGnn u h1 h2
  have hind1 : Function.HasFiniteSupport (fun u : ℂ => if u = ρ then G ρ else 0) := by
    refine (Set.finite_singleton ρ).subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hu (by simp [h])
  have hind2 : Function.HasFiniteSupport (fun u : ℂ => if u = ρ' then G ρ' else 0) := by
    refine (Set.finite_singleton ρ').subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hu (by simp [h])
  have hind : Function.HasFiniteSupport (fun u : ℂ =>
      (if u = ρ then G ρ else 0) + (if u = ρ' then G ρ' else 0)) := hind1.add hind2
  have hH₂fin : Function.HasFiniteSupport H₂ := hGfin.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    refine hu ?_
    by_cases h1 : u = ρ
    · subst h1
      rw [hH₂def]
      simp only [if_true, if_neg hne, add_zero, sub_self]
    · by_cases h2 : u = ρ'
      · subst h2
        rw [hH₂def]
        simp only [if_true, if_neg (Ne.symm hne), zero_add, sub_self]
      · rw [hH₂def]
        simp only [if_neg h1, if_neg h2, add_zero, sub_zero, h0])
  have hsplit : (∑ᶠ u : ℂ, H₂ u) = (∑ᶠ u : ℂ, G u) - G ρ - G ρ' := by
    rw [hH₂def]
    rw [finsum_sub_distrib hGfin hind]
    rw [finsum_add_distrib hind1 hind2]
    rw [finsum_eq_single (fun u : ℂ => if u = ρ then G ρ else 0) ρ
          (by intro x hx; simp [hx])]
    rw [finsum_eq_single (fun u : ℂ => if u = ρ' then G ρ' else 0) ρ'
          (by intro x hx; simp [hx])]
    simp only [if_true]
    ring
  have hkey : G ρ + G ρ' ≤ ∑ᶠ u : ℂ, G u := by
    have h1 := finsum_nonneg hH₂nn
    linarith only [h1, hsplit]
  have hW : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0)) = ∑ᶠ u : ℂ, G u := by
    apply finsum_congr
    intro u
    rw [hGval u, hDval u, hFval u]
  have hρeq : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ then
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
          (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      else 0) = G ρ := by
    rw [hGval ρ, hDval ρ, hFval ρ]
    by_cases h : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ <;> simp [h]
  have hρ'eq : (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ then
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (|s.im| + 2))) ρ' : ℤ) : ℝ) *
          (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ') * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re
      else 0) = G ρ' := by
    rw [hGval ρ', hDval ρ', hFval ρ']
    by_cases h : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ'‖ ≤ δ <;> simp [h]
  rw [hW, hρeq, hρ'eq]
  exact hkey

end Work.ZeroFreeTables.XY
