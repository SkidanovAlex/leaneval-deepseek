import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilVP.scale_pigeonhole
import Submission.Work.WilVP.window_iso

namespace Work.WilVP

/-- A breakpoint-free window gives a good radius: from the ULPM data of the recentred family
`t ↦ F_c(p + σ t)` (hypothesis `hU`, as produced by `Work.WilVP.shift_ulpm_data`) and the
pigeonhole `Work.WilVP.scale_pigeonhole` on the (at most `N`) recentred breakpoints, one finds a
scale `t' ∈ [t/L, t]` whose window `[t'/(2N), 2N t']` is breakpoint-free; then
`Work.WilVP.window_iso` (with `g` the chosen value of the fibre and `D` its domain,
`s := t'`) gives that the ball of radius `t'/2` around `p + σ t'` lies in the domain and the
values stay within the factor `K₀ = N·2^Qb`, i.e. `IsoGood` for every value `y₀` at
`p + σ t'` (uniqueness of `y₀` is what makes the choice of `g` harmless).
`hdom` supplies the domain membership of the chosen scale, which `window_iso` needs at `s = t'`
(the caller derives it from "the piece is contained in the fibre where the value is nonzero"). -/
theorem window_rho_lower {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {K₀ : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y')
    {σ p : ℝ} (hσ : σ = 1 ∨ σ = -1) {c : Fin k → ℝ}
    {N : ℕ} (hN : 0 < N) {Qb : ℕ} {Qs : Finset ℚ} (hQb : ∀ q ∈ Qs, |(q : ℝ)| ≤ Qb)
    {B : Set (Fin (k + 2) → ℝ)}
    (hBcard : {t : ℝ | Fin.cons t (Fin.cons p c) ∈ B}.encard ≤ N)
    (hK : K₀ = (N : ℝ) * 2 ^ Qb)
    (hU : ∀ x₁ x₂ : ℝ, 0 < x₁ → 0 < x₂ →
      Work.WilC4.Route.SameSide N {t : ℝ | Fin.cons t (Fin.cons p c) ∈ B} x₁ x₂ →
      ((∃ y : ℝ, Fin.cons (p + σ * x₁) (Fin.cons y c) ∈ Y) ↔
        (∃ y : ℝ, Fin.cons (p + σ * x₂) (Fin.cons y c) ∈ Y)) ∧
      ∀ y₁ y₂ : ℝ, Fin.cons (p + σ * x₁) (Fin.cons y₁ c) ∈ Y →
        Fin.cons (p + σ * x₂) (Fin.cons y₂ c) ∈ Y →
        ∃ q ∈ Qs, |y₂| * x₁ ^ (q : ℝ) ≤ (N : ℝ) * (|y₁| * x₂ ^ (q : ℝ)) ∧
          |y₁| * x₂ ^ (q : ℝ) ≤ (N : ℝ) * (|y₂| * x₁ ^ (q : ℝ)))
    {L : ℝ} (hL : L = (4 * (N : ℝ) ^ 2 + 1) ^ N)
    {S : ℝ} (hS : 0 < S)
    (hdom : ∀ t : ℝ, 0 < t → t ≤ S / 2 → p + σ * t ∈ Work.WilVP.DomFib Y c) :
    ∀ t : ℝ, 0 < t → t ≤ S / 2 →
      ∃ t' : ℝ, t / L ≤ t' ∧ t' ≤ t ∧
        ∀ y₀ : ℝ, Fin.cons (p + σ * t') (Fin.cons y₀ c) ∈ Y →
          Work.WilVP.IsoGood Y K₀ c (p + σ * t') y₀ (t' / 2) := by
  intro t ht htS
  classical
  -- `σ² = 1`.
  have hσsq : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  -- The geometric factor and the breakpoint set.
  set lam : ℝ := 4 * (N : ℝ) ^ 2 + 1 with hlam
  have hlam_pos : 0 < lam := by rw [hlam]; positivity
  have hlam_ge1 : 1 ≤ lam := by rw [hlam]; nlinarith [sq_nonneg (N : ℝ)]
  set Bset : Set ℝ := {t : ℝ | Fin.cons t (Fin.cons p c) ∈ B} with hBset
  have hBcard' : Bset.encard ≤ N := by rw [hBset]; exact hBcard
  -- Pigeonhole over the (at most `N`) breakpoints.
  obtain ⟨j, hjmem, hjfree⟩ := scale_pigeonhole N hN Bset hBcard' ht
  have hjle : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hjmem)
  set t' : ℝ := t / lam ^ j with ht'def
  have ht'pos : 0 < t' := by rw [ht'def]; positivity
  have ht'le : t' ≤ t := by
    rw [ht'def, div_le_iff₀ (pow_pos hlam_pos j)]
    calc t = t * 1 := by ring
      _ ≤ t * lam ^ j :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hlam_ge1) (le_of_lt ht)
  have ht'low : t / L ≤ t' := by
    have hLN : lam ^ j ≤ lam ^ N := pow_le_pow_right₀ hlam_ge1 hjle
    rw [hL, ht'def]
    exact div_le_div_of_nonneg_left (le_of_lt ht) (pow_pos hlam_pos j) hLN
  -- The recentred domain and the value function of the fibre.
  set D : Set ℝ := {x : ℝ | ∃ y : ℝ, Fin.cons (p + σ * x) (Fin.cons y c) ∈ Y} with hD
  have hDmem : ∀ x : ℝ, x ∈ D ↔ ∃ y : ℝ, Fin.cons (p + σ * x) (Fin.cons y c) ∈ Y := by
    intro x; simp only [hD, Set.mem_ofPred_eq]
  set g : ℝ → ℝ := (fun x : ℝ => if h : x ∈ D then Classical.choose h else 0) with hg
  have hg_spec : ∀ x : ℝ, x ∈ D → Fin.cons (p + σ * x) (Fin.cons (g x) c) ∈ Y := by
    intro x hx
    have h1 : g x = Classical.choose hx := by
      rw [hg]; exact dite_eq_left hx
    rw [h1]
    exact Classical.choose_spec hx
  -- ULPM data in the recentred coordinates, phrased for `window_iso`.
  have hUw : ∀ x₁ x₂ : ℝ, 0 < x₁ → 0 < x₂ → Work.WilC4.Route.SameSide N Bset x₁ x₂ →
      (x₁ ∈ D ↔ x₂ ∈ D) ∧ (x₁ ∈ D → x₂ ∈ D → ∃ q ∈ Qs,
        |g x₂| * x₁ ^ (q : ℝ) ≤ (N : ℝ) * (|g x₁| * x₂ ^ (q : ℝ)) ∧
        |g x₁| * x₂ ^ (q : ℝ) ≤ (N : ℝ) * (|g x₂| * x₁ ^ (q : ℝ))) := by
    intro x₁ x₂ hx₁ hx₂ hss
    obtain ⟨hiff, hineq⟩ := hU x₁ x₂ hx₁ hx₂ hss
    refine ⟨?_, ?_⟩
    · rw [hDmem x₁, hDmem x₂]; exact hiff
    · intro hx₁D hx₂D
      exact hineq (g x₁) (g x₂) (hg_spec x₁ hx₁D) (hg_spec x₂ hx₂D)
  -- The window of `t'` is breakpoint-free, and `t'` is in the recentred domain.
  have hfree' : ∀ b ∈ Bset, ¬ (t' / (2 * N) ≤ b ∧ b ≤ 2 * N * t') := by
    intro b hb
    rw [ht'def, hlam]
    exact hjfree b hb
  have hsD : t' ∈ D := by
    rw [hDmem]
    exact hdom t' ht'pos (le_trans ht'le htS)
  have hwin := window_iso (D := D) (g := g) (N := N) (Qb := Qb) (Qs := Qs) (B := Bset)
    hN hQb hUw ht'pos hfree' hsD
  refine ⟨t', ht'low, ht'le, ?_⟩
  intro y₀ hy₀
  -- Uniqueness of the fibre value makes the choice of `g` harmless.
  have hy₀eq : y₀ = g t' := hfun c (p + σ * t') y₀ (g t') hy₀ (hg_spec t' hsD)
  intro u hu
  -- Recentre the ball: `u = p + σ u'` with `|u' - t'| = |u - (p + σ t')|`.
  set u' : ℝ := σ * (u - p) with hu'def
  have hpσu' : p + σ * u' = u := by
    rw [hu'def]
    have h : σ * (σ * (u - p)) = (σ * σ) * (u - p) := by ring
    rw [h, hσsq, one_mul]
    ring
  have hshift : σ * (u - p) - t' = σ * (u - (p + σ * t')) := by
    have h1 : σ * (u - (p + σ * t')) = σ * (u - p) - σ * σ * t' := by ring
    rw [h1, hσsq]
    ring
  have habs : |u' - t'| = |u - (p + σ * t')| := by
    rw [hu'def, hshift, abs_mul, hσabs, one_mul]
  have hu'lt : |u' - t'| < t' / 2 := by rw [habs]; exact hu
  obtain ⟨hu'D, hineq1, hineq2⟩ := hwin u' hu'lt
  have hgu'Y : Fin.cons u (Fin.cons (g u') c) ∈ Y := by
    have h := hg_spec u' hu'D
    rwa [hpσu'] at h
  refine ⟨g u', hgu'Y, ?_, ?_⟩
  · rw [hK, hy₀eq]; exact hineq1
  · rw [hK, hy₀eq]; exact hineq2

end Work.WilVP
