import Mathlib
import Submission.Work.Drive.chordStrictWideDescent
import Submission.Work.Drive.planeChartDataAux
import Submission.Work.Drive.Neutral.StripDiskAux

namespace Work.Drive

open scoped ContDiff

noncomputable section

/-!
# The direction-only descent of the chord data

`Work.Drive.chordStrictWideDescent` produces smooth `M, W : ℂ × ℝ → ℂ` whose values on the unit
circle are the chord datum `dataMid`/`dchW` of the curve, with the strict band inequality
`4|τ|‖W‖² < ‖M‖²` on the annulus `1/4 ≤ ‖x‖ ≤ 2` and non-vanishing at `τ = 0`.

Here we produce a *radially symmetric* variant: `M, W` depend on `x` only through the **direction**
`x/‖x‖` on `1/8 ≤ ‖x‖`, and are **constant in `x`** on the disk `‖x‖ ≤ 1/16`, all clauses being kept
(with the band annulus widened to `1/8 ≤ ‖x‖ ≤ 2`, since the direction map has modulus one there).

The construction is the pull-back of the descent datum along the smoothed direction map
`dirMap x = pStep (1/16) (1/8) ‖x‖ • (x/‖x‖)`, which is `x/‖x‖` for `‖x‖ ≥ 1/8` and `0` for
`‖x‖ ≤ 1/16`, and whose smoothness off the origin is the only content.
-/

/-- The smoothed direction map: `x ↦ x/‖x‖` for `‖x‖ ≥ 1/8`, `0` for `‖x‖ ≤ 1/16`. -/
private def dirMap (x : ℂ) : ℂ :=
  ((pStep (1 / 16) (1 / 8) ‖x‖ : ℝ) : ℂ) * (x / ((‖x‖ : ℝ) : ℂ))

private lemma contDiff_dirMap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dirMap := by
  -- `x ↦ ‖x‖` is smooth away from the origin
  have hnorm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℂ => ‖x‖) {x : ℂ | x ≠ 0} := by
    refine (?_ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => Real.sqrt (Complex.normSq x)) {x : ℂ | x ≠ 0}).congr ?_
    · intro x hx
      have hns0 : Complex.normSq x ≠ 0 := fun h => hx (Complex.normSq_eq_zero.mp h)
      exact ((Real.contDiffAt_sqrt hns0).comp x
        (Neutral.contDiff_complexNormSq.contDiffAt)).contDiffWithinAt
    · intro x _
      rw [Complex.normSq_eq_norm_sq x, Real.sqrt_sq (norm_nonneg x)]
  have hnormC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => ((‖x‖ : ℝ) : ℂ)) {x : ℂ | x ≠ 0} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hnorm
  have hA : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => ((pStep (1 / 16) (1 / 8) ‖x‖ : ℝ) : ℂ)) {x : ℂ | x ≠ 0} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiff_pStep _ _).comp_contDiffOn hnorm)
  have hB : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℂ => x / ((‖x‖ : ℝ) : ℂ)) {x : ℂ | x ≠ 0} := by
    have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℂ => (((‖x‖ : ℝ) : ℂ))⁻¹) {x : ℂ | x ≠ 0} :=
      hnormC.inv (fun x hx => fun h => norm_ne_zero_iff.mpr hx (Complex.ofReal_eq_zero.mp h))
    exact (contDiffOn_id.mul hinv).congr (fun x hx => by rw [div_eq_mul_inv]; rfl)
  have hone : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dirMap {x : ℂ | x ≠ 0} := hA.mul hB
  have hzero : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dirMap {x : ℂ | ‖x‖ < 1 / 16} :=
    (contDiffOn_const (c := (0 : ℂ))).congr (fun x hx => by
      simp only [dirMap]
      rw [pStep_eq_zero (by norm_num) (le_of_lt hx), Complex.ofReal_zero, zero_mul])
  refine contDiff_of_contDiffOn_union_of_isOpen hone hzero ?_ isOpen_ne
    (isOpen_lt continuous_norm continuous_const)
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  by_cases hx : x = 0
  · exact Or.inr (by rw [hx]; norm_num)
  · exact Or.inl hx

private lemma dirMap_eq_div {x : ℂ} (hx : 1 / 8 ≤ ‖x‖) :
    dirMap x = x / ((‖x‖ : ℝ) : ℂ) := by
  simp only [dirMap]
  rw [pStep_eq_one (by norm_num) hx, Complex.ofReal_one, one_mul]

private lemma dirMap_eq_zero {x : ℂ} (hx : ‖x‖ ≤ 1 / 16) : dirMap x = 0 := by
  simp only [dirMap]
  rw [pStep_eq_zero (by norm_num) hx, Complex.ofReal_zero, zero_mul]

private lemma dirMap_eq_self {x : ℂ} (hx : ‖x‖ = 1) : dirMap x = x := by
  have h8 : (1 / 8 : ℝ) ≤ ‖x‖ := by rw [hx]; norm_num
  rw [dirMap_eq_div h8, hx, Complex.ofReal_one, div_one]

private lemma norm_dirMap {x : ℂ} (hx : 1 / 8 ≤ ‖x‖) : ‖dirMap x‖ = 1 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    norm_num at hx
  rw [dirMap_eq_div hx, norm_div]
  simp [norm_ne_zero_iff.mpr hx0]

theorem directionOnly_descent (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    ∃ M W : ℂ × ℝ → ℂ, ∃ c : ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧ 0 < c ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 →
        W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ)) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
        4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2) ∧
      (∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0) ∧
      (∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0) ∧
      (∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0) ∧
      (∀ x x' : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → 1 / 8 ≤ ‖x'‖ →
        x / ((‖x‖ : ℝ) : ℂ) = x' / ((‖x'‖ : ℝ) : ℂ) →
        M (x, τ) = M (x', τ) ∧ W (x, τ) = W (x', τ)) ∧
      (∀ x x' : ℂ, ∀ τ : ℝ, ‖x‖ ≤ 1 / 16 → ‖x'‖ ≤ 1 / 16 →
        M (x, τ) = M (x', τ) ∧ W (x, τ) = W (x', τ)) := by
  classical
  obtain ⟨M₀, W₀, c, hM₀sm, hW₀sm, hc, hM₀val, hW₀val, hband, hWband, hMdiag, hWdiag⟩ :=
    chordStrictWideDescent γ hγ hγne
  let M : ℂ × ℝ → ℂ := fun p => M₀ (dirMap p.1, p.2)
  let W : ℂ × ℝ → ℂ := fun p => W₀ (dirMap p.1, p.2)
  have hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp only [M]
    exact hM₀sm.comp ((contDiff_dirMap.comp contDiff_fst).prodMk contDiff_snd)
  have hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    dsimp only [W]
    exact hW₀sm.comp ((contDiff_dirMap.comp contDiff_fst).prodMk contDiff_snd)
  refine ⟨M, W, c, hMsm, hWsm, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x τ hτ hx
    change M₀ (dirMap x, τ) = Neutral.dataMid γ x (Real.sqrt τ)
    rw [dirMap_eq_self hx]
    exact hM₀val x τ hτ hx
  · intro x τ hτ hx
    change W₀ (dirMap x, τ) = Neutral.dchW γ (x, Real.sqrt τ)
    rw [dirMap_eq_self hx]
    exact hW₀val x τ hτ hx
  · intro x τ h1 h2 h3 h4
    have h8 : (1 / 4 : ℝ) ≤ ‖dirMap x‖ := by rw [norm_dirMap h1]; norm_num
    have h2' : ‖dirMap x‖ ≤ 2 := by rw [norm_dirMap h1]; norm_num
    change 4 * |τ| * ‖W₀ (dirMap x, τ)‖ ^ 2 < ‖M₀ (dirMap x, τ)‖ ^ 2
    exact hband (dirMap x) τ h8 h2' h3 h4
  · intro x τ h1 h2 h3 h4
    have h8 : (1 / 4 : ℝ) ≤ ‖dirMap x‖ := by rw [norm_dirMap h1]; norm_num
    have h2' : ‖dirMap x‖ ≤ 2 := by rw [norm_dirMap h1]; norm_num
    change W₀ (dirMap x, τ) ≠ 0
    exact hWband (dirMap x) τ h8 h2' h3 h4
  · intro x h1 h2
    have h8 : (1 / 4 : ℝ) ≤ ‖dirMap x‖ := by rw [norm_dirMap h1]; norm_num
    change M₀ (dirMap x, 0) ≠ 0
    exact hMdiag (dirMap x) h8 (le_of_eq (norm_dirMap h1))
  · intro x h1 h2
    have h8 : (1 / 4 : ℝ) ≤ ‖dirMap x‖ := by rw [norm_dirMap h1]; norm_num
    change W₀ (dirMap x, 0) ≠ 0
    exact hWdiag (dirMap x) h8 (le_of_eq (norm_dirMap h1))
  · intro x x' τ h1 h1' hdir
    have hd : dirMap x = dirMap x' := by
      rw [dirMap_eq_div h1, dirMap_eq_div h1', hdir]
    change M₀ (dirMap x, τ) = M₀ (dirMap x', τ) ∧
      W₀ (dirMap x, τ) = W₀ (dirMap x', τ)
    rw [hd]
    exact ⟨rfl, rfl⟩
  · intro x x' τ hx hx'
    change M₀ (dirMap x, τ) = M₀ (dirMap x', τ) ∧
      W₀ (dirMap x, τ) = W₀ (dirMap x', τ)
    rw [dirMap_eq_zero hx, dirMap_eq_zero hx']
    exact ⟨rfl, rfl⟩

end

end Work.Drive
