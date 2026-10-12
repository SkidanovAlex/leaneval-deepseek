import ChallengeDeps
import Submission.Work.BoseBogFS.honestBogOpBoundFS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.honestRegimeRows`

The four **regime rows** of the honest interface of node BOG (`FINDING_honestKAP_session8.md`
§2), uniformly in the admissible chemical potential `μ` (`Adm v ε₀ μ`, i.e. `0 < μ`,
`μ (a v)³ ≤ ε₀` and FS's `ParamsOK`):

* `R ≤ ℓ(μ)·chiR0`                — FS's disjointness regime (`hRℓ`);
* `R / sideAt μ (a v) ≤ r₁`       — the first hypothesis of FS `eq:W1-g` (`hreg`);
* `C·(R / sideAt μ (a v))² ≤ 1/4` — the second-order condition (`hcond`);
* `honestDD v μ R ≤ 1/2`          — the `δ_D` row (`hδD1`), where
  `honestDD v μ R = 8192·μ·(a v)³·(R / a v)²`.

All four are pure consequences of the closed form of the box side

  `sideAt μ a = a · (μa³)^{−163/323}`   (`Work.BoseBox.sideAt_eq_rpow`),

which blows up as `μ → 0⁺`.  The admissible region is cut off by the diluteness bound
`μ·(a v)³ ≤ ε₀`, so a single threshold `ε₀`, small enough, makes all four rows hold
simultaneously: the *first three* are instances of the one statement that the box side
`ℓ(μ) = sideAt μ (a v)` eventually dominates any prescribed ratio `R / r₀`, and the fourth
uses `honestDD = 8192·(μa³)·(R/a v)² ≤ 8192·ε₀·(R/a v)²`.

The potential data `hv`, `hv1`, `hvrad`, `hv_supp` of the statement are not used here; they
belong to the surrounding interface of the `𝒞`-slot.
-/

namespace Work.BoseBogFS

/-- Monotonicity of the admissible region in the diluteness threshold: a smaller threshold
gives a smaller `Adm` set, so a row proved on `Adm v ε μ` transfers to `Adm v ε' μ` for every
`ε' ≥ ε`. -/
lemma adm_mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε ε' μ : ℝ} (h : ε ≤ ε')
    (hA : Work.BoseBoxFix.Adm v ε μ) : Work.BoseBoxFix.Adm v ε' μ :=
  ⟨hA.1, le_trans hA.2.1 h, hA.2.2⟩

/-- **The diluteness threshold at which the box side dominates `R / r₀`.**

For every `r₀ > 0` there is `ε₀ > 0` such that for every admissible chemical potential
(`Work.BoseBoxFix.Adm v ε₀ μ`, whose diluteness clause is `μ·(a v)³ ≤ ε₀`) the box side
`ℓ(μ) = sideAt μ (a v) = a·(μa³)^{−163/323}` satisfies `R / ℓ(μ) ≤ r₀`.

Explicitly `ε₀ = min 1 ((r₀·a/R)^{323/163})`: from `μa³ ≤ ε₀` the negative power is at least
`ε₀^{−163/323} ≥ R/(r₀ a)`, i.e. `R ≤ r₀ · ℓ(μ)`. -/
theorem exists_adm_sideAt_div_le (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hav : 0 < _root_.BoseGases.a v) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ r₀ := by
  have ha : 0 < _root_.BoseGases.a v := hav
  set t : ℝ := r₀ * _root_.BoseGases.a v / R with ht
  have htpos : 0 < t := by rw [ht]; positivity
  refine ⟨min 1 (t ^ ((323 : ℝ) / 163)), lt_min one_pos (Real.rpow_pos_of_pos htpos _), ?_⟩
  intro μ hμ
  have hμpos : 0 < μ := hμ.1
  have hμa3le : μ * (_root_.BoseGases.a v) ^ 3 ≤ min 1 (t ^ ((323 : ℝ) / 163)) := hμ.2.1
  have hμa3pos : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos ha 3)
  have hE0pos : 0 < min 1 (t ^ ((323 : ℝ) / 163)) :=
    lt_min one_pos (Real.rpow_pos_of_pos htpos _)
  have hEle : min 1 (t ^ ((323 : ℝ) / 163)) ≤ t ^ ((323 : ℝ) / 163) := min_le_right _ _
  -- `(μa³)^{163/323} ≤ t`
  have hpow : (μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323) ≤ t := by
    have h1 : (min 1 (t ^ ((323 : ℝ) / 163))) ^ ((163 : ℝ) / 323)
        ≤ (t ^ ((323 : ℝ) / 163)) ^ ((163 : ℝ) / 323) :=
      Real.rpow_le_rpow hE0pos.le hEle (by norm_num)
    have h2 : (t ^ ((323 : ℝ) / 163)) ^ ((163 : ℝ) / 323) = t := by
      rw [← Real.rpow_mul htpos.le]
      rw [show (323 : ℝ) / 163 * ((163 : ℝ) / 323) = 1 by norm_num, Real.rpow_one]
    have h3 : (μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323)
        ≤ (min 1 (t ^ ((323 : ℝ) / 163))) ^ ((163 : ℝ) / 323) :=
      Real.rpow_le_rpow hμa3pos.le hμa3le (by norm_num)
    calc (μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323)
        ≤ (min 1 (t ^ ((323 : ℝ) / 163))) ^ ((163 : ℝ) / 323) := h3
      _ ≤ (t ^ ((323 : ℝ) / 163)) ^ ((163 : ℝ) / 323) := h1
      _ = t := h2
  have hside : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      = _root_.BoseGases.a v * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ)) :=
    Work.BoseBox.sideAt_eq_rpow ha hμpos
  rw [hside, div_le_iff₀ (by positivity)]
  have hmain : R * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323)
      ≤ r₀ * _root_.BoseGases.a v := by
    have h := mul_le_mul_of_nonneg_left hpow hR.le
    rw [ht] at h
    rw [mul_div_cancel₀ (r₀ * _root_.BoseGases.a v) (ne_of_gt hR)] at h
    exact h
  have hp : 0 < (μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323) :=
    Real.rpow_pos_of_pos hμa3pos _
  have hneg : (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(163 / 323 : ℝ))
      = ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323))⁻¹ := by
    rw [Real.rpow_neg hμa3pos.le]
  rw [hneg, show r₀ * (_root_.BoseGases.a v
        * ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323))⁻¹)
        = r₀ * _root_.BoseGases.a v
          / ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((163 : ℝ) / 323)) by ring]
  exact (le_div_iff₀ hp).mpr hmain

/-- **The `hδD1` regime row.**  For every `R > 0` there is `ε₀ > 0` such that on the whole
admissible region the `δ_D`-error of the honest denominator row satisfies

  `honestDD v μ R = 8192·μ·(a v)³·(R / a v)² ≤ 1/2`.

Indeed `honestDD = 8192·(μa³)·(R/a v)² ≤ 8192·ε₀·(R/a v)²`, and the threshold
`ε₀ = min 1 ((a v)²/(16384 R²))` makes the right side `≤ 1/2`. -/
theorem exists_adm_honestDD_le (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hav : 0 < _root_.BoseGases.a v) {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      honestDD v μ R ≤ 1 / 2 := by
  refine ⟨min 1 ((_root_.BoseGases.a v) ^ 2 / (16384 * R ^ 2)),
    lt_min one_pos (by positivity), ?_⟩
  intro μ hμ
  have hμpos : 0 < μ := hμ.1
  have hμa3le : μ * (_root_.BoseGases.a v) ^ 3
      ≤ min 1 ((_root_.BoseGases.a v) ^ 2 / (16384 * R ^ 2)) := hμ.2.1
  have hmax : max 0 μ = μ := max_eq_right hμpos.le
  rw [honestDD, hmax]
  have hle : μ * (_root_.BoseGases.a v) ^ 3
      ≤ (_root_.BoseGases.a v) ^ 2 / (16384 * R ^ 2) := le_trans hμa3le (min_le_right _ _)
  have hratio : (R / _root_.BoseGases.a v) ^ 2
      = R ^ 2 / (_root_.BoseGases.a v) ^ 2 := by rw [div_pow]
  rw [hratio]
  have hkey : μ * (_root_.BoseGases.a v) ^ 3 * (R ^ 2 / (_root_.BoseGases.a v) ^ 2)
      ≤ ((_root_.BoseGases.a v) ^ 2 / (16384 * R ^ 2))
        * (R ^ 2 / (_root_.BoseGases.a v) ^ 2) := by
    gcongr
  have hsimp : ((_root_.BoseGases.a v) ^ 2 / (16384 * R ^ 2))
      * (R ^ 2 / (_root_.BoseGases.a v) ^ 2) = 1 / 16384 := by
    field_simp
  linarith [hkey, hsimp.ge, hsimp.le]

theorem honestRegimeRows (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    {R r₁ C : ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hC : 0 ≤ C) (hr₁ : 0 < r₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) ∧
      (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≤ r₁) ∧
      (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 4) ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → Work.BoseBogFS.honestDD v μ R ≤ 1 / 2 := by
  -- the three ratio rows: `R / sideAt μ (a v) ≤ chiR0`, `≤ r₁`, `≤ 1/(2√(C+1))`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
    exists_adm_sideAt_div_le v hav hR Submission.BoseGases.chiR0_pos
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := exists_adm_sideAt_div_le v hav hR hr₁
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨ε₃, hε₃pos, hε₃⟩ := exists_adm_sideAt_div_le v hav hR
    (r₀ := 1 / (2 * Real.sqrt (C + 1)))
    (div_pos one_pos (mul_pos two_pos (Real.sqrt_pos.mpr hC1)))
  obtain ⟨ε₄, hε₄pos, hε₄⟩ := exists_adm_honestDD_le v hav hR
  refine ⟨min (min ε₁ ε₂) (min ε₃ ε₄),
    lt_min (lt_min hε₁pos hε₂pos) (lt_min hε₃pos hε₄pos), ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    have hA : Work.BoseBoxFix.Adm v ε₁ μ :=
      adm_mono (le_trans (min_le_left (min ε₁ ε₂) (min ε₃ ε₄)) (min_le_left ε₁ ε₂)) hμ
    have h1 := hε₁ μ hA
    rw [div_le_iff₀ (Work.BoseBox.sideAt_pos hA.1 hav)] at h1
    rw [Work.BoseFixR.ell_eq]
    exact le_trans h1 (le_of_eq (mul_comm Submission.BoseGases.chiR0
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
  · intro μ hμ
    have hA : Work.BoseBoxFix.Adm v ε₂ μ :=
      adm_mono (le_trans (min_le_left (min ε₁ ε₂) (min ε₃ ε₄)) (min_le_right ε₁ ε₂)) hμ
    exact hε₂ μ hA
  · intro μ hμ
    have hA : Work.BoseBoxFix.Adm v ε₃ μ :=
      adm_mono (le_trans (min_le_right (min ε₁ ε₂) (min ε₃ ε₄)) (min_le_left ε₃ ε₄)) hμ
    have hx := hε₃ μ hA
    have hx0 : 0 ≤ R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      div_nonneg hR.le (Work.BoseBox.sideAt_pos hA.1 hav).le
    have hsq := pow_le_pow_left₀ hx0 hx 2
    have hr2 : (1 / (2 * Real.sqrt (C + 1))) ^ 2 = 1 / (4 * (C + 1)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hC1.le]
      norm_num
    have hCx : C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2
        ≤ C * (1 / (2 * Real.sqrt (C + 1))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hC
    rw [hr2] at hCx
    have hfin : C * (1 / (4 * (C + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (C + 1))]
      linarith
    linarith
  · intro μ hμ
    have hA : Work.BoseBoxFix.Adm v ε₄ μ :=
      adm_mono (le_trans (min_le_right (min ε₁ ε₂) (min ε₃ ε₄)) (min_le_right ε₃ ε₄)) hμ
    exact hε₄ μ hA

end Work.BoseBogFS
