import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.ArchGlueV2

/-!
# `Work.HP.tau_meas_pos`

Measurability in `a` and positivity of the archimedean factor

  `τ(a;γ) = γ · vol{u : ‖u‖ ≤ 1, a ∈ 𝒞_{ν(u)}^{(γ)}}`   (paper (5.2)),

where `𝒞_v^{(γ)} = {t : |⟨v,t⟩| ≤ ‖v‖‖t‖/(2γ)}` (`Cgam`).

* `measurable_volume_band` : `a ↦ volume (band a γ)` is measurable.  The defining condition of
  `band` is closed in the pair `(a,u)`, hence Borel; a measurable section of a Borel subset of a
  product has measurable measure (`measurable_measure_prodMk_left`, Fubini).
* `volume_band_pos` : if `γ > 0` and `a` has a real zero on the unit sphere, then `band a γ` has
  nonempty interior (a neighbourhood of the zero, shrunk a little to get inside the unit ball),
  hence positive measure.
* `tau_meas_pos` : the three assertions.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-- The sup norm `‖·‖` on `ι → ℝ` is bounded by the Euclidean norm `rNorm`. -/
lemma norm_le_rNorm (v : ι → ℝ) : ‖v‖ ≤ rNorm v := by
  refine (pi_norm_le_iff_of_nonneg (rNorm_nonneg v)).mpr fun i => ?_
  simpa [Real.norm_eq_abs] using abs_apply_le_rNorm v i

/-- `rNorm` vanishes exactly at the origin. -/
lemma rNorm_pos {v : ι → ℝ} : 0 < rNorm v ↔ v ≠ 0 := by
  constructor
  · intro h hv
    rw [hv] at h
    simp [rNorm] at h
  · intro hv
    rcases lt_or_eq_of_le (rNorm_nonneg v) with h | h
    · exact h
    · exact absurd (rNorm_eq_zero.mp h.symm) hv

lemma continuous_rNorm : Continuous (rNorm : (ι → ℝ) → ℝ) := by
  rw [show rNorm = (fun v : ι → ℝ => Real.sqrt (∑ i, v i ^ 2)) from rfl]
  fun_prop

/-- The Veronese map does not kill a nonzero vector. -/
private lemma veronese_ne_zero {d n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) :
    veronese d n x ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx (funext h)
  intro hzero
  let e : Fin (n + 1) → Fin (d + 1) := Function.update (fun _ => 0) i ⟨d, Nat.lt_succ_self d⟩
  have hsum : ∑ j, (e j : ℕ) = d := by
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j _ hj; simp [e, Function.update_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hval : veronese d n x ⟨e, hsum⟩ = x i ^ d := by
    simp only [veronese]
    rw [Finset.prod_eq_single i]
    · simp [e]
    · intro j _ hj; simp [e, Function.update_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  have : veronese d n x ⟨e, hsum⟩ = 0 := by rw [hzero]; rfl
  rw [hval] at this
  exact (pow_ne_zero d hi) this

/-- `g_{a,γ}(u) = ‖ν(u)‖‖a‖/(2γ) − |⟨ν(u), a⟩|`; the `Cgam` condition on `a` is `g ≥ 0`. -/
def gfun (d n : ℕ) (a : Mon d n → ℝ) (γ : ℝ) (u : Fin (n + 1) → ℝ) : ℝ :=
  rNorm (veronese d n u) * rNorm a / (2 * γ) - |dotR (veronese d n u) a|

lemma continuous_gfun (d n : ℕ) (a : Mon d n → ℝ) (γ : ℝ) : Continuous (gfun d n a γ) := by
  rw [show gfun d n a γ = (fun u : Fin (n + 1) → ℝ =>
      Real.sqrt (∑ m : Mon d n, (∏ i, u i ^ (m.1 i : ℕ)) ^ 2) * rNorm a / (2 * γ)
      - |∑ m : Mon d n, (∏ i, u i ^ (m.1 i : ℕ)) * a m|) from rfl]
  fun_prop

/-- Membership in `band`, in terms of `gfun`. -/
lemma mem_band_iff (d n : ℕ) (a : Mon d n → ℝ) (γ : ℝ) (u : Fin (n + 1) → ℝ) :
    u ∈ band d n a γ ↔ rNorm u ≤ 1 ∧ 0 ≤ gfun d n a γ u := by
  simp only [band, Cgam, gfun, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, sub_nonneg.mpr h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, sub_nonneg.mp h2⟩

/-! ## Measurability -/

lemma measurable_volume_band (d n : ℕ) (γ : ℝ) :
    Measurable fun a : Mon d n → ℝ => volume (band d n a γ) := by
  let S : Set ((Mon d n → ℝ) × (Fin (n + 1) → ℝ)) :=
    {p | rNorm p.2 ≤ 1 ∧
      |dotR (veronese d n p.2) p.1| ≤ rNorm (veronese d n p.2) * rNorm p.1 / (2 * γ)}
  have hS : MeasurableSet S := by
    have h1 : Continuous fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) => rNorm p.2 := by
      rw [show (fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) => rNorm p.2)
          = (fun p => Real.sqrt (∑ i, p.2 i ^ 2)) from rfl]
      fun_prop
    have h2 : Continuous fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) =>
        |dotR (veronese d n p.2) p.1| := by
      rw [show (fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) =>
            |dotR (veronese d n p.2) p.1|)
          = (fun p => |∑ m : Mon d n, (∏ i, p.2 i ^ (m.1 i : ℕ)) * p.1 m|) from rfl]
      fun_prop
    have h3 : Continuous fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) =>
        rNorm (veronese d n p.2) * rNorm p.1 / (2 * γ) := by
      rw [show (fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) =>
            rNorm (veronese d n p.2) * rNorm p.1 / (2 * γ))
          = (fun p => Real.sqrt (∑ m : Mon d n, (∏ i, p.2 i ^ (m.1 i : ℕ)) ^ 2)
              * Real.sqrt (∑ i, p.1 i ^ 2) / (2 * γ)) from rfl]
      fun_prop
    exact ((isClosed_le h1 continuous_const).inter (isClosed_le h2 h3)).measurableSet
  have hset : ∀ a : Mon d n → ℝ, band d n a γ = Prod.mk a ⁻¹' S := by
    intro a
    ext u
    simp only [band, S, Cgam, Set.mem_ofPred_eq, Set.mem_preimage]
  have hkey : (fun a : Mon d n → ℝ => volume (band d n a γ))
      = fun a => (volume : Measure (Fin (n + 1) → ℝ)) (Prod.mk a ⁻¹' S) := by
    funext a
    rw [hset a]
  rw [hkey]
  exact measurable_measure_prodMk_left (ν := (volume : Measure (Fin (n + 1) → ℝ))) hS

/-! ## Positivity -/

lemma volume_band_pos {d n : ℕ} {a : Mon d n → ℝ} {γ : ℝ} (hγ : 0 < γ) (ha : IPt d n a) :
    0 < volume (band d n a γ) := by
  by_cases ha0 : a = 0
  · subst ha0
    have hopen : IsOpen {u : Fin (n + 1) → ℝ | rNorm u < 1} :=
      isOpen_lt continuous_rNorm continuous_const
    have hne : ({u : Fin (n + 1) → ℝ | rNorm u < 1}).Nonempty := by
      refine ⟨0, ?_⟩
      simp [rNorm]
    have hpos : 0 < volume {u : Fin (n + 1) → ℝ | rNorm u < 1} :=
      IsOpen.measure_pos volume hopen hne
    refine lt_of_lt_of_le hpos (measure_mono ?_)
    intro u hu
    rw [mem_band_iff]
    exact ⟨le_of_lt hu, by simp [gfun, dotR, rNorm]⟩
  · obtain ⟨x, hx1, hx0⟩ := ha
    have hxne : x ≠ 0 := by
      intro h
      rw [h] at hx1
      simp [rNorm] at hx1
    have hdot : dotR (veronese d n x) a = 0 := by
      have hcomm : dotR (veronese d n x) a = dotR a (veronese d n x) := by
        simp only [dotR]
        exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
      rw [hcomm, ← formEvalR_eq_dotR d n a x, hx0]
    have hgx : 0 < gfun d n a γ x := by
      have hνx : 0 < rNorm (veronese d n x) := rNorm_pos.mpr (veronese_ne_zero hxne)
      have hνa : 0 < rNorm a := rNorm_pos.mpr ha0
      simp only [gfun, hdot, abs_zero, sub_zero]
      positivity
    have hopen : IsOpen {u : Fin (n + 1) → ℝ | 0 < gfun d n a γ u} :=
      isOpen_lt continuous_const (continuous_gfun d n a γ)
    have hnhds : {u : Fin (n + 1) → ℝ | 0 < gfun d n a γ u} ∈ 𝓝 x :=
      hopen.mem_nhds hgx
    have hphi : Continuous fun c : ℝ => c • x := continuous_id.smul continuous_const
    have hpre : (fun c : ℝ => c • x) ⁻¹'
        {u : Fin (n + 1) → ℝ | 0 < gfun d n a γ u} ∈ 𝓝 (1 : ℝ) := by
      refine hphi.continuousAt.preimage_mem_nhds ?_
      simpa using hnhds
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hball⟩
    set δ : ℝ := min ε 1 / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      have : 0 < min ε 1 := lt_min hε one_pos
      linarith
    have hδlt : δ < ε := by
      rw [hδdef]
      have : min ε 1 ≤ ε := min_le_left _ _
      linarith
    have hδlt1 : δ < 1 := by
      rw [hδdef]
      have : min ε 1 ≤ 1 := min_le_right _ _
      linarith
    have hcball : (1 - δ) ∈ Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq,
        show (1 : ℝ) - δ - 1 = -δ from by ring, abs_neg, abs_of_pos hδpos]
      exact hδlt
    have hcpos : 0 < 1 - δ := by linarith
    have hgc : 0 < gfun d n a γ ((1 - δ) • x) := hball hcball
    have hrc : rNorm ((1 - δ) • x) < 1 := by
      rw [rNorm_smul_of_pos (1 - δ) x hcpos, hx1, mul_one]
      linarith
    have hopenU : IsOpen {u : Fin (n + 1) → ℝ | rNorm u < 1 ∧ 0 < gfun d n a γ u} :=
      (isOpen_lt continuous_rNorm continuous_const).inter
        (isOpen_lt continuous_const (continuous_gfun d n a γ))
    have hneU : ({u : Fin (n + 1) → ℝ | rNorm u < 1 ∧ 0 < gfun d n a γ u}).Nonempty :=
      ⟨(1 - δ) • x, hrc, hgc⟩
    have hpos : 0 < volume {u : Fin (n + 1) → ℝ | rNorm u < 1 ∧ 0 < gfun d n a γ u} :=
      IsOpen.measure_pos volume hopenU hneU
    refine lt_of_lt_of_le hpos (measure_mono ?_)
    intro u hu
    rw [mem_band_iff]
    exact ⟨le_of_lt hu.1, le_of_lt hu.2⟩

/-! ## The main statement -/

theorem tau_meas_pos (d n : ℕ) (hn : 3 ≤ n) :
    (∀ (γ : ℝ), 0 < γ → Measurable fun a : Mon d n → ℝ => tauArch d n a γ) ∧
    (∀ (a : Mon d n → ℝ) (γ : ℝ), 0 < γ → IPt d n a → 0 < tauArch d n a γ) ∧
    (∀ (a : Mon d n → ℝ) (γ : ℝ), 0 ≤ γ → 0 ≤ tauArch d n a γ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ
    exact (measurable_volume_band d n γ).ennreal_toReal.const_mul γ
  · intro a γ hγ ha
    have hvol : 0 < volume (band d n a γ) := volume_band_pos hγ ha
    have hsub : band d n a γ ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := by
      intro u hu
      have hru : rNorm u ≤ 1 := ((mem_band_iff d n a γ u).mp hu).1
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (norm_le_rNorm u) hru
    have htop : volume (band d n a γ) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
      rw [Real.volume_pi_closedBall (0 : Fin (n + 1) → ℝ) (by norm_num : (0 : ℝ) ≤ 1)]
      exact ENNReal.ofReal_lt_top
    exact mul_pos hγ (ENNReal.toReal_pos (ne_of_gt hvol) htop)
  · intro a γ hγ
    exact mul_nonneg hγ ENNReal.toReal_nonneg

end Work.HP
