import Mathlib
import Submission.Work.Drive.tcBadDefs
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.spatial_le_slope_mul_dist

/-!
# `Work.Drive.tangentChordGP_of_no_tcBad`

The passage from the *bad set* `Work.Drive.tcBad r ρ k` (the coefficients in the ball `Kv ρ` at
which some pair of parameters separated by `1/(k+1)` on the parameter circle is a degenerate
tangent chord: the chord is parallel to the velocity at the first parameter and the second order
functional `⟪v a × a a, v b⟫` vanishes) to the geometric non-degeneracy condition
`Work.Drive.TangentChordGP (pertV r c)` of `Submission/Work/Drive/genericFullDefs.lean`.

The proof is the parameter reduction: the two conditions defining `TangentChordGP` are
`period`-periodic in each parameter, so a violating pair `(a, b)` with `0 < b - a < period`
can be translated into the half-open period `[0, period)`, where the two parameters are still
distinct (their circular separation is then positive) and where the two slots of `tcPsi`
vanish; the separation scale `k` is then chosen from the separation.  The only geometric input
is the simplicity of the perturbed curve (`hS.injective_on_period`), which makes the chord of
two distinct parameters of one period non-zero.

Everything here is elementary (periodicity, the cross product, one real floor).
-/

set_option maxHeartbeats 800000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## Elementary tools -/

/-- For every positive real `t` there is `k` with `1 / (k + 1) ≤ t`. -/
lemma exists_div_succ_le_tc {t : ℝ} (ht : 0 < t) : ∃ k : ℕ, (1:ℝ)/(k+1) ≤ t := by
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / t)
  refine ⟨k, ?_⟩
  have h1 : (1:ℝ) ≤ (k : ℝ) * t := by
    have h := mul_le_mul_of_nonneg_right hk ht.le
    rwa [div_mul_cancel₀ 1 (ne_of_gt ht)] at h
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (k : ℝ) + 1)]
  nlinarith

/-- The circular separation of two distinct points of one period is positive. -/
lemma csep_pos_of_mem_Ico_tc {x y : ℝ} (hx : x ∈ Set.Ico 0 period)
    (hy : y ∈ Set.Ico 0 period) (hne : x ≠ y) : 0 < csep x y := by
  rw [csep, lt_min_iff]
  refine ⟨abs_pos.mpr (sub_ne_zero.mpr hne), ?_⟩
  have hx2 : x < 2 * Real.pi := by simpa [period] using hx.2
  have hy2 : y < 2 * Real.pi := by simpa [period] using hy.2
  have h1 : |x - y| < 2 * Real.pi := by
    rw [abs_lt]
    exact ⟨by linarith [hx.1, hy2], by linarith [hx2, hy.1]⟩
  linarith

/-- A nonzero vector parallel to two other vectors makes the mixed scalar product
`⟪a × A, b⟫` vanish. -/
lemma inner_cross3_of_parallel_tc {u a b A : Space} (hu : u ≠ 0)
    (h1 : cross3 u a = 0) (h2 : cross3 u b = 0) : inner ℝ (cross3 a A) b = 0 := by
  rcases (cross3_eq_zero_iff_smul_local (u := u) (v := a)).mp h1 with h | ⟨t, ht⟩
  · exact absurd h hu
  rcases (cross3_eq_zero_iff_smul_local (u := u) (v := b)).mp h2 with h | ⟨s, hs⟩
  · exact absurd h hu
  rw [ht, hs, cross3_smul_left]
  rw [inner_smul_left, inner_smul_right]
  rw [show inner ℝ (cross3 u A) u = 0 from
    Commons.Analysis.CrossProduct.inner_cross3_self_left u A]
  ring

/-- Membership in `tcKset` for the parameter pair `tcPar x y`. -/
lemma mem_tcKset_tcPar_tc {x y : ℝ} {k : ℕ} (hx : x ∈ Set.Icc 0 (2 * Real.pi))
    (hy : y ∈ Set.Icc 0 (2 * Real.pi)) (hsep : (1:ℝ)/(k+1) ≤ csep x y) :
    tcPar x y ∈ tcKset k := by
  rw [mem_tcKset]
  show tcBase k (tcHomeo (tcPar x y))
  refine ⟨?_, ?_, ?_⟩
  · simpa [tcHomeo_apply, tcPar] using hx
  · simpa [tcHomeo_apply, tcPar] using hy
  · simpa [tcHomeo_apply, tcPar] using hsep

/-! ## Reduction of a pair of parameters to one period -/

/-- **Reduction of a pair of parameters to one period.**  Two distinct parameters whose difference
is smaller than the period have translates in the half-open period `[0, period)` which are still
distinct. -/
lemma exists_reduce_tc {x y : ℝ} (hne : x ≠ y) (hlt : |y - x| < period) :
    ∃ x' y' : ℝ, x' ∈ Set.Ico 0 period ∧ y' ∈ Set.Ico 0 period ∧ x' ≠ y' ∧
      (∃ n : ℤ, x' = x + n • period) ∧ (∃ m : ℤ, y' = y + m • period) := by
  obtain ⟨n, hn⟩ := exists_zsmul_add_mem_Ico x
  have hd_lt : y - x < period := lt_of_le_of_lt (le_abs_self _) hlt
  have hd_gt : -period < y - x := by
    have h := lt_of_le_of_lt (neg_le_abs (y - x)) hlt
    linarith
  have hy₀_gt : -period < y + n • period := by linarith [hn.1]
  have hy₀_lt : y + n • period < 2 * period := by linarith [hn.2]
  have hper_pos : (0:ℝ) < period := by unfold period; positivity
  by_cases hneg : y + n • period < 0
  · refine ⟨x + n • period, y + n • period + period, hn, ⟨by linarith, by linarith⟩, ?_,
      ⟨n, rfl⟩, ⟨n + 1, by rw [add_zsmul, one_zsmul]; ring⟩⟩
    intro h
    have h2 : y - x = -period := by linarith
    have h3 : |y - x| = period := by rw [h2, abs_neg, abs_of_pos hper_pos]
    linarith [hlt, h3]
  · by_cases hlt' : y + n • period < period
    · refine ⟨x + n • period, y + n • period, hn, ⟨by linarith, hlt'⟩, ?_,
        ⟨n, rfl⟩, ⟨n, rfl⟩⟩
      intro h
      exact hne (by linarith)
    · refine ⟨x + n • period, y + n • period - period, hn, ⟨by linarith, by linarith⟩, ?_,
        ⟨n, rfl⟩, ⟨n - 1, by rw [sub_zsmul, one_zsmul]; ring⟩⟩
      intro h
      have h2 : y - x = period := by linarith
      have h3 : |y - x| = period := by rw [h2, abs_of_pos hper_pos]
      linarith [hlt, h3]

/-! ## Rewriting the two slots of `tcPsi` in terms of the perturbed curve -/

/-- `tcVel` is the velocity of the perturbed curve. -/
lemma tcVel_eq_velocity_tc {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) (t : ℝ) :
    tcVel r c t = velocity (pertV r c) t :=
  (tcVel_eq_pertVelV r c t).trans (velocity_pertV hr.smooth c t).symm

/-- The derivative of the perturbed curve is `pertVelV`. -/
lemma deriv_pertV_eq_tc {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) :
    deriv (pertV r c) = pertVelV r c := by
  funext t
  rw [← velocity_pertV hr.smooth c t]
  rfl

/-- `tcAcc` is the second derivative of the perturbed curve. -/
lemma tcAcc_eq_deriv2_tc {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) (t : ℝ) :
    tcAcc r c t = deriv (deriv (pertV r c)) t := by
  rw [tcAcc_eq_deriv r hr.smooth c t]
  show deriv (pertVelV r c) t = deriv (deriv (pertV r c)) t
  rw [deriv_pertV_eq_tc hr c]

/-- The first slot of `tcPsi` at a parameter pair. -/
lemma tcE1_tcPar_tc {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) (x y : ℝ) :
    tcE1 r (c, tcPar x y) =
      cross3 (pertV r c y - pertV r c x) (velocity (pertV r c) x) := by
  simp only [tcE1, tcPa_tcPar, tcPb_tcPar, tcPos_eq_pertV, tcVel_eq_pertVelV]
  rw [velocity_pertV hr.smooth c x]

/-- The second slot of `tcPsi` at a parameter pair. -/
lemma tcE3_tcPar_tc {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) (x y : ℝ) :
    tcE3 r (c, tcPar x y) =
      inner ℝ (cross3 (velocity (pertV r c) x) (deriv (deriv (pertV r c)) x))
        (velocity (pertV r c) y) := by
  simp only [tcE3, tcPa_tcPar, tcPb_tcPar, tcVel_eq_pertVelV,
    tcAcc_eq_deriv2_tc hr c x]
  rw [velocity_pertV hr.smooth c x, velocity_pertV hr.smooth c y]

/-! ## The configuration is bad -/

/-- **No configuration can avoid being recorded in `tcBad`.**  If two distinct parameters with
`|y - x| < period` have a chord parallel to the velocity at `x`, and either the chord is parallel
to the velocity at `y` as well or the second order functional vanishes, then the coefficient `c`
lies in `tcBad r ρ k` for some separation scale `k`. -/
lemma no_config_tc {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} {c : Coeff}
    (hS : IsSmoothKnot (pertV r c)) (hc : c ∈ Kv ρ) (h : ∀ k : ℕ, c ∉ tcBad r ρ k)
    {x y : ℝ} (hne : x ≠ y) (hlt : |y - x| < period)
    (h1 : cross3 (pertV r c y - pertV r c x) (velocity (pertV r c) x) = 0)
    (h2 : cross3 (pertV r c y - pertV r c x) (velocity (pertV r c) y) = 0 ∨
      inner ℝ (cross3 (velocity (pertV r c) x) (deriv (deriv (pertV r c)) x))
        (velocity (pertV r c) y) = 0) : False := by
  obtain ⟨x', y', hx'mem, hy'mem, hne', ⟨n, hnx⟩, ⟨m, hmy⟩⟩ := exists_reduce_tc hne hlt
  have hperV : Function.Periodic (pertV r c) period := pertV_periodic hr c
  have hperD : Function.Periodic (deriv (pertV r c)) period := periodic_deriv' hperV
  have hperD2 : Function.Periodic (deriv (deriv (pertV r c))) period := periodic_deriv' hperD
  have hPx : pertV r c x' = pertV r c x := by rw [hnx]; exact (hperV.zsmul n) x
  have hPy : pertV r c y' = pertV r c y := by rw [hmy]; exact (hperV.zsmul m) y
  have hVx : velocity (pertV r c) x' = velocity (pertV r c) x := by
    rw [hnx]; exact (hperD.zsmul n) x
  have hVy : velocity (pertV r c) y' = velocity (pertV r c) y := by
    rw [hmy]; exact (hperD.zsmul m) y
  have hAx : deriv (deriv (pertV r c)) x' = deriv (deriv (pertV r c)) x := by
    rw [hnx]; exact (hperD2.zsmul n) x
  have hchord_ne : pertV r c y' - pertV r c x' ≠ 0 := by
    intro hzero
    have hxy : pertV r c y' = pertV r c x' := sub_eq_zero.mp hzero
    exact hne' (hS.injective_on_period hy'mem hx'mem hxy).symm
  have h1' : cross3 (pertV r c y' - pertV r c x') (velocity (pertV r c) x') = 0 := by
    rw [hPy, hPx, hVx]; exact h1
  have h2' : cross3 (pertV r c y' - pertV r c x') (velocity (pertV r c) y') = 0 ∨
      inner ℝ (cross3 (velocity (pertV r c) x') (deriv (deriv (pertV r c)) x'))
        (velocity (pertV r c) y') = 0 := by
    rcases h2 with h2 | h2
    · exact Or.inl (by rw [hPy, hPx, hVy]; exact h2)
    · exact Or.inr (by rw [hVx, hAx, hVy]; exact h2)
  have hE1 : tcE1 r (c, tcPar x' y') = 0 := by
    rw [tcE1_tcPar_tc hr c x' y']; exact h1'
  have hE3 : tcE3 r (c, tcPar x' y') = 0 := by
    rw [tcE3_tcPar_tc hr c x' y']
    rcases h2' with h2 | h2
    · exact inner_cross3_of_parallel_tc hchord_ne h1' h2
    · exact h2
  have hpsi : tcPsi r (c, tcPar x' y') = 0 := by
    show (tcE1 r (c, tcPar x' y'), tcE3 r (c, tcPar x' y')) = (0, 0)
    rw [hE1, hE3]
  have hcsep : 0 < csep x' y' := csep_pos_of_mem_Ico_tc hx'mem hy'mem hne'
  obtain ⟨k, hk⟩ := exists_div_succ_le_tc hcsep
  refine h k ⟨hc, tcPar x' y',
    mem_tcKset_tcPar_tc ⟨hx'mem.1, le_of_lt hx'mem.2⟩ ⟨hy'mem.1, le_of_lt hy'mem.2⟩ hk,
    hpsi⟩

/-! ## The target -/

theorem tangentChordGP_of_no_tcBad {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) {ρ : ℝ} {c : Work.Drive.Coeff}
    (hS : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (Work.Drive.pertV r c))
    (hc : c ∈ Work.Drive.Kv ρ) (h : ∀ k : ℕ, c ∉ Work.Drive.tcBad r ρ k) :
    Work.Drive.TangentChordGP (Work.Drive.pertV r c) := by
  intro a b hab hbp
  have hlt : |b - a| < period := by
    rw [abs_of_pos hab]; exact hbp
  have hlt' : |a - b| < period := by rwa [abs_sub_comm] at hlt
  have hne : a ≠ b := by
    intro h
    rw [h, sub_self] at hab
    exact lt_irrefl 0 hab
  have hne' : b ≠ a := hne.symm
  constructor
  · intro hA
    constructor
    · intro hB
      exact no_config_tc hr hS hc h hne hlt hA (Or.inl hB)
    · intro hC
      exact no_config_tc hr hS hc h hne hlt hA (Or.inr hC)
  · intro hD
    constructor
    · intro hE
      exact no_config_tc hr hS hc h hne hlt hE (Or.inl hD)
    · intro hF
      have hD' : cross3 (pertV r c a - pertV r c b) (velocity (pertV r c) b) = 0 := by
        have hneg : pertV r c a - pertV r c b = -(pertV r c b - pertV r c a) := by abel
        rw [hneg, cross3_neg_left, hD, neg_zero]
      exact no_config_tc hr hS hc h hne' hlt' hD' (Or.inr hF)

end

end Work.Drive
