import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.uhCoeff_bound
import Submission.Work.A14D.uh_hasSum
import Submission.Work.A14D.uhRatio_tendsto
import Submission.Work.C17g.pringsheim

/-!
# A14D — `u_h` is not holomorphic at `x = 1/9`

`uh z = Σₙ aₙ (1−z)ⁿ` is the holomorphic solution of Zagier's operator `L` at `x = 1`
(`Submission.Work.A14.defs`, `Submission.Work.A14D.uhCoeff_bound`).  Its Taylor series at
`x = 1` has radius of convergence exactly `8/9 = |1 − 1/9|`: the coefficients are positive,
`a_{n+1} ≤ (9/8)aₙ` (so the series converges on `|1−z| < 8/9`), and the ratio `a_{n+1}/aₙ`
tends to `9/8` (`Work.A14D.uhRatio_tendsto`), so the terms `aₙ ρⁿ` do not tend to `0` for any
`ρ > 8/9`.  Consequently `Σ aₙ wⁿ` cannot be extended holomorphically past `w = 8/9`:
this is Vivanti–Pringsheim (`Work.C17g.pringsheim`).  Translating back, `uh` has no
holomorphic extension to any neighbourhood of `z = 1/9`, which is the statement below.

Everything is elementary: only the coefficient estimates and Pringsheim's theorem are used
(no ODE theory).
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

/-! ## 1. The coefficients: positivity and geometric bounds -/

/-- All coefficients of `u_h` are positive (in `ℝ`). -/
lemma uhCoeff_posR (n : ℕ) : (0 : ℝ) < (uhCoeff n : ℝ) := by
  have h := uhCoeff_bound.1 n
  exact_mod_cast h

/-- The ratio bound `a_{n+1} ≤ (9/8) aₙ`, cast to `ℝ`. -/
lemma uhCoeff_succ_leR (n : ℕ) : (uhCoeff (n + 1) : ℝ) ≤ 9 / 8 * (uhCoeff n : ℝ) := by
  have h := uhCoeff_bound.2.1 n
  have h2 : ((uhCoeff (n + 1) : ℚ) : ℝ) ≤ ((9 / 8 : ℚ) * uhCoeff n : ℚ) := by exact_mod_cast h
  simpa using h2

/-- `aₙ ≤ a₀ (9/8)ⁿ`. -/
lemma uhCoeff_le_geomR (n : ℕ) : (uhCoeff n : ℝ) ≤ (uhCoeff 0 : ℝ) * (9 / 8) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc (uhCoeff (k + 1) : ℝ) ≤ 9 / 8 * (uhCoeff k : ℝ) := uhCoeff_succ_leR k
      _ ≤ 9 / 8 * ((uhCoeff 0 : ℝ) * (9 / 8) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (uhCoeff 0 : ℝ) * (9 / 8) ^ (k + 1) := by ring

/-! ## 2. The two halves of the radius of convergence -/

/-- The series `Σ aₙ rⁿ` converges for `0 ≤ r < 8/9`. -/
lemma summable_uhCoeff_geomR (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 8 / 9) :
    Summable (fun n : ℕ => (uhCoeff n : ℝ) * r ^ n) := by
  have hgeom : Summable (fun n : ℕ => (uhCoeff 0 : ℝ) * ((9 / 8) * r) ^ n) := by
    refine Summable.mul_left _ (summable_geometric_of_norm_lt_one ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
  · exact mul_nonneg (le_of_lt (uhCoeff_posR n)) (pow_nonneg hr0 n)
  · rw [mul_pow]
    calc (uhCoeff n : ℝ) * r ^ n ≤ ((uhCoeff 0 : ℝ) * (9 / 8) ^ n) * r ^ n :=
          mul_le_mul_of_nonneg_right (uhCoeff_le_geomR n) (pow_nonneg hr0 n)
      _ = (uhCoeff 0 : ℝ) * ((9 / 8) ^ n * r ^ n) := by ring

/-- The series `Σ aₙ ρⁿ` diverges for `ρ > 8/9`: the ratios of successive terms tend to
`(9/8)ρ > 1`, so the terms do not tend to `0`. -/
lemma not_summable_uhCoeff_geomR (ρ : ℝ) (hρ : 8 / 9 < ρ) :
    ¬ Summable (fun n : ℕ => (uhCoeff n : ℝ) * ρ ^ n) := by
  intro hsumm
  have hρpos : 0 < ρ := by linarith
  have hu_pos : ∀ n : ℕ, 0 < (uhCoeff n : ℝ) * ρ ^ n := fun n =>
    mul_pos (uhCoeff_posR n) (pow_pos hρpos n)
  -- the amount by which the term ratio exceeds `1`
  set η : ℝ := (ρ * (9 / 8) - 1) / 2 with hη
  have hηpos : 0 < η := by rw [hη]; nlinarith
  -- the ratio `a_{n+1}/aₙ` is eventually `> (1+η)/ρ`
  have hε0 : 0 < 9 / 16 - 1 / (2 * ρ) := by
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨N, hN⟩ := uhRatio_tendsto (9 / 16 - 1 / (2 * ρ)) hε0
  have hratio : ∀ n ≥ N, 1 + η ≤ ρ * ((uhCoeff (n + 1) : ℝ) / (uhCoeff n : ℝ)) := by
    intro n hn
    have h := (abs_lt.1 (hN n hn)).1
    have hkey : ρ * (9 / 8 - (9 / 16 - 1 / (2 * ρ))) = 1 + η := by rw [hη]; field_simp; ring
    nlinarith [h, hρpos]
  -- the terms grow geometrically along the tail
  set u : ℕ → ℝ := fun n => (uhCoeff n : ℝ) * ρ ^ n with hu
  have huN : 0 < u N := hu_pos N
  have hstep : ∀ n ≥ N, (1 + η) * u n ≤ u (n + 1) := by
    intro n hn
    have hr := hratio n hn
    have hnz : (uhCoeff n : ℝ) ≠ 0 := ne_of_gt (uhCoeff_posR n)
    have heq : u (n + 1) = (ρ * ((uhCoeff (n + 1) : ℝ) / (uhCoeff n : ℝ))) * u n := by
      rw [hu]; simp only; field_simp; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hr (le_of_lt (hu_pos n))
  have h0 : Tendsto u atTop (nhds 0) := by
    rw [hu]; exact hsumm.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, u n < u N := (tendsto_order.1 h0).2 (u N) huN
  obtain ⟨N', hN'⟩ := eventually_atTop.1 hev
  set k : ℕ := max N' N - N + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hNk : N' ≤ N + k := by omega
  have hgrowth : ∀ j : ℕ, (1 + η) ^ j * u N ≤ u (N + j) := by
    intro j
    induction j with
    | zero => simp
    | succ i ih =>
      calc (1 + η) ^ (i + 1) * u N = (1 + η) * ((1 + η) ^ i * u N) := by ring
        _ ≤ (1 + η) * u (N + i) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ u (N + i + 1) := hstep (N + i) (by omega)
        _ = u (N + (i + 1)) := by ring_nf
  have h2 := hgrowth k
  have h3 : 1 < (1 + η) ^ k := one_lt_pow₀ (by linarith) (by omega)
  have h4 : u N < (1 + η) ^ k * u N := by nlinarith
  have h5 : u (N + k) < u N := hN' (N + k) hNk
  linarith

/-! ## 3. `u_h` has no holomorphic extension to a neighbourhood of `1/9` -/

theorem uh_not_holo_at_ninth : ¬ ∃ (g : ℂ → ℂ) (δ : ℝ), 0 < δ ∧ DifferentiableOn ℂ g (ball ninth δ) ∧ ∀ z ∈ ball ninth δ ∩ ball (1 : ℂ) (8 / 9), g z = uh z := by
  rintro ⟨g, δ, hδpos, hgd, hgeq⟩
  -- transport to the variable `w = 1 - z`, so that `1/9 ↦ 8/9`
  set G : ℂ → ℂ := fun t => g (1 - t) with hG
  have hGd : DifferentiableOn ℂ G (ball ((8 / 9 : ℝ) : ℂ) δ) := by
    rw [hG]
    have h : (fun t : ℂ => g (1 - t)) = g ∘ (fun t => (1 : ℂ) - t) := rfl
    rw [h]
    refine hgd.comp ?_ ?_
    · exact (differentiableOn_const (1 : ℂ)).sub differentiableOn_id
    · intro t ht
      rw [mem_ball] at ht ⊢
      change dist ((1 : ℂ) - t) ninth < δ
      have h2 : ((1 : ℂ) - t) - ninth = -(t - ((8 / 9 : ℝ) : ℂ)) := by
        rw [ninth]; push_cast; ring
      rw [dist_eq_norm, h2, norm_neg]
      simpa [dist_eq_norm] using ht
  -- `G` agrees with the coefficient series on the overlap
  have hfg : ∀ z ∈ ball ((8 / 9 : ℝ) : ℂ) δ ∩ ball (0 : ℂ) (8 / 9),
      HasSum (fun n => ((uhCoeff n : ℝ) : ℂ) * z ^ n) (G z) := by
    intro z hz
    obtain ⟨hzδ, hz0⟩ := hz
    rw [mem_ball] at hzδ hz0
    have hwδ : (1 - z) ∈ ball ninth δ := by
      rw [mem_ball]
      have h2 : (1 : ℂ) - z - ninth = -(z - ((8 / 9 : ℝ) : ℂ)) := by
        rw [ninth]; push_cast; ring
      rw [dist_eq_norm, h2, norm_neg]
      simpa [dist_eq_norm] using hzδ
    have hw1 : (1 - z) ∈ ball (1 : ℂ) (8 / 9) := by
      rw [mem_ball]
      have h2 : (1 : ℂ) - z - 1 = -z := by ring
      rw [dist_eq_norm, h2, norm_neg]
      simpa [dist_eq_norm] using hz0
    have hgz : g (1 - z) = uh (1 - z) := hgeq (1 - z) ⟨hwδ, hw1⟩
    have hGz : G z = g (1 - z) := by rw [hG]
    rw [hGz, hgz]
    have hz9 : ‖z‖ < 8 / 9 := by simpa [dist_eq_norm] using hz0
    have hsum := uh_hasSum z hz9
    have hcast : ∀ n : ℕ, ((uhCoeff n : ℝ) : ℂ) = (uhCoeff n : ℂ) := fun n => by norm_num
    have hfuneq : (fun n : ℕ => (uhCoeff n : ℂ) * z ^ n)
        = (fun n : ℕ => ((uhCoeff n : ℝ) : ℂ) * z ^ n) := by
      funext n; rw [hcast n]
    rwa [hfuneq] at hsum
  -- Vivanti–Pringsheim
  obtain ⟨ρ, hρgt, hρsumm⟩ :=
    Work.C17g.pringsheim (fun n => (uhCoeff n : ℝ)) (fun n => le_of_lt (uhCoeff_posR n))
      (8 / 9) (by norm_num) (fun r h0 hr => summable_uhCoeff_geomR r h0 hr)
      G δ hδpos hGd hfg
  exact not_summable_uhCoeff_geomR ρ hρgt hρsumm

end Work.A14D
