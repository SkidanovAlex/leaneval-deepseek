import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.count_walk_level
import Submission.Work.Pert.arith_theta
import Submission.Work.Pert.sum_le_of_count

/-!
# PERT · `Work.Pert.sum_inv_dist_gate_walk`

The harmonic (per-period) lattice sum along the gate walk: if `w : ℕ → ℂ` is a walk whose steps
are within `1/32` of `+1` and whose vertices lie in the gate `Qm Ξ α`, then

`∑_{j ≤ n} 1 / max ρ (dist (α * w j, ℤ)) ≤ 30 (1 + n ‖α‖) (1 + log (2 + n)) / ‖α‖`

for every `ρ ≥ ‖α‖`.

The mechanism is elementary and does not use the gate: `y j = Re (α * w j)` is a real walk whose
steps lie in `[(2/3)‖α‖, (33/32)‖α‖]` (because `InF1 α` means `|arg α| < π/4`), and the distance
of `α * w j` to the lattice `ℤ` is at least the distance of `y j` to `ℤ`.  Counting the visits to
the `s`-neighbourhood of `ℤ` (`Work.Pert.count_walk_level`) and applying a layer-cake argument
(`Work.Pert.sum_le_of_count`) yields the bound; the remaining real arithmetic is
`Work.Pert.arith_theta`.
-/

namespace Work.Pert

open scoped Classical

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The real lattice distance is at most the complex one -/

lemma infDist_re_le_iInf_lattice (x : ℂ) :
    Metric.infDist x.re (Set.range (fun k : ℤ => (k : ℝ))) ≤ ⨅ k : ℤ, dist x (k : ℂ) := by
  apply le_ciInf fun k => ?_
  refine le_trans (Metric.infDist_le_dist_of_mem ⟨k, rfl⟩) ?_
  rw [Real.dist_eq, dist_eq_norm]
  calc |x.re - (k : ℝ)| = |(x - (k : ℂ)).re| := by simp
    _ ≤ ‖x - (k : ℂ)‖ := Complex.abs_re_le_norm _

/-! ## The steps of `Re (α * w ·)` -/

/-- `InF1 α` gives `α.re ≥ (67/96)‖α‖`. -/
lemma InF1_re_ge {α : ℂ} (hInF1 : MandelDim.InF1 α) : (67 / 96 : ℝ) * ‖α‖ ≤ α.re := by
  have hInF1' : |α.im| < α.re := hInF1
  have hrepos : 0 < α.re := by linarith [abs_nonneg α.im]
  have him2 : α.im ^ 2 < α.re ^ 2 := by
    nlinarith [abs_nonneg α.im, sq_abs α.im, hInF1']
  have hnormsq : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq : ‖α‖ ^ 2 < 2 * α.re ^ 2 := by nlinarith [hnormsq, him2]
  have h67 : ((67 / 96 : ℝ) * ‖α‖) ^ 2 ≤ α.re ^ 2 := by nlinarith [hsq]
  have h := (sq_le_sq.mp h67)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 67 / 96),
    abs_of_nonneg (norm_nonneg α), abs_of_nonneg (le_of_lt hrepos)] at h
  linarith [h]

/-- The real part of `α * w j` is a walk with steps in `[(2/3)‖α‖, (33/32)‖α‖]`. -/
lemma re_alpha_step {α : ℂ} (hInF1 : MandelDim.InF1 α) {w : ℕ → ℂ} {n : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    ∀ j < n, (2 / 3) * ‖α‖ ≤ (α * w (j + 1)).re - (α * w j).re ∧
      (α * w (j + 1)).re - (α * w j).re ≤ (33 / 32) * ‖α‖ := by
  have hre_ge : (67 / 96 : ℝ) * ‖α‖ ≤ α.re := InF1_re_ge hInF1
  intro j hj
  set ε : ℂ := w (j + 1) - (w j + 1) with hε
  have hεle : ‖ε‖ ≤ 1 / 32 := by rw [hε]; exact hstep j hj
  have hdiff : (α * w (j + 1)).re - (α * w j).re = α.re + (α * ε).re := by
    have h1 : (α * w (j + 1) - α * w j).re = α.re + (α * ε).re := by
      have h2 : α * w (j + 1) - α * w j = α * ε + α := by rw [hε]; ring
      rw [h2]
      simp only [Complex.add_re, Complex.mul_re]
      ring
    rw [Complex.sub_re] at h1
    exact h1
  have hεbound : |(α * ε).re| ≤ ‖α‖ / 32 := by
    calc |(α * ε).re| ≤ ‖α * ε‖ := Complex.abs_re_le_norm _
      _ = ‖α‖ * ‖ε‖ := norm_mul α ε
      _ ≤ ‖α‖ * (1 / 32) := mul_le_mul_of_nonneg_left hεle (norm_nonneg α)
      _ = ‖α‖ / 32 := by ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp hεbound
  constructor
  · rw [hdiff]; linarith [hre_ge, hlo]
  · rw [hdiff]
    have h3 : α.re ≤ ‖α‖ := Complex.re_le_norm α
    linarith [hhi, h3]

/-! ## Elementary arithmetic helpers -/

lemma one_le_mul_one_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 : ℝ) ≤ (1 + a) * (1 + b) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  nlinarith

/-- The saturated case of the layer cake: the bound produced by `sum_le_of_count` is at most the
target. -/
lemma layer_arith {n : ℕ} {A B ρ r L₃ L : ℝ}
    (hr : 0 < r) (hρ : r ≤ ρ) (hA0 : 0 ≤ A) (hA : A ≤ 2 * (1 + (n : ℝ) * r))
    (hB : B = 3 / r) (hL₃ : L₃ ≤ 1 + L) (hL : 0 ≤ L) :
    A * (B * (2 + L₃) + 1 / ρ) + A * B ≤ 30 * (1 + (n : ℝ) * r) * (1 + L) / r := by
  subst hB
  have h1 : A / ρ ≤ A / r := div_le_div_of_nonneg_left hA0 hr hρ
  have h13 : (0 : ℝ) ≤ 13 + 3 * L := by linarith
  have hkey1 : A * (3 / r * (2 + L₃)) ≤ A * (3 / r * (3 + L)) := by
    have h : (3 / r) * (2 + L₃) ≤ (3 / r) * (3 + L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact mul_le_mul_of_nonneg_left h hA0
  have hkey2 : A * (3 / r * (3 + L)) + A / ρ + A * (3 / r) ≤ (A / r) * (13 + 3 * L) := by
    have e1 : A * (3 / r * (3 + L)) = (A / r) * (9 + 3 * L) := by ring
    have e2 : A * (3 / r) = (A / r) * 3 := by ring
    have e3 : (A / r) * (9 + 3 * L) + A / r + (A / r) * 3 = (A / r) * (13 + 3 * L) := by ring
    linarith [e1, e2, e3, h1]
  have hkey3 : (A / r) * (13 + 3 * L) ≤ ((2 * (1 + (n : ℝ) * r)) / r) * (13 + 3 * L) := by
    have h : A / r ≤ (2 * (1 + (n : ℝ) * r)) / r := div_le_div_of_nonneg_right hA (le_of_lt hr)
    exact mul_le_mul_of_nonneg_right h h13
  have hkey4 : ((2 * (1 + (n : ℝ) * r)) / r) * (13 + 3 * L)
      ≤ 30 * (1 + (n : ℝ) * r) * (1 + L) / r := by
    have e1 : ((2 * (1 + (n : ℝ) * r)) / r) * (13 + 3 * L)
        = (2 * (1 + (n : ℝ) * r) * (13 + 3 * L)) / r := by ring
    have e2 : 30 * (1 + (n : ℝ) * r) * (1 + L) / r
        = (30 * (1 + (n : ℝ) * r) * (1 + L)) / r := by ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (le_of_lt hr)
    have hbase : 0 ≤ 1 + (n : ℝ) * r := by positivity
    have : 2 * (13 + 3 * L) ≤ 30 * (1 + L) := by linarith
    nlinarith [hbase, hL]
  have hmain : A * (3 / r * (2 + L₃) + 1 / ρ) + A * (3 / r)
      ≤ (A / r) * (13 + 3 * L) := by
    have e : A * (3 / r * (2 + L₃) + 1 / ρ) + A * (3 / r)
        = A * (3 / r * (2 + L₃)) + A / ρ + A * (3 / r) := by ring
    rw [e]
    linarith [hkey1, hkey2]
  linarith [hmain, hkey3, hkey4]

/-! ## The main theorem -/

theorem sum_inv_dist_gate_walk {α : ℂ} {Ξ : ℝ} {w : ℕ → ℂ} {n : ℕ} {ρ : ℝ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hρ : ‖α‖ ≤ ρ)
    (hstep : ∀ j < n, ‖w (j+1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    (∑ j ∈ Finset.range (n+1), 1 / max ρ (⨅ k : ℤ, dist (α * w j) (k : ℂ)))
      ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + n)) / ‖α‖ := by
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : |α.im| < α.re := hInF1
    rw [h0] at h1
    simp at h1
  have hrpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hρpos : 0 < ρ := lt_of_lt_of_le hrpos hρ
  set y : ℕ → ℝ := fun j => (α * w j).re with hy
  set e : ℕ → ℝ := fun j => Metric.infDist (y j) (Set.range (fun k : ℤ => (k : ℝ))) with he
  have hde : ∀ j, e j ≤ ⨅ k : ℤ, dist (α * w j) (k : ℂ) := by
    intro j
    simp only [he, hy]
    exact infDist_re_le_iInf_lattice (α * w j)
  have hstep1 : (∑ j ∈ Finset.range (n+1), 1 / max ρ (⨅ k : ℤ, dist (α * w j) (k : ℂ)))
      ≤ ∑ j ∈ Finset.range (n+1), 1 / max ρ (e j) := by
    apply Finset.sum_le_sum
    intro j hj
    apply one_div_le_one_div_of_le (lt_of_lt_of_le hρpos (le_max_left ρ (e j)))
    exact max_le_max le_rfl (hde j)
  have htriv : (∑ j ∈ Finset.range (n+1), 1 / max ρ (e j)) ≤ ((n : ℝ) + 1) / ρ := by
    calc (∑ j ∈ Finset.range (n+1), 1 / max ρ (e j))
        ≤ ∑ j ∈ Finset.range (n+1), 1 / ρ := by
          apply Finset.sum_le_sum
          intro j hj
          exact one_div_le_one_div_of_le hρpos (le_max_left ρ (e j))
      _ = ((n : ℝ) + 1) / ρ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  -- the elementary two cases
  have htriv_target : ((n : ℝ) + 1) ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) →
      (∑ j ∈ Finset.range (n+1), 1 / max ρ (e j))
        ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖ := by
    intro hK
    have h1 : ((n : ℝ) + 1) / ρ ≤ ((n : ℝ) + 1) / ‖α‖ :=
      div_le_div_of_nonneg_left (by positivity) hrpos hρ
    have h2 : ((n : ℝ) + 1) / ‖α‖
        ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖ := by
      rw [div_le_div_iff_of_pos_right hrpos]
      exact hK
    linarith [htriv, h1, h2]
  by_cases hn2 : n ≤ 2
  · -- ## `n ≤ 2`
    refine hstep1.trans (htriv_target ?_)
    have hn2' : (n : ℝ) ≤ 2 := by exact_mod_cast hn2
    have hL : 0 ≤ Real.log (2 + (n : ℝ)) := Real.log_nonneg (by have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    have hone : (1 : ℝ) ≤ (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) :=
      one_le_mul_one_add (by positivity) hL
    have h30 : (30 : ℝ) ≤ 30 * ((1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ)))) := by
      nlinarith [hone]
    linarith
  · rcases lt_or_ge (1 / 2 : ℝ) ‖α‖ with hrbig | hrsmall
    · -- ## `1/2 < ‖α‖`
      refine hstep1.trans (htriv_target ?_)
      have hL : 0 ≤ Real.log (2 + (n : ℝ)) := Real.log_nonneg (by have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      have hone : (1 : ℝ) ≤ (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) :=
        one_le_mul_one_add (by positivity) hL
      have h2 : ((n : ℝ) + 1) / 2 ≤ 1 + (n : ℝ) * ‖α‖ := by nlinarith [hrbig]
      have h3 : 15 * ((n : ℝ) + 1) ≤ 30 * (1 + (n : ℝ) * ‖α‖) := by nlinarith [h2]
      have h4 : 30 * (1 + (n : ℝ) * ‖α‖)
          ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) := by
        have hnn : 0 ≤ (1 + (n : ℝ) * ‖α‖) := by positivity
        nlinarith [hnn, hL]
      linarith
    · -- ## `‖α‖ ≤ 1/2`, `n ≥ 3`
      have hn3 : 3 ≤ n := by omega
      have hn3' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      have hrle : ‖α‖ ≤ 1 / 2 := hrsmall
      set c₀ : ℝ := (2 / 3) * ‖α‖ with hc0
      set c₁ : ℝ := (33 / 32) * ‖α‖ with hc1
      have hc0pos : 0 < c₀ := by rw [hc0]; positivity
      have hc1pos : 0 < c₁ := by rw [hc1]; positivity
      set A : ℝ := (n : ℝ) * c₁ + 2 with hAdef
      set B : ℝ := 2 / c₀ with hBdef
      have hA1 : 1 ≤ A := by
        rw [hAdef]
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hn0, hc1pos]
      have hA0 : 0 ≤ A := le_of_lt (by linarith [hA1])
      have hBpos : 0 < B := by rw [hBdef]; positivity
      have hAB : B = 3 / ‖α‖ := by rw [hBdef, hc0]; field_simp
      have hBH : 3 ≤ B * ρ := by
        rw [hAB]
        have h1 : (3 : ℝ) / ‖α‖ * ‖α‖ = 3 := by field_simp
        have h2 : (3 : ℝ) / ‖α‖ * ‖α‖ ≤ (3 : ℝ) / ‖α‖ * ρ :=
          mul_le_mul_of_nonneg_left hρ (by positivity)
        linarith
      have hy_step : ∀ j < n, c₀ ≤ y (j + 1) - y j ∧ y (j + 1) - y j ≤ c₁ := by
        intro j hj
        have h := re_alpha_step hInF1 hstep j hj
        simp only [hy, hc0, hc1]
        exact h
      have hcount : ∀ t : ℝ, 0 < t →
          (((Finset.range (n+1)).filter (fun j => e j ≤ t)).card : ℝ) ≤ A * (B * t + 1) := by
        intro t ht
        by_cases ht2 : t ≤ 1 / 2
        · have h := count_walk_level (m := y) (c₀ := c₀) (c₁ := c₁) (s := t) (n := n)
            hc0pos ht ht2 hy_step
          have hB' : B * t + 1 = 2 * t / c₀ + 1 := by rw [hBdef]; ring
          rw [hAdef, hB']
          exact h
        · have ht' : (1 : ℝ) / 2 ≤ t := by linarith [not_le.mp ht2]
          have hcard : (((Finset.range (n+1)).filter (fun j => e j ≤ t)).card : ℝ)
              ≤ (n : ℝ) + 1 := by
            have h1 := Finset.card_le_card
              (Finset.filter_subset (fun j => e j ≤ t) (Finset.range (n+1)))
            simp only [Finset.card_range] at h1
            exact_mod_cast h1
          have hbig : (n : ℝ) + 1 ≤ A * (B * t + 1) := by
            have hc1c0 : c₁ / c₀ = 99 / 64 := by rw [hc1, hc0]; field_simp; norm_num
            have hBt : (1 : ℝ) / c₀ ≤ B * t := by
              have h1 : B * (1 / 2) ≤ B * t := mul_le_mul_of_nonneg_left ht' (le_of_lt hBpos)
              have h2 : B * (1 / 2) = 1 / c₀ := by rw [hBdef]; ring
              linarith
            have hAc : (n : ℝ) * c₁ ≤ A := by rw [hAdef]; linarith
            have hprod : (n : ℝ) * (c₁ / c₀) ≤ A * (B * t + 1) := by
              calc (n : ℝ) * (c₁ / c₀) = (n : ℝ) * c₁ * (1 / c₀) := by ring
                _ ≤ A * (1 / c₀) := mul_le_mul_of_nonneg_right hAc (by positivity)
                _ ≤ A * (B * t) := mul_le_mul_of_nonneg_left hBt hA0
                _ ≤ A * (B * t + 1) := by
                    apply mul_le_mul_of_nonneg_left _ hA0
                    linarith
            have hnc : (n : ℝ) + 1 ≤ (n : ℝ) * (c₁ / c₀) := by
              rw [hc1c0]; nlinarith [hn3']
            linarith
          linarith
      by_cases hsat : A * (B * ρ + 1) ≤ (n : ℝ) + 1
      · -- ## saturated: layer cake
        have hsat' : A * (B * ρ + 1) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; exact hsat
        have hsc := sum_le_of_count (K := n+1) (d := e) (A := A) (B := B) (H := ρ)
          hA1 hBpos hρpos hBH
          (fun i hi => by simp only [he]; exact Metric.infDist_nonneg)
          hcount hsat'
        have hKc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hKc] at hsc
        have hL : 0 ≤ Real.log (2 + (n : ℝ)) := Real.log_nonneg (by have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
        have hlog3 : Real.log (2 + ((n : ℝ) + 1)) ≤ 1 + Real.log (2 + (n : ℝ)) := by
          have h2 : 2 + ((n : ℝ) + 1) ≤ 2 * (2 + (n : ℝ)) := by
            have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith
          calc Real.log (2 + ((n : ℝ) + 1)) ≤ Real.log (2 * (2 + (n : ℝ))) :=
                Real.log_le_log (by positivity) h2
            _ = Real.log 2 + Real.log (2 + (n : ℝ)) :=
                Real.log_mul (by norm_num) (by positivity)
            _ ≤ 1 + Real.log (2 + (n : ℝ)) := by
                have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
        have hA2 : A ≤ 2 * (1 + (n : ℝ) * ‖α‖) := by
          rw [hAdef, hc1]
          have hnn : 0 ≤ (n : ℝ) * ‖α‖ := by positivity
          nlinarith
        have hfin := layer_arith (n := n) (A := A) (B := B) (ρ := ρ) (r := ‖α‖)
          (L₃ := Real.log (2 + ((n : ℝ) + 1))) (L := Real.log (2 + (n : ℝ)))
          hrpos hρ hA0 hA2 hAB hlog3 hL
        exact hstep1.trans (hsc.trans hfin)
      · -- ## unsaturated: the trivial bound plus `arith_theta`
        have hlt : (n : ℝ) + 1 < A * (B * ρ + 1) := lt_of_not_ge hsat
        have hABpos : 0 < A * B := mul_pos (by linarith [hA1]) hBpos
        have hKApos : 0 < (n : ℝ) + 1 - A := by
          rw [hAdef, hc1]; nlinarith [hn3', hrle]
        have hρgt : ((n : ℝ) + 1 - A) / (A * B) < ρ := by
          rw [div_lt_iff₀ hABpos]
          nlinarith [hlt]
        have hmain : (∑ j ∈ Finset.range (n+1), 1 / max ρ (e j))
            ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖ := by
          have h1 : ((n : ℝ) + 1) / ρ
              < ((n : ℝ) + 1) * (A * B) / ((n : ℝ) + 1 - A) := by
            have h := div_lt_div_of_pos_left (by positivity : (0 : ℝ) < (n : ℝ) + 1)
              (div_pos hKApos hABpos) hρgt
            have e : ((n : ℝ) + 1) / (((n : ℝ) + 1 - A) / (A * B))
                = ((n : ℝ) + 1) * (A * B) / ((n : ℝ) + 1 - A) := by
              rw [div_div_eq_mul_div]
            rwa [e] at h
          have h2 : ((n : ℝ) + 1) * (A * B) / ((n : ℝ) + 1 - A)
              = 3 * A * ((n : ℝ) + 1) / (((n : ℝ) + 1 - A) * ‖α‖) := by
            rw [hAB]
            field_simp
          have h3 : 3 * A * ((n : ℝ) + 1) / (((n : ℝ) + 1 - A) * ‖α‖)
              ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖ := by
            have harith := arith_theta (n := n) hn3 (r := ‖α‖) hrpos hrle
            rw [← hc1, ← hAdef] at harith
            have hmid : 3 * A * ((n : ℝ) + 1) / ((n : ℝ) + 1 - A)
                ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) := by
              rw [div_le_iff₀ hKApos]
              nlinarith [harith]
            have e : 3 * A * ((n : ℝ) + 1) / (((n : ℝ) + 1 - A) * ‖α‖)
                = (3 * A * ((n : ℝ) + 1) / ((n : ℝ) + 1 - A)) / ‖α‖ := by rw [div_div]
            rw [e]
            exact div_le_div_of_nonneg_right hmid (le_of_lt hrpos)
          calc (∑ j ∈ Finset.range (n+1), 1 / max ρ (e j)) ≤ ((n : ℝ) + 1) / ρ := htriv
            _ ≤ ((n : ℝ) + 1) * (A * B) / ((n : ℝ) + 1 - A) := le_of_lt h1
            _ = 3 * A * ((n : ℝ) + 1) / (((n : ℝ) + 1 - A) * ‖α‖) := h2
            _ ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖ := h3
        exact hstep1.trans hmain

end

end Work.Pert
