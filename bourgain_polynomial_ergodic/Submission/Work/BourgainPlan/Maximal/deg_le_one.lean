import Mathlib
import Submission.Work.BourgainPlan.Maximal.foundations
import Submission.Work.Analysis.HardyLittlewood.ap_maximal_lp

open Finset MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Work.BourgainPlan.Maximal

open Submission.BourgainPlan (discAvg NonnegOnNat)

/-- **The maximal inequality for polynomials of degree `≤ 1`.**  For `P : ℤ[X]` with
`P.natDegree ≤ 1` and `P ≥ 0` on `ℕ`, the discrete maximal inequality holds for every `1 < p`.

Route: such a `P` is `C b + C k * X` with `0 ≤ b, k` (from `NonnegOnNat` and `natDegree ≤ 1`, via
`Polynomial.eval_eq_sum_range`), so `(P.eval i).toNat = b.toNat + k.toNat * i` for `i ≥ 0`, and
`discAvg P N g n = (N)⁻¹ ∑_{i<N} g (n + (k.toNat * i + b.toNat))` by `discAvg_eq_sum` — an
arithmetic-progression average of step `k.toNat` and offset `b.toNat` (the case `k = 0` being a pure
shift of `g`).  Apply `Work.Analysis.HardyLittlewood.ap_maximal_lp` when `k ≠ 0`, and the
translation invariance of `Measure.count` (e.g. `ENNReal.tsum_comp_le_tsum_of_injective`) when
`k = 0`. -/
theorem deg_le_one (P : Polynomial ℤ) (hP : Submission.BourgainPlan.NonnegOnNat P)
    (hdeg : P.natDegree ≤ 1) :
    ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
        ∫⁻ n, (⨆ N : ℕ, ‖Submission.BourgainPlan.discAvg P N g n‖ₑ) ^ p
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  -- Write `P = C c1 * X + C c0`.
  obtain ⟨c1, c0, hPc⟩ :
      ∃ c1 c0 : ℤ, P = Polynomial.C c1 * Polynomial.X + Polynomial.C c0 :=
    ⟨P.coeff 1, P.coeff 0, Polynomial.eq_X_add_C_of_natDegree_le_one hdeg⟩
  have hc0 : 0 ≤ c0 := by
    have h := hP 0
    rw [hPc] at h
    simpa using h
  -- Nonnegativity on `ℕ` forces the slope to be nonnegative.
  have hc1 : 0 ≤ c1 := by
    by_contra hcon
    have hlt : c1 ≤ -1 := by omega
    have h := hP (c0.natAbs + 1)
    rw [hPc] at h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
    have hmpos : (0 : ℤ) ≤ (((c0.natAbs + 1 : ℕ)) : ℤ) := by positivity
    have h1 : c1 * (((c0.natAbs + 1 : ℕ)) : ℤ) ≤ -((((c0.natAbs + 1 : ℕ)) : ℤ)) := by
      have := mul_le_mul_of_nonneg_right hlt hmpos
      simpa using this
    have h2 : c0 ≤ (c0.natAbs : ℤ) := Int.le_natAbs
    have hmcast : (((c0.natAbs + 1 : ℕ)) : ℤ) = (c0.natAbs : ℤ) + 1 := by push_cast; ring
    linarith
  -- The value of `P` at a natural number.
  have heval : ∀ i : ℕ, (P.eval (i : ℤ)).toNat = c1.toNat * i + c0.toNat := by
    intro i
    have hev : P.eval (i : ℤ) = c1 * (i : ℤ) + c0 := by rw [hPc]; simp
    rw [hev]
    have hcast : c1 * (i : ℤ) + c0 = ((c1.toNat * i + c0.toNat : ℕ) : ℤ) := by
      have e1 : (((c1.toNat : ℕ)) : ℤ) = c1 := Int.toNat_of_nonneg hc1
      have e0 : (((c0.toNat : ℕ)) : ℤ) = c0 := Int.toNat_of_nonneg hc0
      calc c1 * (i : ℤ) + c0
          = (((c1.toNat : ℕ)) : ℤ) * (i : ℤ) + (((c0.toNat : ℕ)) : ℤ) := by rw [e1, e0]
        _ = ((c1.toNat * i + c0.toNat : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  -- `discAvg` in arithmetic-progression form.
  have hdisc : ∀ (g : ℕ → ℝ) (N n : ℕ),
      discAvg P N g n
        = (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (n + (c1.toNat * i + c0.toNat)) := by
    intro g N n
    rw [discAvg_eq_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [heval i])
  intro p hp
  rcases Nat.eq_zero_or_pos c1.toNat with hzero | hpos
  · -- Degenerate case: `P` is constant, the average is a pure shift of `g`.
    refine ⟨1, zero_le_one, fun g _ => ?_⟩
    have hsup : ∀ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) = ‖g (n + c0.toNat)‖ₑ := by
      intro n
      apply le_antisymm
      · apply iSup_le; intro N
        rw [hdisc g N n]
        have hsum : ∑ i ∈ Finset.range N, g (n + (c1.toNat * i + c0.toNat))
            = (N : ℝ) * g (n + c0.toNat) := by
          rw [Finset.sum_congr rfl (fun i _ => by rw [hzero, Nat.zero_mul, Nat.zero_add]),
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [hsum]
        rcases Nat.eq_zero_or_pos N with hN | hN
        · subst hN; simp
        · rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hN.ne')]
      · have hle := le_iSup (fun N : ℕ => ‖discAvg P N g n‖ₑ) 1
        rw [hdisc g 1 n] at hle
        simpa [hzero] using hle
    calc ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂MeasureTheory.Measure.count
        = ∫⁻ n, ‖g (n + c0.toNat)‖ₑ ^ p ∂MeasureTheory.Measure.count :=
          MeasureTheory.lintegral_congr (fun n => by rw [hsup n])
      _ = ∑' n : ℕ, ‖g (n + c0.toNat)‖ₑ ^ p := by rw [MeasureTheory.lintegral_count]
      _ ≤ ∑' n : ℕ, ‖g n‖ₑ ^ p :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => n + c0.toNat)
            (fun a _ hab => Nat.add_right_cancel hab) (fun m => ‖g m‖ₑ ^ p)
      _ = ENNReal.ofReal ((1 : ℝ) ^ p)
            * ∫⁻ n, ‖g n‖ₑ ^ p ∂MeasureTheory.Measure.count := by
          rw [Real.one_rpow, MeasureTheory.lintegral_count, ENNReal.ofReal_one, one_mul]
  · -- Nondegenerate case: an arithmetic-progression average.
    obtain ⟨C, hCpos, hC⟩ :=
      Work.Analysis.HardyLittlewood.ap_maximal_lp hp c1.toNat c0.toNat hpos
    refine ⟨C, hCpos.le, fun g hg => ?_⟩
    have hpt : ∀ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p
        = (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
            g (n + (c1.toNat * i + c0.toNat))‖ₑ) ^ p := by
      intro n
      rw [show (⨆ N : ℕ, ‖discAvg P N g n‖ₑ)
            = (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
                g (n + (c1.toNat * i + c0.toNat))‖ₑ)
          from iSup_congr (fun N => by rw [hdisc g N n])]
    calc ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂MeasureTheory.Measure.count
        = ∫⁻ n, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
            g (n + (c1.toNat * i + c0.toNat))‖ₑ) ^ p ∂MeasureTheory.Measure.count :=
          MeasureTheory.lintegral_congr (fun n => hpt n)
      _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂MeasureTheory.Measure.count := hC g hg

end Work.BourgainPlan.Maximal
