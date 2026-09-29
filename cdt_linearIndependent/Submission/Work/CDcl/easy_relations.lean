import Mathlib
import Submission.Work.CDcl.ifc
import Submission.Work.CDcl.rowdefs
import Submission.Work.CDcl.b_rows

/-! Guidance from the requester (Area CDCl of `cdt_linearIndependent`):

# The easy half of `CDClosed`: `d/dy` of the 16 functions other than `G'''`

`Submission.CDTPlan.CDClosed` says that the ℚ(y)-span of the 17 functions
`Submission.CDTPlan.seventeen m n ra rb rab r0` (paper order:
`B₁,B₂,B₃,B₄,B₅,G,G',G'',G''',B₆,B₇,∫yG,∫G,∫(G−G(0))/y,…,∫(G−jet₃)/y⁴`) is closed under `d/dy`.
This request covers every index except `i = 8` (index 8 is `G'''`; its derivative `G''''` needs the
order-4 ODE, proved separately in `Work.CDcl.x_relation` + the assembly).

Statement: for every admissible `m n` there are a nonzero `q ∈ ℚ[y]` and polynomial coefficients
`A i j` such that for all `i ≠ 8`, `q * (seventeen i)' = Σ_j A i j * seventeen j` as power series.
One `q` must serve all `i`, so take e.g. `q = X^4 * q₀` with `q₀ ≠ 0` from `DClosed pureB`
(ℚ[y] is a domain, so this is nonzero).

Route implemented below: the rows of the coefficient matrix `AOf q₀ A₀ G`
(`Submission.Work.CDcl.rowdefs`) are

* `0..4, 9, 10` (`B₁..B₅, B₆, B₇`): the rescaled `D`-closure data of `pureB`
  (`Submission.Work.CDcl.b_rows`);
* `5,6,7` (`G, G', G''`): the next function `G', G'', G'''` (`er_G_row` below);
* `11,12` (`∫yG`, `∫G`): `y·G` and `G` (`er_int_row`, from `derivative (intY f) = f`);
* `13..16` (`∫(G − jet_k)/y^k`): `tq k G = (G − jet_k)/y^k`, and `X^k · tq k G = G − jet k G`
  (`er_tq_row`, from `X_pow_mul_tq`).

This covers every index except `8`; index `8` is `G'''` and its derivative `G''''` needs the
order-4 ODE, which is not part of this statement.
-/

namespace Work.CDcl

open PowerSeries Polynomial

noncomputable section

/-! ## The `G`-rows (`i = 5,6,7`): the derivative is the next function -/

/-- Row `k` (`k = 5,6,7`, i.e. `G, G', G''`): `d/dy G^{(k-5)} = G^{(k-4)}`. -/
lemma er_G_row (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (m n : ℕ)
    (ra rb rab r0 : ℤ) (k : ℕ) (hk : k = 5 ∨ k = 6 ∨ k = 7) :
    (qOf q0 : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0 ⟨k, by omega⟩)
      = ∑ j, (AOf q0 A0 (Submission.CDTPlan.GC m n ra rb rab r0) ⟨k, by omega⟩ j : PowerSeries ℚ) *
          Submission.CDTPlan.seventeen m n ra rb rab r0 j := by
  rcases hk with rfl | rfl | rfl
  · rw [show (⟨5, by omega⟩ : Fin 17) = 5 from rfl,
      show PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0 (5 : Fin 17))
        = Submission.CDTPlan.seventeen m n ra rb rab r0 (6 : Fin 17) from rfl]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, Submission.CDTPlan.seventeen]
  · rw [show (⟨6, by omega⟩ : Fin 17) = 6 from rfl,
      show PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0 (6 : Fin 17))
        = Submission.CDTPlan.seventeen m n ra rb rab r0 (7 : Fin 17) from rfl]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, Submission.CDTPlan.seventeen]
  · rw [show (⟨7, by omega⟩ : Fin 17) = 7 from rfl,
      show PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0 (7 : Fin 17))
        = Submission.CDTPlan.seventeen m n ra rb rab r0 (8 : Fin 17) from rfl]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, Submission.CDTPlan.seventeen]

/-! ## The integral rows (`i = 11,12`): `(∫yG)' = yG`, `(∫G)' = G` -/

/-- Rows `11` and `12`: `d/dy (∫ yG) = yG` and `d/dy (∫G) = G`. -/
lemma er_int_row (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (m n : ℕ)
    (ra rb rab r0 : ℤ) (k : ℕ) (hk : k = 11 ∨ k = 12) :
    (qOf q0 : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0 ⟨k, by omega⟩)
      = ∑ j, (AOf q0 A0 (Submission.CDTPlan.GC m n ra rb rab r0) ⟨k, by omega⟩ j : PowerSeries ℚ) *
          Submission.CDTPlan.seventeen m n ra rb rab r0 j := by
  rcases hk with rfl | rfl
  · rw [show (⟨11, by omega⟩ : Fin 17) = 11 from rfl,
      show Submission.CDTPlan.seventeen m n ra rb rab r0 (11 : Fin 17)
        = Submission.CDTPlan.intY (PowerSeries.X * Submission.CDTPlan.GC m n ra rb rab r0) from rfl,
      derivative_intY]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, Submission.CDTPlan.seventeen]
    ring_nf
  · rw [show (⟨12, by omega⟩ : Fin 17) = 12 from rfl,
      show Submission.CDTPlan.seventeen m n ra rb rab r0 (12 : Fin 17)
        = Submission.CDTPlan.intY (Submission.CDTPlan.GC m n ra rb rab r0) from rfl,
      derivative_intY]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, Submission.CDTPlan.seventeen]

/-! ## The rows `13..16`: `(∫ (G − jet_k G)/y^k)' = (G − jet_k G)/y^k` -/

/-- `X^4·q₀ · tq k f = X^{4-k}·q₀ · (f − jet_k f)` for `k ≤ 4`. -/
lemma er_qOf_mul_tq (q0 : Polynomial ℚ) (k : ℕ) (hk : k ≤ 4) (f : PowerSeries ℚ) :
    (qOf q0 : PowerSeries ℚ) * Submission.CDTPlan.tq k f
      = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (q0 : PowerSeries ℚ)
          * (f - (jet k f : PowerSeries ℚ)) := by
  have hcast : (qOf q0 : PowerSeries ℚ) =
      (PowerSeries.X : PowerSeries ℚ) ^ 4 * (q0 : PowerSeries ℚ) := by
    simp [qOf, Polynomial.coe_mul]
  calc (qOf q0 : PowerSeries ℚ) * Submission.CDTPlan.tq k f
      = (PowerSeries.X : PowerSeries ℚ) ^ 4 * (q0 : PowerSeries ℚ)
          * Submission.CDTPlan.tq k f := by rw [hcast]
    _ = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (PowerSeries.X : PowerSeries ℚ) ^ k
          * (q0 : PowerSeries ℚ) * Submission.CDTPlan.tq k f := by
        rw [show (PowerSeries.X : PowerSeries ℚ) ^ 4
              = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (PowerSeries.X : PowerSeries ℚ) ^ k from by
            conv_lhs => rw [show (4 : ℕ) = (4 - k) + k from by omega, pow_add]]
    _ = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (q0 : PowerSeries ℚ)
          * ((PowerSeries.X : PowerSeries ℚ) ^ k * Submission.CDTPlan.tq k f) := by ring
    _ = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (q0 : PowerSeries ℚ)
          * (f - (jet k f : PowerSeries ℚ)) := by rw [X_pow_mul_tq]

/-- Rows `13..16` (`k = 1..4`): `d/dy (∫ (G − jet_k G)/y^k) = (G − jet_k G)/y^k`, and
`X^k·(G − jet_k G)/y^k = G − jet_k G` absorbs the powers of `y` into the common denominator
`q = X^4 q₀`. -/
lemma er_tq_row (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (m n : ℕ)
    (ra rb rab r0 : ℤ) (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (qOf q0 : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ)
          (Submission.CDTPlan.seventeen m n ra rb rab r0 ⟨12 + k, by omega⟩)
      = ∑ j, (AOf q0 A0 (Submission.CDTPlan.GC m n ra rb rab r0) ⟨12 + k, by omega⟩ j :
            PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 j := by
  interval_cases k
  · rw [show (⟨12 + 1, by omega⟩ : Fin 17) = 13 from rfl,
      show Submission.CDTPlan.seventeen m n ra rb rab r0 (13 : Fin 17)
        = Submission.CDTPlan.intY (Submission.CDTPlan.tq 1 (Submission.CDTPlan.GC m n ra rb rab r0))
        from rfl, derivative_intY, er_qOf_mul_tq q0 1 (by norm_num)]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, rowT, Submission.CDTPlan.seventeen, Submission.CDTPlan.B1]
    ring
  · rw [show (⟨12 + 2, by omega⟩ : Fin 17) = 14 from rfl,
      show Submission.CDTPlan.seventeen m n ra rb rab r0 (14 : Fin 17)
        = Submission.CDTPlan.intY (Submission.CDTPlan.tq 2 (Submission.CDTPlan.GC m n ra rb rab r0))
        from rfl, derivative_intY, er_qOf_mul_tq q0 2 (by norm_num)]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, rowT, Submission.CDTPlan.seventeen, Submission.CDTPlan.B1]
    ring
  · rw [show (⟨12 + 3, by omega⟩ : Fin 17) = 15 from rfl,
      show Submission.CDTPlan.seventeen m n ra rb rab r0 (15 : Fin 17)
        = Submission.CDTPlan.intY (Submission.CDTPlan.tq 3 (Submission.CDTPlan.GC m n ra rb rab r0))
        from rfl, derivative_intY, er_qOf_mul_tq q0 3 (by norm_num)]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, rowT, Submission.CDTPlan.seventeen, Submission.CDTPlan.B1]
    ring
  · rw [show (⟨12 + 4, by omega⟩ : Fin 17) = 16 from rfl,
      show Submission.CDTPlan.seventeen m n ra rb rab r0 (16 : Fin 17)
        = Submission.CDTPlan.intY (Submission.CDTPlan.tq 4 (Submission.CDTPlan.GC m n ra rb rab r0))
        from rfl, derivative_intY, er_qOf_mul_tq q0 4 (by norm_num)]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [AOf, rowT, Submission.CDTPlan.seventeen, Submission.CDTPlan.B1]
    ring

theorem easy_relations (hP : Submission.CDTPlan.PureFacts) (m n : ℕ) (ra rb rab r0 : ℤ)
    (hmn : Submission.CDTPlan.CAdm m n) :
    ∃ (q : Polynomial ℚ) (A : Fin 17 → Fin 17 → Polynomial ℚ), q ≠ 0 ∧
      ∀ i : Fin 17, i ≠ 8 →
        (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.seventeen m n ra rb rab r0 i)
          = ∑ j, (A i j : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 j := by
  obtain ⟨q0, hq0, A0, hA0⟩ := hP.2.2.2.2.2.2.2
  refine ⟨qOf q0, AOf q0 A0 (Submission.CDTPlan.GC m n ra rb rab r0), qOf_ne_zero hq0, ?_⟩
  intro i hi
  fin_cases i
  · exact b_rows q0 A0 hA0 m n ra rb rab r0 0
  · exact b_rows q0 A0 hA0 m n ra rb rab r0 1
  · exact b_rows q0 A0 hA0 m n ra rb rab r0 2
  · exact b_rows q0 A0 hA0 m n ra rb rab r0 3
  · exact b_rows q0 A0 hA0 m n ra rb rab r0 4
  · exact er_G_row q0 A0 m n ra rb rab r0 5 (Or.inl rfl)
  · exact er_G_row q0 A0 m n ra rb rab r0 6 (Or.inr (Or.inl rfl))
  · exact er_G_row q0 A0 m n ra rb rab r0 7 (Or.inr (Or.inr rfl))
  · exact absurd rfl hi
  · exact b_rows q0 A0 hA0 m n ra rb rab r0 5
  · exact b_rows q0 A0 hA0 m n ra rb rab r0 6
  · exact er_int_row q0 A0 m n ra rb rab r0 11 (Or.inl rfl)
  · exact er_int_row q0 A0 m n ra rb rab r0 12 (Or.inr rfl)
  · exact er_tq_row q0 A0 m n ra rb rab r0 1 (by norm_num) (by norm_num)
  · exact er_tq_row q0 A0 m n ra rb rab r0 2 (by norm_num) (by norm_num)
  · exact er_tq_row q0 A0 m n ra rb rab r0 3 (by norm_num) (by norm_num)
  · exact er_tq_row q0 A0 m n ra rb rab r0 4 (by norm_num) (by norm_num)

end

end Work.CDcl
