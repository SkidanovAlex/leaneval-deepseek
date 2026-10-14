import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.mismatchSummandPt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowMulSupAux.basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarP
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The `A · f` row.**  Assembled from the Leibniz expansion
`mixed b a (A · f) = Σ_{i ≤ b}Σ_{j ≤ a} C(b,i)C(a,j) (D_z^i D_θ^j A)(D_z^{b-i}D_θ^{a-j} f)`
(`rowMulSupAux.mixedMul_ae'`) and the per-summand bound: every summand with `1 ≤ a - j` (or with
an `η`/σ-free leaf weight) is closed by `summand_le_easy` with the pointwise coefficient price
`2·KA`, and the single remaining summand (`ρ = leafGam α`, `j = a`) by the hypothesis `hmis`. -/
theorem rowStarFamAf_of_mismatch (Cm : ℝ) (hCm : 0 < Cm)
    (hmis : ∀ α ∈ Set.Ioc 0 1, ∀ (A f : ℝ → ℝ → ℝ) (KA : ℝ) (i a b : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 f →
      0 ≤ KA →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed i a A z θ|
            ≤ KA * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) →
      1 ≤ a → i ≤ b → a + b ≤ 6 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
            * Work.Spaces.DzIter (b - i) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2) rowMulSupAux.mu ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed i a A p.1 p.2
            * Work.Spaces.DzIter (b - i) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu|
        ≤ Cm * KA * (1 + Work.Spaces.HkSq α 6 f)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (A f : Fn) (KA M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
        Work.FTS.EllipticEst.SmoothOpen A →
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
        a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
        |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * f z θ) f|
          ≤ C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Ce, hCepos, heasy⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
  refine ⟨200704 * (2 * Ce + Cm) + 1, by positivity, ?_⟩
  intro α hα A f KA M a b ρ hA hdat hpt hab hleaf
  obtain ⟨hα0, hα1⟩ := hα
  have hαmem : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hA6 : ContDiffOn ℝ 6 (Function.uncurry A) Work.FTS.EllipticEst.Q0 := hA.forall 6
  have hf6 : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hdat.sm.forall 6
  -- ## the price `KA` is nonnegative (read off the `(0,0)` slot)
  have hKA0 : 0 ≤ KA := by
    have h := hpt 0 0 (by omega) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h₁ : Work.Spaces.mixed 0 0 A 1 (Real.pi / 4) = A 1 (Real.pi / 4) := rfl
    rw [h₁] at h
    have h₂ : (if (1 : ℕ) ≤ 0 then (α + Real.sin (2 * (Real.pi / 4)))
        * (Real.sin (2 * (Real.pi / 4))) ^ (α / 5) else (1 : ℝ)) = 1 := by
      rw [if_neg (by omega : ¬ (1 : ℕ) ≤ 0)]
    rw [h₂] at h
    have h₃ : (1 : ℝ) / (1 + 1) = 1 / 2 := by norm_num
    rw [h₃] at h
    nlinarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hdiv1 : ∀ z : ℝ, 0 < z → z / (1 + z) ≤ 1 := by
    intro z hz
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]
    linarith
  -- ## the per-summand bound
  have hterm : ∀ i ∈ Finset.range (b + 1), ∀ j ∈ Finset.range (a + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
          * Work.Spaces.mixed i j A p.1 p.2
          * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2) rowMulSupAux.mu ∧
      |∫ p, ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
          * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu|
        ≤ (2 * Ce + Cm) * KA * (1 + Work.Spaces.HkSq α 6 f) := by
    intro i hi j hj
    have hib : i ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hij : j + i ≤ 6 := by omega
    by_cases hgj : 1 ≤ a - j ∨ ρ = Work.FTS.TransportS.leafEta
        ∨ ρ = Work.FTS.TransportS.leafOne
    · -- ### the guard case: the coefficient slot is pointwise bounded by `2·KA`
      have hptA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed i j A z θ| ≤ 2 * KA := by
        intro z θ hz hθ hθ2
        have h := hpt i j (by omega) z θ hz hθ hθ2
        have hp1 : z / (1 + z) ≤ 1 := hdiv1 z hz
        have hσ0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith) (by linarith [Real.pi_pos])
        have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
        by_cases hj1 : 1 ≤ j
        · have hif : (if 1 ≤ j then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
              else (1 : ℝ))
              = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := if_pos hj1
          rw [hif] at h
          have hPA0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
            mul_nonneg (by linarith) (Real.rpow_nonneg hσ0 _)
          have hPA2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
            have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
            have h2 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
              Real.rpow_le_one hσ0 hσ1 (by linarith)
            nlinarith
          calc |Work.Spaces.mixed i j A z θ|
              ≤ KA * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := h
            _ ≤ KA * 1 * 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hp1 hKA0) hPA2 hPA0 (by linarith)
            _ = 2 * KA := by ring
        · have hif : (if 1 ≤ j then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
              else (1 : ℝ)) = 1 := if_neg hj1
          rw [hif] at h
          have h1 : KA * (z / (1 + z)) ≤ KA * 1 := mul_le_mul_of_nonneg_left hp1 hKA0
          calc |Work.Spaces.mixed i j A z θ| ≤ KA * (z / (1 + z)) * 1 := h
            _ = KA * (z / (1 + z)) := by ring
            _ ≤ KA * 1 := h1
            _ = 1 * KA := by ring
            _ ≤ 2 * KA := by linarith
      obtain ⟨hint, hbd⟩ := heasy α hαmem (fun z θ => Work.Spaces.mixed i j A z θ) f
        (a - j) (b - i) a b ρ (2 * KA) (hA.mixed i j) (by linarith) hptA hdat.sm hdat.h6
        (by omega) hab hleaf hgj
      refine ⟨hint, hbd.trans ?_⟩
      have hstep1 : Ce * (2 * KA) * Work.Spaces.HkSq α 6 f
          ≤ 2 * Ce * (KA * (1 + Work.Spaces.HkSq α 6 f)) := by
        have h2 : (0 : ℝ) ≤ 2 * Ce * KA := by positivity
        rw [show 2 * Ce * (KA * (1 + Work.Spaces.HkSq α 6 f))
              = 2 * Ce * KA + 2 * Ce * KA * Work.Spaces.HkSq α 6 f from by ring,
            show Ce * (2 * KA) * Work.Spaces.HkSq α 6 f
              = 2 * Ce * KA * Work.Spaces.HkSq α 6 f from by ring]
        linarith
      have hstep2 : 2 * Ce * (KA * (1 + Work.Spaces.HkSq α 6 f))
          ≤ (2 * Ce + Cm) * (KA * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_right (by linarith [hCepos]) (by positivity)
      exact hstep1.trans (hstep2.trans (le_of_eq (by ring)))
    · -- ### the mismatch case: `ρ = leafGam α` and all angular derivatives on `A`
      push_neg at hgj
      have hρ : ρ = Work.FTS.TransportS.leafGam α := by
        rcases hleaf with h | h | ⟨-, h⟩
        · exact absurd h hgj.2.1
        · exact absurd h hgj.2.2
        · exact h
      have ha1 : 1 ≤ a := by
        rcases hleaf with h | h | ⟨h, -⟩
        · exact absurd h hgj.2.1
        · exact absurd h hgj.2.2
        · exact h
      have hja' : j = a := by omega
      have hslot : Work.Spaces.mixed (b - i) (a - a) f = Work.Spaces.DzIter (b - i) f := by
        rw [Nat.sub_self]
        rfl
      rw [hρ, hja', hslot]
      have hptKi : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed i a A z θ| ≤ KA * (α + Real.sin (2 * θ))
            * (Real.sin (2 * θ)) ^ (α / 5) := by
        intro z θ hz hθ hθ2
        have h := hpt i a (by omega) z θ hz hθ hθ2
        have hif : (if 1 ≤ a then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
            else (1 : ℝ))
            = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := if_pos ha1
        rw [hif] at h
        have hp1 : z / (1 + z) ≤ 1 := hdiv1 z hz
        have hσ0 : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith) (by linarith [Real.pi_pos])
        have hPA0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_nonneg (by linarith) (Real.rpow_nonneg hσ0 _)
        calc |Work.Spaces.mixed i a A z θ|
            ≤ KA * (z / (1 + z))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := h
          _ ≤ KA * 1 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 hKA0) hPA0
          _ = KA * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by ring
      obtain ⟨hint, hbd⟩ :=
        hmis α hαmem A f KA i a b hA hdat.sm hdat.h6 hKA0 hptKi ha1 hib hab
      refine ⟨hint, hbd.trans ?_⟩
      have h := mul_le_mul_of_nonneg_right
        (show Cm ≤ 2 * Ce + Cm by linarith [hCepos])
        (show (0 : ℝ) ≤ KA * (1 + Work.Spaces.HkSq α 6 f) by
          exact mul_nonneg hKA0 (by linarith))
      calc Cm * KA * (1 + Work.Spaces.HkSq α 6 f)
          = Cm * (KA * (1 + Work.Spaces.HkSq α 6 f)) := by ring
        _ ≤ (2 * Ce + Cm) * (KA * (1 + Work.Spaces.HkSq α 6 f)) := h
        _ = (2 * Ce + Cm) * KA * (1 + Work.Spaces.HkSq α 6 f) := by ring
  -- ## the binomial bookkeeping
  have hcoef : ∀ i ∈ Finset.range (b + 1), ∀ j ∈ Finset.range (a + 1),
      ((b.choose i : ℝ) * (a.choose j : ℝ)) ≤ 4096 := by
    intro i hi j hj
    have hb6 : b ≤ 6 := by omega
    have ha6 : a ≤ 6 := by omega
    have hb64 : (b.choose i : ℝ) ≤ 64 := by
      have h1 : b.choose i ≤ 2 ^ b := Nat.choose_le_two_pow b i
      have h2 : (2 : ℕ) ^ b ≤ 64 := by interval_cases b <;> norm_num
      exact_mod_cast le_trans h1 h2
    have ha64 : (a.choose j : ℝ) ≤ 64 := by
      have h1 : a.choose j ≤ 2 ^ a := Nat.choose_le_two_pow a j
      have h2 : (2 : ℕ) ^ a ≤ 64 := by interval_cases a <;> norm_num
      exact_mod_cast le_trans h1 h2
    have hb0 : (0 : ℝ) ≤ (b.choose i : ℝ) := by positivity
    have ha0 : (0 : ℝ) ≤ (a.choose j : ℝ) := by positivity
    nlinarith [hb64, ha64, hb0, ha0]
  set Kc : ℝ := ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
      ((b.choose i : ℝ) * (a.choose j : ℝ)) with hKcdef
  have hKc0 : 0 ≤ Kc := by
    rw [hKcdef]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))
  have hKcle : Kc ≤ 200704 := by
    rw [hKcdef]
    calc ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
          ((b.choose i : ℝ) * (a.choose j : ℝ))
        ≤ ∑ _i ∈ Finset.range (b + 1), ∑ _j ∈ Finset.range (a + 1), (4096 : ℝ) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hcoef i hi j hj))
      _ = (((b : ℝ) + 1) * (((a : ℝ) + 1) * 4096)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 200704 := by
          have hb7 : (b : ℝ) + 1 ≤ 7 := by
            have : b + 1 ≤ 7 := by omega
            exact_mod_cast this
          have ha7 : (a : ℝ) + 1 ≤ 7 := by
            have : a + 1 ≤ 7 := by omega
            exact_mod_cast this
          have hb0 : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
          have ha0 : (0 : ℝ) ≤ (a : ℝ) + 1 := by positivity
          nlinarith
  -- ## the Leibniz sum
  have hHint : Integrable (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (b + 1),
      ∑ j ∈ Finset.range (a + 1), ((b.choose i : ℝ) * (a.choose j : ℝ))
        * (ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
          * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)) rowMulSupAux.mu := by
    refine rowMulSupAux.integrable_finset_sum _ (fun i hi => ?_)
    exact rowMulSupAux.integrable_finset_sum _ (fun j hj => ((hterm i hi j hj).1).const_mul _)
  have hHval : ∫ p, (∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
        ((b.choose i : ℝ) * (a.choose j : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
            * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)) ∂rowMulSupAux.mu
      = ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
        ((b.choose i : ℝ) * (a.choose j : ℝ))
          * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
              * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
              * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu) := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl (fun j hj => by rw [integral_const_mul])
      · exact fun j hj => ((hterm i hi j hj).1).const_mul _
    · exact fun i hi =>
        rowMulSupAux.integrable_finset_sum _ (fun j hj => ((hterm i hi j hj).1).const_mul _)
  have hHbd : |∫ p, (∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
        ((b.choose i : ℝ) * (a.choose j : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
            * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)) ∂rowMulSupAux.mu|
      ≤ Kc * ((2 * Ce + Cm) * KA * (1 + Work.Spaces.HkSq α 6 f)) := by
    rw [hHval]
    calc |∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
            ((b.choose i : ℝ) * (a.choose j : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
                  * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu)|
        ≤ ∑ i ∈ Finset.range (b + 1), |∑ j ∈ Finset.range (a + 1),
            ((b.choose i : ℝ) * (a.choose j : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
                  * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
            |((b.choose i : ℝ) * (a.choose j : ℝ))
              * (∫ p, ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
                  * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu)| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
            ((b.choose i : ℝ) * (a.choose j : ℝ))
              * |∫ p, ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
                  * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
                  * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu| := by
          refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
          rw [abs_mul, abs_of_nonneg (by positivity :
            (0 : ℝ) ≤ (b.choose i : ℝ) * (a.choose j : ℝ))]
      _ ≤ ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
            ((b.choose i : ℝ) * (a.choose j : ℝ))
              * ((2 * Ce + Cm) * KA * (1 + Work.Spaces.HkSq α 6 f)) := by
          refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
          exact mul_le_mul_of_nonneg_left (hterm i hi j hj).2 (by positivity)
      _ = Kc * ((2 * Ce + Cm) * KA * (1 + Work.Spaces.HkSq α 6 f)) := by
          rw [hKcdef]
          rw [Finset.sum_mul]
          congr 1
          ext i
          rw [Finset.sum_mul]
  -- ## the a.e. identity for the pairing integrand
  have hae : (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) =ᵐ[rowMulSupAux.mu]
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
        ((b.choose i : ℝ) * (a.choose j : ℝ))
          * (ρ p.1 p.2 * Work.Spaces.mixed i j A p.1 p.2
            * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2)) := by
    filter_upwards [rowMulSupAux.mixedMul_ae' hA6 hf6 hab] with p hp
    have hp' : Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
        = ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (a + 1),
          ((b.choose i : ℝ) * (a.choose j : ℝ))
            * (Work.Spaces.mixed i j A p.1 p.2
                * Work.Spaces.mixed (b - i) (a - j) f p.1 p.2) := hp
    rw [hp']
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hGint : Integrable (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) rowMulSupAux.mu := hHint.congr hae.symm
  have hGbd : |∫ p, ρ p.1 p.2 * Work.Spaces.mixed b a (fun z θ => A z θ * f z θ) p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 ∂rowMulSupAux.mu|
      ≤ Kc * ((2 * Ce + Cm) * KA * (1 + Work.Spaces.HkSq α 6 f)) := by
    rw [integral_congr_ae hae]
    exact hHbd
  rw [rowMulSupAux.slotPairing_eq_prod hGint]
  refine hGbd.trans ?_
  -- ## the final arithmetic
  set CD : ℝ := 2 * Ce + Cm with hCDdef
  have hCD0 : 0 ≤ CD := by rw [hCDdef]; linarith [hCepos.le, hCm.le]
  set X : ℝ := (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hSq1 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
  have hKAle : KA * (1 + Work.Spaces.HkSq α 6 f) ≤ X := by
    have h1 : KA ≤ (1 + KA) * (1 + M) := by nlinarith [hKA0, hM0]
    calc KA * (1 + Work.Spaces.HkSq α 6 f)
        ≤ ((1 + KA) * (1 + M)) * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_right h1 hSq1
      _ = X := by rw [hXdef]
  have hstep2 : CD * KA * (1 + Work.Spaces.HkSq α 6 f) ≤ CD * X := by
    calc CD * KA * (1 + Work.Spaces.HkSq α 6 f)
        = CD * (KA * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      _ ≤ CD * X := mul_le_mul_of_nonneg_left hKAle hCD0
  have hstep5 : 200704 * (CD * X) ≤ (200704 * CD + 1) * X := by
    rw [← mul_assoc, add_mul, one_mul]
    exact le_add_of_nonneg_right hX0
  have hα3 : 1 ≤ α ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hα0.le]
    rw [one_le_inv₀ (Real.rpow_pos_of_pos hα0 3)]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  have hYle : (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
      ≤ α ^ (-(3 : ℝ)) * ((1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by
    have hY0 : (0 : ℝ) ≤ (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
      have h1 : (0 : ℝ) ≤ 1 + KA := by linarith
      have h2 : (0 : ℝ) ≤ 1 + M := by linarith
      have h3 : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
      positivity
    nlinarith [hα3, hY0]
  have hb : (0 : ℝ) ≤ 200704 * (2 * Ce + Cm) + 1 := by positivity
  calc Kc * (CD * KA * (1 + Work.Spaces.HkSq α 6 f))
      ≤ Kc * (CD * X) := mul_le_mul_of_nonneg_left hstep2 hKc0
    _ ≤ 200704 * (CD * X) := mul_le_mul_of_nonneg_right hKcle (by positivity)
    _ ≤ (200704 * CD + 1) * X := hstep5
    _ = (200704 * (2 * Ce + Cm) + 1) * (1 + KA) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by rw [hXdef, hCDdef]; ring
    _ ≤ (200704 * (2 * Ce + Cm) + 1) * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by
        calc (200704 * (2 * Ce + Cm) + 1) * (1 + KA) * (1 + M)
              * (1 + Work.Spaces.HkSq α 6 f)
            = (200704 * (2 * Ce + Cm) + 1)
                * ((1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
          _ ≤ (200704 * (2 * Ce + Cm) + 1)
                * (α ^ (-(3 : ℝ))
                  * ((1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f))) :=
              mul_le_mul_of_nonneg_left hYle hb
          _ = (200704 * (2 * Ce + Cm) + 1) * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
                * (1 + Work.Spaces.HkSq α 6 f) := by ring

/-- **The `A · f` row**, assembled from the pointwise-priced mismatch summand. -/
theorem rowStarFamAf : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Fn) (KA M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cm, hCm, hmis⟩ := mismatchSummandPt
  exact rowStarFamAf_of_mismatch Cm hCm hmis

theorem rowStarFam : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (KA M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
            (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      (|Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * f z θ) f|
          ≤ C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) ∧
       |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => A z θ * Work.Spaces.Dth f z θ) f|
          ≤ C * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := rowStarFamAf
  obtain ⟨C2, hC2pos, hC2⟩ := rowStarDth
  refine ⟨max C1 C2, lt_max_of_lt_left hC1pos, ?_⟩
  intro α hα A f KA M a b ρ hA hdat hpt hab hleaf
  -- the datum prices are nonnegative, and so are the prices `KA`, `M`, `HkSq`
  have hKA0 : 0 ≤ KA := by
    have h := hpt 0 0 (by omega) 1 (Real.pi / 4) (by norm_num)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have h₁ : Work.Spaces.mixed 0 0 A 1 (Real.pi / 4) = A 1 (Real.pi / 4) := rfl
    rw [h₁] at h
    have h₂ : (if (1 : ℕ) ≤ 0 then (α + Real.sin (2 * (Real.pi / 4)))
        * (Real.sin (2 * (Real.pi / 4))) ^ (α / 5) else (1 : ℝ)) = 1 := by
      rw [if_neg (by omega : ¬ (1 : ℕ) ≤ 0)]
    rw [h₂] at h
    have h₃ : (1 : ℝ) / (1 + 1) = 1 / 2 := by norm_num
    rw [h₃] at h
    nlinarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hR : (0 : ℝ) ≤ α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
      * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hα.1.le _) (by linarith))
      (by linarith)) (by linarith)
  refine ⟨?_, ?_⟩
  · refine (hC1 α hα A f KA M a b ρ hA hdat hpt hab hleaf).trans ?_
    have hmax := mul_le_mul_of_nonneg_right (le_max_left C1 C2) hR
    calc C1 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
        = C1 * (α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      _ ≤ max C1 C2 * (α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f)) := hmax
      _ = max C1 C2 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  · refine (hC2 α hα A f KA M a b ρ hA hdat hpt hab hleaf).trans ?_
    have hmax := mul_le_mul_of_nonneg_right (le_max_right C1 C2) hR
    calc C2 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
        = C2 * (α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f)) := by ring
      _ ≤ max C1 C2 * (α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f)) := hmax
      _ = max C1 C2 * α ^ (-(3 : ℝ)) * (1 + KA) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
