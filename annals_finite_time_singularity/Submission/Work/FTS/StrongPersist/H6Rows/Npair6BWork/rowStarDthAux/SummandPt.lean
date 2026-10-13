import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDthAux.FlatW
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The pointwise bound of a Leibniz summand with a non-trivial index.**  For `(i,j) ≠ (0,0)`
with `i ≤ a`, `j ≤ b`, `a + b ≤ 6`, the flat priced coefficient slot `D_z^jD_θ^iA` pairs with the
two `f`-slots into at most `2·KA·HkIntegrand α 6 f`. -/
theorem summandPt {α KA : ℝ} {A f : ℝ → ℝ → ℝ} {a b i j : ℕ} {q z θ : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hKA0 : 0 ≤ KA)
    (hflat : ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i A z θ| ≤ KA * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1))
    (hf6 : Work.Spaces.HkMem α 6 f)
    (hia : i ≤ a) (hjb : j ≤ b) (hne : ¬(i = 0 ∧ j = 0)) (hab : a + b ≤ 6)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    |Work.FTS.TransportS.SlotT2.canonW q z θ
        * Work.Spaces.mixed j i A z θ
        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ 2 * KA * Work.Spaces.HkIntegrand α 6 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hij6 : j + i ≤ 6 := by omega
  have hX := hflat j i hij6 z θ hz hθ0 hθ1
  have hcnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
    Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
  have hIk : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hzfac0 : 0 ≤ z / (1 + z) := div_nonneg hz.le (by linarith)
  have hzfac1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hYord : (a - i + 1) + (b - j) ≤ 6 := by omega
  have hYη : (a - i + 1) = 0 → q ≤ Work.Spaces.eta := fun h => absurd h (by omega)
  have hYle : Work.FTS.TransportS.SlotT2.canonW q z θ
      * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f (a - i + 1) (b - j)
      hqγ hYη hYord hθIoo
  have hZle : Work.FTS.TransportS.SlotT2.canonW q z θ
      * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q f a b
      hqγ hqη (by omega) hθIoo
  have hAM : 2 * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
        * |Work.Spaces.mixed b a f z θ|
      ≤ (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
        + (Work.Spaces.mixed b a f z θ) ^ 2 := by
    have h := sq_nonneg (|Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
      - |Work.Spaces.mixed b a f z θ|)
    rw [sub_sq, sq_abs, sq_abs] at h
    linarith
  have habs : |Work.FTS.TransportS.SlotT2.canonW q z θ
        * Work.Spaces.mixed j i A z θ
        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      = Work.FTS.TransportS.SlotT2.canonW q z θ
        * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
        * |Work.Spaces.mixed b a f z θ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hcnn]
  rw [habs]
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `i = 0`, hence `j ≥ 1`: use the weight `q` itself for both `f`-slots
    subst hi0
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr fun h => hne ⟨rfl, h⟩
    have hX' : |Work.Spaces.mixed j 0 A z θ| ≤ KA * (z / (1 + z)) := by
      have h := hX
      have hif : (if (1 : ℕ) ≤ 0 then
          (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else (1 : ℝ)) = 1 :=
        if_neg (by norm_num)
      rw [hif, mul_one] at h
      simpa using h
    have hws : Work.FTS.TransportS.SlotT2.canonW q z θ
          * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have hAM' : 2 * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ|
          ≤ (Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ) ^ 2
            + (Work.Spaces.mixed b a f z θ) ^ 2 := by
        have h := sq_nonneg (|Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          - |Work.Spaces.mixed b a f z θ|)
        rw [sub_sq, sq_abs, sq_abs] at h
        linarith
      have h := mul_le_mul_of_nonneg_left hAM' hcnn
      have hY' := hYle
      have hZ' := hZle
      linarith
    calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j 0 A z θ|
          * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ KA * (z / (1 + z)) * Work.FTS.TransportS.SlotT2.canonW q z θ
          * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
            (abs_nonneg _)
          calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j 0 A z θ|
              ≤ Work.FTS.TransportS.SlotT2.canonW q z θ * (KA * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_left hX' hcnn
            _ = KA * (z / (1 + z)) * Work.FTS.TransportS.SlotT2.canonW q z θ := by ring
      _ = KA * (z / (1 + z)) * (Work.FTS.TransportS.SlotT2.canonW q z θ
            * |Work.Spaces.mixed (b - j) ((a - 0) + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ|) := by ring
      _ ≤ KA * (z / (1 + z)) * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul_of_nonneg_left hws (mul_nonneg hKA0 hzfac0)
      _ ≤ KA * 1 * Work.Spaces.HkIntegrand α 6 f z θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzfac1 hKA0) hIk
      _ = KA * Work.Spaces.HkIntegrand α 6 f z θ := by ring
      _ ≤ 2 * KA * Work.Spaces.HkIntegrand α 6 f z θ := by
          have : 0 ≤ KA * Work.Spaces.HkIntegrand α 6 f z θ := mul_nonneg hKA0 hIk
          linarith
  · -- `1 ≤ i`: the flat price with the `γ`-weight
    have hi1 : 1 ≤ i := hipos
    have hYleγ : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed (b - j) (a - i + 1) f z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α (Work.Spaces.gam α) f
        (a - i + 1) (b - j) le_rfl
        (fun h => absurd h (by omega)) hYord hθIoo
    have hZleγ : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α (Work.Spaces.gam α) f a b
        le_rfl (fun h => absurd h (by omega)) (by omega) hθIoo
    have hX' : |Work.Spaces.mixed j i A z θ|
        ≤ KA * (z / (1 + z)) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      have h := hX
      rw [if_pos hi1] at h
      exact h
    have hwq : Work.FTS.TransportS.SlotT2.canonW q z θ
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        ≤ 2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ :=
      canonWMulFlatAgm hα0 hα1 hqγ hz hθ0 hθ1
    have hcγnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ :=
      Work.FTS.TransportS.SlotT2.canonW_nonneg hθI
    have hγw : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have h := mul_le_mul_of_nonneg_left hAM hcγnn
      have hY' := hYleγ
      have hZ' := hZleγ
      linarith
    calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i A z θ|
          * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ Work.FTS.TransportS.SlotT2.canonW q z θ
            * (KA * (z / (1 + z))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hX' hcnn) (abs_nonneg _)) (abs_nonneg _)
      _ = KA * (z / (1 + z)) * (Work.FTS.TransportS.SlotT2.canonW q z θ
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ| := by ring
      _ ≤ KA * (z / (1 + z))
            * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ)
            * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
            * |Work.Spaces.mixed b a f z θ| := by
          have hwq' : KA * (z / (1 + z))
                * (Work.FTS.TransportS.SlotT2.canonW q z θ
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              ≤ KA * (z / (1 + z))
                * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ) :=
            mul_le_mul_of_nonneg_left hwq (mul_nonneg hKA0 hzfac0)
          calc KA * (z / (1 + z))
                * (Work.FTS.TransportS.SlotT2.canonW q z θ
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ|
              = (KA * (z / (1 + z))
                  * (Work.FTS.TransportS.SlotT2.canonW q z θ
                      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ| := by ring
            _ ≤ (KA * (z / (1 + z))
                  * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ))
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ| :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwq' (abs_nonneg _))
                  (abs_nonneg _)
            _ = KA * (z / (1 + z))
                * (2 * Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ)
                * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
                * |Work.Spaces.mixed b a f z θ| := by ring
      _ = KA * (z / (1 + z)) * (2 * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * |Work.Spaces.mixed (b - j) (a - i + 1) f z θ|
              * |Work.Spaces.mixed b a f z θ|)) := by ring
      _ ≤ KA * (z / (1 + z)) * (2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hγw (by norm_num))
            (mul_nonneg hKA0 hzfac0)
      _ ≤ 2 * KA * Work.Spaces.HkIntegrand α 6 f z θ := by
          have h2 : KA * (z / (1 + z)) * (2 * Work.Spaces.HkIntegrand α 6 f z θ)
              ≤ KA * 1 * (2 * Work.Spaces.HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzfac1 hKA0) (by linarith)
          linarith

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
