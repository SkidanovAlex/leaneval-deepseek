import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6SplitSlots
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6Split
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The per-order slots

The two lemmas below are the pointwise, per-order versions of `N0Aux.zslot6_split` and
`N0Aux.mslot6_split`: instead of pricing the order-`b` jet of `X` by one of two global constants,
the `b`-th summand of the Leibniz expansion is priced by `B b` and by the `ℋ^{6-b}`-integrand
of `f`. -/

/-- A single pure `D_z`-slot at level `6`, with the jet of `X` at order `b` priced by `B b`. -/
theorem zslot6_per {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ} {z θ : ℝ}
    (hB : ∀ b : ℕ, 0 ≤ B b)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hjet : ∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  have hlei := Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf i 0
    (by omega) z θ hz hθ0 hθ1
  have hmm : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      = Work.Spaces.mixed i 0 (fun z θ => X z * f z θ) z θ := rfl
  have hsum : Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hmm, hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by
      rw [Work.Spaces.mixed_zero_right]
      ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.choose_sq_le_4096 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b := hjet b (by omega)
    have hG : (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α (6 - b) f z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α (6 - b) f z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
      _ ≤ 4096 * B b * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B b := mul_nonneg (by norm_num) (hB b)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
      _ = 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
      ≤ 4096 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2))
        ≤ ∑ b ∈ Finset.range (i + 1),
            (4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
          Finset.sum_le_sum hper
      _ = 4096 * (∑ b ∈ Finset.range (i + 1),
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          rw [Finset.mul_sum]
      _ ≤ 4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro b _ _
          exact mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.DzIter (i - b) f z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 7 * (4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ ≤ 200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
        have hnn : 0 ≤ ∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ :=
          Finset.sum_nonneg fun b _ =>
            mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
        nlinarith [hnn]

/-- A single mixed slot at level `6`, with the jet of `X` at order `b` priced by `B b`. -/
theorem mslot6_per {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ} {z θ : ℝ}
    (hB : ∀ b : ℕ, 0 ≤ B b)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hjet : ∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  have hj6 : j ≤ 6 := by omega
  have hlei := Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul hX hf j i hj6 z θ
    hz hθ0 hθ1
  have hsum : Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 4096 :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.choose_sq_le_4096 j b hbj hj6
    have hRd : (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b := hjet b (by omega)
    have hG : (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (6 - b) f z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (6 - b) f z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b X z) ^ 2
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          ring
      _ ≤ 4096 * B b * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
          have hc : (0 : ℝ) ≤ 4096 * B b := mul_nonneg (by norm_num) (hB b)
          exact mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) hc
      _ = 4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 7 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 7)
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
      ≤ 4096 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
            * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2))
        ≤ ∑ b ∈ Finset.range (j + 1),
            (4096 * (B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
          Finset.sum_le_sum hper
      _ = 4096 * (∑ b ∈ Finset.range (j + 1),
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          rw [Finset.mul_sum]
      _ ≤ 4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro b _ _
          exact mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b X z
                * (Work.Spaces.mixed (j - b) i f z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 7 * (4096 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ ≤ 200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
        have hnn : 0 ≤ ∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ :=
          Finset.sum_nonneg fun b _ =>
            mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
        nlinarith [hnn]

/-! ## The pointwise majorant of the whole integrand -/

/-- The universal constant of the per-order radial engine (the value of `MajC` for the
per-order family, with room to spare over the exact `200704 * 56`). -/
def RadPerC : ℝ := 20000000

theorem RadPerC_pos : 0 < RadPerC := by norm_num [RadPerC]

/-- **The per-order pointwise majorant**: the `ℋ⁶`-integrand of `X · f` is bounded by the
per-order family `Σ_{b≤6} B b · HkIntegrand α (6-b) f`. -/
theorem maj_pt_per {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ} {z θ : ℝ}
    (hB : ∀ b : ℕ, 0 ≤ B b)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hjet : ∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b) :
    Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
      ≤ RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  have hSnn : 0 ≤ ∑ b ∈ Finset.range 7,
      B b * Work.Spaces.HkIntegrand α (6 - b) f z θ :=
    Finset.sum_nonneg fun b _ =>
      mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ)
  have hBase : 0 ≤ 200704 * (∑ b ∈ Finset.range 7,
      B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
    mul_nonneg (by norm_num) hSnn
  have hZ : (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1),
          (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (6 + 1),
            (200704 * (∑ b ∈ Finset.range 7,
              B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
          Finset.sum_le_sum fun i hi =>
            zslot6_per hB hX hf hz hθ0 hθ1 hjet i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 7 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hM : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 49 * (200704 * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
            (200704 * (∑ b ∈ Finset.range 7,
              B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [ite_eq_left hc]
            exact mslot6_per hB hX hf hz hθ0 hθ1 hjet i j hc.1 hc.2
          · rw [ite_eq_right hc]
            exact hBase
      _ = 49 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
          ring
  rw [Work.Spaces.HkIntegrand]
  calc (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      ≤ 7 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
        + 49 * (200704 * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)) := add_le_add hZ hM
    _ ≤ RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
        have hM' : 200704 * 56 ≤ RadPerC := by norm_num [RadPerC]
        calc 7 * (200704 * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
              + 49 * (200704 * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
            = (200704 * 56) * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by ring
          _ ≤ RadPerC * (∑ b ∈ Finset.range 7,
                B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
              mul_le_mul_of_nonneg_right hM' hSnn

/-! ## The engine -/

/-- **The per-order radial-product engine at level `6`** (namespace `Work.FTS.StrongEps.E4R3.Nblock6`).

For a *radial* factor `X : ℝ → ℝ` (only `C⁶` on `(0,∞)` is assumed — `SmoothOpen` of the lift
is FALSE for angular moments such as `FK w`) and a `SmoothOpen` datum `f` which is
`ℋ⁶`-honest, with per-order pointwise jet bounds `(D_z^b X z)² ≤ B b` (`b ≤ 6`, a.e. in `z`),

  `HkSq α 6 (X·f) ≤ C * Σ_{b≤6} B b * HkSq α (6-b) f`.

This is the per-order refinement of `Apriori4Proofs.N0Aux.radialMaj6_split` (which prices the
orders `b ≤ 4` by a single `Blo` and `b ≥ 5` by a single `Bhi`; that dichotomy is not enough
here, because the radial factor `FK w` at hand has order-`4` jets bounded only by the
`ℋ⁵`-price of `w`).

Recipe: copy `Apriori4Proofs/blocks/N0Aux/Maj6SplitSlots.lean` (`zslot6_split`, `mslot6_split`)
and `Maj6Split.lean` (`maj_pt`, `radialMaj6_split`), replacing the two constants `Blo`/`Bhi`
(used for `b ≤ 4` resp. `b ≥ 5`, priced by `HkIntegrand α 6 f` resp. `HkIntegrand α 2 f`) by the
single family `B : ℕ → ℝ`: the summand indexed by `b` in the Leibniz expansion of a slot `(i,j)`
is priced by `HkIntegrand α (6 - b) f` via `Work.Spaces.sq_le_HkIntegrand_z` (`i - b ≤ 6 - b`)
resp. `Work.Spaces.sq_le_HkIntegrand_mixed` (`1 ≤ i`, `i + (j - b) ≤ 6 - b`), using
`leibniz_radial_mul`, `(i.choose b)² ≤ 4096` for `i ≤ 6` and `sq_sum_le_card_mul_sum_sq`.  Then
integrate over `z ∈ Iz`, `θ ∈ Iθ` using `HkMem_mono_open`, `HkIntegrand_mono` and the a.e. jet
hypothesis (the RHS slices are integrable by `HkMem α (6-b) f`). -/
theorem RadPer : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {B : ℕ → ℝ},
    ContDiffOn ℝ 6 X (Set.Ioi (0 : ℝ)) → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 f → (∀ b : ℕ, 0 ≤ B b) →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ b : ℕ, b ≤ 6 →
      (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b) →
    Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ C * ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkSq α (6 - b) f := by
  refine ⟨RadPerC + 1, by linarith [RadPerC_pos], ?_⟩
  intro α X f B hX hf hm6 hB hjet
  -- honesty of the lower-order data
  have hm : ∀ b : ℕ, b ≤ 6 → Work.Spaces.HkMem α (6 - b) f := fun b _ =>
    Work.FTS.OpenPkg.HkMem_mono_open hf (6 - b) (Nat.sub_le 6 b) hm6
  -- the majorant slices are integrable
  have hSlice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ =>
      ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)
      Work.Spaces.Iθ := by
    intro z hz
    show Integrable (fun θ => ∑ b ∈ Finset.range 7,
      B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) (volume.restrict Work.Spaces.Iθ)
    refine MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => ?_)
    exact ((hm b (by simp only [Finset.mem_range] at hb; omega)).1 z hz).const_mul (B b)
  -- the inner integral of a sum is the sum of the inner integrals
  have hS7eq : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)
        = ∑ b ∈ Finset.range 7, B b * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    intro z hz
    rw [MeasureTheory.integral_finsetSum (Finset.range 7)
      (f := fun b θ => B b * Work.Spaces.HkIntegrand α (6 - b) f z θ)
      (fun b hb => ((hm b (by simp only [Finset.mem_range] at hb; omega)).1 z hz).const_mul (B b))]
    exact Finset.sum_congr rfl fun b _ => MeasureTheory.integral_const_mul (B b) _
  -- the outer integral of the sum is the sum of the outer integrals
  have hT : IntegrableOn (fun z => ∑ b ∈ Finset.range 7,
      B b * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
      Work.Spaces.Iz := by
    show Integrable (fun z => ∑ b ∈ Finset.range 7,
      B b * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ))
      (volume.restrict Work.Spaces.Iz)
    refine MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => ?_)
    exact ((hm b (by simp only [Finset.mem_range] at hb; omega)).2).const_mul (B b)
  have hinner : (fun z => ∫ θ in Work.Spaces.Iθ, RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => RadPerC * (∑ b ∈ Finset.range 7, B b * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (6 - b) f z θ))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iz) measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul, hS7eq z hz]
  have hGint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, RadPerC *
      (∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
      Work.Spaces.Iz :=
    (hT.const_mul RadPerC).congr hinner.symm
  -- the a.e. jet bounds, together with `z ∈ Iz`
  have hgood : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      z ∈ Work.Spaces.Iz ∧
        (∀ b : ℕ, b ≤ 6 → (Work.Elliptic.DzdIter b X z) ^ 2 ≤ B b) :=
    (MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) (s := Work.Spaces.Iz)
      measurableSet_Ici).and hjet
  have hIoo : (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    exact Measure.restrict_congr_set haeeq.symm
  -- the pointwise comparison, sliced in `θ`
  have hslice_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, RadPerC * (∑ b ∈ Finset.range 7,
            B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    filter_upwards [hgood] with z hz
    obtain ⟨hzIz, hzjet⟩ := hz
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      ((hSlice z hzIz).const_mul RadPerC) ?_
    rw [hIoo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hzIz) with hz0 | hzpos
    · rw [← hz0, Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.HkIntegrand_zero]
      exact mul_nonneg RadPerC_pos.le (Finset.sum_nonneg fun b _ =>
        mul_nonneg (hB b) (Work.Spaces.HkIntegrand_nonneg α (6 - b) f 0 θ))
    · exact maj_pt_per hB hX hf hzpos hθ.1 hθ.2 hzjet
  -- integrate in `z`
  have houter : Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, RadPerC * (∑ b ∈ Finset.range 7,
          B b * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    rw [Work.Spaces.HkSq]
    exact MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ)
      hGint hslice_ae
  -- evaluate the majorant integral
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, RadPerC *
      (∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
      = RadPerC * ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkSq α (6 - b) f := by
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, RadPerC *
        (∑ b ∈ Finset.range 7, B b * Work.Spaces.HkIntegrand α (6 - b) f z θ))
        = ∫ z in Work.Spaces.Iz, RadPerC * (∑ b ∈ Finset.range 7, B b *
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)) :=
      MeasureTheory.integral_congr_ae hinner
    rw [h1, MeasureTheory.integral_const_mul]
    have h2 : (∫ z in Work.Spaces.Iz, (∑ b ∈ Finset.range 7, B b *
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ)))
        = ∑ b ∈ Finset.range 7, B b * (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
      rw [MeasureTheory.integral_finsetSum (Finset.range 7)
        (f := fun b z => B b * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α (6 - b) f z θ))
        (fun b hb => ((hm b (by simp only [Finset.mem_range] at hb; omega)).2).const_mul (B b))]
      exact Finset.sum_congr rfl fun b _ => MeasureTheory.integral_const_mul (B b) _
    rw [h2]
    simp only [Work.Spaces.HkSq]
  refine houter.trans_eq hval |>.trans ?_
  have hSq_nn : 0 ≤ ∑ b ∈ Finset.range 7, B b * Work.Spaces.HkSq α (6 - b) f :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hB b) (Work.Spaces.HkSq_nonneg α (6 - b) f)
  exact mul_le_mul_of_nonneg_right (by linarith [RadPerC_pos]) hSq_nn

end Work.FTS.StrongEps.E4R3.Nblock6
