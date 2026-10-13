/-
# `N0Aux.Maj6Split` — the level-matched radial majorant at level `6`

`Work.FTS.StrongPersist.H6Pair6Aux.radialMaj6` bounds the `ℋ⁶`-integrand of a product
`X z · f z θ` (with `X` radial, `C⁶` on `(0,∞)`) by a *single* constant `B` dominating the
`D_z`-iterates of `X` up to order `6`.  For the pieces of `N₀` the two regimes are different:
the low iterates (`j ≤ 4`) of `X = L₁₂(w)` are priced by the *small* quantity `|w|_{ℋ⁴}` (which
is `≤ C₀ α²` in the applications), while only the top iterates `j = 5, 6` are priced by
`|w|_{ℋ⁶}`.  Because the top iterates only occur in slots where *all but at most two*
derivatives fall on `f`, the lossy constant `B` can be replaced by the level-matched pair
`(Blo, Bhi)`:

  `HkSq α 6 (X · f) ≤ C (Blo² |f|²_{ℋ⁶} + Bhi² |f|²_{ℋ²})`,

with `C` universal.  This is the engine that makes the `α`-uniform estimates of the `N₀`-block
possible (a single `B` would produce the bound `B² |f|²_{ℋ⁶}` and lose the small factor).

The proof is copied from `radialMaj6`: the Leibniz expansion `leibniz_radial_mul` of each slot,
the single-slot bounds `sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed` (used at level `6` when
the derivative on `X` is `≤ 4` and at level `2` when it is `≥ 5`), binomial bounds
`b.choose k ≤ 2^b ≤ 64` and Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6SplitSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## The pointwise majorant of the whole integrand -/

theorem maj_pt {α Blo Bhi : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi)
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hLo : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ Blo)
    (hHi : ∀ j : ℕ, j ≤ 6 → |Work.Elliptic.DzdIter j X z| ≤ Bhi) :
    Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
      ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
  have hHk6 : 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  have hHk2 : 0 ≤ Work.Spaces.HkIntegrand α 2 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 2 f z θ
  have hBase : 0 ≤ 200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
      + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
    linarith
  -- the pure `z`-part
  have hZ : (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1),
          (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (6 + 1),
            (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) :=
          Finset.sum_le_sum fun i hi =>
            zslot6_split hBlo hBhi hX hf hz hθ0 hθ1 hLo hHi i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- the mixed part
  have hM : (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
    calc (∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range (6 + 1), ∑ _j ∈ Finset.range (6 + 1),
            (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [if_pos hc]
            exact mslot6_split hBlo hBhi hX hf hz hθ0 hθ1 hLo hHi i j hc.1 hc.2
          · rw [if_neg hc]
            exact hBase
      _ = 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := by
          simp only [Finset.sum_const, Finset.card_range, Nat.cast_ofNat, nsmul_eq_mul]
          norm_num
          ring
  rw [Work.Spaces.HkIntegrand]
  have h7 : (7 : ℝ) ≤ MajC := by norm_num [MajC]
  have h49 : (49 : ℝ) ≤ MajC := by norm_num [MajC]
  calc (∑ i ∈ Finset.range (6 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + ∑ i ∈ Finset.range (6 + 1), ∑ j ∈ Finset.range (6 + 1),
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      ≤ 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
        + 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) := add_le_add hZ hM
    _ ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
        have hY : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ :=
          add_nonneg (mul_nonneg (sq_nonneg Blo) hHk6) (mul_nonneg (sq_nonneg Bhi) hHk2)
        have hM' : 200704 * 56 ≤ MajC := by norm_num [MajC]
        calc 7 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
                + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
              + 49 * (200704 * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
                + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
            = (200704 * 56) * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by ring
          _ ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
              + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) :=
              mul_le_mul_of_nonneg_right hM' hY

/-! ## The engine -/

/-- **The level-matched radial majorant at level `6`.**  If `X : ℝ → ℝ` is `C⁶` on `(0,∞)`
with `|D_z^j X| ≤ Blo` for `j ≤ 4` and `≤ Bhi` for `j ≤ 6`, and `f` is `C^∞` on the open
quadrant with `HkMem α 6 f`, then

  `HkSq α 6 (X · f) ≤ C · (Blo² · HkSq α 6 f + Bhi² · HkSq α 2 f)`,

with `C` universal (independent of `α`, `X`, `f`, `Blo`, `Bhi`). -/
theorem radialMaj6_split : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (X : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (Blo Bhi : ℝ),
    ContDiffOn ℝ 6 X (Set.Ioi 0) → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 f → 0 ≤ Blo → 0 ≤ Bhi →
    (∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j X z| ≤ Blo) →
    (∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j X z| ≤ Bhi) →
    Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ C * (Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f) := by
  refine ⟨MajC + 1, by linarith [MajC_pos], ?_⟩
  intro α X f Blo Bhi hX hf hm6 hBlo hBhi hLo hHi
  have hm2 : Work.Spaces.HkMem α 2 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf 2 (by norm_num) hm6
  -- the pointwise majorant on the open quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ
        ≤ MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0, HkIntegrand_zero]
      have h : 0 ≤ Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f 0 θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f 0 θ :=
        add_nonneg (mul_nonneg (sq_nonneg Blo) (Work.Spaces.HkIntegrand_nonneg α 6 f 0 θ))
          (mul_nonneg (sq_nonneg Bhi) (Work.Spaces.HkIntegrand_nonneg α 2 f 0 θ))
      exact mul_nonneg MajC_pos.le h
    · exact maj_pt hBlo hBhi hX hf hzpos hθ.1 hθ.2
        (fun j hj => hLo j hj z (Set.mem_Ioi.mpr hzpos))
        (fun j hj => hHi j hj z (Set.mem_Ioi.mpr hzpos))
  -- the inner comparison
  have hIoo : (volume.restrict Work.Spaces.Iθ) = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    exact Measure.restrict_congr_set haeeq.symm
  have hmaj_slice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => MajC *
      (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) Work.Spaces.Iθ := by
    intro z hz
    have h1 : IntegrableOn (fun θ => Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ)
        Work.Spaces.Iθ := (hm6.1 z hz).const_mul _
    have h2 : IntegrableOn (fun θ => Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)
        Work.Spaces.Iθ := (hm2.1 z hz).const_mul _
    simpa only [Pi.add_apply, IntegrableOn] using (h1.add h2).const_mul MajC
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    intro z hz
    refine integral_mono_of_nonneg ?_ (hmaj_slice z hz) ?_
    · exact Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 6 (fun z θ => X z * f z θ) z θ
    · rw [hIoo]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact hpt z hz θ hθ
  -- integrability of the outer majorant and the evaluation of its integral
  have hA : IntegrableOn (fun z => Blo ^ 2 * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ)) Work.Spaces.Iz := hm6.2.const_mul _
  have hB : IntegrableOn (fun z => Bhi ^ 2 * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 2 f z θ)) Work.Spaces.Iz := hm2.2.const_mul _
  have hae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, MajC * (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
        = MajC * (Blo ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
            + Bhi ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 2 f z θ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    · exact (hm6.1 z hz).const_mul _
    · exact (hm2.1 z hz).const_mul _
  have hmaj_z : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, MajC *
      (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ)) Work.Spaces.Iz := by
    refine ((hA.add hB).const_mul MajC).congr ?_
    filter_upwards [hae] with z hz
    simp only [Pi.add_apply]
    exact hz.symm
  -- the outer comparison
  have houter : (∫ z in Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (fun z θ => X z * f z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, MajC *
          (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ) := by
    refine integral_mono_of_nonneg ?_ hmaj_z ?_
    · exact Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact hslice z hz
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, MajC *
      (Blo ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
        + Bhi ^ 2 * Work.Spaces.HkIntegrand α 2 f z θ))
      = MajC * (Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f) := by
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hA hB, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    unfold Work.Spaces.HkSq
    ring
  have hHkSq := houter.trans_eq hval
  exact hHkSq.trans (by
    have h0 : 0 ≤ Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f :=
      add_nonneg (mul_nonneg (sq_nonneg Blo) (Work.Spaces.HkSq_nonneg α 6 f))
        (mul_nonneg (sq_nonneg Bhi) (Work.Spaces.HkSq_nonneg α 2 f))
    have hle : MajC ≤ MajC + 1 := by linarith
    calc MajC * (Blo ^ 2 * Work.Spaces.HkSq α 6 f + Bhi ^ 2 * Work.Spaces.HkSq α 2 f)
        ≤ (MajC + 1) * (Blo ^ 2 * Work.Spaces.HkSq α 6 f
            + Bhi ^ 2 * Work.Spaces.HkSq α 2 f) :=
          mul_le_mul_of_nonneg_right hle h0)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux