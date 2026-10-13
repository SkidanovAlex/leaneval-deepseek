/-
# `slot_aPriori` with the missing smoothness hypothesis on the limiting source

The requested `Work.FTS.PhiStar.Honesty.SlotsLimit.slot_aPriori` assumes only `HkMem α (k+1) F`
(no smoothness of `F`) together with `HkSq α (k+1) (G n - F) → 0`; as explained in
`../_refute/NOTES_slot_aPriori_FALSE.md` that statement is false, and the missing hypothesis is
`smoothness of F` — which the consumer `hkMem_slots_of_approx` does carry.

Under `SmoothOpen F` the missing step (the uniform bound and the Cauchy property of the *sources*)
follows from the subadditivity `HkSq α l (u - v) ≤ 2(HkSq α l u + HkSq α l v)`
(`HkSq_sub_le_open`), and `slot_aPriori_of_source` gives the conclusion.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.slot_aPriori_of_source
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.HkSq_sub_le_open
import Submission.Work.FTS.PhiStar.Honesty.ellEstUnif_diff
import Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_sub
import Submission.Work.FTS.GalFields.RHS.HkSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false

/-- **The requested statement with the missing hypothesis `SmoothOpen F`.**

With `F` smooth on the open quadrant, `hconv` and `hF` *do* bound the sources: the subadditivity
`HkSq α l (u - v) ≤ 2(HkSq α l u + HkSq α l v)` (`HkSq_sub_le_open`) applied to
`G n - G m = (G n - F) - (G m - F)` gives `HkSq α (k+1) (G n) ≤ 2(HkSq α (k+1) (G n - F) +
2HkSq α (k+1) F)` and the Cauchy property of the sources, and `slot_aPriori_of_source` finishes.

This is the form the consumer `hkMem_slots_of_approx` (which carries `hsmF : SmoothOpen F`) can
use; it is *not* derivable without smoothness of `F` — see
`../_refute/NOTES_slot_aPriori_FALSE.md`. -/
theorem slot_aPriori_smooth (k : ℕ) (hk : 1 ≤ k) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hsmG : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hGn : ∀ n : ℕ, Work.Spaces.HkMem α (k + 1) (G n))
    (hsmF : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α (k + 1) F)
    (hEll : ∀ n : ℕ, Work.FTS.EllipticEst.TT.EllWeakPos α (k + 1) (G n)
      (Work.FTS.PhiStar.Series.psiSeries α (G n)))
    (hconv : Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α (k + 1)
      (fun z θ => G n z θ - F z θ)) Filter.atTop (nhds 0)) :
    ∃ B : ℝ, 0 < B ∧
      (∀ (r : Fin 3) (n : ℕ), Work.Spaces.HkMem α k
        (slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G n)))) ∧
      (∀ (r : Fin 3) (n : ℕ), Work.Spaces.HkSq α k
        (slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G n))) ≤ B) ∧
      (∀ (r : Fin 3) (n m : ℕ), Work.Spaces.HkMem α k
        (fun z θ => slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G n)) z θ
          - slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G m)) z θ)) ∧
      (∀ r : Fin 3, Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α k
          (fun z θ => slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G nm.1)) z θ
            - slot r.1 (Work.FTS.PhiStar.Series.psiSeries α (G nm.2)) z θ))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) := by
  -- the per-datum honesty of `G n - F`
  have hsubsm : ∀ n, Work.FTS.EllipticEst.SmoothOpen (fun z θ => G n z θ - F z θ) :=
    fun n => Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl (hsmG n) hsmF
  have hsubmem : ∀ n, Work.Spaces.HkMem α (k + 1) (fun z θ => G n z θ - F z θ) :=
    fun n => EllWeakAux.HkMem_sub_of_eqOn_Q0 α (k + 1) (hsmG n) hsmF (hGn n) hF
      (fun _ _ _ _ _ => rfl)
  -- the sequence of sources is bounded
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ n : ℕ, Work.Spaces.HkSq α (k + 1)
      (fun z θ => G n z θ - F z θ) ≤ M := by
    have hEv : ∀ᶠ n : ℕ in Filter.atTop,
        Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - F z θ) < 1 :=
      hconv.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEv
    refine ⟨1 + ∑ n ∈ Finset.range (N + 1), Work.Spaces.HkSq α (k + 1)
      (fun z θ => G n z θ - F z θ), fun n => ?_⟩
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (N + 1), Work.Spaces.HkSq α (k + 1)
        (fun z θ => G i z θ - F z θ) :=
      Finset.sum_nonneg (fun i _ => Work.Spaces.HkSq_nonneg α (k + 1) _)
    by_cases hn : n ≤ N
    · have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
      have hle := Finset.single_le_sum
        (f := fun i => Work.Spaces.HkSq α (k + 1) (fun z θ => G i z θ - F z θ))
        (fun i _ => Work.Spaces.HkSq_nonneg α (k + 1) _) hmem
      linarith
    · have hNn : N ≤ n := by omega
      have h1 := hN n hNn
      linarith
  have hbound : ∃ B : ℝ, ∀ n : ℕ, Work.Spaces.HkSq α (k + 1) (G n) ≤ B := by
    refine ⟨2 * M + 2 * Work.Spaces.HkSq α (k + 1) F, fun n => ?_⟩
    have hsum : (fun z θ => (G n z θ - F z θ) + F z θ) = G n := by funext z θ; ring
    have hadd := Work.FTS.GalFields.RHS.HkSq_add_le_open α (k + 1) hα (hsubsm n) hsmF
      (hsubmem n) hF
    calc Work.Spaces.HkSq α (k + 1) (G n)
        = Work.Spaces.HkSq α (k + 1) (fun z θ => (G n z θ - F z θ) + F z θ) := by rw [hsum]
      _ ≤ 2 * (Work.Spaces.HkSq α (k + 1) (fun z θ => G n z θ - F z θ)
            + Work.Spaces.HkSq α (k + 1) F) := hadd
      _ ≤ 2 * M + 2 * Work.Spaces.HkSq α (k + 1) F := by linarith [hM n]
  -- the sources are Cauchy
  have hcauchy : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α (k + 1)
      (fun z θ => G nm.1 z θ - G nm.2 z θ)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    have hmaj : Filter.Tendsto (fun nm : ℕ × ℕ => 2 * (Work.Spaces.HkSq α (k + 1)
        (fun z θ => G nm.1 z θ - F z θ))
        + 2 * (Work.Spaces.HkSq α (k + 1) (fun z θ => G nm.2 z θ - F z θ)))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
      have h1 : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α (k + 1)
          (fun z θ => G nm.1 z θ - F z θ)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
        hconv.comp Filter.tendsto_fst
      have h2 : Filter.Tendsto (fun nm : ℕ × ℕ => Work.Spaces.HkSq α (k + 1)
          (fun z θ => G nm.2 z θ - F z θ)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
        hconv.comp Filter.tendsto_snd
      simpa using (h1.const_mul 2).add (h2.const_mul 2)
    refine squeeze_zero (fun nm => Work.Spaces.HkSq_nonneg α (k + 1) _) ?_ hmaj
    intro nm
    have hsum2 : (fun z θ => (G nm.1 z θ - F z θ) - (G nm.2 z θ - F z θ))
        = fun z θ => G nm.1 z θ - G nm.2 z θ := by funext z θ; ring
    calc Work.Spaces.HkSq α (k + 1) (fun z θ => G nm.1 z θ - G nm.2 z θ)
        = Work.Spaces.HkSq α (k + 1)
            (fun z θ => (G nm.1 z θ - F z θ) - (G nm.2 z θ - F z θ)) := by rw [hsum2]
      _ ≤ 2 * (Work.Spaces.HkSq α (k + 1) (fun z θ => G nm.1 z θ - F z θ)
            + Work.Spaces.HkSq α (k + 1) (fun z θ => G nm.2 z θ - F z θ)) :=
          HkSq_sub_le_open α (k + 1) (hsubsm nm.1) (hsubsm nm.2) (hsubmem nm.1) (hsubmem nm.2)
      _ = 2 * (Work.Spaces.HkSq α (k + 1) (fun z θ => G nm.1 z θ - F z θ))
            + 2 * (Work.Spaces.HkSq α (k + 1) (fun z θ => G nm.2 z θ - F z θ)) := by ring
  exact slot_aPriori_of_source k hk hα hα4 hsmG hGn hEll hbound hcauchy

end Work.FTS.PhiStar.Honesty.SlotsLimit
