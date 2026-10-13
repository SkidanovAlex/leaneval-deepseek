/-
# `Work.FTS.Apriori.Limit.exists_test_cutoff` — a sequence of test cut-offs

This module constructs, for each `k : ℕ`, a smooth function `η k` on the open quadrant
`Qd = (0,∞) × (0,π/2)` with

* `TestQ (η k)` (smooth on `Qd`, compact support inside `Qd`),
* `0 ≤ η k z θ ≤ 1` everywhere,
* `η k → 1` pointwise on `Qd` as `k → ∞`.

The construction is the obvious exhaustion of `Qd` by the nested closed rectangles

`cutBoxK k = [1/(k+1), k+1] × [1/(k+1), π/2 - 1/(k+1)]`,

together with the open rectangles `cutBoxT k` (slightly larger) and `cutBoxO k` (their
closure).  Mathlib's smooth Urysohn lemma `exists_contDiff_support_eq_eq_one_iff` supplies,
for each `k`, a smooth `f` with support exactly `cutBoxT k` and `f = 1` exactly on `cutBoxK k`;
since `closure (cutBoxT k) = cutBoxO k ⊆ Qd`, this `f` is a legitimate test function, and the
exhaustion gives the pointwise convergence to `1`.
-/
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.Apriori.Limit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

/-- The closed rectangle `[1/(k+1), k+1] × [1/(k+1), π/2 - 1/(k+1)]`, on which the `k`-th
cut-off is required to equal `1`. -/
def cutBoxK (k : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ×ˢ
    Set.Icc (1 / ((k : ℝ) + 1)) (π / 2 - 1 / ((k : ℝ) + 1))

/-- The open rectangle in which the `k`-th cut-off is supported (its support is exactly this
set). -/
def cutBoxT (k : ℕ) : Set (ℝ × ℝ) :=
  Set.Ioo (1 / (2 * ((k : ℝ) + 1))) (2 * ((k : ℝ) + 1)) ×ˢ
    Set.Ioo (1 / (2 * ((k : ℝ) + 1))) (π / 2 - 1 / (2 * ((k : ℝ) + 1)))

/-- The closure of `cutBoxT k`, a compact rectangle contained in the open quadrant `Qd`. -/
def cutBoxO (k : ℕ) : Set (ℝ × ℝ) :=
  Set.Icc (1 / (2 * ((k : ℝ) + 1))) (2 * ((k : ℝ) + 1)) ×ˢ
    Set.Icc (1 / (2 * ((k : ℝ) + 1))) (π / 2 - 1 / (2 * ((k : ℝ) + 1)))

lemma cutBoxK_subset_T (k : ℕ) : cutBoxK k ⊆ cutBoxT k := by
  intro p hp
  simp only [cutBoxK, cutBoxT, mem_prod, mem_Icc, mem_Ioo] at *
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlt : 1 / (2 * ((k : ℝ) + 1)) < 1 / ((k : ℝ) + 1) := by
    apply one_div_lt_one_div_of_lt hk
    linarith
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma cutBoxT_subset_O (k : ℕ) : cutBoxT k ⊆ cutBoxO k := by
  intro p hp
  simp only [cutBoxT, cutBoxO, mem_prod, mem_Icc, mem_Ioo] at *
  exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, le_of_lt hp.2.1, le_of_lt hp.2.2⟩

lemma isOpen_cutBoxT (k : ℕ) : IsOpen (cutBoxT k) :=
  (isOpen_Ioo (a := 1 / (2 * ((k : ℝ) + 1))) (b := 2 * ((k : ℝ) + 1))).prod
    (isOpen_Ioo (a := 1 / (2 * ((k : ℝ) + 1))) (b := π / 2 - 1 / (2 * ((k : ℝ) + 1))))

lemma isClosed_cutBoxK (k : ℕ) : IsClosed (cutBoxK k) :=
  (isClosed_Icc (a := 1 / ((k : ℝ) + 1)) (b := (k : ℝ) + 1)).prod
    (isClosed_Icc (a := 1 / ((k : ℝ) + 1)) (b := π / 2 - 1 / ((k : ℝ) + 1)))

lemma isClosed_cutBoxO (k : ℕ) : IsClosed (cutBoxO k) :=
  (isClosed_Icc (a := 1 / (2 * ((k : ℝ) + 1))) (b := 2 * ((k : ℝ) + 1))).prod
    (isClosed_Icc (a := 1 / (2 * ((k : ℝ) + 1))) (b := π / 2 - 1 / (2 * ((k : ℝ) + 1))))

lemma isCompact_cutBoxO (k : ℕ) : IsCompact (cutBoxO k) :=
  (isCompact_Icc (a := 1 / (2 * ((k : ℝ) + 1))) (b := 2 * ((k : ℝ) + 1))).prod
    (isCompact_Icc (a := 1 / (2 * ((k : ℝ) + 1))) (b := π / 2 - 1 / (2 * ((k : ℝ) + 1))))

lemma closure_cutBoxT_subset_O (k : ℕ) : closure (cutBoxT k) ⊆ cutBoxO k :=
  closure_minimal (cutBoxT_subset_O k) (isClosed_cutBoxO k)

lemma cutBoxO_subset_Qd (k : ℕ) : cutBoxO k ⊆ Qd := by
  intro p hp
  simp only [cutBoxO, Qd, mem_prod, mem_Icc, mem_Ioi, mem_Ioo] at *
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have hpos : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by positivity
  have hlt : π / 2 - 1 / (2 * ((k : ℝ) + 1)) < π / 2 := by linarith
  exact ⟨lt_of_lt_of_le hpos h1, lt_of_lt_of_le hpos h3, lt_of_le_of_lt h4 hlt⟩

/-- For every `k` there is a smooth function with support exactly `cutBoxT k` and equal to `1`
on `cutBoxK k`.  It is a test function of the quadrant: its topological support is contained in
`cutBoxO k ⊆ Qd`. -/
lemma exists_smooth_cutoff (k : ℕ) :
    ∃ f : ℝ × ℝ → ℝ,
      ContDiff ℝ Work.Stability.smoothOrder f ∧ Set.range f ⊆ Set.Icc 0 1 ∧
      Function.support f = cutBoxT k ∧
      tsupport f ⊆ Qd ∧ HasCompactSupport f ∧ ∀ p ∈ cutBoxK k, f p = 1 := by
  obtain ⟨f, hcd, hrange, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) (isOpen_cutBoxT k) (isClosed_cutBoxK k)
      (cutBoxK_subset_T k)
  refine ⟨f, ?_, hrange, hsupp, ?_, ?_, fun p hp => (hone p).1 hp⟩
  · simpa only [Work.Stability.smoothOrder] using hcd
  · intro p hp
    exact (cutBoxO_subset_Qd k) ((closure_cutBoxT_subset_O k) (closure_mono (le_of_eq hsupp) hp))
  · have ht : tsupport f ⊆ cutBoxO k := fun p hp =>
      (closure_cutBoxT_subset_O k) (closure_mono (le_of_eq hsupp) hp)
    exact (isCompact_cutBoxO k).of_isClosed_subset (isClosed_tsupport f) ht

/-- Every point of the open quadrant eventually lies in the exhausting rectangle `cutBoxK k`. -/
lemma eventually_mem_cutBoxK (z θ : ℝ) (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    ∀ᶠ k in Filter.atTop, (z, θ) ∈ cutBoxK k := by
  have h1 : ∀ᶠ (k : ℕ) in Filter.atTop, 1 / ((k : ℝ) + 1) ≤ z :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (eventually_le_nhds hz)
  have h2 : ∀ᶠ (k : ℕ) in Filter.atTop, z ≤ (k : ℝ) + 1 :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (z - 1))).mono
      (fun k hk => by linarith)
  have h3 : ∀ᶠ (k : ℕ) in Filter.atTop, 1 / ((k : ℝ) + 1) ≤ θ :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (eventually_le_nhds hθ)
  have h4 : ∀ᶠ (k : ℕ) in Filter.atTop, θ ≤ π / 2 - 1 / ((k : ℝ) + 1) :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_le_nhds (by linarith : (0 : ℝ) < π / 2 - θ))).mono
      (fun k hk => by linarith)
  filter_upwards [h1, h2, h3, h4] with k hk1 hk2 hk3 hk4
  simpa only [cutBoxK, mem_prod, mem_Icc] using ⟨⟨hk1, hk2⟩, hk3, hk4⟩

theorem exists_test_cutoff :
    ∃ η : ℕ → ℝ → ℝ → ℝ,
      (∀ k, Work.FTS.Apriori.Limit.TestQ (η k)) ∧
      (∀ k z θ, 0 ≤ η k z θ ∧ η k z θ ≤ 1) ∧
      (∀ z θ, (z, θ) ∈ Work.FTS.Apriori.Limit.Qd →
        Filter.Tendsto (fun k => η k z θ) Filter.atTop (nhds 1)) := by
  choose F hF using exists_smooth_cutoff
  have hcd : ∀ k, ContDiff ℝ Work.Stability.smoothOrder (F k) := fun k => (hF k).1
  have hrange : ∀ k, Set.range (F k) ⊆ Set.Icc 0 1 := fun k => (hF k).2.1
  have hts : ∀ k, tsupport (F k) ⊆ Qd := fun k => (hF k).2.2.2.1
  have hcs : ∀ k, HasCompactSupport (F k) := fun k => (hF k).2.2.2.2.1
  have hone : ∀ k p, p ∈ cutBoxK k → F k p = 1 := fun k => (hF k).2.2.2.2.2
  have hun : ∀ k, Function.uncurry (fun z θ => F k (z, θ)) = F k := fun k => by
    funext p; obtain ⟨a, b⟩ := p; rfl
  refine ⟨fun k z θ => F k (z, θ), ?_, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_, ?_⟩
    · rw [hun k]; exact (hcd k).contDiffOn (s := Qd)
    · rw [hun k]; exact hcs k
    · rw [hun k]; exact hts k
  · intro k z θ
    exact (hrange k) (Set.mem_range_self (z, θ))
  · intro z θ hp
    have hz : 0 < z := hp.1
    have hθ : 0 < θ := hp.2.1
    have hθ2 : θ < π / 2 := hp.2.2
    have hev : (fun _ : ℕ => (1 : ℝ)) =ᶠ[Filter.atTop] (fun k : ℕ => F k (z, θ)) := by
      filter_upwards [eventually_mem_cutBoxK z θ hz hθ hθ2] with k hk
      exact (hone k (z, θ) hk).symm
    exact tendsto_const_nhds.congr' hev

end Work.FTS.Apriori.Limit
