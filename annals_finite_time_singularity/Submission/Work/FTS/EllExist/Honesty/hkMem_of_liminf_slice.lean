import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.HkMem_of_majorant_ae
import Submission.Work.FTS.EllExist.Honesty.integrable_and_integral_le_liminf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

/-
**`HkMem α k f` and `HkSq α k f ≤ C` from a pointwise `liminf` domination.**

The hypotheses say that, for every `z ∈ Iz`, the angular slice `θ ↦ HkIntegrand α k f z θ`
is dominated a.e. (in `θ`, w.r.t. `volume.restrict Iθ`) by the pointwise limit inferior of
the slices of a sequence `fs n` of `HkMem`-functions whose `z`-slices are bounded by a
`z`-dependent constant `B z` ("`hz`"), and whose global `HkSq`-norms are bounded by `C`
("`hb`").

The proof is Fatou's lemma, applied twice:

* **slice level.**  For each `z ∈ Iz` we apply
  `integrable_and_integral_le_liminf` to the sequence `n ↦ HkIntegrand α k (fs n) z ·`
  (integrable on `Iθ` by `hfs n`, nonnegative everywhere, with integrals bounded by `B z`)
  and the function `HkIntegrand α k f z ·` (a.e. strongly measurable by `hsl`, nonnegative
  everywhere, dominated a.e. by the `liminf` by `hae`).  This gives both the integrability
  of each angular slice of `f` — the first half of `HkMem α k f` — and the pointwise bound
  `∫_θ HkIntegrand α k f z θ ≤ liminf_n ∫_θ HkIntegrand α k (fs n) z θ`.

* **outer level.**  The same lemma applied to `u n := (z ↦ ∫_θ HkIntegrand α k (fs n) z θ)`
  (integrable by `hfs n`, nonnegative, with integrals `HkSq α k (fs n) ≤ C`) and
  `h := (z ↦ ∫_θ HkIntegrand α k f z θ)` (a.e. strongly measurable by `houter`,
  nonnegative, and dominated a.e. in `z` by the slice-level bound just proved) gives the
  integrability of the outer function — the second half of `HkMem α k f` — together with
  `HkSq α k f ≤ liminf_n HkSq α k (fs n) ≤ C`, the last step because every term of the
  sequence is `≤ C`.

The two applications are the content of `Work.FTS.EllExist.Honesty.integrable_and_integral_le_liminf`
(slice-level Fatou with an a.e. domination by a pointwise `liminf`, whose conclusion bundles
the integrability of the dominated function with the bound on its integral).
-/

theorem hkMem_of_liminf_slice {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {fs : ℕ → ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hfs : ∀ n, Work.Spaces.HkMem α k (fs n))
    (hb : ∀ n, Work.Spaces.HkSq α k (fs n) ≤ C)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (houter : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hae : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α k f z θ
        ≤ Filter.liminf (fun n => Work.Spaces.HkIntegrand α k (fs n) z θ) Filter.atTop)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ B : ℝ, ∀ n,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fs n) z θ) ≤ B) :
    Work.Spaces.HkMem α k f ∧ Work.Spaces.HkSq α k f ≤ C := by
  -- the per-slice bounds `B z` may be taken nonnegative, since they bound an integral of a
  -- pointwise nonnegative integrand
  have hB0 : ∀ z ∈ Work.Spaces.Iz, ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fs n) z θ) ≤ B := by
    intro z hz1
    obtain ⟨B, hB⟩ := hz z hz1
    exact ⟨B, le_trans (MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (fs 0) z θ))
      (hB 0), hB⟩
  -- slice level: each angular slice of `HkIntegrand α k f` is integrable on `Iθ`, and it is
  -- bounded in integral by the `liminf` of the slices of the `fs n`
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz1
    obtain ⟨B, hB0', hB⟩ := hB0 z hz1
    exact (integrable_and_integral_le_liminf
      (u := fun n θ => Work.Spaces.HkIntegrand α k (fs n) z θ)
      (h := fun θ => Work.Spaces.HkIntegrand α k f z θ) (D := B)
      (fun n => (hfs n).1 z hz1)
      (fun n => Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fs n) z θ)
      hB hB0' (hsl z hz1)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (hae z hz1)).1
  -- hence the same domination holds a.e. in `z` for the `θ`-integrals
  have hslice_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) z
        ≤ (fun a => Filter.liminf (fun n => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fs n) a θ) Filter.atTop) z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz1
    obtain ⟨B, hB0', hB⟩ := hB0 z hz1
    exact (integrable_and_integral_le_liminf
      (u := fun n θ => Work.Spaces.HkIntegrand α k (fs n) z θ)
      (h := fun θ => Work.Spaces.HkIntegrand α k f z θ) (D := B)
      (fun n => (hfs n).1 z hz1)
      (fun n => Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (fs n) z θ)
      hB hB0' (hsl z hz1)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (hae z hz1)).2
  -- outer level: the `θ`-integral of `HkIntegrand α k f` is integrable in `z`, and its
  -- integral is bounded by the `liminf` of the `HkSq`-norms of the `fs n`
  have hmain : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz)
      ∧ (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ Filter.liminf (fun n => Work.Spaces.HkSq α k (fs n)) Filter.atTop := by
    refine integrable_and_integral_le_liminf
      (u := fun n z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fs n) z θ)
      (h := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) (D := C)
      (fun n => (hfs n).2)
      (fun n => Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (fs n) z θ))
      (fun n => hb n) hC houter
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
      hslice_le
  -- the liminf of a sequence bounded above by `C` is at most `C`
  have hlim : Filter.liminf (fun n => Work.Spaces.HkSq α k (fs n)) Filter.atTop ≤ C := by
    refine Filter.liminf_le_of_le ⟨0, ?_⟩ ?_
    · rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall fun n => Work.Spaces.HkSq_nonneg α k (fs n)
    · intro b hb''
      obtain ⟨n, hn⟩ := hb''.exists
      exact le_trans hn (hb n)
  exact ⟨⟨hslice, hmain.1⟩, le_trans hmain.2 hlim⟩

end Work.FTS.EllExist.Honesty
