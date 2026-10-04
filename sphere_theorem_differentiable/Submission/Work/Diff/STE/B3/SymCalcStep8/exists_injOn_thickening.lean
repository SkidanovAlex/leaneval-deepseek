import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.localInvKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

open Set Filter Metric

/-- **Injectivity of a locally invertible map on a thickening of a compact set.**

If `θ : (ι → ℝ) → (ι → ℝ)` is smooth, `K` is compact, `θ` is injective on `K` and the Jacobian
determinant of `θ` does not vanish on `K`, then `θ` is injective on a `Metric.thickening ε K` for
some `ε > 0`.

This is the "uniformity" step of the local-inverse construction of `localInverseData`: the
hypotheses are pointwise on the compact `K`, and compactness upgrades them to a uniform
neighbourhood.

Route (the usual compactness/sequence argument):

* If no `ε > 0` worked, there would be pairs `q n = (x n, y n)` with
  `x n, y n ∈ Metric.thickening (1/(n+1)) K`, `θ (x n) = θ (y n)` and `x n ≠ y n`.
* All `q n` lie in the compact set `Metric.cthickening 1 K ×ˢ Metric.cthickening 1 K`, so a
  subsequence converges to some `a`.  Since the (closed) set on which `θ ∘ fst = θ ∘ snd` contains
  every `q n`, it contains `a`, i.e. `θ a.1 = θ a.2`.
* From `Metric.mem_thickening_iff` one gets points `k n ∈ K` with `dist (x n) (k n) < 1/(n+1)`,
  hence `k n → a.1` and, `K` being closed, `a.1 ∈ K`; likewise `a.2 ∈ K`.
* Injectivity on `K` gives `a.1 = a.2 =: c ∈ K`, and `lid_injOn_nhds` (the inverse function
  theorem, in `localInvKit`) gives a neighbourhood `U ∋ c` on which `θ` is injective.  But `U`
  contains both coordinates of almost every `q n` along the subsequence, forcing `x n = y n` — a
  contradiction. -/
theorem exists_injOn_thickening {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (K : Set (ι → ℝ)) (hK : IsCompact K) (hinj : Set.InjOn θ K)
    (hdet : ∀ z ∈ K, (fderiv ℝ θ z).det ≠ 0) :
    ∃ ε > 0, ∀ x y, x ∈ Metric.thickening ε K → y ∈ Metric.thickening ε K → θ x = θ y → x = y := by
  by_contra hcon
  push Not at hcon
  -- bad pairs at every scale
  have hbad : ∀ n : ℕ, ∃ p : (ι → ℝ) × (ι → ℝ),
      p.1 ∈ Metric.thickening (1 / (↑n + 1) : ℝ) K ∧
      p.2 ∈ Metric.thickening (1 / (↑n + 1) : ℝ) K ∧ θ p.1 = θ p.2 ∧ p.1 ≠ p.2 := by
    intro n
    obtain ⟨x, y, hx, hy, hxy, hne⟩ := hcon (1 / (↑n + 1) : ℝ) (by positivity)
    exact ⟨(x, y), hx, hy, hxy, hne⟩
  let q : ℕ → (ι → ℝ) × (ι → ℝ) := fun n => Classical.choose (hbad n)
  have hq : ∀ n : ℕ, (q n).1 ∈ Metric.thickening (1 / (↑n + 1) : ℝ) K ∧
      (q n).2 ∈ Metric.thickening (1 / (↑n + 1) : ℝ) K ∧ θ (q n).1 = θ (q n).2 ∧ (q n).1 ≠ (q n).2 :=
    fun n => Classical.choose_spec (hbad n)
  -- all the bad pairs lie in a compact set
  have hcomp : IsCompact (Metric.cthickening 1 K ×ˢ Metric.cthickening 1 K) :=
    (hK.cthickening).prod hK.cthickening
  have hqmem : ∀ n, q n ∈ Metric.cthickening 1 K ×ˢ Metric.cthickening 1 K := by
    intro n
    have hle : (1 / (↑n + 1) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact ⟨Metric.thickening_subset_cthickening 1 K (Metric.thickening_mono hle K (hq n).1),
           Metric.thickening_subset_cthickening 1 K (Metric.thickening_mono hle K (hq n).2.1)⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hqmem
  have hlim' : Tendsto (q ∘ φ) atTop (nhds a.1 ×ˢ nhds a.2) := by
    rw [← nhds_prod_eq]; exact hlim
  have hlim1 : Tendsto (fun n => (q (φ n)).1) atTop (nhds a.1) := hlim'.fst
  have hlim2 : Tendsto (fun n => (q (φ n)).2) atTop (nhds a.2) := hlim'.snd
  have h1div : Tendsto (fun n : ℕ => (1:ℝ) / (↑(φ n) + 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  -- the first coordinates converge to a point of `K`
  have hx1 : ∀ n : ℕ, ∃ z ∈ K, dist ((q (φ n)).1) z < (1:ℝ) / (↑(φ n) + 1) :=
    fun n => Metric.mem_thickening_iff.mp (hq (φ n)).1
  choose k hkK hkdist using hx1
  have hktend : Tendsto k atTop (nhds a.1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (f := fun n => dist (k n) a.1)
      (g := fun n => (1:ℝ) / (↑(φ n) + 1) + dist ((q (φ n)).1) a.1)
      (fun n => dist_nonneg) (fun n => ?_) ?_
    · calc dist (k n) a.1 ≤ dist (k n) ((q (φ n)).1) + dist ((q (φ n)).1) a.1 := dist_triangle _ _ _
        _ ≤ 1 / (↑(φ n) + 1) + dist ((q (φ n)).1) a.1 := by
            rw [dist_comm (k n) ((q (φ n)).1)]
            exact add_le_add (le_of_lt (hkdist n)) le_rfl
    · have h2 : Tendsto (fun n => dist ((q (φ n)).1) a.1) atTop (nhds 0) :=
        tendsto_iff_dist_tendsto_zero.mp hlim1
      simpa using h1div.add h2
  have ha1K : a.1 ∈ K := hK.isClosed.mem_of_tendsto hktend (Eventually.of_forall hkK)
  -- and so do the second coordinates
  have hx2 : ∀ n : ℕ, ∃ z ∈ K, dist ((q (φ n)).2) z < (1:ℝ) / (↑(φ n) + 1) :=
    fun n => Metric.mem_thickening_iff.mp (hq (φ n)).2.1
  choose l hlK hldist using hx2
  have hltend : Tendsto l atTop (nhds a.2) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (f := fun n => dist (l n) a.2)
      (g := fun n => (1:ℝ) / (↑(φ n) + 1) + dist ((q (φ n)).2) a.2)
      (fun n => dist_nonneg) (fun n => ?_) ?_
    · calc dist (l n) a.2 ≤ dist (l n) ((q (φ n)).2) + dist ((q (φ n)).2) a.2 := dist_triangle _ _ _
        _ ≤ 1 / (↑(φ n) + 1) + dist ((q (φ n)).2) a.2 := by
            rw [dist_comm (l n) ((q (φ n)).2)]
            exact add_le_add (le_of_lt (hldist n)) le_rfl
    · have h2 : Tendsto (fun n => dist ((q (φ n)).2) a.2) atTop (nhds 0) :=
        tendsto_iff_dist_tendsto_zero.mp hlim2
      simpa using h1div.add h2
  have ha2K : a.2 ∈ K := hK.isClosed.mem_of_tendsto hltend (Eventually.of_forall hlK)
  -- the two limit points have the same image, hence coincide
  have hclosedT : IsClosed {p : (ι → ℝ) × (ι → ℝ) | θ p.1 = θ p.2} :=
    isClosed_eq (hθ.continuous.comp continuous_fst) (hθ.continuous.comp continuous_snd)
  have hθeq : θ a.1 = θ a.2 :=
    hclosedT.mem_of_tendsto hlim (Eventually.of_forall fun n => (hq (φ n)).2.2.1)
  have haeq : a.1 = a.2 := hinj ha1K ha2K hθeq
  -- local injectivity at the common limit point contradicts the badness of the pairs
  obtain ⟨U, hU, hinjU⟩ := lid_injOn_nhds θ hθ (hdet a.1 ha1K)
  have hev1 : ∀ᶠ n in atTop, (q (φ n)).1 ∈ U := hlim'.fst hU
  have hev2 : ∀ᶠ n in atTop, (q (φ n)).2 ∈ U := hlim'.snd (haeq ▸ hU)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  exact (hq (φ n)).2.2.2 (hinjU hn1 hn2 (hq (φ n)).2.2.1)

end Work.Diff.STE.B3.SymCalcStep8
