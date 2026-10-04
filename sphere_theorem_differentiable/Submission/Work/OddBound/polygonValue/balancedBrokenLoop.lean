import Mathlib
import Submission.Work.OddBound.design.PolygonValueBoundFamily
import Submission.Work.OddBound.polygonValue.Basic
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygonValue.balancing.Defs
import Submission.Work.OddBound.polygonValue.balancing.Book
import Submission.Work.OddBound.polygonValue.balancing.continuous_fract_comp
import Submission.Work.OddBound.polygonValue.balancing.continuousOn_gLoop
import Submission.Work.OddBound.polygonValue.balancing.gPt_eq_side_Icc
import Submission.Work.OddBound.polygonValue.exists_partition_gPt_affine
import Submission.Work.OddBound.polygonValue.curveLength_gPt_affine
import Submission.Work.OddBound.polygonValue.curveSpeedEqOfAffineLength

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.OddBound.polygonValue

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-- **The concatenation and arclength-balancing half of `Work.OddBound.polygonValue.brokenGeodesicFamily`.**

Given, for every side `i : Fin N` of the based closed `N`-gon family `w`, a *jointly continuous*
family of side curves `S i r τ` (the point at fraction `r` of arclength along the minimising
geodesic of that side at time `τ`) with the constant-speed length formula, the endpoints
(`hS0`, `hS1`: `S i · τ` runs from `gonVert p (w τ) i` to `gonVert p (w τ) (i + 1)`), the two special
slices (`hS0slice`: at `τ = 0` the side is the corresponding arc of the geodesic `γ`; `hS1slice`:
at `τ = 1` everything is the base point), the periodicity `hper` of `γ`, the bound `hLlt` on `L`,
and the fact `hside0` that all `τ = 0` sides have length `L/N`, build the **balanced** closed loop
family `c`: concatenate the `N` side curves into the broken geodesic of each slice, then
reparametrise proportionally to arclength (the `τ`-dependent piecewise affine change of variable
with breakpoints `cumLen τ i / totLen τ`), made `1`-periodic in `s` with `Int.fract`.

The result is exactly the hypothesis package of
`Work.OddBound.liftPiecewise.long_homotopy_lower_bound_piecewise`.  The two halves of the slice at
`τ` have length `totLen τ / 2 = gonLength p (w τ)/2 < π/√K` by `hE` and
`Work.OddBound.gonLength_lt_of_energy_lt`, and at `τ = 0` the balancing map is the identity
(`hside0`), so the slice is `s ↦ γ (L s)`, whose halves have length `L/2 < π/√K` by `hLlt`; the
slice at `τ = 1` is constant at `p`. -/
theorem balancedBrokenLoop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K)
    {p : M} {L : ℝ} (hL : 0 < L) (hLlt : L < 2 * Real.pi / Real.sqrt K) {γ : ℝ → M}
    (hper : ∀ t : ℝ, γ (t + L) = γ t)
    {N : ℕ} (hN : 0 < N)
    {w : ℝ → Fin (N - 1) → M}
    (hw0 : w 0 = fun i : Fin (N - 1) => γ (L * ((i : ℕ) + 1) / N))
    (hw1 : ∀ i : Fin (N - 1), w 1 i = p)
    (hE : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Work.OddBound.gonEnergy (I := I) p (w τ) < 2 * Real.pi ^ 2 / K)
    (hside0 : ∀ i : Fin N, Work.OddBound.gonSideLen (I := I) p (w 0) (i : ℕ) = L / N)
    {S : Fin N → ℝ → ℝ → M}
    (hScont : ∀ i : Fin N, ContinuousOn (fun u : ℝ × ℝ => S i u.1 u.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hS0slice : ∀ (i : Fin N) (r : ℝ), r ∈ Set.Icc (0 : ℝ) 1 →
      S i r 0 = γ (L * ((i : ℕ) + r) / N))
    (hS1slice : ∀ (i : Fin N) (r : ℝ), r ∈ Set.Icc (0 : ℝ) 1 → S i r 1 = p) :
    ∃ c : ℝ → ℝ → M,
      Continuous (fun u : ℝ × ℝ => c u.1 u.2) ∧
      (∀ s t : ℝ, c (s + 1) t = c s t) ∧
      (∀ t : ℝ, c 0 t = p) ∧
      (∀ s : ℝ, c s 0 = γ (L * s)) ∧
      (∀ s : ℝ, c s 1 = p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ (k : ℕ) (a : Fin (k + 1) → ℝ),
        StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
        ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => c s t)
          (Set.Icc (a j.castSucc) (a j.succ))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) 0 (1 / 2)
            < Real.pi / Real.sqrt K ∧
        Submission.Length.curveLength (I := I) (fun s : ℝ => c s t) (1 / 2) 1
            < Real.pi / Real.sqrt K) := by
  classical
  refine ⟨gFam (I := I) p hN w S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) joint continuity of `(s,t) ↦ gFam s t = gLoop (clamp01 t) (Int.fract s)`
    have hG : Continuous (fun q : ℝ × ℝ =>
        gLoop (I := I) p hN w S (clamp01 q.1) q.2) :=
      balancing.continuousOn_gLoop (I := I) (p := p) (N := N) (w := w) (S := S)
        hN hScont hSsm hS0 hS1 hSlen
    have hper' : ∀ x : ℝ, (fun u : ℝ => gLoop (I := I) p hN w S (clamp01 x) u) 1
        = (fun u : ℝ => gLoop (I := I) p hN w S (clamp01 x) u) 0 := fun x =>
      (gLoop_one_eq_p (I := I) (clamp01_mem x) hSsm hS0 hS1 hSlen hN).trans
        (gLoop_zero_eq_p (I := I) (clamp01_mem x) hSsm hS0 hS1 hSlen hN).symm
    have hff := balancing.continuous_fract_comp (X := ℝ)
      (G := fun x u : ℝ => gLoop (I := I) p hN w S (clamp01 x) u) hG hper'
    have h2 : Continuous (fun q : ℝ × ℝ =>
        gLoop (I := I) p hN w S (clamp01 q.2) (Int.fract q.1)) := by
      have hsw : Continuous (Prod.swap : ℝ × ℝ → ℝ × ℝ) := continuous_swap
      simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap] using hff.comp hsw
    simpa only [gFam_def] using h2
  · -- (b) `1`-periodicity in `s`
    intro s t
    simp only [gFam_def, Int.fract_add_one]
  · -- (c) the base point
    intro t
    simp only [gFam_def, Int.fract_zero]
    exact gLoop_zero_eq_p (I := I) (clamp01_mem t) hSsm hS0 hS1 hSlen hN
  · -- (d) the slice at `t = 0` is the geodesic `γ`
    intro s
    have hfract : Int.fract s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩
    rw [gFam_def, clamp01_eq_zero_of_nonpos (le_refl (0 : ℝ)),
      gLoop_zero_slice_eq_gamma (I := I) hN hL hper hside0 hSsm hS0 hS1 hSlen hS0slice hfract]
    exact gamma_mul_fract hper s
  · -- (e) the slice at `t = 1` is constant at `p`
    intro s
    rw [gFam_def, clamp01_eq_one_of_one_le (le_refl (1 : ℝ))]
    exact gLoop_one_slice_eq_p (I := I) hN hw1 hSsm hS0 hS1 hSlen (Int.fract s)
  · -- (f) piecewise `C¹` in `s`
    intro t ht
    have hτeq : clamp01 t = t := clamp01_eq_self ht.1 ht.2
    have hside := balancing.gPt_eq_side_Icc (I := I) (p := p) (N := N) (w := w) (S := S)
      hN ht hSsm hS0 hS1 hSlen
    obtain ⟨k, a, hmono, ha0, ha1, hpiece⟩ :=
      exists_partition_gPt_affine (I := I) (p := p) (N := N) (w := w) (S := S)
        hN ht (fun i => hSsm i t ht) hside
    refine ⟨k, a, hmono, ha0, ha1, ?_⟩
    intro j
    refine (hpiece j).congr (fun s hs => ?_)
    rw [gFam_def, hτeq, gLoop_def]
    have hs0 : 0 ≤ s := by
      have h1 : a 0 ≤ a j.castSucc := hmono.monotone (Fin.zero_le _)
      rw [ha0] at h1
      linarith [hs.1]
    rcases lt_or_ge s 1 with hs1 | hs1
    · rw [Int.fract_eq_self.mpr ⟨hs0, hs1⟩]
    · have hsle : s ≤ 1 := by
        have h1 : a j.succ ≤ a (Fin.last k) := hmono.monotone (Fin.le_last _)
        rw [ha1] at h1
        exact le_trans hs.2 h1
      have hs1' : s = 1 := le_antisymm hsle hs1
      subst hs1'
      rw [Int.fract_one, ← gLoop_def, ← gLoop_def,
        gLoop_zero_eq_p (I := I) ht hSsm hS0 hS1 hSlen hN,
        gLoop_one_eq_p (I := I) ht hSsm hS0 hS1 hSlen hN]
  · -- (g) the two halves have length `totLen/2 < π/√K`
    intro t ht
    have hτeq : clamp01 t = t := clamp01_eq_self ht.1 ht.2
    have hside := balancing.gPt_eq_side_Icc (I := I) (p := p) (N := N) (w := w) (S := S)
      hN ht hSsm hS0 hS1 hSlen
    have hsp : ∀ i : Fin N, ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 →
        Submission.Length.curveSpeed (I := I) (fun r : ℝ => S i r t) r
          = sideLen (I := I) p w t (i : ℕ) := fun i r hr =>
      curveSpeedEqOfAffineLength (I := I) (h := fun r : ℝ => S i r t)
        (hSsm i t ht) (fun a b ha hab hb => hSlen i t ht a b ha hab hb) r hr.1 hr.2
    have hgl1 : Submission.Length.curveLength (I := I)
        (fun s : ℝ => gLoop (I := I) p hN w S t s) 0 (1 / 2)
        = totLen (I := I) p w t * (1 / 2) := by
      simpa only [gLoop_def, sub_zero] using
        curveLength_gPt_affine (I := I) (p := p) (N := N) (w := w) (S := S)
          hN ht (fun i => hSsm i t ht) hside hsp (a := 0) (b := 1 / 2)
          (by norm_num) (by norm_num) (by norm_num)
    have hgl2 : Submission.Length.curveLength (I := I)
        (fun s : ℝ => gLoop (I := I) p hN w S t s) (1 / 2) 1
        = totLen (I := I) p w t * (1 / 2) := by
      have h := curveLength_gPt_affine (I := I) (p := p) (N := N) (w := w) (S := S)
        hN ht (fun i => hSsm i t ht) hside hsp (a := 1 / 2) (b := 1)
        (by norm_num) (by norm_num) (by norm_num)
      have h' : totLen (I := I) p w t * (1 - 1 / 2) = totLen (I := I) p w t * (1 / 2) := by
        norm_num
      rw [h'] at h
      simpa only [gLoop_def] using h
    -- the speed of the `fract`-parametrisation agrees with that of `gLoop` a.e.
    have hslicespeed : ∀ {x : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 →
        Submission.Length.curveSpeed (I := I) (fun s : ℝ => gFam (I := I) p hN w S s t) x
          = Submission.Length.curveSpeed (I := I)
              (fun u : ℝ => gLoop (I := I) p hN w S t u) x := by
      intro x hx
      have hev : (fun s : ℝ => gFam (I := I) p hN w S s t) =ᶠ[𝓝 x]
          (fun u : ℝ => gLoop (I := I) p hN w S t u) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        rw [gFam_def, hτeq, Int.fract_eq_self.mpr ⟨le_of_lt hy.1, hy.2⟩]
      have hxx : gFam (I := I) p hN w S x t = gLoop (I := I) p hN w S t x := hev.eq_of_nhds
      simp only [Submission.Length.curveSpeed_def,
        Submission.Geodesic.curveVelocity_apply]
      rw [hev.mfderiv_eq, hxx]
      -- v4.34: the rewrite leaves a `tangentSpaceCast`, definitionally the identity.
      all_goals first | rfl | (ext v; rfl)
    have hcongr1 : Submission.Length.curveLength (I := I)
        (fun s : ℝ => gFam (I := I) p hN w S s t) 0 (1 / 2)
        = Submission.Length.curveLength (I := I)
            (fun u : ℝ => gLoop (I := I) p hN w S t u) 0 (1 / 2) := by
      rw [Submission.Length.curveLength_def, Submission.Length.curveLength_def]
      exact intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall
        (fun x hx => hslicespeed (by
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
          exact ⟨hx.1, by linarith [hx.2]⟩)))
    have hcongr2 : Submission.Length.curveLength (I := I)
        (fun s : ℝ => gFam (I := I) p hN w S s t) (1 / 2) 1
        = Submission.Length.curveLength (I := I)
            (fun u : ℝ => gLoop (I := I) p hN w S t u) (1 / 2) 1 := by
      have hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc (1 / 2) 1 →
          Submission.Length.curveSpeed (I := I) (fun s : ℝ => gFam (I := I) p hN w S s t) x
            = Submission.Length.curveSpeed (I := I)
                (fun u : ℝ => gLoop (I := I) p hN w S t u) x := by
        refine MeasureTheory.ae_iff.mpr
          (MeasureTheory.measure_mono_null ?_ (measure_singleton 1))
        intro x hx
        rw [Set.mem_ofPred_eq] at hx
        push_neg at hx
        by_contra hx1
        rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hx
        exact hx.2 (hslicespeed ⟨by linarith [hx.1.1],
          lt_of_le_of_ne hx.1.2 (by simpa using hx1)⟩)
      rw [Submission.Length.curveLength_def, Submission.Length.curveLength_def]
      exact intervalIntegral.integral_congr_ae hae
    have hT : totLen (I := I) p w t < 2 * (Real.pi / Real.sqrt K) := by
      have h := Work.OddBound.gonLength_lt_of_energy_lt (I := I) (p := p) (K := K) hK (w t)
        (hE t ht)
      rw [mul_div_assoc] at h
      simpa only [totLen] using h
    refine ⟨?_, ?_⟩
    · rw [hcongr1, hgl1]; linarith
    · rw [hcongr2, hgl2]; linarith

end Work.OddBound.polygonValue
