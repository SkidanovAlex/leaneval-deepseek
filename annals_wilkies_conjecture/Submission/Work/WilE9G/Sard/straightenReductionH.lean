import Mathlib
import Submission.Work.WilE9G.Sard.FlatDefs
import Submission.Work.WilE9G.Sard.null_of_normalForm
import Submission.Work.WilE9G.Sard.exists_coord_of_ne_zero
import Submission.Work.WilE9G.Sard.exists_local_diffeomorph_update
import Submission.Work.WilE9G.Sard.isBounded_insertNth_preimage_closedBall

/-!
# The rank-positive step of the Morse–Sard induction: straightening

`straightenReductionH`: given Morse–Sard in target dimension `m - 1` (in the bounded form
`SardGB (m-1)`), for a map `F : ℝ^d → ℝ^m` which is analytic at the points of a set
`A ⊆ critSet F`, the values of `F` on `A ∩ ball x δ` are null for some `δ > 0`, provided
`fderiv ℝ F x ≠ 0`.

The proof straightens one component of `F` by a local analytic change of variables `Φ`
(`exists_local_diffeomorph_update`), turning `F`, in the new coordinates, into an insertion of the
last coordinate into a map to `ℝ^{m-1}`; the critical set then becomes the union over `c` of the
critical sets of the slices, and Fubini together with the induction hypothesis for target dimension
`m - 1` gives nullity.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Filter
open scoped Topology

namespace Work.WilE9G.Sard

/-! ## The sliced step, in bounded form -/

/-- **The regular (normal form) slice reduction of Morse–Sard, bounded form.**

If `g : ℝ^{k+1} → ℝ^{n+1}` is analytic at `y₀` and, near `y₀`, its `i`-th component is the `j`-th
coordinate, then the critical values of `g` over a neighbourhood of `y₀` are null, given the
bounded Morse–Sard statement in target dimension `n`.

The proof slices the domain along the coordinate `j`: writing `z = insertNth j c w`, the critical
set of `g` in the ball maps into the union, over `c`, of the critical sets of the slice maps
`w ↦ dropJ i (g (insertNth j c w)) : ℝ^k → ℝ^n`; each of these has null image by the induction
hypothesis (applied to the bounded set of `w` whose insertion lies in the ball), and the resulting
set has null slices, hence is null by Fubini. -/
theorem null_of_normalForm_bdd {k n : ℕ} {g : (Fin (k + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {y₀ : Fin (k + 1) → ℝ} (hg : AnalyticAt ℝ g y₀) (i : Fin (n + 1)) (j : Fin (k + 1))
    (hnorm : ∀ᶠ y in nhds y₀, g y i = y j)
    (H : ∀ (d' : ℕ) (G : (Fin d' → ℝ) → (Fin n → ℝ)) (B : Set (Fin d' → ℝ)),
      Bornology.IsBounded B → (∀ z ∈ B, AnalyticAt ℝ G z) →
      MeasureTheory.volume (G '' (critSet G ∩ B)) = 0) :
    ∃ W : Set (Fin (k + 1) → ℝ), IsOpen W ∧ y₀ ∈ W ∧
      MeasureTheory.volume (g '' (critSet g ∩ W)) = 0 := by
  classical
  have hmem : ∀ᶠ y in nhds y₀, AnalyticAt ℝ g y ∧ g y i = y j :=
    hg.eventually_analyticAt.and hnorm
  obtain ⟨R, hRpos, hR⟩ := Metric.mem_nhds_iff.mp hmem
  set ρ : ℝ := R / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hcb : Metric.closedBall y₀ ρ ⊆ Metric.ball y₀ R := by
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    rw [dist_eq_norm] at hy ⊢
    rw [hρdef] at hy
    linarith
  have hWf : ∀ y ∈ Metric.closedBall y₀ ρ, AnalyticAt ℝ g y ∧ g y i = y j :=
    fun y hy => hR (hcb hy)
  have hdf : ∀ y ∈ Metric.closedBall y₀ ρ, DifferentiableAt ℝ g y :=
    fun y hy => (hWf y hy).1.differentiableAt
  -- the joint slice map
  let Hm : (Fin k → ℝ) × ℝ → (Fin n → ℝ) :=
    fun q => dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j q.2 q.1))
  -- the compact piece of the critical set
  set Scrit : Set (Fin (k + 1) → ℝ) := Metric.closedBall y₀ ρ ∩ critSet g with hScritdef
  -- the map sending a critical point to its critical value in split coordinates
  let Λ : (Fin (k + 1) → ℝ) → ℝ × (Fin n → ℝ) := fun z => (z j, dropJ i (g z))
  set T : Set (ℝ × (Fin n → ℝ)) := Λ '' Scrit with hTdef
  have hScritcomp : IsCompact Scrit := by
    rw [hScritdef]
    exact aux_compact_critSet (f := g) (c := y₀) (ρ := ρ) fun x hx =>
      (AnalyticAt.contDiffAt (hWf x hx).1 : ContDiffAt ℝ 1 g x).continuousAt_fderiv one_ne_zero
  have hΛcont : ContinuousOn Λ Scrit := by
    intro z hz
    obtain ⟨hz1, _⟩ := hz
    have hgc : ContinuousAt g z := (hWf z hz1).1.continuousAt
    have h1 : ContinuousWithinAt (fun z : Fin (k + 1) → ℝ => z j) Scrit z :=
      (continuous_apply j).continuousAt.continuousWithinAt
    have h2 : ContinuousWithinAt (fun z : Fin (k + 1) → ℝ => dropJ i (g z)) Scrit z :=
      (ContinuousAt.comp ((dropJ i).continuous.continuousAt) hgc).continuousWithinAt
    exact h1.prodMk h2
  have hTcomp : IsCompact T := by
    rw [hTdef]
    exact hScritcomp.image_of_continuousOn hΛcont
  have hTmeas : MeasurableSet T := hTcomp.measurableSet
  -- the slices of `T` are null
  have hslice : ∀ c : ℝ, volume {v : Fin n → ℝ | (c, v) ∈ T} = 0 := by
    intro c
    set Uc : Set (Fin k → ℝ) :=
      {w | Fin.insertNth (α := fun _ => ℝ) j c w ∈ Metric.closedBall y₀ ρ} with hUcdef
    have hUcbdd : Bornology.IsBounded Uc := isBounded_insertNth_preimage_closedBall j c y₀ ρ
    have hUcan : ∀ w ∈ Uc, AnalyticAt ℝ (fun w' : Fin k → ℝ =>
        dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j c w'))) w := by
      intro w hw
      exact analyticAt_slice j i (fun y hy => (hWf y hy).1) hw
    have hHnull := H k (fun w' : Fin k → ℝ =>
      dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j c w'))) Uc hUcbdd hUcan
    have hsub : {v : Fin n → ℝ | (c, v) ∈ T} ⊆
        (fun w : Fin k → ℝ =>
          dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j c w))) ''
          (critSet (fun w : Fin k → ℝ =>
            dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j c w))) ∩ Uc) := by
      intro v hv
      rw [hTdef] at hv
      obtain ⟨z, hzScrit, hzLam⟩ := hv
      obtain ⟨hz1, hz2⟩ := hzScrit
      have hzj : z j = c := congrArg Prod.fst hzLam
      have hzv : dropJ i (g z) = v := congrArg Prod.snd hzLam
      have hzd : Fin.insertNth (α := fun _ => ℝ) j c (dropJ j z) = z := by
        rw [← hzj]; exact insertNth_dropJ j z
      have hcrit : ¬ Function.Surjective (fderiv ℝ (fun w' : Fin k → ℝ =>
          dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j c w'))) (dropJ j z)) := by
        intro hsurj
        have hkey := aux_slice_criticality (g := g) (H := Hm) (w := dropJ j z) (t := c) j i
          (by rw [hzd]; exact hdf z hz1)
          (analyticAt_sliceMap j i (fun y hy => (hWf y hy).1)
            (show Fin.insertNth (α := fun _ => ℝ) j c (dropJ j z) ∈ Metric.closedBall y₀ ρ by
              rw [hzd]; exact hz1)).differentiableAt
          (by
            have hopen : IsOpen {q : (Fin k → ℝ) × ℝ |
                Fin.insertNth (α := fun _ => ℝ) j q.2 q.1 ∈ Metric.ball y₀ R} :=
              Metric.isOpen_ball.preimage (continuous_iff_continuousAt.mpr fun q =>
                (analyticAt_insI j q).continuousAt)
            have hmemq : (dropJ j z, c) ∈ {q : (Fin k → ℝ) × ℝ |
                Fin.insertNth (α := fun _ => ℝ) j q.2 q.1 ∈ Metric.ball y₀ R} := by
              show Fin.insertNth (α := fun _ => ℝ) j c (dropJ j z) ∈ Metric.ball y₀ R
              rw [hzd]; exact hcb hz1
            filter_upwards [hopen.mem_nhds hmemq] with q hq
            have hqj : g (Fin.insertNth (α := fun _ => ℝ) j q.2 q.1) i = q.2 :=
              (hR hq).2.trans (Fin.insertNth_apply_same (α := fun _ => ℝ) j q.2 q.1)
            show g (Fin.insertNth (α := fun _ => ℝ) j q.2 q.1) =
              Fin.insertNth (α := fun _ => ℝ) i q.2
                (dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j q.2 q.1)))
            simpa only [hqj] using
              (insertNth_dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j q.2 q.1))).symm)
          hsurj
        rw [hzd] at hkey
        exact hz2 hkey
      refine ⟨dropJ j z, ⟨?_, ?_⟩, ?_⟩
      · exact hcrit
      · show Fin.insertNth (α := fun _ => ℝ) j c (dropJ j z) ∈ Metric.closedBall y₀ ρ
        rw [hzd]; exact hz1
      · show dropJ i (g (Fin.insertNth (α := fun _ => ℝ) j c (dropJ j z))) = v
        rw [hzd]; exact hzv
    exact le_antisymm ((measure_mono hsub).trans (le_of_eq hHnull)) bot_le
  have hTnull : volume T = 0 :=
    Work.WilE2.RegVals.volume_eq_zero_of_slices_null_real hTmeas hslice
  have hnullT : volume
      ((⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm) '' T) = 0 := by
    rw [Work.WilE2.image_null_iff_of_measurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm)
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm T]
    exact hTnull
  refine ⟨Metric.ball y₀ ρ, Metric.isOpen_ball, Metric.mem_ball_self hρpos, ?_⟩
  refine measure_mono_null ?_ hnullT
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨hzcrit, hzball⟩ := hz
  have hzcb : z ∈ Metric.closedBall y₀ ρ := Metric.ball_subset_closedBall hzball
  have hzScrit : z ∈ Scrit := by rw [hScritdef]; exact ⟨hzcb, hzcrit⟩
  have hzWf := hWf z hzcb
  refine ⟨Λ z, ?_, ?_⟩
  · rw [hTdef]; exact ⟨z, hzScrit, rfl⟩
  · rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
    show Fin.insertNth (α := fun _ => ℝ) i (z j) (dropJ i (g z)) = g z
    rw [← hzWf.2]
    exact insertNth_dropJ i (g z)

/-! ## The straightening reduction -/

theorem straightenReductionH {d m : ℕ} (hm : 1 ≤ m)
    (H : ∀ (d' : ℕ) (G : (Fin d' → ℝ) → (Fin (m - 1) → ℝ)) (B : Set (Fin d' → ℝ)),
      Bornology.IsBounded B → (∀ z ∈ B, AnalyticAt ℝ G z) →
      MeasureTheory.volume (G '' (critSet G ∩ B)) = 0)
    (F : (Fin d → ℝ) → (Fin m → ℝ)) (A : Set (Fin d → ℝ)) (hcrit : A ⊆ critSet F)
    (han : ∀ x ∈ A, AnalyticAt ℝ F x) (x : Fin d → ℝ) (hx : x ∈ A)
    (hne : fderiv ℝ F x ≠ 0) :
    ∃ δ > 0, MeasureTheory.volume (F '' (A ∩ Metric.ball x δ)) = 0 := by
  classical
  -- a non-zero derivative has a non-zero matrix coefficient
  obtain ⟨i, j, hij⟩ := exists_coord_of_ne_zero (fderiv ℝ F x) hne
  have hdpos : 1 ≤ d := by have h := j.isLt; omega
  -- rewrite the dimensions as successors
  obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, (Nat.sub_add_cancel hdpos).symm⟩
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  subst hk
  subst hn
  -- the scalar component `z ↦ F z i`
  have hfan : AnalyticAt ℝ (fun z : Fin (k + 1) → ℝ => F z i) x :=
    (analyticAt_pi_iff.mp (han x hx)) i
  have hfd : fderiv ℝ (fun z : Fin (k + 1) → ℝ => F z i) x
      = (ContinuousLinearMap.proj i).comp (fderiv ℝ F x) :=
    Work.WilE2.fderiv_coord F x (han x hx).differentiableAt i
  have hderiv_ne : (fderiv ℝ (fun z : Fin (k + 1) → ℝ => F z i) x) (Pi.single j 1) ≠ 0 := by
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    exact hij
  -- the local analytic change of variables replacing coordinate `j` by `F · i`
  obtain ⟨Φ, Ψ, hΦan, hΨan, hΦeq, hΨΦ, hΦΨ⟩ :=
    exists_local_diffeomorph_update j hfan hderiv_ne
  let y : Fin (k + 1) → ℝ := Φ x
  have hΨx : Ψ y = x := hΨΦ.self_of_nhds
  -- transport `F` by the inverse chart
  let G : (Fin (k + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun w => F (Ψ w)
  have hGan : AnalyticAt ℝ G y := by
    have h1 : AnalyticAt ℝ F (Ψ y) := by rw [hΨx]; exact han x hx
    exact h1.comp hΨan
  have hGnorm : ∀ᶠ w in nhds y, G w i = w j := by
    have hΦeq' : {z : Fin (k + 1) → ℝ | Φ z = Function.update z j (F z i)} ∈ nhds (Ψ y) := by
      rw [hΨx]; exact hΦeq
    have h1 : ∀ᶠ w in nhds y, Φ (Ψ w) = w := hΦΨ
    have h2 : ∀ᶠ w in nhds y, Φ (Ψ w) = Function.update (Ψ w) j (F (Ψ w) i) :=
      hΨan.continuousAt.preimage_mem_nhds hΦeq'
    filter_upwards [h1, h2] with w hw1 hw2
    show F (Ψ w) i = w j
    have h3 : (Φ (Ψ w)) j = F (Ψ w) i := by rw [hw2, Function.update_self]
    rw [← h3, hw1]
  -- the hypothesis in target dimension `n`
  have H' : ∀ (d' : ℕ) (G : (Fin d' → ℝ) → (Fin n → ℝ)) (B : Set (Fin d' → ℝ)),
      Bornology.IsBounded B → (∀ z ∈ B, AnalyticAt ℝ G z) →
      MeasureTheory.volume (G '' (critSet G ∩ B)) = 0 := H
  obtain ⟨W, hWo, hyW, hWnull⟩ := null_of_normalForm_bdd hGan i j hGnorm H'
  -- a neighbourhood of `y` on which `G` is analytic and in normal form
  obtain ⟨Rx, hRxpos, hRx⟩ : ∃ R > 0, Metric.ball y R ⊆
      {w | AnalyticAt ℝ G w ∧ G w i = w j} :=
    Metric.mem_nhds_iff.mp (hGan.eventually_analyticAt.and hGnorm)
  have hgood : ∀ᶠ z in nhds x,
      Ψ (Φ z) = z ∧ Φ z ∈ W ∧ Φ z ∈ Metric.ball y Rx ∧ AnalyticAt ℝ F z ∧
        AnalyticAt ℝ Ψ (Φ z) := by
    have h1 : ∀ᶠ z in nhds x, Ψ (Φ z) = z := hΨΦ
    have h2 : Φ ⁻¹' (W ∩ Metric.ball y Rx) ∈ nhds x :=
      hΦan.continuousAt.preimage_mem_nhds
        ((hWo.inter Metric.isOpen_ball).mem_nhds ⟨hyW, Metric.mem_ball_self hRxpos⟩)
    have h3 : ∀ᶠ z in nhds x, AnalyticAt ℝ F z := (han x hx).eventually_analyticAt
    have h4 : ∀ᶠ z in nhds x, AnalyticAt ℝ Ψ (Φ z) :=
      hΦan.continuousAt.preimage_mem_nhds hΨan.eventually_analyticAt
    filter_upwards [h1, h2, h3, h4] with z h1 h2 h3 h4
    exact ⟨h1, h2.1, h2.2, h3, h4⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨δ, hδpos, ?_⟩
  refine measure_mono_null ?_ hWnull
  rintro y' ⟨z, ⟨hzA, hzball⟩, rfl⟩
  obtain ⟨hz1, hz2, hz3, hz4, hz5⟩ := hδ (Metric.mem_ball.mp hzball)
  have hFzG : G (Φ z) = F z := by
    show F (Ψ (Φ z)) = F z
    rw [hz1]
  refine ⟨Φ z, ⟨?_, hz2⟩, hFzG⟩
  -- criticality transfers across the chart
  rw [mem_critSet]
  intro hsurj
  have hzc : ¬ Function.Surjective (fderiv ℝ F z) := by
    have h := hcrit hzA
    rwa [mem_critSet] at h
  have hFdiff : DifferentiableAt ℝ F (Ψ (Φ z)) := by rw [hz1]; exact hz4.differentiableAt
  have hΨdiff : DifferentiableAt ℝ Ψ (Φ z) := hz5.differentiableAt
  have hchain : fderiv ℝ G (Φ z) = (fderiv ℝ F (Ψ (Φ z))).comp (fderiv ℝ Ψ (Φ z)) := by
    have h := fderiv_comp (𝕜 := ℝ) (x := Φ z) (f := Ψ) (g := F) hFdiff hΨdiff
    exact h
  rw [hchain] at hsurj
  rw [hz1] at hsurj
  have hsurjF : Function.Surjective (fderiv ℝ F z) := by
    intro v
    obtain ⟨u, hu⟩ := hsurj v
    exact ⟨(fderiv ℝ Ψ (Φ z)) u, by rw [← hu, ContinuousLinearMap.comp_apply]⟩
  exact hzc hsurjF

end Work.WilE9G.Sard
