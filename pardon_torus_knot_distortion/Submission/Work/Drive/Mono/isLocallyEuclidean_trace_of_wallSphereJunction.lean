import Mathlib
import Submission.Work.Drive.Mono.TightFaceModel
import Submission.Work.Drive.Mono.isLocallyArc_max_family_common_derivative
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_wallSphereJunction
import Submission.Work.Drive.Mono.hdir_of_htrans
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.CoreTopology.isClosed_carrier
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.BoxShrink.Pinch.Basic

/-!
# The local model of the trace of the tilted sweep at a wall ∩ box-sphere junction

At a point `z` of the surface which lies on the box sphere (`boxNorm c σ z = s`), strictly inside the
tilted slab and at the level (`ℓ z = lam`), with the level wall crossing the box sphere
*transversally* on the surface at `z`, the trace

`carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)`

of the tilted sweep is locally Euclidean of dimension one: near `z` it is the "V" made of the half
of the box-sphere trace on the side `ℓ ≥ lam` and the half of the wall trace inside the box.

The three ingredients are

* `Work.Drive.Mono.hdir_of_htrans` — the junction point `z` is approached by points of the open box
  on the far side of the wall (the transversality of the two derivatives at the parameter `p`);
* `Work.Drive.Mono.frontier_tiltedLevelRemoved_wallSphereJunction` — the frontier of the removed set
  near `z` is exactly `{boxNorm ≤ s} ∩ {ℓ ≥ lam} ∩ ({boxNorm = s} ∪ {ℓ = lam})`;
* `Work.Drive.Mono.isLocallyArc_max_family_common_derivative` — in the parameter plane, the zero set
  of `max (max over the tight faces i of (faceLin c σ i εᵢ (par ·) - s)) (lam - ℓ ∘ par)` is locally
  an arc, where the maximum over the tight faces is the box norm near `z`
  (`Work.Drive.Mono.eventually_boxNorm_eq_sup_tight`, `Work.Drive.Mono.fderiv_tightFace_sub_s_eq`).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped _root_.Topology

noncomputable section

theorem isLocallyEuclidean_trace_of_wallSphereJunction {ψ : Submission.Diffeo} {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ} {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hs : 0 < s) (hℓne : ℓ ≠ 0) (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzsphere : Submission.boxNorm c σ z = s)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| < h) (hzl : ℓ z = lam)
    (hreg : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0)
    (htrans : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  classical
  obtain ⟨p, hp, hD, htrans'⟩ := htrans
  -- 1. the direction property at the junction
  obtain ⟨δ₁, hδ₁pos, hdir₁⟩ := hdir_of_htrans (u := u) (v := v) (h := h)
    hs hℓne hzsphere hzl hp hD htrans'
  -- 2. the local description of the frontier
  obtain ⟨O₁, hO₁open, hzO₁, hchar⟩ :=
    frontier_tiltedLevelRemoved_wallSphereJunction hs hℓne hzsphere hzslab hzl ⟨δ₁, hδ₁pos, hdir₁⟩
  -- 3. the plane model from the tight faces and the wall
  haveI : Nonempty (TightFaceIdx c σ s z) := tightFaceIdx_nonempty hzsphere
  set Ψ : TightFaceIdx c σ s z → ℝ × ℝ → ℝ := fun i q =>
    Work.Smooth.BoxGeneric.faceLin c σ i.1 (tightEps c σ z i.1) (Work.BoxShrink.Pinch.par ψ q) - s
    with hΨdef
  set Gm : ℝ × ℝ → ℝ := fun q => lam - Work.Drive.EpsForm.sweepHeight ψ ℓ q with hGdef
  have hΨcd : ∀ i, ContDiff ℝ 1 (Ψ i) := by
    intro i
    rw [hΨdef]
    exact ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i.1 (tightEps c σ z i.1)).sub
      contDiff_const).of_le (by simp : (1 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞))
  have hΨp : ∀ i, Ψ i p = 0 := by
    intro i
    rw [hΨdef]
    change Work.Smooth.BoxGeneric.faceLin c σ i.1 (tightEps c σ z i.1)
      (Work.BoxShrink.Pinch.par ψ p) - s = 0
    rw [hp]
    exact sub_eq_zero.mpr (faceLin_tightEps_tight_eq i.2)
  have hΨd : ∀ i, fderiv ℝ (Ψ i) p =
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
    intro i
    rw [hΨdef]
    exact fderiv_tightFace_sub_s_eq hs hzsphere i.2 hp hD
  have hGcd : ContDiff ℝ 1 Gm := by
    rw [hGdef]
    have h1 : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (Work.Drive.EpsForm.sweepHeight ψ ℓ) :=
      (ContinuousLinearMap.contDiff ℓ).comp (Work.Smooth.Morse.param_contDiff ψ)
    exact (contDiff_const.sub h1).of_le (by simp : (1 : WithTop ℕ∞) ≤ (((⊤ : ℕ∞)) : WithTop ℕ∞))
  have hGp : Gm p = 0 := by
    rw [hGdef]
    change lam - Work.Drive.EpsForm.sweepHeight ψ ℓ p = 0
    rw [show Work.Drive.EpsForm.sweepHeight ψ ℓ p = ℓ (Work.BoxShrink.Pinch.par ψ p) from rfl,
      hp, hzl, sub_self]
  have hGind : ∀ t : ℝ, fderiv ℝ Gm p ≠
      t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
    intro t ht
    have hfd : fderiv ℝ Gm p = -fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p := by
      rw [hGdef]
      exact fderiv_const_sub lam
    have h4 : -fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
      rw [← hfd]
      exact ht
    have h5 : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
        (-t) • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p :=
      (neg_eq_iff_eq_neg.mp h4).trans (neg_smul t _).symm
    exact htrans' (-t) h5
  obtain ⟨V, hVopen, hpV, hVloc⟩ :=
    isLocallyArc_max_family_common_derivative hΨcd hGcd hΨp hGp hΨd hD hGind
  -- 4. the neighbourhood of `p` on which the model is the trace
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp (eventually_boxNorm_eq_sup_tight hs hzsphere)
  have hcont : Continuous (Work.BoxShrink.Pinch.par ψ) := Work.BoxShrink.Pinch.par_continuous ψ
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hpV)
  obtain ⟨δ₄, hδ₄pos, hδ₄inj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  have hnhds₂ : {q : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ q ∈ Metric.ball z δ₂} ∈ 𝓝 p :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by rw [hp]; exact Metric.mem_ball_self hδ₂pos))
  obtain ⟨δ₅, hδ₅pos, hδ₅⟩ := Metric.mem_nhds_iff.mp hnhds₂
  have hnhds₁ : {q : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ q ∈ O₁} ∈ 𝓝 p :=
    hcont.continuousAt (hO₁open.mem_nhds (by rw [hp]; exact hzO₁))
  obtain ⟨δ₆, hδ₆pos, hδ₆⟩ := Metric.mem_nhds_iff.mp hnhds₁
  set δ : ℝ := min (min δ₃ δ₄) (min δ₅ δ₆) with hδdef
  have hδpos : 0 < δ :=
    lt_min (lt_min hδ₃pos hδ₄pos) (lt_min hδ₅pos hδ₆pos)
  have hδ₃' : δ ≤ δ₃ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₄' : δ ≤ δ₄ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₅' : δ ≤ δ₅ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₆' : δ ≤ δ₆ := le_trans (min_le_right _ _) (min_le_right _ _)
  set B : Set (ℝ × ℝ) := Metric.ball p δ with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hpB : p ∈ B := by rw [hBdef]; exact Metric.mem_ball_self hδpos
  have hBV : B ⊆ V := fun q hq => hδ₃ (Metric.ball_subset_ball hδ₃' hq)
  have hBinj : Set.InjOn (Work.BoxShrink.Pinch.par ψ) B := fun a ha b hb hab =>
    hδ₄inj (Metric.ball_subset_ball hδ₄' ha) (Metric.ball_subset_ball hδ₄' hb) hab
  have hBbox : ∀ q ∈ B, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) =
      tightSup c σ s z hzsphere (Work.BoxShrink.Pinch.par ψ q) :=
    fun q hq => hδ₂ (hδ₅ (Metric.ball_subset_ball hδ₅' hq))
  have hBO₁ : ∀ q ∈ B, Work.BoxShrink.Pinch.par ψ q ∈ O₁ :=
    fun q hq => hδ₆ (Metric.ball_subset_ball hδ₆' hq)
  -- the model set
  set M : Set (ℝ × ℝ) := {q : ℝ × ℝ |
    max (Finset.sup' Finset.univ Finset.univ_nonempty (fun i => Ψ i q)) (Gm q) = 0} with hMdef
  have hsup_eq : ∀ q : ℝ × ℝ, (Finset.univ : Finset (TightFaceIdx c σ s z)).sup'
        (tightIdx_nonempty hzsphere) (fun i => Ψ i q) =
      tightSup c σ s z hzsphere (Work.BoxShrink.Pinch.par ψ q) - s := by
    intro q
    have h1 : (Finset.univ : Finset (TightFaceIdx c σ s z)).sup' (tightIdx_nonempty hzsphere)
        (fun i => Ψ i q) =
        (Finset.univ : Finset (TightFaceIdx c σ s z)).sup' (tightIdx_nonempty hzsphere)
          (fun i => Work.Smooth.BoxGeneric.faceLin c σ i.1 (tightEps c σ z i.1)
            (Work.BoxShrink.Pinch.par ψ q) - s) := by
      refine Finset.sup'_congr (tightIdx_nonempty hzsphere) rfl ?_
      intro i _
      rw [hΨdef]
    rw [h1, finset_sup_sub_eq, tightSup]
  -- the pointwise identification of the trace with the model
  have hpoint : ∀ q ∈ B, (Work.BoxShrink.Pinch.par ψ q ∈
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔ q ∈ M) := by
    intro q hq
    rw [hchar _ (hBO₁ q hq)]
    have hbox := hBbox q hq
    have hsupq : (Finset.univ : Finset (TightFaceIdx c σ s z)).sup'
          Finset.univ_nonempty (fun i => Ψ i q) =
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) - s := by
      rw [finset_sup'_proof_irrel Finset.univ_nonempty (tightIdx_nonempty hzsphere) _,
        hsup_eq q, hbox]
    have hGq : Gm q = lam - ℓ (Work.BoxShrink.Pinch.par ψ q) := by
      rw [hGdef]
      change lam - Work.Drive.EpsForm.sweepHeight ψ ℓ q = lam - ℓ (Work.BoxShrink.Pinch.par ψ q)
      rw [show Work.Drive.EpsForm.sweepHeight ψ ℓ q = ℓ (Work.BoxShrink.Pinch.par ψ q) from rfl]
    rw [hMdef]
    simp only [Set.mem_setOf_eq]
    rw [Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff, hsupq, hGq]
    constructor
    · rintro ⟨hb, hl, hdisj⟩
      refine ⟨by linarith, by linarith, ?_⟩
      rcases hdisj with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by linarith, by linarith, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  -- 5. transport to the surface
  have hZc : ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) ⊆
      (Work.Smooth.Morse.torus ψ).carrier := Set.inter_subset_left
  have hPB : B ∩ M ⊆ B := Set.inter_subset_left
  have hloc : Work.Smooth.OneManifold.IsLocallyArcP (B ∩ (B ∩ M)) := by
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc ↥(V ∩ M) := hVloc
    have h2 : Work.Smooth.SphereJordan.IsLocallyArc ↥((V ∩ M) ∩ B) :=
      Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen h1 hBopen
    have h3 : (V ∩ M) ∩ B = B ∩ (B ∩ M) := by
      ext q
      constructor
      · rintro ⟨⟨hqV, hqM⟩, hqB⟩
        exact ⟨hqB, hqB, hqM⟩
      · rintro ⟨hqB, -, hqM⟩
        exact ⟨⟨hBV hqB, hqM⟩, hqB⟩
    exact h3 ▸ h2
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.BoxShrink.Pinch.par ψ '' (B' ∩ (B ∩ M)) =
        Work.BoxShrink.Pinch.par ψ '' B' ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
    intro B' _ hB'sub
    ext y
    constructor
    · rintro ⟨q, ⟨hqB', hqBM⟩, rfl⟩
      exact ⟨⟨q, hqB', rfl⟩, Work.BoxShrink.Pinch.par_mem_carrier ψ q,
        (hpoint q (hB'sub hqB')).mpr hqBM.2⟩
    · rintro ⟨⟨q, hqB', rfl⟩, hy⟩
      exact ⟨q, ⟨hqB', hB'sub hqB', (hpoint q (hB'sub hqB')).mp hy.2⟩, rfl⟩
  have hlocE : Work.Smooth.OneManifold.IsLocallyEuclidean
      (Work.BoxShrink.Pinch.par ψ '' B ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param hZc hBopen hPB hident hBinj hloc
  -- 6. the ambient open set
  obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp
    (Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen)
  have hWeq' : Subtype.val ⁻¹' W =
      Subtype.val ⁻¹' (Work.BoxShrink.Pinch.par ψ '' B : Set R3) := hWeq
  have hWcar : (Work.Smooth.Morse.torus ψ).carrier ∩ W = Work.BoxShrink.Pinch.par ψ '' B := by
    ext x
    constructor
    · rintro ⟨hxc, hxW⟩
      have h1 : (⟨x, hxc⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
          Subtype.val ⁻¹' (Work.BoxShrink.Pinch.par ψ '' B) := by
        rw [← hWeq']
        exact hxW
      exact h1
    · rintro ⟨q, hq, rfl⟩
      refine ⟨Work.BoxShrink.Pinch.par_mem_carrier ψ q, ?_⟩
      have h2 : (⟨Work.BoxShrink.Pinch.par ψ q,
          Work.BoxShrink.Pinch.par_mem_carrier ψ q⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
          Subtype.val ⁻¹' W := by
        rw [hWeq']
        exact ⟨q, hq, rfl⟩
      exact h2
  refine ⟨W ∩ O₁, hWopen.inter hO₁open, ⟨?_, hzO₁⟩, ?_⟩
  · have h1 : z ∈ (Work.Smooth.Morse.torus ψ).carrier ∩ W := by
      rw [hWcar]
      exact ⟨p, hpB, hp⟩
    exact h1.2
  · have hset : (W ∩ O₁) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) =
        (Work.BoxShrink.Pinch.par ψ '' B ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) ∩ O₁ := by
      ext x
      constructor
      · rintro ⟨⟨hxW, hxO₁⟩, hxZ⟩
        have h2 : x ∈ Work.BoxShrink.Pinch.par ψ '' B := by
          rw [← hWcar]
          exact ⟨hxZ.1, hxW⟩
        exact ⟨⟨h2, hxZ⟩, hxO₁⟩
      · rintro ⟨⟨hxWB, hxZ⟩, hxO₁⟩
        have hxW : x ∈ W := by
          have h1 : x ∈ (Work.Smooth.Morse.torus ψ).carrier ∩ W := by
            rw [hWcar]
            exact hxWB
          exact h1.2
        exact ⟨⟨hxW, hxO₁⟩, hxZ⟩
    rw [hset]
    refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn Set.inter_subset_left ?_ hlocE
    rw [Work.Smooth.OneManifold.IsOpenInSet]
    have hpre : Subtype.val ⁻¹' ((Work.BoxShrink.Pinch.par ψ '' B ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) ∩ O₁) =
        {x : ↥(Work.BoxShrink.Pinch.par ψ '' B ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) | (x : R3) ∈ O₁} := by
      ext x
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨x.2, h⟩
    rw [hpre]
    exact hO₁open.preimage continuous_subtype_val

end

end Work.Drive.Mono
