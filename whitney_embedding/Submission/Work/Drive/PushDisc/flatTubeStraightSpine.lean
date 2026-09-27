import Mathlib
import Submission.Work.Drive.Push.flattenAlignedSpine
import Submission.Work.Drive.Push.spineAlignment
import Submission.Work.Drive.PushDisc.sheetOneTubeFlattening

/-!
# The flat tube of the first sheet, with the arc's image straightened

`Work.Drive.PushDisc.flatTubeStraightSpine` strengthens
`Work.Drive.PushDisc.sheetOneTubeFlattening` by the arc row
`A (f (γ₁ t)) = A (f p₁) + t • (A (f q₁) - A (f p₁))`.

The route is the one of `sheetOneTubeFlattening`, with the flattening step strengthened:

* `Work.Whitney.CutPush.exists_tube_injOn` produces the tube `U₀`;
* `Work.Drive.Push.spineAlignment` straightens the arc (`A₂ (A₁ (f (γ₁ t))) = a + t • e`) and
  aligns the tangent planes to the fixed `n`-plane `K`;
* `Work.Drive.Push.flattenAlignedSpine`, copied here as `flattenAlignedSpineStraight` with the extra
  conjunct `A (F (δ t)) = K.starProjection a + t • e`, flattens the aligned sheet onto `K`.

The arc row of the target then follows from
`A (f (γ₁ t)) = A₃ (F (γ₁ t)) = K.starProjection a + t • e = A (f p₁) + t • (A (f q₁) - A (f p₁))`,
using `A (f p₁) = K.starProjection a` and `A (f q₁) = K.starProjection a + e`.
-/

set_option maxHeartbeats 4000000

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

namespace Work.Drive.Push

/-- **Flattening an aligned spine, with the spine's image straightened.**  Same statement as
`Work.Drive.Push.flattenAlignedSpine`, with the additional conclusion that the diffeomorphism `A`
carries the spine `δ` exactly onto the straight segment from `K.starProjection a` to
`K.starProjection a + e`. -/

theorem flattenAlignedSpineStraight {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFimm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y))
    (δ : ℝ → M)
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
    (hK : Module.finrank ℝ K = n)
    (a e : EuclideanSpace ℝ (Fin (2 * n))) (he : e ≠ 0)
    (haff : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → F (δ t) = a + t • e)
    (hrange : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)).toLinearMap = K) :
    ∃ (U : Set M) (A Ain : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen U ∧ δ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ain ∧
      Function.LeftInverse Ain A ∧ Function.RightInverse Ain A ∧
      (∀ x : M, x ∈ U → A (F x) ∈ K) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → A (F (δ t)) = K.starProjection a + t • e) := by
  classical
  -- 1. the direction of the spine lies in `K`
  have hmemK : e ∈ K := spine_direction_mem F hF δ hδ K a e haff hrange
  -- 2. the projection onto `K`, the identification `K ≅ ℝⁿ`, and the base coordinate `ψ`
  have hfinB : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  set eiso : ↥K ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofFinrankEq ↥K (EuclideanSpace ℝ (Fin n)) (by rw [hK, hfinB])).toContinuousLinearEquiv
    with heiso
  set b : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (eiso : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n)).comp K.orthogonalProjectionOnto with hb
  set ψ : M → EuclideanSpace ℝ (Fin n) := fun x => b (F x) with hψdef
  have hb_apply : ∀ y : EuclideanSpace ℝ (Fin (2 * n)),
      b y = (eiso : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n)) (K.orthogonalProjectionOnto y) := by
    intro y
    simp only [hb, ContinuousLinearMap.comp_apply]
  have hψsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    rw [hψdef]
    exact b.contMDiff.comp hF
  have hψcont : Continuous ψ := hψsm.continuous
  -- 3. `mfderiv ψ` is injective at every point of the spine
  have hψinj_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ψ (δ t)) := by
    intro t ht
    have hmdF : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t) :=
      hF.mdifferentiableAt (by simp)
    have hbmd : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) => b y) (F (δ t)) :=
      (b.contMDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).mdifferentiableAt (by simp)
    have hmfderiv_b : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) => b y) (F (δ t)) = b := by
      rw [mfderiv_eq_fderiv]
      exact b.hasFDerivAt.fderiv
    have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ψ (δ t)
        = b.comp (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)) := by
      have h := mfderiv_comp (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (I'' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (f := F) (g := fun y => b y) (δ t) hbmd hmdF
      rw [hmfderiv_b] at h
      rw [hψdef]
      exact h
    have hker : ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (δ t),
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ψ (δ t)) v = 0 → v = 0 := by
      intro v hv
      let w : EuclideanSpace ℝ (Fin (2 * n)) :=
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t) v
      have hz0 : (b.comp (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t))) v = 0 := by
        rw [← hcomp]
        exact hv
      have hz : b w = 0 := hz0
      have h2 : (eiso : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n)) (K.orthogonalProjectionOnto w) = 0 := by
        rw [← hb_apply]
        exact hz
      have h3 : K.orthogonalProjectionOnto w = 0 :=
        eiso.injective (h2.trans (map_zero eiso).symm)
      have h4 : w ∈ Kᗮ := (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := K)).mp h3
      have h5 : w ∈ K := by
        have hmem : ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)).toLinearMap) v ∈ K := by
          have hmem0 := LinearMap.mem_range_self
            ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)).toLinearMap) v
          rwa [hrange t ht] at hmem0
        exact hmem
      have h6 : w = 0 := by
        have hm : w ∈ K ⊓ Kᗮ := Submodule.mem_inf.mpr ⟨h5, h4⟩
        rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
        exact hm
      exact hFimm (δ t) (h6.trans (map_zero _).symm)
    intro a b hab
    exact sub_eq_zero.mp (hker (a - b) (by rw [map_sub, hab, sub_self]))

  -- 4. local sections of `ψ` at the points of the spine
  have hsec : ∀ t : ↥(Set.Icc (0 : ℝ) 1),
      ∃ (S : Set (EuclideanSpace ℝ (Fin n))) (U : Set M) (σ : EuclideanSpace ℝ (Fin n) → M),
        IsOpen S ∧ ψ (δ (t : ℝ)) ∈ S ∧ IsOpen U ∧ δ (t : ℝ) ∈ U ∧
        (∀ u ∈ S, ψ (σ u) = u) ∧ (∀ x ∈ U, σ (ψ x) = x) ∧
        ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ S := by
    intro t
    exact exists_localSection_of_mfderiv_injective ψ hψsm (δ (t : ℝ)) (hψinj_deriv (t : ℝ) t.2)
  choose S U σ hSopen hSmem hUopen hUmem hright hleft hσsm using hsec
  -- 5. `ψ` is injective on an open tube around the spine
  have hloc : ∀ x ∈ δ '' Set.Icc (0 : ℝ) 1, ∃ V ∈ 𝓝 x, Set.InjOn ψ V := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨U ⟨t, ht⟩, (hUopen ⟨t, ht⟩).mem_nhds (hUmem ⟨t, ht⟩), ?_⟩
    intro a ha b hb hab
    rw [← hleft ⟨t, ht⟩ a ha, ← hleft ⟨t, ht⟩ b hb, hab]
  have hKcpt : IsCompact (δ '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hδ.continuous
  have hbene : b e ≠ 0 := by
    intro h0
    have h0' : (eiso : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n)) (K.orthogonalProjectionOnto e) = 0 := by
      rw [← hb_apply]
      exact h0
    have h1 : K.orthogonalProjectionOnto e = 0 :=
      eiso.injective (h0'.trans (map_zero eiso).symm)
    have h2 : e ∈ Kᗮ := (Submodule.orthogonalProjectionOnto_eq_zero_iff (K := K)).mp h1
    have h3 : e = 0 := by
      have hm : e ∈ K ⊓ Kᗮ := Submodule.mem_inf.mpr ⟨hmemK, h2⟩
      rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
      exact hm
    exact he h3
  have hKinj : Set.InjOn ψ (δ '' Set.Icc (0 : ℝ) 1) := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩ hts
    have h1 : ψ (δ t) = b a + t • b e := by
      show b (F (δ t)) = b a + t • b e
      rw [haff t ht, map_add, map_smul]
    have h2 : ψ (δ s) = b a + s • b e := by
      show b (F (δ s)) = b a + s • b e
      rw [haff s hs, map_add, map_smul]
    rw [h1, h2] at hts
    have h3 : (t - s) • b e = 0 := by
      rw [sub_smul, add_left_cancel hts, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rw [show t = s by linarith]
    · exact absurd h hbene
  letI : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  obtain ⟨U₁, hU₁open, hKU₁, hU₁inj⟩ :=
    Work.Whitney.CutPush.exists_isOpen_injOn_of_compact_injOn hKcpt hψcont hKinj hloc
  -- 6. shrinking the local data to closed balls
  have hshrink : ∀ t : ↥(Set.Icc (0 : ℝ) 1), ∃ d : ℝ, 0 < d ∧
      Metric.closedBall (ψ (δ (t : ℝ))) d ⊆ S t ∧
      (∀ u ∈ Metric.ball (ψ (δ (t : ℝ))) d, σ t u ∈ U t ∩ U₁) := by
    intro t
    obtain ⟨r₁, hr₁, hr₁sub⟩ := (Metric.isOpen_iff.mp (hSopen t)) (ψ (δ (t : ℝ))) (hSmem t)
    have hcontσ : ContinuousAt (σ t) (ψ (δ (t : ℝ))) :=
      (hσsm t).continuousOn.continuousAt ((hSopen t).mem_nhds (hSmem t))
    have hmemU : σ t (ψ (δ (t : ℝ))) ∈ U t ∩ U₁ := by
      have h1 : σ t (ψ (δ (t : ℝ))) = δ (t : ℝ) := hleft t (δ (t : ℝ)) (hUmem t)
      rw [h1]
      exact ⟨hUmem t, hKU₁ (mem_image_of_mem δ t.2)⟩
    have hpre : (σ t) ⁻¹' (U t ∩ U₁) ∈ 𝓝 (ψ (δ (t : ℝ))) :=
      hcontσ.preimage_mem_nhds ((hUopen t).inter hU₁open |>.mem_nhds hmemU)
    obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨min r₁ r₂ / 2, by have := lt_min hr₁ hr₂; linarith, ?_, ?_⟩
    · exact (Metric.closedBall_subset_ball (by linarith [min_le_left r₁ r₂])).trans hr₁sub
    · intro u hu
      exact hr₂sub (Metric.ball_subset_ball (by linarith [min_le_right r₁ r₂, hr₂]) hu)
  choose d hdpos hdS hdU using hshrink
  -- 7. a finite subcover and the thickening on which the partition of unity is equal to one
  have hcover : ψ '' (δ '' Set.Icc (0 : ℝ) 1) ⊆
      ⋃ t : ↥(Set.Icc (0 : ℝ) 1), Metric.ball (ψ (δ (t : ℝ))) (d t) := by
    rintro y ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Metric.mem_ball_self (hdpos ⟨t, ht⟩)⟩
  obtain ⟨s₀, hs₀⟩ := (hKcpt.image hψcont).elim_finite_subcover
    (fun t : ↥(Set.Icc (0 : ℝ) 1) => Metric.ball (ψ (δ (t : ℝ))) (d t))
    (fun t => Metric.isOpen_ball) hcover
  set Ω : Set (EuclideanSpace ℝ (Fin n)) :=
    ⋃ t ∈ s₀, Metric.ball (ψ (δ (t : ℝ))) (d t) with hΩdef
  have hΩopen : IsOpen Ω := isOpen_biUnion (fun t _ => Metric.isOpen_ball)
  have hKΩ : ψ '' (δ '' Set.Icc (0 : ℝ) 1) ⊆ Ω := by
    intro y hy
    obtain ⟨t, hts, hty⟩ := Set.mem_iUnion₂.mp (hs₀ hy)
    exact Set.mem_iUnion₂.mpr ⟨t, hts, hty⟩
  obtain ⟨r, hr, hrsub⟩ :=
    (hKcpt.image hψcont).exists_cthickening_subset_open hΩopen hKΩ
  set K' : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.cthickening r (ψ '' (δ '' Set.Icc (0 : ℝ) 1)) with hK'def
  have hK'closed : IsClosed K' := Metric.isClosed_cthickening
  have hK'cover : K' ⊆ ⋃ i : ↥s₀, Metric.ball (ψ (δ (i.1 : ℝ))) (d i.1) := by
    intro y hy
    have hyΩ : y ∈ Ω := hrsub hy
    obtain ⟨t, hts, hty⟩ := Set.mem_iUnion₂.mp hyΩ
    exact Set.mem_iUnion.mpr ⟨⟨t, hts⟩, hty⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) hK'closed
    (fun i : ↥s₀ => Metric.ball (ψ (δ (i.1 : ℝ))) (d i.1))
    (fun i => Metric.isOpen_ball) hK'cover

  -- 8. the correction function
  have hρS : ρ.IsSubordinate (fun i : ↥s₀ => S i.1) :=
    fun i => (hρ i).trans (Metric.ball_subset_closedBall.trans (hdS i.1))
  let c : ↥s₀ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun i u => Kᗮ.starProjection
      (F (σ i.1 u) - ((eiso.symm u : ↥K) : EuclideanSpace ℝ (Fin (2 * n))))
  have hc : ∀ i : ↥s₀, ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (c i) (S i.1) := by
    intro i
    have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => F (σ i.1 u)) (S i.1) :=
      ContMDiffOn.comp (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (I'' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (M' := M)
        (f := σ i.1) (g := F) (t := Set.univ)
        (hF.contMDiffOn (s := Set.univ)) (hσsm i.1) (fun _ _ => trivial)
    have h2 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => ((eiso.symm u : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))) (S i.1) :=
      (((K.subtypeL.comp (eiso.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] ↥K)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).contMDiff).contMDiffOn
    exact ((Kᗮ.starProjection : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).contMDiff.comp_contMDiffOn (h1.sub h2))
  let htilde : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun u => ∑ i : ↥s₀, ρ i u • c i u
  have htilde_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) htilde := by
    have hterm : ∀ i : ↥s₀, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => ρ i u • c i u) := by
      intro i
      exact contDiff_smul_of_contDiffOn' (hc i).contDiffOn (hSopen i.1)
        (contMDiff_iff_contDiff.mp (ρ i).contMDiff) (hρS i)
    simpa [htilde] using ContDiff.sum (f := fun i u => ρ i u • c i u) (s := Finset.univ)
      (fun i _ => hterm i)
  have htilde_mem : ∀ u : EuclideanSpace ℝ (Fin n), htilde u ∈ Kᗮ := by
    intro u
    have hsum : (∑ i : ↥s₀, ρ i u • c i u) ∈ Kᗮ := by
      refine Submodule.sum_mem _ (fun i _ => ?_)
      refine Submodule.smul_mem _ _ ?_
      show Kᗮ.starProjection (F (σ i.1 u) - ((eiso.symm u : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))) ∈ Kᗮ
      rw [Submodule.starProjection_apply]
      exact Subtype.coe_prop _
    simpa [htilde] using hsum
  -- 9. the shear
  have hbsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    rw [hb]
    exact (((eiso : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n)).comp K.orthogonalProjectionOnto)).contDiff
  let g : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) := fun y => htilde (b y)
  have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    have h' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => htilde (b y)) :=
      htilde_sm.comp hbsm
    simpa [g] using h'
  have hgmem : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), g y ∈ Kᗮ := fun y => htilde_mem (b y)
  obtain ⟨Φ, Φinv, hΦsm, hΦinvsm, hΦleft, hΦright, hΦform, hΦinvform⟩ :=
    Work.Whitney.CutPush.exists_global_diffeo_of_base_shear K g hgsm hgmem
  have hb_star : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), b (K.starProjection y) = b y := by
    intro y
    have h1 : K.starProjection y
        = ((K.orthogonalProjectionOnto y : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) :=
      (Submodule.starProjection_apply K y).symm
    rw [h1, hb_apply, hb_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  -- 10. the tube and the conclusion
  set Uset : Set M := U₁ ∩ ψ ⁻¹' Metric.thickening r (ψ '' (δ '' Set.Icc (0 : ℝ) 1)) with hUset
  have hthickopen : IsOpen (Metric.thickening r (ψ '' (δ '' Set.Icc (0 : ℝ) 1))) :=
    Metric.isOpen_thickening
  have hUsetopen : IsOpen Uset := by
    rw [hUset]
    exact hU₁open.inter (hthickopen.preimage hψcont)
  have hUseg : δ '' Set.Icc (0 : ℝ) 1 ⊆ Uset := by
    intro x hx
    exact ⟨hKU₁ hx, Metric.self_subset_thickening hr _ (mem_image_of_mem ψ hx)⟩
  have hΦeq : ∀ x : M, x ∈ Uset →
      Φ (F x) = ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) := by
    intro x hx
    obtain ⟨hxU₁, hxth⟩ := hx
    have hxK' : ψ x ∈ K' := Metric.thickening_subset_cthickening r _ hxth
    have hΦx : Φ (F x) = F x - htilde (ψ x) := by
      rw [hΦform]
      congr 1
      show htilde (b (K.starProjection (F x))) = htilde (ψ x)
      rw [hb_star]
    have hht : htilde (ψ x)
        = F x - ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) := by
      have hv : ∀ i : ↥s₀, ρ i (ψ x) • c i (ψ x)
          = ρ i (ψ x) • (F x - ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))) := by
        intro i
        by_cases h0 : ρ i (ψ x) = 0
        · rw [h0, zero_smul, zero_smul]
        · have hsupp : ψ x ∈ tsupport (ρ i) := subset_tsupport _ (Function.mem_support.mpr h0)
          have hball : ψ x ∈ Metric.ball (ψ (δ (i.1 : ℝ))) (d i.1) := hρ i hsupp
          have hσU : σ i.1 (ψ x) ∈ U i.1 ∩ U₁ := hdU i.1 (ψ x) hball
          have hS : ψ x ∈ S i.1 := hdS i.1 (Metric.ball_subset_closedBall hball)
          have hσeq : σ i.1 (ψ x) = x :=
            hU₁inj hσU.2 hxU₁ (hright i.1 (ψ x) hS)
          have hmem : K.orthogonalProjectionOnto (F (σ i.1 (ψ x))) = eiso.symm (ψ x) := by
            have h1 : (eiso : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n))
                (K.orthogonalProjectionOnto (F (σ i.1 (ψ x)))) = ψ x := by
              rw [← hb_apply]
              exact hright i.1 (ψ x) hS
            calc K.orthogonalProjectionOnto (F (σ i.1 (ψ x)))
                = eiso.symm ((eiso : ↥K →L[ℝ] EuclideanSpace ℝ (Fin n))
                    (K.orthogonalProjectionOnto (F (σ i.1 (ψ x))))) :=
                  (ContinuousLinearEquiv.symm_apply_apply eiso
                    (K.orthogonalProjectionOnto (F (σ i.1 (ψ x))))).symm
              _ = eiso.symm (ψ x) := by rw [h1]
          have hperp : F x - ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) ∈ Kᗮ := by
            have h2 : eiso.symm (ψ x) = K.orthogonalProjectionOnto (F x) := by
              rw [← hmem, hσeq]
            rw [h2, ← Submodule.starProjection_apply]
            exact Submodule.sub_starProjection_mem_orthogonal (K := K) (F x)
          have hcval : c i (ψ x)
              = F x - ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) := by
            show Kᗮ.starProjection (F (σ i.1 (ψ x))
              - ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))) = _
            rw [hσeq]
            exact Submodule.starProjection_eq_self_iff.mpr hperp
          rw [hcval]
      have hsum1 : (∑ i : ↥s₀, ρ i (ψ x)) = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact ρ.sum_eq_one hxK'
      show (∑ i : ↥s₀, ρ i (ψ x) • c i (ψ x))
        = F x - ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n)))
      rw [Finset.sum_congr rfl (fun i _ => hv i), ← Finset.sum_smul, hsum1, one_smul]
    rw [hΦx, hht]
    rw [show F x - (F x - ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n))))
        = ((eiso.symm (ψ x) : ↥K) : EuclideanSpace ℝ (Fin (2 * n))) from by abel]
  refine ⟨Uset, Φ, Φinv, hUsetopen, hUseg, hΦsm, hΦinvsm, hΦleft, hΦright, ?_, ?_⟩
  · intro x hx
    rw [hΦeq x hx]
    exact Subtype.coe_prop _
  · intro t ht
    rw [hΦeq (δ t) (hUseg (mem_image_of_mem δ ht))]
    have hba_eq : (eiso.symm (ψ (δ t)) : EuclideanSpace ℝ (Fin (2 * n)))
        = K.starProjection (F (δ t)) := by
      have h1 : eiso.symm (ψ (δ t)) = K.orthogonalProjectionOnto (F (δ t)) := by
        show eiso.symm (b (F (δ t))) = K.orthogonalProjectionOnto (F (δ t))
        rw [hb_apply]
        exact ContinuousLinearEquiv.symm_apply_apply eiso (K.orthogonalProjectionOnto (F (δ t)))
      rw [h1]
      exact (Submodule.starProjection_apply K (F (δ t))).symm
    rw [hba_eq, haff t ht, map_add, map_smul,
      Submodule.starProjection_eq_self_iff.mpr hmemK]

end Work.Drive.Push

namespace Work.Drive.PushDisc

set_option maxHeartbeats 1000000

/-- Flat tube of the first sheet with the arc's image straightened.

This is `Work.Drive.PushDisc.sheetOneTubeFlattening` with the arc row
`A (f (γ₁ t)) = A (f p₁) + t • (A (f q₁) - A (f p₁))` exposed.

ROUTE. Reproduce the proof of `Work.Drive.PushDisc.sheetOneTubeFlattening`
(`Work.Whitney.CutPush.exists_tube_injOn` -> `Work.Drive.Push.spineAlignment` -> flattening), but copy
`Submission/Work/Drive/Push/flattenAlignedSpine.lean` into your own file and strengthen the conclusion
of its main result by the conjunct `∀ t ∈ Set.Icc 0 1, A (F (δ t)) = K.starProjection a + t • e`
(the proof already establishes it: there `Φ (F x) = eiso.symm (ψ x)` on the tube, and
`ψ (δ t) = b a + t • b e`).  Then put `A := A₃ ∘ A₂ ∘ A₁`; the arc row follows from
`A₂ (A₁ (f (γ₁ t))) = a + t • e` (from `spineAlignment`),
`A₃ (a + t • e) = K.starProjection a + t • e` (the strengthened part), and
`A (f p₁) = K.starProjection a`, `A (f q₁) = K.starProjection a + e`.  Intersect the flattening tube
with the `exists_tube_injOn` tube `U₀` to get `closure U ⊆ W` and `p₂, q₂ ∉ U`. -/
theorem flatTubeStraightSpine {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M) (hW₁ : p₁ ∈ W) (hW₃ : q₁ ∈ W) (hp₁p₂ : p₁ ≠ p₂)
    (hfp : f p₁ = f p₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (γ₁ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hp₂arc : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) (hq₂arc : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
      (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (U : Set M),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      Module.finrank ℝ K = n ∧ IsOpen U ∧ closure U ⊆ W ∧ γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U ∧
      p₂ ∉ U ∧ q₂ ∉ U ∧ (∀ x : M, x ∈ U → A (f x) ∈ K) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        A (f (γ₁ t)) = A (f p₁) + t • (A (f q₁) - A (f p₁))) := by
  classical
  -- ## `p₂` and `q₂` are the points to be removed: interchange the roles of the two double points
  have hclean' : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₂ ∧ z = p₁) ∨ (y = p₁ ∧ z = p₂) ∨ (y = q₂ ∧ z = q₁) ∨
        (y = q₁ ∧ z = q₂) := by
    intro y z hy hz hyz
    rcases hclean y z hy hz hyz with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  -- ## the tube around the arc: open, inside `W` (even its closure), avoiding `p₂`, `q₂`,
  --     with `f` injective on it
  obtain ⟨U₀, hU₀o, hU₀arc, hU₀cl, hp₂U₀, hq₂U₀, hU₀inj⟩ :=
    Work.Whitney.CutPush.exists_tube_injOn hclean' hWopen γ₁ hγ₁
      (fun t ht => hγW₁ t ht) hp₂arc hq₂arc
  -- ## first half: straighten the arc and align the tangent planes of `f` along it
  obtain ⟨A₁, A₁i, A₂, A₂i, K, a, e, hA₁, hA₁i, hA₁l, hA₁r, hA₂, hA₂i, hA₂l, hA₂r,
    he, hKfin, haff, hrange⟩ :=
    Work.Drive.Push.spineAlignment hn f hf himm γ₁ hγ₁smooth hγ₁imm hγ₁inj U₀ hU₀o hU₀arc hU₀inj
  -- ## second half: flatten the aligned sheet onto the plane `K`, keeping the arc straight
  set F : M → EuclideanSpace ℝ (Fin (2 * n)) := fun y => A₂ (A₁ (f y)) with hFdef
  have hFsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    hA₂.contMDiff.comp (hA₁.contMDiff.comp hf)
  have hA₁fsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => A₁ (f y)) := hA₁.contMDiff.comp hf
  have hA₁fimm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) (fun y : M => A₁ (f y)) y) :=
    Work.Whitney.CutPush.mfderiv_comp_injective f hf himm A₁ A₁i hA₁ hA₁i hA₁l
  have hFimm : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y) := by
    intro y
    exact Work.Whitney.CutPush.mfderiv_comp_injective (fun z : M => A₁ (f z)) hA₁fsm hA₁fimm
      A₂ A₂i hA₂ hA₂i hA₂l y
  obtain ⟨U₁, A₃, A₃i, hU₁o, hU₁arc, hA₃, hA₃i, hA₃l, hA₃r, hflat, harcrow⟩ :=
    Work.Drive.Push.flattenAlignedSpineStraight hn F hFsm hFimm γ₁ hγ₁smooth K hKfin a e he
      haff hrange
  -- ## the arc row on the flattened side
  have hrow₀ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      A₃ (A₂ (A₁ (f (γ₁ t)))) = K.starProjection a + t • e := by
    intro t ht
    exact harcrow t ht
  have hA0 : A₃ (A₂ (A₁ (f p₁))) = K.starProjection a := by
    have h := hrow₀ 0 (by norm_num)
    rw [hγ₁0] at h
    simpa using h
  have hA1 : A₃ (A₂ (A₁ (f q₁))) = K.starProjection a + e := by
    have h := hrow₀ 1 (by norm_num)
    rw [hγ₁1] at h
    simpa using h
  -- ## assembly: intersect the two tubes
  refine ⟨fun y => A₃ (A₂ (A₁ y)), fun y => A₁i (A₂i (A₃i y)), K, U₁ ∩ U₀, ?_, ?_, ?_, ?_,
    hKfin, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hA₃.comp (hA₂.comp hA₁)
  · exact hA₁i.comp (hA₂i.comp hA₃i)
  · intro y
    show A₁i (A₂i (A₃i (A₃ (A₂ (A₁ y))))) = y
    rw [hA₃l (A₂ (A₁ y)), hA₂l (A₁ y), hA₁l y]
  · intro y
    show A₃ (A₂ (A₁ (A₁i (A₂i (A₃i y))))) = y
    rw [hA₁r (A₂i (A₃i y)), hA₂r (A₃i y), hA₃r y]
  · exact hU₁o.inter hU₀o
  · exact (closure_mono Set.inter_subset_right).trans hU₀cl
  · exact fun x hx => ⟨hU₁arc hx, hU₀arc hx⟩
  · exact fun hx => hp₂U₀ hx.2
  · exact fun hx => hq₂U₀ hx.2
  · intro x hx
    exact hflat x hx.1
  · intro t ht
    change A₃ (A₂ (A₁ (f (γ₁ t)))) =
      A₃ (A₂ (A₁ (f p₁))) + t • (A₃ (A₂ (A₁ (f q₁))) - A₃ (A₂ (A₁ (f p₁))))
    rw [hA0, hA1, hrow₀ t ht,
      show K.starProjection a + e - K.starProjection a = e from by abel]

end Work.Drive.PushDisc
