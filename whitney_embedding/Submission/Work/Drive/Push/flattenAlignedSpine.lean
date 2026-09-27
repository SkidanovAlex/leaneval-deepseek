import Mathlib
import Submission.Work.Drive.Push.localGraphFunction
import Submission.Work.Whitney.CutPush.collar_injectivity
import Submission.Work.Whitney.CutPush.local_injectivity
import Submission.Work.Whitney.CutPush.smooth_extension_near_compact
import Submission.Work.Whitney.CutPush.collar_shear
import Submission.Work.Whitney.CutPush.spine_composite
import Submission.Work.Whitney.CutPush.slice_flattening

/-!
# Flattening an aligned spine
-/

set_option maxHeartbeats 4000000

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

namespace Work.Drive.Push

/-- A function smooth on an open set, multiplied by a smooth scalar function whose topological
support is contained in that set, is smooth. -/
theorem contDiff_smul_of_contDiffOn' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {N : ℕ}
    {Ω : Set X} {f : X → EuclideanSpace ℝ (Fin N)} {g : X → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f Ω) (hΩ : IsOpen Ω)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (h : tsupport g ⊆ Ω) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => g p • f p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ Ω
  · exact hg.contDiffAt.smul (hf.contDiffAt (hΩ.mem_nhds hp))
  · have hpk : p ∉ tsupport g := fun h' => hp (h h')
    have hopen : (tsupport g)ᶜ ∈ 𝓝 p := (isClosed_tsupport g).isOpen_compl.mem_nhds hpk
    have hev : (fun q => g q • f q) =ᶠ[𝓝 p] (fun _ => (0 : EuclideanSpace ℝ (Fin N))) := by
      filter_upwards [hopen] with q hq
      have hq0 : g q = 0 := by
        by_contra hz
        exact hq (subset_tsupport g (Function.mem_support.mpr hz))
      rw [hq0, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **The direction of the spine lies in the plane.**  The derivative of `t ↦ F (δ t)` is `e`, and
it is also the composition of `mfderiv F (δ t)` with `mfderiv δ t`, hence lies in `K`. -/
theorem spine_direction_mem {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (δ : ℝ → M)
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n))))
    (a e : EuclideanSpace ℝ (Fin (2 * n)))
    (haff : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → F (δ t) = a + t • e)
    (hrange : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)).toLinearMap = K) :
    e ∈ K := by
  have ht : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have haffd : HasFDerivAt (fun t : ℝ => a + t • e)
      (ContinuousLinearMap.toSpanSingleton ℝ e) (1 / 2 : ℝ) := by
    have h1 : HasFDerivAt (fun t : ℝ => t • e)
        (ContinuousLinearMap.toSpanSingleton ℝ e) (1 / 2 : ℝ) :=
      (ContinuousLinearMap.toSpanSingleton ℝ e).hasFDerivAt
    simpa using h1.const_add a
  have hev : (fun t : ℝ => F (δ t)) =ᶠ[𝓝 (1 / 2 : ℝ)] (fun t : ℝ => a + t • e) := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)] with t ht'
    exact haff t (Set.Ioo_subset_Icc_self ht')
  have hmdδ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ (1 / 2 : ℝ) :=
    hδ.mdifferentiableAt (by simp)
  have hmdF : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ (1 / 2 : ℝ)) :=
    hF.mdifferentiableAt (by simp)
  have hkey : e = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ (1 / 2 : ℝ))
      ((mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ (1 / 2 : ℝ)) 1) := by
    have hfd : fderiv ℝ (fun t : ℝ => F (δ t)) (1 / 2 : ℝ) 1 = e := by
      have h2 : fderiv ℝ (fun t : ℝ => F (δ t)) (1 / 2 : ℝ)
          = ContinuousLinearMap.toSpanSingleton ℝ e :=
        (haffd.congr_of_eventuallyEq hev).fderiv
      rw [h2, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rw [← hfd, ← mfderiv_eq_fderiv]
    exact mfderiv_comp_apply (x := (1 / 2 : ℝ)) (f := δ) (g := F) hmdF hmdδ (1 : ℝ)
  rw [hkey]
  have hmem : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ (1 / 2 : ℝ))
      ((mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) δ (1 / 2 : ℝ)) 1)
      ∈ LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ (1 / 2 : ℝ))).toLinearMap) :=
    LinearMap.mem_range_self _ _
  rw [hrange (1 / 2 : ℝ) ht] at hmem
  exact hmem



/-- **Flattening an aligned spine.** -/
theorem flattenAlignedSpine {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
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
      (∀ x : M, x ∈ U → A (F x) ∈ K) := by
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
  refine ⟨Uset, Φ, Φinv, hUsetopen, hUseg, hΦsm, hΦinvsm, hΦleft, hΦright, ?_⟩
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
  exact Subtype.coe_prop _

end Work.Drive.Push
