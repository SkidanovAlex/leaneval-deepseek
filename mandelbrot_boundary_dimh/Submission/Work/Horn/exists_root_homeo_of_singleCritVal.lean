import Mathlib
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap
import Submission.Work.BasinSC.StepOneCrit.isConnected_diff_finite
import Submission.Work.Horn.fiber_finite
import Submission.Work.Horn.eventually_ncard_eq_of_local_trivialization
import Submission.Work.Horn.exists_ball_injOn_and_mapsTo
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn
import Submission.Work.HornSeq.exists_homeomorph_unitDisc_of_injOn_analytic
import Submission.Work.HornSeq.eventually_ncard_fiber_eq
import Submission.Work.HornSeq.isLocalHomeomorphOn_of_localInj_surj
import Submission.Work.HornSeq.local_inj_surj_phi_comp
import Submission.Work.HornSeq.isCompact_preimage_phi_comp_of_notMem

namespace Work.Horn

open Set Metric Filter Topology
open scoped Topology

/-! ## The main theorem -/

theorem exists_root_homeo_of_singleCritVal {B : Set ℂ} {f : ℂ → ℂ} {v : ℂ} {φ : ℂ → ℂ}
    (hBopen : IsOpen B) (hBconn : IsConnected B)
    (hf : DifferentiableOn ℂ f B) (hmap : Set.MapsTo f B B) (hsurj : B ⊆ f '' B)
    (hproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hvB : v ∈ B) (hcritval : ∀ z ∈ B, deriv f z = 0 → f z = v)
    (hnc : ∃ c ∈ B, ¬ ∀ᶠ z in nhds c, f z = f c)
    (hφ0 : φ v = 0) (hφmaps : ∀ z ∈ B, ‖φ z‖ < 1)
    (hφsurj : ∀ w : ℂ, ‖w‖ < 1 → ∃ z ∈ B, φ z = w)
    (hφne : ∀ z ∈ B, z ≠ v → φ z ≠ 0)
    (hφana : ∀ z ∈ B, AnalyticAt ℂ φ z)
    (hφinj : Set.InjOn φ B) :
    ∃ (d : ℕ) (_ : 0 < d) (ψ : ↥(B \ (B ∩ f ⁻¹' {v})) ≃ₜ ↥Work.BasinSC.puncturedDisc),
      ∀ z : ↥(B \ (B ∩ f ⁻¹' {v})), (ψ z : ℂ) ^ d = φ (f z.1) := by
  classical
  have hpre : IsPreconnected B := hBconn.isPreconnected
  obtain ⟨c, hcB, hnc'⟩ := hnc
  -- the fibre of `v` is finite
  have hFfin : (B ∩ f ⁻¹' {v}).Finite := fiber_finite hBopen hpre hf hcB hnc' hproper hvB
  -- the punctured domain
  set Zset : Set ℂ := B \ (B ∩ f ⁻¹' {v}) with hZdef
  have hZmem : ∀ z : ℂ, z ∈ Zset ↔ z ∈ B ∧ f z ≠ v := by
    intro z
    constructor
    · intro hz
      exact ⟨hz.1, fun h => hz.2 ⟨hz.1, by simpa using h⟩⟩
    · rintro ⟨hzB, hz⟩
      exact ⟨hzB, fun h => hz (by simpa using h.2)⟩
  have hZopen : IsOpen Zset := hBopen.sdiff hFfin.isClosed
  have hZconn : IsConnected Zset :=
    Work.BasinSC.StepOneCrit.isConnected_diff_finite hBopen hBconn hFfin
  haveI hZc : ConnectedSpace ↥Zset := isConnected_iff_connectedSpace.mp hZconn
  haveI hZl : LocallyPathConnectedSpace ↥Zset := hZopen.locallyPathConnectedSpace
  haveI hZp : PathConnectedSpace ↥Zset := PathConnectedSpace.of_locallyPathConnectedSpace
  -- the homeomorphism `B ≅ 𝔻` realised by `φ`
  obtain ⟨H, hH⟩ := Work.HornSeq.exists_homeomorph_unitDisc_of_injOn_analytic hBopen hφmaps hφsurj hφana hφinj
  -- the inverse function
  let φi : ℂ → ℂ := fun w => if h : w ∈ Metric.ball (0 : ℂ) 1 then (H.symm ⟨w, h⟩ : ℂ) else v
  have hφi_mem : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → φi w ∈ B := by
    intro w hw
    have h1 : φi w = (H.symm ⟨w, hw⟩ : ℂ) := by unfold φi; rw [dif_pos hw]
    rw [h1]
    exact (H.symm ⟨w, hw⟩).2
  have hφi_eq : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → φ (φi w) = w := by
    intro w hw
    have hmem := hφi_mem w hw
    have h1 : (⟨φi w, hmem⟩ : ↥B) = H.symm ⟨w, hw⟩ := by
      apply Subtype.ext
      show φi w = (H.symm ⟨w, hw⟩ : ℂ)
      unfold φi; rw [dif_pos hw]
    calc φ (φi w) = (H ⟨φi w, hmem⟩ : ℂ) := (hH ⟨φi w, hmem⟩).symm
      _ = (H (H.symm ⟨w, hw⟩) : ℂ) := by rw [h1]
      _ = w := by rw [Homeomorph.apply_symm_apply]
  have hφi_self : ∀ z : ℂ, z ∈ B → φi (φ z) = z := by
    intro z hz
    have hzball : φ z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hφmaps z hz
    have h1 : (⟨φ z, hzball⟩ : ↥(Metric.ball (0 : ℂ) 1)) = H ⟨z, hz⟩ := by
      apply Subtype.ext
      show φ z = (H ⟨z, hz⟩ : ℂ)
      rw [hH]
    calc φi (φ z) = (H.symm ⟨φ z, hzball⟩ : ℂ) := by unfold φi; rw [dif_pos hzball]
      _ = (H.symm (H ⟨z, hz⟩) : ℂ) := by rw [h1]
      _ = z := by rw [Homeomorph.symm_apply_apply]
  have hφi_ne_v : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 → w ≠ 0 → φi w ≠ v := by
    intro w hw hw0 h
    have h1 := hφi_eq w hw
    rw [h, hφ0] at h1
    exact hw0 h1.symm
  -- the punctured disc is open
  have hWopen : IsOpen Work.BasinSC.puncturedDisc := by
    have hset : Work.BasinSC.puncturedDisc = Metric.ball (0 : ℂ) 1 \ {0} := by
      ext w
      simp only [Work.BasinSC.mem_puncturedDisc, Metric.mem_ball, dist_zero_right, Set.mem_sdiff,
        Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact Metric.isOpen_ball.sdiff isClosed_singleton
  -- the map `φ ∘ f` out of the punctured domain
  have hqZ : ∀ z : ℂ, z ∈ Zset → φ (f z) ∈ Work.BasinSC.puncturedDisc := by
    intro z hz
    have hz' := (hZmem z).mp hz
    exact ⟨hφne (f z) (hmap hz'.1) hz'.2, hφmaps (f z) (hmap hz'.1)⟩
  let q : ↥Zset → ↥Work.BasinSC.puncturedDisc := fun z => ⟨φ (f z.1), hqZ z.1 z.2⟩
  have hcontQ : ContinuousOn (fun z : ℂ => φ (f z)) Zset := by
    have hφcont : ContinuousOn φ B := fun z hz => (hφana z hz).continuousAt.continuousWithinAt
    exact (hφcont.comp hf.continuousOn hmap).mono (fun z hz => hz.1)
  have hdata := Work.HornSeq.local_inj_surj_phi_comp hBopen hf hmap hcritval hφ0 hφmaps hφsurj hφne hφana hφinj
  have hqloc : IsLocalHomeomorphOn q Set.univ :=
    Work.HornSeq.isLocalHomeomorphOn_of_localInj_surj hWopen hcontQ hqZ hdata
  -- properness of `q`
  have hqcont : Continuous q := by
    have hcc : Continuous (fun z : ↥Zset => φ (f z.1)) :=
      continuousOn_iff_continuous_domRestrict.mp hcontQ
    exact hcc.subtype_mk (fun z => hqZ z.1 z.2)
  have hproperK : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 → φ v ∉ K →
      IsCompact ((fun z : ↥Zset => φ (f z.1)) ⁻¹' K) :=
    fun K hK hKb hvK => Work.HornSeq.isCompact_preimage_phi_comp_of_notMem hmap hproper hFfin H hH hK hKb hvK
  have hqproper : IsProperMap q := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hqcont, ?_⟩
    intro K hK
    have hK' : IsCompact (Subtype.val '' K : Set ℂ) := hK.image continuous_subtype_val
    have hK'b : (Subtype.val '' K : Set ℂ) ⊆ Metric.ball (0 : ℂ) 1 := by
      rintro x ⟨u, hu, rfl⟩
      have hu' : (u : ℂ) ∈ Work.BasinSC.puncturedDisc := u.2
      rw [Metric.mem_ball, dist_zero_right]
      exact hu'.2
    have hKv : φ v ∉ (Subtype.val '' K : Set ℂ) := by
      rintro ⟨u, hu, huv⟩
      exact u.2.1 (by rw [huv]; exact hφ0)
    have hKeq : q ⁻¹' K = (fun z : ↥Zset => φ (f z.1)) ⁻¹' (Subtype.val '' K) := by
      ext z
      constructor
      · intro hz
        exact ⟨q z, hz, rfl⟩
      · rintro ⟨u, hu, huz⟩
        have hqu : q z = u := Subtype.ext huz.symm
        show q z ∈ K
        rwa [hqu]
    rw [hKeq]
    exact hproperK _ hK' hK'b hKv
  have hqclosed : IsClosedMap q := hqproper.isClosedMap
  -- the fibre cardinal is locally constant, hence constant
  have hcount : ∀ w : ↥Work.BasinSC.puncturedDisc,
      (q ⁻¹' {w}).ncard = (B ∩ f ⁻¹' {φi (w : ℂ)}).ncard := by
    intro w
    have hwball : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact w.2.2
    have hweq : φ (φi (w : ℂ)) = (w : ℂ) := hφi_eq (w : ℂ) hwball
    have hφimem : φi (w : ℂ) ∈ B := hφi_mem (w : ℂ) hwball
    have hφine : φi (w : ℂ) ≠ v := hφi_ne_v (w : ℂ) hwball w.2.1
    refine Set.ncard_congr (fun z _ => (z.1 : ℂ)) ?_ ?_ ?_
    · intro z hz
      have hzZ := (hZmem z.1).mp z.2
      have hqz : φ (f z.1) = (w : ℂ) :=
        congrArg (fun x : ↥Work.BasinSC.puncturedDisc => (x : ℂ)) (Set.mem_singleton_iff.mp hz)
      refine ⟨hzZ.1, ?_⟩
      show f z.1 = φi (w : ℂ)
      exact hφinj (hmap hzZ.1) hφimem (by rw [hqz, hweq])
    · intro a b ha hb hab
      exact Subtype.ext hab
    · intro t ht
      obtain ⟨htB, htf⟩ := ht
      have htf' : f t = φi (w : ℂ) := Set.mem_singleton_iff.mp htf
      have htZ : t ∈ Zset := (hZmem t).mpr ⟨htB, by rw [htf']; exact hφine⟩
      refine ⟨⟨t, htZ⟩, ?_, rfl⟩
      show q ⟨t, htZ⟩ = w
      apply Subtype.ext
      show φ (f t) = (w : ℂ)
      rw [htf', hweq]
  have hfibfin : ∀ w : ↥Work.BasinSC.puncturedDisc, (q ⁻¹' {w}).Finite := by
    intro w
    have hwball : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact w.2.2
    have hweq : φ (φi (w : ℂ)) = (w : ℂ) := hφi_eq (w : ℂ) hwball
    have hfin : (B ∩ f ⁻¹' {φi (w : ℂ)}).Finite :=
      fiber_finite hBopen hpre hf hcB hnc' hproper (hφi_mem (w : ℂ) hwball)
    refine Set.Finite.of_finite_image ?_ (fun a _ b _ hab => Subtype.ext hab)
    refine hfin.subset ?_
    rintro t ⟨z, hz, rfl⟩
    have hzZ := (hZmem z.1).mp z.2
    have hqz : φ (f z.1) = (w : ℂ) :=
      congrArg (fun x : ↥Work.BasinSC.puncturedDisc => (x : ℂ)) (Set.mem_singleton_iff.mp hz)
    refine ⟨hzZ.1, ?_⟩
    show f z.1 = φi (w : ℂ)
    exact hφinj (hmap hzZ.1) (hφi_mem (w : ℂ) hwball) (by rw [hqz, hweq])
  -- a base point of `B` different from `v`
  obtain ⟨t₁, ht₁B, ht₁ne⟩ : ∃ t ∈ B, t ≠ v := by
    have hBinf : B.Infinite := Work.BasinSC.StepOneCrit.isOpen_infinite hBopen hBconn.nonempty
    obtain ⟨t, htB, htv⟩ := hBinf.exists_notMem_finset ({v} : Finset ℂ)
    exact ⟨t, htB, by simpa using htv⟩
  let w₁ : ↥Work.BasinSC.puncturedDisc := ⟨φ t₁, hφne t₁ ht₁B ht₁ne, hφmaps t₁ ht₁B⟩
  let d : ℕ := (q ⁻¹' {w₁}).ncard
  have hw₁val : φi ((w₁ : ℂ)) = t₁ := by
    show φi (φ t₁) = t₁
    exact hφi_self t₁ ht₁B
  have hdpos : 0 < d := by
    show 0 < (q ⁻¹' {w₁}).ncard
    rw [Set.ncard_pos (hfibfin w₁)]
    obtain ⟨z, hzB, hzf⟩ := hsurj ht₁B
    have hzZ : z ∈ Zset := (hZmem z).mpr ⟨hzB, by rw [hzf]; exact ht₁ne⟩
    refine ⟨⟨z, hzZ⟩, ?_⟩
    show q ⟨z, hzZ⟩ = w₁
    apply Subtype.ext
    show φ (f z) = (w₁ : ℂ)
    rw [hzf]
  haveI hpreBv : PreconnectedSpace ↥(B \ {v}) := isPreconnected_iff_preconnectedSpace.mp
    (Work.BasinSC.StepOneCrit.isPreconnected_diff_singleton hBopen hpre v)
  have hNloc : IsLocallyConstant
      (fun u : ↥(B \ {v}) => (B ∩ f ⁻¹' {(u : ℂ)}).ncard) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    rw [nhds_subtype]
    refine Filter.eventually_comap.mpr ?_
    have huB : (u : ℂ) ∈ B := u.2.1
    have hev := Work.HornSeq.eventually_ncard_fiber_eq hBopen hpre hf hcB hnc' hproper huB
      (fun z hz hfz => by
        intro h0
        exact u.2.2 (Set.mem_singleton_iff.mpr (by rw [← hfz, hcritval z hz h0])))
    filter_upwards [hev] with s hs a ha
    rw [ha]
    exact hs
  have hconst : ∀ w : ↥Work.BasinSC.puncturedDisc, (q ⁻¹' {w}).ncard = d := by
    intro w
    have hwball : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact w.2.2
    show (q ⁻¹' {w}).ncard = (q ⁻¹' {w₁}).ncard
    rw [hcount w, hcount w₁, hw₁val]
    exact hNloc.apply_eq_of_preconnectedSpace
      ⟨φi (w : ℂ), hφi_mem (w : ℂ) hwball, by simpa using hφi_ne_v (w : ℂ) hwball w.2.1⟩
      ⟨t₁, ht₁B, by simpa using ht₁ne⟩
  -- the covering is classified
  have hcov : IsCoveringMap q := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    exact IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hqclosed (fun x _ => hfibfin x) hqloc
  obtain ⟨dd, hdd, ψ, hψ⟩ :=
    Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap hcov ⟨d, hdpos, hconst⟩
  exact ⟨dd, hdd, ψ, fun z => hψ z⟩

end Work.Horn
