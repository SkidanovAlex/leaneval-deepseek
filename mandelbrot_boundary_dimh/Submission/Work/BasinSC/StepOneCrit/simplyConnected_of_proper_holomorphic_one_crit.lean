import Mathlib
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap
import Submission.Work.BasinSC.StepOneCrit.Auxiliary
import Submission.Work.BasinSC.StepOneCrit.finite_fiber
import Submission.Work.BasinSC.StepOneCrit.isConnected_diff_finite
import Submission.Work.BasinSC.StepOneCrit.homeomorph_ball_single_zero
import Submission.Work.BasinSC.StepOneCrit.uniformization_to_ball
import Submission.Lib.Unif2.Commons.Analysis.Complex.bijective_of_properInto_ball_holomorphic_single_zero
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
import Submission.Lib.Unif2.Commons.Topology.Covering.natCard_fiber_eq_of_preconnected
import Submission.Lib.Unif2.Work.Modulus.puncturedConnected

/-!
# Riemann-Hurwitz-lite, one critical point (the inductive step of Shishikura's Lemma 5.2)

If `p : V' → V` is proper, surjective and holomorphic between plane domains, the target `V` is a
nonempty open connected simply connected proper subdomain of `ℂ`, and `p` has exactly one critical
point `c ∈ V'`, then `V'` is simply connected (indeed `V' ≅ 𝔻`).

Route: `V ≅ 𝔻` (Riemann mapping, `uniformization_to_ball`); `Z := V' ∖ q⁻¹(q c) → 𝔻*` is a
connected covering of degree `d`; by the classification of coverings of `𝔻*`
(`Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap`) one gets `Z ≅ 𝔻*` and then
`q⁻¹(0) = {c}` and the local degree at `c` is `d`, so `q - q c` has a holomorphic `d`-th root `g`
with `g^d = q - q c`, and `g` is proper of degree `1`, hence a homeomorphism `V' ≅ 𝔻`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Topology Manifold
open Filter Set Metric

namespace Work.BasinSC.StepOneCrit

-- Riemann-Hurwitz-lite, one critical point (the inductive step of Shishikura's Lemma 5.2):
-- if `p : V' → V` is proper, surjective and holomorphic between plane domains, the target `V` is
-- a nonempty open connected simply connected proper subdomain of `ℂ`, and `p` has exactly one
-- critical point `c ∈ V'`, then `V'` is simply connected (indeed `V' ≅ 𝔻`).
theorem simplyConnected_of_proper_holomorphic_one_crit
    {V V' : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty) (hVsc : SimplyConnectedSpace ↥V)
    (hVproper : V ≠ Set.univ) (hV'o : IsOpen V') (hV'c : IsConnected V')
    {p : ℂ → ℂ} (hp : DifferentiableOn ℂ p V')
    (hmaps : Set.MapsTo p V' V) (hsurj : V ⊆ p '' V')
    (hprop : ∀ K ⊆ V, IsCompact K → IsCompact (V' ∩ p ⁻¹' K))
    {c : ℂ} (hc : c ∈ V') (hc' : deriv p c = 0) (huniq : ∀ z ∈ V', deriv p z = 0 → z = c) :
    SimplyConnectedSpace ↥V' := by
  classical
  -- Step 0: `p c ∈ V`
  have hpc : p c ∈ V := hmaps hc
  -- Step 1: uniformise the target
  obtain ⟨φ, ψ, hφ0, hφmaps, hψmaps, hφψ, hψφ, hφdiff, hψdiff, hφderiv, hψderiv⟩ :=
    uniformization_to_ball hVo hVne hVsc hVproper hpc
  -- Step 2: transport `p` to `q = φ ∘ p : V' → 𝔻`
  let q : ℂ → ℂ := fun z => φ (p z)
  have hqdiff : ∀ z ∈ V', DifferentiableAt ℂ q z := fun z hz =>
    (hφdiff (p z) (hmaps hz)).comp z (hp.differentiableAt (hV'o.mem_nhds hz))
  have hqmaps : ∀ z ∈ V', q z ∈ Metric.ball (0 : ℂ) 1 := fun z hz => hφmaps (p z) (hmaps hz)
  have hqc : q c = 0 := hφ0
  have hqcrit : deriv q c = 0 := by
    change deriv (φ ∘ p) c = 0
    rw [deriv_comp (x := c) (h := p) (h₂ := φ)
      (hφdiff (p c) hpc) (hp.differentiableAt (hV'o.mem_nhds hc)), hc', mul_zero]
  have hquniq : ∀ z ∈ V', deriv q z = 0 → z = c := by
    intro z hz hz0
    change deriv (φ ∘ p) z = 0 at hz0
    rw [deriv_comp (x := z) (h := p) (h₂ := φ)
      (hφdiff (p z) (hmaps hz)) (hp.differentiableAt (hV'o.mem_nhds hz))] at hz0
    rcases mul_eq_zero.mp hz0 with h | h
    · exact absurd h (hφderiv (p z) (hmaps hz))
    · exact huniq z hz h
  have hqsurj : Metric.ball (0 : ℂ) 1 ⊆ q '' V' := by
    intro w hw
    obtain ⟨z, hz, hzv⟩ := hsurj (hψmaps w hw)
    refine ⟨z, hz, ?_⟩
    change φ (p z) = w
    rw [hzv, hψφ w hw]
  have hψcont : ContinuousOn ψ (Metric.ball (0 : ℂ) 1) :=
    fun w hw => (hψdiff w hw).continuousAt.continuousWithinAt
  have hqprop : ∀ K ⊆ Metric.ball (0 : ℂ) 1, IsCompact K → IsCompact (V' ∩ q ⁻¹' K) := by
    intro K hK hKc
    have hψKc : IsCompact (ψ '' K) := hKc.image_of_continuousOn (hψcont.mono hK)
    have hψKV : ψ '' K ⊆ V := by rintro _ ⟨w, hw, rfl⟩; exact hψmaps w (hK hw)
    have hPK : IsCompact ((fun z : ↥V' => p z) ⁻¹' (ψ '' K)) := by
      have h : IsCompact (V' ∩ p ⁻¹' (ψ '' K)) := hprop _ hψKV hψKc
      have hset : (fun z : ↥V' => p z) ⁻¹' (ψ '' K)
          = Subtype.val ⁻¹' (V' ∩ p ⁻¹' (ψ '' K)) := by
        ext z; exact ⟨fun hz => ⟨z.2, hz⟩, fun hz => hz.2⟩
      rw [hset]
      exact (Topology.IsInducing.subtypeVal (t := V')).isCompact_preimage' h
        (by rintro z ⟨hzV, -⟩; exact ⟨⟨z, hzV⟩, rfl⟩)
    have hQcont : Continuous fun z : ↥V' => q z := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (hqdiff z.1 z.2).continuousAt.comp continuous_subtype_val.continuousAt
    have hcl : IsClosed ((fun z : ↥V' => q z) ⁻¹' K) := hKc.isClosed.preimage hQcont
    have hsub : (fun z : ↥V' => q z) ⁻¹' K ⊆ (fun z : ↥V' => p z) ⁻¹' (ψ '' K) := by
      intro z hz
      change q z ∈ K at hz
      have hzV : p z.1 ∈ V := hmaps z.2
      have h1 : ψ (q z) = p z.1 := by
        change ψ (φ (p z.1)) = p z.1
        rw [hφψ (p z.1) hzV]
      show p z.1 ∈ ψ '' K
      rw [← h1]
      exact ⟨q z, hz, rfl⟩
    have hcomp : IsCompact ((fun z : ↥V' => q z) ⁻¹' K) := hPK.of_isClosed_subset hcl hsub
    have himg : Subtype.val '' ((fun z : ↥V' => q z) ⁻¹' K) = V' ∩ q ⁻¹' K := by
      ext z; constructor
      · rintro ⟨z', hz', rfl⟩; exact ⟨z'.2, hz'⟩
      · rintro ⟨hz'V', hz'K⟩; exact ⟨⟨z, hz'V'⟩, hz'K, rfl⟩
    rw [← himg]
    exact hcomp.image continuous_subtype_val
  -- Step 3: the zero fibre `A` is finite and the punctured domain `Z` is connected
  have hqdiffOn : DifferentiableOn ℂ q V' := fun z hz => (hqdiff z hz).differentiableWithinAt
  have hAcomp : IsCompact (V' ∩ q ⁻¹' {0}) :=
    hqprop {0} (by rintro z rfl; simp [Metric.mem_ball]) isCompact_singleton
  have hhalf : (1 / 2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; norm_num
  obtain ⟨z₁, hz₁V', hz₁q⟩ := hqsurj hhalf
  have hAne : ∃ z ∈ V', q z ≠ 0 := ⟨z₁, hz₁V', by rw [hz₁q]; norm_num⟩
  set A : Set ℂ := {z : ℂ | z ∈ V' ∧ q z = 0} with hAdef
  have hAeq : V' ∩ q ⁻¹' {0} = A := by ext z; simp [hAdef]
  have hAfinA : A.Finite := by
    have h := finite_fiber hV'o hV'c hqdiffOn hAne hAcomp
    rwa [hAeq] at h
  have hZopen : IsOpen (V' \ A) := hV'o.sdiff hAfinA.isClosed
  have hZconn : IsConnected (V' \ A) := isConnected_diff_finite hV'o hV'c hAfinA
  -- the punctured target is open and nonempty
  have hpdopen : IsOpen Work.BasinSC.puncturedDisc := by
    have h1 : Work.BasinSC.puncturedDisc = ({0}ᶜ : Set ℂ) ∩ Metric.ball (0 : ℂ) 1 := by
      ext w; simp [Work.BasinSC.puncturedDisc, Metric.mem_ball, dist_eq_norm]
    rw [h1]; exact isOpen_compl_singleton.inter Metric.isOpen_ball
  have hpdne : Nonempty ↥Work.BasinSC.puncturedDisc :=
    ⟨⟨1 / 2, by rw [Work.BasinSC.mem_puncturedDisc]; exact ⟨by norm_num, by norm_num⟩⟩⟩
  -- the covering map `q` restricted to `Z`
  have hZq : ∀ z : ↥(V' \ A), q z.1 ∈ Work.BasinSC.puncturedDisc := fun z =>
    ⟨fun h0 => z.2.2 ⟨z.2.1, h0⟩, by
      have h := hqmaps z.1 z.2.1
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      exact h⟩
  let qt : ↥(V' \ A) → ↥Work.BasinSC.puncturedDisc := fun z => ⟨q z.1, hZq z⟩
  have hqtcont : Continuous qt := by
    have h1 : Continuous fun z : ↥(V' \ A) => q z.1 := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (hqdiff z.1 z.2.1).continuousAt.comp continuous_subtype_val.continuousAt
    exact h1.subtype_mk _
  haveI hZne' : Nonempty ↥(V' \ A) :=
    ⟨⟨z₁, hz₁V', by rintro ⟨-, h0⟩; rw [hz₁q] at h0; norm_num at h0⟩⟩
  have hlocqt : IsLocalHomeomorphOn qt Set.univ := by
    have hlocq : IsLocalHomeomorphOn q (V' \ A) := by
      refine IsLocalHomeomorphOn.mk q (V' \ A) fun z hz => ?_
      have hzderiv : deriv q z ≠ 0 := by
        intro h0
        exact hz.2 ⟨hz.1, by rw [hquniq z hz.1 h0]; exact hqc⟩
      have hana : AnalyticAt ℂ q z := hqdiffOn.analyticAt (hV'o.mem_nhds hz.1)
      let u : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv q z) hzderiv)
      have hsf : HasStrictFDerivAt q (u : ℂ →L[ℂ] ℂ) z :=
        (hana.hasStrictDerivAt).hasStrictFDerivAt_equiv hzderiv
      exact ⟨hsf.toOpenPartialHomeomorph, hsf.mem_toOpenPartialHomeomorph_source, fun w _ => rfl⟩
    have hlocV : IsLocalHomeomorphOn (Subtype.val : ↥(V' \ A) → ℂ) Set.univ :=
      IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn
        ((hZopen.isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph _) |>.mono (subset_univ _)
    have hloc1 : IsLocalHomeomorphOn (fun z : ↥(V' \ A) => q z.1) Set.univ :=
      hlocq.comp hlocV (by intro z _; exact z.2)
    haveI := hpdne
    have hinctop : IsLocalHomeomorphOn (Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ) Set.univ :=
      IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn
        ((hpdopen.isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph _) |>.mono (subset_univ _)
    have hinc : IsLocalHomeomorphOn (Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ)
        (qt '' Set.univ) :=
      hinctop.mono (by rintro _ ⟨z, -, rfl⟩; exact trivial)
    refine IsLocalHomeomorphOn.of_comp_left (f := qt)
      (g := (Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ)) (s := Set.univ) ?_ hinc ?_
    · have h2 : (Subtype.val ∘ qt) = fun z : ↥(V' \ A) => q z.1 := rfl
      rw [h2]; exact hloc1
    · intro z _; exact hqtcont.continuousAt
  have hqtproper : IsProperMap qt := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hqtcont, ?_⟩
    intro K hK
    have hK' : IsCompact ((Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ) '' K) :=
      hK.image continuous_subtype_val
    have hK'D : (Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ) '' K ⊆ Metric.ball (0 : ℂ) 1 := by
      rintro _ ⟨w, _, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact w.2.2
    have hc1 : IsCompact (V' ∩ q ⁻¹' ((Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ) '' K)) :=
      hqprop _ hK'D hK'
    have hset : qt ⁻¹' K
        = Subtype.val ⁻¹' (V' ∩ q ⁻¹' ((Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ) '' K)) := by
      ext z; constructor
      · intro hz; exact ⟨z.2.1, ⟨qt z, hz, rfl⟩⟩
      · rintro ⟨hzV', hzK'⟩
        obtain ⟨w, hwK, hwv⟩ := hzK'
        have hEq : qt z = w := Subtype.ext hwv.symm
        show qt z ∈ K
        rw [hEq]; exact hwK
    rw [hset]
    exact (Topology.IsInducing.subtypeVal (t := V' \ A)).isCompact_preimage' hc1
      (by
        rintro z ⟨hzV', hzS⟩
        obtain ⟨w, -, hwv⟩ := hzS
        exact ⟨⟨z, hzV', fun hA => w.2.1 (hwv.trans hA.2)⟩, rfl⟩)
  have hqtclosed : IsClosedMap qt := hqtproper.isClosedMap
  have hfibfin : ∀ w ∈ (Set.univ : Set ↥Work.BasinSC.puncturedDisc), (qt ⁻¹' {w}).Finite := by
    intro w _
    have hcomp : IsCompact (V' ∩ q ⁻¹' {(w : ℂ)}) :=
      hqprop {w.1} (by
        rintro z rfl
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact w.2.2) isCompact_singleton
    obtain ⟨z₂, hz₂V', hz₂q⟩ := hqsurj (Metric.mem_ball_self zero_lt_one)
    have hne : ∃ z ∈ V', q z ≠ (w : ℂ) := ⟨z₂, hz₂V', by rw [hz₂q]; exact Ne.symm w.2.1⟩
    have hfin := finite_fiber hV'o hV'c hqdiffOn hne hcomp
    have himg : ((Subtype.val : ↥(V' \ A) → ℂ) '' (qt ⁻¹' {w})).Finite := by
      refine hfin.subset ?_
      rintro z ⟨z', hz', rfl⟩
      have hz'q : q z'.1 = (w : ℂ) := by
        have h2 := congrArg (fun t : ↥Work.BasinSC.puncturedDisc => (t : ℂ)) hz'
        simpa [qt] using h2
      exact ⟨z'.2.1, hz'q⟩
    exact Set.Finite.of_finite_image himg Subtype.val_injective.injOn
  have hcov : IsCoveringMap qt := by
    have hcovOn : IsCoveringMapOn qt Set.univ :=
      IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hqtclosed hfibfin (by rw [Set.preimage_univ]; exact hlocqt)
    exact isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  haveI hZpc : PathConnectedSpace ↥(V' \ A) := by
    haveI : ConnectedSpace ↥(V' \ A) := isConnected_iff_connectedSpace.mp hZconn
    haveI : LocallyPathConnectedSpace ↥(V' \ A) := hZopen.locallyPathConnectedSpace
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  haveI hZlpc : LocallyPathConnectedSpace ↥(V' \ A) := hZopen.locallyPathConnectedSpace
  haveI hPdprec : PreconnectedSpace ↥Work.BasinSC.puncturedDisc := by
    have h1 : IsPreconnected (Metric.ball (0 : ℂ) 1 \ {0}) :=
      Work.Modulus.isPreconnected_ball_diff_center (by norm_num : (0 : ℝ) < 1)
    have hset : Metric.ball (0 : ℂ) 1 \ {0} = Work.BasinSC.puncturedDisc := by
      ext w
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, Metric.mem_ball, dist_eq_norm, sub_zero,
        Work.BasinSC.puncturedDisc, Set.mem_ofPred_eq]
      tauto
    exact isPreconnected_iff_preconnectedSpace.mp (hset ▸ h1)
  -- Step 4: the covering has constant fibre cardinality `d`, hence is a `d`-th power
  let w0 : ↥Work.BasinSC.puncturedDisc :=
    ⟨1 / 2, by rw [Work.BasinSC.mem_puncturedDisc]; exact ⟨by norm_num, by norm_num⟩⟩
  have hz₁Z : z₁ ∈ V' \ A :=
    ⟨hz₁V', by rintro ⟨-, h0⟩; rw [hz₁q] at h0; norm_num at h0⟩
  have hw0fib : (qt ⁻¹' {w0}).Nonempty :=
    ⟨⟨z₁, hz₁Z⟩, by
      show qt ⟨z₁, hz₁Z⟩ = w0
      exact Subtype.ext hz₁q⟩
  let d : ℕ := (qt ⁻¹' {w0}).ncard
  have hd : 0 < d := by
    refine Set.ncard_pos (hfibfin w0 (Set.mem_univ _)) |>.mpr ?_
    exact hw0fib
  have hdeg : ∀ w : ↥Work.BasinSC.puncturedDisc, (qt ⁻¹' {w}).ncard = d := by
    intro w
    have hcard := Commons.Topology.Covering.natCard_fiber_eq_of_preconnected (f := qt)
      hcov.isCoveringMapOn isPreconnected_univ (Set.mem_univ w) (Set.mem_univ w0)
    simp only [Nat.card_coe_set_eq] at hcard
    rw [hcard]
  obtain ⟨d, hd, Ψh, hΨhpow⟩ :=
    Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap hcov ⟨d, hd, hdeg⟩
  -- Step 5: the d-th root of q on V'
  let ΨZ : ℂ → ℂ := fun z =>
    if h : z ∈ V' \ A then ((Ψh ⟨z, h⟩ : ↥Work.BasinSC.puncturedDisc) : ℂ) else 0
  have hΨZval : ∀ z (hz : z ∈ V' \ A),
      ΨZ z = ((Ψh ⟨z, hz⟩ : ↥Work.BasinSC.puncturedDisc) : ℂ) := fun z hz => dite_eq_left hz
  have hΨZpow : ∀ z ∈ V' \ A, (ΨZ z) ^ d = q z := by
    intro z hz
    rw [hΨZval z hz, hΨhpow ⟨z, hz⟩]
  have hΨZne : ∀ z ∈ V' \ A, ΨZ z ≠ 0 := by
    intro z hz h0
    have h := hΨZpow z hz
    rw [h0, zero_pow hd.ne'] at h
    exact hz.2 ⟨hz.1, h.symm⟩
  have hΨZcont : ContinuousOn ΨZ (V' \ A) := by
    have h1 : Continuous (((Subtype.val : ↥Work.BasinSC.puncturedDisc → ℂ)) ∘ Ψh) :=
      continuous_subtype_val.comp Ψh.continuous
    rw [continuousOn_iff_continuous_domRestrict]
    rw [show (V' \ A).domRestrict ΨZ = (Subtype.val ∘ Ψh : ↥(V' \ A) → ℂ) from by
      funext z
      exact hΨZval z.1 z.2]
    exact h1
  have hΨZan : ∀ z ∈ V' \ A, AnalyticAt ℂ ΨZ z := by
    intro z hz
    refine analyticAt_of_pow_eq_of_continuousAt hd (hqdiffOn.analyticAt (hV'o.mem_nhds hz.1))
      (fun h0 => hz.2 ⟨hz.1, h0⟩) (hΨZcont.continuousAt (hZopen.mem_nhds hz)) ?_
    filter_upwards [hZopen.mem_nhds hz] with w hw
    exact hΨZpow w hw
  have hΨZinj : ∀ z ∈ V' \ A, ∀ w ∈ V' \ A, ΨZ z = ΨZ w → z = w := by
    intro z hz w hw hzw
    rw [hΨZval z hz, hΨZval w hw] at hzw
    have h1 : (⟨z, hz⟩ : ↥(V' \ A)) = ⟨w, hw⟩ := Ψh.injective (Subtype.ext hzw)
    exact congrArg Subtype.val h1
  have hΨ0off : ∀ z ∉ V' \ A, ΨZ z = 0 := fun z hz => dite_eq_right hz
  have hΨ0A : ∀ z ∈ A, ΨZ z = 0 := fun z hz => dite_eq_right (fun h => h.2 hz)

  -- Step 6: psiZ is holomorphic on V' (removable singularity at the fibre of 0)
  have hΨan : ∀ z ∈ V', AnalyticAt ℂ ΨZ z := by
    intro z hz
    by_cases hzZ : z ∈ V' \ A
    · exact hΨZan z hzZ
    · have hzA : z ∈ A := by
        by_contra h
        exact hzZ ⟨hz, h⟩
      have hqzc : q z = 0 := hzA.2
      have hAc : IsClosed (A \ {z}) := (hAfinA.subset sdiff_subset).isClosed
      have hznot : z ∉ A \ {z} := fun h => h.2 rfl
      obtain ⟨δ, hδ, hδA⟩ := Metric.isOpen_iff.mp hAc.isOpen_compl z hznot
      have hnorm : ∀ᶠ w in 𝓝 z, ‖ΨZ w‖ = ‖q w‖ ^ ((1 : ℝ) / d) := by
        filter_upwards [hV'o.mem_nhds hz] with w hw
        by_cases hwZ : w ∈ V' \ A
        · have h1 : ‖q w‖ = ‖ΨZ w‖ ^ d := by rw [← hΨZpow w hwZ, norm_pow]
          rw [h1, ← Real.rpow_natCast (‖ΨZ w‖) d, ← Real.rpow_mul (norm_nonneg _),
            mul_one_div, div_self (by exact_mod_cast hd.ne'), Real.rpow_one]
        · have hwA : w ∈ A := by
            by_contra h
            exact hwZ ⟨hw, h⟩
          rw [hΨ0A w hwA, hwA.2, norm_zero,
            Real.zero_rpow (by positivity : ((1 : ℝ) / d) ≠ 0)]
      have htend : Tendsto (fun w => ‖ΨZ w‖) (𝓝 z) (𝓝 0) := by
        have hc : Tendsto (fun w => ‖q w‖) (𝓝 z) (𝓝 (‖q z‖)) :=
          (hqdiff z hz).continuousAt.norm
        rw [hqzc, norm_zero] at hc
        have hrpow := (Real.continuousAt_rpow_const 0 ((1 : ℝ) / d) (Or.inr (by positivity))).tendsto
        rw [Real.zero_rpow (by positivity : ((1 : ℝ) / d) ≠ 0)] at hrpow
        exact Tendsto.congr' (Filter.EventuallyEq.symm hnorm) (hrpow.comp hc)
      have hcont : ContinuousAt ΨZ z := by
        show Tendsto ΨZ (𝓝 z) (𝓝 (ΨZ z))
        rw [hΨ0A z hzA]
        exact tendsto_zero_iff_norm_tendsto_zero.mpr htend
      refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hcont
      have hball : ∀ᶠ w in 𝓝 (z : ℂ), w ∈ V' ∩ Metric.ball z δ :=
        (hV'o.inter Metric.isOpen_ball).mem_nhds ⟨hz, Metric.mem_ball_self hδ⟩
      filter_upwards [(show ∀ᶠ w in 𝓝 (z : ℂ), w ∈ V' ∩ Metric.ball z δ from hball).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwz
      exact (hΨZan w ⟨hw.1, fun hA => hδA hw.2 ⟨hA, hwz⟩⟩).differentiableAt
  have hΨpow : ∀ z ∈ V', (ΨZ z) ^ d = q z := by
    intro z hz
    by_cases hzZ : z ∈ V' \ A
    · exact hΨZpow z hzZ
    · have hzA : z ∈ A := by
        by_contra h
        exact hzZ ⟨hz, h⟩
      rw [hΨ0A z hzA, hzA.2, zero_pow hd.ne']
  have hΨmaps : ∀ z ∈ V', ΨZ z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h1 : ‖ΨZ z‖ ^ d = ‖q z‖ := by rw [← hΨpow z hz, norm_pow]
    have h2 : ‖q z‖ < 1 := by
      have h := hqmaps z hz
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    have h3 : ‖ΨZ z‖ ^ d < (1 : ℝ) ^ d := by rw [h1, one_pow]; exact h2
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) zero_le_one hd.ne').mp h3
  have hΨprop : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 →
      IsCompact (V' ∩ ΨZ ⁻¹' K) := by
    intro K hKc hKD
    have hKd : IsCompact ((fun ζ : ℂ => ζ ^ d) '' K) := hKc.image (continuous_id.pow d)
    have hKdD : (fun ζ : ℂ => ζ ^ d) '' K ⊆ Metric.ball (0 : ℂ) 1 := by
      rintro _ ⟨ζ, hζK, rfl⟩
      have hζ : ‖ζ‖ < 1 := by
        have h := hKD hζK
        rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hζ hd.ne'
    have hPK : IsCompact ((fun z : ↥V' => q z.1) ⁻¹' ((fun ζ : ℂ => ζ ^ d) '' K)) := by
      have h : IsCompact (V' ∩ q ⁻¹' ((fun ζ : ℂ => ζ ^ d) '' K)) := hqprop _ hKdD hKd
      have hset : (fun z : ↥V' => q z.1) ⁻¹' ((fun ζ : ℂ => ζ ^ d) '' K)
          = Subtype.val ⁻¹' (V' ∩ q ⁻¹' ((fun ζ : ℂ => ζ ^ d) '' K)) := by
        ext z; exact ⟨fun hz => ⟨z.2, hz⟩, fun hz => hz.2⟩
      rw [hset]
      exact (Topology.IsInducing.subtypeVal (t := V')).isCompact_preimage' h
        (by rintro z ⟨hzV, -⟩; exact ⟨⟨z, hzV⟩, rfl⟩)
    have hQcont : Continuous fun z : ↥V' => ΨZ z.1 := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (hΨan z.1 z.2).continuousAt.comp continuous_subtype_val.continuousAt
    have hcl : IsClosed ((fun z : ↥V' => ΨZ z.1) ⁻¹' K) := hKc.isClosed.preimage hQcont
    have hsub : (fun z : ↥V' => ΨZ z.1) ⁻¹' K
        ⊆ (fun z : ↥V' => q z.1) ⁻¹' ((fun ζ : ℂ => ζ ^ d) '' K) := by
      intro z hz
      change ΨZ z.1 ∈ K at hz
      exact ⟨ΨZ z.1, hz, hΨpow z.1 z.2⟩
    have hcomp : IsCompact ((fun z : ↥V' => ΨZ z.1) ⁻¹' K) := hPK.of_isClosed_subset hcl hsub
    have himg : Subtype.val '' ((fun z : ↥V' => ΨZ z.1) ⁻¹' K) = V' ∩ ΨZ ⁻¹' K := by
      ext z; constructor
      · rintro ⟨z', hz', rfl⟩; exact ⟨z'.2, hz'⟩
      · rintro ⟨hz'V', hz'K⟩; exact ⟨⟨z, hz'V'⟩, hz'K, rfl⟩
    rw [← himg]
    exact hcomp.image continuous_subtype_val
  -- Step 7: the fibre of `0` is the single simple zero `c`
  have hnonlc : ∀ z ∈ A, ¬ ∀ᶠ w in 𝓝 z, ΨZ w = ΨZ z := by
    intro z hzA hcon
    have hcon2 : ∀ᶠ w in 𝓝 z, q w = q z := by
      filter_upwards [hcon, hV'o.mem_nhds hzA.1] with w hw hwV
      calc q w = (ΨZ w) ^ d := (hΨpow w hwV).symm
        _ = (ΨZ z) ^ d := by rw [hw]
        _ = q z := hΨpow z hzA.1
    have hEq : Set.EqOn q (fun _ => q z) V' :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hqdiffOn.analyticOnNhd hV'o)
        analyticOnNhd_const hV'c.isPreconnected hzA.1 hcon2
    have h1 : q z₁ = q z := hEq hz₁V'
    rw [hz₁q] at h1
    have h2 : q z = 0 := hzA.2
    rw [← h1] at h2
    norm_num at h2
  have hballA : ∀ z ∈ A, ∃ δ > 0, Metric.ball z δ ∩ A = {z} := by
    intro z hzA
    have hcl : IsClosed (A \ {z}) := (hAfinA.subset sdiff_subset).isClosed
    obtain ⟨δ, hδ, hδ'⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl z (fun h => h.2 rfl)
    refine ⟨δ, hδ, ?_⟩
    ext w; constructor
    · rintro ⟨hwB, hwA⟩
      by_contra hne
      exact hδ' hwB ⟨hwA, hne⟩
    · rintro hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact ⟨Metric.mem_ball_self hδ, hzA⟩
  have hmap_ball : ∀ z ∈ A, ∀ U ∈ 𝓝 z, ΨZ '' U ∈ 𝓝 0 := by
    intro z hzA U hU
    rcases AnalyticAt.eventually_constant_or_nhds_le_map_nhds (hΨan z hzA.1) with hcon | hle
    · exact absurd hcon (hnonlc z hzA)
    · have h1 : ΨZ '' U ∈ 𝓝 (ΨZ z) :=
        hle (Filter.mem_map.mpr (Filter.mem_of_superset hU (fun w hw => ⟨w, hw, rfl⟩)))
      rwa [hΨ0A z hzA] at h1
  have hcA : c ∈ A := ⟨hc, hqc⟩
  have hAeq : A = {c} := by
    have hsub : A ⊆ {c} := by
      intro z hzA
      rw [Set.mem_singleton_iff]
      by_contra hzc
      have hdist : 0 < ‖z - c‖ := by
        rw [norm_pos_iff]
        exact sub_ne_zero.mpr hzc
      obtain ⟨δz, hδz, hδzA⟩ := hballA z hzA
      obtain ⟨δc, hδc, hδcA⟩ := hballA c hcA
      obtain ⟨δz', hδz', hδz'sub⟩ := Metric.mem_nhds_iff.mp (hV'o.mem_nhds hzA.1)
      obtain ⟨δc', hδc', hδc'sub⟩ := Metric.mem_nhds_iff.mp (hV'o.mem_nhds hc)
      set rz : ℝ := min (min δz δz') (‖z - c‖ / 3) with hrz
      set rc : ℝ := min (min δc δc') (‖z - c‖ / 3) with hrc
      have hrzpos : 0 < rz := lt_min (lt_min hδz hδz') (by positivity)
      have hrcpos : 0 < rc := lt_min (lt_min hδc hδc') (by positivity)
      have hUz : Metric.ball z rz ∈ 𝓝 z := Metric.ball_mem_nhds z hrzpos
      have hUc : Metric.ball c rc ∈ 𝓝 c := Metric.ball_mem_nhds c hrcpos
      obtain ⟨ηz, hηzpos, hηzsub⟩ := Metric.mem_nhds_iff.mp (hmap_ball z hzA _ hUz)
      obtain ⟨ηc, hηcpos, hηcsub⟩ := Metric.mem_nhds_iff.mp (hmap_ball c hcA _ hUc)
      set ζ : ℂ := ((min ηz ηc / 2 : ℝ) : ℂ) with hζ
      have hζpos : 0 < ‖ζ‖ := by
        rw [hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact div_pos (lt_min hηzpos hηcpos) (by norm_num)
      have hζnorm : ‖ζ‖ = min ηz ηc / 2 := by
        rw [hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hminpos : 0 < min ηz ηc := lt_min hηzpos hηcpos
      have hζz : ζ ∈ Metric.ball (0 : ℂ) ηz := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, hζnorm]
        exact lt_of_lt_of_le (div_lt_self hminpos one_lt_two) (min_le_left _ _)
      have hζc : ζ ∈ Metric.ball (0 : ℂ) ηc := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, hζnorm]
        exact lt_of_lt_of_le (div_lt_self hminpos one_lt_two) (min_le_right _ _)
      have hζne : ζ ≠ 0 := by
        intro hζ0
        have h := hζnorm
        rw [hζ0, norm_zero] at h
        linarith [show (0 : ℝ) < min ηz ηc / 2 by positivity]
      obtain ⟨a, haB, haΨ⟩ := hηzsub hζz
      obtain ⟨b, hbB, hbΨ⟩ := hηcsub hζc
      have haV : a ∈ V' := hδz'sub (lt_of_lt_of_le (Metric.mem_ball.mp haB)
        (le_trans (min_le_left _ _) (min_le_right δz δz')))
      have hbV : b ∈ V' := hδc'sub (lt_of_lt_of_le (Metric.mem_ball.mp hbB)
        (le_trans (min_le_left _ _) (min_le_right δc δc')))
      have hrzle : rz ≤ ‖z - c‖ / 3 := min_le_right _ _
      have hrcle : rc ≤ ‖z - c‖ / 3 := min_le_right _ _
      have hdisj : ¬ ∃ p : ℂ, p ∈ Metric.ball z rz ∧ p ∈ Metric.ball c rc := by
        rintro ⟨p, hpz, hpc⟩
        have h2 : dist p z < rz := Metric.mem_ball.mp hpz
        have h3 : dist p c < rc := Metric.mem_ball.mp hpc
        have h6 : dist z c < ‖z - c‖ := by
          calc dist z c ≤ dist z p + dist p c := dist_triangle _ _ _
            _ = dist p z + dist p c := by rw [dist_comm]
            _ < rz + rc := add_lt_add h2 h3
            _ ≤ ‖z - c‖ / 3 + ‖z - c‖ / 3 := add_le_add hrzle hrcle
            _ = 2 * ‖z - c‖ / 3 := by ring
            _ < ‖z - c‖ := by linarith
        rw [dist_eq_norm] at h6
        exact lt_irrefl _ h6
      have hab : a ≠ b := by
        intro h
        exact hdisj ⟨a, haB, h ▸ hbB⟩
      have haA : a ∉ A := fun hA => by
        have h0 : ΨZ a = 0 := hΨ0A a hA
        rw [haΨ] at h0
        exact hζne h0
      have hbA : b ∉ A := fun hA => by
        have h0 : ΨZ b = 0 := hΨ0A b hA
        rw [hbΨ] at h0
        exact hζne h0
      exact hab (hΨZinj a ⟨haV, haA⟩ b ⟨hbV, hbA⟩ (by rw [haΨ, hbΨ]))
    ext z; constructor
    · intro hz; exact hsub hz
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact hcA
  -- Step 8: `deriv ΨZ c ≠ 0` and the degree-one endgame
  have hderivc : deriv ΨZ c ≠ 0 := by
    intro h0
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hV'o.mem_nhds hc)
    obtain ⟨w, hwne, _hwlt, a, b, hab, halt, hblt, hfa, hfb⟩ :=
      Commons.Analysis.Complex.exists_two_preimages_near_of_deriv_eq_zero
        (hΨan c hc) h0 (hnonlc c hcA) hρpos
    have hΨc : ΨZ c = 0 := hΨ0A c hcA
    rw [hΨc] at hwne
    have haV : a ∈ V' := hρsub (by rw [Metric.mem_ball, dist_eq_norm]; exact halt)
    have hbV : b ∈ V' := hρsub (by rw [Metric.mem_ball, dist_eq_norm]; exact hblt)
    have haA : a ∉ A := fun hA => hwne (by rw [← hfa, hΨ0A a hA])
    have hbA : b ∉ A := fun hA => hwne (by rw [← hfb, hΨ0A b hA])
    exact hab (hΨZinj a ⟨haV, haA⟩ b ⟨hbV, hbA⟩ (by rw [hfa, hfb]))
  have hΨdiffOn : DifferentiableOn ℂ ΨZ V' := fun z hz => (hΨan z hz).differentiableWithinAt
  have hfib : ∀ z ∈ V', ΨZ z = 0 ↔ z = c := by
    intro z hz
    constructor
    · intro hz0
      have hzA : z ∈ A := ⟨hz, by rw [← hΨpow z hz, hz0, zero_pow hd.ne']⟩
      rwa [hAeq] at hzA
    · intro hz
      rw [hz]
      exact hΨ0A c hcA
  obtain ⟨e⟩ := homeomorph_ball_single_zero hV'o hV'c hΨdiffOn hΨmaps hΨprop hc hfib hderivc
  exact Work.BasinSC.simplyConnectedSpace_of_homeomorph
    (e.trans (Homeomorph.unitBall.symm : ↥(Metric.ball (0 : ℂ) 1) ≃ₜ ℂ))
end Work.BasinSC.StepOneCrit
