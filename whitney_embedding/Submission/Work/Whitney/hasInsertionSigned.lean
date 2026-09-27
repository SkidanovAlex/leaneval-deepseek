import Mathlib
import Submission.Work.Whitney.InsertSigned
import Submission.Work.Whitney.hasInsertionNF
import Submission.Work.Whitney.exists_oppositeType_of_insertion
import Submission.Work.Whitney.pairDet_ne_zero_iff

/-!
# The signed insertion step: `Work.Whitney.HasInsertionSigned`

The signing of the compact branch of Whitney's strong embedding theorem requires more from the
insertion step than the atlas-free `Work.Whitney.HasInsertionNF`: the inserted partner double point
must be of the *opposite type* to the pre-existing one along the arcs the endgame will use
(`Work.Whitney.OppositeType`).  The insertion construction already produces **two** candidate maps
`fp`, `fm`, obtained by gluing the same model double point at a clean point and differing by an
orientation-reversing isometry of the model (`Work.Whitney.exists_addDoublePoint_both_signs_located`,
via the reflection `Work.Whitney.exists_reflection_det_neg`): they insert the *same* double point
`(p', q')` with *opposite* nonzero signs read in the gluing chart.

This file repeats the proof of `Work.Whitney.hasInsertionNF` keeping *both* candidates (the proof of
`Work.Whitney.exists_insertedDP_NF` discards `fm` at the very end), and then feeds the two candidates
into the proved sign count `Work.Whitney.exists_oppositeType_of_insertion`: for every pair of
continuous arcs `γ₁ : p₁ → p'`, `γ₂ : p₂ → q'`, one of `fp`, `fm` (indeed the one whose sign product
along the arcs is negative) makes `(p₁,p₂)` and `(p',q')` opposite-typed.

## Main results

* `Work.Whitney.exists_insertedDP_signed` — the insertion, signed: two candidates with the full
  `InsertedDP`/`SimpleDP`/`TransDP'` structure and the `OppositeType` alternative along any arcs.
* `Work.Whitney.hasInsertionSigned` — the interface `Work.Whitney.HasInsertionSigned` of the target.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

set_option maxHeartbeats 1000000

/-- **The insertion step, signed.**  A simple transverse double point of a smooth immersion of a
compact manifold with finitely many simple transverse double points can be supplemented by a freshly
inserted double point, preserving simplicity and transversality (the latter certified by smooth
charts) — and this in **two ways** `fp`, `fm` inserting the same double point `(p', q')` with
opposite signs, one of which is of opposite type along any prescribed pair of arcs `γ₁ : p₁ → p'`,
`γ₂ : p₂ → q'`. -/
theorem exists_insertedDP_signed {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (hfin : (doubleSet f).Finite)
    (hsimple : SimpleDP f) (htrans : TransDP' f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂) :
    ∃ (fp fm : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      InsertedDP f p₁ p₂ fp p' q' ∧ SimpleDP fp ∧ TransDP' fp ∧
      InsertedDP f p₁ p₂ fm p' q' ∧ SimpleDP fm ∧ TransDP' fm ∧
      (∀ (γ₁ γ₂ : ℝ → M), Continuous γ₁ → Continuous γ₂ →
        γ₁ 0 = p₁ → γ₁ 1 = p' → γ₂ 0 = p₂ → γ₂ 1 = q' →
        Work.Whitney.OppositeType fp γ₁ γ₂ p₁ p₂ p' q' ∨
          Work.Whitney.OppositeType fm γ₁ γ₂ p₁ p₂ p' q') := by
  classical
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  -- ### the finite set of double point preimages
  let D : Set M := {y : M | ∃ w : M, w ≠ y ∧ f w = f y}
  have hDfin : D.Finite := by
    have h : D = Prod.fst '' doubleSet f := by
      ext y
      constructor
      · rintro ⟨w, hwy, hfw⟩
        exact ⟨(y, w), ⟨hwy.symm, hfw.symm⟩, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q.2, hq.1.symm, hq.2.symm⟩
    rw [h]; exact hfin.image _
  have hDclosed : IsClosed D := hDfin.isClosed
  -- ### a clean point and a chart around it
  obtain ⟨z, c₀, -, hc₀src, h0c₀, hc₀z, -, hc₀sm, hc₀inv, hclean_z⟩ :=
    exists_clean_point_and_chart (n := n) (by omega) f hfin p₁ Set.univ Filter.univ_mem
  have hzsrc : z ∈ c₀.source := by rw [hc₀src]; exact mem_chart_source _ _
  have hzD : z ∉ D := by
    rintro ⟨w, hwz, hfw⟩
    exact hclean_z w z hwz hfw hfw.symm
  have hsymm0 : c₀.symm 0 = z := by rw [← hc₀z]; exact c₀.left_inv hzsrc
  -- ### the clean ball around `z`
  have hclean0 : ∀ y w : M, y ≠ w → f y = f w → f (c₀.symm 0) ≠ f y := by
    intro y w hyw hfyw
    rw [hsymm0]
    exact hclean_z y w hyw hfyw
  obtain ⟨c₁, R₀, η₀, hR₀, hη₀, hc₁src, hc₁tgt, hc₁eq, hc₁symm, hball₀, hsrc₀, hinj₀, hsep₀⟩ :=
    exists_clean_ball f hf himm c₀ h0c₀ hc₀sm hc₀inv hclean0
  have hzsrc₁ : z ∈ c₁.source := by rw [hc₁src]; exact hzsrc
  have hc₁z : c₁ z = 0 := by rw [hc₁eq z hzsrc]; exact hc₀z
  have h0c₁ : (0 : EuclideanSpace ℝ (Fin n)) ∈ c₁.target := by
    rw [hc₁tgt]; exact h0c₀
  have hsymm0₁ : c₁.symm 0 = z := by rw [← hc₁z]; exact c₁.left_inv hzsrc₁
  have hc₁sm : ∀ y : M, y ∈ c₁.source → ContMDiffAt (𝓡 n) (𝓡 n) ∞ c₁ y := by
    intro y hy
    have hy₀ : y ∈ c₀.source := by rwa [hc₁src] at hy
    refine (hc₀sm y hy₀).congr_of_eventuallyEq ?_
    filter_upwards [(c₀.open_source).mem_nhds hy₀] with w hw
    rw [hc₁eq w hw]
  have hc₁inv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c₁.target → ContMDiffAt (𝓡 n) (𝓡 n) ∞ c₁.symm u := by
    intro u hu
    have hu₀ : u ∈ c₀.target := by rwa [hc₁tgt] at hu
    refine (hc₀inv u hu₀).congr_of_eventuallyEq ?_
    filter_upwards [(c₀.open_target).mem_nhds hu₀] with w hw
    rw [hc₁symm w hw]
  -- ### a neighbourhood of `z` whose closure avoids the double point preimages
  have hc₀tgt_open : IsOpen c₀.target := c₀.open_target
  let F : Set (EuclideanSpace ℝ (Fin n)) := c₀ '' (D ∩ c₀.source)
  have hFfin : F.Finite := (hDfin.subset Set.inter_subset_left).image _
  have h0F : (0 : EuclideanSpace ℝ (Fin n)) ∉ F := by
    rintro ⟨y, ⟨hyD, hysrc⟩, hy0⟩
    have hyz : y = z := c₀.injOn hysrc hzsrc (by rw [hy0, hc₀z])
    exact hzD (hyz ▸ hyD)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hFfin.isClosed.isOpen_compl 0 h0F
  obtain ⟨ε', hε'pos, hε'sub⟩ := Metric.isOpen_iff.mp hc₀tgt_open 0 h0c₀
  set τ : ℝ := min (ε / 2) (ε' / 2) with hτdef
  have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
  have hτle_ε : τ ≤ ε / 2 := min_le_left _ _
  have hτle_ε' : τ ≤ ε' / 2 := min_le_right _ _
  have hτball : Metric.ball 0 τ ⊆ c₀.target :=
    fun u hu => hε'sub (Metric.closedBall_subset_ball (by linarith) (Metric.ball_subset_closedBall hu))
  have hτclosed : Metric.closedBall 0 τ ⊆ c₀.target := by
    intro u hu
    exact hε'sub (Metric.closedBall_subset_ball (by linarith) hu)
  have hτF : Metric.closedBall 0 τ ⊆ Fᶜ := by
    intro u hu
    exact hεsub (Metric.closedBall_subset_ball (by linarith) hu)
  have hWopen : IsOpen (c₀.symm '' Metric.ball 0 τ ∩ c₁.source) :=
    (c₀.isOpen_image_symm_of_subset_target Metric.isOpen_ball hτball).inter (c₁.open_source)
  have hzW : z ∈ c₀.symm '' Metric.ball 0 τ ∩ c₁.source := by
    refine ⟨⟨0, ?_, ?_⟩, hzsrc₁⟩
    · rw [Metric.mem_ball, dist_zero_right]; simpa using hτpos
    · rw [hsymm0]
  have hclosedImg : IsClosed (c₀.symm '' Metric.closedBall 0 τ) :=
    (IsCompact.image_of_continuousOn (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) τ)
      ((c₀.continuousOn_symm).mono hτclosed)).isClosed
  have hclW : closure (c₀.symm '' Metric.ball 0 τ ∩ c₁.source) ⊆ c₀.symm '' Metric.closedBall 0 τ := by
    refine closure_minimal ?_ hclosedImg
    rintro y ⟨⟨u, hu, rfl⟩, -⟩
    exact ⟨u, Metric.ball_subset_closedBall hu, rfl⟩
  have hmeet : ∀ a : M, a ∈ D → a ∉ closure (c₀.symm '' Metric.ball 0 τ ∩ c₁.source) := by
    intro a ha hacl
    obtain ⟨u, hu, hueq⟩ := hclW hacl
    have hsrc : a ∈ c₀.source := by rw [← hueq]; exact c₀.map_target (hτclosed hu)
    have hFa : u ∈ F := ⟨a, ⟨ha, hsrc⟩, by rw [← hueq]; exact c₀.right_inv (hτclosed hu)⟩
    exact (hτF hu) hFa
  -- ### the gluing chart
  set W : Set M := c₀.symm '' Metric.ball 0 τ ∩ c₁.source with hWdef
  set ψ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ (3 * R₀ + 1) with hψdef
  have hψnorm : ‖ψ‖ = 3 * R₀ + 1 := by
    rw [hψdef, EuclideanSpace.norm_single, Real.norm_of_nonneg (by linarith)]
  have hψgt : 3 * R₀ < ‖ψ‖ := by rw [hψnorm]; linarith
  obtain ⟨cc, r, hrpos, hrball, hcctgt, hccsrc, hccsubW, hzcc, hccz, hcceq, hccjunk, hccsm, hccinv⟩ :=
    exists_gluing_chart_open c₁ h0c₁ hc₁sm hc₁inv (c₀.symm '' Metric.ball 0 τ ∩ c₁.source)
      hWopen (by rw [hsymm0₁]; exact hzW) Set.inter_subset_right ψ
  have hWsub : c₀.symm '' Metric.ball 0 τ ∩ c₁.source ⊆ c₁.source := Set.inter_subset_right
  have hzcc' : z ∈ cc.source := by rw [← hsymm0₁]; exact hzcc
  have hccz' : cc z = 0 := by rw [← hsymm0₁]; exact hccz
  have h0cc : (0 : EuclideanSpace ℝ (Fin n)) ∈ cc.target := by
    rw [hcctgt, Metric.mem_ball, dist_zero_right, norm_zero]
    linarith [hrpos]
  -- ### tubular data for the gluing chart
  obtain ⟨H, ρt, L, hρt, hL, hHc, hHaxis, hHinj, hHimm, hHLip⟩ :=
    exists_tubular_data_smooth f hf himm cc h0cc hccsm hccinv
  -- ### the separating radius (only the avoidance of the double point preimages is needed)
  have hnhdsD : (Dᶜ : Set M) ∈ 𝓝 z := IsClosed.compl_mem_nhds hDclosed hzD
  have hcont_symm : ContinuousAt (cc.symm : EuclideanSpace ℝ (Fin n) → M) 0 := (hccinv 0).continuousAt
  have hsymm0cc : cc.symm 0 = z := by rw [← hccz']; exact cc.left_inv hzcc'
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := Metric.mem_nhds_iff.mp
    (hcont_symm.preimage_mem_nhds (by rw [hsymm0cc]; exact hnhdsD))
  -- ### the description of the gluing chart's source
  have hchar : ∀ y : M, y ∈ W → (y ∈ cc.source ↔ ‖c₁ y‖ < r / 2) := by
    intro y hyW
    have hy : y ∈ c₁.source := Set.inter_subset_right hyW
    constructor
    · intro hyc
      rw [hccsrc] at hyc
      obtain ⟨u, hu, hueq⟩ := hyc
      have hu' : u ∈ Metric.ball 0 r := Metric.ball_subset_ball (by linarith) hu
      have hcu : c₁ y = u := by rw [← hueq]; exact c₁.right_inv (hrball hu')
      rw [hcu]
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
    · intro hyb
      rw [hccsrc]
      refine ⟨c₁ y, ?_, c₁.left_inv hy⟩
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hinC : ∀ y : M, y ∈ W → ‖c₁ y‖ < r / 2 → y ∈ cc.source :=
    fun y hyW hy => (hchar y hyW).mpr hy
  have hcceqW : ∀ y : M, y ∈ W → cc y = c₁ y := fun y hyW => hcceq y hyW
  set ρ : ℝ := min ρ₁ (min (3 * R₀ + 1) (r / 2)) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₁pos (lt_min (by linarith) (by linarith))
  have hρψ : ρ ≤ ‖ψ‖ := by
    rw [hψnorm]
    linarith [min_le_left (3 * R₀ + 1) (r / 2), min_le_right ρ₁ (min (3 * R₀ + 1) (r / 2))]
  have hρτ : ρ ≤ r / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hsubρ : ∀ y : M, ‖cc y‖ < ρ → y ∉ D := by
    intro y hy
    have hyW : y ∈ W := by
      by_contra hnotW
      have h1 : ‖cc y‖ = ‖ψ‖ := by rw [hccjunk y hnotW, hψnorm]
      linarith [hρψ]
    have hyc : y ∈ cc.source :=
      hinC y hyW (by rw [← hcceqW y hyW]; exact lt_of_lt_of_le hy hρτ)
    have hylt : ‖cc y‖ < ρ₁ := lt_of_lt_of_le hy (min_le_left _ _)
    have hmem : cc.symm (cc y) ∈ Dᶜ :=
      hρ₁sub (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hylt)
    have hyeq : cc.symm (cc y) = y := cc.left_inv hyc
    rwa [hyeq] at hmem
  have hDρ : ∀ a : M, a ∈ D → ρ ≤ ‖cc a‖ := fun a ha =>
    le_of_not_gt (fun h => hsubρ a h ha)
  -- ### the insertion radius
  set R : ℝ := min R₀ (min (ρ / 3) (min (ρt / 4) (r / 8))) with hRdef
  have hRpos : 0 < R := lt_min hR₀ (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  have hRR₀ : R ≤ R₀ := min_le_left _ _
  have h3Rρ : 3 * R ≤ ρ := by
    have h : R ≤ ρ / 3 := le_trans (min_le_right _ _) (min_le_left _ _); linarith
  have hRρt : R ≤ ρt / 4 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRr : R ≤ r / 8 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h3Rr : 3 * R < r / 2 := by linarith
  have h3RR₀ : 3 * R ≤ 3 * R₀ := by linarith
  -- ### the clean data at the insertion radius
  obtain ⟨η, hηpos, hclean₂, hsep₂⟩ :=
    exists_clean_data_shrink f hf.continuous c₁ R₀ η₀ hR₀ hη₀ hsrc₀ hball₀ hinj₀ hsep₀ R hRpos hRR₀
  -- ### transfer to the gluing chart
  have hsrc_cc : ∀ y : M, ‖cc y‖ ≤ 3 * R → y ∈ cc.source := by
    intro y hy
    have hyW : y ∈ W := by
      by_contra hnotW
      have h1 : ‖cc y‖ = ‖ψ‖ := by rw [hccjunk y hnotW, hψnorm]
      linarith [hψgt, hy, h3RR₀]
    exact hinC y hyW (by rw [← hcceqW y hyW]; linarith [hy, h3Rr])
  have hclean_cc : ∀ y : M, ‖cc y‖ < R → ∀ z : M, f y = f z → z = y := by
    intro y hy z hz
    have hysrc : y ∈ cc.source := hsrc_cc y (le_of_lt (by linarith))
    have hy₁ : ‖c₁ y‖ < R := by rw [← hcceq y (hccsubW hysrc)]; exact hy
    exact hclean₂ y hy₁ z hz
  have hsep_cc : ∀ y z : M, ‖cc y‖ < R → 2 * R ≤ ‖cc z‖ → f y ≠ f z → η ≤ ‖f y - f z‖ := by
    intro y z hy hz hne
    have hysrc : y ∈ cc.source := hsrc_cc y (le_of_lt (by linarith))
    have hy₁ : ‖c₁ y‖ < R := by rw [← hcceq y (hccsubW hysrc)]; exact hy
    have hz₁ : 2 * R ≤ ‖c₁ z‖ := by
      by_cases hzW : z ∈ c₀.symm '' Metric.ball 0 τ ∩ c₁.source
      · rw [← hcceq z hzW]; exact hz
      · have hzs : z ∉ cc.source := fun h => hzW (hccsubW h)
        by_cases hzs₁ : z ∈ c₁.source
        · have hge : r / 2 ≤ ‖c₁ z‖ := by
            by_contra hlt
            have hzc : z ∈ cc.source := by
              rw [hccsrc]
              exact ⟨c₁ z, by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact not_le.mp hlt,
                c₁.left_inv hzs₁⟩
            exact hzW (hccsubW hzc)
          linarith
        · have hbig : ¬ (‖c₁ z‖ ≤ 3 * R₀) := fun h => hzs₁ (hsrc₀ z h)
          linarith
    exact hsep₂ y z hy₁ hz₁ hne
  have hball_cc : Metric.ball 0 (3 * R) ⊆ cc.target := by
    rw [hcctgt]
    exact Metric.ball_subset_ball (le_of_lt h3Rr)
  -- ### the modification is the identity near every double point preimage
  have hgerm : ∀ a : M, a ∈ D → ∀ᶠ y in 𝓝 a, R ≤ ‖cc y‖ := by
    intro a ha
    have hmem : (closure (c₀.symm '' Metric.ball 0 τ ∩ c₁.source))ᶜ ∈ 𝓝 a :=
      IsClosed.compl_mem_nhds isClosed_closure (hmeet a ha)
    filter_upwards [hmem] with y hy
    have hyW : y ∉ c₀.symm '' Metric.ball 0 τ ∩ c₁.source := fun h => hy (subset_closure h)
    have h1 : ‖cc y‖ = ‖ψ‖ := by rw [hccjunk y hyW, hψnorm]
    linarith [hψgt, h3RR₀, hRpos]
  have hgemm : ∀ (g : M → EuclideanSpace ℝ (Fin (2 * n))),
      (∀ y : M, R ≤ ‖cc y‖ → g y = f y) → ∀ a : M, a ∈ D → f =ᶠ[𝓝 a] g :=
    fun g hout a ha => (hgerm a ha).mono (fun y hy => (hout y hy).symm)
  -- ### the located insertion
  have hUopen : IsOpen {y : M | ‖cc y‖ < 3 * R} := by
    have hset : {y : M | ‖cc y‖ < 3 * R} = cc.source ∩ cc ⁻¹' Metric.ball 0 (3 * R) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball,
        dist_eq_norm, sub_zero]
      constructor
      · intro hy; exact ⟨hsrc_cc y (le_of_lt hy), hy⟩
      · intro h; exact h.2
    rw [hset]
    exact (cc.continuousOn).isOpen_inter_preimage (cc.open_source) Metric.isOpen_ball
  have h0U : cc.symm 0 ∈ {y : M | ‖cc y‖ < 3 * R} := by
    show ‖cc (cc.symm 0)‖ < 3 * R
    rw [cc.right_inv h0cc, norm_zero]; linarith
  have hUsub : {y : M | ‖cc y‖ < 3 * R} ⊆ cc.source := fun y hy => hsrc_cc y (le_of_lt hy)
  have hballU : Metric.ball 0 (3 * R) ⊆ cc '' {y : M | ‖cc y‖ < 3 * R} := by
    intro u hu
    refine ⟨cc.symm u, ?_, cc.right_inv (hball_cc hu)⟩
    show ‖cc (cc.symm u)‖ < 3 * R
    rw [cc.right_inv (hball_cc hu)]
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
  -- ### the model deviation
  have h2Rρt : 2 * R < ρt := by linarith
  have hδex : ∃ δ : ℝ, 0 < δ ∧ L * δ < η ∧ 2 * R + δ ≤ ρt := by
    refine ⟨min (η / (2 * L)) ((ρt - 2 * R) / 2), ?_, ?_, ?_⟩
    · exact lt_min (by positivity) (by linarith)
    · have h2 : L * (η / (2 * L)) = η / 2 := by field_simp
      have hle : L * min (η / (2 * L)) ((ρt - 2 * R) / 2) ≤ L * (η / (2 * L)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hL)
      linarith
    · have hle : min (η / (2 * L)) ((ρt - 2 * R) / 2) ≤ (ρt - 2 * R) / 2 := min_le_right _ _
      linarith
  obtain ⟨δ, hδpos, hδLη, hδR⟩ := hδex
  obtain ⟨βp, βm, a, b, hab, haR, hbR, hβpc, hβmc, hβpimm, hβmimm, hβpR, hβmR, hβpδ, hβmδ,
    hβpact, hβmact, hβpab, hβmab, hβpuniq, hβmuniq, hβpdet, hβmdet⟩ :=
      exists_bump_model_pair_smooth_scaled n δ R hδpos hRpos
  -- ### the two insertion variants
  obtain ⟨fp, fm, p', q', hfp_sm, hfm_sm, hfp_imm, hfm_imm, hfp_out, hfm_out, hp'lt, hq'lt,
    hfp_ds, hfm_ds, hfp_detC, hflip_c⟩ :=
    exists_addDoublePoint_both_signs_located hn f hf himm cc h0cc hccsm (fun u _ => hccinv u)
      {y : M | ‖cc y‖ < 3 * R} hUopen h0U hUsub H hHc hHaxis ρt L hρt hL hHinj hHimm hHLip
      βp hβpc hβpimm a b hab hβpab hβpuniq R δ η hRpos hδpos hηpos hβpact hβpR hβpδ hβpdet
      haR hbR hδR hδLη hballU (fun y hy => hsrc_cc y (le_of_lt hy)) hclean_cc hsep_cc
  -- ### the inserted points and the relevant memberships
  have hp'src : p' ∈ cc.source := hsrc_cc p' (le_of_lt (by linarith))
  have hq'src : q' ∈ cc.source := hsrc_cc q' (le_of_lt (by linarith))
  have hp₁D : p₁ ∈ D := ⟨p₂, hp₁p₂.symm, hfp.symm⟩
  have hp₂D : p₂ ∈ D := ⟨p₁, hp₁p₂, hfp⟩
  -- ### the gluing chart is a smooth chart
  have hcc_chart : IsSmoothChart cc :=
    ⟨fun y hy => (hccsm y hy).contMDiffWithinAt, fun u _ => (hccinv u).contMDiffWithinAt⟩
  -- ### the assembly
  have key : ∀ (g : M → EuclideanSpace ℝ (Fin (2 * n))),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g →
      (∀ z : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g z)) →
      (∀ y : M, R ≤ ‖cc y‖ → g y = f y) →
      doubleSet g = doubleSet f ∪ {(p', q'), (q', p')} →
      doubleDetC g cc p' q' ≠ 0 →
      InsertedDP f p₁ p₂ g p' q' ∧ SimpleDP g ∧ TransDP' g := by
    intro g hg_sm hg_imm hg_out hg_ds hg_detC
    have hmemP' : (p', q') ∈ doubleSet g := by rw [hg_ds]; exact Or.inr (by simp)
    have hp'q' : p' ≠ q' := (mem_doubleSet.mp hmemP').1
    have hsimpleNew := simple_of_inserted f g cc R p' q' hp'q' hp'lt hq'lt hg_out hclean_cc hg_ds
    have hgemm_g : ∀ a : M, a ∈ D → f =ᶠ[𝓝 a] g := hgemm g hg_out
    have hpre : ∀ z : M, f z = f p₁ → z = p₁ ∨ z = p₂ :=
      fun z hz => hsimple (p₁, p₂) (by rw [mem_doubleSet]; exact ⟨hp₁p₂, hfp⟩) z hz
    have hR₁ : R < ‖cc p₁‖ := by linarith [hDρ p₁ hp₁D, hRpos]
    have hR₂ : R < ‖cc p₂‖ := by linarith [hDρ p₂ hp₂D, hRpos]
    have hsimpleOld := simple_transported f g cc R p₁ p₂ p' q' hRpos hp'lt hq'lt hR₁ hR₂ hpre hfp hg_ds
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨hg_sm, hg_imm, hg_ds, ?_, hsimpleNew.1, hsimpleOld, ?_, ?_⟩
      · rw [hg_ds]; exact hfin.union (by simp)
      · refine ⟨hp'q', ?_, ?_, ?_, ?_, hp₁p₂⟩
        · intro h; rw [h] at hp'lt; linarith
        · intro h; rw [h] at hp'lt; linarith
        · intro h; rw [h] at hq'lt; linarith
        · intro h; rw [h] at hq'lt; linarith
      · intro hmem
        have h1 : f p' = f q' := (mem_doubleSet.mp hmem).2
        exact hp'q' (hclean_cc p' hp'lt q' h1).symm
    · intro p hp z hz
      rw [hg_ds] at hp
      rcases hp with hpold | hpnew
      · have hfp12 : f p.1 = f p.2 := (mem_doubleSet.mp hpold).2
        have hpne : p.1 ≠ p.2 := (mem_doubleSet.mp hpold).1
        by_cases hzp : z = p.1
        · exact Or.inl hzp
        · have hmem : (z, p.1) ∈ doubleSet g := by rw [mem_doubleSet]; exact ⟨hzp, hz⟩
          rw [hg_ds] at hmem
          rcases hmem with hmem | hmem
          · have hfz : f z = f p.1 := (mem_doubleSet.mp hmem).2
            have hmem' : (p.1, z) ∈ doubleSet f := by
              rw [mem_doubleSet]; exact ⟨fun h => hzp h.symm, hfz.symm⟩
            have h1 : p.2 = p.1 ∨ p.2 = z := hsimple (p.1, z) hmem' p.2 hfp12.symm
            rcases h1 with h1 | h1
            · exact absurd h1.symm hpne
            · exact Or.inr h1.symm
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨hz', hp1'⟩ | ⟨hz', hp1'⟩
            · exfalso
              have hfq : f q' = f p.2 := by rw [← hp1']; exact hfp12
              have hne : f q' ≠ f p.2 := fun heq =>
                hpne (by rw [hp1', hclean_cc q' hq'lt p.2 heq])
              exact hne hfq
            · exfalso
              have hfq : f p' = f p.2 := by rw [← hp1']; exact hfp12
              have hne : f p' ≠ f p.2 := fun heq =>
                hpne (by rw [hp1', hclean_cc p' hp'lt p.2 heq])
              exact hne hfq
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpnew
        rcases hpnew with hpnew | hpnew
        · have hp1 : p.1 = p' := by rw [hpnew]
          have hp2 : p.2 = q' := by rw [hpnew]
          have hz' : g z = g p' := by rw [← hp1]; exact hz
          rcases hsimpleNew.1 z hz' with h1 | h1
          · exact Or.inl (by rw [h1, hp1])
          · exact Or.inr (by rw [h1, hp2])
        · have hp1 : p.1 = q' := by rw [hpnew]
          have hp2 : p.2 = p' := by rw [hpnew]
          have hz' : g z = g q' := by rw [← hp1]; exact hz
          rcases hsimpleNew.2 z hz' with h1 | h1
          · exact Or.inl (by rw [h1, hp1])
          · exact Or.inr (by rw [h1, hp2])
    · intro p hp
      rw [hg_ds] at hp
      rcases hp with hpold | hpnew
      · obtain ⟨e₁, e₂, he₁, he₂, hpe₁, hpe₂, hpe⟩ := htrans p hpold
        have hpq₁ : p.1 ∈ D := ⟨p.2, (mem_doubleSet.mp hpold).1.symm, (mem_doubleSet.mp hpold).2.symm⟩
        have hpq₂ : p.2 ∈ D := ⟨p.1, (mem_doubleSet.mp hpold).1, (mem_doubleSet.mp hpold).2⟩
        refine ⟨e₁, e₂, he₁, he₂, hpe₁, hpe₂, ?_⟩
        rw [← pairDet_congr e₁ e₂ p.1 p.2 hpe₁ hpe₂ (hgemm_g p.1 hpq₁) (hgemm_g p.2 hpq₂)]
        exact hpe
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpnew
        rcases hpnew with hpnew | hpnew
        · have hp1 : p.1 = p' := by rw [hpnew]
          have hp2 : p.2 = q' := by rw [hpnew]
          refine ⟨cc, cc, hcc_chart, hcc_chart, ?_, ?_, ?_⟩
          · rw [hp1]; exact hp'src
          · rw [hp2]; exact hq'src
          · rw [hp1, hp2]
            show doubleDetC g cc p' q' ≠ 0
            exact hg_detC
        · have hp1 : p.1 = q' := by rw [hpnew]
          have hp2 : p.2 = p' := by rw [hpnew]
          refine ⟨cc, cc, hcc_chart, hcc_chart, ?_, ?_, ?_⟩
          · rw [hp1]; exact hq'src
          · rw [hp2]; exact hp'src
          · rw [hp1, hp2]
            show doubleDetC g cc q' p' ≠ 0
            have h1 : doubleDetRep (fun u : EuclideanSpace ℝ (Fin n) => g (cc.symm u))
                (cc p') (cc q') ≠ 0 := hg_detC
            have h2 : doubleDetRep (fun u : EuclideanSpace ℝ (Fin n) => g (cc.symm u))
                (cc q') (cc p') ≠ 0 := by
              rw [doubleDetRep_ne_zero_iff] at h1 ⊢
              rwa [sup_comm]
            exact h2
  obtain ⟨hI_fp, hS_fp, hT_fp⟩ := key fp hfp_sm hfp_imm hfp_out hfp_ds hfp_detC
  have hfm_detC : doubleDetC fm cc p' q' ≠ 0 := by
    rw [hflip_c]; exact neg_ne_zero.mpr hfp_detC
  obtain ⟨hI_fm, hS_fm, hT_fm⟩ := key fm hfm_sm hfm_imm hfm_out hfm_ds hfm_detC
  -- ### the two candidates insert the same double point `(p', q')`
  have hfp' : fp p' = fp q' := by
    have hmem : (p', q') ∈ doubleSet fp := by
      rw [hI_fp.doubleSet_eq]; exact Or.inr (by simp)
    exact (mem_doubleSet.mp hmem).2
  have hfm' : fm p' = fm q' := by
    have hmem : (p', q') ∈ doubleSet fm := by
      rw [hI_fm.doubleSet_eq]; exact Or.inr (by simp)
    exact (mem_doubleSet.mp hmem).2
  have hp'q' : p' ≠ q' := hI_fp.distinct.1
  -- ### the pre-existing double point `(p₁,p₂)` is transverse
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hspan : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤ := by
    have hmemOld : (p₁, p₂) ∈ doubleSet f := by
      rw [mem_doubleSet]; exact ⟨hp₁p₂, hfp⟩
    obtain ⟨e₁, e₂, he₁, he₂, hpe₁, hpe₂, hpedet⟩ := htrans (p₁, p₂) hmemOld
    refine (pairDet_ne_zero_iff f e₁ e₂ p₁ p₂ hpe₁ hpe₂ ?_ ?_ ?_ ?_ ?_ ?_).mp hpedet
    · exact (he₁.1.contMDiffAt (e₁.open_source.mem_nhds hpe₁)).mdifferentiableAt htop
    · exact (he₂.1.contMDiffAt (e₂.open_source.mem_nhds hpe₂)).mdifferentiableAt htop
    · exact (he₁.2.contMDiffAt (e₁.open_target.mem_nhds (e₁.map_source hpe₁))).mdifferentiableAt htop
    · exact (he₂.2.contMDiffAt (e₂.open_target.mem_nhds (e₂.map_source hpe₂))).mdifferentiableAt htop
    · exact (hf p₁).mdifferentiableAt htop
    · exact (hf p₂).mdifferentiableAt htop
  refine ⟨fp, fm, p', q', hI_fp, hS_fp, hT_fp, hI_fm, hS_fm, hT_fm, ?_⟩
  -- ### the sign count: for every pair of arcs one of the two candidates is opposite-typed
  intro γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
  exact exists_oppositeType_of_insertion (f := f) (fp := fp) (fm := fm) (p₁ := p₁) (p₂ := p₂)
    (p' := p') (q' := q') (c := cc) (γ₁ := γ₁) (γ₂ := γ₂)
    hf hfp_sm hfm_sm hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hcc_chart hp'src hq'src hp₁p₂ hp'q'
    hfp' hfm' (hgemm fp hfp_out p₁ hp₁D).symm (hgemm fp hfp_out p₂ hp₂D).symm
    (hgemm fm hfm_out p₁ hp₁D).symm (hgemm fm hfm_out p₂ hp₂D).symm
    hspan hfp_detC hflip_c

/-- **The signed insertion interface.**  The insertion supplies two candidates `fp`, `fm` inserting
one and the same partner double point `(p', q')`, with the full `InsertedDP`/`SimpleDP`/`TransDP'`
structure, such that for every pair of arcs from `p₁`, `p₂` to `p'`, `q'` one of the two is of
opposite type along those arcs. -/
theorem hasInsertionSigned {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] :
    Work.Whitney.HasInsertionSigned n M := by
  intro f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp
  exact exists_insertedDP_signed hn f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp

end Work.Whitney
