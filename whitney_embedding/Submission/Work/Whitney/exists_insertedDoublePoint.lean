import Mathlib
import Submission.Work.Whitney.InsertedDoublePoint
import Submission.Work.Whitney.reduce_double_points_abstract
import Submission.Work.Whitney.exists_clean_point_and_chart
import Submission.Work.Whitney.exists_gluing_chart_open
import Submission.Work.Whitney.insert_double_point_oriented
import Submission.Work.Whitney.clean_data_shrink
import Submission.Work.Whitney.exists_tubular_data_smooth
import Submission.Work.Whitney.exists_bump_model_pair_smooth_scaled
import Submission.Work.Whitney.exists_addDoublePoint_both_signs_located
import Submission.Work.Whitney.fderiv_transition_det_ne_zero
import Submission.Work.Whitney.SignCompare
import Submission.Work.Whitney.doubleDetC_untouched
import Submission.Work.Whitney.EndgameAux

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology Filter

set_option maxHeartbeats 1000000

-- INSTANTIATION OF `Work.Whitney.HasInsertion` (see reduce_double_points_abstract.lean), i.e. the
-- insertion step of Whitney's endgame together with the preservation of the two global invariants
-- `SimpleDP` and `TransDP`.
--
-- An earlier attempt at this path was declared FALSE with the (correct) objection that
-- `Work.Whitney.IsOrientedAtlas A` alone does not force the charts of `A` to be compatible with
-- the smooth structure (`x ↦ x³` on `ℝ` is such a "chart"), so the `pairDet`-based sign
-- statements could be meaningless.  That is why the hypothesis here is the stronger
-- `Work.Whitney.IsSmoothOrientedAtlas A` (an oriented atlas of genuine smooth charts, both
-- directions smooth), which is exactly what the construction needs.
--
-- Route (all lemmas below are proved and sorry-free in this workspace; import what you need):
--  * `Work.Whitney.exists_clean_point_and_chart`: a clean point `z` and a chart-like `c₀` centred
--    at `z`.  Pass the neighbourhood `V = Dᶜ`, where `D = {y | ∃ z ≠ y, f z = f y}` is the finite
--    set of double point preimages of `f` (`hfin`); then `z ∉ D`.
--  * `Work.Whitney.exists_chart_globally_smooth_symm`: shrink `c₀` to `c₁` whose `symm` is smooth
--    everywhere.
--  * `Work.Whitney.exists_clean_ball` + `Work.Whitney.exists_clean_data_shrink`: a junk-controlled
--    chart `c'`, a radius `R > 0` and a separation constant `η`, with the clean conditions at
--    radius `R`.  Shrink `R` further so that `‖c' y‖ > R` for every `y ∈ D` (equivalently: the ball
--    `{y | ‖c' y‖ < 3R}` avoids `D`, which holds for small `R` because `z ∉ D` and `D` is finite).
--    This makes `f' =ᶠ[𝓝 y] f` at every double point preimage `y` of `f`, hence
--    `pairDet f' = pairDet f` there by `Work.Whitney.pairDet_congr`.
--  * `Work.Whitney.exists_tubular_data_smooth`: `H, ρ, L`.
--  * `Work.Whitney.exists_bump_model_pair_smooth_scaled`: the model `β` and its double point
--    `(a,b)` with independent support radius `R` and deviation `δ`; choose `δ > 0` with
--    `L * δ < η` and `2 * R + δ ≤ ρ`.
--  * `Work.Whitney.exists_addDoublePoint_oriented` (file `insert_double_point_oriented.lean`): the
--    insertion.  Take for `c₃` any chart of `A` containing the `3R`-ball (it exists by the covering
--    clause of `IsOrientedAtlas`, which is part of `IsSmoothOrientedAtlas`; the charts of `A` are
--    smooth precisely so that the transition argument goes through, cf.
--    `Work.Whitney.fderiv_transition_det_ne_zero`).  Its conclusion does not locate `p'`,`q'`; the
--    located conclusion (`‖c p'‖ < R`, `‖c q'‖ < R`) and `f' = f` for `‖c y‖ ≥ R` are available
--    inside its proof (`Work.Whitney.exists_addDoublePoint_both_signs_located` + the gluing move),
--    so copy that proof into a local variant with those extra conjuncts.
--  * Fields of `Work.Whitney.InsertedDoublePoint`: `simple_new` ←
--    `Work.Whitney.simple_of_inserted`, `simple_old` ← `Work.Whitney.simple_transported`
--    (EndgameAux.lean); `distinct` ← `c p' ≠ c q'` and `‖c p'‖ < R < ‖c p₁‖, ‖c p₂‖`;
--    `new_not_old` ← the injectivity of `f` on the `R`-ball (from the clean-ball data) at `p'`,`q'`.
--  * `SimpleDP f'`: the new pair via `simple_new`; an old pair `p ∈ doubleSet f` via
--    `doubleSet f' = doubleSet f ∪ {(p',q'),(q',p')}` and `hsimple`; the remaining cases
--    `p.1 = q'` / `p.1 = p'` (and symmetrically for `p.2`) are impossible: e.g. `p.1 = q'` gives
--    `f q' = f p.2`, and since `‖c q'‖ < R` we get `‖c p.2‖ ≥ 2R` (otherwise injectivity on the
--    `2R`-ball forces `q' = p.2`, contradicting `p.1 ≠ p.2`), whence the separation of the
--    clean-ball data gives `η ≤ ‖f q' - f p.2‖ = 0`, a contradiction.
--  * `TransDP A f'`: the new pair from the `oppositeSign` field (it provides charts of `A` at
--    `p'`,`q'` with nonvanishing `pairDet`); the old pairs from `htrans p` and `pairDet_congr`
--    using the germ agreement above (the charts of `A` are smooth, so the `pairDet` statements are
--    meaningful).
--
-- Engineering: `lean_check`/`lean_tactic` are broken here; use scratch files at the workspace root
-- and `lake env lean F.lean` (batch checks into ONE file).  `ContDiff ℝ ⊤` is *analyticity*;
-- `C^∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`.  Do not edit files that are not yours.
theorem exists_insertedDoublePoint {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (hfin : (Work.Whitney.doubleSet f).Finite)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : Work.Whitney.IsSmoothOrientedAtlas A)
    (hsimple : Work.Whitney.SimpleDP f)
    (htrans : Work.Whitney.TransDP A f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂) :
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      Work.Whitney.InsertedDoublePoint f A p₁ p₂ f' p' q' ∧
      Work.Whitney.SimpleDP f' ∧ Work.Whitney.TransDP A f' := by
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
  -- ### an atlas chart around `z`
  obtain ⟨hAor, hAsm⟩ := hA
  obtain ⟨c₃, hc₃A, hz₃⟩ := hAor.1 z
  have hc₃sm : ∀ y : M, y ∈ c₃.source → ContMDiffAt (𝓡 n) (𝓡 n) ∞ c₃ y :=
    fun y hy => (hAsm c₃ hc₃A).1 y hy
  have hc₃inv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c₃.target → ContMDiffAt (𝓡 n) (𝓡 n) ∞ c₃.symm u :=
    fun u hu => (hAsm c₃ hc₃A).2 u hu
  -- ### the separating radius
  have hnhdsD : (Dᶜ : Set M) ∈ 𝓝 z := IsClosed.compl_mem_nhds hDclosed hzD
  have hnhds : (Dᶜ ∩ c₃.source) ∈ 𝓝 z := Filter.inter_mem hnhdsD ((c₃.open_source).mem_nhds hz₃)
  have hcont_symm : ContinuousAt (cc.symm : EuclideanSpace ℝ (Fin n) → M) 0 := (hccinv 0).continuousAt
  have hsymm0cc : cc.symm 0 = z := by rw [← hccz']; exact cc.left_inv hzcc'
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := Metric.mem_nhds_iff.mp
    (hcont_symm.preimage_mem_nhds (by rw [hsymm0cc]; exact hnhds))
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
  have hsubρ : ∀ y : M, ‖cc y‖ < ρ → y ∈ c₃.source ∧ y ∉ D := by
    intro y hy
    have hyW : y ∈ W := by
      by_contra hnotW
      have h1 : ‖cc y‖ = ‖ψ‖ := by rw [hccjunk y hnotW, hψnorm]
      linarith [hρψ]
    have hyc : y ∈ cc.source :=
      hinC y hyW (by rw [← hcceqW y hyW]; exact lt_of_lt_of_le hy hρτ)
    have hylt : ‖cc y‖ < ρ₁ := lt_of_lt_of_le hy (min_le_left _ _)
    have hmem : cc.symm (cc y) ∈ Dᶜ ∩ c₃.source :=
      hρ₁sub (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hylt)
    have hyeq : cc.symm (cc y) = y := cc.left_inv hyc
    rw [hyeq] at hmem
    exact ⟨hmem.2, hmem.1⟩
  have hDρ : ∀ a : M, a ∈ D → ρ ≤ ‖cc a‖ := fun a ha =>
    le_of_not_gt (fun h => (hsubρ a h).2 ha)
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
  -- ### the sign in the atlas
  obtain ⟨d₁, d₂, hd₁A, hd₂A, hp₁d₁, hp₂d₂, hP⟩ :=
    htrans (p₁, p₂) (by rw [mem_doubleSet]; exact ⟨hp₁p₂, hfp⟩)
  have hp'₃ : p' ∈ c₃.source := (hsubρ p' (by linarith [hp'lt, h3Rρ])).1
  have hq'₃ : q' ∈ c₃.source := (hsubρ q' (by linarith [hq'lt, h3Rρ])).1
  have hp'src : p' ∈ cc.source := hsrc_cc p' (by linarith [hp'lt])
  have hq'src : q' ∈ cc.source := hsrc_cc q' (by linarith [hq'lt])
  have hp₁D : p₁ ∈ D := ⟨p₂, hp₁p₂.symm, hfp.symm⟩
  have hp₂D : p₂ ∈ D := ⟨p₁, hp₁p₂, hfp⟩
  have heq₁p : fp =ᶠ[𝓝 p₁] f := (hgerm p₁ hp₁D).mono (fun y hy => hfp_out y hy)
  have heq₂p : fp =ᶠ[𝓝 p₂] f := (hgerm p₂ hp₂D).mono (fun y hy => hfp_out y hy)
  have heq₁m : fm =ᶠ[𝓝 p₁] f := (hgerm p₁ hp₁D).mono (fun y hy => hfm_out y hy)
  have heq₂m : fm =ᶠ[𝓝 p₂] f := (hgerm p₂ hp₂D).mono (fun y hy => hfm_out y hy)
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u => cc (c₃.symm u) with hT
  have hTp' : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => cc (c₃.symm u)) (c₃ p')).det ≠ 0 :=
    fderiv_transition_det_ne_zero cc c₃ p' hp'src hp'₃ hccsm (fun u _ => hccinv u) hc₃sm hc₃inv
  have hTq' : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => cc (c₃.symm u)) (c₃ q')).det ≠ 0 :=
    fderiv_transition_det_ne_zero cc c₃ q' hq'src hq'₃ hccsm (fun u _ => hccinv u) hc₃sm hc₃inv
  have htransp : doubleDetC fp c₃ p' q' =
      doubleDetC fp cc p' q' * ((fderiv ℝ T (c₃ p')).det * (fderiv ℝ T (c₃ q')).det) :=
    doubleDetC_transition fp cc c₃ p' q' hp'src hp'₃ hq'src hq'₃
      (differentiableAt_comp_chart_globally_smooth (g := fp) (fun y => hfp_sm y) cc
        (fun u => hccinv u) (cc p'))
      (differentiableAt_comp_chart_globally_smooth (g := fp) (fun y => hfp_sm y) cc
        (fun u => hccinv u) (cc q'))
      (differentiableAt_transition_of_globally_smooth cc c₃ hccsm hc₃inv p' hp'src hp'₃)
      (differentiableAt_transition_of_globally_smooth cc c₃ hccsm hc₃inv q' hq'src hq'₃)
  have htransm : doubleDetC fm c₃ p' q' =
      doubleDetC fm cc p' q' * ((fderiv ℝ T (c₃ p')).det * (fderiv ℝ T (c₃ q')).det) :=
    doubleDetC_transition fm cc c₃ p' q' hp'src hp'₃ hq'src hq'₃
      (differentiableAt_comp_chart_globally_smooth (g := fm) (fun y => hfm_sm y) cc
        (fun u => hccinv u) (cc p'))
      (differentiableAt_comp_chart_globally_smooth (g := fm) (fun y => hfm_sm y) cc
        (fun u => hccinv u) (cc q'))
      (differentiableAt_transition_of_globally_smooth cc c₃ hccsm hc₃inv p' hp'src hp'₃)
      (differentiableAt_transition_of_globally_smooth cc c₃ hccsm hc₃inv q' hq'src hq'₃)
  have hfactor : (fderiv ℝ T (c₃ p')).det * (fderiv ℝ T (c₃ q')).det ≠ 0 := mul_ne_zero hTp' hTq'
  have hB : doubleDetC fp c₃ p' q' ≠ 0 := by
    rw [htransp]; exact mul_ne_zero hfp_detC hfactor
  have hflip : doubleDetC fm c₃ p' q' = - doubleDetC fp c₃ p' q' := by
    rw [htransm, htransp, hflip_c]; ring
  have hBm : doubleDetC fm c₃ p' q' ≠ 0 := by
    rw [hflip]; exact neg_ne_zero.mpr hB
  -- ### the assembly
  have key : ∀ (g : M → EuclideanSpace ℝ (Fin (2 * n))),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g →
      (∀ z : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g z)) →
      (∀ y : M, R ≤ ‖cc y‖ → g y = f y) →
      doubleSet g = doubleSet f ∪ {(p', q'), (q', p')} →
      OppositeSign A g p₁ p₂ p' q' →
      doubleDetC g c₃ p' q' ≠ 0 →
      InsertedDoublePoint f A p₁ p₂ g p' q' ∧ SimpleDP g ∧ TransDP A g := by
    intro g hg_sm hg_imm hg_out hg_ds hg_sign hg_detC₃
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
    · refine ⟨hg_sm, hg_imm, hg_ds, hg_sign, ?_, hsimpleNew.1, hsimpleOld, ?_, ?_⟩
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
      · obtain ⟨e₁, e₂, he₁A, he₂A, hpe₁, hpe₂, hpe⟩ := htrans p hpold
        have hpq₁ : p.1 ∈ D := ⟨p.2, (mem_doubleSet.mp hpold).1.symm, (mem_doubleSet.mp hpold).2.symm⟩
        have hpq₂ : p.2 ∈ D := ⟨p.1, (mem_doubleSet.mp hpold).1, (mem_doubleSet.mp hpold).2⟩
        refine ⟨e₁, e₂, he₁A, he₂A, hpe₁, hpe₂, ?_⟩
        rw [← pairDet_congr e₁ e₂ p.1 p.2 hpe₁ hpe₂ (hgemm_g p.1 hpq₁) (hgemm_g p.2 hpq₂)]
        exact hpe
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpnew
        rcases hpnew with hpnew | hpnew
        · have hp1 : p.1 = p' := by rw [hpnew]
          have hp2 : p.2 = q' := by rw [hpnew]
          refine ⟨c₃, c₃, hc₃A, hc₃A, ?_, ?_, ?_⟩
          · rw [hp1]; exact hp'₃
          · rw [hp2]; exact hq'₃
          · rw [hp1, hp2]
            show doubleDetC g c₃ p' q' ≠ 0
            exact hg_detC₃
        · have hp1 : p.1 = q' := by rw [hpnew]
          have hp2 : p.2 = p' := by rw [hpnew]
          refine ⟨c₃, c₃, hc₃A, hc₃A, ?_, ?_, ?_⟩
          · rw [hp1]; exact hq'₃
          · rw [hp2]; exact hp'₃
          · rw [hp1, hp2]
            show doubleDetC g c₃ q' p' ≠ 0
            have h1 : doubleDetRep (fun u : EuclideanSpace ℝ (Fin n) => g (c₃.symm u)) (c₃ p') (c₃ q') ≠ 0 :=
              hg_detC₃
            have h2 : doubleDetRep (fun u : EuclideanSpace ℝ (Fin n) => g (c₃.symm u)) (c₃ q') (c₃ p') ≠ 0 := by
              rw [doubleDetRep_ne_zero_iff] at h1 ⊢
              rwa [sup_comm]
            exact h2
  rcases oppositeSign_or_of_neg A f fp fm p₁ p₂ p' q' d₁ d₂ c₃ hd₁A hd₂A hc₃A
    hp₁d₁ hp₂d₂ hp'₃ hq'₃ heq₁p heq₂p heq₁m heq₂m hP hB hflip with hsgn | hsgn
  · exact ⟨fp, p', q', key fp hfp_sm hfp_imm hfp_out hfp_ds hsgn hB⟩
  · exact ⟨fm, p', q', key fm hfm_sm hfm_imm hfm_out hfm_ds hsgn hBm⟩

end Work.Whitney
