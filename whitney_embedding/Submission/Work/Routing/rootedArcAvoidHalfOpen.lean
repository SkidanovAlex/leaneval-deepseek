import Mathlib
import Submission.Work.Routing.rootedArc
import Submission.Work.Routing.rootedArcAvoid

/-!
# The rooted arc with a half-open avoidance window

`Work.Routing.rootedArcAvoid` gives an arc with a prescribed germ window `[0,e]` whose body avoids a
closed set `S` from a *later* parameter `e₂ > e` on.  The strictness `e₂ > e` is forced: the germ
window lies inside `S`, so at `t = e` the arc is in `S` and cannot also avoid it.

This file removes the gap by making the avoidance window *half-open* at the germ end: the arc is the
straight germ on `[0,e]` and avoids `S` on `(e,1]`.  The reachability argument is
`Work.Routing.rootedArcAvoid`'s verbatim — only the bump step's interval changes (it is restated
below as `bumpStepGermAvoidHF`), and the seed hypothesis `hAavoid` is correspondingly half-open.

The germ-window points no longer need to be excluded from the entity `U = W ∖ S` by hand: they are
*derived* to lie in `S` from `hUdisj` together with `hgermW`.

Notation: `bumpStepGermAvoidHF` is `Work.Routing.bumpStepGermAvoid` with the two avoidance intervals
`Icc e₂ 1` replaced by `e < t → t ≤ 1`.
-/

namespace Work.Routing

open Set Topology Function
open scoped Manifold ContDiff Topology

noncomputable section

theorem bumpStepGermAvoidHF {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]
    {W : Set M} {p : M} {v : EuclideanSpace ℝ (Fin n)} {e : ℝ}
    (he : 0 < e) (he1 : e < 1)
    {κ : ℝ} (hκspec : Work.Noncompact.CompressionTube.IsBumpConst n (M := M) κ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {α : ℝ → M} (hαcd : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder α) (hα0 : α 0 = p)
    (hαimm : ∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) α t))
    (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    (hαimg : ∀ t ∈ Set.Icc (0:ℝ) 1, α t ∈ W)
    (hαgerm : ∀ t ∈ Set.Icc (0:ℝ) e, α t = c.symm (c p + t • v))
    {cc : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hccc : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder cc cc.source)
    (hccs : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder cc.symm cc.target)
    (hα1src : α 1 ∈ cc.source)
    {R : ℝ} (hRpos : 0 < R) (hRclosed : Metric.closedBall (cc (α 1)) R ⊆ cc.target)
    (hRW : cc.symm '' Metric.ball (cc (α 1)) R ⊆ W)
    (hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e, α t ∉ cc.symm '' Metric.ball (cc (α 1)) R)
    {z' : M} (hz'src : z' ∈ cc.source) (hz'dist : ‖cc z' - cc (α 1)‖ < κ * R)
    {S : Set M} (hSdisj : Disjoint S (cc.symm '' Metric.ball (cc (α 1)) R))
    (hSav : ∀ t : ℝ, e < t → t ≤ 1 → α t ∉ S) :
    ∃ α' : ℝ → M, ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α' ∧ α' 0 = p ∧ α' 1 = z' ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α' t)) ∧
      Set.InjOn α' (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α' t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e, α' t = c.symm (c p + t • v)) ∧
      (∀ t : ℝ, e < t → t ≤ 1 → α' t ∉ S) := by
  have hn0 : Work.Noncompact.CompressionTube.smoothOrder ≠ (0 : WithTop ℕ∞) := by
    simp [Work.Noncompact.CompressionTube.smoothOrder]
  obtain ⟨ψ, hψcd, hψinj, hψid, hψz, hψA, hψimm, -⟩ :=
    hκspec cc hccc hccs (α 1) hα1src R hRpos hRclosed z' hz'src hz'dist
  have hψmem : ∀ x : M, x ∈ cc.symm '' Metric.ball (cc (α 1)) R →
      ψ x ∈ cc.symm '' Metric.ball (cc (α 1)) R := fun x hx => hψA ⟨x, hx, rfl⟩
  have hSnotmem : ∀ x : M, x ∈ cc.symm '' Metric.ball (cc (α 1)) R → x ∉ S :=
    fun x hxb hxs => (Set.disjoint_left.mp hSdisj) hxs hxb
  refine ⟨ψ ∘ α, hψcd.comp hαcd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (ψ ∘ α) 0 = p
    rw [Function.comp_apply]
    have h := hψid (α 0) (hRavoid 0 ⟨le_refl 0, he.le⟩)
    rw [hα0] at h ⊢
    exact h
  · show (ψ ∘ α) 1 = z'
    rw [Function.comp_apply]
    exact hψz
  · intro t
    have hψmd : MDifferentiableAt (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n) ψ (α t) :=
      hψcd.contMDiffAt.mdifferentiableAt hn0
    have hαmd : MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α t :=
      hαcd.contMDiffAt.mdifferentiableAt hn0
    have hcomp := mfderiv_comp (I := Work.Noncompact.CompressionTube.MCreal)
      (I' := Work.Noncompact.CompressionTube.MC n)
      (I'' := Work.Noncompact.CompressionTube.MC n) (f := α) (g := ψ) t hψmd hαmd
    rw [hcomp]
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    exact hαimm t (hψimm (α t) hab)
  · intro s hs t ht hst
    exact hαinj hs ht (hψinj hst)
  · intro t ht
    by_cases hmem : α t ∈ cc.symm '' Metric.ball (cc (α 1)) R
    · exact hRW (hψmem (α t) hmem)
    · rw [Function.comp_apply, hψid (α t) hmem]; exact hαimg t ht
  · intro t ht
    rw [Function.comp_apply, hψid (α t) (hRavoid t ht)]
    exact hαgerm t ht
  · intro t ht1 ht2
    by_cases hmem : α t ∈ cc.symm '' Metric.ball (cc (α 1)) R
    · exact hSnotmem _ (hψmem (α t) hmem)
    · rw [Function.comp_apply, hψid (α t) hmem]
      exact hSav t ht1 ht2


theorem rootedArcAvoidHalfOpen {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {W U S : Set M} (hW : IsOpen W) (hUopen : IsOpen U) (hUpc : IsPreconnected U)
    (hSclosed : IsClosed S) (hUW : W \ S ⊆ U) (hUsub : U ⊆ W) (hSUdisj : Disjoint S U)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M) {p q : M} (hpc : p ∈ c.source)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) {e : ℝ} (he : 0 < e)
    (hgermW : ∀ t : ℝ, 0 ≤ t → t ≤ e → c.symm (c p + t • v) ∈ W)
    (hUdisj : Disjoint U (c.symm '' ((fun t : ℝ => c p + t • v) '' Set.Icc (0:ℝ) e)))
    (he1 : e < 1)
    {A : ℝ → M} (hAcd : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder A) (hA0 : A 0 = p)
    (hAgerm : ∀ t : ℝ, 0 ≤ t → t ≤ e → A t = c.symm (c p + t • v))
    (hAimg : ∀ t ∈ Set.Icc (0:ℝ) 1, A t ∈ W)
    (hAimm : ∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) A t))
    (hAinj : Set.InjOn A (Set.Icc (0:ℝ) 1))
    (hAavoid : ∀ t : ℝ, e < t → t ≤ 1 → A t ∉ S)
    (hqW : q ∈ W) (hqS : q ∉ S) :
    ∃ α : ℝ → M, α 0 = p ∧ α 1 = q ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → α t ∈ W) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → α t = c.symm (c p + t • v)) ∧
      (∀ t : ℝ, e < t → t ≤ 1 → α t ∉ S) ∧
      ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (w : EuclideanSpace ℝ (Fin n)) (e' : ℝ), 0 < e' ∧ w ≠ 0 ∧
        c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder M ∧ q ∈ c'.source ∧
        ∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → α t = c'.symm (c' q + (t - 1) • w) := by
  classical
  have hn0 : Work.Noncompact.CompressionTube.smoothOrder ≠ (0 : WithTop ℕ∞) := by
    simp [Work.Noncompact.CompressionTube.smoothOrder]
  -- ## the reachable set
  set S₀ : Set M := {z | ∃ α : ℝ → M,
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α ∧ α 0 = p ∧ α 1 = z ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e, α t = c.symm (c p + t • v)) ∧
      (∀ t : ℝ, e < t → t ≤ 1 → α t ∉ S)} with hS₀def
  have hS₀U : S₀ ⊆ U := by
    intro z hz
    rw [hS₀def] at hz
    obtain ⟨α, -, -, hα1, -, -, hαimg, -, hαav⟩ := hz
    exact hUW ⟨hα1 ▸ hαimg 1 ⟨by norm_num, le_refl 1⟩, by rw [← hα1]; exact hαav 1 he1 le_rfl⟩
  have hseedU : A 1 ∈ U := hUW ⟨hAimg 1 ⟨by norm_num, le_refl 1⟩, hAavoid 1 he1 le_rfl⟩
  have hseedS : A 1 ∈ S₀ := by
    rw [hS₀def]
    exact ⟨A, hAcd, hA0, rfl, hAimm, hAinj, hAimg,
      (fun t ht => hAgerm t ht.1 ht.2), hAavoid⟩
  -- ## `S₀` is open
  have hSopen : IsOpen S₀ := by
    rw [isOpen_iff_forall_mem_open]
    rintro z hz
    rw [hS₀def] at hz
    have hzU : z ∈ U := hS₀U (by rw [hS₀def]; exact hz)
    obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm, hαav⟩ := hz
    have hzS : z ∉ S := by rw [← hα1]; exact hαav 1 he1 le_rfl
    obtain ⟨κ, hκpos, hκspec⟩ :=
      Work.Noncompact.CompressionTube.exists_isBumpConst (n := n) (M := M)
    set cz : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) z with hczdef
    have hzsrc : z ∈ cz.source := mem_chart_source _ z
    have hczc : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder cz cz.source := contMDiffOn_chart
    have hczs : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder cz.symm cz.target := contMDiffOn_chart_symm
    obtain ⟨ρz, hρzpos, hρzsub⟩ :=
      Metric.isOpen_iff.mp cz.open_target (cz z) (cz.map_source hzsrc)
    have hcontz : ContinuousAt cz.symm (cz z) :=
      cz.continuousOn_symm.continuousAt (cz.open_target.mem_nhds (cz.map_source hzsrc))
    obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ :=
      Metric.mem_nhds_iff.mp (hcontz.preimage_mem_nhds
        (hUopen.mem_nhds (by rw [cz.left_inv hzsrc]; exact hzU)))
    set R : ℝ := min (ρz / 2) ρ₂ with hRdef
    have hRpos : 0 < R := lt_min (by linarith) hρ₂pos
    have hRleρ : R ≤ ρz / 2 := min_le_left _ _
    have hRleρ₂ : R ≤ ρ₂ := min_le_right _ _
    have hRclosed : Metric.closedBall (cz (α 1)) R ⊆ cz.target := by
      rw [hα1]
      exact Subset.trans (Metric.closedBall_subset_ball (by linarith [hRleρ])) hρzsub
    have hRU : cz.symm '' Metric.ball (cz (α 1)) R ⊆ U := by
      rw [hα1]
      rintro x ⟨y, hy, rfl⟩
      exact hρ₂sub (Metric.ball_subset_ball hRleρ₂ hy)
    have hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e, α t ∉ cz.symm '' Metric.ball (cz (α 1)) R := by
      intro t ht hmem
      have hg : α t = c.symm (c p + t • v) := hαgerm t ht
      exact Set.disjoint_left.mp hUdisj (hRU hmem)
        ⟨c p + t • v, ⟨t, ⟨ht.1, ht.2⟩, rfl⟩, hg.symm⟩
    have hSdisj : Disjoint S (cz.symm '' Metric.ball (cz (α 1)) R) :=
      (hSUdisj.mono_right hRU)
    have hSav : ∀ t : ℝ, e < t → t ≤ 1 → α t ∉ S := hαav
    refine ⟨cz.symm '' (Metric.ball (cz z) (κ * R) ∩ cz.target), ?_, ?_, ?_⟩
    · rintro z' ⟨u, hu, rfl⟩
      have hutgt : u ∈ cz.target := hu.2
      have hz'src : cz.symm u ∈ cz.source := cz.map_target hutgt
      have hdist : ‖cz (cz.symm u) - cz (α 1)‖ < κ * R := by
        rw [cz.right_inv hutgt, hα1]
        exact Metric.mem_ball.mp hu.1
      have hα1src : α 1 ∈ cz.source := by rw [hα1]; exact hzsrc
      obtain ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩ :=
        bumpStepGermAvoidHF (n := n) (M := M) he he1 hκspec hαcd hα0 hαimm hαinj hαimg
          (fun t ht => hαgerm t ht) hczc hczs hα1src hRpos hRclosed (fun x hx => hUsub (hRU hx))
          hRavoid hz'src hdist hSdisj hSav
      rw [hS₀def]
      exact ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩
    · exact cz.isOpen_image_symm_of_subset_target (Metric.isOpen_ball.inter cz.open_target)
        (fun x hx => hx.2)
    · exact ⟨cz z, ⟨Metric.mem_ball_self (mul_pos hκpos hRpos), cz.map_source hzsrc⟩,
        cz.left_inv hzsrc⟩
  -- ## `S₀` is closed inside `U`
  have hScl : closure S₀ ∩ U ⊆ S₀ := by
    rintro r ⟨hrcl, hrU⟩
    obtain ⟨κ, hκpos, hκspec⟩ :=
      Work.Noncompact.CompressionTube.exists_isBumpConst (n := n) (M := M)
    set cr : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) r with hcrdef
    have hrsrc : r ∈ cr.source := mem_chart_source _ r
    have hcrc : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder cr cr.source := contMDiffOn_chart
    have hcrs : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder cr.symm cr.target := contMDiffOn_chart_symm
    obtain ⟨ρc, hρcpos, hρcsub⟩ := Metric.isOpen_iff.mp cr.open_target (cr r) (cr.map_source hrsrc)
    have hcont : ContinuousAt cr.symm (cr r) :=
      cr.continuousOn_symm.continuousAt (cr.open_target.mem_nhds (cr.map_source hrsrc))
    obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ :=
      Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds
        (hUopen.mem_nhds (by rw [cr.left_inv hrsrc]; exact hrU)))
    set R : ℝ := min (ρc / 2) ρ₂ with hRdef
    have hRpos : 0 < R := lt_min (by linarith) hρ₂pos
    have hRleρ : R ≤ ρc / 2 := min_le_left _ _
    have hRleρ₂ : R ≤ ρ₂ := min_le_right _ _
    have hRball : Metric.closedBall (cr r) R ⊆ cr.target :=
      Subset.trans (Metric.closedBall_subset_ball (by linarith [hRleρ])) hρcsub
    have hRG : cr.symm '' Metric.ball (cr r) R ⊆ U := by
      rintro x ⟨y, hy, rfl⟩
      exact hρ₂sub (Metric.ball_subset_ball hRleρ₂ hy)
    set δ : ℝ := min (R / 4) (κ * (R / 4)) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact div_pos (lt_min (by linarith) (mul_pos hκpos (by linarith))) (by norm_num)
    have hδR : δ ≤ R / 4 := by
      rw [hδdef]
      have h1 : min (R / 4) (κ * (R / 4)) ≤ R / 4 := min_le_left _ _
      linarith
    have hδκ : δ < κ * (R / 2) := by
      rw [hδdef]
      have h1 : min (R / 4) (κ * (R / 4)) ≤ κ * (R / 4) := min_le_right _ _
      have h2 : 0 < κ * (R / 4) := mul_pos hκpos (by linarith)
      linarith
    have hballtarget : Metric.ball (cr r) δ ⊆ cr.target :=
      Subset.trans Metric.ball_subset_closedBall
        (Subset.trans (Metric.closedBall_subset_closedBall (le_trans hδR (by linarith))) hRball)
    have hballopen : IsOpen (cr.symm '' Metric.ball (cr r) δ) :=
      cr.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtarget
    have hrball : r ∈ cr.symm '' Metric.ball (cr r) δ :=
      ⟨cr r, Metric.mem_ball_self hδpos, cr.left_inv hrsrc⟩
    obtain ⟨u, hu_ball, hu_S⟩ := (mem_closure_iff_nhds.mp hrcl) _ (hballopen.mem_nhds hrball)
    obtain ⟨v', hv'ball, hvu⟩ := hu_ball
    have hv'tgt : v' ∈ cr.target :=
      hballtarget (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hv'ball) (by linarith)))
    have hu_src : u ∈ cr.source := hvu ▸ cr.map_target hv'tgt
    have hcu : cr u = v' := by rw [← hvu, cr.right_inv hv'tgt]
    rw [hS₀def] at hu_S
    obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm, hαav⟩ := hu_S
    have hdu : dist v' (cr r) < δ := Metric.mem_ball.mp hv'ball
    have hRclosed : Metric.closedBall (cr (α 1)) (R / 2) ⊆ cr.target := by
      rw [hα1, hcu]
      refine Subset.trans ?_ hRball
      intro x hx
      rw [Metric.mem_closedBall] at hx ⊢
      calc dist x (cr r) ≤ dist x v' + dist v' (cr r) := dist_triangle _ _ _
        _ ≤ R / 2 + δ := add_le_add hx (le_of_lt hdu)
        _ ≤ R := by linarith [hδR]
    have hballsub : Metric.ball (cr (α 1)) (R / 2) ⊆ Metric.ball (cr r) R := by
      rw [hα1, hcu]
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y (cr r) ≤ dist y v' + dist v' (cr r) := dist_triangle _ _ _
        _ < R / 2 + δ := add_lt_add hy hdu
        _ ≤ R := by linarith [hδR]
    have hRW : cr.symm '' Metric.ball (cr (α 1)) (R / 2) ⊆ W :=
      fun x hx => hUsub (hRG (Set.image_mono hballsub hx))
    have hRB : Disjoint S (cr.symm '' Metric.ball (cr (α 1)) (R / 2)) :=
      hSUdisj.mono_right (Subset.trans (Set.image_mono hballsub) hRG)
    have hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e, α t ∉ cr.symm '' Metric.ball (cr (α 1)) (R / 2) := by
      intro t ht hmem
      have hg : α t = c.symm (c p + t • v) := hαgerm t ht
      exact Set.disjoint_left.mp hUdisj (hRG (Set.image_mono hballsub hmem))
        ⟨c p + t • v, ⟨t, ⟨ht.1, ht.2⟩, rfl⟩, hg.symm⟩
    have hdistr : ‖cr r - cr (α 1)‖ < κ * (R / 2) := by
      rw [hα1, hcu, norm_sub_rev]
      rw [dist_eq_norm] at hdu
      linarith [hδκ]
    have hα1src : α 1 ∈ cr.source := by rw [hα1]; exact hu_src
    have hSav : ∀ t : ℝ, e < t → t ≤ 1 → α t ∉ S := hαav
    obtain ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩ :=
      bumpStepGermAvoidHF (n := n) (M := M) he he1 hκspec hαcd hα0 hαimm hαinj hαimg
        (fun t ht => hαgerm t ht) hcrc hcrs hα1src (by linarith) hRclosed hRW hRavoid
        hrsrc hdistr hRB hSav
    rw [hS₀def]
    exact ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩
  -- ## conclusion
  have hsub : U ⊆ S₀ :=
    hUpc.subset_of_closure_inter_subset hSopen ⟨A 1, hseedU, hseedS⟩ hScl
  have hqU : q ∈ U := hUW ⟨hqW, hqS⟩
  have hqS₀ : q ∈ S₀ := hsub hqU
  rw [hS₀def] at hqS₀
  obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm, hαav⟩ := hqS₀
  obtain ⟨c', w, e', he'pos, hwne, hc'max, hqsrc, hterm⟩ :=
    Work.Noncompact.CompressionTube.exists_straightened_chart hαcd (hαimm 1)
  refine ⟨α, hα0, hα1, hαcd, hαimm, hαinj, hαimg,
    (fun t ht0 hte => hαgerm t ⟨ht0, hte⟩), hαav, c', w, e', he'pos, hwne,
    hc'max, hα1 ▸ hqsrc, ?_⟩
  intro t ht1 ht2
  obtain ⟨hsrc, heq⟩ := hterm t ht1 ht2
  rw [hα1] at heq
  rw [← heq, c'.left_inv hsrc]


