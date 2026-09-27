import Mathlib
import Submission.Work.Routing.germArcExtentAvoid
import Submission.Work.Routing.bump_step_avoid
import Submission.Work.Noncompact.CompressionTube.immersedLine
import Submission.Work.Routing.traceSeparation

/-!
# The rooted arc: a germ window inside a chart ball, and the body off that ball

`Work.Routing.rootedArc` produces, in an open preconnected region `W` and for any target `q` off a
chart ball `B = c.symm '' closedBall (c p) ρ`, an arc `α` from `p` to `q` which

* carries the straight germ `t ↦ c.symm (c p + t • v)` on `[0,e]` with `e ≤ ρ` (so the **whole germ
  window lies inside `B`**), and
* whose **sub-arc from parameter `e₂` on stays outside the closed ball `B`** (`e ≤ e₂`, `ρ < e₂`,
  `e₂ < 1`).

That is exactly the *rootedness* the consecutive separation of the corridor routing consumes:
every visit of `α` to the *open* ball `B` happens at a parameter `≤ e₂`, so the ball visits of the
piece are controlled by the declared window – with the radius `ρ` and the window `e₂` both **chosen
freely**, which is what the older attempts (`Work.Routing.rootedArcWithGerm`) could not deliver.

## Why the ambient is `W ∖ B` and not `W ∖ (B ∪ germ ray)`

Running the reachability argument of `Work.Noncompact.CompressionTube.immersedArcWithGerm` with an
extra *avoidance* clause forces a choice of ambient:

* deleting the germ ray from `W ∖ B` destroys openness at `p` (the ray accumulates at `p`), and the
  set `W ∖ (B ∪ ray)` is the complement of a *closed ball with a spike*, whose preconnectedness is a
  separate topological theorem (the folding/pushing map of the design notes);
* the way out taken here: **keep the germ window inside `B`** (`e ≤ ρ`), so no germ point lies in the
  ambient `W ∖ B` at all.  The undesirable points of a good arc (its germ window) are then *outside*
  the ambient, which is precisely what makes the clopen argument of the reachability work: the
  ambient is `W ∖ B`, open preconnected by the proved
  `Work.Noncompact.CompressionTube.isPreconnected_sdiff_chartClosedBall`.

Consequently the predicate carries only clauses that the ambient already respects:

    S = { z | ∃ α, smooth, immersion, `InjOn` on `[0,1]`, image in `W`,
                germ on `[0,e]`, and `∀ t ∈ [e₂,1], α t ∉ B` } ,

and `S ⊆ W ∖ B`.  The seed is the proved `germArcExtentAvoid` (a straight ray with prescribed germ
extent `e₂` whose far part already avoids `B`), and the bump step is `bumpStepGermAvoid` below – the
proved `bump_step_avoid_tail` with the *germ window* and the *avoidance window* decoupled.
-/

namespace Work.Routing

open Set Topology Function
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The bump step with decoupled germ and avoidance windows.**  `Work.Noncompact.CompressionTube
.bump_step_avoid_tail` with one parameter for the germ window and another for the part of the arc
that has to avoid a closed set. -/
theorem bumpStepGermAvoid {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]
    {W : Set M} {p : M} {v : EuclideanSpace ℝ (Fin n)} {e e₂ : ℝ}
    (he : 0 < e) (he₂ : 0 < e₂)
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
    (hSav : ∀ t ∈ Set.Icc e₂ 1, α t ∉ S) :
    ∃ α' : ℝ → M, ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α' ∧ α' 0 = p ∧ α' 1 = z' ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α' t)) ∧
      Set.InjOn α' (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α' t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e, α' t = c.symm (c p + t • v)) ∧
      (∀ t ∈ Set.Icc e₂ 1, α' t ∉ S) := by
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
  · intro t ht
    by_cases hmem : α t ∈ cc.symm '' Metric.ball (cc (α 1)) R
    · exact hSnotmem _ (hψmem (α t) hmem)
    · rw [Function.comp_apply, hψid (α t) hmem]
      exact hSav t ⟨ht.1, ht.2⟩

/-- **The rooted arc.**  A prescribed germ window `[0,e]` sitting inside the chart ball
`B = c.symm '' closedBall (c p) ρ` (`e ≤ ρ`), the sub-arc from `e₂` on staying outside `B`
(`ρ < e₂ < 1`), reaching any `q ∉ B` inside the open preconnected `W`. -/
theorem rootedArc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPreconnected W)
    {p q : M} (hp : p ∈ W) (hq : q ∈ W) (hpq : p ≠ q)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M) (hpc : p ∈ c.source)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    {e : ℝ} (he : 0 < e)
    {ρ ρ' : ℝ} (heρ : e * ‖v‖ ≤ ρ) (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hρtgt : Metric.closedBall (c p) ρ ⊆ c.target)
    (hρ'tgt : Metric.closedBall (c p) ρ' ⊆ c.target)
    (hballW : c.symm '' Metric.closedBall (c p) ρ' ⊆ W)
    {e₂ : ℝ} (he₂ : 0 < e₂) (hee₂ : e ≤ e₂) (hρe₂ : ρ < e₂ * ‖v‖) (he₂1 : e₂ < 1)
    (hqB : q ∉ c.symm '' Metric.closedBall (c p) ρ)
    {ρ₀ : ℝ} (he₂ρ₀ : e₂ < ρ₀)
    (hray : ∀ t : ℝ, 0 ≤ t → t < ρ₀ → c p + t • v ∈ c.target)
    (hrayb : ∀ t : ℝ, -ρ₀ < t → t ≤ 0 → c p + t • v ∈ c.target)
    (hgerW : ∀ t : ℝ, 0 < t → t < ρ₀ → c.symm (c p + t • v) ∈ W) :
    ∃ α : ℝ → M, α 0 = p ∧ α 1 = q ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → α t ∈ W) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → α t = c.symm (c p + t • v)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → e₂ ≤ t →
        α t ∉ c.symm '' Metric.closedBall (c p) ρ) ∧
      ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (w : EuclideanSpace ℝ (Fin n)) (e' : ℝ), 0 < e' ∧ w ≠ 0 ∧
        c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder M ∧ q ∈ c'.source ∧
        ∀ t : ℝ, 1 - e' ≤ t → t ≤ 1 → α t = c'.symm (c' q + (t - 1) • w) := by
  classical
  have hn0 : Work.Noncompact.CompressionTube.smoothOrder ≠ (0 : WithTop ℕ∞) := by
    simp [Work.Noncompact.CompressionTube.smoothOrder]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set U : Set M := W \ c.symm '' Metric.closedBall (c p) ρ with hUdef
  have hBclosed : IsClosed (c.symm '' Metric.closedBall (c p) ρ) :=
    ((isCompact_closedBall (c p) ρ).image_of_continuousOn
      (c.continuousOn_symm.mono hρtgt)).isClosed
  have hUopen : IsOpen U := hW.sdiff hBclosed
  have hUpc : IsPreconnected U :=
    Work.Noncompact.CompressionTube.isPreconnected_sdiff_chartClosedBall hn hW hWc hpc
      hρ hρρ' hρ'tgt hballW
  -- ## the seed
  obtain ⟨A, hAcd, hA0, hAimm, hAinj, hAimg, hAgerm, _hAgtgt, hAavoid, _hAterm⟩ :=
    Work.Noncompact.CompressionTube.germArcExtentAvoid (n := n) (M := M) hn hW hp c hc hpc hv
      (ρpos := ρ₀) (ρneg := ρ₀) (by linarith) (by linarith) hray hrayb
      (fun t ht1 ht2 => hgerW t ht1 (by simpa [min_self] using ht2))
      (L := e₂) he₂ (by simpa using he₂ρ₀)
      (h := (e₂ + 1) / 2) (by linarith) (by linarith)
      (δ := (e₂ + 1) / 2) (by linarith) (by linarith)
      hρ hρe₂ hρtgt
  -- ## the reachable set
  set S : Set M := {z | ∃ α : ℝ → M,
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α ∧ α 0 = p ∧ α 1 = z ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e, α t = c.symm (c p + t • v)) ∧
      (∀ t ∈ Set.Icc e₂ 1, α t ∉ c.symm '' Metric.closedBall (c p) ρ)}
    with hSdef
  have hSU : S ⊆ U := by
    intro z hz
    rw [hSdef] at hz
    obtain ⟨α, -, -, hα1, -, -, hαimg, -, hαav⟩ := hz
    refine ⟨hα1 ▸ hαimg 1 ⟨by norm_num, le_refl 1⟩, ?_⟩
    rw [← hα1]
    exact hαav 1 ⟨he₂1.le, le_refl 1⟩
  have hseedU : A 1 ∈ U := by
    refine ⟨hAimg 1 ⟨by norm_num, le_refl 1⟩, ?_⟩
    exact hAavoid 1 he₂1.le le_rfl
  have hseedS : A 1 ∈ S := by
    rw [hSdef]
    exact ⟨A, hAcd, hA0, rfl, hAimm, hAinj, hAimg,
      fun t ht => hAgerm t ⟨ht.1, le_trans ht.2 hee₂⟩,
      fun t ht => hAavoid t ht.1 ht.2⟩
  -- ## `S` is open
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro z hz
    rw [hSdef] at hz
    have hzU : z ∈ U := hSU (by rw [hSdef]; exact hz)
    obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm, hαav⟩ := hz
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
      have hd : ‖t • v‖ ≤ ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact le_trans (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)) heρ
      have hball : α t ∈ c.symm '' Metric.closedBall (c p) ρ :=
        ⟨c p + t • v, Metric.mem_closedBall.mpr (by
          rw [dist_eq_norm, add_sub_cancel_left]; exact hd), by rw [hg]⟩
      exact (hRU hmem).2 hball
    have hSdisj : Disjoint (c.symm '' Metric.closedBall (c p) ρ)
        (cz.symm '' Metric.ball (cz (α 1)) R) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => (hRU hx2).2 hx1
    have hSav : ∀ t ∈ Set.Icc e₂ 1, α t ∉ c.symm '' Metric.closedBall (c p) ρ := hαav
    refine ⟨cz.symm '' (Metric.ball (cz z) (κ * R) ∩ cz.target), ?_, ?_, ?_⟩
    · rintro z' ⟨u, hu, rfl⟩
      have hutgt : u ∈ cz.target := hu.2
      have hz'src : cz.symm u ∈ cz.source := cz.map_target hutgt
      have hdist : ‖cz (cz.symm u) - cz (α 1)‖ < κ * R := by
        rw [cz.right_inv hutgt, hα1]
        exact Metric.mem_ball.mp hu.1
      have hα1src : α 1 ∈ cz.source := by rw [hα1]; exact hzsrc
      obtain ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩ :=
        bumpStepGermAvoid (n := n) (M := M) he he₂ hκspec hαcd hα0 hαimm hαinj hαimg
          (fun t ht => hαgerm t ht) hczc hczs hα1src hRpos hRclosed (fun x hx => (hRU hx).1)
          hRavoid hz'src hdist hSdisj hSav
      rw [hSdef]
      exact ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩
    · exact cz.isOpen_image_symm_of_subset_target (Metric.isOpen_ball.inter cz.open_target)
        (fun x hx => hx.2)
    · exact ⟨cz z, ⟨Metric.mem_ball_self (mul_pos hκpos hRpos), cz.map_source hzsrc⟩,
        cz.left_inv hzsrc⟩
  -- ## `S` is closed inside `U`
  have hScl : closure S ∩ U ⊆ S := by
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
    rw [hSdef] at hu_S
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
      fun x hx => (hRG (Set.image_mono hballsub hx)).1
    have hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e, α t ∉ cr.symm '' Metric.ball (cr (α 1)) (R / 2) := by
      intro t ht hmem
      have hg : α t = c.symm (c p + t • v) := hαgerm t ht
      have hd : ‖t • v‖ ≤ ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact le_trans (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)) heρ
      have hball : α t ∈ c.symm '' Metric.closedBall (c p) ρ :=
        ⟨c p + t • v, Metric.mem_closedBall.mpr (by
          rw [dist_eq_norm, add_sub_cancel_left]; exact hd), by rw [hg]⟩
      exact (hRG (Set.image_mono hballsub hmem)).2 hball
    have hdistr : ‖cr r - cr (α 1)‖ < κ * (R / 2) := by
      rw [hα1, hcu, norm_sub_rev]
      rw [dist_eq_norm] at hdu
      linarith [hδκ]
    have hα1src : α 1 ∈ cr.source := by rw [hα1]; exact hu_src
    have hSdisj : Disjoint (c.symm '' Metric.closedBall (c p) ρ)
        (cr.symm '' Metric.ball (cr (α 1)) (R / 2)) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => (hRG (Set.image_mono hballsub hx2)).2 hx1
    have hSav : ∀ t ∈ Set.Icc e₂ 1, α t ∉ c.symm '' Metric.closedBall (c p) ρ := hαav
    obtain ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩ :=
      bumpStepGermAvoid (n := n) (M := M) he he₂ hκspec hαcd hα0 hαimm hαinj hαimg
        (fun t ht => hαgerm t ht) hcrc hcrs hα1src (by linarith) hRclosed hRW hRavoid
        hrsrc hdistr hSdisj hSav
    rw [hSdef]
    exact ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ, hα'av⟩
  -- ## conclusion
  have hsub : U ⊆ S :=
    hUpc.subset_of_closure_inter_subset hSopen ⟨A 1, hseedU, hseedS⟩ hScl
  have hqU : q ∈ U := ⟨hq, hqB⟩
  have hqS : q ∈ S := hsub hqU
  rw [hSdef] at hqS
  obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm, hαav⟩ := hqS
  obtain ⟨c', w, e', he'pos, hwne, hc'max, hqsrc, hterm⟩ :=
    Work.Noncompact.CompressionTube.exists_straightened_chart hαcd (hαimm 1)
  refine ⟨α, hα0, hα1, hαcd, hαimm, hαinj, hαimg, (fun t ht0 hte => hαgerm t ⟨ht0, hte⟩),
    (fun t ht hte => hαav t ⟨hte, ht.2⟩), c', w, e', he'pos, hwne,
    hc'max, hα1 ▸ hqsrc, ?_⟩
  intro t ht1 ht2
  obtain ⟨hsrc, heq⟩ := hterm t ht1 ht2
  rw [hα1] at heq
  rw [← heq, c'.left_inv hsrc]

end

end Work.Routing

namespace Work.Routing

open Set Topology Function
open scoped Manifold ContDiff Topology

/-- **Trace confinement from a constructive avoidance.**

The consecutive separation of the corridor routing consumes a *trace confinement*: the arriving
piece's visits to a set `C` must lie in a small set `B`.  In the construction the arriving piece
`β₁` is *built first*, its body outside `B` is a compact set `β₁ '' Icc ∖ B`, and the departing
piece `β₂` is then produced by a reachability that avoids that compact set.  This lemma records the
trivial set-theoretic consequence:

if every point of `β₂` is either in `B ∪ B'` or outside `β₁ '' Icc ∖ B`, and `B'` is disjoint from
`β₁ '' Icc ∖ B`, then `β₁ '' Icc ∩ β₂ '' Icc ⊆ B`.

(`B` plays the role of the rootedness ball, `B'` of the *other* junction's ball: the two are
disjoint in the routing because they sit inside the two, disjoint, necks of the chain.) -/
theorem inter_subset_of_body_avoids {n : ℕ} {M : Type*} [TopologicalSpace M]
    {β₁ β₂ : ℝ → M} {B B' : Set M}
    (hcase : ∀ t ∈ Set.Icc (0:ℝ) 1,
      β₂ t ∈ B ∪ B' ∨ β₂ t ∉ β₁ '' Set.Icc (0:ℝ) 1 \ B)
    (hdisjB' : Disjoint B' (β₁ '' Set.Icc (0:ℝ) 1 \ B)) :
    β₁ '' Set.Icc (0:ℝ) 1 ∩ β₂ '' Set.Icc (0:ℝ) 1 ⊆ B := by
  intro x hx
  obtain ⟨⟨s, hs, hxs⟩, ⟨t, ht, hxt⟩⟩ := hx
  by_cases hB : β₂ t ∈ B
  · rw [← hxt]; exact hB
  · rcases hcase t ht with hmem | hnot
    · rcases hmem with h | h
      · exact absurd h hB
      · exact absurd ⟨⟨s, hs, hxs.trans hxt.symm⟩, hB⟩ (Set.disjoint_left.mp hdisjB' h)
    · exact absurd ⟨⟨s, hs, hxs.trans hxt.symm⟩, hB⟩ hnot

end Work.Routing

namespace Work.Routing

open Set Topology Function
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]

/-- **The junction separation in the shape the routing produces it.**

Two pieces arrive at and depart from a junction `σ` with the two halves of one straight chart germ.
If, in addition,

* the arriving piece lies in a set `C` and the departing piece in a set `C'` with
  `C ∩ C' ⊆ B` (in the routing `C = h.C i`, `C' = h.C (i+1)`, `C ∩ C' = neck`, `B` the rootedness
  ball containing the neck — see `NOTES_posLaneWin_SESSION4.txt` §7),
* each piece's visits to `B` are its own germ window (`hProot`, `hQroot`),

then the two images meet only at `σ`.

Note that no trace condition of the form "the arriving piece's visits to the whole of `C'` are in
`B`" is needed: it is enough that the *intersection* `C ∩ C'` is inside `B`.  This is the form that
avoids the obstruction of §3 of the same note. -/
theorem inter_subset_singleton_of_neck {P₁ Q₁ : ℝ → M}
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {σ : M} {w : EuclideanSpace ℝ (Fin n)} {e e' : ℝ}
    (hw : w ≠ 0) (he : 0 < e) (he' : 0 < e')
    (hP1 : P₁ 1 = σ) (hQ0 : Q₁ 0 = σ) (hsrc : σ ∈ c.source)
    (hPgerm : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P₁ t = c.symm (c σ + (t - 1) • w))
    (hQgerm : ∀ t : ℝ, 0 ≤ t → t ≤ e' → Q₁ t = c.symm (c σ + t • w))
    (hPtgt : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → c σ + (t - 1) • w ∈ c.target)
    (hQtgt : ∀ t : ℝ, 0 ≤ t → t ≤ e' → c σ + t • w ∈ c.target)
    {C C' B : Set M} (hPsub : P₁ '' Set.Icc (0:ℝ) 1 ⊆ C)
    (hQsub : Q₁ '' Set.Icc (0:ℝ) 1 ⊆ C') (hinter : C ∩ C' ⊆ B)
    (hProot : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → P₁ t ∈ B → t ∈ Set.Icc (1 - e) 1)
    (hQroot : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → Q₁ t ∈ B → t ∈ Set.Icc (0:ℝ) e') :
    P₁ '' Set.Icc (0:ℝ) 1 ∩ Q₁ '' Set.Icc (0:ℝ) 1 ⊆ {σ} := by
  refine Work.Routing.inter_subset_singleton_of_trace (P := P₁) (Q := Q₁)
    (C := Q₁ '' Set.Icc (0:ℝ) 1) (B := B) hw he he' hP1 hQ0 hsrc hPgerm hQgerm
    hPtgt hQtgt ?_ ?_ hProot hQroot
  · intro t ht
    exact ⟨t, ht, rfl⟩
  · intro t ht hmem
    exact hinter ⟨hPsub ⟨t, ht, rfl⟩, hQsub hmem⟩

end Work.Routing
