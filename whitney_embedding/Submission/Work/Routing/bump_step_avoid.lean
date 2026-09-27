import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm

/-!
# The bump step, preserving avoidance of a closed set

`Work.Noncompact.CompressionTube.bump_step` moves the endpoint of an arc carrying a prescribed germ
by a bump translation supported in a chart ball around that endpoint.  Its proof never uses the fact
that the bump is *invisible* outside its support ball: `exists_bump_imm` gives a map `ψ` which is
the identity outside `c.symm '' ball (c y) R` and which maps that ball **into itself**.

That last property is what is needed to *carry along an avoidance statement*: if `S` is a set
disjoint from the ball, then `x ∉ S` implies `ψ x ∉ S` — either `x` is outside the ball (then
`ψ x = x`), or `x` is in the ball (then `ψ x` is in the ball, hence outside `S`).

This lemma is the engine of the body-avoids-a-closed-ball result
(`Work.Routing.exists_body_avoiding_ball_head`): the reachability argument for
"arcs carrying the germ whose *non-germ* part avoids `c.symm '' closedBall (c p) ρ`" needs its
bump steps to stay inside that class, and this is exactly the compatibility.
-/

namespace Work.Noncompact.CompressionTube

open Set Metric Function
open scoped Manifold ContDiff

/-- **The bump step, preserving avoidance of a closed set disjoint from the support ball.** -/
theorem bump_step_avoid {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {W : Set M} {p : M} {v : EuclideanSpace ℝ (Fin n)} {e₀ : ℝ} (he₀pos : 0 < e₀)
    {κ : ℝ} (hκspec : IsBumpConst n (M := M) κ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {α : ℝ → M} (hαcd : ContMDiff MCreal (MC n) smoothOrder α) (hα0 : α 0 = p)
    (hαimm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α t))
    (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    (hαimg : ∀ t ∈ Set.Icc (0:ℝ) 1, α t ∈ W)
    (hαgerm : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t = c.symm (c p + t • v))
    {cc : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hccc : ContMDiffOn (MC n) (MC n) smoothOrder cc cc.source)
    (hccs : ContMDiffOn (MC n) (MC n) smoothOrder cc.symm cc.target)
    (hα1src : α 1 ∈ cc.source)
    {R : ℝ} (hRpos : 0 < R) (hRclosed : Metric.closedBall (cc (α 1)) R ⊆ cc.target)
    (hRW : cc.symm '' Metric.ball (cc (α 1)) R ⊆ W)
    (hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t ∉ cc.symm '' Metric.ball (cc (α 1)) R)
    {z' : M} (hz'src : z' ∈ cc.source) (hz'dist : ‖cc z' - cc (α 1)‖ < κ * R)
    {S : Set M} (hSdisj : Disjoint S (cc.symm '' Metric.ball (cc (α 1)) R))
    (hSav : ∀ t ∈ Set.Icc (0:ℝ) 1, α t ∉ S) :
    ∃ α' : ℝ → M, ContMDiff MCreal (MC n) smoothOrder α' ∧ α' 0 = p ∧ α' 1 = z' ∧
      (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α' t)) ∧
      Set.InjOn α' (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α' t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e₀, α' t = c.symm (c p + t • v)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α' t ∉ S) := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  obtain ⟨ψ, hψcd, hψinj, hψid, hψz, hψA, hψimm, -⟩ :=
    hκspec cc hccc hccs (α 1) hα1src R hRpos hRclosed z' hz'src hz'dist
  have hψmem : ∀ x : M, x ∈ cc.symm '' Metric.ball (cc (α 1)) R →
      ψ x ∈ cc.symm '' Metric.ball (cc (α 1)) R := fun x hx => hψA ⟨x, hx, rfl⟩
  have hSnotmem : ∀ x : M, x ∈ cc.symm '' Metric.ball (cc (α 1)) R → x ∉ S := by
    intro x hxb hxs
    have h2 : x ∈ (∅ : Set M) :=
      (Set.disjoint_iff_inter_eq_empty.mp hSdisj) ▸ (Set.mem_inter hxs hxb)
    exact h2
  refine ⟨ψ ∘ α, hψcd.comp hαcd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (ψ ∘ α) 0 = p
    rw [Function.comp_apply]
    have h := hψid (α 0) (hRavoid 0 ⟨le_refl 0, he₀pos.le⟩)
    rw [hα0] at h ⊢
    exact h
  · show (ψ ∘ α) 1 = z'
    rw [Function.comp_apply]
    exact hψz
  · intro t
    have hψmd : MDifferentiableAt (MC n) (MC n) ψ (α t) :=
      hψcd.contMDiffAt.mdifferentiableAt hn0
    have hαmd : MDifferentiableAt MCreal (MC n) α t :=
      hαcd.contMDiffAt.mdifferentiableAt hn0
    have hcomp := mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC n) (f := α) (g := ψ) t
      hψmd hαmd
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
      exact hSav t ht

end Work.Noncompact.CompressionTube

namespace Work.Noncompact.CompressionTube

open Set Metric Function
open scoped Manifold ContDiff

/-- **The bump step, carrying along avoidance of a closed set by the *non-germ* part only.**

This is the form the reachability argument for `exists_body_avoiding_ball_head` consumes: the germ
window `[0,e₀]` of the arc lies inside the avoided ball (it starts at the germ head), so only the
part on `[e₀,1]` can be required to avoid `S`; the conclusion transfers exactly that condition.
The two cases are the same as in `bump_step_avoid`: either `α t` lies in the support ball (then
`ψ (α t)` stays in the support ball, which is disjoint from `S`), or `ψ` fixes `α t`. -/
theorem bump_step_avoid_tail {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {W : Set M} {p : M} {v : EuclideanSpace ℝ (Fin n)} {e₀ : ℝ} (he₀pos : 0 < e₀)
    {κ : ℝ} (hκspec : IsBumpConst n (M := M) κ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {α : ℝ → M} (hαcd : ContMDiff MCreal (MC n) smoothOrder α) (hα0 : α 0 = p)
    (hαimm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α t))
    (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    (hαimg : ∀ t ∈ Set.Icc (0:ℝ) 1, α t ∈ W)
    (hαgerm : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t = c.symm (c p + t • v))
    {cc : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hccc : ContMDiffOn (MC n) (MC n) smoothOrder cc cc.source)
    (hccs : ContMDiffOn (MC n) (MC n) smoothOrder cc.symm cc.target)
    (hα1src : α 1 ∈ cc.source)
    {R : ℝ} (hRpos : 0 < R) (hRclosed : Metric.closedBall (cc (α 1)) R ⊆ cc.target)
    (hRW : cc.symm '' Metric.ball (cc (α 1)) R ⊆ W)
    (hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t ∉ cc.symm '' Metric.ball (cc (α 1)) R)
    {z' : M} (hz'src : z' ∈ cc.source) (hz'dist : ‖cc z' - cc (α 1)‖ < κ * R)
    {S : Set M} (hSdisj : Disjoint S (cc.symm '' Metric.ball (cc (α 1)) R))
    (hSav : ∀ t ∈ Set.Icc e₀ 1, α t ∉ S) :
    ∃ α' : ℝ → M, ContMDiff MCreal (MC n) smoothOrder α' ∧ α' 0 = p ∧ α' 1 = z' ∧
      (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α' t)) ∧
      Set.InjOn α' (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α' t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e₀, α' t = c.symm (c p + t • v)) ∧
      (∀ t ∈ Set.Icc e₀ 1, α' t ∉ S) := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  obtain ⟨ψ, hψcd, hψinj, hψid, hψz, hψA, hψimm, -⟩ :=
    hκspec cc hccc hccs (α 1) hα1src R hRpos hRclosed z' hz'src hz'dist
  have hψmem : ∀ x : M, x ∈ cc.symm '' Metric.ball (cc (α 1)) R →
      ψ x ∈ cc.symm '' Metric.ball (cc (α 1)) R := fun x hx => hψA ⟨x, hx, rfl⟩
  have hSnotmem : ∀ x : M, x ∈ cc.symm '' Metric.ball (cc (α 1)) R → x ∉ S := by
    intro x hxb hxs
    have h2 : x ∈ (∅ : Set M) :=
      (Set.disjoint_iff_inter_eq_empty.mp hSdisj) ▸ (Set.mem_inter hxs hxb)
    exact h2
  refine ⟨ψ ∘ α, hψcd.comp hαcd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (ψ ∘ α) 0 = p
    rw [Function.comp_apply]
    have h := hψid (α 0) (hRavoid 0 ⟨le_refl 0, he₀pos.le⟩)
    rw [hα0] at h ⊢
    exact h
  · show (ψ ∘ α) 1 = z'
    rw [Function.comp_apply]
    exact hψz
  · intro t
    have hψmd : MDifferentiableAt (MC n) (MC n) ψ (α t) :=
      hψcd.contMDiffAt.mdifferentiableAt hn0
    have hαmd : MDifferentiableAt MCreal (MC n) α t :=
      hαcd.contMDiffAt.mdifferentiableAt hn0
    have hcomp := mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC n) (f := α) (g := ψ) t
      hψmd hαmd
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
      exact hSav t ht

end Work.Noncompact.CompressionTube
