import Mathlib
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceGraphData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric.WeakRegion

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

variable {n : ℕ} [NeZero n]

/-- **The `s`-slice of `F` is differentiable, with derivative `Ds`, from the domain-membership
hypothesis alone.**  This is `HalfSpaceGraphSetup.hasDerivAt_slice` with the structure `Box`
replaced by the (weakly weaker) hypothesis that the whole `ρ`-ball `× [0,δ]` lies in the relative
domain; the box statement is proved *below* `exists_box`, so it cannot be used there. -/
theorem hasDerivAt_slice_of (S : HalfSpaceGraphSetup n) {ρ δ : ℝ}
    (hmem : ∀ u ∈ Metric.ball (hsMk S.p) ρ, ∀ s ∈ Set.Icc 0 δ, (u, s) ∈ S.dom)
    {u : hsTang n} (hu : u ∈ Metric.ball (hsMk S.p) ρ) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) δ) :
    HasDerivAt (fun t : ℝ => S.F (u, t)) (S.Ds (u, s)) s := by
  have hsIcc : s ∈ Set.Icc 0 δ := Set.Ioo_subset_Icc_self hs
  have hF' := S.hasFDerivWithinAt_F (u, s) (hmem u hu s hsIcc)
  have hγ : HasDerivAt (fun t : ℝ => (u, t)) (0, (1 : ℝ)) s :=
    (hasDerivAt_const (x := s) u).prodMk (hasDerivAt_id s)
  have hmaps : MapsTo (fun t : ℝ => (u, t)) (Set.Ioo (0 : ℝ) δ) S.dom :=
    fun t ht => hmem u hu t (Set.Ioo_subset_Icc_self ht)
  have h2 := hF'.comp_hasDerivWithinAt s hγ.hasDerivWithinAt hmaps
  have hval : ((S.L (u, s) ∘L hsConn) ((0 : hsTang n), (1 : ℝ))) = S.Ds (u, s) := by
    rw [ContinuousLinearMap.comp_apply]
    show S.L (u, s) (hsConn ((0 : hsTang n), (1 : ℝ))) = S.L (u, s) eZero
    rw [hsConn_apply_pair]
    simp
  rw [hval] at h2
  exact h2.hasDerivAt (isOpen_Ioo.mem_nhds hs)

/-- **The signed mean-value bound on the box, from the domain-membership and derivative bounds
alone.**  This is `HalfSpaceGraphSetup.slice_mem_Icc` with `Box` replaced by the two explicit
uniform bounds; used in the proof of `exists_box`, where the box is not yet available. -/
theorem slice_mem_Icc_of (S : HalfSpaceGraphSetup n) {ρ δ M : ℝ}
    (hmem : ∀ u ∈ Metric.ball (hsMk S.p) ρ, ∀ s ∈ Set.Icc 0 δ, (u, s) ∈ S.dom)
    (hL : ∀ u ∈ Metric.ball (hsMk S.p) ρ, ∀ s ∈ Set.Icc 0 δ,
      ‖S.L (u, s)‖ ≤ M ∧ S.Ds (u, s) ≤ S.c / 2)
    {u : hsTang n} (hu : u ∈ Metric.ball (hsMk S.p) ρ) {a b : ℝ} (ha : a ∈ Set.Icc 0 δ)
    (hb : b ∈ Set.Icc 0 δ) (hab : a ≤ b) :
    S.F (u, b) - S.F (u, a) ∈ Set.Icc (-M * (b - a)) (S.c / 2 * (b - a)) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) δ := fun x hx =>
    ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
  refine derivBoundIcc (φ := fun t : ℝ => S.F (u, t)) hab ?_ ?_ ?_ ?_
  · have hcont0 : ContinuousOn (fun t : ℝ => S.F (u, t)) (Set.Icc 0 δ) := by
      have h1 : ContinuousOn (fun t : ℝ => (u, t)) (Set.Icc 0 δ) :=
        (continuous_const.prodMk continuous_id).continuousOn
      have hFc : ContinuousOn S.F S.dom := S.contDiffOn_F.continuousOn
      exact hFc.comp h1 (fun t ht => hmem u hu t ht)
    exact hcont0.mono (Set.Icc_subset_Icc ha.1 hb.2)
  · intro x hx
    exact ((hasDerivAt_slice_of S hmem hu (hsub hx)).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_slice_of S hmem hu (hsub hx)).deriv]
    have hLx : ‖S.L (u, x)‖ ≤ M := (hL u hu x (Set.Ioo_subset_Icc_self (hsub hx))).1
    have h2 : -(S.Ds (u, x)) ≤ ‖S.L (u, x)‖ := by
      calc -(S.Ds (u, x)) ≤ |S.Ds (u, x)| := neg_le_abs _
        _ = ‖S.Ds (u, x)‖ := (Real.norm_eq_abs _).symm
        _ = ‖S.L (u, x) eZero‖ := rfl
        _ ≤ ‖S.L (u, x)‖ * ‖eZero (n := n)‖ := (S.L (u, x)).le_opNorm _
        _ = ‖S.L (u, x)‖ := by rw [eZero_norm, mul_one]
    linarith
  · intro x hx
    rw [(hasDerivAt_slice_of S hmem hu (hsub hx)).deriv]
    exact (hL u hu x (Set.Ioo_subset_Icc_self (hsub hx))).2

/-- **The local box.** Around the point `pt` of the relative domain, all the local hypotheses of the
half-space graph result hold uniformly on a box `ball (hsMk S.p) ρ × [0,δ]`: membership in the
relative domain, the derivative bounds `‖L‖ ≤ M`, `Ds ≤ c/2`, and the two sign conditions
`0 ≤ F (u,0)`, `F (u,δ) < 0`. -/
theorem exists_box {n : ℕ} [NeZero n] (S : Work.PTGeometric.WeakRegion.HalfSpaceGraphSetup n) :
    ∃ ρ δ M, S.Box ρ δ M := by
  -- the uniform bound on `‖L‖`: `M = ‖L pt‖ + 1`
  set M := ‖S.L S.pt‖ + 1 with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith [norm_nonneg (S.L S.pt)]
  -- `‖L‖` stays below `M` near `pt` inside the domain
  have hLt : Tendsto S.L (𝓝[S.dom] S.pt) (𝓝 (S.L S.pt)) := S.continuousWithinAt_L
  have e1 : ∀ᶠ x in 𝓝[S.dom] S.pt, S.L x ∈ Metric.ball (S.L S.pt) (1:ℝ) :=
    hLt (Metric.ball_mem_nhds _ one_pos)
  have e1' : ∀ᶠ x : hsTang n × ℝ in 𝓝 S.pt, x ∈ S.dom → ‖S.L x‖ ≤ M := by
    rw [eventually_nhdsWithin_iff] at e1
    refine e1.mono fun x hx hxdom => ?_
    have hx1 := hx hxdom
    rw [Metric.mem_ball] at hx1
    have hx2 : ‖S.L x - S.L S.pt‖ < 1 := by rwa [dist_eq_norm] at hx1
    calc ‖S.L x‖ = ‖S.L S.pt + (S.L x - S.L S.pt)‖ := by abel_nf
      _ ≤ ‖S.L S.pt‖ + ‖S.L x - S.L S.pt‖ := norm_add_le _ _
      _ ≤ M := by rw [hMdef]; linarith
  -- `Ds` is strictly below `c/2` near `pt` inside the domain
  have hDst : Tendsto S.Ds (𝓝[S.dom] S.pt) (𝓝 (S.Ds S.pt)) :=
    S.continuousWithinAt_Ds_at S.pt S.pt_mem_dom
  have e2 : ∀ᶠ x in 𝓝[S.dom] S.pt, S.Ds x ∈ Metric.ball (S.Ds S.pt) (-S.c/2) :=
    hDst (Metric.ball_mem_nhds _ (by linarith [S.hc]))
  have e2' : ∀ᶠ x : hsTang n × ℝ in 𝓝 S.pt, x ∈ S.dom → S.Ds x ≤ S.c/2 := by
    rw [eventually_nhdsWithin_iff] at e2
    refine e2.mono fun x hx hxdom => ?_
    have hx1 := hx hxdom
    rw [Metric.mem_ball, Real.dist_eq] at hx1
    have hx2 : S.Ds x - S.Ds S.pt ≤ -S.c/2 := le_of_lt (lt_of_le_of_lt (le_abs_self _) hx1)
    rw [S.Ds_pt] at hx2
    linarith
  -- the domain membership near `pt`
  have hV : ∀ᶠ x : hsTang n × ℝ in 𝓝 S.pt, hsConn x ∈ S.U := by
    have h : Tendsto hsConn (𝓝 S.pt) (𝓝 (hsConn S.pt)) := hsConn.continuous.continuousAt
    rw [S.hsConn_pt] at h
    exact h (S.hUopen.mem_nhds S.hpU)
  have e3 : ∀ᶠ x : hsTang n × ℝ in 𝓝 S.pt,
      hsConn x ∈ S.U ∧ (x ∈ S.dom → ‖S.L x‖ ≤ M ∧ S.Ds x ≤ S.c/2) :=
    hV.and (e1'.and e2' |>.mono fun x h => fun hx => ⟨h.1 hx, h.2 hx⟩)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp e3
  -- the boundary sign condition on a ball around `hsMk S.p`
  have hsignEv : ∀ᶠ u : hsTang n in 𝓝 (hsMk S.p), 0 ≤ S.F (u, 0) := by
    have hcont : Continuous (fun u : hsTang n => ((u : hsTang n) : EuclideanSpace ℝ (Fin n))) :=
      continuous_subtype_val
    have hval : ((hsMk S.p : hsTang n) : EuclideanSpace ℝ (Fin n)) = S.p := by
      rw [hsMk_coe]; exact tailVec_self_of_apply_zero S.hp0
    have h1 : ∀ᶠ z : EuclideanSpace ℝ (Fin n) in 𝓝 S.p, z.ofLp 0 = 0 → 0 ≤ S.Ψ z := S.hsign_nhds
    have h2 : ∀ᶠ u : hsTang n in 𝓝 (hsMk S.p),
        ((((u : hsTang n)) : EuclideanSpace ℝ (Fin n)).ofLp 0 = 0 →
          0 ≤ S.Ψ ((u : hsTang n) : EuclideanSpace ℝ (Fin n))) := by
      have ht : Tendsto (fun u : hsTang n => ((u : hsTang n) : EuclideanSpace ℝ (Fin n)))
          (𝓝 (hsMk S.p)) (𝓝 (((hsMk S.p : hsTang n) : EuclideanSpace ℝ (Fin n)))) :=
        hcont.continuousAt
      rw [hval] at ht
      exact ht.eventually h1
    filter_upwards [h2] with u hu
    rw [show S.F (u, 0) = S.Ψ ((u : hsTang n) : EuclideanSpace ℝ (Fin n)) from by
      rw [S.F_apply, hsConn_apply_pair, zero_smul, add_zero]]
    exact hu (mem_hsTang.mp u.property)
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.mp hsignEv
  -- the box parameters: `δ = min (ε/2) ρ₁`, small enough for the domain, the derivative bounds
  -- and the boundary sign
  set δ := min (ε/2) ρ₁ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (by linarith) hρ₁
  have hδε : δ ≤ ε/2 := by rw [hδdef]; exact min_le_left _ _
  have hδρ : δ ≤ ρ₁ := by rw [hδdef]; exact min_le_right _ _
  have hbox : ∀ u ∈ Metric.ball (hsMk S.p) δ, ∀ s ∈ Set.Icc 0 δ,
      (u,s) ∈ S.dom ∧ (‖S.L (u,s)‖ ≤ M ∧ S.Ds (u,s) ≤ S.c/2) := by
    intro u hu s hs
    have hsε : s ∈ Metric.ball (0:ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      linarith [hs.2, hδε, hε]
    have huε : u ∈ Metric.ball (hsMk S.p) ε :=
      Metric.ball_subset_ball (by linarith [hδε, hε]) hu
    have hpt : (u,s) ∈ Metric.ball S.pt ε := by
      show (u,s) ∈ Metric.ball (hsMk S.p, 0) ε
      rw [← ball_prod_same (hsMk S.p) (0:ℝ) ε]
      exact ⟨huε, hsε⟩
    obtain ⟨hU, hb⟩ := hεsub hpt
    have hdom : (u,s) ∈ S.dom := by rw [S.mem_dom_iff]; exact ⟨hU, hs.1⟩
    exact ⟨hdom, hb hdom⟩
  have hmem₁ : ∀ u ∈ Metric.ball (hsMk S.p) δ, ∀ s ∈ Set.Icc 0 δ, (u,s) ∈ S.dom :=
    fun u hu s hs => (hbox u hu s hs).1
  have hL₁ : ∀ u ∈ Metric.ball (hsMk S.p) δ, ∀ s ∈ Set.Icc 0 δ,
      ‖S.L (u,s)‖ ≤ M ∧ S.Ds (u,s) ≤ S.c/2 := fun u hu s hs => (hbox u hu s hs).2
  have hsign₁ : ∀ u ∈ Metric.ball (hsMk S.p) δ, 0 ≤ S.F (u,0) :=
    fun u hu => hρ₁sub (Metric.ball_subset_ball hδρ hu)
  have hIcc0 : (0:ℝ) ∈ Set.Icc 0 δ := ⟨le_refl 0, hδpos.le⟩
  have hIccδ : δ ∈ Set.Icc 0 δ := ⟨hδpos.le, le_refl δ⟩
  -- the slices decrease by at least `|c|/2` per unit
  have hmono : ∀ u ∈ Metric.ball (hsMk S.p) δ, S.F (u,δ) ≤ S.F (u,0) + S.c/2*δ := by
    intro u hu
    have h := (slice_mem_Icc_of S hmem₁ hL₁ hu hIcc0 hIccδ hδpos.le).2
    rw [sub_zero] at h
    linarith
  -- `F (·,0)` is continuous at `hsMk S.p`, with value `F pt 0 = 0`
  have hF0 : Tendsto (fun u : hsTang n => S.F (u,0)) (𝓝 (hsMk S.p)) (𝓝 0) := by
    have hval : ((hsMk S.p : hsTang n) : EuclideanSpace ℝ (Fin n)) = S.p := by
      rw [hsMk_coe]; exact tailVec_self_of_apply_zero S.hp0
    have hdom_ev : ∀ᶠ u : hsTang n in 𝓝 (hsMk S.p), ((u, 0) : hsTang n × ℝ) ∈ S.dom := by
      have hcont : Continuous (fun u : hsTang n => ((u : hsTang n) : EuclideanSpace ℝ (Fin n))) :=
        continuous_subtype_val
      have hU : ∀ᶠ u : hsTang n in 𝓝 (hsMk S.p),
          ((u : hsTang n) : EuclideanSpace ℝ (Fin n)) ∈ S.U := by
        have ht : Tendsto (fun u : hsTang n => ((u : hsTang n) : EuclideanSpace ℝ (Fin n)))
            (𝓝 (hsMk S.p)) (𝓝 (((hsMk S.p : hsTang n) : EuclideanSpace ℝ (Fin n)))) :=
          hcont.continuousAt
        rw [hval] at ht
        exact ht (S.hUopen.mem_nhds S.hpU)
      filter_upwards [hU] with u hu
      rw [S.mem_dom_iff]
      refine ⟨?_, le_refl 0⟩
      show hsConn (u, 0) ∈ S.U
      rwa [hsConn_apply_pair, zero_smul, add_zero]
    have hinner : Tendsto (fun u : hsTang n => ((u, 0) : hsTang n × ℝ)) (𝓝 (hsMk S.p))
        (𝓝[S.dom] S.pt) :=
      tendsto_nhdsWithin_iff.mpr ⟨(continuous_id.prodMk continuous_const).continuousAt, hdom_ev⟩
    have h2 : Tendsto S.F (𝓝[S.dom] S.pt) (𝓝 (S.F S.pt)) :=
      (S.contDiffOn_F.continuousOn.continuousWithinAt S.pt_mem_dom)
    have h3 := h2.comp hinner
    rw [S.F_pt] at h3
    simpa [Function.comp_def] using h3
  have hcδ : S.c * δ < 0 := mul_neg_of_neg_of_pos S.hc hδpos
  -- shrink once more so that `F (u,0)` is small compared with `|c| δ`
  have hsmall_ev : ∀ᶠ u : hsTang n in 𝓝 (hsMk S.p), S.F (u,0) < -S.c*δ/8 :=
    hF0.eventually_lt_const (by linarith)
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.mem_nhds_iff.mp hsmall_ev
  refine ⟨min ρ₂ δ, δ, M, lt_min hρ₂ hδpos, hδpos, hM, ?_, ?_, ?_⟩
  · intro u hu s hs
    exact hmem₁ u (Metric.ball_subset_ball (min_le_right ρ₂ δ) hu) s hs
  · intro u hu s hs
    exact hL₁ u (Metric.ball_subset_ball (min_le_right ρ₂ δ) hu) s hs
  · intro u hu
    have huδ : u ∈ Metric.ball (hsMk S.p) δ := Metric.ball_subset_ball (min_le_right ρ₂ δ) hu
    refine ⟨hsign₁ u huδ, ?_⟩
    have hs2 : S.F (u,0) < -S.c*δ/8 := hρ₂sub (Metric.ball_subset_ball (min_le_left ρ₂ δ) hu)
    have hm := hmono u huδ
    have h3 : S.F (u,0) + S.c/2*δ < 0 := by linarith
    linarith

end

end Work.PTGeometric.WeakRegion
