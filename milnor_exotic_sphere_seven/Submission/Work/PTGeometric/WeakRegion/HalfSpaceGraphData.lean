import Mathlib
import Submission.Work.PTGeometric.WeakRegion.Basic
import Submission.Work.PTGeometric.WeakRegion.exists_graph_halfSpace
import Submission.Work.PTGeometric.WeakRegion.HalfSpaceCoords
import Submission.Work.PTGeometric.WeakRegion.derivBoundIcc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGeometric/WeakRegion: the data of the `C^∞` half-space graph theorem

Vocabulary for `Work.PTGeometric.WeakRegion.exists_graph_halfSpace_cinf`.  The hypotheses of the
theorem are bundled in the structure `HalfSpaceGraphSetup`, and the objects of the proof live in the
coordinates `(u,s) ∈ T × ℝ` (`T = hsTang n` the tangential hyperplane, `hsConn (u,s) = u + s • e 0`).

* `HalfSpaceGraphSetup.dom` : the relative domain `hsConn ⁻¹' (U ∩ {0 ≤ z 0})`;
* `HalfSpaceGraphSetup.F`   : `F (u,s) = Ψ (u + s • e 0)`;
* `HalfSpaceGraphSetup.L`   : the within-derivative `fderivWithin Ψ (U ∩ {0 ≤ z 0})` at `hsConn x`;
* `HalfSpaceGraphSetup.Ds`  : its normal component (the `s`-derivative);
* `HalfSpaceGraphSetup.Du`  : its tangential part (a functional on `T`);
* `HalfSpaceGraphSetup.A`   : the would-be derivative of the graph function, `-(∂_s F)⁻¹ ∂_u F`;
* `HalfSpaceGraphSetup.Box` : a box on which all the local estimates hold uniformly;
* `HalfSpaceGraphSetup.Root`: the root (graph) function of `F` on a box.
-/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric.WeakRegion

noncomputable section

variable {n : ℕ} [NeZero n]

theorem proj_eZero : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0) (eZero (n := n)) = 1 := by
  rw [show (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0) (eZero (n := n))
      = (eZero (n := n)).ofLp 0 from PiLp.proj_apply 2 (fun _ : Fin n => ℝ) 0 (eZero (n := n)),
    eZero_apply]

/-- The standing data of the `C^∞` half-space graph theorem. -/
structure HalfSpaceGraphSetup (n : ℕ) [NeZero n] where
  Ψ : EuclideanSpace ℝ (Fin n) → ℝ
  p : EuclideanSpace ℝ (Fin n)
  hp0 : p.ofLp 0 = 0
  U : Set (EuclideanSpace ℝ (Fin n))
  hUopen : IsOpen U
  hpU : p ∈ U
  hCU : ContDiffOn ℝ ∞ Ψ (U ∩ Set.range (modelWithCornersEuclideanHalfSpace n))
  h0 : Ψ p = 0
  c : ℝ
  hc : c < 0
  hd : fderivWithin ℝ Ψ (Set.range (modelWithCornersEuclideanHalfSpace n)) p
      = c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0)
  hsign : ∀ᶠ z in 𝓝[Set.range (modelWithCornersEuclideanHalfSpace n)] p,
      z.ofLp 0 = 0 → 0 ≤ Ψ z

namespace HalfSpaceGraphSetup

variable (S : HalfSpaceGraphSetup n)

/-- The relative domain of the problem in `(u,s)`-coordinates. -/
def dom : Set (hsTang n × ℝ) := hsConn ⁻¹' (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n))

/-- The point `p` in `(u,s)`-coordinates. -/
def pt : hsTang n × ℝ := (hsMk S.p, 0)

/-- `F (u,s) = Ψ (u + s • e 0)`. -/
def F : hsTang n × ℝ → ℝ := fun x => S.Ψ (hsConn x)

/-- The within-derivative of `Ψ` at `hsConn x` with respect to the fixed relative domain. -/
def L (x : hsTang n × ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  fderivWithin ℝ S.Ψ (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) (hsConn x)

/-- The normal derivative of `Ψ` at `hsConn x`. -/
def Ds (x : hsTang n × ℝ) : ℝ := S.L x (eZero (n := n))

/-- The tangential derivative of `Ψ` at `hsConn x`, as a functional on the tangential hyperplane. -/
def Du (x : hsTang n × ℝ) : hsTang n →L[ℝ] ℝ := (S.L x).comp (Submodule.subtypeL (hsTang n))

/-- The candidate derivative of the graph function. -/
def A (x : hsTang n × ℝ) : hsTang n →L[ℝ] ℝ := (-(S.Ds x)⁻¹) • S.Du x

theorem mem_dom_iff {x : hsTang n × ℝ} :
    x ∈ S.dom ↔ hsConn x ∈ S.U ∧ 0 ≤ x.2 := by
  rw [dom, Set.mem_preimage, Set.mem_inter_iff, range_modelWithCornersEuclideanHalfSpace,
    Set.mem_ofPred_eq, hsConn_ofLp_zero]

theorem dom_of_mem (x : hsTang n × ℝ) (hx : x ∈ S.dom) : hsConn x ∈ S.U := (S.mem_dom_iff.mp hx).1

theorem dom_of_nhds {x : hsTang n × ℝ} (hx : hsConn x ∈ S.U) (hx2 : 0 ≤ x.2) : x ∈ S.dom :=
  S.mem_dom_iff.mpr ⟨hx, hx2⟩

theorem hsConn_pt : hsConn S.pt = S.p := by
  rw [show S.pt = (hsMk S.p, S.p.ofLp 0) from by rw [pt, S.hp0]]
  exact hsConn_mk S.p

theorem F_apply (u : hsTang n) (s : ℝ) : S.F (u, s) = S.Ψ (hsConn (u, s)) := rfl

theorem F_apply_pair (u : hsTang n) (s : ℝ) :
    S.F (u, s) = S.Ψ (((u : hsTang n) : EuclideanSpace ℝ (Fin n)) + s • eZero) := rfl

theorem F_pt : S.F S.pt = 0 := by
  rw [show S.pt = (hsMk S.p, S.p.ofLp 0) from by rw [pt, S.hp0]]
  rw [F_apply, hsConn_mk, S.h0]

theorem pt_mem_dom : S.pt ∈ S.dom := by
  rw [mem_dom_iff, hsConn_pt]
  exact ⟨S.hpU, le_refl 0⟩

theorem uniqueDiffOn_target :
    UniqueDiffOn ℝ (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) := by
  have h := (modelWithCornersEuclideanHalfSpace n).uniqueDiffOn
  rw [Set.inter_comm]
  exact h.inter S.hUopen

theorem contDiffOn_F : ContDiffOn ℝ ∞ S.F S.dom :=
  S.hCU.comp_continuousLinearMap hsConn

theorem contDiffOn_F_k (k : ℕ) : ContDiffOn ℝ (k : WithTop ℕ∞) S.F S.dom :=
  contDiffOn_infty.mp S.contDiffOn_F k

/-- The boundary sign hypothesis, two-sidedly near `p`. -/
theorem hsign_nhds : ∀ᶠ z in 𝓝 S.p, z.ofLp 0 = 0 → 0 ≤ S.Ψ z := by
  have h := S.hsign
  rw [eventually_nhdsWithin_iff] at h
  refine h.mono fun z hz hz0 => hz ?_ hz0
  rw [range_modelWithCornersEuclideanHalfSpace, Set.mem_ofPred_eq]
  rw [hz0]

theorem continuousWithinAt_L_at (x : hsTang n × ℝ) (hx : x ∈ S.dom) :
    ContinuousWithinAt S.L S.dom x := by
  have hx' : hsConn x ∈ S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n) := hx
  have hΨ : ContinuousWithinAt
      (fderivWithin ℝ S.Ψ (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)))
      (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) (hsConn x) :=
    (S.hCU.contDiffWithinAt hx').continuousWithinAt_fderivWithin S.uniqueDiffOn_target
      (by simp) hx'
  exact hΨ.comp (hsConn.continuous.continuousWithinAt) (fun y hy => hy)

theorem continuousWithinAt_L : ContinuousWithinAt S.L S.dom S.pt :=
  S.continuousWithinAt_L_at S.pt S.pt_mem_dom

theorem L_pt : S.L S.pt = S.c • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0) := by
  show fderivWithin ℝ S.Ψ (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) (hsConn S.pt)
    = S.c • _
  rw [hsConn_pt]
  have h1 : fderivWithin ℝ S.Ψ (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) S.p
      = fderivWithin ℝ S.Ψ (Set.range (modelWithCornersEuclideanHalfSpace n)) S.p := by
    rw [Set.inter_comm]
    exact fderivWithin_inter (S.hUopen.mem_nhds S.hpU)
  rw [h1, S.hd]

theorem Ds_pt : S.Ds S.pt = S.c := by
  rw [Ds, L_pt, ContinuousLinearMap.smul_apply, proj_eZero, smul_eq_mul, mul_one]

/-- `F` is differentiable within its domain with the explicit derivative `L x ∘ hsConn`. -/
theorem hasFDerivWithinAt_F (x : hsTang n × ℝ) (hx : x ∈ S.dom) :
    HasFDerivWithinAt S.F (S.L x ∘L hsConn) S.dom x := by
  have hx' : hsConn x ∈ S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n) := hx
  have hΨ : DifferentiableWithinAt ℝ S.Ψ
      (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) (hsConn x) :=
    ((contDiffOn_infty.mp S.hCU 1).differentiableOn (by simp)) (hsConn x) hx'
  exact (hΨ.hasFDerivWithinAt).comp x (hsConn.hasFDerivWithinAt) (fun y hy => hy)

theorem hsConn_inl (u : hsTang n) :
    hsConn (ContinuousLinearMap.inl ℝ (hsTang n) ℝ u)
      = ((u : hsTang n) : EuclideanSpace ℝ (Fin n)) := by
  rw [ContinuousLinearMap.inl_apply, hsConn_apply_pair]
  simp

theorem Du_apply (x : hsTang n × ℝ) (v : hsTang n) :
    S.Du x v = S.L x ((v : hsTang n) : EuclideanSpace ℝ (Fin n)) := rfl

theorem A_apply (x : hsTang n × ℝ) (v : hsTang n) :
    S.A x v = (-(S.Ds x)⁻¹) * S.L x ((v : hsTang n) : EuclideanSpace ℝ (Fin n)) := by
  simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, Du_apply,
    smul_eq_mul, neg_mul]

theorem continuousWithinAt_Ds_at (x : hsTang n × ℝ) (hx : x ∈ S.dom) :
    ContinuousWithinAt S.Ds S.dom x :=
  (S.continuousWithinAt_L_at x hx).clm_apply continuousWithinAt_const

theorem continuousWithinAt_Du_at (x : hsTang n × ℝ) (hx : x ∈ S.dom) :
    ContinuousWithinAt S.Du S.dom x :=
  (S.continuousWithinAt_L_at x hx).clm_comp continuousWithinAt_const

/-- **A box** on which all the local hypotheses of the proof hold uniformly: for every `u` in the
open ball `ball (hsMk S.p) ρ` and every `s ∈ [0,δ]`, the point `(u,s)` lies in the relative domain,
the derivative bound `‖L‖ ≤ M` and the strict negativity `Ds ≤ c/2` hold, and `F (u,0) ≥ 0`. -/
structure Box (ρ δ M : ℝ) : Prop where
  hρ : 0 < ρ
  hδ : 0 < δ
  hM : 0 < M
  hmem : ∀ u ∈ Metric.ball (hsMk S.p) ρ, ∀ s ∈ Set.Icc 0 δ, (u, s) ∈ S.dom
  hL : ∀ u ∈ Metric.ball (hsMk S.p) ρ, ∀ s ∈ Set.Icc 0 δ,
      ‖S.L (u, s)‖ ≤ M ∧ S.Ds (u, s) ≤ S.c / 2
  hsign : ∀ u ∈ Metric.ball (hsMk S.p) ρ, 0 ≤ S.F (u, 0) ∧ S.F (u, δ) < 0

/-- **A root function** on a box: `h u ∈ [0,δ]` is the (unique) zero of `s ↦ F (u,s)`. -/
structure Root {ρ δ M : ℝ} (B : S.Box ρ δ M) (h : hsTang n → ℝ) : Prop where
  hmem : ∀ u ∈ Metric.ball (hsMk S.p) ρ, h u ∈ Set.Icc 0 δ ∧ S.F (u, h u) = 0
  hcont : ContinuousOn h (Metric.ball (hsMk S.p) ρ)
  hchar : ∀ u ∈ Metric.ball (hsMk S.p) ρ, ∀ s ∈ Set.Icc 0 δ, (S.F (u, s) ≤ 0 ↔ h u ≤ s)
  hzero : h (hsMk S.p) = 0

/-- The `s`-slice `t ↦ F (u,t)` has derivative `Ds (u,s)` at `s`. -/
theorem hasFDerivWithinAt_F_slice {ρ δ M : ℝ} (B : S.Box ρ δ M) (b : ℝ)
    (hb : b ∈ Set.Icc 0 δ) (u : hsTang n) (hu : u ∈ Metric.ball (hsMk S.p) ρ) :
    HasFDerivWithinAt (fun v : hsTang n => S.F (v, b)) (S.Du (u, b))
      (Metric.ball (hsMk S.p) ρ) u := by
  have hF' := S.hasFDerivWithinAt_F (u, b) (B.hmem u hu b hb)
  have hφ : HasFDerivWithinAt (fun v : hsTang n => (v, b))
      (ContinuousLinearMap.inl ℝ (hsTang n) ℝ) (Metric.ball (hsMk S.p) ρ) u :=
    (hasFDerivAt_prodMk_left u b).hasFDerivWithinAt
  have h2 := hF'.comp u hφ (fun v hv => B.hmem v hv b hb)
  rw [show (S.L (u, b) ∘L hsConn) ∘L ContinuousLinearMap.inl ℝ (hsTang n) ℝ = S.Du (u, b) from by
    ext v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hsConn_inl]
    rfl] at h2
  exact h2


/-- The `s`-slice `t ↦ F (u,t)` has derivative `Ds (u,s)` at `s`. -/
theorem hasDerivAt_slice {ρ δ M : ℝ} (B : S.Box ρ δ M) {u : hsTang n}
    (hu : u ∈ Metric.ball (hsMk S.p) ρ) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) δ) :
    HasDerivAt (fun t : ℝ => S.F (u, t)) (S.Ds (u, s)) s := by
  have hsIcc : s ∈ Set.Icc 0 δ := Set.Ioo_subset_Icc_self hs
  have hF' := S.hasFDerivWithinAt_F (u, s) (B.hmem u hu s hsIcc)
  have hγ : HasDerivAt (fun t : ℝ => (u, t)) (0, (1 : ℝ)) s :=
    (hasDerivAt_const (x := s) u).prodMk (hasDerivAt_id s)
  have hmaps : MapsTo (fun t : ℝ => (u, t)) (Set.Ioo (0 : ℝ) δ) S.dom :=
    fun t ht => B.hmem u hu t (Set.Ioo_subset_Icc_self ht)
  have h2 := hF'.comp_hasDerivWithinAt s hγ.hasDerivWithinAt hmaps
  have hval : ((S.L (u, s) ∘L hsConn) ((0 : hsTang n), (1 : ℝ))) = S.Ds (u, s) := by
    rw [ContinuousLinearMap.comp_apply]
    show S.L (u, s) (hsConn ((0 : hsTang n), (1 : ℝ))) = S.L (u, s) eZero
    rw [hsConn_apply_pair]
    simp
  rw [hval] at h2
  have h3 : HasDerivAt (fun t : ℝ => S.F (u, t)) (S.Ds (u, s)) s :=
    h2.hasDerivAt (isOpen_Ioo.mem_nhds hs)
  exact h3

/-- The signed mean-value bound for the slices `s ↦ F (u,s)`. -/
theorem slice_mem_Icc {ρ δ M : ℝ} (B : S.Box ρ δ M) {u : hsTang n}
    (hu : u ∈ Metric.ball (hsMk S.p) ρ) {a b : ℝ} (ha : a ∈ Set.Icc 0 δ)
    (hb : b ∈ Set.Icc 0 δ) (hab : a ≤ b) :
    S.F (u, b) - S.F (u, a) ∈ Set.Icc (-M * (b - a)) (S.c / 2 * (b - a)) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) δ := fun x hx =>
    ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩
  refine derivBoundIcc (φ := fun t : ℝ => S.F (u, t)) hab ?_ ?_ ?_ ?_
  · have hcont0 : ContinuousOn (fun t : ℝ => S.F (u, t)) (Set.Icc 0 δ) := by
      have h1 : ContinuousOn (fun t : ℝ => (u, t)) (Set.Icc 0 δ) :=
        (continuous_const.prodMk continuous_id).continuousOn
      have hFc : ContinuousOn S.F S.dom := S.contDiffOn_F.continuousOn
      exact hFc.comp h1 (fun t ht => B.hmem u hu t ht)
    exact hcont0.mono (Set.Icc_subset_Icc ha.1 hb.2)
  · intro x hx
    exact ((S.hasDerivAt_slice B hu (hsub hx)).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [(S.hasDerivAt_slice B hu (hsub hx)).deriv]
    have hL := (B.hL u hu x (Set.Ioo_subset_Icc_self (hsub hx))).1
    have h2 : -(S.Ds (u, x)) ≤ ‖S.L (u, x)‖ := by
      calc -(S.Ds (u, x)) ≤ |S.Ds (u, x)| := neg_le_abs _
        _ = ‖S.Ds (u, x)‖ := (Real.norm_eq_abs _).symm
        _ = ‖S.L (u, x) eZero‖ := rfl
        _ ≤ ‖S.L (u, x)‖ * ‖eZero (n := n)‖ := (S.L (u, x)).le_opNorm _
        _ = ‖S.L (u, x)‖ := by rw [eZero_norm, mul_one]
    linarith
  · intro x hx
    rw [(S.hasDerivAt_slice B hu (hsub hx)).deriv]
    exact (B.hL u hu x (Set.Ioo_subset_Icc_self (hsub hx))).2

/-- The slices are strictly decreasing. -/
theorem slice_strictAntiOn {ρ δ M : ℝ} (B : S.Box ρ δ M) {u : hsTang n}
    (hu : u ∈ Metric.ball (hsMk S.p) ρ) :
    StrictAntiOn (fun s : ℝ => S.F (u, s)) (Set.Icc 0 δ) := by
  intro a ha b hb hab
  have h := (S.slice_mem_Icc B hu ha hb hab.le).2
  have hc2 : S.c / 2 < 0 := by linarith [S.hc]
  have hneg : S.c / 2 * (b - a) < 0 := mul_neg_of_neg_of_pos hc2 (sub_pos.mpr hab)
  linarith


/-- The derivative field `L` is `C^m` on the relative domain. -/
theorem contDiffOn_L (m : ℕ) : ContDiffOn ℝ (m : WithTop ℕ∞) S.L S.dom := by
  have h1 : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞)
      (fderivWithin ℝ S.Ψ (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)))
      (S.U ∩ Set.range (modelWithCornersEuclideanHalfSpace n)) := by
    refine (contDiffOn_infty.mp S.hCU (m + 1)).fderivWithin S.uniqueDiffOn_target ?_
    simp
  exact h1.comp_continuousLinearMap hsConn

/-- The normal derivative `Ds` is `C^m` on the relative domain. -/
theorem contDiffOn_Ds (m : ℕ) : ContDiffOn ℝ (m : WithTop ℕ∞) S.Ds S.dom := by
  show ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => S.L x (eZero (n := n))) S.dom
  exact (S.contDiffOn_L m).clm_apply contDiffOn_const

/-- The tangential derivative `Du` is `C^m` on the relative domain. -/
theorem contDiffOn_Du (m : ℕ) : ContDiffOn ℝ (m : WithTop ℕ∞) S.Du S.dom := by
  show ContDiffOn ℝ (m : WithTop ℕ∞)
    (fun x => (S.L x).comp (Submodule.subtypeL (hsTang n))) S.dom
  exact (S.contDiffOn_L m).clm_comp contDiffOn_const

end HalfSpaceGraphSetup

end

end Work.PTGeometric.WeakRegion
