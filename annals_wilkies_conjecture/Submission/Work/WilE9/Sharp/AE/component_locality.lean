/-
  WilE9 / Sharp / AE — component locality of an effectively smooth stratum.

  The third conjunct of `EffStratum.Good` is *ambient locality*: near every point `z` of a
  stratum's set the zero set of the `1 + m` equations coincides with the stratum's set.  What
  the extended-system construction (and only that) consumes is the *component* form of it: a
  point near `z` at which the equations vanish does not merely lie in `E.X.set`, it lies in the
  same connected component of `E.X.set` as `z`.

  This is a genuine consequence of the implicit function theorem: `Good` also gives that the
  fibre Jacobian `∂h/∂(fibre)` is invertible at `z`, so the zero set of `h` near `z` is the
  graph of a smooth function of the `n` base coordinates; a graph over a ball is connected, and
  the points of the graph over a small ball satisfy the equations.  Hence any near-by zero of
  the equations is joined to `z` inside `E.X.set`.

  The file is organised as

  * `baseOf` / `fibreOf` / `append_baseOf_fibreOf`: the identification
    `ℝ^{n+q} ≃ ℝⁿ × ℝ^q` via `Fin.castAdd` / `Fin.natAdd` / `Fin.append`;
  * `append_mem_connectedComponentIn`: connected components are carried along a continuous map;
  * `graphEval_eq_zero_iff`: the pointwise reading of `graphEval`'s zero set;
  * `zero_set_component_locality_aux`: the analytic core (`Work.WilE9.Sharp.AE.
    zero_set_component_locality` proves the same statement in its own file);
  * `component_locality`: the goal, obtained by applying the core to the graph map
    `graphEval E.X.c E.h` and transporting along `Fin.append`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.AE.Basic
import Submission.Work.WilE9.Ift.ift_exists

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Filter Topology
open scoped Topology
namespace Work.WilE9.Sharp.AE

open WilkiesDesign WilkiesDesign.E

/-! ## The identification `ℝ^{n+q} ≃ ℝⁿ × ℝ^q` -/

section Coords

variable {n q : ℕ}

/-- The first `n` coordinates of a point of `ℝ^{n+q}` (the "base" coordinates). -/
def baseOf (z : Fin (n + q) → ℝ) : Fin n → ℝ := fun i => z (Fin.castAdd q i)

/-- The last `q` coordinates of a point of `ℝ^{n+q}` (the "fibre" coordinates). -/
def fibreOf (z : Fin (n + q) → ℝ) : Fin q → ℝ := fun l => z (Fin.natAdd n l)

/-- `Fin.append` is the inverse of `(baseOf, fibreOf)`. -/
theorem append_baseOf_fibreOf (z : Fin (n + q) → ℝ) :
    Fin.append (baseOf z) (fibreOf z) = z := by
  funext s
  refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;> simp [baseOf, fibreOf]

/-- `baseOf` is a left inverse of `Fin.append`. -/
theorem baseOf_append (x : Fin n → ℝ) (y : Fin q → ℝ) :
    baseOf (Fin.append x y) = x := by
  funext i
  simp [baseOf]

/-- `fibreOf` is a left inverse of `Fin.append`. -/
theorem fibreOf_append (x : Fin n → ℝ) (y : Fin q → ℝ) :
    fibreOf (Fin.append x y) = y := by
  funext l
  simp [fibreOf]

theorem continuous_baseOf : Continuous fun z : Fin (n + q) → ℝ => baseOf z :=
  continuous_pi fun i => continuous_apply (Fin.castAdd q i)

theorem continuous_fibreOf : Continuous fun z : Fin (n + q) → ℝ => fibreOf z :=
  continuous_pi fun l => continuous_apply (Fin.natAdd n l)

theorem continuous_pairOf :
    Continuous fun z : Fin (n + q) → ℝ => (baseOf z, fibreOf z) :=
  continuous_baseOf.prodMk continuous_fibreOf

end Coords

/-! ## `Fin.append` as a map of pairs -/

theorem continuous_appendPair {n q : ℕ} :
    Continuous fun p : (Fin n → ℝ) × (Fin q → ℝ) => Fin.append p.1 p.2 := by
  have h := (Work.WilE9.Ift.appendCLM n q).continuous
  rwa [Work.WilE9.Ift.coe_appendCLM] at h

/-- **Components are carried along `Fin.append`.**  If `T` sits over `X` (every pair of `T`
maps into `X` under `Fin.append`) and `u ∈ T`, then the `Fin.append`-image of the component of
`u` in `T` lies in the component of its image in `X`. -/
theorem append_mem_connectedComponentIn {n q : ℕ} {X : Set (Fin (n + q) → ℝ)}
    {T : Set ((Fin n → ℝ) × (Fin q → ℝ))} (hT : ∀ p ∈ T, Fin.append p.1 p.2 ∈ X)
    {u : (Fin n → ℝ) × (Fin q → ℝ)} (hu : u ∈ T)
    {p : (Fin n → ℝ) × (Fin q → ℝ)} (hp : p ∈ connectedComponentIn T u) :
    Fin.append p.1 p.2 ∈ connectedComponentIn X (Fin.append u.1 u.2) := by
  have hcont := continuous_appendPair (n := n) (q := q)
  have himg : Fin.append p.1 p.2 ∈
      (fun p : (Fin n → ℝ) × (Fin q → ℝ) => Fin.append p.1 p.2) ''
        connectedComponentIn T u :=
    ⟨p, hp, rfl⟩
  refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_ himg
  · exact (isPreconnected_connectedComponentIn (F := T) (x := u)).image _
      hcont.continuousOn
  · exact ⟨u, IsPreconnected.subset_connectedComponentIn (s := {u}) (x := u) (F := T)
      isPreconnected_singleton rfl (by rw [Set.singleton_subset_iff]; exact hu)
      (Set.mem_singleton u), rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hT w (connectedComponentIn_subset T u hw)

/-! ## The zero set of `graphEval`, pointwise -/

theorem graphEval_eq_zero_iff {n q r : ℕ} (c : EAChain (n + q) r)
    (F : Fin q → EAPoly (n + q) r) (v : (Fin n → ℝ) × (Fin q → ℝ)) :
    Work.WilE9.Ift.graphEval c F v = 0 ↔
      ∀ j, eaEval c (F j) (Fin.append v.1 v.2) = 0 := by
  rw [funext_iff]
  simp only [Work.WilE9.Ift.graphEval_apply, Pi.zero_apply]

/-! ## The analytic core: the zero set of an invertible system is locally a graph -/

/-- **Local-connectedness form of the implicit function theorem.**  Let `F : ℝⁿ × ℝ^q → ℝ^q`
be `C^∞` near `u`, with `F u = 0` and with the derivative in the second block invertible.  If
the zeros of `F` close to `u` lie in a set `T`, then every zero of `F` close enough to `u` lies
in the connected component of `u` in `T`.

The proof is the one of the implicit function theorem: the zeros of `F` near `u` are the graph
of the implicit function `g` of the first variable, which is smooth, so the graph over a small
ball is connected and consists of zeros; by the hypothesis it lies in `T`, and every near-by
zero is on it.

(This statement is also proved, in its own file, as
`Work.WilE9.Sharp.AE.zero_set_component_locality`.) -/
theorem zero_set_component_locality_aux {n q : ℕ}
    (F : ((Fin n → ℝ) × (Fin q → ℝ)) → (Fin q → ℝ))
    (u : (Fin n → ℝ) × (Fin q → ℝ))
    (hcdf : ContDiffAt ℝ ⊤ F u) (hF0 : F u = 0)
    (hif : ((fderiv ℝ F u) ∘SL ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin q → ℝ)).IsInvertible)
    (T : Set ((Fin n → ℝ) × (Fin q → ℝ)))
    (hT : ∀ᶠ v in 𝓝 u, F v = 0 → v ∈ T) :
    ∀ᶠ v in 𝓝 u, F v = 0 → v ∈ connectedComponentIn T u := by
  classical
  have hpn : (⊤ : WithTop ℕ∞) ≠ 0 := (WithTop.coe_lt_top (0 : ℕ∞)).ne'
  set g : (Fin n → ℝ) → (Fin q → ℝ) := hcdf.implicitFunction hpn hif with hg
  have hg0 : g u.1 = u.2 := hcdf.implicitFunction_apply_self hpn hif
  have hgcd : ContDiffAt ℝ ⊤ g u.1 := hcdf.contDiffAt_implicitFunction hpn hif
  -- the zeros of `F` near `u` are exactly the graph of `g`
  have huniq : ∀ᶠ v in 𝓝 u, F v = 0 → g v.1 = v.2 := by
    have h := hcdf.eventually_apply_eq_iff_implicitFunction hpn hif
    filter_upwards [h] with v hv hv0
    exact hv.mp (by rw [hv0, hF0])
  have hgr : ∀ᶠ x in 𝓝 u.1, F (x, g x) = 0 := by
    have h := hcdf.eventually_apply_implicitFunction hpn hif
    filter_upwards [h] with x hx
    rw [hx, hF0]
  -- extract the radii
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp huniq
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hT
  -- the graph of `g` stays close to `u` (hence, by `hT`, in `T`) as `x` approaches `u.1`
  have hgball : ∀ᶠ x in 𝓝 u.1, dist (g x) u.2 < δ₂ := by
    have h := hgcd.continuousAt.eventually (Metric.ball_mem_nhds (g u.1) hδ₂pos)
    filter_upwards [h] with x hx
    rwa [hg0] at hx
  have hdist : ∀ᶠ x in 𝓝 u.1, dist (x, g x) u < δ₂ := by
    filter_upwards [Metric.ball_mem_nhds u.1 hδ₂pos, hgball] with x hx1 hx2
    rw [Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hx1) hx2
  have hΓT : ∀ᶠ x in 𝓝 u.1, (x, g x) ∈ T := by
    filter_upwards [hdist, hgr] with x hx1 hx2
    exact hδ₂ hx1 hx2
  obtain ⟨ρT, hρTpos, hρT⟩ := Metric.eventually_nhds_iff.mp hΓT
  obtain ⟨s, hs_mem, hgs⟩ := hgcd.contDiffOn le_rfl (fun _ => rfl)
  obtain ⟨ρs, hρspos, hρs⟩ := Metric.mem_nhds_iff.mp hs_mem
  have hball_sub : Metric.closedBall u.1 (ρs / 2) ⊆ s := fun x hx =>
    hρs (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)))
  set ρ : ℝ := min ρT (min (ρs / 2) δ₁) / 2 with hρdef
  have hmid_pos : 0 < min ρT (min (ρs / 2) δ₁) :=
    lt_min hρTpos (lt_min (by linarith) hδ₁pos)
  have hρ_pos : 0 < ρ := by rw [hρdef]; linarith
  have hρT' : ρ < ρT := by
    have h1 : min ρT (min (ρs / 2) δ₁) ≤ ρT := min_le_left _ _
    rw [hρdef]; linarith
  have hρs' : ρ < ρs / 2 := by
    have h1 : min ρT (min (ρs / 2) δ₁) ≤ ρs / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    rw [hρdef]; linarith
  have hδ₁' : ρ < δ₁ := by
    have h1 : min ρT (min (ρs / 2) δ₁) ≤ δ₁ :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    rw [hρdef]; linarith
  -- the graph over the closed ball is a connected piece of `T` containing `u`
  have hcontOn : ContinuousOn (fun x : Fin n → ℝ => (x, g x)) (Metric.closedBall u.1 ρ) :=
    continuousOn_id.prodMk (hgs.continuousOn.mono fun x hx =>
      hball_sub (Metric.closedBall_subset_closedBall (by linarith) hx))
  have hSpre : IsPreconnected
      ((fun x : Fin n → ℝ => (x, g x)) '' Metric.closedBall u.1 ρ) :=
    (convex_closedBall u.1 ρ).isPreconnected.image _ hcontOn
  have huS : u ∈ (fun x : Fin n → ℝ => (x, g x)) '' Metric.closedBall u.1 ρ :=
    ⟨u.1, by rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hρ_pos,
      by show (u.1, g u.1) = u; rw [hg0]⟩
  have hST : (fun x : Fin n → ℝ => (x, g x)) '' Metric.closedBall u.1 ρ ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hρT (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hρT'))
  have hScomp : (fun x : Fin n → ℝ => (x, g x)) '' Metric.closedBall u.1 ρ ⊆
      connectedComponentIn T u :=
    IsPreconnected.subset_connectedComponentIn hSpre huS hST
  -- every zero of `F` in the ball of radius `ρ` is on that graph
  refine Metric.eventually_nhds_iff.mpr ⟨ρ, hρ_pos, fun v hv hv0 => ?_⟩
  have hv2 : g v.1 = v.2 := hδ₁ (lt_of_lt_of_le hv (le_of_lt hδ₁')) hv0
  refine hScomp ⟨v.1, ?_, ?_⟩
  · rw [Metric.mem_closedBall]
    calc dist v.1 u.1 ≤ dist v u := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ ≤ ρ := le_of_lt hv
  · show (v.1, g v.1) = v
    exact Prod.ext rfl hv2

/-! ## The goal -/

theorem component_locality {n m : ℕ} (E : Work.WilE9.Sharp.EffStratum n m)
    (hgood : E.Good) :
    ∀ z ∈ E.X.set, ∀ᶠ z' in nhds z, (∀ a, WilkiesDesign.E.eaEval E.X.c (E.h a) z' = 0) →
      z' ∈ connectedComponentIn E.X.set z := by
  intro z hz
  obtain ⟨hz0, hzdet, hzloc⟩ := hgood z hz
  -- the ambient point as a pair `(base, fibre)`
  set u : (Fin n → ℝ) × (Fin (1 + m) → ℝ) := (baseOf z, fibreOf z) with hu
  have hzu : Fin.append u.1 u.2 = z := by
    rw [hu]
    exact append_baseOf_fibreOf z
  -- the graph map of the equations is `C^∞` at `u`
  have hcdf : ContDiffAt ℝ ⊤ (Work.WilE9.Ift.graphEval E.X.c E.h) u :=
    (Work.WilE9.Ift.graphEval_contDiff E.X.c E.h).contDiffAt
  have hF0 : Work.WilE9.Ift.graphEval E.X.c E.h u = 0 := by
    rw [graphEval_eq_zero_iff]
    intro j
    rw [hzu]
    exact hz0 j
  have hpn : (⊤ : WithTop ℕ∞) ≠ 0 := (WithTop.coe_lt_top (0 : ℕ∞)).ne'
  -- the fibre Jacobian at `u` is the one `Good` gives at `z`
  set A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ :=
    Matrix.of fun j l => eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h j)) (Fin.append u.1 u.2)
    with hA
  have hAdet : A.det ≠ 0 := by
    rw [hA, hzu]
    exact hzdet
  have hAunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hAdet
  have hif : ((fderiv ℝ (Work.WilE9.Ift.graphEval E.X.c E.h) u)
      ∘SL ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin (1 + m) → ℝ)).IsInvertible := by
    have hpt : ∀ v : Fin (1 + m) → ℝ,
        ((fderiv ℝ (Work.WilE9.Ift.graphEval E.X.c E.h) u)
          ∘SL ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin (1 + m) → ℝ)) v =
            Matrix.mulVec A v := by
      intro v
      rw [(Work.WilE9.Ift.hasFDerivAt_graphEval E.X.c E.h u.1 u.2).fderiv, hA]
      exact Work.WilE9.Ift.graphEval_snd E.X.c E.h u.1 u.2 v
    refine ⟨(Matrix.toLinearEquiv' A (Matrix.invertibleOfIsUnitDet A hAunit)).toContinuousLinearEquiv,
      ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    rw [hpt v]
    change (Matrix.toLin' A) v = Matrix.mulVec A v
    exact Matrix.toLin'_apply A v
  -- `Good`'s locality, read on the graph map
  have hT : ∀ᶠ v in 𝓝 u, Work.WilE9.Ift.graphEval E.X.c E.h v = 0 →
      Fin.append v.1 v.2 ∈ E.X.set := by
    have htend : Tendsto (fun v : (Fin n → ℝ) × (Fin (1 + m) → ℝ) => Fin.append v.1 v.2)
        (𝓝 u) (𝓝 z) := by
      rw [← hzu]
      exact continuous_appendPair.continuousAt
    have h1 := htend.eventually hzloc
    filter_upwards [h1] with v hv hFv
    exact hv ((graphEval_eq_zero_iff E.X.c E.h v).mp hFv)
  -- the analytic core
  have hcore : ∀ᶠ v in 𝓝 u, Work.WilE9.Ift.graphEval E.X.c E.h v = 0 →
      v ∈ connectedComponentIn
        {p : (Fin n → ℝ) × (Fin (1 + m) → ℝ) | Fin.append p.1 p.2 ∈ E.X.set} u :=
    zero_set_component_locality_aux (Work.WilE9.Ift.graphEval E.X.c E.h) u hcdf hF0 hif
      {p : (Fin n → ℝ) × (Fin (1 + m) → ℝ) | Fin.append p.1 p.2 ∈ E.X.set} hT
  -- transport back to the ambient coordinates
  have hstep : ∀ᶠ z' in 𝓝 z,
      Work.WilE9.Ift.graphEval E.X.c E.h (baseOf z', fibreOf z') = 0 →
        z' ∈ connectedComponentIn E.X.set z := by
    have htend2 : Tendsto (fun z' : Fin (n + (1 + m)) → ℝ => (baseOf z', fibreOf z'))
        (𝓝 z) (𝓝 u) := by
      rw [hu]
      exact continuous_pairOf.continuousAt
    have h1 := htend2.eventually hcore
    filter_upwards [h1] with z' hz' hFz'
    have hp : (baseOf z', fibreOf z') ∈ connectedComponentIn
        {p : (Fin n → ℝ) × (Fin (1 + m) → ℝ) | Fin.append p.1 p.2 ∈ E.X.set} u :=
      hz' hFz'
    have htr : Fin.append (baseOf z') (fibreOf z') ∈ connectedComponentIn E.X.set z := by
      have h := append_mem_connectedComponentIn (X := E.X.set)
        (T := {p : (Fin n → ℝ) × (Fin (1 + m) → ℝ) | Fin.append p.1 p.2 ∈ E.X.set})
        (fun p hp => hp) (by
          show Fin.append u.1 u.2 ∈ E.X.set
          rw [hzu]
          exact hz) hp
      rwa [hzu] at h
    rwa [append_baseOf_fibreOf z'] at htr
  filter_upwards [hstep] with z' hz' hz0'
  exact hz' ((graphEval_eq_zero_iff E.X.c E.h (baseOf z', fibreOf z')).mpr fun a => by
    rw [append_baseOf_fibreOf z']
    exact hz0' a)

end Work.WilE9.Sharp.AE
