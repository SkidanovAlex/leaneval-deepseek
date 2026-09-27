import Mathlib
import Submission.Work.Projection.mfderiv_chartAt_decomp
import Submission.Work.Embedding.smooth_implicit_function_nhd
import Submission.Work.Whitney.taylor_second_order_ball
import Submission.Work.Whitney.coprod_equiv_of_range_sup
import Submission.Work.Projection.compact_embedding

/-!
# The local sheet model at a transverse double point of an immersion

This file proves `Work.Whitney.exists_sheet_model`.  Given a smooth map `f : M → ℝ^{2n}` of a
smooth `n`-manifold which at `p₁ ≠ p₂` has a *transverse* double point (`f p₁ = f p₂` and the two
tangent images span `ℝ^{2n}`), the two branches through the double point can be written, in a
suitable linear identification `Φ : ℝ^{2n} ≃L ℝⁿ × ℝⁿ`, as graphs `u ↦ (u, hᵢ u)` over the first
factor of a neighbourhood of `0`; moreover `h₂` vanishes to second order and `h₁ - h₂` is
approximately the (invertible) linear map `A = Dh₁(0) - Dh₂(0)`.

The construction is the inverse function theorem for the two "coordinate projections" `gᵢ` obtained
by composing `f` with `Φ` and projecting to the first factor: the sheet `σᵢ` is the local inverse of
`gᵢ` at `pᵢ`, smoothly extended off a small ball by a cut-off.  The quantitative statements then
follow from Taylor's formula on a ball.
-/

namespace Work.Whitney

set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Topology NNReal
open Topology Metric

/-! ## Elementary analytic tools -/

/-- **Second order Taylor bound on a ball** (general target dimension).  A `C^∞` map between
Euclidean spaces is equal to its first order Taylor polynomial up to an error `O (‖h‖²)` on any
ball.  This is `Work.Whitney.taylor_second_order_ball` with the target dimension made arbitrary. -/
theorem taylor_second_order_ball_gen {n N : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (p : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ r →
      ‖G (p + h) - G p - fderiv ℝ G p h‖ ≤ C * ‖h‖ ^ 2 := by
  have hGdiff : Differentiable ℝ G := (contDiff_infty_iff_fderiv.1 hG).1
  have hG' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ G) :=
    (contDiff_infty_iff_fderiv.1 hG).2
  have h1 : ContDiffOn ℝ (1 : WithTop ℕ∞) (fderiv ℝ G) (closedBall p r) :=
    (hG'.of_le (m := 1) (by norm_num)).contDiffOn
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, LipschitzOnWith L (fderiv ℝ G) (closedBall p r) :=
    ContDiffOn.exists_lipschitzOnWith h1 (by norm_num)
      (convex_closedBall p r) (isCompact_closedBall p r)
  refine ⟨(L : ℝ) + 1, by positivity, ?_⟩
  intro h hh
  have hconv : Convex ℝ (closedBall p ‖h‖) := convex_closedBall p ‖h‖
  have hmem_p : p ∈ closedBall p ‖h‖ := by simp [mem_closedBall]
  have hmem_ph : p + h ∈ closedBall p ‖h‖ := by
    rw [mem_closedBall, dist_eq_norm]
    simp
  have hder : ∀ x ∈ closedBall p ‖h‖,
      HasFDerivWithinAt G (fderiv ℝ G x) (closedBall p ‖h‖) x :=
    fun x _ => ((hGdiff x).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ x ∈ closedBall p ‖h‖, ‖fderiv ℝ G x - fderiv ℝ G p‖ ≤ (L : ℝ) * ‖h‖ := by
    intro x hx
    have hxr : x ∈ closedBall p r := by
      rw [mem_closedBall] at hx ⊢
      exact le_trans hx hh
    have hp_r : p ∈ closedBall p r := by
      rw [mem_closedBall]
      simpa using hr.le
    have hd := hL.dist_le_mul x hxr p hp_r
    rw [dist_eq_norm, dist_eq_norm] at hd
    have hxp : ‖x - p‖ ≤ ‖h‖ := by
      rw [← dist_eq_norm]; exact hx
    calc ‖fderiv ℝ G x - fderiv ℝ G p‖ ≤ (L : ℝ) * ‖x - p‖ := hd
      _ ≤ (L : ℝ) * ‖h‖ := mul_le_mul_of_nonneg_left hxp (by positivity)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := G) (f' := fun x => fderiv ℝ G x) (φ := fderiv ℝ G p)
      hder hbound hconv hmem_p hmem_ph
  simp only [add_sub_cancel_left] at key
  calc ‖G (p + h) - G p - fderiv ℝ G p h‖ ≤ (L : ℝ) * ‖h‖ * ‖h‖ := key
    _ = (L : ℝ) * ‖h‖ ^ 2 := by ring
    _ ≤ ((L : ℝ) + 1) * ‖h‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖h‖)
        linarith

/-- **A smooth cut-off.**  For `0 < R < R'` there is a smooth function equal to `1` on the closed
ball of radius `R`, vanishing outside the ball of radius `R'`, with values in `[0,1]`. -/
theorem exists_smooth_cutoff {n : ℕ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R') :
    ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ u, 0 ≤ χ u ∧ χ u ≤ 1) ∧
      (∀ u, ‖u‖ ≤ R → χ u = 1) ∧ (∀ u, R' ≤ ‖u‖ → χ u = 0) := by
  let hb : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨R, R', hR, hRR'⟩
  have hRin : hb.rIn = R := rfl
  have hRout : hb.rOut = R' := rfl
  refine ⟨hb, hb.contDiff, fun u => ⟨hb.nonneg' u, hb.le_one⟩, ?_, ?_⟩
  · intro u hu
    refine hb.one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, hRin]
    exact hu
  · intro u hu
    refine hb.zero_of_le_dist ?_
    rw [dist_eq_norm, hRout]
    simpa using hu


/-! ## The chart representation of a smooth map with invertible derivative -/

/-- **The chart representation at a point is smooth with injective derivative.**  If `g : M → ℝⁿ`
is a smooth map on an `n`-manifold and its manifold derivative at `p` is injective, then the
coordinate representation `y ↦ g ((chartAt ℝⁿ p).symm y)` is `C^∞` on the chart target and its
Fréchet derivative at the image `chartAt ℝⁿ p` of `p` is injective. -/
theorem chartRep_smooth_and_fderiv_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (g : M → EuclideanSpace ℝ (Fin n))
    (hg : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (p : M) (hinj : Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) g p)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) =>
          g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
        (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
      Function.Injective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
          g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)) := by
  classical
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) p
  -- smoothness of the inverse chart on its target, composed with `g`
  have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (c.symm : EuclideanSpace ℝ (Fin n) → M) c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) p)
  have hcomp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin n) => g (c.symm y)) c.target :=
    ContMDiffOn.comp (t := Set.univ) (hg.contMDiffOn (s := Set.univ)) hsymm
      (fun y _ => Set.mem_univ _)
  refine ⟨?_, ?_⟩
  · exact contMDiffOn_iff_contDiffOn.mp hcomp
  · -- injectivity of the derivative at `c p`
    have hpsrc : p ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) p
    have hptgt : c p ∈ c.target := c.map_source hpsrc
    have hdec := Work.Projection.mfderiv_chartAt_decomp g hg p p hpsrc
    -- the pointwise form of the chain rule
    have hdpoint : ∀ x : TangentSpace (𝓡 n) p,
        mfderiv (𝓡 n) (𝓡 n) g p x
          = fderiv ℝ (fun y => g (c.symm y)) (c p) (mfderiv (𝓡 n) (𝓡 n) c p x) := by
      intro x
      exact congrFun (congrArg DFunLike.coe hdec) x
    have hsurj : Function.Surjective (mfderiv (𝓡 n) (𝓡 n) c p) :=
      (mdifferentiable_chart (I := 𝓡 n) p).mfderiv_surjective hpsrc
    intro a b hab
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    have h0 : mfderiv (𝓡 n) (𝓡 n) g p a' = mfderiv (𝓡 n) (𝓡 n) g p b' := by
      rw [hdpoint a', hdpoint b']
      exact hab
    exact congrArg (mfderiv (𝓡 n) (𝓡 n) c p) (hinj h0)

/-! ## The inverse function theorem with a smooth local inverse on an open set -/

/-- **The inverse function theorem, in the form "the local inverse is smooth on an open set".**
Let `G : E → E` be `C^∞` on an open set `V ∋ a` (with `E` a finite dimensional real vector space)
and suppose `fderiv ℝ G a` is injective (hence invertible).  Then there are an open neighbourhood
`O` of `G a` and a total function `L : E → E` which is `C^∞` on `O`, is a right inverse of `G` on
`O` (`G (L y) = y`), maps `O` into a fixed open neighbourhood `W ⊆ V` of `a`, and is the unique
inverse of `G` among points of `W`. -/
theorem exists_localInverse_smooth_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : E → E) (V : Set E) (hV : IsOpen V) (a : E) (ha : a ∈ V)
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G V)
    (hd : Function.Injective (fderiv ℝ G a)) :
    ∃ (L : E → E) (O W : Set E),
      IsOpen O ∧ G a ∈ O ∧ IsOpen W ∧ a ∈ W ∧ W ⊆ V ∧
      L (G a) = a ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L O ∧
      (∀ y ∈ O, L y ∈ W) ∧
      (∀ y ∈ O, G (L y) = y) ∧
      (∀ y ∈ O, ∀ z ∈ W, G z = y → z = L y) := by
  classical
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have haV : V ∈ 𝓝 a := hV.mem_nhds ha
  have hGat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G a := hG.contDiffAt haV
  -- the derivative at `a` is a continuous linear equivalence
  have hda : HasFDerivAt G (fderiv ℝ G a) a := (hGat.differentiableAt hnz).hasFDerivAt
  have hker : (fderiv ℝ G a).ker = ⊥ := LinearMap.ker_eq_bot.mpr hd
  have hrange : (fderiv ℝ G a).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hd)
  let e₀ : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective (fderiv ℝ G a) hker hrange
  have he₀ : (e₀ : E →L[ℝ] E) = fderiv ℝ G a := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hda₀ : HasFDerivAt G (e₀ : E →L[ℝ] E) a := hda.congr_fderiv he₀.symm
  -- the inverse function theorem of Mathlib: a partial homeomorphism with `toFun = G`
  let e : OpenPartialHomeomorph E E := hGat.toOpenPartialHomeomorph G hda₀ hnz
  have he_coe : (e : E → E) = G := ContDiffAt.toOpenPartialHomeomorph_coe hGat hda₀ hnz
  have ha_src : a ∈ e.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hGat hda₀ hnz
  have hGa_tgt : G a ∈ e.target :=
    ContDiffAt.image_mem_toOpenPartialHomeomorph_target hGat hda₀ hnz
  -- a ball around `a` on which the derivative stays invertible and which lies in `V ∩ e.source`
  have hcont : ContinuousAt (fderiv ℝ G) a := hGat.continuousAt_fderiv hnz
  have hInv : (fderiv ℝ G a).IsInvertible := ⟨e₀, he₀⟩
  have hnhds : {y : E | (fderiv ℝ G y).IsInvertible} ∈ 𝓝 a :=
    hcont.preimage_mem_nhds
      (Work.Embedding.isOpen_isInvertible.mem_nhds hInv)
  have hball : {y : E | (fderiv ℝ G y).IsInvertible} ∩ V ∩ e.source ∈ 𝓝 a :=
    Filter.inter_mem (Filter.inter_mem hnhds haV) (e.open_source.mem_nhds ha_src)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hball
  -- the data
  refine ⟨fun y => e.symm y, e.target ∩ (fun y => e.symm y) ⁻¹' Metric.ball a ρ,
    Metric.ball a ρ, ?_, ?_, isOpen_ball, mem_ball_self hρpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `O` is open
    refine isOpen_iff_mem_nhds.mpr fun y hy => ?_
    have hy_tgt : y ∈ e.target := hy.1
    exact Filter.inter_mem (e.open_target.mem_nhds hy_tgt)
      ((e.continuousAt_symm hy_tgt).preimage_mem_nhds (isOpen_ball.mem_nhds hy.2))
  · -- `G a ∈ O`
    refine ⟨hGa_tgt, ?_⟩
    show e.symm (G a) ∈ Metric.ball a ρ
    have hsymm : e.symm (G a) = a := by
      have h1 : e a = G a := congrFun he_coe a
      rw [← h1]
      exact OpenPartialHomeomorph.left_inv _ ha_src
    rw [hsymm]
    exact mem_ball_self hρpos
  · -- `W ⊆ V`
    intro y hy
    exact (hρsub hy).1.2
  · -- the value at `G a`
    show (fun y => e.symm y) (G a) = a
    have h1 : e a = G a := congrFun he_coe a
    rw [← h1]
    exact OpenPartialHomeomorph.left_inv _ ha_src
  · -- smoothness of the inverse on `O`
    refine (IsOpen.contDiffOn_iff (s := e.target ∩ (fun y => e.symm y) ⁻¹' Metric.ball a ρ) ?_).mpr
      fun y hy => ?_
    · refine isOpen_iff_mem_nhds.mpr fun y hy => ?_
      have hy_tgt : y ∈ e.target := hy.1
      exact Filter.inter_mem (e.open_target.mem_nhds hy_tgt)
        ((e.continuousAt_symm hy_tgt).preimage_mem_nhds (isOpen_ball.mem_nhds hy.2))
    · have hy_tgt : y ∈ e.target := hy.1
      have hyW : e.symm y ∈ Metric.ball a ρ := hy.2
      have hyV : e.symm y ∈ V := (hρsub hyW).1.2
      have hyInv : (fderiv ℝ G (e.symm y)).IsInvertible := (hρsub hyW).1.1
      obtain ⟨e₁, he₁⟩ := hyInv
      have hGat' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (e.symm y) :=
        hG.contDiffAt (hV.mem_nhds hyV)
      have hfd : HasFDerivAt G (fderiv ℝ G (e.symm y)) (e.symm y) :=
        (hGat'.differentiableAt hnz).hasFDerivAt
      have hf₀' : HasFDerivAt (e : E → E) (e₁ : E →L[ℝ] E) (e.symm y) := by
        rw [he_coe]
        exact hfd.congr_fderiv he₁.symm
      have hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : E → E) (e.symm y) := by
        rw [he_coe]
        exact hGat'
      exact e.contDiffAt_symm hy_tgt hf₀' hf
  · -- the inverse stays in `W`
    intro y hy
    exact hy.2
  · -- `G ∘ L = id` on `O`
    intro y hy
    have h1 : e (e.symm y) = y := OpenPartialHomeomorph.right_inv _ hy.1
    calc G ((fun y => e.symm y) y) = G (e.symm y) := rfl
      _ = e (e.symm y) := (congrFun he_coe (e.symm y)).symm
      _ = y := h1
  · -- uniqueness on `W`
    intro y hy z hzW hzy
    have hz_src : z ∈ e.source := (hρsub hzW).2
    exact e.injOn hz_src (e.map_target hy.1) (by
      rw [congrFun he_coe z, hzy, OpenPartialHomeomorph.right_inv _ hy.1])

/-! ## The linear splitting adapted to two transverse subspaces -/

/-- **A linear splitting adapted to two transverse subspaces.**  If `L₁, L₂` are subspaces of a
finite dimensional real space `V` of dimension `2n` whose sum is everything and each of which has
dimension `n` (so that `V = L₁ ⊕ L₂`), then there is a continuous linear equivalence
`Φ : V ≃L[ℝ] (ℝⁿ × ℝⁿ)` such that

* the second coordinate of `Φ` vanishes exactly on `L₂` (so `Φ (L₂) = ℝⁿ × {0}`),
* on `L₁` both coordinates are injective (so `Φ (L₁) ∩ (ℝⁿ × {0}) = ⊥` and
  `Φ (L₁) ∩ ({0} × ℝⁿ) = ⊥`),

i.e. both `L₁` and `L₂` are graphs over the first factor. -/
theorem exists_prod_equiv_of_transverse {n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L₁ L₂ : Submodule ℝ V) (hsup : L₁ ⊔ L₂ = ⊤) (hV : Module.finrank ℝ V = 2 * n)
    (h₁ : Module.finrank ℝ L₁ = n) (h₂ : Module.finrank ℝ L₂ = n) :
    ∃ Φ : V ≃L[ℝ] (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ x : V, (Φ x).2 = 0 ↔ x ∈ L₂) ∧
      (∀ x ∈ L₁, (Φ x).1 = 0 → x = 0) ∧
      (∀ x ∈ L₁, (Φ x).2 = 0 → x = 0) := by
  classical
  -- the two subspaces are complementary
  have hdisj : L₁ ⊓ L₂ = ⊥ := by
    have hform := Submodule.finrank_sup_add_finrank_inf_eq L₁ L₂
    rw [hsup, finrank_top, hV, h₁, h₂] at hform
    have hzero : Module.finrank ℝ ↥(L₁ ⊓ L₂) = 0 := by omega
    exact (Submodule.finrank_eq_zero (S := L₁ ⊓ L₂)).mp hzero
  have hcompl : IsCompl L₁ L₂ :=
    ⟨disjoint_iff_inf_le.mpr (le_of_eq hdisj), codisjoint_iff_le_sup.mpr (le_of_eq hsup.symm)⟩
  -- linear identifications of the two pieces with `ℝⁿ`
  let α : L₂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h₂, finrank_euclideanSpace_fin])
  let β : L₁ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h₁, finrank_euclideanSpace_fin])
  let γ : L₁ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h₁, finrank_euclideanSpace_fin])
  -- the direct sum decomposition `V = L₁ ⊕ L₂`
  let e : (L₁ × L₂) ≃ₗ[ℝ] V := Submodule.prodEquivOfIsCompl L₁ L₂ hcompl
  have he_coe : ∀ (a : L₁) (b : L₂), (e (a, b) : V) = (a : V) + (b : V) := by
    intro a b
    have h := Submodule.coe_prodEquivOfIsCompl L₁ L₂ hcompl
    have h2 : e (a, b) = (L₁.subtype.coprod L₂.subtype) (a, b) := by
      rw [← h]; rfl
    simpa [LinearMap.coprod_apply] using h2
  have hdecomp : ∀ x : V, (x : V) = ((e.symm x).1 : V) + ((e.symm x).2 : V) := by
    intro x
    have h := he_coe (e.symm x).1 (e.symm x).2
    rw [← h, LinearEquiv.apply_symm_apply]
  -- elementary algebraic consequences of the decomposition
  have hsub_eq : ∀ (x : V) (a : L₁) (b : L₂), (x : V) = (a : V) + (b : V) →
      x - (a : V) = (b : V) := by
    intro x a b h
    rw [h]
    abel
  have hsub_eq' : ∀ (x : V) (a : L₁) (b : L₂), (x : V) = (a : V) + (b : V) →
      x - (b : V) = (a : V) := by
    intro x a b h
    rw [h]
    abel
  have hsum_eq : ∀ (x : V) (a : L₁) (b : L₂), (x : V) = (a : V) + (b : V) → (a : V) = 0 →
      (x : V) = (b : V) := by
    intro x a b h ha
    rw [h, ha, zero_add]
  have hsum_eq' : ∀ (x : V) (a : L₁) (b : L₂), (x : V) = (a : V) + (b : V) → (b : V) = 0 →
      (x : V) = (a : V) := by
    intro x a b h hb
    rw [h, hb, add_zero]
  -- the model linear equivalence, in the coordinates `L₁ × L₂`
  let Φp : (L₁ × L₂) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    { toFun := fun p => (β p.1 + α p.2, γ p.1)
      invFun := fun q => (γ.symm q.2, α.symm (q.1 - β (γ.symm q.2)))
      left_inv := by
        rintro ⟨a, b⟩
        refine Prod.ext ?_ ?_
        · dsimp only
          exact LinearEquiv.symm_apply_apply γ a
        · dsimp only
          rw [LinearEquiv.symm_apply_apply γ a]
          rw [show β a + α b - β a = α b by abel]
          exact LinearEquiv.symm_apply_apply α b
      right_inv := by
        rintro ⟨u, w⟩
        refine Prod.ext ?_ ?_
        · dsimp only
          rw [show α (α.symm (u - β (γ.symm w))) = (u - β (γ.symm w)) from
            LinearEquiv.apply_symm_apply α _]
          abel
        · dsimp only
          exact LinearEquiv.apply_symm_apply γ w
      map_add' := by
        rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
        refine Prod.ext ?_ ?_
        · show β (a₁ + a₂) + α (b₁ + b₂) = (β a₁ + α b₁) + (β a₂ + α b₂)
          rw [map_add, map_add]
          abel
        · show γ (a₁ + a₂) = γ a₁ + γ a₂
          rw [map_add]
      map_smul' := by
        rintro c ⟨a, b⟩
        refine Prod.ext ?_ ?_
        · show β (c • a) + α (c • b) = c • (β a + α b)
          rw [map_smul, map_smul, smul_add]
        · show γ (c • a) = c • γ a
          rw [map_smul] }
  let Φₗ : V ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    e.symm.trans Φp
  have hΦcoe : ∀ x : V, Φₗ x
      = (β (e.symm x).1 + α (e.symm x).2, γ (e.symm x).1) := fun x => rfl
  -- the coordinate along `L₂` of a point of `L₁` vanishes, and conversely
  have hcomp₂ : ∀ x ∈ L₁, ((e.symm x).2 : V) = 0 := by
    intro x hxL
    have hb : (x - ((e.symm x).1 : V)) ∈ L₂ := by
      rw [hsub_eq x (e.symm x).1 (e.symm x).2 (hdecomp x)]
      exact (e.symm x).2.2
    have hbL₁ : (x - ((e.symm x).1 : V)) ∈ L₁ := L₁.sub_mem hxL (e.symm x).1.2
    have hmem : (x - ((e.symm x).1 : V)) ∈ L₁ ⊓ L₂ := ⟨hbL₁, hb⟩
    rw [hdisj] at hmem
    rw [hsub_eq x (e.symm x).1 (e.symm x).2 (hdecomp x)] at hmem
    simpa using hmem
  have hcomp₁ : ∀ x ∈ L₂, ((e.symm x).1 : V) = 0 := by
    intro x hxL₂
    have ha : (x - ((e.symm x).2 : V)) ∈ L₁ := by
      rw [hsub_eq' x (e.symm x).1 (e.symm x).2 (hdecomp x)]
      exact (e.symm x).1.2
    have haL₂ : (x - ((e.symm x).2 : V)) ∈ L₂ := L₂.sub_mem hxL₂ (e.symm x).2.2
    have hmem : (x - ((e.symm x).2 : V)) ∈ L₁ ⊓ L₂ := ⟨ha, haL₂⟩
    rw [hdisj] at hmem
    rw [hsub_eq' x (e.symm x).1 (e.symm x).2 (hdecomp x)] at hmem
    simpa using hmem
  refine ⟨Φₗ.toContinuousLinearEquiv, ?_, ?_, ?_⟩
  · -- the second coordinate vanishes exactly on `L₂`
    intro x
    have h2eq : (Φₗ.toContinuousLinearEquiv x).2 = γ (e.symm x).1 := rfl
    rw [h2eq]
    constructor
    · intro hx
      have ha : (e.symm x).1 = 0 := γ.injective (by rw [hx, map_zero])
      have ha' : ((e.symm x).1 : V) = 0 := congrArg (fun z : L₁ => (z : V)) ha
      have hx' : (x : V) = ((e.symm x).2 : V) :=
        hsum_eq x (e.symm x).1 (e.symm x).2 (hdecomp x) ha'
      rw [hx']
      exact (e.symm x).2.2
    · intro hx
      have h0 : ((e.symm x).1 : V) = 0 := hcomp₁ x hx
      have ha : (e.symm x).1 = 0 := Subtype.ext h0
      rw [ha]
      exact γ.map_zero
  · -- the first coordinate is injective on `L₁`
    intro x hxL hx
    have hb0 : ((e.symm x).2 : V) = 0 := hcomp₂ x hxL
    have hb : (e.symm x).2 = 0 := Subtype.ext hb0
    have hsum : β (e.symm x).1 + α (e.symm x).2 = 0 := by
      have h := hx
      rw [show (Φₗ.toContinuousLinearEquiv x).1 = (Φₗ x).1 from rfl, hΦcoe] at h
      exact h
    have hβ : β (e.symm x).1 = 0 := by
      have h' : β (e.symm x).1 + α (0 : L₂) = 0 := by rw [← hb]; exact hsum
      simpa using h'
    have ha : (e.symm x).1 = 0 := β.injective (by rw [hβ, map_zero])
    have ha' : ((e.symm x).1 : V) = 0 := congrArg (fun z : L₁ => (z : V)) ha
    have h1 := hsum_eq' x (e.symm x).1 (e.symm x).2 (hdecomp x) hb0
    rw [h1, ha']
  · -- the second coordinate is injective on `L₁`
    intro x hxL hx
    have hb0 : ((e.symm x).2 : V) = 0 := hcomp₂ x hxL
    have hsum : γ (e.symm x).1 = 0 := by
      have h := hx
      rw [show (Φₗ.toContinuousLinearEquiv x).2 = (Φₗ x).2 from rfl, hΦcoe] at h
      exact h
    have ha : (e.symm x).1 = 0 := γ.injective (by rw [hsum, map_zero])
    have ha' : ((e.symm x).1 : V) = 0 := congrArg (fun z : L₁ => (z : V)) ha
    have h1 := hsum_eq x (e.symm x).1 (e.symm x).2 (hdecomp x) ha'
    rw [h1, hb0]

/-! ## Dimension facts for a transverse double point -/

/-- The dimension of the tangent space of a manifold modelled on `ℝⁿ` is `n`. -/
lemma finrank_tangentSpace_self (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    Module.finrank ℝ (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p) = n := by
  rw [show Module.finrank ℝ
        (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p)
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) from rfl, finrank_euclideanSpace_fin]

/-- The range of the manifold derivative of a map from an `n`-manifold to `ℝ^{2n}` has dimension
at most `n`. -/
lemma finrank_mfderiv_range_le {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p : M) :
    Module.finrank ℝ ↥(mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p).range ≤ n := by
  haveI : Module.Finite ℝ (TangentSpace (𝓡 n) p) :=
    (inferInstance : Module.Finite ℝ (EuclideanSpace ℝ (Fin n)))
  refine le_trans (LinearMap.finrank_range_le
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p).toLinearMap) ?_
  exact le_of_eq (finrank_tangentSpace_self n p)

/-- **A transverse double point forces the two branches to be immersions.**  If the ranges of the
manifold derivatives of `f` at `p₁` and `p₂` span `ℝ^{2n}`, then each has dimension exactly `n` and
each derivative is injective. -/
theorem finrank_range_mfderiv_of_transverse {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ : M) (hfp : f p₁ = f p₂)
    (htr : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤) :
    Module.finrank ℝ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range = n ∧
    Module.finrank ℝ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = n ∧
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁) ∧
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂) := by
  haveI hF₁ : Module.Finite ℝ (TangentSpace (𝓡 n) p₁) :=
    (inferInstance : Module.Finite ℝ (EuclideanSpace ℝ (Fin n)))
  haveI hF₂ : Module.Finite ℝ (TangentSpace (𝓡 n) p₂) :=
    (inferInstance : Module.Finite ℝ (EuclideanSpace ℝ (Fin n)))
  let A₁ : TangentSpace (𝓡 n) p₁ →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁
  let A₂ : TangentSpace (𝓡 n) p₂ →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂
  have hsup : A₁.range ⊔ A₂.range = ⊤ := htr
  have hb₁ : Module.finrank ℝ ↥A₁.range ≤ n := by
    refine le_trans (LinearMap.finrank_range_le A₁.toLinearMap) ?_
    exact le_of_eq (finrank_tangentSpace_self n p₁)
  have hb₂ : Module.finrank ℝ ↥A₂.range ≤ n := by
    refine le_trans (LinearMap.finrank_range_le A₂.toLinearMap) ?_
    exact le_of_eq (finrank_tangentSpace_self n p₂)
  have htop : Module.finrank ℝ ↥(⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * n)))) = 2 * n := by
    rw [finrank_top, finrank_euclideanSpace_fin]
  have hform := Submodule.finrank_sup_add_finrank_inf_eq A₁.range A₂.range
  have hle : 2 * n ≤ Module.finrank ℝ ↥A₁.range + Module.finrank ℝ ↥A₂.range := by
    have h1 : 2 * n ≤ Module.finrank ℝ ↥(A₁.range ⊔ A₂.range) := by rw [hsup, htop]
    have h2 : Module.finrank ℝ ↥(A₁.range ⊔ A₂.range)
        ≤ Module.finrank ℝ ↥A₁.range + Module.finrank ℝ ↥A₂.range := by omega
    omega
  have heq₁ : Module.finrank ℝ ↥A₁.range = n := by omega
  have heq₂ : Module.finrank ℝ ↥A₂.range = n := by omega
  have hinjA : ∀ (p : M) [Module.Finite ℝ (TangentSpace (𝓡 n) p)]
      (B : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))),
      Module.finrank ℝ ↥B.range = n → Function.Injective B := by
    intro p _ B hp
    have hrank := LinearMap.finrank_range_add_finrank_ker B.toLinearMap
    have hsrc : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
      rw [show Module.finrank ℝ (TangentSpace (𝓡 n) p)
          = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) from rfl, finrank_euclideanSpace_fin]
    rw [hsrc, hp] at hrank
    have hker : Module.finrank ℝ ↥B.toLinearMap.ker = 0 := by omega
    exact LinearMap.ker_eq_bot.mp ((Submodule.finrank_eq_zero (S := B.toLinearMap.ker)).mp hker)
  exact ⟨heq₁, heq₂, hinjA p₁ A₁ heq₁, hinjA p₂ A₂ heq₂⟩



/-! ## The local sheet of a smooth map at a point -/

/-- The manifold derivative of `f - f p₀` equals that of `f`, as a continuous linear map into the
model space (the two are only definitionally equal because the tangent space ignores the base
point). -/
lemma mfderiv_sub_const_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : M → E'} {p : M} (c : E')
    (h : MDifferentiableAt I 𝓘(𝕜, E') f p) :
    (mfderiv I 𝓘(𝕜, E') (fun x => f x - c) p : TangentSpace I p →L[𝕜] E')
      = (mfderiv I 𝓘(𝕜, E') f p : TangentSpace I p →L[𝕜] E') := by
  have h2 : (mfderiv I 𝓘(𝕜, E') (fun x => f x - c) p : TangentSpace I p →L[𝕜] E')
      = mfderiv I 𝓘(𝕜, E') (f - fun _ => c) p := rfl
  rw [h2, mfderiv_sub h (mdifferentiableAt_const (I := I) (c := c)), mfderiv_const]
  exact sub_zero _

/-- **The image of a ball under a local inverse is open.**  If `L` is a (unique) right inverse of
`G` on the ball of radius `r` with values in an open set `W` on which `G` is continuous, then the
image of that ball under `L` is open. -/
lemma isOpen_image_ball_of_localInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G L : E → E) (W : Set E) (r : ℝ) (hr : 0 < r) (hWopen : IsOpen W)
    (hWcont : ∀ z ∈ W, ContinuousAt G z)
    (hLW : ∀ y : E, ‖y‖ < r → L y ∈ W)
    (hGid : ∀ y : E, ‖y‖ < r → G (L y) = y)
    (huniq : ∀ y : E, ‖y‖ < r → ∀ z ∈ W, G z = y → z = L y) :
    IsOpen (L '' Metric.ball 0 r) := by
  have hset : L '' Metric.ball 0 r = W ∩ G ⁻¹' Metric.ball 0 r := by
    apply Set.Subset.antisymm
    · rintro z ⟨y, hy, rfl⟩
      refine ⟨hLW y (mem_ball_zero_iff.mp hy), ?_⟩
      show G (L y) ∈ Metric.ball 0 r
      rw [hGid y (mem_ball_zero_iff.mp hy)]
      exact hy
    · rintro z ⟨hzW, hzG⟩
      have hzG' : ‖G z‖ < r := mem_ball_zero_iff.mp hzG
      exact ⟨G z, mem_ball_zero_iff.mpr hzG', (huniq (G z) hzG' z hzW rfl).symm⟩
  rw [hset]
  refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
  exact Filter.inter_mem (hWopen.mem_nhds hz.1)
    ((hWcont z hz.1).preimage_mem_nhds (isOpen_ball.mem_nhds hz.2))

/-- **The local sheet model at a point.**  Given a smooth `f : M → ℝ^{2n}`, points `p`, `p₀` of `M`
with `f p = f p₀`, a linear identification `Φ : ℝ^{2n} ≃L ℝⁿ × ℝⁿ` whose first coordinate
projection of `mfderiv f p` is an invertible map `Ed`, there are a smooth parametrisation
`σ : ℝⁿ → M` of a neighbourhood of `p` and a graph function `h : ℝⁿ → ℝⁿ` such that, on a ball of
radius `R > 0` around `0`,

* `Φ (f (σ u) - f p₀) = (u, h u)`,
* `σ` is injective on the closed ball and the image of the open ball is open,
* `fderiv ℝ h 0 = Φ₂ ∘L mfderiv f p ∘L Ed⁻¹`. -/
private theorem exists_sheet_data {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p p₀ : M) (hfp : f p = f p₀)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (Ed : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p ≃L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (hEd : (Ed : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p →L[ℝ]
          EuclideanSpace ℝ (Fin n))
        = ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ∘L
            (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
              (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
          ∘L mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p) :
    ∃ (σ : EuclideanSpace ℝ (Fin n) → M)
      (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 < R ∧ σ 0 = p ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      (∀ r : ℝ, 0 < r → r ≤ R → Set.InjOn σ (Metric.closedBall 0 r)) ∧
      (∀ r : ℝ, 0 < r → r ≤ R → IsOpen (σ '' Metric.ball 0 r)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R → Φ (f (σ u) - f p₀) = (u, h u)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      fderiv ℝ h 0
        = (((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
              (EuclideanSpace ℝ (Fin n))) ∘L
            (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
              (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
          ∘L mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p)
          ∘L (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ]
              TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) p) := by
  classical
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- the two coordinate projections of the linear identification `Φ`
  let Φ₁ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ∘L
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  let Φ₂ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ∘L
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  -- the "first coordinate" of `f`, shifted by `f p₀`
  let H : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x => f x - f p₀
  let g : M → EuclideanSpace ℝ (Fin n) := Φ₁ ∘ H
  have hH_sm : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) H :=
    hf.sub contMDiff_const
  have hg_sm : ContMDiff (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    Work.Projection.contMDiff_comp_clm (n := n) (N := 2 * n) (k := n) Φ₁ H hH_sm
  have hH_deriv : mfderiv (𝓡 n) (𝓡 (2 * n)) H p
      = mfderiv (𝓡 n) (𝓡 (2 * n)) f p :=
    mfderiv_sub_const_eq (I := 𝓡 n) (f := f) (p := p) (f p₀) (hf.mdifferentiableAt hnz)
  have hmg : mfderiv (𝓡 n) (𝓡 n) g p
      = (Ed : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [Work.Projection.mfderiv_comp_clm (n := n) (N := 2 * n) (k := n) Φ₁ H hH_sm p,
      hH_deriv, hEd]
  have hginj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) g p) := by
    rw [hmg]
    exact Ed.injective
  -- the chart at `p` and the chart representation of `g`
  let c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) p
  have hpsrc : p ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) p
  have hcpt : c p ∈ c.target := c.map_source hpsrc
  let G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun y => g (c.symm y)
  have hGsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G c.target :=
    (chartRep_smooth_and_fderiv_injective g hg_sm p hginj).1
  have hGinj : Function.Injective (fderiv ℝ G (c p)) :=
    (chartRep_smooth_and_fderiv_injective g hg_sm p hginj).2
  -- the inverse function theorem
  obtain ⟨L, O, W, hOopen, hGO, hWopen, hcptW, hWV, hL0, hLsm, hLO, hLright, hLuniq⟩ :=
    exists_localInverse_smooth_on G c.target c.open_target (c p) hcpt hGsm hGinj
  have hG0 : G (c p) = 0 := by
    change g (c.symm (c p)) = 0
    rw [c.left_inv hpsrc]
    change Φ₁ (f p - f p₀) = 0
    rw [hfp, sub_self]
    simp
  have hL00 : L 0 = c p := by rw [← hG0]; exact hL0
  -- radii
  obtain ⟨r, hrpos, hOball⟩ := Metric.mem_nhds_iff.mp (hOopen.mem_nhds hGO)
  have hOball' : Metric.ball 0 r ⊆ O := by
    intro y hy
    exact hOball (by rwa [hG0])
  obtain ⟨R₁, hR₁pos, hR₁r⟩ := exists_between hrpos
  obtain ⟨R₀, hR₀pos, hR₀R₁⟩ := exists_between hR₁pos
  obtain ⟨χ, hχsm, hχbd, hχ1, hχ0⟩ := exists_smooth_cutoff hR₀pos hR₀R₁
  -- the parametrisation and the graph function
  let σ : EuclideanSpace ℝ (Fin n) → M := fun u => c.symm (L (χ u • u))
  let h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun u => Φ₂ (f (σ u) - f p₀)
  have hballO : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < R₁ → u ∈ O := by
    intro u hu
    exact hOball' (mem_ball_zero_iff.mpr (by linarith))
  have hu_char : ∀ u : EuclideanSpace ℝ (Fin n), χ u • u ∈ O := by
    intro u
    by_cases hcase : ‖u‖ < R₁
    · refine hballO (χ u • u) ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχbd u).1]
      calc χ u * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right (hχbd u).2 (norm_nonneg u)
        _ = ‖u‖ := one_mul _
        _ < R₁ := hcase
    · have h0 : χ u = 0 := hχ0 u (le_of_not_gt hcase)
      rw [h0, zero_smul]
      exact hballO 0 (by simpa using hR₁pos)
  -- basic properties of `σ`
  have hσ0 : σ 0 = p := by
    change c.symm (L (χ 0 • 0)) = p
    rw [smul_zero, hL00, c.left_inv hpsrc]
  have hσ_graph : ∀ u : EuclideanSpace ℝ (Fin n), χ u = 1 → g (σ u) = u := by
    intro u hu
    have h1 : χ u • u ∈ O := hu_char u
    have h2 : G (L (χ u • u)) = χ u • u := hLright (χ u • u) h1
    change G (L (χ u • u)) = u
    rw [h2, hu, one_smul]
  -- smoothness of `σ`
  have hσ_sm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n)
      ((⊤ : ℕ∞) : WithTop ℕ∞) σ := by
    rw [← contMDiffOn_univ]
    intro u _
    rw [contMDiffWithinAt_univ]
    by_cases hcase : ‖u‖ < r
    · -- the parametrisation is smooth where the cut-off is supported
      have huO : χ u • u ∈ O := hu_char u
      have hχ_at : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ)
          ((⊤ : ℕ∞) : WithTop ℕ∞) χ u :=
        (contMDiff_iff_contDiff.mpr hχsm).contMDiffAt
      have hsmul : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => χ z • z) u :=
        hχ_at.smul contMDiffAt_id
      have hL_at : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞) L (χ u • u) :=
        ((contMDiffOn_iff_contDiffOn.mpr hLsm).contMDiffAt (hOopen.mem_nhds huO))
      have hcomp : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z => L (χ z • z)) u :=
        ContMDiffAt.comp u hL_at hsmul
      have hcs : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
          ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => c.symm z) (L (χ u • u)) :=
        contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) p)
          (hWV (hLO (χ u • u) huO))
      exact ContMDiffAt.comp u hcs hcomp
    · -- away from the support the cut-off vanishes identically
      have hmem : {z : EuclideanSpace ℝ (Fin n) | R₁ < ‖z‖} ∈ 𝓝 u :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds
          (lt_of_lt_of_le hR₁r (not_lt.mp hcase))
      have hev : σ =ᶠ[𝓝 u] (fun _ => c.symm (L 0)) := by
        filter_upwards [hmem] with z hz
        change c.symm (L (χ z • z)) = c.symm (L 0)
        rw [hχ0 z hz.le, zero_smul]
      exact (contMDiffAt_const (c := c.symm (L 0))).congr_of_eventuallyEq hev
  -- injectivity of `σ` on the closed ball
  have hσ_inj : ∀ r : ℝ, 0 < r → r ≤ R₀ → Set.InjOn σ (Metric.closedBall 0 r) := by
    intro r hr hrR u hu v hv huv
    have hu' : ‖u‖ ≤ r := mem_closedBall_zero_iff.mp hu
    have hv' : ‖v‖ ≤ r := mem_closedBall_zero_iff.mp hv
    have hu1 : χ u = 1 := hχ1 u (by linarith)
    have hv1 : χ v = 1 := hχ1 v (by linarith)
    have huO : u ∈ O := hballO u (by linarith)
    have hvO : v ∈ O := hballO v (by linarith)
    have hLu : L u ∈ c.target := hWV (hLO u huO)
    have hLv : L v ∈ c.target := hWV (hLO v hvO)
    have hsymm : c.symm (L u) = c.symm (L v) := by
      have h1 : σ u = c.symm (L u) := by
        change c.symm (L (χ u • u)) = c.symm (L u)
        rw [hu1, one_smul]
      have h2 : σ v = c.symm (L v) := by
        change c.symm (L (χ v • v)) = c.symm (L v)
        rw [hv1, one_smul]
      rw [← h1, ← h2]
      exact huv
    have hLuv : L u = L v := by
      have hinj : Set.InjOn (fun y => c.symm y) c.target := by
        have := (c.symm).injOn
        rwa [OpenPartialHomeomorph.symm_source] at this
      exact hinj hLu hLv hsymm
    calc u = G (L u) := (hLright u huO).symm
      _ = G (L v) := by rw [hLuv]
      _ = v := hLright v hvO
  -- openness of the image of the ball
  have hgraph : ∀ u : EuclideanSpace ℝ (Fin n), χ u = 1 → Φ (f (σ u) - f p₀) = (u, h u) := by
    intro u hu
    have h1 : g (σ u) = u := hσ_graph u hu
    have h2 : (Φ (f (σ u) - f p₀)).1 = g (σ u) := rfl
    exact Prod.ext (by rw [h2, h1]) rfl
  have hσ_open : ∀ r : ℝ, 0 < r → r ≤ R₀ → IsOpen (σ '' Metric.ball 0 r) := by
    intro r hr hrR
    have hset : σ '' Metric.ball 0 r = c.symm '' (L '' Metric.ball 0 r) := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨L u, ⟨u, hu, rfl⟩, ?_⟩
        change c.symm (L u) = c.symm (L (χ u • u))
        rw [show χ u = 1 from hχ1 u (by rw [mem_ball_zero_iff] at hu; linarith), one_smul]
      · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨u, hu, ?_⟩
        change c.symm (L (χ u • u)) = c.symm (L u)
        rw [show χ u = 1 from hχ1 u (by rw [mem_ball_zero_iff] at hu; linarith), one_smul]
    rw [hset]
    refine c.isOpen_image_symm_of_subset_target ?_ ?_
    · exact isOpen_image_ball_of_localInverse G L W r hr hWopen
        (fun z hz => hGsm.continuousOn.continuousAt (c.open_target.mem_nhds (hWV hz)))
        (fun y hy => hLO y (hballO y (by linarith)))
        (fun y hy => hLright y (hballO y (by linarith)))
        (fun y hy z hzW hzy => hLuniq y (hballO y (by linarith)) z hzW hzy)
    · rintro y ⟨u, hu, rfl⟩
      exact hWV (hLO u (hballO u (by rw [mem_ball_zero_iff] at hu; linarith)))
  -- the derivative of the graph function
  have hmσ : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) σ 0
      = (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p) := by
    -- the manifold derivative of `σ`, with clean type ascriptions
    let Tσ : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p :=
      mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) σ 0
    change Tσ = (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p)
    have hEq : (fun u => g (σ u)) =ᶠ[𝓝 0] id := by
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) hR₀pos] with u hu
      exact hσ_graph u (hχ1 u (mem_ball_zero_iff.mp hu).le)
    have h1 : (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n)
          (fun u => g (σ u)) 0 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [hEq.mfderiv_eq, mfderiv_id]
      rfl
    have h2 : (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n)
          (fun u => g (σ u)) 0 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        = (Ed : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin n)) ∘L Tσ := by
      rw [show (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (fun u => g (σ u)) 0 :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          = mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) (g ∘ σ) 0 from rfl]
      rw [mfderiv_comp 0 (g := g) (f := σ) (hg_sm.mdifferentiableAt hnz)
        (hσ_sm.mdifferentiableAt hnz), hσ0, hmg]
      rfl
    have hcomp : (Ed : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin n)) ∘L Tσ
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      rw [← h2, h1]
    have hx : ∀ x : EuclideanSpace ℝ (Fin n),
        (Ed : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin n)) (Tσ x) = x := by
      intro x
      have h3 := congrArg (fun (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =>
        S x) hcomp
      show (Ed : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin n)) (Tσ x) = x
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h3
    ext x
    calc Tσ x = (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p)
          ((Ed : TangentSpace (𝓡 n) p →L[ℝ] EuclideanSpace ℝ (Fin n)) (Tσ x)) :=
          (ContinuousLinearEquiv.symm_apply_apply Ed (Tσ x)).symm
      _ = (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p) x := by rw [hx x]
  have hHfd : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (σ u) - f p₀) 0
      = mfderiv (𝓡 n) (𝓡 (2 * n)) f p ∘L
        (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p) := by
    rw [← mfderiv_eq_fderiv]
    rw [mfderiv_sub_const_eq (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (f := fun u : EuclideanSpace ℝ (Fin n) => f (σ u)) (p := 0) (f p₀)
      ((hf.comp hσ_sm).mdifferentiableAt hnz)]
    have h1 : (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))) (fun u : EuclideanSpace ℝ (Fin n) => f (σ u)) 0 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
        = mfderiv (𝓡 n) (𝓡 (2 * n)) f p ∘L
          (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) σ 0 :
            EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p) := by
      rw [show (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))) (fun u : EuclideanSpace ℝ (Fin n) => f (σ u)) 0 :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
          = mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))) (f ∘ σ) 0 from rfl]
      rw [mfderiv_comp 0 (g := f) (f := σ) (hf.mdifferentiableAt hnz)
        (hσ_sm.mdifferentiableAt hnz), hσ0]
    rw [h1, hmσ]
    rfl
  have hh_deriv : fderiv ℝ h 0
      = (((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin n))) ∘L
          (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
        ∘L mfderiv (𝓡 n) (𝓡 (2 * n)) f p)
        ∘L (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p) := by
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin n) => f (σ u) - f p₀) :=
      contMDiff_iff_contDiff.mp ((hf.comp hσ_sm).sub contMDiff_const)
    have hHd : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => f (σ u) - f p₀)
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f p ∘L
          (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p)) 0 :=
      (((hcd.differentiable (by simp)) 0).hasFDerivAt).congr_fderiv hHfd
    have hcomp' : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) => Φ₂ (f (σ u) - f p₀))
        (Φ₂ ∘L (mfderiv (𝓡 n) (𝓡 (2 * n)) f p ∘L
          (Ed.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) p))) 0 :=
      (Φ₂.hasFDerivAt (x := (fun u : EuclideanSpace ℝ (Fin n) => f (σ u) - f p₀) 0)).comp 0 hHd
    rw [show fderiv ℝ h 0
        = fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => Φ₂ (f (σ u) - f p₀)) 0 from rfl,
      hcomp'.fderiv]
    rfl
  refine ⟨σ, h, R₀, hR₀pos, hσ0, hσ_sm, hσ_inj, hσ_open, ?_, ?_, hh_deriv⟩
  · intro u hu
    exact hgraph u (hχ1 u hu)
  · -- smoothness of the graph function
    have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => f (σ u) - f p₀) := (hf.comp hσ_sm).sub contMDiff_const
    have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => Φ₂ (f (σ u) - f p₀)) := Φ₂.contMDiff.comp h1
    exact contMDiff_iff_contDiff.mp h2

/-! ## The local sheet model at a transverse double point -/

/-- **The local sheet model at a transverse double point.** -/
theorem exists_sheet_model {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (p₁ p₂ : M) (hp : p₁ ≠ p₂) (hfp : f p₁ = f p₂)
    (htr : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤) :
    ∃ (Φ : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (σ₁ σ₂ : EuclideanSpace ℝ (Fin n) → M)
      (h₁ h₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (α K R₀ : ℝ),
      0 < α ∧ 0 < K ∧ 0 < R₀ ∧ (∀ u, α * ‖u‖ ≤ ‖A u‖) ∧
      σ₁ 0 = p₁ ∧ σ₂ 0 = p₂ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₁ ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) σ₂ ∧
      Set.InjOn σ₁ (Metric.closedBall 0 R₀) ∧ Set.InjOn σ₂ (Metric.closedBall 0 R₀) ∧
      IsOpen (σ₁ '' Metric.ball 0 R₀) ∧ IsOpen (σ₂ '' Metric.ball 0 R₀) ∧
      (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ R₀ → Φ (f (σ₁ w) - f p₁) = (w, h₁ w)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → Φ (f (σ₂ u) - f p₁) = (u, h₂ u)) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u - h₂ u - A u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₂ u‖ ≤ K * ‖u‖ ^ 2) ∧
      (∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ R₀ → ‖h₁ u‖ ≤ K * ‖u‖) := by
  classical
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  haveI hF₁ : Module.Finite ℝ (TangentSpace (𝓡 n) p₁) :=
    (inferInstance : Module.Finite ℝ (EuclideanSpace ℝ (Fin n)))
  haveI hF₂ : Module.Finite ℝ (TangentSpace (𝓡 n) p₂) :=
    (inferInstance : Module.Finite ℝ (EuclideanSpace ℝ (Fin n)))
  -- the two derivatives and the linear splitting
  let A₁ : TangentSpace (𝓡 n) p₁ →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁
  let A₂ : TangentSpace (𝓡 n) p₂ →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂
  have hsup : A₁.range ⊔ A₂.range = ⊤ := htr
  obtain ⟨hfin₁, hfin₂, hinj₁, hinj₂⟩ := finrank_range_mfderiv_of_transverse f p₁ p₂ hfp htr
  have hVfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n :=
    finrank_euclideanSpace_fin
  obtain ⟨Φ, hΦzero, hΦfst, hΦsnd⟩ :=
    exists_prod_equiv_of_transverse A₁.range A₂.range hsup hVfin hfin₁ hfin₂
  -- the two coordinate projections of `Φ`
  let Φ₁ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ∘L
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  let Φ₂ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ∘L
      (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  -- the projected map and its derivative at the two points
  let H : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x => f x - f p₁
  let g : M → EuclideanSpace ℝ (Fin n) := Φ₁ ∘ H
  have hH_sm : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) H :=
    hf.sub contMDiff_const
  have hg_sm : ContMDiff (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    Work.Projection.contMDiff_comp_clm (n := n) (N := 2 * n) (k := n) Φ₁ H hH_sm
  have hHd₁ : mfderiv (𝓡 n) (𝓡 (2 * n)) H p₁ = mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁ :=
    mfderiv_sub_const_eq (I := 𝓡 n) (f := f) (p := p₁) (f p₁) (hf.mdifferentiableAt hnz)
  have hHd₂ : mfderiv (𝓡 n) (𝓡 (2 * n)) H p₂ = mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂ :=
    mfderiv_sub_const_eq (I := 𝓡 n) (f := f) (p := p₂) (f p₁) (hf.mdifferentiableAt hnz)
  have hmg₁ : (mfderiv (𝓡 n) (𝓡 n) g p₁ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = (Φ₁ ∘L A₁) := by
    rw [Work.Projection.mfderiv_comp_clm (n := n) (N := 2 * n) (k := n) Φ₁ H hH_sm p₁, hHd₁]
  have hmg₂ : (mfderiv (𝓡 n) (𝓡 n) g p₂ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = (Φ₁ ∘L A₂) := by
    rw [Work.Projection.mfderiv_comp_clm (n := n) (N := 2 * n) (k := n) Φ₁ H hH_sm p₂, hHd₂]
  -- injectivity of the projected derivative
  have hinjg₁ : Function.Injective (mfderiv (𝓡 n) (𝓡 n) g p₁ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [hmg₁]
    intro v w hvw
    have h2 : Φ₁ (A₁ v) = Φ₁ (A₁ w) := hvw
    have h1 : Φ₁ (A₁ (v - w)) = 0 := by
      rw [A₁.map_sub v w, Φ₁.map_sub (A₁ v) (A₁ w), h2, sub_self]
    have h3 : (Φ (A₁ (v - w))).1 = 0 := h1
    have h4 : A₁ (v - w) = 0 := hΦfst (A₁ (v - w)) ⟨v - w, rfl⟩ h3
    have h5 : v - w = 0 := hinj₁ (by
      change A₁ (v - w) = A₁ 0
      rw [h4, map_zero])
    exact sub_eq_zero.mp h5
  have hinjg₂ : Function.Injective (mfderiv (𝓡 n) (𝓡 n) g p₂ :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    rw [hmg₂]
    intro v w hvw
    have h2 : Φ₁ (A₂ v) = Φ₁ (A₂ w) := hvw
    have h1 : Φ₁ (A₂ (v - w)) = 0 := by
      rw [A₂.map_sub v w, Φ₁.map_sub (A₂ v) (A₂ w), h2, sub_self]
    have h3 : (Φ (A₂ (v - w))).1 = 0 := h1
    have h4 : (Φ (A₂ (v - w))).2 = 0 := (hΦzero (A₂ (v - w))).mpr ⟨v - w, rfl⟩
    have h5 : Φ (A₂ (v - w)) = 0 := Prod.ext h3 h4
    have h6 : A₂ (v - w) = 0 := Φ.injective (by rw [h5, map_zero])
    have h7 : v - w = 0 := hinj₂ (by
      change A₂ (v - w) = A₂ 0
      rw [h6, map_zero])
    exact sub_eq_zero.mp h7
  -- the inverse function theorem on each sheet
  let D₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) g p₁
  let D₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) g p₂
  have hD₁ : Function.Injective D₁ := hinjg₁
  have hD₂ : Function.Injective D₂ := hinjg₂
  let Ed₁ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofBijective D₁ (LinearMap.ker_eq_bot.mpr hD₁)
      (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hD₁))
  let Ed₂ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofBijective D₂ (LinearMap.ker_eq_bot.mpr hD₂)
      (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hD₂))
  have hEd₁ : (Ed₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      = ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ∘L
          (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
        ∘L mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁ := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hmg₁
  have hEd₂ : (Ed₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      = ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) ∘L
          (Φ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))))
        ∘L mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂ := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact hmg₂
  obtain ⟨σ₁, h₁, R₁, hR₁pos, hσ₁0, hσ₁sm, hσ₁inj, hσ₁open, hgraph₁, hh₁sm, hder₁⟩ :=
    exists_sheet_data f hf p₁ p₁ rfl Φ Ed₁ hEd₁
  obtain ⟨σ₂, h₂, R₂, hR₂pos, hσ₂0, hσ₂sm, hσ₂inj, hσ₂open, hgraph₂, hh₂sm, hder₂raw⟩ :=
    exists_sheet_data f hf p₂ p₁ hfp.symm Φ Ed₂ hEd₂
  -- the linear map `A` and its injectivity modulus
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Φ₂ ∘L A₁) ∘L (Ed₁.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  have hder₁' : fderiv ℝ h₁ 0 = A := hder₁
  have hAinj : Function.Injective A := by
    intro u v huv
    have hA : Φ₂ (A₁ (Ed₁.symm u)) = Φ₂ (A₁ (Ed₁.symm v)) := huv
    have h1 : Φ₂ (A₁ (Ed₁.symm u) - A₁ (Ed₁.symm v)) = 0 := by
      rw [Φ₂.map_sub, hA, sub_self]
    have h2 : (Φ (A₁ (Ed₁.symm u) - A₁ (Ed₁.symm v))).2 = 0 := h1
    have h3 : A₁ (Ed₁.symm u) - A₁ (Ed₁.symm v) = 0 :=
      hΦsnd _ ⟨Ed₁.symm u - Ed₁.symm v, A₁.map_sub (Ed₁.symm u) (Ed₁.symm v)⟩ h2
    have h4 : A₁ (Ed₁.symm u) = A₁ (Ed₁.symm v) := sub_eq_zero.mp h3
    have h5 : Ed₁.symm u = Ed₁.symm v := hinj₁ (by
      change A₁ (Ed₁.symm u) = A₁ (Ed₁.symm v)
      exact h4)
    have h6 : u = v := by
      have h7 : (Ed₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (Ed₁.symm u) = u := ContinuousLinearEquiv.apply_symm_apply Ed₁ u
      have h8 : (Ed₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (Ed₁.symm v) = v := ContinuousLinearEquiv.apply_symm_apply Ed₁ v
      rw [← h7, ← h8]
      exact congrArg (fun z => (Ed₁ : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) z) h5
    exact h6
  obtain ⟨α, hαpos, hAα⟩ : ∃ α : ℝ, 0 < α ∧ ∀ u : EuclideanSpace ℝ (Fin n), α * ‖u‖ ≤ ‖A u‖ := by
    have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hAinj
    have hrange : A.range = ⊤ :=
      LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hAinj)
    let Ae : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearEquiv.ofBijective A hker hrange
    have hAecoe : (Ae : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = A :=
      ContinuousLinearEquiv.coe_ofBijective _ _ _
    set M : ℝ := max ‖(Ae.symm : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n))‖ 1 with hM
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    refine ⟨M⁻¹, inv_pos.mpr hMpos, fun u => ?_⟩
    have hsymm : (Ae.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (Ae u) = u :=
      ContinuousLinearEquiv.symm_apply_apply Ae u
    have h1 : ‖u‖ ≤ ‖(Ae.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖
        * ‖Ae u‖ := by
      calc ‖u‖ = ‖(Ae.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
            (Ae u)‖ := by rw [hsymm]
        _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖Ae u‖ = ‖A u‖ := by
      have h2' : Ae u = A u := by
        rw [← hAecoe]
        rfl
      rw [h2']
    rw [h2] at h1
    have h3 : ‖u‖ ≤ M * ‖A u‖ :=
      le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    calc M⁻¹ * ‖u‖ ≤ M⁻¹ * (M * ‖A u‖) := mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hMpos.le)
      _ = (M⁻¹ * M) * ‖A u‖ := by ring
      _ = ‖A u‖ := by rw [inv_mul_cancel₀ hMpos.ne', one_mul]
  -- the graph functions vanish at `0` and their derivatives
  have hh₁0 : h₁ 0 = 0 := by
    have h := hgraph₁ 0 (by simpa using hR₁pos.le)
    rw [hσ₁0, sub_self, map_zero] at h
    exact (Prod.ext_iff.mp h).2.symm
  have hh₂0 : h₂ 0 = 0 := by
    have h := hgraph₂ 0 (by simpa using hR₂pos.le)
    rw [hσ₂0, ← hfp, sub_self, map_zero] at h
    exact (Prod.ext_iff.mp h).2.symm
  have hder₂ : fderiv ℝ h₂ 0 = 0 := by
    have hzero : Φ₂ ∘L mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂ = 0 := by
      rw [show mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂ = A₂ from rfl]
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
      exact (hΦzero (A₂ v)).mpr ⟨v, rfl⟩
    rw [hder₂raw, hzero]
    simp
  -- the Taylor bounds
  obtain ⟨C₁, hC₁pos, hC₁⟩ := taylor_second_order_ball_gen h₁ hh₁sm 0 1 one_pos
  obtain ⟨C₂, hC₂pos, hC₂⟩ := taylor_second_order_ball_gen h₂ hh₂sm 0 1 one_pos
  have hcomb_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin n) => h₁ u - h₂ u - A u) :=
    (hh₁sm.sub hh₂sm).sub A.contDiff
  obtain ⟨C₃, hC₃pos, hC₃⟩ := taylor_second_order_ball_gen _ hcomb_sm 0 1 one_pos
  have hA0 : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => A u) 0 = A :=
    ContinuousLinearMap.fderiv A
  have hcomb0 : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => h₁ u - h₂ u - A u) 0 = 0 := by
    have hd₁ : DifferentiableAt ℝ h₁ 0 := (hh₁sm.differentiable (by simp)) 0
    have hd₂ : DifferentiableAt ℝ h₂ 0 := (hh₂sm.differentiable (by simp)) 0
    have hdA : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin n) => A u) 0 := A.differentiableAt
    change fderiv ℝ ((h₁ - h₂) - fun u : EuclideanSpace ℝ (Fin n) => A u) 0 = 0
    rw [fderiv_sub (hd₁.sub hd₂) hdA, fderiv_sub hd₁ hd₂, hder₁', hder₂, hA0]
    simp
  have hcombval : (fun u : EuclideanSpace ℝ (Fin n) => h₁ u - h₂ u - A u) 0 = 0 := by
    simp [hh₁0, hh₂0]
  -- the radius and the constant
  set R₀ : ℝ := min (min R₁ R₂) 1 with hR₀def
  have hR₀pos : 0 < R₀ := lt_min (lt_min hR₁pos hR₂pos) one_pos
  have hR₀R₁ : R₀ ≤ R₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₀R₂ : R₀ ≤ R₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₀1 : R₀ ≤ 1 := min_le_right _ _
  set K : ℝ := max (max C₂ C₃) (‖A‖ + C₁ * R₀) + 1 with hKdef
  have hKpos : 0 < K := by
    have h0 : (0 : ℝ) ≤ max (max C₂ C₃) (‖A‖ + C₁ * R₀) :=
      le_trans (le_trans hC₂pos.le (le_max_left C₂ C₃)) (le_max_left _ _)
    rw [hKdef]; linarith
  have hC₃K : C₃ ≤ K := by
    rw [hKdef]
    linarith [le_trans (le_max_right C₂ C₃) (le_max_left (max C₂ C₃) (‖A‖ + C₁ * R₀))]
  have hC₂K : C₂ ≤ K := by
    rw [hKdef]
    linarith [le_trans (le_max_left C₂ C₃) (le_max_left (max C₂ C₃) (‖A‖ + C₁ * R₀))]
  have hAK : ‖A‖ + C₁ * R₀ ≤ K := by
    rw [hKdef]
    linarith [le_max_right (max C₂ C₃) (‖A‖ + C₁ * R₀)]
  refine ⟨Φ, σ₁, σ₂, h₁, h₂, A, α, K, R₀, hαpos, hKpos, hR₀pos, hAα, hσ₁0, hσ₂0,
    hσ₁sm, hσ₂sm, hσ₁inj R₀ hR₀pos hR₀R₁, hσ₂inj R₀ hR₀pos hR₀R₂,
    hσ₁open R₀ hR₀pos hR₀R₁, hσ₂open R₀ hR₀pos hR₀R₂,
    (fun u hu => hgraph₁ u (le_trans hu hR₀R₁)),
    (fun u hu => hgraph₂ u (le_trans hu hR₀R₂)), ?_, ?_, ?_⟩
  · -- the two graph functions differ by `A` to second order
    intro u hu
    have h := hC₃ u (le_trans hu hR₀1)
    have h' : ‖h₁ u - h₂ u - A u‖ ≤ C₃ * ‖u‖ ^ 2 := by
      simpa [zero_add, hcomb0, hcombval, hh₁0, hh₂0, ContinuousLinearMap.zero_apply,
        map_zero] using h
    exact le_trans h' (mul_le_mul_of_nonneg_right hC₃K (sq_nonneg _))
  · -- the second graph function vanishes to second order
    intro u hu
    have h := hC₂ u (le_trans hu hR₀1)
    have h' : ‖h₂ u‖ ≤ C₂ * ‖u‖ ^ 2 := by
      simpa [zero_add, hder₂, hh₂0, ContinuousLinearMap.zero_apply] using h
    exact le_trans h' (mul_le_mul_of_nonneg_right hC₂K (sq_nonneg _))
  · -- the first graph function is bounded by `K ‖u‖`
    intro u hu
    have h := hC₁ u (le_trans hu hR₀1)
    have h' : ‖h₁ u - A u‖ ≤ C₁ * ‖u‖ ^ 2 := by
      simpa [zero_add, hder₁', hh₁0, ContinuousLinearMap.zero_apply] using h
    have h2 : ‖h₁ u‖ ≤ ‖A u‖ + C₁ * ‖u‖ ^ 2 := by
      have h3 : h₁ u = (h₁ u - A u) + A u := by abel
      calc ‖h₁ u‖ = ‖(h₁ u - A u) + A u‖ := congrArg Norm.norm h3
        _ ≤ ‖h₁ u - A u‖ + ‖A u‖ := norm_add_le _ _
        _ ≤ C₁ * ‖u‖ ^ 2 + ‖A u‖ := add_le_add h' le_rfl
        _ = ‖A u‖ + C₁ * ‖u‖ ^ 2 := by ring
    have h4 : ‖A u‖ ≤ ‖A‖ * ‖u‖ := A.le_opNorm u
    have h5 : C₁ * ‖u‖ ^ 2 ≤ (C₁ * R₀) * ‖u‖ := by
      have h6 : C₁ * ‖u‖ ≤ C₁ * R₀ := mul_le_mul_of_nonneg_left hu hC₁pos.le
      calc C₁ * ‖u‖ ^ 2 = (C₁ * ‖u‖) * ‖u‖ := by ring
        _ ≤ (C₁ * R₀) * ‖u‖ := mul_le_mul_of_nonneg_right h6 (norm_nonneg u)
    have h7 : ‖A u‖ + C₁ * ‖u‖ ^ 2 ≤ (‖A‖ + C₁ * R₀) * ‖u‖ := by
      rw [add_mul]
      exact add_le_add h4 h5
    exact le_trans h2 (le_trans h7 (mul_le_mul_of_nonneg_right hAK (norm_nonneg u)))

end Work.Whitney
