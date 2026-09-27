import Mathlib
import Submission.Work.Embedding.exists_embedding_of_components
import Submission.Work.Embedding.countable_connectedComponents

open scoped Manifold ContDiff
open Topology Filter Metric

-- `letI` is needed to register the local instances below (`LocallyConnectedSpace`, `Countable`).
set_option linter.style.haveILetI false

/-!
# Reduction of the general case of Whitney's strong embedding theorem to the connected case

This file proves `Work.Embedding.exists_embedding_of_components_general`: if every *connected*
open subset of a smooth `n`-manifold `M` (`n ≥ 1`, Hausdorff, second countable, *no compactness*)
admits a smooth embedding into `ℝ^{2n}` with injective manifold derivative, then `M` itself does.

The proof is a countable disjoint-union assembly, generalising
`Work.Embedding.exists_embedding_of_components` (the compact case).

* Since `M` is locally connected and second countable it has countably many connected components
  (`Work.Embedding.countable_connectedComponents`); each component is clopen, so they form
  a countable partition of `M` by connected open sets.
* Applying the hypothesis to each component gives an embedding `E c : U c → ℝ^{2n}` with injective
  derivative.  Unlike in the compact case the image of `E c` need not be bounded, so it cannot be
  moved into a small ball by an affine map.  It is moved there by the *squeeze*
  `sq x = (√(1 + ‖x‖²))⁻¹ • x` of `ℝ^{2n}` into its open unit ball (Mathlib's
  `OpenPartialHomeomorph.univUnitBall`): this is a smooth embedding with injective derivative and
  bounded image, so `place c y = cc c + (1/4) • sq y` maps `ℝ^{2n}` onto the ball of radius `1/4`
  around a centre `cc c`, the centres being chosen pairwise at distance `≥ 2`.  Consequently the
  placed images are pairwise disjoint.
* The maps are glued by putting `e x := place (mk x) (E (mk x) x)` on the component of `x`.  On the
  neighbourhood `U (mk x)` of `x` the map `e` agrees with the smooth map of that component, which
  gives smoothness; the disjointness of the placed balls gives injectivity and injectivity of the
  derivative, and — for the topology, where compactness may no longer be used — also the
  `IsInducing` property: the ball of radius `1/2` around `cc (mk x)` meets the image of no other
  component, so a neighbourhood of `e x` inside `ℝ^{2n}` can be chosen inside the placed image of an
  arbitrary open neighbourhood of `x`.
-/

namespace Work.Embedding

/-! ## The squeeze of a Euclidean space into its unit ball -/

/-- The squeeze `x ↦ (√(1 + ‖x‖²))⁻¹ • x`: a smooth embedding of `ℝ^k` onto the open unit ball
(Mathlib's `OpenPartialHomeomorph.univUnitBall`). -/
noncomputable def sq (k : ℕ) : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) :=
  ⇑(OpenPartialHomeomorph.univUnitBall (E := EuclideanSpace ℝ (Fin k)))

theorem sq_contMDiff (k : ℕ) :
    ContMDiff (𝓡 k) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) (sq k) :=
  (OpenPartialHomeomorph.contDiff_univUnitBall (E := EuclideanSpace ℝ (Fin k)) (n := ⊤)).contMDiff

theorem sq_injective (k : ℕ) : Function.Injective (sq k) := by
  intro x y h
  have h' : (Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k))) x =
      Homeomorph.unitBall y := by
    apply Subtype.ext
    rw [Homeomorph.unitBall_apply_coe, Homeomorph.unitBall_apply_coe]
    exact h
  exact (Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k))).injective h'

theorem sq_norm_lt_one (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) : ‖sq k x‖ < 1 := by
  have h : ((Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k))) x : EuclideanSpace ℝ (Fin k))
      ∈ ball (0 : EuclideanSpace ℝ (Fin k)) 1 :=
    (Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k)) x).2
  rw [mem_ball_zero_iff] at h
  rwa [Homeomorph.unitBall_apply_coe] at h

theorem sq_isEmbedding (k : ℕ) : Topology.IsEmbedding (sq k) := by
  have h : Topology.IsEmbedding
      (Subtype.val ∘ ⇑(Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k)))) :=
    IsEmbedding.subtypeVal.comp
      (Homeomorph.isEmbedding (Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k))))
  have hfun : (Subtype.val ∘ ⇑(Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k)))) = sq k := by
    funext x
    rw [Function.comp_apply, Homeomorph.unitBall_apply_coe]
    rfl
  rwa [hfun] at h

theorem sq_fderiv_injective (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    Function.Injective
      (⇑(fderiv ℝ (sq k) x) : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) := by
  have hfun : (fun y => (OpenPartialHomeomorph.univUnitBall
        (E := EuclideanSpace ℝ (Fin k))).symm (sq k y)) =
      fun y : EuclideanSpace ℝ (Fin k) => y := by
    funext y
    exact PartialHomeomorph.left_inv _ (by rw [OpenPartialHomeomorph.univUnitBall_source]; trivial)
  have hdF : DifferentiableAt ℝ (sq k) x :=
    ((OpenPartialHomeomorph.contDiff_univUnitBall (E := EuclideanSpace ℝ (Fin k))
      (n := ⊤)).differentiable (by simp)).differentiableAt
  have hmem : sq k x ∈ ball (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    rw [show sq k x = ↑(Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k)) x) from
      (Homeomorph.unitBall_apply_coe x).symm]
    exact (Homeomorph.unitBall (E := EuclideanSpace ℝ (Fin k)) x).2
  have hdG : DifferentiableAt ℝ
      (⇑(OpenPartialHomeomorph.univUnitBall (E := EuclideanSpace ℝ (Fin k))).symm) (sq k x) :=
    ((OpenPartialHomeomorph.contDiffOn_univUnitBall_symm (E := EuclideanSpace ℝ (Fin k))
      (n := ⊤)).contDiffAt (isOpen_ball.mem_nhds hmem)).differentiableAt (by simp)
  have hcomp : fderiv ℝ (fun y => (OpenPartialHomeomorph.univUnitBall
        (E := EuclideanSpace ℝ (Fin k))).symm (sq k y)) x
      = (fderiv ℝ (⇑(OpenPartialHomeomorph.univUnitBall
          (E := EuclideanSpace ℝ (Fin k))).symm) (sq k x)).comp (fderiv ℝ (sq k) x) :=
    fderiv_comp (x := x) hdG hdF
  rw [hfun, fderiv_fun_id] at hcomp
  have hcomp' : (fderiv ℝ (⇑(OpenPartialHomeomorph.univUnitBall
        (E := EuclideanSpace ℝ (Fin k))).symm) (sq k x)).comp (fderiv ℝ (sq k) x)
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)) := hcomp.symm
  intro u v huv
  have h1 : (fderiv ℝ (sq k) x) (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h2 : (fderiv ℝ (⇑(OpenPartialHomeomorph.univUnitBall
        (E := EuclideanSpace ℝ (Fin k))).symm) (sq k x))
      ((fderiv ℝ (sq k) x) (u - v)) = u - v := by
    have h' := congrArg (fun (L : EuclideanSpace ℝ (Fin k) →L[ℝ]
      EuclideanSpace ℝ (Fin k)) => L (u - v)) hcomp'
    simpa using h'
  rw [h1, map_zero] at h2
  exact sub_eq_zero.mp h2.symm

theorem sq_mfderiv_injective (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    Function.Injective (mfderiv (𝓡 k) (𝓡 k) (sq k) x) := by
  rw [mfderiv_eq_fderiv]
  change Function.Injective
    (⇑(fderiv ℝ (sq k) x) : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
  exact sq_fderiv_injective k x

/-! ## Countably many components -/


/-! ## The countable disjoint-union gluing -/

theorem exists_embedding_of_components_general {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (hconn : ∀ U : TopologicalSpace.Opens M, IsConnected (U : Set M) →
      ∃ e : U → EuclideanSpace ℝ (Fin (2 * n)),
        ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
        Topology.IsEmbedding e ∧
        ∀ x : U, Function.Injective
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x)) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x) := by
  classical
  have hLC : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  letI : LocallyConnectedSpace M := hLC
  have hCount : Countable (ConnectedComponents M) := countable_connectedComponents
  letI : Countable (ConnectedComponents M) := hCount
  -- ## the components
  let U : ConnectedComponents M → TopologicalSpace.Opens M := compOpens
  have hUconn : ∀ c, IsConnected (U c : Set M) := fun c => isConnected_compOpens c
  have hUclosed : ∀ c, IsClosed (U c : Set M) := fun c => isClosed_compOpens c
  have hmemU : ∀ x : M, x ∈ (U (ConnectedComponents.mk x) : Set M) :=
    fun x => (mem_compOpens _ x).mpr rfl
  -- ## the embeddings provided on the components
  have hcomp : ∀ c : ConnectedComponents M, ∃ e : ↥(U c) → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
        Topology.IsEmbedding e ∧
        ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) :=
    fun c => hconn (U c) (hUconn c)
  let Ec : (c : ConnectedComponents M) → ↥(U c) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun c => Classical.choose (hcomp c)
  have hEc : ∀ c : ConnectedComponents M,
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (Ec c) ∧
        Topology.IsEmbedding (Ec c) ∧
        ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) (Ec c) x) :=
    fun c => Classical.choose_spec (hcomp c)
  -- ## pairwise separated centres, one per component
  obtain ⟨t, ht⟩ := Countable.exists_injective_nat (ConnectedComponents M)
  let b : EuclideanSpace ℝ (Fin (2 * n)) := EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ)
  have hb : ‖b‖ = 1 := by
    rw [show b = PiLp.single 2 (⟨0, by omega⟩ : Fin (2 * n)) (1 : ℝ) from rfl,
      PiLp.norm_single, norm_one]
  let cc : ConnectedComponents M → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun c => ((2 * ((t c : ℕ) : ℝ)) + 1) • b
  have hcc_sep : ∀ c d : ConnectedComponents M, c ≠ d → 2 ≤ ‖cc c - cc d‖ := by
    intro c d hcd
    have hne : t c ≠ t d := fun h => hcd (ht h)
    show 2 ≤ ‖((2 * ((t c : ℕ) : ℝ)) + 1) • b - ((2 * ((t d : ℕ) : ℝ)) + 1) • b‖
    rw [← sub_smul, norm_smul, hb, mul_one, Real.norm_eq_abs]
    exact two_le_abs_two_mul_add_one_sub hne
  -- ## the placement map of each component
  let place : ConnectedComponents M → EuclideanSpace ℝ (Fin (2 * n)) →
      EuclideanSpace ℝ (Fin (2 * n)) := fun c y => cc c + (1/4 : ℝ) • sq (2 * n) y
  have haffine_cdiff : ∀ c, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z) :=
    fun c => contDiff_const.add (contDiff_id.const_smul (1/4 : ℝ))
  have haffine : ∀ c, ContMDiff (𝓡 (2 * n)) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z) :=
    fun c => (haffine_cdiff c).contMDiff
  have hplace_smooth : ∀ c, ContMDiff (𝓡 (2 * n)) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (place c) := by
    intro c
    have hdecomp : place c = (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z) ∘
        (sq (2 * n)) := rfl
    rw [hdecomp]
    exact (haffine c).comp (sq_contMDiff (2 * n))
  have hplace_inj : ∀ c, Function.Injective (place c) := by
    intro c
    have hdecomp : place c = (fun w : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • w) ∘
        (sq (2 * n)) := rfl
    rw [hdecomp]
    refine Function.Injective.comp ?_ (sq_injective (2 * n))
    intro y z hyz
    have h3 : cc c + (1/4 : ℝ) • y = cc c + (1/4 : ℝ) • z := hyz
    exact injective_smul_of_ne_zero (by norm_num : (1/4 : ℝ) ≠ 0) (add_left_cancel h3)
  have hplace_norm : ∀ (c : ConnectedComponents M) (y : EuclideanSpace ℝ (Fin (2 * n))),
      ‖place c y - cc c‖ < 1/4 := by
    intro c y
    have h := mul_lt_mul_of_pos_left (sq_norm_lt_one (2 * n) y) (by norm_num : (0 : ℝ) < 1/4)
    rw [show place c y = cc c + (1/4 : ℝ) • sq (2 * n) y from rfl, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ (1/4 : ℝ))]
    linarith
  have hplace_dist : ∀ (c : ConnectedComponents M) (y : EuclideanSpace ℝ (Fin (2 * n))),
      dist (cc c) (place c y) < 1/4 := by
    intro c y
    rw [dist_eq_norm, norm_sub_rev]
    exact hplace_norm c y
  have hplace_emb : ∀ c, Topology.IsEmbedding (place c) := by
    intro c
    have hA : Topology.IsEmbedding
        (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z) := by
      have h1fun : ⇑(Homeomorph.smulOfNeZero (1/4 : ℝ) (by norm_num) :
          EuclideanSpace ℝ (Fin (2 * n)) ≃ₜ EuclideanSpace ℝ (Fin (2 * n))) =
          fun z : EuclideanSpace ℝ (Fin (2 * n)) => (1/4 : ℝ) • z := by
        funext z
        simp
      have h2fun : ⇑(Homeomorph.addLeft (cc c) :
          EuclideanSpace ℝ (Fin (2 * n)) ≃ₜ EuclideanSpace ℝ (Fin (2 * n))) =
          fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + z := by
        funext z
        simp
      have h1 : Topology.IsEmbedding
          (fun z : EuclideanSpace ℝ (Fin (2 * n)) => (1/4 : ℝ) • z) := by
        rw [← h1fun]
        exact (Homeomorph.smulOfNeZero (1/4 : ℝ) (by norm_num) :
          EuclideanSpace ℝ (Fin (2 * n)) ≃ₜ EuclideanSpace ℝ (Fin (2 * n))).isEmbedding
      have h2 : Topology.IsEmbedding
          (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + z) := by
        rw [← h2fun]
        exact (Homeomorph.addLeft (cc c) :
          EuclideanSpace ℝ (Fin (2 * n)) ≃ₜ EuclideanSpace ℝ (Fin (2 * n))).isEmbedding
      have h3 := h2.comp h1
      simpa only [Function.comp_def] using h3
    have hdecomp : place c = (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z) ∘
        (sq (2 * n)) := rfl
    rw [hdecomp]
    exact hA.comp (sq_isEmbedding (2 * n))
  have hplace_deriv : ∀ (c : ConnectedComponents M) (y : EuclideanSpace ℝ (Fin (2 * n))),
      Function.Injective (mfderiv (𝓡 (2 * n)) (𝓡 (2 * n)) (place c) y) := by
    intro c y
    rw [mfderiv_eq_fderiv]
    change Function.Injective (⇑(fderiv ℝ (place c) y) :
      EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    have hdecomp : place c = (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z) ∘
        (sq (2 * n)) := rfl
    have hdF : DifferentiableAt ℝ (sq (2 * n)) y :=
      ((sq_contMDiff (2 * n)).contDiff.differentiable (by simp)).differentiableAt
    have hdG : DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z) (sq (2 * n) y) :=
      ((haffine_cdiff c).differentiable (by simp)).differentiableAt
    have hfd : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (2 * n)) => cc c + (1/4 : ℝ) • z)
        (sq (2 * n) y) = (1/4 : ℝ) •
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_const_add_smul (cc c) (1/4 : ℝ) (sq (2 * n) y)
    rw [hdecomp, fderiv_comp (x := y) hdG hdF, hfd, ContinuousLinearMap.coe_comp]
    exact Function.Injective.comp
      (injective_smul_id (E := EuclideanSpace ℝ (Fin (2 * n))) (by norm_num : (1/4 : ℝ) ≠ 0))
      (sq_fderiv_injective (2 * n) y)
  -- ## the glued map
  let G : (c : ConnectedComponents M) → M → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun c x => if h : x ∈ (U c : Set M) then place c (Ec c ⟨x, h⟩) else 0
  have hG_apply : ∀ (c : ConnectedComponents M) (x : M), G c x =
      (if h : x ∈ (U c : Set M) then place c (Ec c ⟨x, h⟩) else 0) := fun c x => rfl
  have hG_pos : ∀ (c : ConnectedComponents M) (x : M) (hx : x ∈ (U c : Set M)),
      G c x = place c (Ec c ⟨x, hx⟩) := by
    intro c x hx
    rw [hG_apply]
    exact dif_pos hx
  have hG_neg : ∀ (c : ConnectedComponents M) (x : M), x ∉ (U c : Set M) → G c x = 0 := by
    intro c x hx
    rw [hG_apply]
    exact dif_neg hx
  let e : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x => G (ConnectedComponents.mk x) x
  have he_apply : ∀ x : M, e x = place (ConnectedComponents.mk x)
      (Ec (ConnectedComponents.mk x) ⟨x, hmemU x⟩) := fun x => hG_pos _ x (hmemU x)
  have he_apply_of_eq : ∀ {c : ConnectedComponents M} {y : M}, ConnectedComponents.mk y = c →
      e y = G c y := by
    intro c y h
    show G (ConnectedComponents.mk y) y = G c y
    rw [h]
  -- ## smoothness of each `G c`
  have hG_smooth : ∀ c, ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (G c) := by
    intro c
    have hsub1 : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ↥(U c) => G c ↑z) := by
      have heq : (fun z : ↥(U c) => G c ↑z) = (fun z => place c (Ec c z)) := by
        funext z
        exact hG_pos c ↑z z.2
      rw [heq]
      exact (hplace_smooth c).comp (hEc c).1
    have h1 : ∀ y ∈ (U c : Set M),
        ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (G c) y :=
      fun y hy => contMDiffAt_subtype_iff.mp (hsub1.contMDiffAt (x := ⟨y, hy⟩))
    have h2 : ∀ y ∉ (U c : Set M),
        ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (G c) y := by
      intro y hy
      have hcompl : (((U c : TopologicalSpace.Opens M) : Set M))ᶜ ∈ 𝓝 y :=
        (hUclosed c).isOpen_compl.mem_nhds hy
      have hev : G c =ᶠ[𝓝 y] (fun _ : M => (0 : EuclideanSpace ℝ (Fin (2 * n)))) :=
        Filter.eventually_of_mem hcompl fun z hz => hG_neg c z hz
      exact (contMDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin (2 * n))))).congr_of_eventuallyEq hev
    intro y
    by_cases hy : y ∈ (U c : Set M)
    · exact h1 y hy
    · exact h2 y hy
  -- ## `e` agrees with `G (mk x)` near `x`
  have hev_glue : ∀ x : M, e =ᶠ[𝓝 x] G (ConnectedComponents.mk x) := by
    intro x
    refine Filter.eventually_of_mem ((U (ConnectedComponents.mk x)).2.mem_nhds (hmemU x))
      fun y hy => ?_
    show G (ConnectedComponents.mk y) y = G (ConnectedComponents.mk x) y
    have h : ConnectedComponents.mk y = ConnectedComponents.mk x :=
      (mem_compOpens (ConnectedComponents.mk x) y).mp hy
    rw [h]
  have he_smooth : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) e := by
    intro x
    exact ((hG_smooth (ConnectedComponents.mk x)).contMDiffAt).congr_of_eventuallyEq
      (hev_glue x)
  -- ## injectivity
  have he_inj : Function.Injective e := by
    intro x y hxy
    by_cases hcd : ConnectedComponents.mk x = ConnectedComponents.mk y
    · have hy' : y ∈ (U (ConnectedComponents.mk x) : Set M) :=
        (mem_compOpens (ConnectedComponents.mk x) y).mpr hcd.symm
      have h1 : e x = place (ConnectedComponents.mk x)
          (Ec (ConnectedComponents.mk x) ⟨x, hmemU x⟩) := he_apply x
      have h2 : e y = place (ConnectedComponents.mk x)
          (Ec (ConnectedComponents.mk x) ⟨y, hy'⟩) := by
        rw [he_apply_of_eq (c := ConnectedComponents.mk x) hcd.symm]
        exact hG_pos _ y hy'
      rw [h1, h2] at hxy
      have h3 : (⟨x, hmemU x⟩ : ↥(U (ConnectedComponents.mk x))) = ⟨y, hy'⟩ :=
        Function.Injective.comp (hplace_inj _) ((hEc _).2.1).injective hxy
      exact congrArg Subtype.val h3
    · exfalso
      have hdist : 2 ≤ dist (cc (ConnectedComponents.mk x)) (cc (ConnectedComponents.mk y)) := by
        rw [dist_eq_norm]
        exact hcc_sep _ _ hcd
      have hxb : dist (cc (ConnectedComponents.mk x)) (e x) < 1 / 4 := by
        rw [he_apply x]
        exact hplace_dist _ _
      have hyb : dist (cc (ConnectedComponents.mk y)) (e y) < 1 / 4 := by
        rw [he_apply y]
        exact hplace_dist _ _
      have hstep : dist (e x) (cc (ConnectedComponents.mk y)) =
          dist (cc (ConnectedComponents.mk y)) (e y) := by rw [hxy, dist_comm]
      have htri : dist (cc (ConnectedComponents.mk x)) (cc (ConnectedComponents.mk y)) ≤
          dist (cc (ConnectedComponents.mk x)) (e x) +
            dist (cc (ConnectedComponents.mk y)) (e y) := by
        calc dist (cc (ConnectedComponents.mk x)) (cc (ConnectedComponents.mk y))
            ≤ dist (cc (ConnectedComponents.mk x)) (e x) +
              dist (e x) (cc (ConnectedComponents.mk y)) := dist_triangle _ _ _
          _ = dist (cc (ConnectedComponents.mk x)) (e x) +
              dist (cc (ConnectedComponents.mk y)) (e y) := by rw [hstep]
      linarith
  -- ## the induced topology
  have he_inducing : Topology.IsInducing e := by
    rw [Topology.isInducing_iff_nhds]
    intro x
    refine le_antisymm ?_ ?_
    · exact (he_smooth.continuous.continuousAt).tendsto.le_comap
    · intro V hV
      rw [Filter.mem_comap]
      obtain ⟨O, hOV, hOopen, hxO⟩ := mem_nhds_iff.mp hV
      let c : ConnectedComponents M := ConnectedComponents.mk x
      have hxU : x ∈ (U c : Set M) := hmemU x
      have hSopen : IsOpen ((Subtype.val : ↥(U c) → M) ⁻¹' (O : Set M)) :=
        hOopen.preimage continuous_subtype_val
      have hEmb : Topology.IsEmbedding (fun u : ↥(U c) => place c (Ec c u)) :=
        (hplace_emb c).comp (hEc c).2.1
      have hInd : IsOpen[TopologicalSpace.induced (fun u : ↥(U c) => place c (Ec c u))
          inferInstance] ((Subtype.val : ↥(U c) → M) ⁻¹' (O : Set M)) := by
        rw [← hEmb.eq_induced]
        exact hSopen
      obtain ⟨S₁, hS₁open, hS₁⟩ := isOpen_induced_iff.mp hInd
      have hxS₁ : e x ∈ S₁ := by
        rw [he_apply x]
        have hx : (⟨x, hxU⟩ : ↥(U c)) ∈ (fun u : ↥(U c) => place c (Ec c u)) ⁻¹' S₁ := by
          rw [hS₁]
          exact hxO
        exact hx
      have hxball : e x ∈ ball (cc c) (1 / 2) := by
        rw [mem_ball, he_apply x, dist_comm]
        have h4 : dist (cc c) (place c (Ec c ⟨x, hxU⟩)) < 1 / 4 := hplace_dist _ _
        linarith
      refine ⟨S₁ ∩ ball (cc c) (1 / 2), (hS₁open.inter isOpen_ball).mem_nhds ⟨hxS₁, hxball⟩, ?_⟩
      intro y hy
      obtain ⟨hyS₁, hyball⟩ := hy
      rw [mem_ball] at hyball
      have hylt : dist (cc (ConnectedComponents.mk y)) (cc c) < 2 := by
        have h1 : dist (cc (ConnectedComponents.mk y)) (e y) < 1 / 4 := by
          rw [he_apply y]
          exact hplace_dist _ _
        have h2 : dist (e y) (cc c) < 1 / 2 := hyball
        calc dist (cc (ConnectedComponents.mk y)) (cc c)
            ≤ dist (cc (ConnectedComponents.mk y)) (e y) + dist (e y) (cc c) :=
              dist_triangle _ _ _
          _ < 1 / 4 + 1 / 2 := add_lt_add h1 h2
          _ < 2 := by norm_num
      have hmk : ConnectedComponents.mk y = c := by
        by_contra hne
        have h3 : 2 ≤ ‖cc (ConnectedComponents.mk y) - cc c‖ := hcc_sep _ _ hne
        rw [dist_eq_norm] at hylt
        linarith
      have hyU : y ∈ (U c : Set M) := (mem_compOpens c y).mpr hmk
      have he_y : e y = place c (Ec c ⟨y, hyU⟩) := by
        rw [he_apply_of_eq (c := c) hmk]
        exact hG_pos c y hyU
      have hmemS₁ : (⟨y, hyU⟩ : ↥(U c)) ∈ (fun u : ↥(U c) => place c (Ec c u)) ⁻¹' S₁ := by
        show place c (Ec c ⟨y, hyU⟩) ∈ S₁
        rw [← he_y]
        exact hyS₁
      rw [hS₁] at hmemS₁
      exact hOV hmemS₁
  -- ## the derivative
  have he_deriv : ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
    intro x
    have hx : x ∈ (U (ConnectedComponents.mk x) : Set M) := hmemU x
    rw [(hev_glue x).mfderiv_eq]
    have hkey := mfderiv_comp_subtype_val (U := U (ConnectedComponents.mk x)) (x := ⟨x, hx⟩)
      (f := G (ConnectedComponents.mk x)) (hG_smooth (ConnectedComponents.mk x))
    rw [← hkey]
    have heq : (fun z : ↥(U (ConnectedComponents.mk x)) => G (ConnectedComponents.mk x) ↑z)
        = (place (ConnectedComponents.mk x) ∘ Ec (ConnectedComponents.mk x)) := by
      funext z
      exact hG_pos _ ↑z z.2
    rw [heq]
    rw [mfderiv_comp (x := ⟨x, hx⟩) (f := Ec (ConnectedComponents.mk x))
      (g := place (ConnectedComponents.mk x))
      ((hplace_smooth (ConnectedComponents.mk x)).contMDiffAt.mdifferentiableAt (by simp))
      ((hEc (ConnectedComponents.mk x)).1.contMDiffAt.mdifferentiableAt (by simp))]
    exact Function.Injective.comp
      (f := ⇑(mfderiv (𝓡 n) (𝓡 (2 * n)) (Ec (ConnectedComponents.mk x)) ⟨x, hx⟩))
      (g := ⇑(mfderiv (𝓡 (2 * n)) (𝓡 (2 * n)) (place (ConnectedComponents.mk x))
        (Ec (ConnectedComponents.mk x) ⟨x, hx⟩)))
      (hplace_deriv _ _) ((hEc (ConnectedComponents.mk x)).2.2 ⟨x, hx⟩)
  exact ⟨e, he_smooth, (Topology.isEmbedding_iff e).mpr ⟨he_inducing, he_inj⟩, he_deriv⟩

end Work.Embedding
