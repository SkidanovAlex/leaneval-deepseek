import Mathlib
import Submission.Work.Drive.sard_weak_empty_interior
import Submission.Work.Sard.submersion_local_form
import Submission.Work.MetricSquare.generic_regularization_of_family
import Submission.Work.MetricSquare.generic_regularization_of_family_face_ball
import Submission.Work.Drive.BoxParityDefs

/-!
# Avoidance of a lower-dimensional compact set by the zero set of a generic parametric family

This file supplies the analysis that the *parametric-Sard* route to the counting half of the chain
route still needs beyond transversal surjectivity: for a *generic* parameter a smooth family
`Φ : ℝ^m × ℝ^{n+1} → ℝ^n` has **no** zero on a fixed compact subset `K` of a lower-dimensional set
(`dim K < n`), provided the parameter-derivative is surjective at the base zeros.

The two mathematical ingredients are

* `interior_image_eq_empty_of_contDiffOn` — a smooth image of a set lying in a space of dimension
  `< finrank F` has empty interior (through the Hausdorff dimension bound
  `Work.Drive.interior_eq_empty_of_holder` of the workspace's Sard chapter);
* `exists_local_avoid_gen` — at a base zero `(p₀, y₀)` of the composed map `Φ (·, B ·)` whose
  parameter-derivative is onto, the *local normal form* of `Work.Sard.submersion_local_form` writes
  the zero set as the image of a map from `Fin (m + Module.finrank ℝ X - n) → ℝ`, a space of dimension
  `m + d - n < m`, so the set of parameters at which a zero occurs near `y₀` has empty interior.

The global form `exists_forall_notMem_family` (finite family of parametrised pieces) is the Baire
assembly, exactly parallel to `Work.Drive.exists_forall_good_on_compact_face`.

## Why it is needed

The engine's `TParity.faceHyp` requires, at a triple point on the boundary of the nine-box, that
**exactly one** coordinate of **exactly one** block is on a face.  The transversality half of that
condition is produced by parametric Sard (`Work.Drive.transHyp_of_good_family`,
`Work.Drive.faceHyp_direction_of_good_family`); the *positional* half ("no two coordinates are on a
face at the same time") is not, because the codimension-`2` skeleton of the box has dimension
`n - 1 < n` while a single coordinate face has dimension `n`.  This file proves the avoidance that
covers precisely the lower-dimensional part. -/

set_option maxHeartbeats 1000000

namespace Work.Drive
namespace AvoidLowDim

open Set Metric Filter
open scoped ContDiff Topology NNReal

noncomputable section

/-- **A smooth image of a lower-dimensional set has empty interior.**

If `f : E → F` is smooth on an open set `V ⊇ K` and `finrank ℝ E < finrank ℝ F`, then `f '' K` has
empty interior.  (`f` is locally Lipschitz, so `dimH (f '' K) ≤ dimH K ≤ finrank E < finrank F`, and
a set of Hausdorff dimension `< finrank F` has empty interior.) -/
theorem interior_image_eq_empty_of_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hfin : Module.finrank ℝ E < Module.finrank ℝ F) {V : Set E} (hV : IsOpen V)
    {f : E → F} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f V) {K : Set E} (hK : K ⊆ V) :
    interior (f '' K) = ∅ := by
  refine Work.Drive.interior_eq_empty_of_holder f K 1 (by norm_num) ?_ ?_
  · intro x hx
    obtain ⟨C, t, ht, hlip⟩ :=
      ((hf.contDiffAt (hV.mem_nhds (hK hx))).of_le (by simp)).exists_lipschitzOnWith
    refine ⟨C, K ∩ t, inter_mem_nhdsWithin K ht, ?_⟩
    have hmono : LipschitzOnWith C f (K ∩ t) := hlip.mono (Set.inter_subset_right (s := K))
    exact (show ((1 : ℕ) : NNReal) = 1 from Nat.cast_one) ▸ hmono.holderOnWith
  · rw [Nat.cast_one, div_one]
    exact_mod_cast hfin

/-- **Local avoidance at a base zero of the composed map.**

Let `Φ : ℝ^m × ℝ^{n+1} → ℝ^n` be smooth, `B : ℝ^d → ℝ^{n+1}` smooth with `d < n`, and let
`(p₀, y₀)` be a zero of `y ↦ Φ (p₀, B y)` at which the parameter-derivative is *onto*.  Then there
are a neighbourhood `W` of `(p₀, y₀)` in the parameter space and a compact set `A ⊆ ℝ^m` of empty
interior such that every zero of `y ↦ Φ (p, B y)` with `(p, y) ∈ W` satisfies `p ∈ A`. -/
lemma exists_local_avoid_gen (m n : ℕ) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (hX : Module.finrank ℝ X < n)
    (Φ : EuclideanSpace ℝ (Fin m) × Amb n → Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (B : X → Amb n) (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (p₀ : EuclideanSpace ℝ (Fin m)) (y₀ : X)
    (h0 : Φ (p₀, B y₀) = 0)
    (hsurjp : Function.Surjective
      (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', B y₀)) p₀)) :
    ∃ W : Set (EuclideanSpace ℝ (Fin m) × X), IsOpen W ∧ (p₀, y₀) ∈ W ∧
      ∃ A : Set (EuclideanSpace ℝ (Fin m)), IsCompact A ∧ interior A = ∅ ∧
        ∀ (p : EuclideanSpace ℝ (Fin m)) (y : X),
          (p, y) ∈ W → Φ (p, B y) = 0 → p ∈ A := by
  classical
  set u : EuclideanSpace ℝ (Fin m) × X → Tgt n :=
    fun q => Φ (q.1, B q.2) with hu
  have hu_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u := by
    rw [hu]
    exact hΦ.comp (contDiff_fst.prodMk (hB.comp contDiff_snd))
  have hfw : fderiv ℝ u (p₀, y₀) = (fderiv ℝ Φ (p₀, B y₀)).comp
      ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (X)).prod
        ((fderiv ℝ B y₀).comp
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (X)))) := by
    rw [hu]
    exact (((hΦ.differentiable (by simp) (p₀, B y₀)).hasFDerivAt).comp (p₀, y₀)
      (hasFDerivAt_fst.prodMk
        ((hB.differentiable (by simp) y₀).hasFDerivAt.comp (p₀, y₀) hasFDerivAt_snd))).fderiv
  have hfw_apply : ∀ (v : EuclideanSpace ℝ (Fin m)) (w : X),
      fderiv ℝ u (p₀, y₀) (v, w) = (fderiv ℝ Φ (p₀, B y₀)) (v, fderiv ℝ B y₀ w) := by
    intro v w
    rw [hfw, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    simp
  have h3 : ∀ v : EuclideanSpace ℝ (Fin m),
      (fderiv ℝ Φ (p₀, B y₀)) (v, 0)
        = fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', B y₀)) p₀ v := by
    intro v
    have h := congrArg (fun (L : EuclideanSpace ℝ (Fin m) →L[ℝ] Tgt n) => L v)
      (Work.MetricSquare.fd_comp_inl Φ hΦ p₀ (B y₀))
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using h
  have hsurju : Function.Surjective (fderiv ℝ u (p₀, y₀)) := by
    intro w
    obtain ⟨v, hv⟩ := hsurjp w
    refine ⟨(v, 0), ?_⟩
    rw [hfw_apply, map_zero]
    exact (h3 v).trans hv
  have hu0 : u (p₀, y₀) = 0 := h0
  -- ## the linear algebra datum of the normal form
  set K0 : Submodule ℝ (EuclideanSpace ℝ (Fin m) × X) :=
    (fderiv ℝ u (p₀, y₀) : EuclideanSpace ℝ (Fin m) × X →ₗ[ℝ] Tgt n).ker
    with hK0
  obtain ⟨C0, hC0⟩ := K0.exists_isCompl
  have hXd : Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × X) = m + Module.finrank ℝ X := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin]
  have hK0codim : Module.finrank ℝ ↥K0 + n = m + Module.finrank ℝ X := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℝ u (p₀, y₀) : EuclideanSpace ℝ (Fin m) × X →ₗ[ℝ] Tgt n)
    rw [LinearMap.range_eq_top.mpr hsurju, finrank_top, finrank_euclideanSpace_fin, hXd] at h
    have hker : (fderiv ℝ u (p₀, y₀) :
        EuclideanSpace ℝ (Fin m) × X →ₗ[ℝ] Tgt n).ker = K0 := hK0.symm
    rw [hker] at h
    omega
  have hK0dim : Module.finrank ℝ ↥K0 = m + Module.finrank ℝ X - n := by omega
  obtain ⟨φ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (R := ℝ) (M := ↥K0) (M' := Fin (m + Module.finrank ℝ X - n) → ℝ) (by rw [hK0dim]; simp)
  let lam : EuclideanSpace ℝ (Fin m) × X →L[ℝ]
      (Fin (m + Module.finrank ℝ X - n) → ℝ) :=
    LinearMap.toContinuousLinearMap ((φ : ↥K0 →ₗ[ℝ] _).comp (K0.projectionOnto C0 hC0))
  have hlamker : lam.ker = C0 := by
    change (((φ : ↥K0 →ₗ[ℝ] (Fin (m + Module.finrank ℝ X - n) → ℝ)).comp (K0.projectionOnto C0 hC0)) :
      (EuclideanSpace ℝ (Fin m) × X) →ₗ[ℝ] _).ker = C0
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr φ.injective, Submodule.comap_bot,
      Submodule.ker_projectionOnto]
  have hlam : Disjoint (fderiv ℝ u (p₀, y₀)).ker lam.ker := by
    rw [hlamker, ← hK0]
    exact hC0.disjoint
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × X)
      = Module.finrank ℝ (Tgt n) + (m + Module.finrank ℝ X - n) := by
    rw [hXd, finrank_euclideanSpace_fin]
    omega
  -- ## the normal form
  obtain ⟨e, hx0t, he_smooth, he_u, he_symm, he_bij⟩ :=
    Work.Sard.submersion_local_form (m + Module.finrank ℝ X - n) hm u hu_smooth (p₀, y₀) hsurju lam hlam
  set γ : (Fin (m + Module.finrank ℝ X - n) → ℝ) → EuclideanSpace ℝ (Fin m) :=
    fun w => (e ((0 : Tgt n), w)).1 with hγ
  set Uγ : Set (Fin (m + Module.finrank ℝ X - n) → ℝ) := {w | ((0 : Tgt n), w) ∈ e.source} with hUγ
  have hc₀source : ((0 : Tgt n), lam (p₀, y₀)) ∈ e.source := by
    have h := e.map_target hx0t
    rwa [he_symm (p₀, y₀) hx0t, hu0] at h
  have hUγ_open : IsOpen Uγ := by
    rw [hUγ]
    exact e.open_source.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hUγ_open.mem_nhds hc₀source)
  set Kc : Set (Fin (m + Module.finrank ℝ X - n) → ℝ) := Metric.closedBall (lam (p₀, y₀)) (ρ / 2) with hKc
  have hKc_Uγ : Kc ⊆ Uγ := by
    intro w hw
    refine hρsub ?_
    rw [Metric.mem_ball]
    have h2 : dist w (lam (p₀, y₀)) ≤ ρ / 2 := Metric.mem_closedBall.mp hw
    linarith
  set A : Set (EuclideanSpace ℝ (Fin m)) := γ '' Kc with hA
  have hA_compact : IsCompact A := by
    rw [hA]
    refine IsCompact.image_of_continuousOn (isCompact_closedBall (lam (p₀, y₀)) (ρ / 2)) ?_
    have hcont : ContinuousOn (fun w : Fin (m + Module.finrank ℝ X - n) → ℝ => e ((0 : Tgt n), w)) Kc :=
      he_smooth.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun w hw => hKc_Uγ hw)
    rw [hγ]
    exact hcont.fst
  have hA_int : interior A = ∅ := by
    rw [hA]
    have hγ_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ Uγ := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : Fin (m + Module.finrank ℝ X - n) → ℝ => ((0 : Tgt n), w)) Uγ :=
        (contDiff_const.prodMk contDiff_id).contDiffOn
      have h2 := he_smooth.comp h1 (fun w hw => hw)
      rw [hγ]
      exact h2.fst
    refine interior_image_eq_empty_of_contDiffOn (E := Fin (m + Module.finrank ℝ X - n) → ℝ)
      (F := EuclideanSpace ℝ (Fin m)) ?_ hUγ_open hγ_smooth (fun w hw => hKc_Uγ hw)
    rw [Module.finrank_fin_fun, finrank_euclideanSpace_fin]
    omega
  refine ⟨e.target ∩ lam ⁻¹' Metric.ball (lam (p₀, y₀)) (ρ / 4), ?_, ?_, A, hA_compact, hA_int,
    ?_⟩
  · exact e.open_target.inter (Metric.isOpen_ball.preimage lam.continuous)
  · exact ⟨hx0t, Metric.mem_ball_self (by linarith)⟩
  · intro p y hW hzero
    obtain ⟨ht, hb⟩ := hW
    have hq : (p, y) = e ((0 : Tgt n), lam (p, y)) := by
      have huq : u (p, y) = 0 := hzero
      have h1 : e.symm (p, y) = ((0 : Tgt n), lam (p, y)) := by
        rw [he_symm (p, y) ht, huq]
      exact (e.right_inv ht).symm.trans (congrArg e h1)
    have hp : p = γ (lam (p, y)) := by
      rw [hγ]
      simpa using congrArg Prod.fst hq
    rw [hp]
    refine ⟨lam (p, y), ?_, rfl⟩
    rw [hKc, Metric.mem_closedBall]
    have h4 := Metric.mem_ball.mp hb
    linarith


/-- **Global avoidance for a finite family of lower-dimensional pieces.**

Let `Φ : ℝ^m × ℝ^{n+1} → ℝ^n` be smooth and, for each `i`, let `B i : ℝ^{d i} → ℝ^{n+1}` be a smooth
parametrisation with `d i < n` and `K i` compact.  If the parameter-derivative of `Φ` is onto at every
zero lying over `⋃ i B i '' K i`, then there is a parameter `p` with `‖p‖ < ε` such that
`Φ (p, B i y) ≠ 0` for every `i` and every `y ∈ K i`. -/
theorem exists_forall_notMem_family (m n : ℕ) (ι : Type*) [Fintype ι]
    (X : ι → Type*) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, FiniteDimensional ℝ (X i)] (hX : ∀ i, Module.finrank ℝ (X i) < n)
    (B : ∀ i, X i → Amb n)
    (hB : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B i))
    (K : ∀ i, Set (X i)) (hK : ∀ i, IsCompact (K i))
    (Φ : EuclideanSpace ℝ (Fin m) × Amb n → Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (y : Amb n), ‖p‖ < ε →
      (∃ i, y ∈ B i '' K i) → Φ (p, y) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', y)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧ ∀ i, ∀ y ∈ K i, Φ (p, B i y) ≠ 0 := by
  classical
  set Bad : Set (EuclideanSpace ℝ (Fin m)) :=
    {p | ∃ i, ∃ y ∈ K i, Φ (p, B i y) = 0} with hBad
  have hBad_int : interior (Bad ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) = ∅ := by
    by_contra hne
    obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hp₀' : p₀ ∈ Bad ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε := interior_subset hp₀
    obtain ⟨ε', hε'pos, hε'sub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp₀)
    have hp₀norm : ‖p₀‖ < ε := by
      have h := Metric.mem_ball.mp hp₀'.2
      rwa [dist_zero_right] at h
    set ε'' : ℝ := min ε' (ε - ‖p₀‖) with hε''def
    have hε''pos : 0 < ε'' := lt_min hε'pos (by linarith)
    have hsmall : Metric.closedBall p₀ (ε'' / 2) ⊆
        Bad ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε := by
      intro p hp
      have hd : dist p p₀ ≤ ε'' / 2 := Metric.mem_closedBall.mp hp
      have hmem : p ∈ Metric.ball p₀ ε' := by
        rw [Metric.mem_ball]
        have h2 : ε'' ≤ ε' := by rw [hε''def]; exact min_le_left _ _
        linarith
      refine ⟨(interior_subset (hε'sub hmem)).1, ?_⟩
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖p‖ ≤ dist p p₀ + ‖p₀‖ := by
        calc ‖p‖ = ‖(p - p₀) + p₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖p - p₀‖ + ‖p₀‖ := norm_add_le _ _
          _ = dist p p₀ + ‖p₀‖ := by rw [dist_eq_norm]
      linarith [min_le_right ε' (ε - ‖p₀‖), hε''def]
    set Zfam : ∀ i : ι, Set (EuclideanSpace ℝ (Fin m) × X i) :=
      fun i => {x | x.1 ∈ Metric.closedBall p₀ (ε'' / 2) ∧ x.2 ∈ K i ∧ Φ (x.1, B i x.2) = 0}
      with hZfam
    have hZi : ∀ i : ι, IsCompact (Zfam i) := by
      intro i
      have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin m) × X i =>
          Φ (x.1, B i x.2)) :=
        hΦ.continuous.comp (continuous_fst.prodMk ((hB i).continuous.comp continuous_snd))
      have hset : Zfam i = (Metric.closedBall p₀ (ε'' / 2) ×ˢ K i) ∩
          {x : EuclideanSpace ℝ (Fin m) × X i |
            Φ (x.1, B i x.2) = 0} := by
        rw [hZfam]
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
        tauto
      rw [hset]
      exact IsCompact.of_isClosed_subset
        ((isCompact_closedBall p₀ (ε'' / 2)).prod (hK i))
        (((isCompact_closedBall p₀ (ε'' / 2)).isClosed.prod (hK i).isClosed).inter
          (isClosed_eq hcont continuous_const))
        Set.inter_subset_left
    have hex : ∀ i : ι, ∃ (s : Finset ↥(Zfam i)) (A : ↥(Zfam i) → Set (EuclideanSpace ℝ (Fin m))),
        (∀ x ∈ s, IsCompact (A x) ∧ interior (A x) = ∅) ∧
        ∀ p ∈ Metric.closedBall p₀ (ε'' / 2), ∀ y ∈ K i, Φ (p, B i y) = 0 →
          ∃ x ∈ s, p ∈ A x := by
      intro i
      have hloc : ∀ x : ↥(Zfam i), ∃ (W : Set (EuclideanSpace ℝ (Fin m) ×
            X i)) (A : Set (EuclideanSpace ℝ (Fin m))),
          IsOpen W ∧ (x.1 ∈ W) ∧ IsCompact A ∧ interior A = ∅ ∧
          ∀ (p : EuclideanSpace ℝ (Fin m)) (y : X i),
            (p, y) ∈ W → Φ (p, B i y) = 0 → p ∈ A := by
        intro x
        obtain ⟨hx1, hx2, hx3⟩ := x.2
        have hnorm : ‖x.1.1‖ < ε := by
          have h := (hsmall hx1).2
          rwa [Metric.mem_ball, dist_zero_right] at h
        obtain ⟨W, hW1, hW2, A, hA1, hA2, hA3⟩ :=
          (exists_local_avoid_gen m n (hX i) Φ hΦ (B i) (hB i) x.1.1 x.1.2 hx3)
            (hsurj x.1.1 (B i x.1.2) hnorm ⟨i, x.1.2, hx2, rfl⟩ hx3)
        exact ⟨W, A, hW1, hW2, hA1, hA2, hA3⟩
      choose W A hWopen hxW hAcomp hAint hAprop using hloc
      obtain ⟨s, hs⟩ := (hZi i).elim_finite_subcover (fun x : ↥(Zfam i) => W x)
        (fun x => hWopen x)
        (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
      refine ⟨s, fun x => A x, ?_, ?_⟩
      · intro x hx
        exact ⟨hAcomp x, hAint x⟩
      · intro p hp y hy hzero
        have hxZi : (p, y) ∈ Zfam i := ⟨hp, hy, hzero⟩
        obtain ⟨x, hxs, hxW'⟩ := Set.mem_iUnion₂.mp (hs hxZi)
        exact ⟨x, hxs, hAprop x p y hxW' hzero⟩
    choose s A hAfin hAprop using hex
    have hcover : Metric.closedBall p₀ (ε'' / 2) ⊆
        ⋃ (q : Σ i : ι, ↥(s i)), A q.1 q.2 := by
      intro p hp
      obtain ⟨i, y, hy, hzero⟩ := (hsmall hp).1
      obtain ⟨x, hxs, hpx⟩ := hAprop i p hp y hy hzero
      exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hxs⟩⟩, hpx⟩
    have hbaire : interior (⋃ (q : Σ i : ι, ↥(s i)), A q.1 q.2) = ∅ :=
      Work.Sard.wp.interior_eq_empty_iUnion_isClosed
        (fun q => ((hAfin q.1 q.2.1 q.2.2).1).isClosed)
        (fun q => (hAfin q.1 q.2.1 q.2.2).2)
    have hint : (interior (Metric.closedBall p₀ (ε'' / 2))).Nonempty :=
      ⟨p₀, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
        (Metric.mem_ball_self (by linarith))⟩
    have hsub : interior (Metric.closedBall p₀ (ε'' / 2)) ⊆
        interior (⋃ (q : Σ i : ι, ↥(s i)), A q.1 q.2) := interior_mono hcover
    rw [hbaire] at hsub
    exact hint.ne_empty (Set.Subset.antisymm hsub (Set.empty_subset _))
  obtain ⟨p, hpball, hp⟩ := Work.MetricSquare.exists_norm_lt_notMem_of_interior_eq_empty
    (Bad ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε) hBad_int hε
  refine ⟨p, hpball, ?_⟩
  intro i y hy hzero
  exact hp ⟨⟨i, y, hy, hzero⟩, by rw [Metric.mem_ball, dist_zero_right]; exact hpball⟩


/-- The two possible face values of a coordinate, as a real number. -/
def faceVal (b : Bool) : ℝ := if b then 1 else 0

lemma faceVal_decide (x : ℝ) (h : x = 0 ∨ x = 1) : faceVal (decide (x = 1)) = x := by
  rcases h with h | h <;> simp [faceVal, h]

/-- The `i`-th coordinate functional on the nine-box. -/
def coordFun (i : Fin 9) : Amb 8 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 9 => ℝ) i

lemma coordFun_apply (i : Fin 9) (x : Amb 8) : coordFun i x = x i := by
  simp [coordFun, PiLp.proj_apply]

/-- The direction space of the pair of coordinates `(i,j)`: the points whose `i`-th and `j`-th
coordinates vanish.  This is the `7`-dimensional piece underlying the two-face set of `(i,j)`. -/
def pairDir (i j : Fin 9) : Submodule ℝ (Amb 8) := (coordFun i).ker ⊓ (coordFun j).ker

lemma mem_pairDir {i j : Fin 9} {z : Amb 8} : z ∈ pairDir i j ↔ z i = 0 ∧ z j = 0 := by
  simp [pairDir, coordFun_apply]

/-- The base point of the face pair `(i,j)` with face values `b₁`, `b₂`. -/
def faceBase (i j : Fin 9) (b₁ b₂ : Bool) : Amb 8 :=
  WithLp.toLp 2 (fun k : Fin 9 => if k = i then faceVal b₁ else if k = j then faceVal b₂ else 0)

lemma faceBase_apply_fst (i j : Fin 9) (b₁ b₂ : Bool) : faceBase i j b₁ b₂ i = faceVal b₁ := by
  simp [faceBase, WithLp.ofLp_toLp]

lemma faceBase_apply_snd {i j : Fin 9} (h : j ≠ i) (b₁ b₂ : Bool) :
    faceBase i j b₁ b₂ j = faceVal b₂ := by
  simp [faceBase, WithLp.ofLp_toLp, h]

lemma faceBase_apply_of_ne {i j k : Fin 9} (hk : k ≠ i) (hk' : k ≠ j) (b₁ b₂ : Bool) :
    faceBase i j b₁ b₂ k = 0 := by
  simp [faceBase, WithLp.ofLp_toLp, hk, hk']

/-- The index type of the two-face pieces of the nine-box: a pair of coordinates together with the
two face values.  (The pairs with equal coordinates carry the junk piece `⊥`.) -/
abbrev FaceIdx := (Fin 9 × Fin 9) × Bool × Bool

/-- **Avoidance of the two-face set of the nine-box.**

Let `Φ : ℝ^m × ℝ^9 → ℝ^8` be smooth with the parameter-derivative onto at every zero over the box.
Then there is a parameter `p` with `‖p‖ < ε` such that `Φ (p, ·)` has **no** zero at a point of the
nine-box lying on two coordinate faces at once — the positional half of `TParity.faceHyp`.

The proof feeds `exists_forall_notMem_family` with the `81 × 4` pieces: for the pair `(i,j)`,
`i ≠ j`, and the face values `(b₁,b₂)`, the direction space `pairDir i j = {z | z i = 0 ∧ z j = 0}`
has dimension `< 8` (it is a proper submodule of the coordinate hyperplane `{z i = 0}`, of dimension
`8`), and the parametrisation `l ↦ faceBase i j b₁ b₂ + l` covers the face pair, its parameter set
being the `l` with `faceBase i j b₁ b₂ + l` in the box. -/
theorem exists_forall_notMem_twoFace (m : ℕ) (K : Set (Amb 8)) (hK : IsCompact K)
    (Φ : EuclideanSpace ℝ (Fin m) × Amb 8 → Tgt 8)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (y : Amb 8), ‖p‖ < ε →
      y ∈ K → Φ (p, y) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', y)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      ∀ y ∈ K,
        (∃ i j : Fin 9, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) →
        Φ (p, y) ≠ 0 := by
  classical
  have hkerdim : ∀ i : Fin 9, Module.finrank ℝ ((coordFun i).ker) = 8 := by
    intro i
    have hsurji : Function.Surjective (coordFun i) := by
      intro r
      exact ⟨WithLp.toLp 2 (Pi.single i r), by simp [coordFun_apply]⟩
    have h := LinearMap.finrank_range_add_finrank_ker (coordFun i : Amb 8 →ₗ[ℝ] ℝ)
    rw [LinearMap.range_eq_top.mpr hsurji, finrank_top, Module.finrank_self,
      finrank_euclideanSpace_fin] at h
    omega
  have hpairDim : ∀ i j : Fin 9, i ≠ j → Module.finrank ℝ (pairDir i j) < 8 := by
    intro i j hij
    have hle : pairDir i j ≤ (coordFun i).ker := inf_le_left
    have hzk : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) i = 0 := by
      rw [WithLp.ofLp_toLp, Pi.single_eq_of_ne hij]
    have hzj : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) j = 1 := by
      rw [WithLp.ofLp_toLp, Pi.single_eq_same]
    have hzker : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) ∈ (coordFun i).ker := by
      rw [LinearMap.mem_ker]
      change coordFun i (WithLp.toLp 2 (Pi.single j 1) : Amb 8) = 0
      rw [coordFun_apply]; exact hzk
    have hznot : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) ∉ pairDir i j := by
      rw [mem_pairDir]
      exact fun h => by rw [hzj] at h; exact one_ne_zero h.2
    have hne : pairDir i j ≠ (coordFun i).ker := fun hcon => hznot (by rw [hcon]; exact hzker)
    have h1 : Module.finrank ℝ (pairDir i j) ≤ Module.finrank ℝ ((coordFun i).ker) :=
      Submodule.finrank_mono hle
    have h2 : Module.finrank ℝ (pairDir i j) ≠ Module.finrank ℝ ((coordFun i).ker) := by
      intro hcon
      exact hne (Submodule.eq_of_le_of_finrank_eq hle hcon)
    rw [hkerdim i] at h1 h2
    omega
  set L : FaceIdx → Submodule ℝ (Amb 8) :=
    fun t => if t.1.1 = t.1.2 then ⊥ else pairDir t.1.1 t.1.2 with hL
  set aa : FaceIdx → Amb 8 := fun t => faceBase t.1.1 t.1.2 t.2.1 t.2.2 with haa
  have hLdim : ∀ t : FaceIdx, Module.finrank ℝ (L t) < 8 := by
    intro t
    by_cases hij : t.1.1 = t.1.2
    · have hbot : L t = ⊥ := by rw [hL]; simp [hij]
      rw [hbot]; simp
    · have hpair : L t = pairDir t.1.1 t.1.2 := by rw [hL]; simp [hij]
      rw [hpair]
      exact hpairDim t.1.1 t.1.2 hij
  set KK : ∀ t : FaceIdx, Set (L t) :=
    fun t => {l | aa t + (l : Amb 8) ∈ K} with hKK
  have hKK_closed : ∀ t : FaceIdx, IsClosed (KK t) := by
    intro t
    have hcont : Continuous (fun l : ↥(L t) => aa t + (l : Amb 8)) :=
      continuous_const.add (Submodule.subtypeL (L t)).continuous
    rw [hKK]
    exact hK.isClosed.preimage hcont
  have hKK_bdd : ∀ t : FaceIdx, Bornology.IsBounded (KK t) := by
    intro t
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C + ‖aa t‖, fun l hl => ?_⟩
    have hl' : aa t + (l : Amb 8) ∈ K := hl
    calc ‖l‖ = ‖(l : Amb 8)‖ := rfl
      _ = ‖(aa t + (l : Amb 8)) - aa t‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖aa t + (l : Amb 8)‖ + ‖aa t‖ := norm_sub_le _ _
      _ ≤ C + ‖aa t‖ := by linarith [hC _ hl']
  have hKK_compact : ∀ t : FaceIdx, IsCompact (KK t) := fun t =>
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKK_closed t, hKK_bdd t⟩
  have hcover : ∀ y ∈ K,
      (∃ i j : Fin 9, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) →
      ∃ t : FaceIdx, y ∈ (fun l : ↥(L t) => aa t + (l : Amb 8)) '' (KK t) := by
    intro y hy h2
    obtain ⟨i, j, hij, hi, hj⟩ := h2
    have hci : faceVal (decide (y i = 1)) = y i := faceVal_decide (y i) hi
    have hcj : faceVal (decide (y j = 1)) = y j := faceVal_decide (y j) hj
    set t : FaceIdx := ((i, j), (decide (y i = 1), decide (y j = 1))) with ht
    have haat : aa t = faceBase i j (decide (y i = 1)) (decide (y j = 1)) := by rw [haa, ht]
    have hLt : L t = pairDir i j := by rw [hL, ht]; simp [hij]
    have hmem : y - aa t ∈ L t := by
      rw [hLt, mem_pairDir]
      constructor
      · rw [PiLp.sub_apply, haat, faceBase_apply_fst, hci, sub_self]
      · rw [PiLp.sub_apply, haat, faceBase_apply_snd hij.symm, hcj, sub_self]
    refine ⟨t, ⟨y - aa t, hmem⟩, ?_, ?_⟩
    · show aa t + ((⟨y - aa t, hmem⟩ : ↥(L t)) : Amb 8) ∈ K
      rw [add_sub_cancel]
      exact hy
    · show aa t + ((⟨y - aa t, hmem⟩ : ↥(L t)) : Amb 8) = y
      rw [add_sub_cancel]
  have hsurj' : ∀ (p' : EuclideanSpace ℝ (Fin m)) (y : Amb 8), ‖p'‖ < ε →
      (∃ t : FaceIdx, y ∈ (fun l : ↥(L t) => aa t + (l : Amb 8)) '' (KK t)) →
      Φ (p', y) = 0 →
      Function.Surjective (fderiv ℝ (fun p'' : EuclideanSpace ℝ (Fin m) => Φ (p'', y)) p') := by
    intro p' y hp' hy0 hzero
    obtain ⟨t, l, hlK, hl⟩ := hy0
    exact hsurj p' y hp'
      (by rw [← show aa t + (l : Amb 8) = y from hl]; exact hlK) hzero
  obtain ⟨p, hpnorm, hp⟩ := exists_forall_notMem_family m 8 FaceIdx (fun t => ↥(L t))
    (fun t => hLdim t) (fun t => fun l : ↥(L t) => aa t + (l : Amb 8))
    (fun t => contDiff_const.add (Submodule.subtypeL (L t)).contDiff)
    (fun t => KK t) hKK_compact Φ hΦ ε hε hsurj'
  refine ⟨p, hpnorm, ?_⟩
  intro y hy h2
  obtain ⟨t, ⟨l, hlK, hl⟩⟩ := hcover y hy h2
  have h := hp t l hlK
  rw [show aa t + (l : Amb 8) = y from hl] at h
  exact h


/-- The box form of `exists_forall_notMem_twoFace`: the compact set is the whole nine-box. -/
theorem exists_forall_notMem_twoFace_box (m : ℕ)
    (Φ : EuclideanSpace ℝ (Fin m) × Amb 8 → Tgt 8)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (ε : ℝ) (hε : 0 < ε)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (y : Amb 8), ‖p‖ < ε →
      y ∈ Submission.Drive.unitBox 8 → Φ (p, y) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', y)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      ∀ y ∈ Submission.Drive.unitBox 8,
        (∃ i j : Fin 9, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) →
        Φ (p, y) ≠ 0 :=
  exists_forall_notMem_twoFace m (Submission.Drive.unitBox 8) (isCompact_unitBox 8) Φ hΦ ε hε hsurj

end

end AvoidLowDim
end Work.Drive
