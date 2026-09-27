import Mathlib
import Submission.Work.Drive.avoidLowDim
import Submission.Work.Sard.submersion_local_form
import Submission.Work.Sard.dimH_levelSet_le
import Submission.Work.Sard.weak_interior_empty_open_prod

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The bad parameters of a rich family form a set of empty interior

This file proves `Work.Drive.zeroSet_projection_interior_eq_empty`: for a smooth
`Ψ : ℝ^m × ℝ^d → ℝ^n` with `d < n` which is a submersion at every zero in `K₁ ×ˢ K₂`
(`K₁`, `K₂` compact), the set of parameters `t ∈ K₁` at which the slice `Ψ (t, ·)` has a zero in `K₂`
has empty interior.

The proof has two halves.

* **Local.**  At a zero `p₀ = (t₀, z₀)` of `Ψ` the normal form
  `Work.Sard.submersion_local_form` writes the zero set of `Ψ` near `p₀` as the image of a smooth map
  `γ : ℝ^{m + d - n} → ℝ^m × ℝ^d` (the graph over a complement of `ker (fderiv ℝ Ψ p₀)`).  The
  projection of the zero set to the first factor is therefore (locally) the image of
  `w ↦ (γ w).1` on a compact parameter set, an image of a space of dimension `m + d - n < m`: it is
  compact with empty interior (`Work.Drive.AvoidLowDim.interior_image_eq_empty_of_contDiffOn`).
* **Global.**  The set of zeros is compact, so finitely many of these local pieces cover it; the bad
  parameters are contained in a finite union of compact sets with empty interior, which therefore has
  empty interior as well (`Work.Sard.wp.interior_eq_empty_iUnion_isClosed`).
-/

set_option maxHeartbeats 1000000

namespace Work.Drive

open Set Metric Filter
open scoped ContDiff Topology NNReal

noncomputable section

/-- A surjective continuous linear map cannot increase dimension: `finrank ℝ F ≤ finrank ℝ E`. -/
lemma finrank_target_le_of_surjective_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (h : Function.Surjective L) : Module.finrank ℝ F ≤ Module.finrank ℝ E := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (L : E →ₗ[ℝ] F)
  have h2 : Module.finrank ℝ ↥(LinearMap.range (L : E →ₗ[ℝ] F)) = Module.finrank ℝ F := by
    rw [LinearMap.range_eq_top.mpr h, finrank_top]
  omega

/-- **The local form of the bad-parameter set.**

Let `Ψ : ℝ^m × ℝ^d → ℝ^n` be smooth with `d < n ≤ m + d`, and let `p₀ = (t₀, z₀)` be a zero of `Ψ` at
which `fderiv ℝ Ψ` is surjective.  Then there are a neighbourhood `W` of `p₀` and a *compact* set
`A ⊆ ℝ^m` of **empty interior** such that every zero of `Ψ` in `W` has its first coordinate in `A`.

Proof: `submersion_local_form` writes the zero set of `Ψ` near `p₀` as
`e '' ({0} × U)` for a local inverse `e` of the submersion normal form, so the set of first coordinates
of the zeros near `p₀` is contained in the image of a smooth map defined on a neighbourhood of a point
of `ℝ^(m + d - n)`.  Cut the domain down to a compact ball inside `U`; the image `A` is compact since
the map is continuous on the (open) source, and it has empty interior because its domain has dimension
`m + d - n < m`. -/
theorem zeroSet_local_avoid {m d n : ℕ} (hdn : d < n) (hmn : n ≤ m + d)
    (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (t₀ : EuclideanSpace ℝ (Fin m)) (z₀ : EuclideanSpace ℝ (Fin d))
    (h0 : Ψ (t₀, z₀) = 0)
    (hsurj : Function.Surjective (fderiv ℝ Ψ (t₀, z₀))) :
    ∃ W : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)), IsOpen W ∧ (t₀, z₀) ∈ W ∧
      ∃ A : Set (EuclideanSpace ℝ (Fin m)), IsCompact A ∧ interior A = ∅ ∧
        ∀ (t : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin d)),
          (t, z) ∈ W → Ψ (t, z) = 0 → t ∈ A := by
  classical
  -- ## the dimension bookkeeping
  have hXd : Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) = m + d := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  have hGn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + (m + d - n) := by
    rw [hXd, hGn]; omega
  -- ## the linear algebra datum of the normal form
  set K0 : Submodule ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) :=
    (fderiv ℝ Ψ (t₀, z₀) :
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).ker
    with hK0
  obtain ⟨C0, hC0⟩ := K0.exists_isCompl
  have hK0codim : Module.finrank ℝ ↥K0 + n
      = m + d := by
    have h := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℝ Ψ (t₀, z₀) :
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hGn, hXd] at h
    have hker : (fderiv ℝ Ψ (t₀, z₀) :
        EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin n)).ker = K0 := hK0.symm
    rw [hker] at h
    omega
  have hK0dim : Module.finrank ℝ ↥K0 = m + d - n := by omega
  obtain ⟨φ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (R := ℝ) (M := ↥K0) (M' := Fin (m + d - n) → ℝ) (by rw [hK0dim]; simp)
  let lam : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) →L[ℝ]
      (Fin (m + d - n) → ℝ) :=
    LinearMap.toContinuousLinearMap ((φ : ↥K0 →ₗ[ℝ] (Fin (m + d - n) → ℝ)).comp
      (K0.projectionOnto C0 hC0))
  have hlamker : lam.ker = C0 := by
    change (((φ : ↥K0 →ₗ[ℝ] (Fin (m + d - n) → ℝ)).comp (K0.projectionOnto C0 hC0)) :
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] _).ker = C0
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr φ.injective, Submodule.comap_bot,
      Submodule.ker_projectionOnto]
  have hlam : Disjoint (fderiv ℝ Ψ (t₀, z₀)).ker lam.ker := by
    rw [hlamker, ← hK0]
    exact hC0.disjoint
  -- ## the normal form
  obtain ⟨e, hx0t, he_smooth, _he_u, he_symm, _he_bij⟩ :=
    Work.Sard.submersion_local_form (m + d - n) hm Ψ hΨ (t₀, z₀) hsurj lam hlam
  -- ## the graph parametrisation of the zero set
  set γ : (Fin (m + d - n) → ℝ) → EuclideanSpace ℝ (Fin m) :=
    fun w => (e ((0 : EuclideanSpace ℝ (Fin n)), w)).1 with hγ
  set Uγ : Set (Fin (m + d - n) → ℝ) :=
    {w | ((0 : EuclideanSpace ℝ (Fin n)), w) ∈ e.source} with hUγ
  have hc₀source : ((0 : EuclideanSpace ℝ (Fin n)), lam (t₀, z₀)) ∈ e.source := by
    have h := e.map_target hx0t
    rwa [he_symm (t₀, z₀) hx0t, h0] at h
  have hUγ_open : IsOpen Uγ := by
    rw [hUγ]
    exact e.open_source.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hUγ_open.mem_nhds hc₀source)
  set Kc : Set (Fin (m + d - n) → ℝ) :=
    Metric.closedBall (lam (t₀, z₀)) (ρ / 2) with hKc
  have hKc_Uγ : Kc ⊆ Uγ := by
    intro w hw
    refine hρsub ?_
    rw [Metric.mem_ball]
    have h2 : dist w (lam (t₀, z₀)) ≤ ρ / 2 := Metric.mem_closedBall.mp hw
    linarith
  -- ## the compact piece of the bad parameters
  set A : Set (EuclideanSpace ℝ (Fin m)) := γ '' Kc with hA
  have hA_compact : IsCompact A := by
    rw [hA]
    refine IsCompact.image_of_continuousOn
      (isCompact_closedBall (lam (t₀, z₀)) (ρ / 2)) ?_
    have hcont : ContinuousOn
        (fun w : Fin (m + d - n) → ℝ => e ((0 : EuclideanSpace ℝ (Fin n)), w)) Kc :=
      he_smooth.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun w hw => hKc_Uγ hw)
    rw [hγ]
    exact hcont.fst
  have hA_int : interior A = ∅ := by
    rw [hA]
    have hγ_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ Uγ := by
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : Fin (m + d - n) → ℝ => ((0 : EuclideanSpace ℝ (Fin n)), w)) Uγ :=
        (contDiff_const.prodMk contDiff_id).contDiffOn
      have h2 := he_smooth.comp h1 (fun w hw => hw)
      rw [hγ]
      exact h2.fst
    refine Work.Drive.AvoidLowDim.interior_image_eq_empty_of_contDiffOn
      (E := Fin (m + d - n) → ℝ) (F := EuclideanSpace ℝ (Fin m)) ?_ hUγ_open hγ_smooth
      (fun w hw => hKc_Uγ hw)
    rw [Module.finrank_fin_fun, finrank_euclideanSpace_fin]
    omega
  refine ⟨e.target ∩ lam ⁻¹' Metric.ball (lam (t₀, z₀)) (ρ / 4), ?_, ?_, A, hA_compact, hA_int,
    ?_⟩
  · exact e.open_target.inter (Metric.isOpen_ball.preimage lam.continuous)
  · exact ⟨hx0t, Metric.mem_ball_self (by linarith)⟩
  · intro t z hW hzero
    obtain ⟨ht, hb⟩ := hW
    have hq : (t, z) = e ((0 : EuclideanSpace ℝ (Fin n)), lam (t, z)) := by
      have h1 : e.symm (t, z) = ((0 : EuclideanSpace ℝ (Fin n)), lam (t, z)) := by
        rw [he_symm (t, z) ht, hzero]
      exact (e.right_inv ht).symm.trans (congrArg e h1)
    have ht' : t = γ (lam (t, z)) := by
      rw [hγ]
      simpa using congrArg Prod.fst hq
    rw [ht']
    refine ⟨lam (t, z), ?_, rfl⟩
    rw [hKc, Metric.mem_closedBall]
    have h4 := Metric.mem_ball.mp hb
    linarith

/-- **The bad parameters of a rich family form a set of empty interior.**  Let
`Ψ : ℝ^m × ℝ^d → ℝ^n` be smooth with `d < n`, and let `K₁`, `K₂` be compact.  If `Ψ` is a *submersion*
at each of its zeros in `K₁ × K₂` (i.e. `fderiv ℝ Ψ` is surjective there), then the set of parameters
`t ∈ K₁` whose slice `Ψ (t, ·)` has a zero in `K₂` has empty interior.

Reason: being a submersion, `Ψ` realises its zero set near each such zero as the graph of a smooth map
over an `(m + d - n)`-dimensional space (`Work.Sard.submersion_local_form`); compactness makes finitely
many such graphs cover the zeros, so the bad set is contained in a finite union of images of
`(m + d - n)`-dimensional sets — and `m + d - n < m` because `d < n`, so each image has empty interior
(`Work.Sard.interior_image_eq_empty_of_holder_dimH` of the Sard chapter / `avoidLowDim`'s
`interior_image_eq_empty_of_contDiffOn`), and the finite union too (the pieces are closed).  This is the
engine of the chart-genericity step of the `hdense`/`hn2` route: the bad parameters are those at which
the perturbed class map of the chart fails to be an immersion on a compact piece of the disk, and the
`2 × 2` minors of the class derivative give the map `Ψ` (`d = 2` parameters of the disk and `n = 3`
minors, so `d = 2 < 3 = n`). -/
theorem zeroSet_projection_interior_eq_empty {m d n : ℕ} (hdn : d < n)
    (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin n))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (K₁ : Set (EuclideanSpace ℝ (Fin m))) (hK₁ : IsCompact K₁)
    (K₂ : Set (EuclideanSpace ℝ (Fin d))) (hK₂ : IsCompact K₂)
    (hsub : ∀ p ∈ K₁ ×ˢ K₂, Ψ p = 0 → Function.Surjective (fderiv ℝ Ψ p)) :
    interior {t ∈ K₁ | ∃ z ∈ K₂, Ψ (t, z) = 0} = ∅ := by
  classical
  by_cases hmn : n ≤ m + d
  · -- ## the main case: the zeros are covered by finitely many local pieces
    set Z : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) :=
      (K₁ ×ˢ K₂) ∩ {p | Ψ p = 0} with hZ
    have hZcomp : IsCompact Z := by
      rw [hZ]
      exact (hK₁.prod hK₂).inter_right (isClosed_eq hΨ.continuous continuous_const)
    have hloc : ∀ p : ↥Z,
        ∃ W : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)),
          IsOpen W ∧ ((p : ↥Z) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) ∈ W ∧
          ∃ A : Set (EuclideanSpace ℝ (Fin m)), IsCompact A ∧ interior A = ∅ ∧
            ∀ (t : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin d)),
              (t, z) ∈ W → Ψ (t, z) = 0 → t ∈ A := by
      intro p
      obtain ⟨hpK, hp0⟩ := p.2
      exact zeroSet_local_avoid hdn hmn Ψ hΨ (p : ↥Z).1.1 (p : ↥Z).1.2 hp0
        (hsub (p : ↥Z).1 hpK hp0)
    choose W hWopen hpW A hAcomp hAint hAprop using hloc
    obtain ⟨s, hs⟩ := hZcomp.elim_finite_subcover (fun p : ↥Z => W p) (fun p => hWopen p)
      (fun p hp => Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hpW ⟨p, hp⟩⟩)
    have hcover : {t ∈ K₁ | ∃ z ∈ K₂, Ψ (t, z) = 0} ⊆ ⋃ p : ↥s, A p := by
      rintro t ⟨htK, z, hzK, hzero⟩
      have hmemZ : (t, z) ∈ Z := ⟨⟨htK, hzK⟩, hzero⟩
      obtain ⟨p, hps, hpW'⟩ := Set.mem_iUnion₂.mp (hs hmemZ)
      exact Set.mem_iUnion.mpr ⟨⟨p, hps⟩, hAprop p t z hpW' hzero⟩
    have hempty : interior (⋃ p : ↥s, A p) = ∅ :=
      Work.Sard.wp.interior_eq_empty_iUnion_isClosed (fun p => (hAcomp p).isClosed)
        (fun p => hAint p)
    have hle : interior {t ∈ K₁ | ∃ z ∈ K₂, Ψ (t, z) = 0}
        ≤ interior (⋃ p : ↥s, A p) := interior_mono hcover
    rw [hempty] at hle
    exact le_bot_iff.mp hle
  · -- ## the degenerate case `m + d < n`: there are no zeros at all
    have hempty : {t ∈ K₁ | ∃ z ∈ K₂, Ψ (t, z) = 0} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨htK, z, hzK, hzero⟩
      have hsurj := hsub (t, z) ⟨htK, hzK⟩ hzero
      have h1 : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
          ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) :=
        finrank_target_le_of_surjective_clm (fderiv ℝ Ψ (t, z)) hsurj
      rw [finrank_euclideanSpace_fin, Module.finrank_prod, finrank_euclideanSpace_fin,
        finrank_euclideanSpace_fin] at h1
      omega
    rw [hempty, interior_empty]

end

end Work.Drive
