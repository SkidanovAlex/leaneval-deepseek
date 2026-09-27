import Mathlib
import Submission.Work.Whitney.CutPush.smooth_range_projection_family
import Submission.Work.Whitney.CutPush.section_family
import Submission.Work.Whitney.CutPush.projection_family_local

/-!
# The local range projection, the collapse, and the partition of unity used by M1

This file supplies the tools with which the *global* smooth orthogonal-projection family onto the
tangent planes `T t = range (mfderiv F (δ t))` of the sheet is built out of a finite chart cover of
the parameter interval (the M1 brick of `NOTES_S58_alignment.md` §2):

* `exists_local_projection_family` — the **local** form of `exists_smooth_projection_range_family`:
  the family `Ψ` needs to be injective only on an open set `U`, and the orthogonal projection
  `Q t := Ψ t ∘ ((Ψ t)* ∘ Ψ t)⁻¹ ∘ (Ψ t)*` onto `range (Ψ t)` is produced with `ContDiffOn` on `U`.
  This is what lets a chart-local family (whose injectivity is only known inside the chart) feed the
  construction;
* `sum_smul_projection_eq_of_common_range` — the **collapse**: an average `Σ ρ i • P i` of projections
  whose *active* members (`ρ i ≠ 0`) all have the same range *is* that common projection.  Hence the
  average of a partition-of-unity-weighted family of projections is again an orthogonal projection of
  the same rank (this is why the averaged family can be fed to the ODE transport);
* `exists_smooth_partitionOfUnity_univ` — a smooth partition of unity on `ℝ` subordinate to a finite
  open cover of the whole line (the version of `exists_smooth_partitionOfUnity_Icc_neg1_2` in which
  the weights sum to one *everywhere*, which is what makes the averaged projection a projection off
  the interval as well).
-/

namespace Work.Whitney.CutPush

open scoped ContDiff Manifold
open Topology

/-- **The orthogonal projection onto the range of a family that is injective only on an open set.**

The *local* form of `exists_smooth_projection_range_family`.  For `t ∈ U` the map
`Q t := Ψ t ∘ ((Ψ t)* ∘ Ψ t)⁻¹ ∘ (Ψ t)*` is the orthogonal projection onto `range (Ψ t)`, and `t ↦ Q t`
is `C^∞` on `U`.  (Off `U` the formula is still defined but carries no information.) -/
theorem exists_local_projection_family {n : ℕ}
    (Ψ : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    {U : Set ℝ} (hU : IsOpen U) (hinj : ∀ t ∈ U, Function.Injective (Ψ t)) :
    ∃ Q : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q U ∧
      (∀ t ∈ U, LinearMap.range (Q t : EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))
        = LinearMap.range (Ψ t : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin (2 * n)))) ∧
      (∀ t ∈ U, ∀ x y : EuclideanSpace ℝ (Fin (2 * n)),
        inner ℝ (Q t x) y = inner ℝ x (Q t y)) ∧
      (∀ t ∈ U, Q t * Q t = Q t) := by
  classical
  have hadj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ContinuousLinearMap.adjoint (Ψ t)) :=
    (((ContinuousLinearMap.adjoint :
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))) ≃ₗᵢ⋆[ℝ]
          (EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n))).toLinearIsometry).toContinuousLinearMap).contDiff.comp
      hΨ
  set S : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun t => (ContinuousLinearMap.adjoint (Ψ t)).comp (Ψ t) with hSdef
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S := by
    have h := hadj.clm_comp hΨ
    simpa [hSdef, ContinuousLinearMap.comp_apply] using h
  have hS_apply : ∀ (t : ℝ) (v : EuclideanSpace ℝ (Fin n)),
      S t v = (ContinuousLinearMap.adjoint (Ψ t)) (Ψ t v) := by
    intro t v
    rw [hSdef]
    rfl
  have hinjS : ∀ t ∈ U, Function.Injective (S t) := by
    intro t ht x y hxy
    have hkey : ∀ z : EuclideanSpace ℝ (Fin n), inner ℝ (S t z) z = ‖Ψ t z‖ ^ 2 := by
      intro z
      rw [hS_apply t z, ContinuousLinearMap.adjoint_inner_left (Ψ t) z (Ψ t z),
        real_inner_self_eq_norm_sq]
    have hzero : S t (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h2 : ‖Ψ t (x - y)‖ ^ 2 = 0 := by
      rw [← hkey (x - y), hzero]
      simp
    have h4 : ‖Ψ t (x - y)‖ = 0 := by
      nlinarith [norm_nonneg (Ψ t (x - y))]
    have h3 : Ψ t (x - y) = 0 := norm_eq_zero.mp h4
    exact sub_eq_zero.mp (hinj t ht (by rw [h3, map_zero]))
  have hinv : ∀ t ∈ U, (S t).IsInvertible := by
    intro t ht
    have hbij : Function.Bijective (S t) :=
      ⟨hinjS t ht, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))
          = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))).mp (hinjS t ht)⟩
    refine ⟨(LinearEquiv.ofBijective (S t : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n)) hbij).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl
  have hSinv : ∀ t ∈ U, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => ContinuousLinearMap.inverse (S s)) t := by
    intro t ht
    exact (hinv t ht).contDiffAt_map_inverse.comp t hS.contDiffAt
  have hSinv_apply : ∀ t ∈ U, ∀ v : EuclideanSpace ℝ (Fin n), S t ((S t).inverse v) = v := by
    intro t ht v
    exact (((hinv t ht).inverse_apply_eq (x := (S t).inverse v) (y := v)).mp rfl).symm
  set Q : ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fun t => (Ψ t).comp (((S t).inverse).comp (ContinuousLinearMap.adjoint (Ψ t))) with hQdef
  have hQat : ∀ t ∈ U, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q t := by
    intro t ht
    have h1 := (hSinv t ht).clm_comp hadj.contDiffAt
    have h2 := hΨ.contDiffAt.clm_comp h1
    simpa [hQdef] using h2
  have hQon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q U :=
    hU.contDiffOn_iff.mpr fun t ht => hQat t ht
  have hQ_apply : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin (2 * n))), Q t x =
      Ψ t ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x)) := by
    intro t x
    rw [hQdef]
    rfl
  have hrange : ∀ t ∈ U, LinearMap.range (Q t : EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)))
      = LinearMap.range (Ψ t : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n))) := by
    intro t ht
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      refine ⟨(S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x), ?_⟩
      show (Ψ t) ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x)) = (Q t) x
      rw [hQ_apply t x]
    · rintro y ⟨x, rfl⟩
      refine ⟨Ψ t x, ?_⟩
      show (Q t) (Ψ t x) = (Ψ t) x
      rw [hQ_apply t (Ψ t x)]
      have h1 : (S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) (Ψ t x)) = x := by
        rw [← hS_apply t x]
        exact hinjS t ht (hSinv_apply t ht (S t x))
      rw [h1]
  have hMinner : ∀ t ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ ((S t).inverse u) v = inner ℝ u ((S t).inverse v) := by
    intro t ht u v
    have hvu : (S t).inverse v = (S t).inverse v := rfl
    have hv : v = (S t) ((S t).inverse v) := (hSinv_apply t ht v).symm
    have hu : u = (S t) ((S t).inverse u) := (hSinv_apply t ht u).symm
    have h1 : inner ℝ ((S t).inverse u) v
        = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
      calc inner ℝ ((S t).inverse u) v
          = inner ℝ ((S t).inverse u) ((S t) ((S t).inverse v)) := by conv_lhs => rw [hv]
        _ = inner ℝ ((S t).inverse u)
              ((ContinuousLinearMap.adjoint (Ψ t)) (Ψ t ((S t).inverse v))) := by
              rw [hS_apply t ((S t).inverse v)]
        _ = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
              rw [ContinuousLinearMap.adjoint_inner_right (Ψ t) ((S t).inverse u)
                (Ψ t ((S t).inverse v))]
    have h2 : inner ℝ u ((S t).inverse v)
        = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
      calc inner ℝ u ((S t).inverse v)
          = inner ℝ ((S t) ((S t).inverse u)) ((S t).inverse v) := by conv_lhs => rw [hu]
        _ = inner ℝ ((ContinuousLinearMap.adjoint (Ψ t)) (Ψ t ((S t).inverse u)))
              ((S t).inverse v) := by rw [hS_apply t ((S t).inverse u)]
        _ = inner ℝ (Ψ t ((S t).inverse u)) (Ψ t ((S t).inverse v)) := by
              rw [ContinuousLinearMap.adjoint_inner_left (Ψ t) ((S t).inverse v)
                (Ψ t ((S t).inverse u))]
    rw [h1, h2]
  have hQadj : ∀ t ∈ U, ∀ x y : EuclideanSpace ℝ (Fin (2 * n)),
      inner ℝ (Q t x) y = inner ℝ x (Q t y) := by
    intro t ht x y
    have h1 : inner ℝ (Q t x) y
        = inner ℝ ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x))
            ((ContinuousLinearMap.adjoint (Ψ t)) y) := by
      rw [hQ_apply t x, ← ContinuousLinearMap.adjoint_inner_right (Ψ t)
        ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x)) y]
    have h2 : inner ℝ x (Q t y)
        = inner ℝ ((ContinuousLinearMap.adjoint (Ψ t)) x)
            ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) y)) := by
      rw [hQ_apply t y, ← ContinuousLinearMap.adjoint_inner_left (Ψ t)
        ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) y)) x]
    rw [h1, h2]
    exact hMinner t ht _ _
  have hidem : ∀ t ∈ U, Q t * Q t = Q t := by
    intro t ht
    refine ContinuousLinearMap.ext fun x => ?_
    show Q t (Q t x) = Q t x
    rw [hQ_apply t (Q t x), hQ_apply t x,
      ← hS_apply t ((S t).inverse ((ContinuousLinearMap.adjoint (Ψ t)) x)),
      hSinv_apply t ht]
  exact ⟨Q, hQon, hrange, hQadj, hidem⟩

/-- **The collapse.**  An average `Σ i, ρ i • P i` of projections whose *active* members (`ρ i ≠ 0`)
all have the same range is that common projection.  Hence such an average is again an orthogonal
projection, with the rank of the common range.  The projection clauses are required only for the
*active* indices (which is the form the assembly consumes: the summands coming from local chart
families are projections only where the local data is correct). -/
theorem sum_smul_projection_eq_of_common_range {m : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (ρ : ι → ℝ) (hsum : ∑ i, ρ i = 1)
    (ι₀ : ι) (hι₀ : ρ ι₀ ≠ 0)
    (hP : ∀ i, ρ i ≠ 0 → P i * P i = P i)
    (hPs : ∀ i, ρ i ≠ 0 → ∀ x y : EuclideanSpace ℝ (Fin m), inner ℝ (P i x) y = inner ℝ x (P i y))
    (hcommon : ∀ i, ρ i ≠ 0 → LinearMap.range (P i) = LinearMap.range (P ι₀)) :
    ∑ i, ρ i • P i = P ι₀ := by
  have hstep : ∀ i, ρ i • P i = ρ i • P ι₀ := by
    intro i
    by_cases hi : ρ i = 0
    · rw [hi, zero_smul, zero_smul]
    · have heq : P i = P ι₀ :=
        eq_of_projection_range_eq (hP i hi) (hP ι₀ hι₀) (hPs i hi) (hPs ι₀ hι₀) (hcommon i hi)
      rw [heq]
  calc ∑ i, ρ i • P i = ∑ i, ρ i • P ι₀ := Finset.sum_congr rfl fun i _ => hstep i
    _ = (∑ i, ρ i) • P ι₀ := (Finset.sum_smul).symm
    _ = P ι₀ := by rw [hsum, one_smul]

/-- **A smooth partition of unity on `ℝ` subordinate to a finite open cover of the whole line.** -/
theorem exists_smooth_partitionOfUnity_univ {ι : Type*} [Fintype ι]
    (J : ι → Set ℝ) (hJ : ∀ i, IsOpen (J i)) (hcov : (Set.univ : Set ℝ) ⊆ ⋃ i, J i) :
    ∃ ρ : ι → ℝ → ℝ, (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i)) ∧
      (∀ i t, 0 ≤ ρ i t) ∧
      (∀ i, tsupport (ρ i) ⊆ J i) ∧
      (∀ t, ∑ i, ρ i t = 1) := by
  classical
  obtain ⟨F, hF⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ℝ)) (s := (Set.univ : Set ℝ)) isClosed_univ J hJ hcov
  refine ⟨fun i t => F i t, fun i => contMDiff_iff_contDiff.mp (F i).contMDiff,
    fun i t => F.nonneg i t, fun i => hF i, fun t => ?_⟩
  have h := F.sum_eq_one (Set.mem_univ t)
  rwa [finsum_eq_sum_of_fintype] at h

end Work.Whitney.CutPush
