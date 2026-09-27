import Mathlib
import Submission.Work.Isotopy.frame_matching_span

/-!
# The projection family of M1's fold

## The local brick

`Work.Whitney.CutPush.frameLinearMap_self_is_projection`: for an orthonormal family
`c : Fin k → ℝ^m`, the frame map `Work.Isotopy.frameLinearMap c c` (that is, `x ↦ Σ_j ⟪c j, x⟫ • c j`)
is idempotent, self-adjoint, and has range exactly `span (range c)`, of dimension `k`.  So it is the
orthogonal projection onto the span of the frame.

*Traps recorded:* the range equality must be proved **before** the final `refine`, because the finrank
clause has to rewrite with it (`LinearMap.range_eq_map` alone leaves `map Π ⊤`, not the span); and
`finrank_span_eq_card` returns `Fintype.card (Fin k)`, so `simpa` is needed to land on `k`.

## The collapse

`eq_of_projection_range_eq` (self-adjoint idempotents with the same range are equal) and
`sum_smul_frameLinearMap_eq_of_common_range`: a convex combination of frame maps whose *active* members
(all `i` with `ρ i ≠ 0`) have a common range is that common projection.  With
`Q t := Σ i, ρ i t • Π i t` and `hagree` making every active `Π i t` have the fibre as range, the
collapse gives `Q t = P t`, so idempotence, self-adjointness and rank read off from the single
projection `P t` instead of being proved for the sum.

*Traps recorded:* `LinearMap.mul_apply` does not exist in this revision — apply the multiplication
identity with `congrArg` and simplify with `LinearMap.comp_apply`; and `Finset.sum_smul` is oriented
`(Σ i, ρ i) • f = Σ i, ρ i • f`, so the collapse uses `(Finset.sum_smul).symm`.

## The partition of unity

`exists_smooth_partitionOfUnity_Icc_neg1_2`: for a finite open cover `J` of the interval `Icc (-1) 2`
used by M1 (the parameter range of the collar), smooth `ρ i` with `0 ≤ ρ i`, `tsupport (ρ i) ⊆ J i` and
`Σ i, ρ i t = 1` on the interval.  This is what turns the patchwise projections into the single
projection family
`Q t = Σ i, ρ i t • Π i t` consumed by `exists_smooth_frame_of_projection_family`.
-/

namespace Work.Whitney.CutPush

open scoped BigOperators Topology Manifold
open Work.Isotopy

variable {m : ℕ}

/-- **The frame map of an orthonormal frame is the orthogonal projection onto its span.** -/
theorem frameLinearMap_self_is_projection {k : ℕ} (c : Fin k → EuclideanSpace ℝ (Fin m))
    (hc : Orthonormal ℝ c) :
    (frameLinearMap c c).comp (frameLinearMap c c) = frameLinearMap c c ∧
      LinearMap.range (frameLinearMap c c) = Submodule.span ℝ (Set.range c) ∧
      Module.finrank ℝ (LinearMap.range (frameLinearMap c c)) = k ∧
      (∀ x y : EuclideanSpace ℝ (Fin m),
        inner ℝ (frameLinearMap c c x) y = inner ℝ x (frameLinearMap c c y)) := by
  have happ : ∀ x : EuclideanSpace ℝ (Fin m),
      frameLinearMap c c x = ∑ j, inner ℝ (c j) x • c j := fun x => frameLinearMap_apply c c x
  have hmem : ∀ x : EuclideanSpace ℝ (Fin m),
      frameLinearMap c c x ∈ Submodule.span ℝ (Set.range c) := by
    intro x
    rw [happ x]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hfix : ∀ x ∈ Submodule.span ℝ (Set.range c), frameLinearMap c c x = x :=
    frameLinearMap_id_on_span c hc
  have hrange : LinearMap.range (frameLinearMap c c) = Submodule.span ℝ (Set.range c) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, rfl⟩
      exact hmem x
    · rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      exact LinearMap.mem_range.mpr ⟨c j, frameLinearMap_apply_frame c c hc j⟩
  refine ⟨?_, hrange, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply]
    exact hfix _ (hmem x)
  · rw [hrange]
    simpa using finrank_span_eq_card hc.linearIndependent
  · intro x y
    rw [happ x, happ y, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, RCLike.conj_to_real, inner_smul_right, real_inner_comm (c j) x]
    ring

/-- **Orthogonal projections with the same range are equal.**  (Trap: LinearMap.mul_apply does not
exist in this revision; apply the multiplication identity with congrArg and simplify with
LinearMap.comp_apply.) -/
theorem eq_of_projection_range_eq {P Q : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)}
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPs : ∀ x y : EuclideanSpace ℝ (Fin m), inner ℝ (P x) y = inner ℝ x (P y))
    (hQs : ∀ x y : EuclideanSpace ℝ (Fin m), inner ℝ (Q x) y = inner ℝ x (Q y))
    (hr : LinearMap.range P = LinearMap.range Q) : P = Q := by
  have hPfix : ∀ z ∈ LinearMap.range P, P z = z := by
    rintro z ⟨w, rfl⟩
    have h := congrArg (fun (f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) => f w) hP
    simpa [LinearMap.comp_apply] using h
  have hQfix : ∀ z ∈ LinearMap.range Q, Q z = z := by
    rintro z ⟨w, rfl⟩
    have h := congrArg (fun (f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) => f w) hQ
    simpa [LinearMap.comp_apply] using h
  have hPQ : ∀ x, P (Q x) = Q x := fun x =>
    hPfix _ (hr ▸ LinearMap.mem_range_self Q x)
  have hQP : ∀ x, Q (P x) = P x := fun x =>
    hQfix _ (hr.symm ▸ LinearMap.mem_range_self P x)
  refine LinearMap.ext fun x => ?_
  have key : ∀ y, inner ℝ (P x) y = inner ℝ (Q x) y := by
    intro y
    calc inner ℝ (P x) y = inner ℝ (Q (P x)) y := by rw [hQP x]
      _ = inner ℝ (P x) (Q y) := hQs (P x) y
      _ = inner ℝ x (P (Q y)) := hPs x (Q y)
      _ = inner ℝ x (Q y) := by rw [hPQ y]
      _ = inner ℝ (Q x) y := (hQs x y).symm
  have hzero : inner ℝ (P x - Q x) (P x - Q x) = 0 := by
    have h := key (P x - Q x)
    rw [inner_sub_left, h, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- **The collapse.** A convex combination of frame maps whose *active* members all have the same
range is the common projection. -/
theorem sum_smul_frameLinearMap_eq_of_common_range {N k : ℕ}
    (c : Fin N → Fin k → EuclideanSpace ℝ (Fin m))
    (hc : ∀ i, Orthonormal ℝ (c i))
    (ρ : Fin N → ℝ) (hsum : ∑ i, ρ i = 1)
    (ι₀ : Fin N) (hι₀ : ρ ι₀ ≠ 0)
    (hcommon : ∀ i, ρ i ≠ 0 →
      LinearMap.range (frameLinearMap (c i) (c i)) = LinearMap.range (frameLinearMap (c ι₀) (c ι₀))) :
    ∑ i, ρ i • frameLinearMap (c i) (c i) = frameLinearMap (c ι₀) (c ι₀) := by
  have hstep : ∀ i, ρ i • frameLinearMap (c i) (c i) = ρ i • frameLinearMap (c ι₀) (c ι₀) := by
    intro i
    by_cases hi : ρ i = 0
    · rw [hi, zero_smul, zero_smul]
    · have hPi := frameLinearMap_self_is_projection (c i) (hc i)
      have hP0 := frameLinearMap_self_is_projection (c ι₀) (hc ι₀)
      have heq : frameLinearMap (c i) (c i) = frameLinearMap (c ι₀) (c ι₀) :=
        eq_of_projection_range_eq hPi.1 hP0.1 hPi.2.2.2 hP0.2.2.2 (hcommon i hi)
      rw [heq]
  calc ∑ i, ρ i • frameLinearMap (c i) (c i)
      = ∑ i, ρ i • frameLinearMap (c ι₀) (c ι₀) := Finset.sum_congr rfl fun i _ => hstep i
    _ = (∑ i, ρ i) • frameLinearMap (c ι₀) (c ι₀) := (Finset.sum_smul).symm
    _ = frameLinearMap (c ι₀) (c ι₀) := by rw [hsum, one_smul]



/-- **A smooth partition of unity subordinate to a finite open cover of `Icc (-1) 2`.** -/
theorem exists_smooth_partitionOfUnity_Icc_neg1_2 {ι : Type*} [Fintype ι]
    (J : ι → Set ℝ) (hJ : ∀ i, IsOpen (J i))
    (hcov : Set.Icc (-1 : ℝ) 2 ⊆ ⋃ i, J i) :
    ∃ ρ : ι → ℝ → ℝ, (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i)) ∧
      (∀ i t, 0 ≤ ρ i t) ∧
      (∀ i, tsupport (ρ i) ⊆ J i) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 2, ∑ i, ρ i t = 1) := by
  classical
  obtain ⟨F, hF⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ℝ)) (s := Set.Icc (-1 : ℝ) 2) isClosed_Icc J hJ hcov
  refine ⟨fun i t => F i t, fun i => contMDiff_iff_contDiff.mp (F i).contMDiff,
    fun i t => F.nonneg i t, fun i => hF i, ?_⟩
  intro t ht
  have h := F.sum_eq_one ht
  rwa [finsum_eq_sum_of_fintype] at h


/-- **The smoothness of the projection family `Q`.**  The CLM family
`Q t = Σ i, ρ i t • (Σ j, (innerSL ℝ (c i j t)).smulRight (c i j t))` has a jointly `C^∞` application
map.  This is the "smooth layer" of `P`: the summands are products of smooth functions, so it is a
`ContDiff.sum`/`.smul` computation once the CLM notation is unfolded
(`ContinuousLinearMap.smulRight_apply`, `innerSL_apply_apply`).

The frames `c i j` are assumed *globally* smooth, not merely smooth on `pat i`: that is the shape the
application has (the chart-local families are extended by a clamping reparametrisation of the
parameter, which keeps them globally defined and globally orthonormal while the span-correctness stays
local), and it is why no bump-multiplication is needed here — the weights `ρ i` already carry the
support condition `tsupport (ρ i) ⊆ pat i`. -/
theorem contDiff_projection_family {N k : ℕ}
    (c : Fin N → Fin k → ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ∀ i j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c i j))
    (ρ : Fin N → ℝ → ℝ) (hρ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        ∑ i, ρ i p.1 • ∑ j, (innerSL ℝ (c i j p.1)).smulRight (c i j p.1) p.2) := by
  have hrew : (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        ∑ i, ρ i p.1 • ∑ j, (innerSL ℝ (c i j p.1)).smulRight (c i j p.1) p.2)
      = fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
        ∑ i, ρ i p.1 • ∑ j, inner ℝ (c i j p.1) p.2 • c i j p.1 := by
    funext p
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [hrew]
  refine ContDiff.sum fun i _ => ?_
  refine ((hρ i).comp contDiff_fst).smul ?_
  refine ContDiff.sum fun j _ => ?_
  exact (ContDiff.inner ℝ ((hc i j).comp contDiff_fst) contDiff_snd).smul
    ((hc i j).comp contDiff_fst)

end Work.Whitney.CutPush
