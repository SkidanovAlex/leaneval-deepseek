import Mathlib
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.delta1_separating
import Submission.Work.ORVonNeumann.Rep.exists_rightRegular
import Submission.Work.Rep.mul_eq_zero_iff_exists_starProjection_mul
import Submission.Work.Rep.starProjection_mul_comm_of_invt
import Submission.Work.Rep.starProjection_ker_orthogonal_mem_groupVonNeumann

namespace Work.Rep

open Work.ORVonNeumann

theorem directly_finite_of_tau_tracial {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (htau : ∀ a b : ↥(Work.ORVonNeumann.groupVonNeumann G), inner ℂ (Work.ORVonNeumann.delta1 G) (((a * b : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.boundedEnd G) (Work.ORVonNeumann.delta1 G)) = inner ℂ (Work.ORVonNeumann.delta1 G) (((b * a : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.boundedEnd G) (Work.ORVonNeumann.delta1 G))) : ∀ a b : ↥(Work.ORVonNeumann.groupVonNeumann G), a * b = 1 → b * a = 1 := by
  intro a b hab
  let A : boundedEnd G := (a : boundedEnd G)
  let B : boundedEnd G := (b : boundedEnd G)
  have hA : A ∈ groupVonNeumann G := a.2
  have hB : B ∈ groupVonNeumann G := b.2
  have hAB : A * B = 1 := by
    have h := congrArg (fun x : ↥(groupVonNeumann G) => (x : boundedEnd G)) hab
    simpa [A, B] using h
  -- the orthogonal projection onto the kernel of `A`
  let q : boundedEnd G := A.ker.starProjection
  have hq_mem : q ∈ groupVonNeumann G :=
    starProjection_ker_orthogonal_mem_groupVonNeumann A hA
  have hq_idem : q * q = q := Submodule.isIdempotentElem_starProjection A.ker
  have hq_adj : star q = q := (isStarProjection_starProjection (U := A.ker)).isSelfAdjoint
  -- `A` kills the kernel projection, hence `A * (1 - q) = A`
  have hAq : A * q = 0 :=
    (mul_eq_zero_iff_exists_starProjection_mul A q).mpr ⟨1, by rw [mul_one]⟩
  have hA1mq : A * (1 - q) = A := by rw [mul_sub, mul_one, hAq, sub_zero]
  -- the defect `1 - B * A` factors through the kernel projection
  obtain ⟨Y, hY⟩ : ∃ Y, 1 - B * A = A.ker.starProjection * Y :=
    (mul_eq_zero_iff_exists_starProjection_mul A (1 - B * A)).mp (by
      rw [mul_sub, mul_one, ← mul_assoc, hAB, one_mul, sub_self])
  have h1mq : 1 - q = (1 - q) * B * A := by
    have h0 : (1 - q) * (1 - B * A) = 0 := by
      rw [hY, ← mul_assoc, sub_mul, one_mul, hq_idem, sub_self, zero_mul]
    have h2 : (1 - q) = (1 - q) * (B * A) :=
      sub_eq_zero.mp (by simpa [mul_sub, mul_one] using h0)
    rwa [← mul_assoc] at h2
  -- the trace computation
  have hmem1 : (1 - q) * B ∈ groupVonNeumann G :=
    mul_mem (sub_mem (one_mem _) hq_mem) hB
  have htrace : inner ℂ (delta1 G) (q (delta1 G)) = 0 := by
    have h := htau ⟨(1 - q) * B, hmem1⟩ ⟨A, hA⟩
    have hL : ((⟨(1 - q) * B, hmem1⟩ * ⟨A, hA⟩ : ↥(groupVonNeumann G)) : boundedEnd G)
        = 1 - q := by
      rw [Subalgebra.coe_mul]; exact h1mq.symm
    have hR : ((⟨A, hA⟩ * ⟨(1 - q) * B, hmem1⟩ : ↥(groupVonNeumann G)) : boundedEnd G) = 1 := by
      rw [Subalgebra.coe_mul]
      rw [← mul_assoc, hA1mq, hAB]
    rw [hL, hR] at h
    simp only [sub_apply, one_apply_eq_self, inner_sub_right] at h
    have hA' : inner ℂ (delta1 G) (delta1 G) - inner ℂ (delta1 G) (q (delta1 G))
        = inner ℂ (delta1 G) (delta1 G) := h
    have h1 : inner ℂ (delta1 G) (delta1 G) + (- inner ℂ (delta1 G) (q (delta1 G)))
        = inner ℂ (delta1 G) (delta1 G) + 0 := by
      rw [add_zero]; simpa [sub_eq_add_neg] using hA'
    exact neg_eq_zero.mp (add_left_cancel h1)
  -- hence the kernel projection vanishes
  have hq0 : q = 0 := by
    have hq1 : q (delta1 G) = 0 := by
      have h : inner ℂ (q (delta1 G)) (q (delta1 G)) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_right q (delta1 G) (q (delta1 G)),
          ← ContinuousLinearMap.star_eq_adjoint, hq_adj]
        rw [← mul_apply_eq_comp, hq_idem]
        exact htrace
      exact inner_self_eq_zero.mp h
    have hd := Work.ORVonNeumann.Rep.delta1_separating (G := G) ⟨q, hq_mem⟩ hq1
    simpa using Subtype.ext_iff.mp hd
  -- hence `A` is injective and `B * A = 1`
  have hAinj : ∀ ξ : l2 G, A ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have h1 : q ξ = ξ := Submodule.starProjection_eq_self_iff.mpr hξ
    rw [hq0] at h1
    simpa using h1.symm
  have hBA : B * A = 1 := by
    have hzero : A * (B * A - 1) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, hAB, one_mul, sub_self]
    have hsub : B * A - 1 = 0 := by
      refine ContinuousLinearMap.ext fun ξ => ?_
      have h2 : A ((B * A - 1) ξ) = 0 := by
        have := congrArg (fun T : boundedEnd G => T ξ) hzero
        simpa [mul_apply_eq_comp] using this
      simpa using hAinj ((B * A - 1) ξ) h2
    exact sub_eq_zero.mp hsub
  refine Subtype.ext ?_
  change (b : boundedEnd G) * (a : boundedEnd G) = (1 : boundedEnd G)
  exact hBA


end Work.Rep
