import Mathlib
import Submission.Work.CoreTopology.All

namespace Work.BoxShrink.Bubble.Plane

open LeanEval.KnotTheory.PardonDistortion

/-- A subset of a discrete set (for the subspace topology) is discrete. -/
lemma isDiscrete_of_subset {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsDiscrete t) (hst : s ⊆ t) : IsDiscrete s := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen] at ht ⊢
  intro y hy
  obtain ⟨u, hu, huy⟩ := ht y (hst hy)
  refine ⟨u, hu, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · calc u ∩ s ⊆ u ∩ t := Set.inter_subset_inter_right _ hst
      _ = {y} := huy
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨?_, ?_⟩
    · rw [hx]; exact (huy.symm ▸ Set.mem_singleton y : y ∈ u ∩ t).1
    · rw [hx]; exact hy

/-- An integer multiple of `2π` of absolute value `< π` is `0`. -/
lemma int_mul_two_pi_eq_zero {k : ℤ} (h : |(k : ℝ) * (2 * Real.pi)| < Real.pi) : k = 0 := by
  by_contra hk
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  have h2 : Real.pi < |(k : ℝ) * (2 * Real.pi)| := by
    rw [abs_mul]
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have h3 : |((2 : ℝ) * Real.pi)| = 2 * Real.pi := abs_of_pos hp
    rw [h3]
    calc Real.pi < 1 * (2 * Real.pi) := by linarith
      _ ≤ |(k : ℝ)| * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

/-- Each fibre of the parametrisation `q ↦ P.psi q.1 q.2` is discrete: it is a coset
of the lattice `(2πℤ)²`. -/
lemma fiber_isDiscrete (P : Work.CoreTopology.ParamTorus) (z : R3) :
    IsDiscrete {q : ℝ × ℝ | P.psi q.1 q.2 = z} := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro q hq
  refine ⟨Set.Ioo (q.1 - Real.pi) (q.1 + Real.pi) ×ˢ
      Set.Ioo (q.2 - Real.pi) (q.2 + Real.pi), isOpen_Ioo.prod isOpen_Ioo, ?_⟩
  ext q'
  rw [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hbox, hq'⟩
    rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo] at hbox
    obtain ⟨⟨h1l, h1r⟩, ⟨h2l, h2r⟩⟩ := hbox
    have heq : P.psi q'.1 q'.2 = P.psi q.1 q.2 := hq'.trans hq.symm
    obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := (P.psi_eq_iff q'.1 q'.2 q.1 q.2).mp heq
    have hk0 : k = 0 := by
      apply int_mul_two_pi_eq_zero
      have hthis : q'.1 - q.1 = (k : ℝ) * (2 * Real.pi) := by rw [hk]; ring
      rw [← hthis, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have hm0 : m = 0 := by
      apply int_mul_two_pi_eq_zero
      have hthis : q'.2 - q.2 = (m : ℝ) * (2 * Real.pi) := by rw [hm]; ring
      rw [← hthis, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have hq1 : q'.1 = q.1 := by rw [hk, hk0]; ring
    have hq2 : q'.2 = q.2 := by rw [hm, hm0]; ring
    exact Prod.ext hq1 hq2
  · intro h
    subst h
    refine ⟨?_, hq⟩
    rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
    exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩

/-- The preimage of a finite set under the parametrisation of a `ParamTorus`, restricted to a
compact set, is finite.  Indeed the parametrisation is injective modulo the lattice `(2πℤ)²`,
so each fibre is discrete; a compact discrete set is finite and a finite union of finite sets
is finite. -/
theorem finite_preimage {P : Work.CoreTopology.ParamTorus}
    {Z : Set LeanEval.KnotTheory.PardonDistortion.R3} (hZ : Z.Finite) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) :
    (K ∩ {q : ℝ × ℝ | P.psi q.1 q.2 ∈ Z}).Finite := by
  have hcont : Continuous (fun q : ℝ × ℝ => P.psi q.1 q.2) := P.cont
  refine (hZ.biUnion (t := fun z => K ∩ (fun q : ℝ × ℝ => P.psi q.1 q.2) ⁻¹' {z})
    (fun z _ => ?_)).subset ?_
  · have hclosed : IsClosed ((fun q : ℝ × ℝ => P.psi q.1 q.2) ⁻¹' ({z} : Set R3)) :=
      isClosed_singleton.preimage hcont
    exact (hK.inter_right hclosed).finite
      (isDiscrete_of_subset (fiber_isDiscrete P z) Set.inter_subset_right)
  · intro q hq
    rw [Set.mem_iUnion]
    exact ⟨P.psi q.1 q.2, by rw [Set.mem_iUnion]; exact ⟨hq.2, hq.1, rfl⟩⟩

end Work.BoxShrink.Bubble.Plane
