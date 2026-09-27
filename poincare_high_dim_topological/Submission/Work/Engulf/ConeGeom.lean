import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.PL.Generic.domDim_join_step

/-!
# Geometric helpers for the cone complex `Γ' = Γ ∪ a ∗ σ`

The two "glue nicely" computations for the cone complex: a cone `insert a u` glued against an old
face `s`, and two cones `insert a u`, `insert a v` glued against each other.  Also the affine
independence of `insert a u` when `a` is outside the affine span of `u`.
-/

namespace Work.Engulf.Aux

open Set Metric

theorem insert_eq_union_singleton {N : ℕ} (u : Finset (PL.E N)) (a : PL.E N) :
    insert a u = u ∪ {a} := by
  rw [Finset.insert_eq, Finset.union_comm]

theorem simp_insert_eq_simp_union_singleton {N : ℕ} (u : Finset (PL.E N)) (a : PL.E N) :
    PL.simp (insert a u) = PL.simp (u ∪ {a}) := by
  rw [insert_eq_union_singleton]

/-- **H1** (cone vs old face). -/
theorem simp_insert_inter_simp_of_notMem {N : ℕ} {u s : Finset (PL.E N)} {a : PL.E N}
    (hglue : PL.simp u ∩ PL.simp s ⊆ PL.simp (u ∩ s))
    (ha : a ∉ affineSpan ℝ ((u ∪ s : Finset (PL.E N)) : Set (PL.E N))) :
    PL.simp (insert a u) ∩ PL.simp s ⊆ PL.simp (u ∩ s) := by
  intro x hx
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  by_cases hxu : x ∈ PL.simp u
  · exact hglue ⟨hxu, hx2⟩
  · exfalso
    have hx1' : x ∈ PL.simp (u ∪ {a}) := by
      rw [← simp_insert_eq_simp_union_singleton]; exact hx1
    have hmem := Work.PL.Generic.mem_affineSpan_union_of_mem_simp_insert
      (s := u) (σ := s) (y := a) (x := x) hx1' hxu hx2
    exact ha (by simpa [Finset.coe_union] using hmem)

/-- **H2** (cone vs cone). -/
theorem simp_insert_inter_simp_insert {N : ℕ} {u v : Finset (PL.E N)} {a : PL.E N}
    (hglue : PL.simp u ∩ PL.simp v ⊆ PL.simp (u ∩ v))
    (ha : a ∉ affineSpan ℝ ((u ∪ v : Finset (PL.E N)) : Set (PL.E N))) :
    PL.simp (insert a u) ∩ PL.simp (insert a v) ⊆ PL.simp (insert a (u ∩ v)) := by
  intro x hx
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hxu, hxv⟩ := hx
  have hmono : PL.simp (u ∩ v) ⊆ PL.simp (insert a (u ∩ v)) :=
    PL.simp_mono (Finset.subset_insert a (u ∩ v))
  rcases eq_or_ne u ∅ with rfl | hu0
  · rw [Finset.empty_inter]
    exact hxu
  rcases eq_or_ne v ∅ with rfl | hv0
  · rw [Finset.inter_empty]
    exact hxv
  have hun : u.Nonempty := Finset.nonempty_iff_ne_empty.2 hu0
  have hvn : v.Nonempty := Finset.nonempty_iff_ne_empty.2 hv0
  have hxu' : x ∈ PL.simp (u ∪ {a}) := by
    rw [← simp_insert_eq_simp_union_singleton]; exact hxu
  have hxv' : x ∈ PL.simp (v ∪ {a}) := by
    rw [← simp_insert_eq_simp_union_singleton]; exact hxv
  by_cases hxu'' : x ∈ PL.simp u
  · have hglue' : PL.simp v ∩ PL.simp u ⊆ PL.simp (v ∩ u) := by
      rw [Set.inter_comm (PL.simp v) (PL.simp u),
        show v ∩ u = u ∩ v from Finset.inter_comm v u]
      exact hglue
    have ha' : a ∉ affineSpan ℝ ((v ∪ u : Finset (PL.E N)) : Set (PL.E N)) := by
      rw [Finset.union_comm v u]; exact ha
    have hmem : x ∈ PL.simp (v ∩ u) :=
      simp_insert_inter_simp_of_notMem (u := v) (s := u) hglue' ha' ⟨hxv, hxu''⟩
    rw [show v ∩ u = u ∩ v from Finset.inter_comm v u] at hmem
    exact hmono hmem
  by_cases hxv'' : x ∈ PL.simp v
  · exact hmono (simp_insert_inter_simp_of_notMem (u := u) (s := v) hglue ha ⟨hxu, hxv''⟩)
  · obtain ⟨μ, hμ, p, hp, hxp⟩ :=
      Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert (s := u) (y := a) hun hxu' hxu''
    obtain ⟨ν, hν, q, hq, hxq⟩ :=
      Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert (s := v) (y := a) hvn hxv' hxv''
    rcases eq_or_ne μ ν with hμν | hμν
    · have hpq : (1 - ν) • p = (1 - ν) • q := by
        have h0 : (1 - μ) • p + μ • a = (1 - ν) • q + ν • a := by rw [← hxp, ← hxq]
        rw [hμν] at h0
        exact add_right_cancel h0
      rcases eq_or_ne ν 1 with hν1 | hν1
      · have hxa : x = a := by rw [hxq, hν1]; simp
        rw [hxa]
        exact subset_convexHull ℝ ((insert a (u ∩ v) : Finset (PL.E N)) : Set (PL.E N)) (by simp)
      · have h1ν : (1 - ν) ≠ 0 := fun h => hν1 (by linarith)
        have hpq' : p = q := by
          have hc := congrArg (fun z => (1 - ν)⁻¹ • z) hpq
          rw [smul_smul, smul_smul, inv_mul_cancel₀ h1ν, one_smul, one_smul] at hc
          exact hc
        have hpuv : p ∈ PL.simp (u ∩ v) := hglue ⟨hp, by rw [hpq']; exact hq⟩
        have hp' : p ∈ PL.simp (insert a (u ∩ v)) := hmono hpuv
        have ha' : a ∈ PL.simp (insert a (u ∩ v)) :=
          subset_convexHull ℝ ((insert a (u ∩ v) : Finset (PL.E N)) : Set (PL.E N)) (by simp)
        have hν0 : 0 ≤ ν := le_of_lt hν.1
        have h1ν' : 0 ≤ 1 - ν := by linarith [hν.2]
        have hsum : ν + (1 - ν) = 1 := by ring
        have hmem : ν • a + (1 - ν) • p ∈ PL.simp (insert a (u ∩ v)) :=
          (convex_convexHull ℝ ((insert a (u ∩ v) : Finset (PL.E N)) : Set (PL.E N)))
            ha' hp' hν0 h1ν' hsum
        have hxp' : x = (1 - ν) • p + ν • a := by rw [hxp, hμν]
        rw [hxp', add_comm]
        exact hmem
    · exfalso
      have h0 : (1 - μ) • p + μ • a = (1 - ν) • q + ν • a := by rw [← hxp, ← hxq]
      have hrel : (μ - ν) • a = (1 - ν) • q - (1 - μ) • p := by
        have h1 : μ • a - ν • a = (1 - ν) • q - (1 - μ) • p := by
          calc μ • a - ν • a
              = ((1 - μ) • p + μ • a) - ((1 - μ) • p + ν • a) := by abel
            _ = ((1 - ν) • q + ν • a) - ((1 - μ) • p + ν • a) := by rw [h0]
            _ = (1 - ν) • q - (1 - μ) • p := by abel
        rw [sub_smul]; exact h1
      have hca : μ - ν ≠ 0 := sub_ne_zero.mpr hμν
      have hkey : (μ - ν) • (p +ᵥ (((1 - ν) / (μ - ν)) • (q -ᵥ p)))
          = (1 - ν) • q - (1 - μ) • p := by
        rw [vsub_eq_sub, vadd_eq_add]
        simp only [smul_add, smul_sub, smul_smul]
        match_scalars <;> field_simp <;> ring
      have hfin : a = p +ᵥ (((1 - ν) / (μ - ν)) • (q -ᵥ p)) :=
        (smul_right_inj (r := μ - ν) hca).mp (by rw [hkey, hrel])
      have hpQ : p ∈ affineSpan ℝ ((u : Set (PL.E N)) ∪ (v : Set (PL.E N))) :=
        (affineSpan_mono ℝ (Set.subset_union_left)) (PL.simp_subset_affineSpan u hp)
      have hqQ : q ∈ affineSpan ℝ ((u : Set (PL.E N)) ∪ (v : Set (PL.E N))) :=
        (affineSpan_mono ℝ (Set.subset_union_right)) (PL.simp_subset_affineSpan v hq)
      have hmem := Work.PL.Generic.affineSubspace_add_smul_vsub_mem
        (affineSpan ℝ ((u : Set (PL.E N)) ∪ (v : Set (PL.E N)))) hpQ hqQ ((1 - ν) / (μ - ν))
      rw [← hfin] at hmem
      exact ha (by simpa [Finset.coe_union] using hmem)

/-- Affine independence of `insert a u` when `a` is outside the affine span of `u`. -/
theorem cone_affineIndependent {N : ℕ} {u : Finset (PL.E N)} {a : PL.E N}
    (hu : AffineIndependent ℝ (fun v : u => (v : PL.E N)))
    (ha : a ∉ affineSpan ℝ (u : Set (PL.E N))) :
    AffineIndependent ℝ (fun v : (insert a u : Finset (PL.E N)) => (v : PL.E N)) := by
  have hau : a ∉ u := by
    intro h
    exact ha (subset_affineSpan ℝ (u : Set (PL.E N)) (by simpa using h))
  let i : (insert a u : Finset (PL.E N)) := ⟨a, Finset.mem_insert_self a u⟩
  let e : u ≃ { y : (insert a u : Finset (PL.E N)) // y ≠ i } :=
    { toFun := fun t => ⟨⟨t.1, Finset.mem_insert_of_mem t.2⟩,
        fun h => hau (by
          have h' : (t : PL.E N) = a := by simpa [i] using Subtype.ext_iff.mp h
          exact h' ▸ t.2)⟩
      invFun := fun y => ⟨y.1.1, by
        rcases Finset.mem_insert.mp y.1.2 with h | h
        · exact absurd (Subtype.ext h) y.2
        · exact h⟩
      left_inv := fun t => by ext; rfl
      right_inv := fun y => by ext; rfl }
  have h1 : AffineIndependent ℝ
      (fun x : { y : (insert a u : Finset (PL.E N)) // y ≠ i } => (x : PL.E N)) :=
    (affineIndependent_equiv e
      (p := fun x : { y : (insert a u : Finset (PL.E N)) // y ≠ i } => (x : PL.E N))).mp hu
  have hset : (fun v : (insert a u : Finset (PL.E N)) => (v : PL.E N)) '' {x | x ≠ i}
      = (u : Set (PL.E N)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Finset.mem_insert.mp x.2 with h | h
      · exact absurd (Subtype.ext h) hx
      · exact h
    · intro hy
      exact ⟨⟨y, Finset.mem_insert_of_mem hy⟩, fun h => hau (by
        have h' : y = a := by simpa [i] using Subtype.ext_iff.mp h
        exact h' ▸ hy), rfl⟩
  refine AffineIndependent.affineIndependent_of_notMem_span (k := ℝ) (i := i) h1 ?_
  rw [hset]
  simpa using ha

end Work.Engulf.Aux
