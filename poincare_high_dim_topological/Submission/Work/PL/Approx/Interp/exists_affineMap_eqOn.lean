import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Interp

open scoped Affine

/-- A linearly independent family of vectors can be extended to a linear map with prescribed
values on the family (over a division ring, any linearly independent family of a vector space
extends to a basis). -/
private lemma exists_linearMap_eq_of_linearIndependent {ι : Type*} {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (u : ι → V) (hu : LinearIndependent ℝ u) (f : ι → W) :
    ∃ L : V →ₗ[ℝ] W, ∀ i, L (u i) = f i := by
  classical
  have hset : Set.range u ⊆ Set.univ := Set.subset_univ _
  set T := hu.linearIndepOn_id.extend hset with hT
  set b : Module.Basis (↥T) ℝ V := Module.Basis.extend hu.linearIndepOn_id with hb
  refine ⟨b.constr ℝ (fun x : ↥T =>
      if h : ∃ i, u i = (x : V) then f (Classical.choose h) else 0), fun i => ?_⟩
  have hmem : u i ∈ T := by
    rw [hT]; exact hu.linearIndepOn_id.subset_extend hset (Set.mem_range_self i)
  have hbx : b ⟨u i, hmem⟩ = u i := by
    rw [hb]
    exact congrFun (Module.Basis.coe_extend hu.linearIndepOn_id) ⟨u i, hmem⟩
  rw [← hbx, b.constr_basis ℝ]
  have hex : ∃ j, u j = ((⟨u i, hmem⟩ : ↥T) : V) := ⟨i, rfl⟩
  have hchoose : Classical.choose hex = i := hu.injective (Classical.choose_spec hex)
  rw [dite_eq_left hex, hchoose]

/-- The differences `v -ᵥ v₀`, `v ∈ s \ {v₀}`, of an affinely independent finite family are
linearly independent. -/
private lemma linearIndependent_vsub_erase {N : ℕ} (s : Finset (PL.E N))
    (hs : AffineIndependent ℝ ((↑) : s → PL.E N)) {v0 : PL.E N} (hv0 : v0 ∈ s) :
    LinearIndependent ℝ (fun v : ↥(s.erase v0) => (v : PL.E N) -ᵥ v0) := by
  classical
  have h1 : LinearIndependent ℝ
      (fun i : {x : ↥s // x ≠ ⟨v0, hv0⟩} => ((i.1 : ↥s) : PL.E N) -ᵥ v0) :=
    (affineIndependent_iff_linearIndependent_vsub ℝ (fun v : ↥s => (v : PL.E N)) ⟨v0, hv0⟩).1 hs
  refine h1.comp (fun v : ↥(s.erase v0) =>
      (⟨⟨(v : PL.E N), Finset.mem_of_mem_erase v.2⟩, ?_⟩ : {x : ↥s // x ≠ ⟨v0, hv0⟩})) ?inj
  · intro h
    exact Finset.ne_of_mem_erase v.2 (Subtype.ext_iff.1 h)
  · intro v w hvw
    have h : ((v : PL.E N)) = ((w : PL.E N)) := by
      have := congrArg (fun x : {x : ↥s // x ≠ ⟨v0, hv0⟩} => ((x.1 : ↥s) : PL.E N)) hvw
      simpa using this
    exact Subtype.ext h

lemma exists_affineMap_eqOn {N n : ℕ} (s : Finset (PL.E N))
    (hs : AffineIndependent ℝ ((↑) : s → PL.E N)) (g : PL.E N → PL.E n) :
    ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ v ∈ s, A v = g v := by
  classical
  rcases s.eq_empty_or_nonempty with hs0 | ⟨v0, hv0⟩
  · rw [hs0]
    refine ⟨AffineMap.const ℝ (PL.E N) (0 : PL.E n), ?_⟩
    simp
  · obtain ⟨L, hL⟩ := exists_linearMap_eq_of_linearIndependent
      (fun v : ↥(s.erase v0) => (v : PL.E N) -ᵥ v0)
      (linearIndependent_vsub_erase s hs hv0) (fun v : ↥(s.erase v0) => g v -ᵥ g v0)
    refine ⟨AffineMap.mk' (fun x => g v0 +ᵥ L (x -ᵥ v0)) L v0 ?_, ?_⟩
    · intro p'
      simp [vsub_eq_sub, vadd_eq_add, add_comm]
    · intro v hv
      rw [AffineMap.coe_mk']
      by_cases hvv : v = v0
      · subst hvv
        simp
      · have hmem : v ∈ s.erase v0 := Finset.mem_erase.2 ⟨hvv, hv⟩
        rw [hL ⟨v, hmem⟩]
        simp [vsub_eq_sub, vadd_eq_add]

end Work.PL.Approx.Interp
