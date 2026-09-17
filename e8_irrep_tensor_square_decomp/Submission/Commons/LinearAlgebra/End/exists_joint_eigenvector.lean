import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace Commons.LinearAlgebra.End

/-- Over an algebraically closed field, an endomorphism `f` of a finite-dimensional space
has an eigenvector inside any nonzero `f`-stable submodule `E`. -/
theorem exists_eigenvector_mem_submodule {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V)
    (E : Submodule K V) (hE : E ≠ ⊥) (hstable : ∀ x ∈ E, f x ∈ E) :
    ∃ x ∈ E, x ≠ 0 ∧ ∃ μ : K, f x = μ • x := by
  have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hstable)
  obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
  refine ⟨(y : V), y.2, fun h => hy.2 (Subtype.ext h), μ, ?_⟩
  have h1 : ((f.restrict hstable) y : V) = f (y : V) := rfl
  have h2 : ((μ • y : E) : V) = μ • (y : V) := rfl
  rw [hy.apply_eq_smul, h2] at h1
  exact h1.symm

/-- Refinement step for commuting families: if `W` is a nonzero submodule stable under a commuting
family `T` indexed by a finite set `s`, then a common eigenvector of the whole family indexed by
`insert a s` exists in `W`. -/
theorem exists_joint_eigenvector_finset {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ι : Type*} [DecidableEq ι]
    (T : ι → Module.End K V) (hcomm : ∀ i j, T i * T j = T j * T i) :
    ∀ (s : Finset ι) (W : Submodule K V), W ≠ ⊥ →
      (∀ i ∈ s, ∀ x ∈ W, T i x ∈ W) →
      ∃ (w : V) (lam : ι → K), w ∈ W ∧ w ≠ 0 ∧ ∀ i ∈ s, T i w = lam i • w := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro W hW _
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨w, fun _ => 0, hwW, hw0, by
        intro i hi
        exact absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
      intro W hW hstab
      obtain ⟨w₀, lam₀, hw₀W, hw₀0, hw₀eq⟩ :=
        ih W hW (fun i hi x hx => hstab i (Finset.mem_insert_of_mem hi) x hx)
      -- the common eigenspace of the `s`-indexed sub-family, inside `W`
      let E : Submodule K V :=
        { carrier := {x : V | x ∈ W ∧ ∀ i ∈ s, T i x = lam₀ i • x}
          zero_mem' := ⟨W.zero_mem, by intro i _; simp⟩
          add_mem' := fun {a b} ha hb =>
            ⟨W.add_mem ha.1 hb.1, fun i hi => by
              rw [map_add, ha.2 i hi, hb.2 i hi, smul_add]⟩
          smul_mem' := fun c {x} hx =>
            ⟨W.smul_mem c hx.1, fun i hi => by
              rw [map_smul, hx.2 i hi, smul_smul, smul_smul, mul_comm]⟩ }
      have hw₀E : w₀ ∈ E := ⟨hw₀W, hw₀eq⟩
      have hEne : E ≠ ⊥ := (Submodule.ne_bot_iff E).mpr ⟨w₀, hw₀E, hw₀0⟩
      have hstable_a : ∀ x ∈ E, T a x ∈ E := by
        intro x hx
        refine ⟨hstab a (Finset.mem_insert_self a s) x hx.1, ?_⟩
        intro i hi
        rw [← Module.End.mul_apply, hcomm i a, Module.End.mul_apply, hx.2 i hi, map_smul]
      obtain ⟨x, hxE, hx0, μ, hμ⟩ := exists_eigenvector_mem_submodule (T a) E hEne hstable_a
      refine ⟨x, Function.update lam₀ a μ, hxE.1, hx0, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · rw [Function.update_self]
        exact hμ
      · rw [Function.update_of_ne (by rintro rfl; exact ha his), hxE.2 i his]

/-- A commuting family of endomorphisms of a finite-dimensional vector space over an algebraically
closed field, restricted to a nonzero stable submodule, has a common eigenvector in that submodule. -/
theorem exists_joint_eigenvector {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Module.End K V) (hcomm : ∀ i j, T i * T j = T j * T i)
    (W : Submodule K V) (hW : W ≠ ⊥) (hmap : ∀ i, ∀ x ∈ W, T i x ∈ W) :
    ∃ (w : V) (lam : ι → K), w ∈ W ∧ w ≠ 0 ∧ ∀ i, T i w = lam i • w := by
  obtain ⟨w, lam, hw, hw0, hl⟩ :=
    exists_joint_eigenvector_finset T hcomm Finset.univ W hW
      (fun i _ x hx => hmap i x hx)
  exact ⟨w, lam, hw, hw0, fun i => hl i (Finset.mem_univ i)⟩

end Commons.LinearAlgebra.End