import Mathlib
import Submission.Work.CFTLib.Basic

/-!
# `conjSup p K' L'' ≤ K'` is incompatible with `[L'' : K'] = p`

Let `F` be a number field, `K'/F` a finite extension inside `A = AlgebraicClosure F`, and
`L''/K'` a finite extension of degree a prime `p`.  Write

`conjSup p K' L'' = ⨆ σ : Gal(K'/F), σ.liftNormal A (L'')`

for the compositum inside `A` of the conjugates of `L''` by the lifts to `A` of the
`F`-automorphisms of `K'`.

**If every such conjugate is contained in `K'`, then `[L'' : K'] = 1`** — hence `p = 1`,
a contradiction.  The point is that the conjugate of `L''` by the lift `e` of the *identity* of
`K'` is a field `C = e(L'')` with `K' ⊆ C` (because `e` fixes `K'` pointwise and `K' ⊆ L''`), while
`C ≤ conjSup p K' L'' ≤ K'` by hypothesis; so `C = K'`.  Since `e` fixes `K'` pointwise it is a
`K'`-algebra isomorphism `L'' ≅ C = K'`, whence `[L'' : K'] = 1`; and the element `x ∈ L''` is
recovered as `x = e.symm (e x)` with `e x ∈ K'` and `e.symm` fixing `K'` pointwise.  Thus
`L'' ⊆ K'` as subsets of `A`, so `L'' = ⊥` as an intermediate field of `A/↥K'` and
`Module.finrank ↥K' L'' = 1`.
-/

namespace Work.CFTLib.ConjSup

open IntermediateField

/-- The lift to `A` of the identity automorphism of `K'` fixes `K'` pointwise: `e.symm` likewise
sends `K'` into itself.  Hence the conjugate `e(L'')` strictly contains `K'`. -/
theorem finrankContradiction (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (K' : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K'] (L'' : IntermediateField ↥K' (AlgebraicClosure F)) [FiniteDimensional ↥K' L''] (hle : Work.CFTLib.conjSup p K' L'' ≤ K') (hdeg : Module.finrank ↥K' L'' = p) : False := by
  classical
  -- the lift of the identity automorphism of `K'` to the algebraic closure, and its underlying
  -- algebra homomorphism (which is the conjugating map appearing in `conjSup` for `σ = 1`)
  let e : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F :=
    (1 : ↥K' ≃ₐ[F] ↥K').liftNormal (AlgebraicClosure F)
  let φ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F := e.toAlgHom
  -- `e` fixes `K'` pointwise
  have hφfix : ∀ k : ↥K', φ (algebraMap ↥K' (AlgebraicClosure F) k) = algebraMap ↥K' (AlgebraicClosure F) k := by
    intro k
    change e (algebraMap ↥K' (AlgebraicClosure F) k) = algebraMap ↥K' (AlgebraicClosure F) k
    rw [AlgEquiv.liftNormal_commutes]
    simp
  -- the same statement for elements of `A` lying in `K'`
  have hφfix' : ∀ k : AlgebraicClosure F, k ∈ (K' : Set (AlgebraicClosure F)) → φ k = k := by
    intro k hk
    have h : (algebraMap ↥K' (AlgebraicClosure F) (⟨k, hk⟩ : ↥K') : AlgebraicClosure F) = k := rfl
    rw [← h, hφfix]
  -- the conjugate `C = e(L'')` is one of the terms of the supremum defining `conjSup`, hence ≤ K'
  have hC_le : ((L''.restrictScalars F).map φ : IntermediateField F (AlgebraicClosure F)) ≤ K' :=
    (le_iSup (fun σ : ↥K' ≃ₐ[F] ↥K' =>
      (L''.restrictScalars F).map (σ.liftNormal (AlgebraicClosure F)).toAlgHom) 1).trans hle
  -- consequently `e` maps `L''` into `K'`
  have hφxC : ∀ x ∈ (L'' : Set (AlgebraicClosure F)), φ x ∈ (K' : Set (AlgebraicClosure F)) := by
    intro x hx
    apply hC_le
    rw [IntermediateField.mem_map]
    exact ⟨x, hx, rfl⟩
  -- and `e.symm` also fixes `K'` pointwise, since `e` does
  have hφsymmfix : ∀ k ∈ (K' : Set (AlgebraicClosure F)), e.symm k = k := by
    intro k hk
    have h1 : k = φ k := (hφfix' k hk).symm
    rw [h1]
    change e.symm (e k) = φ k
    rw [e.symm_apply_apply]
    exact h1
  -- hence `L'' ⊆ K'` as subsets of `A`
  have hsub : (L'' : Set (AlgebraicClosure F)) ⊆ (K' : Set (AlgebraicClosure F)) := by
    intro x hx
    have h1 : φ x ∈ (K' : Set (AlgebraicClosure F)) := hφxC x hx
    have h2 : e.symm (φ x) = x := by
      change e.symm (e x) = x
      exact e.symm_apply_apply x
    rw [← h2, hφsymmfix (φ x) h1]
    exact h1
  -- therefore `L'' = ⊥` as an intermediate field of `A / ↥K'`
  have hLbot : L'' = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, hsub hx⟩, rfl⟩
  -- so `L''` is one-dimensional over `K'`, contradicting `[L'' : K'] = p` with `p` prime
  have hfin1 : Module.finrank ↥K' L'' = 1 := by
    rw [IntermediateField.finrank_eq_one_iff]
    exact hLbot
  exact (Fact.out : p.Prime).ne_one (by rw [← hdeg, hfin1])

end Work.CFTLib.ConjSup
