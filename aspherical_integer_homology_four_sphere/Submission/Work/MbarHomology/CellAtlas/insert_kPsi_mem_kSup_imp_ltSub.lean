/-
# `kPsi` is injective modulo the old level on the chains of the new face

This file proves the elementary point that makes the comparison map `kPsi` of
`Submission/Work/MbarHomology/CellAtlas/InsertSetup.lean` an isomorphism of the
piece carried by the new cell: a chain `z` of the order complex of the root face
`A.root (n+1) f₀` whose image under `kPsi` already lies in the *old* level
`kSup A n E k` (i.e. away from the new cell, `f₀ ∉ E`) must lie in the boundary
`ltSub P (A.root (n+1) f₀) k` of that face.

The proof rests on one computation: `kPsi` sends the basis simplex of a simplex
`A.lift σ` with carrier `(n+1, f₀)` to the basis vector `σ` of `kMod`, so the
coefficient of a basis vector `σ` with carrier `(n+1, f₀)` in `kPsi z` is the
coefficient of `A.lift σ` in `z` (`Insert.kPsi_coeff`).  A simplex of the support
of `z` whose top vertex is the root of the new cell therefore maps to a nonzero
basis vector whose carrier is `(n+1, f₀)`, which the old level does not contain
since `f₀ ∉ E`; so no simplex of the support of `z` has the root as its top
vertex, and `z` lies in the boundary.
-/
import Mathlib
import Submission.Work.MbarHomology.CellAtlas.InsertSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Work.MbarHomology.CellAtlas

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

namespace Insert

/-- The inverse of `liftEquiv` at the lift of a simplex, for an arbitrary proof
that the lift has the root as its top vertex. -/
theorem liftEquiv_symm_lift_any (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n))
    (σ : Fin (K.card k)) (h : A.car σ = ⟨n, e⟩)
    (h' : A.lift σ (Fin.last k) = A.root n e) :
    (A.liftEquiv k n e).symm ⟨A.lift σ, h'⟩ = ⟨σ, h⟩ := by
  have h1 : (⟨A.lift σ, h'⟩ : {s : Work.Subdivision.Simplex P.Cell k //
      s (Fin.last k) = A.root n e}) = ⟨A.lift σ, by rw [A.lift_top σ, h]⟩ :=
    Subtype.ext rfl
  rw [h1, liftEquiv_symm_lift A k n e σ h]

/-- `kPsi` carries the basis simplex of `A.lift σ` to the basis vector `σ`. -/
theorem kGen_lift (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (σ : Fin (K.card k)) (hσ : A.car σ = ⟨n + 1, f₀⟩) :
    kGen A n f₀ k (A.lift σ) = Finsupp.single σ (1 : ℤ) := by
  rw [kGen]
  split_ifs with h
  · rw [liftEquiv_symm_lift_any A k (n + 1) f₀ σ hσ h]
  · exact absurd (by rw [A.lift_top σ, hσ]) h

/-- `kPsi` carries any other basis simplex to a vector whose `σ`-coefficient
vanishes. -/
theorem kGen_apply_eq_zero (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1)))
    (k : ℕ) (s : Work.Subdivision.Simplex P.Cell k) (σ : Fin (K.card k))
    (hne : s ≠ A.lift σ) : (kGen A n f₀ k s) σ = 0 := by
  rw [kGen]
  by_cases h : s (Fin.last k) = A.root (n + 1) f₀
  · rw [dif_pos h]
    refine Finsupp.single_eq_of_ne ?_
    intro heq
    have h2 : A.lift σ = s := by rw [heq]; exact lift_liftEquiv_symm A k (n + 1) f₀ s h
    exact hne h2.symm
  · rw [dif_neg h, Finsupp.zero_apply]

/-- **The coefficients of `kPsi`**: the coefficient of a basis vector `σ` with
carrier `(n+1, f₀)` in `kPsi z` is the coefficient of `A.lift σ` in `z`. -/
theorem kPsi_coeff (A : CellAtlas K P C) (n : ℕ) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (z : Work.Subdivision.chainMod P.Cell k) (σ : Fin (K.card k))
    (hσ : A.car σ = ⟨n + 1, f₀⟩) :
    (kPsi A n f₀ k z) σ = z (A.lift σ) := by
  rw [kPsi]
  rw [linearCombination_apply_single_sum]
  rw [Finset.sum_eq_single (A.lift σ)]
  · rw [kGen_lift A n f₀ k σ hσ, Finsupp.single_eq_same, mul_one]
  · intro b _ hne
    rw [kGen_apply_eq_zero A n f₀ k b σ hne, mul_zero]
  · intro hnot
    rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]

/-- No simplex of the support of `z` has the root of the new cell as its top
vertex, as soon as `kPsi z` lies in the old level. -/
theorem kPsi_top_ne (A : CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ) (z : Work.Subdivision.chainMod P.Cell k)
    (hmem : kPsi A n f₀ k z ∈ kSup A n E k) :
    ∀ s ∈ z.support, s (Fin.last k) ≠ A.root (n + 1) f₀ := by
  intro s hs hsa
  have hbad : A.car ((A.liftEquiv k (n + 1) f₀).symm ⟨s, hsa⟩).1 = ⟨n + 1, f₀⟩ :=
    car_liftEquiv_symm A k (n + 1) f₀ s hsa
  have hcoeff : (kPsi A n f₀ k z) ((A.liftEquiv k (n + 1) f₀).symm ⟨s, hsa⟩).1 = z s := by
    rw [kPsi_coeff A n f₀ k z _ hbad, lift_liftEquiv_symm A k (n + 1) f₀ s hsa]
  have hsupp : ((A.liftEquiv k (n + 1) f₀).symm ⟨s, hsa⟩).1 ∈ (kPsi A n f₀ k z).support :=
    Finsupp.mem_support_iff.mpr (by rw [hcoeff]; exact Finsupp.mem_support_iff.mp hs)
  have hinD := (mem_kSup.mp hmem) _ hsupp
  rw [hbad] at hinD
  exact hf ((inD_succ_iff (C := C) (E := E) (n := n) f₀).mp hinD)

end Insert

theorem insert_kPsi_mem_kSup_imp_ltSub {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx} (A : Work.MbarHomology.CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (hf : f₀ ∉ E) (k : ℕ) (z : Work.Subdivision.chainMod P.Cell k) (hz : z ∈ Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) k) (hmem : Work.MbarHomology.CellAtlas.Insert.kPsi A n f₀ k z ∈ Work.MbarHomology.CellAtlas.kSup A n E k) : z ∈ Work.Subdivision.PolyCW.ltSub P (A.root (n + 1) f₀) k := by
  refine Work.Subdivision.PolyCW.mem_ltSub_of_support (P := P) fun s hs i => ?_
  have hle := Work.Subdivision.PolyCW.leSub_support (P := P) hz s hs
  have hne := Insert.kPsi_top_ne A n E f₀ hf k z hmem s hs
  have hlast : s (Fin.last k) < A.root (n + 1) f₀ := lt_of_le_of_ne (hle (Fin.last k)) hne
  exact lt_of_le_of_lt ((Work.Subdivision.Simplex.strictMono s).monotone (Fin.le_last i)) hlast

end Work.MbarHomology.CellAtlas
