/-
# The comparison map `kPsi` is a chain map into `kSup E`

`Insert.kPsi A n f₀ k` is the `ℤ`-linear map from the chains of the order complex of the
root face `A.root (n+1) f₀` to the `k`-chains of `K`, read in the free model `kMod K k`:
it sends a simplex `s` of the subdivision whose top vertex is the root to the basis vector of
the (unique) simplex of `K` whose carrier is `(n+1, f₀)` and whose lift is `s`, and it kills all
other simplices.

The point of this file is `insert_kPsi_chain`: for `z` supported on the order complex of the
root face, the failure of `kPsi` to be a chain map,
`kδCpt K k (kPsi A n f₀ (k+1) z) - kPsi A n f₀ k (D k z)`,
lands in the subcomplex `kSup A n E k` carried by the *old* level.  Concretely, the boundary of
a `(k+1)`-simplex `s` of the order complex of the root face yields the faces obtained by deleting
one of the first `k+1` vertices — these again have top vertex the root, and are matched bijectively
with the corresponding faces of the lift — together with the face obtained by deleting the top
vertex, whose own top vertex is *strictly below* the root, hence whose `kPsi`-image vanishes;
what remains is the last face of the lifted simplex, whose carrier has dimension `< n+1` and so
already lies in `kSup A n E k`.

The reduction from a general chain to the spanning simplices is the linearity of the expression
`z ↦ kδCpt K k (kPsi A n f₀ (k+1) z) - kPsi A n f₀ k (D k z)`.
-/
import Mathlib
import Submission.Work.MbarHomology.CellAtlas.InsertSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

namespace CellAtlas

namespace Insert

-- As in `InsertSetup.lean`: pin the module structures on free modules.
attribute [local instance 2000] Pi.Function.module Finsupp.module

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

/-- The inverse of `liftEquiv` at a simplex that is the lift of a given simplex of `K`. -/
theorem liftEquiv_symm_eq (A : CellAtlas K P C) (k n : ℕ) (e : Fin (C.dim n))
    (s : Work.Subdivision.Simplex P.Cell k) (h : s (Fin.last k) = A.root n e)
    (σ : Fin (K.card k)) (hσ : A.lift σ = s) (hc : A.car σ = ⟨n, e⟩) :
    (A.liftEquiv k n e).symm ⟨s, h⟩ = ⟨σ, hc⟩ := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext hσ.symm

/-- The top vertex of a simplex of the order complex, after deleting a non-last vertex. -/
theorem Simplex.face_castSucc_last {k : ℕ} (s : Work.Subdivision.Simplex P.Cell (k + 1))
    (j : Fin (k + 1)) :
    (s.face j.castSucc) (Fin.last k) = s (Fin.last (k + 1)) := by
  rw [Work.Subdivision.Simplex.face_apply]
  congr 1
  ext
  simp

/-- The top vertex of a simplex of the order complex, after deleting the last vertex. -/
theorem Simplex.face_last_last {k : ℕ} (s : Work.Subdivision.Simplex P.Cell (k + 1)) :
    (s.face (Fin.last (k + 1))) (Fin.last k) = s (Fin.last k).castSucc := by
  rw [Work.Subdivision.Simplex.face_apply]
  congr 1
  ext
  simp

/-- **The basis case, top vertex the root.**  If `s` is a `(k+1)`-simplex of the subdivision whose
top vertex is the root face, the chain-map defect of `kPsi` on `s` is (up to sign) the last face of
the lifted simplex, whose carrier has dimension `≤ n` and hence lies in `kSup A n E k`. -/
theorem kPsi_chain_single_top (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (s : Work.Subdivision.Simplex P.Cell (k + 1)) (hlast : s (Fin.last (k + 1)) = A.root (n + 1) f₀) :
    kδCpt K k (kPsi A n f₀ (k + 1) (Finsupp.single s 1)) -
        kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k (Finsupp.single s 1)) ∈
      kSup A n E k := by
  obtain ⟨σ, hcar, hlift⟩ : ∃ σ : Fin (K.card (k+1)), A.car σ = ⟨n+1, f₀⟩ ∧ A.lift σ = s :=
    ⟨((A.liftEquiv (k+1) (n+1) f₀).symm ⟨s, hlast⟩).1,
      ((A.liftEquiv (k+1) (n+1) f₀).symm ⟨s, hlast⟩).2,
      lift_liftEquiv_symm A (k+1) (n+1) f₀ s hlast⟩
  have h1 : kPsi A n f₀ (k + 1) (Finsupp.single s 1) = Finsupp.single σ 1 := by
    rw [kPsi_sdElem, kGen_eq_single A n f₀ (k + 1) s hlast]
    rw [liftEquiv_symm_eq A (k+1) (n+1) f₀ s hlast σ hlift hcar]
  have h3 : kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k (Finsupp.single s 1))
      = ∑ i : Fin (k+2), (-1:ℤ)^(i:ℕ) • kGen A n f₀ k (s.face i) := by
    rw [Work.Subdivision.D_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, kPsi_sdElem]
  have h4 : ∀ j : Fin (k+1),
      kGen A n f₀ k (s.face j.castSucc) = Finsupp.single (K.face σ j.castSucc) 1 := by
    intro j
    have hlastj : (s.face j.castSucc) (Fin.last k) = A.root (n+1) f₀ := by
      rw [Simplex.face_castSucc_last, hlast]
    rw [kGen_eq_single A n f₀ k (s.face j.castSucc) hlastj]
    have hface_lift : A.lift (K.face σ j.castSucc) = s.face j.castSucc := by
      rw [(A.face_ne_last σ j).2, hlift]
    have hcar_face : A.car (K.face σ j.castSucc) = ⟨n+1, f₀⟩ := by
      rw [(A.face_ne_last σ j).1, hcar]
    rw [liftEquiv_symm_eq A k (n+1) f₀ (s.face j.castSucc) hlastj (K.face σ j.castSucc)
      hface_lift hcar_face]
  have h5 : kGen A n f₀ k (s.face (Fin.last (k+1))) = 0 := by
    refine kGen_eq_zero A n f₀ k _ ?_
    rw [Simplex.face_last_last]
    intro hcontra
    have hlt : s (Fin.last k).castSucc < A.root (n+1) f₀ := by
      rw [← hlast]; exact s.strictMono (by simp)
    exact absurd hcontra (ne_of_lt hlt)
  have heq : (∑ i : Fin (k+2), (-1:ℤ)^(i:ℕ) • Finsupp.single (K.face σ i) 1)
      - (∑ i : Fin (k+2), (-1:ℤ)^(i:ℕ) • kGen A n f₀ k (s.face i))
      = (-1:ℤ)^((Fin.last (k+1) : Fin (k+2)):ℕ) •
          Finsupp.single (K.face σ (Fin.last (k+1))) 1 := by
    rw [Fin.sum_univ_castSucc (f := fun i : Fin (k+2) =>
          (-1:ℤ)^(i:ℕ) • Finsupp.single (K.face σ i) 1),
      Fin.sum_univ_castSucc (f := fun i : Fin (k+2) =>
          (-1:ℤ)^(i:ℕ) • kGen A n f₀ k (s.face i))]
    have hsum : (∑ j : Fin (k+1), (-1:ℤ)^((j.castSucc : Fin (k+2)):ℕ) •
          kGen A n f₀ k (s.face j.castSucc))
        = (∑ j : Fin (k+1), (-1:ℤ)^((j.castSucc : Fin (k+2)):ℕ) •
            Finsupp.single (K.face σ j.castSucc) 1) :=
      Finset.sum_congr rfl fun j _ => by rw [h4 j]
    have hlast0 : (-1:ℤ)^((Fin.last (k+1) : Fin (k+2)):ℕ) •
        kGen A n f₀ k (s.face (Fin.last (k+1))) = 0 := by
      rw [h5, smul_zero]
    rw [hsum, hlast0, add_zero]
    abel
  rw [h1, kδCpt_single, h3, heq]
  refine Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨K.face σ (Fin.last (k+1)), Or.inl ?_, rfl⟩
  have hcar' : (A.car σ).1 = n + 1 := by rw [hcar]
  have hfl := A.face_last σ
  rw [hcar'] at hfl
  omega

/-- **The basis case, top vertex not the root.**  If the top vertex of `s` is not the root face then
both terms of the chain-map defect vanish: `kPsi` kills `s` itself, and every face of `s` either
still has top vertex `s`'s top vertex, or has top vertex the second-to-last vertex of `s`, which is
strictly below the root. -/
theorem kPsi_chain_single_notTop (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ)
    (s : Work.Subdivision.Simplex P.Cell (k + 1)) (hs : ∀ i, s i ≤ A.root (n + 1) f₀)
    (hlast : s (Fin.last (k + 1)) ≠ A.root (n + 1) f₀) :
    kδCpt K k (kPsi A n f₀ (k + 1) (Finsupp.single s 1)) -
        kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k (Finsupp.single s 1)) ∈
      kSup A n E k := by
  have h1 : kPsi A n f₀ (k + 1) (Finsupp.single s 1) = 0 := by
    rw [kPsi_sdElem, kGen_eq_zero A n f₀ (k + 1) s hlast]
  have h3 : kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k (Finsupp.single s 1))
      = ∑ i : Fin (k+2), (-1:ℤ)^(i:ℕ) • kGen A n f₀ k (s.face i) := by
    rw [Work.Subdivision.D_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, kPsi_sdElem]
  have hzero : ∀ i : Fin (k+2), kGen A n f₀ k (s.face i) = 0 := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · refine kGen_eq_zero A n f₀ k _ ?_
      rw [Simplex.face_castSucc_last]
      exact hlast
    · refine kGen_eq_zero A n f₀ k _ ?_
      rw [Simplex.face_last_last]
      intro hcontra
      have hlt : s (Fin.last k).castSucc < A.root (n+1) f₀ :=
        lt_of_lt_of_le (s.strictMono (by simp)) (hs (Fin.last (k+1)))
      exact absurd hcontra (ne_of_lt hlt)
  rw [h1, map_zero, h3, Finset.sum_eq_zero (fun i _ => by rw [hzero i, smul_zero])]
  simp

end Insert

open Work.MbarHomology.CellAtlas.Insert

/-- **`kPsi` is a chain map modulo the old level.**  For a chain `z` of the order complex of the
root face `A.root (n+1) f₀`, the defect of `kPsi` against the differentials lies in
`kSup A n E k`. -/
theorem insert_kPsi_chain {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx} (A : Work.MbarHomology.CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) (z : Work.Subdivision.chainMod P.Cell (k + 1)) (hz : z ∈ Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) (k + 1)) : Work.MbarHomology.CellAtlas.kδCpt K k (Work.MbarHomology.CellAtlas.Insert.kPsi A n f₀ (k + 1) z) - Work.MbarHomology.CellAtlas.Insert.kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k z) ∈ Work.MbarHomology.CellAtlas.kSup A n E k := by
  have hFadd : ∀ x y : Work.Subdivision.chainMod P.Cell (k + 1),
      (kδCpt K k (kPsi A n f₀ (k + 1) (x + y)) -
          kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k (x + y)))
        = (kδCpt K k (kPsi A n f₀ (k + 1) x) -
            kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k x))
          + (kδCpt K k (kPsi A n f₀ (k + 1) y) -
              kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k y)) := by
    intro x y
    simp only [map_add]
    abel
  have hFsmul : ∀ (c : ℤ) (x : Work.Subdivision.chainMod P.Cell (k + 1)),
      (kδCpt K k (kPsi A n f₀ (k + 1) (c • x)) -
          kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k (c • x)))
        = c • (kδCpt K k (kPsi A n f₀ (k + 1) x) -
            kPsi A n f₀ k (Work.Subdivision.D (α := P.Cell) k x)) := by
    intro c x
    simp only [map_smul]
    rw [smul_sub]
  rw [Work.Subdivision.PolyCW.leSub] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      by_cases hlast : s (Fin.last (k+1)) = A.root (n+1) f₀
      · exact kPsi_chain_single_top A n E f₀ k s hlast
      · exact kPsi_chain_single_notTop A n E f₀ k s hs hlast
  | zero =>
      simp only [map_zero, sub_self]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [hFadd x y]
      exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
      rw [hFsmul c x]
      exact Submodule.smul_mem _ _ ih

end CellAtlas

end

end Work.MbarHomology
