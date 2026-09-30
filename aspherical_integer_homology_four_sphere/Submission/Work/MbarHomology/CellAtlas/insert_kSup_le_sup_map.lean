import Mathlib
import Submission.Work.MbarHomology.CellAtlas.InsertSetup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MbarHomology.CellAtlas

open Work.Subdivision

attribute [local instance 2000] Pi.Function.module Finsupp.module

/-- Adding a single `(n+1)`-cell `f₀` to the level `E` enlarges the `K`-side
filtration only by the image under the comparison map `kPsi` of the local chains of
the order complex of the root face `root (n+1) f₀`.

The new generators of `kSup (insert f₀ E)` that were not already in `kSup E` are
exactly the basis vectors `single σ 1` whose carrier is `⟨n+1, f₀⟩`; such a `σ` is
the lift of a simplex `A.lift σ` of the subdivision whose top vertex is the root
face, hence lies in `leSub P (root (n+1) f₀)`, and `kPsi (single (A.lift σ) 1) =
single σ 1` by `kGen_eq_single` and `liftEquiv_symm_lift`. -/
theorem insert_kSup_le_sup_map {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx} (A : Work.MbarHomology.CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) : Work.MbarHomology.CellAtlas.kSup A n (insert f₀ E) k ≤ Work.MbarHomology.CellAtlas.kSup A n E k ⊔ Submodule.map (Work.MbarHomology.CellAtlas.Insert.kPsi A n f₀ k) (Work.Subdivision.PolyCW.leSub P (A.root (n + 1) f₀) k) := by
  classical
  unfold kSup
  rw [Submodule.span_le]
  rintro y ⟨σ, hσ, rfl⟩
  by_cases hE : InD (C := C) n E (A.car σ)
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨σ, hE, rfl⟩)
  · have hcar : A.car σ = ⟨n + 1, f₀⟩ := by
      rcases (inD_insert_iff (C := C) (E := E) (f₀ := f₀)).mp hσ with h | h
      · exact absurd h hE
      · exact h
    refine Submodule.mem_sup_right ?_
    refine Submodule.mem_map.mpr ⟨Finsupp.single (A.lift σ) (1 : ℤ), ?_, ?_⟩
    · exact PolyCW.mem_leSub_of_support P (fun τ hτ i => by
        have hτ' : τ = A.lift σ := Finset.mem_singleton.mp (Finsupp.support_single_subset hτ)
        rw [hτ']
        have htop : (A.lift σ) (Fin.last k) = A.root (n + 1) f₀ := by
          rw [A.lift_top σ, hcar]
        calc (A.lift σ) i ≤ (A.lift σ) (Fin.last k) :=
              (A.lift σ).strictMono.monotone (Fin.le_last i)
          _ = A.root (n + 1) f₀ := htop)
    · rw [Insert.kPsi_sdElem]
      have htop : (A.lift σ).toFun (Fin.last k) = A.root (n + 1) f₀ := by
        rw [A.lift_top σ, hcar]
      rw [Insert.kGen_eq_single A n f₀ k (A.lift σ) htop]
      congr 1
      exact congrArg Subtype.val (Insert.liftEquiv_symm_lift A k (n + 1) f₀ σ hcar)

end Work.MbarHomology.CellAtlas
