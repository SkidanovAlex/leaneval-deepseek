import Mathlib
import Submission.Work.Kunneth.Chapter

/-!
# Cycles are killed by boundaries when homology is torsion

If every homology class in degree `j` of a chain complex of `ℤ`-modules has finite order, then
every cycle `x` in degree `j` has a nonzero multiple `m • x` which is a boundary, i.e. lies in the
image of the differential `K.d (j + 1) j`.

The mathematical content is the tautology "`x` is a cycle, so its class `[x] ∈ H_j` is defined, and
`m • [x] = [m • x] = 0` means exactly that `m • x` is a boundary", together with the concrete
description of the homology of a short complex of modules as the kernel of `g` modulo the image of
`f` (Mathlib's `ShortComplex.moduleCatLeftHomologyData` and
`ShortComplex.moduleCat_pOpcycles_eq_zero_iff`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

/-- **Torsion in homology kills cycles (short complex form).**  For a short complex `S` of
`ℤ`-modules whose homology is a torsion group, every "cycle" `x : S.X₂` (i.e. `S.g x = 0`) admits
`m > 0` with `m • x = S.f y` for some `y : S.X₁`.

The proof: the class of `x` in `S.homology` is `S.homologyπ (S.cyclesMk x hx)`; by hypothesis some
`m > 0` kills it.  Applying `S.homologyι` and using
`S.homologyπ ≫ S.homologyι = S.iCycles ≫ S.pOpcycles`, this says that the image of `m • x = m • S.iCycles z`
in `S.opcycles` vanishes, i.e. `m • x` lies in the range of `S.f`
(`ShortComplex.moduleCat_pOpcycles_eq_zero_iff`). -/
lemma shortComplex_torsion_of_homology_torsion (S : ShortComplex (ModuleCat ℤ))
    (htor : ∀ a : ↥S.homology, ∃ m : ℕ, 0 < m ∧ m • a = 0)
    (x : S.X₂) (hx : S.g.hom x = 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ y : S.X₁, S.f.hom y = m • x := by
  let z : S.cycles := S.cyclesMk x hx
  obtain ⟨m, hmpos, hm⟩ := htor (S.homologyπ z)
  refine ⟨m, hmpos, ?_⟩
  have hz : S.pOpcycles (m • x) = 0 := by
    have h1 : S.iCycles z = x := S.i_cyclesMk x hx
    have h3 : S.iCycles (m • z) = m • x := by
      rw [show S.iCycles (m • z) = m • S.iCycles z from by simp, h1]
    rw [← h3, ← ConcreteCategory.comp_apply, ← S.homology_π_ι, ConcreteCategory.comp_apply]
    rw [show S.homologyπ (m • z) = m • S.homologyπ z from by simp, hm]
    exact map_zero _
  rw [S.moduleCat_pOpcycles_eq_zero_iff] at hz
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, hy⟩

theorem cyclesTorsionOfHomologyTorsion (K : ChainComplex (ModuleCat ℤ) ℕ) (j : ℕ)
    (h : ∀ a : ↥(K.homology j), ∃ m : ℕ, 0 < m ∧ m • a = 0) :
    ∀ x : ↥(K.X j), (K.d j (j - 1)).hom x = 0 →
      ∃ m : ℕ, 0 < m ∧ ∃ y : ↥(K.X (j + 1)), (K.d (j + 1) j).hom y = m • x := by
  intro x hx
  -- the indices `c.next j = j - 1` and `c.prev j = j + 1` of the `ComplexShape.down ℕ`
  have hnext : (ComplexShape.down ℕ).next j = j - 1 := by
    by_cases hj : j = 0
    · subst hj
      rw [ComplexShape.next_eq_self' _ 0 (fun k hk => by rw [ComplexShape.down_Rel] at hk; omega)]
    · apply ComplexShape.next_eq'
      rw [ComplexShape.down_Rel]
      omega
  have hprev : (ComplexShape.down ℕ).prev j = j + 1 :=
    ComplexShape.prev_eq' _ (by rw [ComplexShape.down_Rel])
  -- `x` is a cycle for the short complex `K.sc j`
  have hxS : ((K.sc j).g).hom x = 0 := by
    show (K.d j ((ComplexShape.down ℕ).next j)).hom x = 0
    rw [hnext]
    exact hx
  have htor : ∀ a : ↥((K.sc j).homology), ∃ m : ℕ, 0 < m ∧ m • a = 0 := h
  obtain ⟨m, hmpos, y, hy⟩ := shortComplex_torsion_of_homology_torsion (K.sc j) htor x hxS
  refine ⟨m, hmpos, ?_⟩
  rw [← hprev]
  exact ⟨y, hy⟩

end Work.Serre
