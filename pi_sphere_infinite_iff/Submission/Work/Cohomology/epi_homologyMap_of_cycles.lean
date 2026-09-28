import Mathlib

open CategoryTheory Limits

namespace Work.Cohomology

theorem epi_homologyMap_of_cycles {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (n : ℕ)
    (h : ∀ (z : D.X n), (D.d n (n - 1)) z = 0 →
          ∃ (c : C.X n) (b : D.X (n + 1)),
            (C.d n (n - 1)) c = 0 ∧ (φ.f n) c = z + (D.d (n + 1) n) b) :
    CategoryTheory.Epi (HomologicalComplex.homologyMap φ n) := by
  have hnext : (ComplexShape.down ℕ).next n = n - 1 := by
    cases n with | zero => simp | succ n => simp
  -- It suffices to show that `cyclesMap φ n ≫ D.homologyπ n : C.cycles n ⟶ D.homology n` is epi.
  have key : Epi (HomologicalComplex.cyclesMap φ n ≫ D.homologyπ n) := by
    rw [ModuleCat.epi_iff_surjective]
    intro w
    -- lift the class `w` to a cycle of `D`
    have hsurj := (ModuleCat.epi_iff_surjective (D.homologyπ n)).mp inferInstance
    obtain ⟨zz, hzz⟩ := hsurj w
    have hz : D.d n (n - 1) (D.iCycles n zz) = 0 := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
      simp
    -- the standing hypothesis provides a cycle `c0` of `C` representing `z` up to a boundary
    obtain ⟨c0, b, hc0, hphi⟩ := h (D.iCycles n zz) hz
    -- build the corresponding element of `C.cycles n`
    have hs : (C.sc n).g c0 = 0 := by
      show C.d n ((ComplexShape.down ℕ).next n) c0 = 0
      rw [hnext]; exact hc0
    have hker : c0 ∈ LinearMap.ker (C.sc n).g.hom := hs
    let x : (C.sc n).moduleCatLeftHomologyData.K := ⟨c0, hker⟩
    let cc : C.cycles n := (C.sc n).moduleCatCyclesIso.inv x
    have hcc_i : C.iCycles n cc = c0 := by
      show (C.sc n).iCycles ((C.sc n).moduleCatCyclesIso.inv x) = c0
      rw [← ModuleCat.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles]
      rfl
    refine ⟨cc, ?_⟩
    show D.homologyπ n (HomologicalComplex.cyclesMap φ n cc) = w
    -- `cyclesMap φ n cc` and `zz` differ by the boundary `D.d (n+1) n b`
    have hL : D.iCycles n (HomologicalComplex.cyclesMap φ n cc) = φ.f n c0 := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply, hcc_i]
    have hR : D.iCycles n (zz + D.toCycles (n + 1) n b) = φ.f n c0 := by
      rw [map_add, ← ModuleCat.comp_apply (f := D.toCycles (n + 1) n) (g := D.iCycles n),
        HomologicalComplex.toCycles_i, hphi]
    have hkey : HomologicalComplex.cyclesMap φ n cc = zz + D.toCycles (n + 1) n b :=
      (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance (hL.trans hR.symm)
    rw [hkey, map_add, hzz]
    have hzero : D.homologyπ n (D.toCycles (n + 1) n b) = 0 := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
      simp
    rw [hzero, add_zero]
  -- conclude via the naturality square, using that `C.homologyπ n` is epi
  have key2 : Epi (C.homologyπ n ≫ HomologicalComplex.homologyMap φ n) := by
    rw [HomologicalComplex.homologyπ_naturality]
    exact key
  exact epi_of_epi (C.homologyπ n) (HomologicalComplex.homologyMap φ n)

end Work.Cohomology
