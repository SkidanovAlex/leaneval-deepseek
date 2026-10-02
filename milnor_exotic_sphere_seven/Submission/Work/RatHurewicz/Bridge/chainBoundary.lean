import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A cycle of vanishing homology class is a boundary

For a chain complex `K` of `ℤ`-modules and a cycle `z ∈ Z_n(K)` whose homology class vanishes, the
underlying chain is the boundary of a `(n+1)`-chain.  This is the elementary "cycles modulo
boundaries" statement, obtained from the exactness of the short complex `K.sc n`.
-/

open CategoryTheory

namespace Work.RatHurewicz.Bridge

noncomputable section

/-- Applying the index transport `XIsoOfEq` to the differential. -/
theorem XIsoOfEq_hom_comp_d_apply (K : ChainComplex (ModuleCat ℤ) ℕ) {n : ℕ}
    (hprev : (ComplexShape.down ℕ).prev n = n + 1) (w : K.X ((ComplexShape.down ℕ).prev n)) :
    (K.d (n + 1) n).hom ((K.XIsoOfEq hprev).hom w)
      = (K.d ((ComplexShape.down ℕ).prev n) n).hom w := by
  have hh := congrArg (fun (g : K.X ((ComplexShape.down ℕ).prev n) ⟶ K.X n) =>
    (ConcreteCategory.hom g) w) (HomologicalComplex.XIsoOfEq_hom_comp_d K hprev n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh

/-- **A cycle of a chain complex of `ℤ`-modules whose class vanishes is a boundary.** -/
theorem chain_homologypi_eq_zero (K : ChainComplex (ModuleCat ℤ) ℕ) [∀ i, K.HasHomology i]
    (n : ℕ) (z : K.cycles n) (h : K.homologyπ n z = 0) :
    ∃ y : K.X (n + 1), (K.d (n + 1) n).hom y = (K.iCycles n).hom z := by
  have hprev : (ComplexShape.down ℕ).prev n = n + 1 := by
    rw [ComplexShape.prev_eq']
    rfl
  let z' : (K.sc n).cycles := z
  have hkey : ∃ w : (K.sc n).X₁, (K.sc n).f.hom w = (K.sc n).iCycles.hom z' := by
    have hzero : (K.sc n).homologyι ((K.sc n).homologyπ z') = 0 := by
      rw [show (K.sc n).homologyπ z' = 0 from h, map_zero]
    have hpop : (K.sc n).pOpcycles ((K.sc n).iCycles.hom z') = 0 := by
      have hh := congrArg (fun (g : (K.sc n).cycles ⟶ (K.sc n).opcycles) => g z')
        (ShortComplex.homology_π_ι (K.sc n))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      rw [← hh]
      exact hzero
    have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc n) ((K.sc n).iCycles.hom z')).mp hpop
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hkey
  refine ⟨(K.XIsoOfEq hprev).hom w, ?_⟩
  rw [XIsoOfEq_hom_comp_d_apply K hprev w]
  exact hw

end

end Work.RatHurewicz.Bridge
