import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

open MeasureTheory Set
open scoped ENNReal

namespace Commons.Lattice.Minkowski

/-- **Minkowski's convex-body (second fundamental) statement** in its standard symmetric-convex-body form, which reaches *cone-shaped* bodies and not only ellipsoids/balls. Proof route: let `K' := (1/2)K`. If `K ∩ L = {0}` the translates `K' + l` (`l ∈ L`) are pairwise disjoint: if `x/2 + l = y/2 + l'` with `x,y ∈ K`, then `(x - y)/2 = l' - l ∈ L`, while convexity and symmetry give `(x - y)/2 ∈ K`, hence `x = y` and `l = l'`. So the translates fit inside a fundamental domain (`ZLattice.isAddFundamentalDomain`) and measure additivity gives `volume K' ≤ ZLattice.covolume L`, i.e. `volume K ≤ 2^n * covolume L`. -/
theorem convex_body {n : ℕ} {L : Submodule ℤ (EuclideanSpace ℝ (Fin n))}
    [DiscreteTopology L] [IsZLattice ℝ L]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hcl : IsClosed K) (hbdd : Bornology.IsBounded K) (hint : (interior K).Nonempty)
    (hvol : (2 : ℝ) ^ n * ZLattice.covolume L < (MeasureTheory.volume K).toReal) :
    ∃ v : L, v ≠ 0 ∧ (v : EuclideanSpace ℝ (Fin n)) ∈ K := by
  classical
  haveI : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  let F : Set (EuclideanSpace ℝ (Fin n)) :=
    ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L (Module.finBasis ℤ L))
  have hfund : IsAddFundamentalDomain L F MeasureTheory.volume :=
    ZLattice.isAddFundamentalDomain (Module.finBasis ℤ L) MeasureTheory.volume
  have hfund' : IsAddFundamentalDomain L.toAddSubgroup F MeasureTheory.volume := hfund
  have hcov : ZLattice.covolume L = MeasureTheory.volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L MeasureTheory.volume hfund
  have hFtop : MeasureTheory.volume F ≠ ⊤ :=
    ne_of_lt (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded _))
  have hKtop : MeasureTheory.volume K ≠ ⊤ := ne_of_lt hbdd.measure_lt_top
  have hpowtop : (2 : ℝ≥0∞) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) ≠ ⊤ :=
    ENNReal.pow_ne_top (by norm_num)
  have hlt : MeasureTheory.volume F * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) <
      MeasureTheory.volume K := by
    refine (ENNReal.toReal_lt_toReal (a := MeasureTheory.volume F * 2 ^
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) (b := MeasureTheory.volume K)
      (ENNReal.mul_ne_top hFtop hpowtop) hKtop).mp ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, finrank_euclideanSpace, Fintype.card_fin]
    simp only [ENNReal.toReal_ofNat]
    have h := hvol
    rw [hcov, measureReal_def, mul_comm] at h
    exact h
  obtain ⟨x, hxne, hxmem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund' hsym hconv hlt
  exact ⟨x, hxne, hxmem⟩

end Commons.Lattice.Minkowski