import Mathlib
import Submission.Subspace.RealRank.RankBox
import Submission.Subspace.RealRank.RealComplex
import Submission.Subspace.ApproxSpace
import Submission.Subspace.Stage3
import Submission.Subspace.RankDescReal

/-!
# The rank of the compound box

For the rank descent we need the exact `ℚ`-rank of the box of the *compound* system: given an
invertible real system `M`, exponents `xbar` with negative sum and a collection of `N' - 1`
independent integer vectors in the box, the rank is exactly `N' - 1 = C(N,r) - 1`.

* lower bound: the `N' - 1` wedge vectors ([`rankBox_compound_ge`] in `RankBox.lean`);
* upper bound: the general rank bound `no_independent_int_points_of_small_domain` applied to the
  compound system (negative exponent sum).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Submission.Subspace.RealRank

variable {N r : ℕ}

/-- **Rank bound for the compound box.** -/
theorem finrank_compBox_le {N r : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0)
    (xbar : Idx N r → ℝ) (hxbar : ∑ i, xbar i < 0) (hcard : 2 ≤ Fintype.card (Idx N r)) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      Module.finrank ℚ (Submodule.span ℚ (intCastVec '' compBox r M xbar Q))
        ≤ Fintype.card (Idx N r) - 1 := by
  classical
  haveI : Nonempty (Idx N r) := Fintype.card_pos_iff.mp (by omega)
  set L : Idx N r → Idx N r → ℂ := fun i j => ((Commons.LinearAlgebra.Matrix.compound r M) i j : ℂ)
    with hLdef
  have hLmat : Matrix.of L = (algebraMap ℝ ℂ).mapMatrix (Commons.LinearAlgebra.Matrix.compound r M) := rfl
  have hLdet : (Matrix.of L).det ≠ 0 := by
    intro h0
    have h1 : (Matrix.of L).det = (((Commons.LinearAlgebra.Matrix.compound r M).det : ℝ) : ℂ) := by
      rw [hLmat]
      exact (RingHom.map_det (algebraMap ℝ ℂ) (Commons.LinearAlgebra.Matrix.compound r M)).symm
    rw [h1, Complex.ofReal_eq_zero] at h0
    exact Commons.LinearAlgebra.Matrix.det_compound_ne_zero M hM h0
  have hind : LinearIndependent ℂ L := by
    have hunit : IsUnit (Matrix.of L) := (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hLdet)
    have hrow : LinearIndependent ℂ (Matrix.of L).row := Matrix.linearIndependent_rows_iff_isUnit.mpr hunit
    simpa [hLdef] using hrow
  obtain ⟨Q₀, hQ₀1, hQ₀⟩ :=
    Submission.Subspace.no_independent_int_points_of_small_domain hcard L hind xbar hxbar
  refine ⟨Q₀, hQ₀1, fun Q hQ => ?_⟩
  by_contra hlt
  push_neg at hlt
  -- the rank is maximal, hence `N'` independent box points exist
  have hfrB : Module.finrank ℚ (Submodule.span ℚ (intCastVec '' compBox r M xbar Q))
      = Fintype.card (Idx N r) := by
    have hle : Module.finrank ℚ (Submodule.span ℚ (intCastVec '' compBox r M xbar Q))
        ≤ Fintype.card (Idx N r) := by
      calc Module.finrank ℚ (Submodule.span ℚ (intCastVec '' compBox r M xbar Q))
          ≤ Module.finrank ℚ (⊤ : Submodule ℚ (Idx N r → ℚ)) := Submodule.finrank_mono le_top
        _ = Fintype.card (Idx N r) := by
              rw [finrank_top, Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨g, hgmem, hgli⟩ :=
    Submission.Subspace.exists_fin_box_independent (Fintype.card (Idx N r)) (compBox r M xbar Q)
      (Submodule.span ℚ (intCastVec '' compBox r M xbar Q)) Submodule.subset_span rfl hfrB
  -- reindex by `Idx N r`
  set e : Idx N r ≃ Fin (Fintype.card (Idx N r)) := Fintype.equivFin (Idx N r) with hedef
  refine hQ₀ Q hQ ⟨fun i => g (e i), ?_, ?_⟩
  · have hcomp := hgli.comp e e.injective
    have hfun : (fun i : Idx N r => fun k => ((g (e i)) k : ℚ))
        = ((fun i : Fin (Fintype.card (Idx N r)) => fun k => ((g i) k : ℚ)) ∘ ⇑e) := rfl
    rw [hfun]
    exact hcomp
  · intro i k
    have h1 : (∑ j : Idx N r, L k j * ((g (e i) j : ℤ) : ℂ))
        = ((∑ j : Idx N r, (Commons.LinearAlgebra.Matrix.compound r M) k j
            * (g (e i) j : ℝ) : ℝ) : ℂ) := by
      simp only [hLdef]
      push_cast
      rfl
    rw [h1, norm_ofReal_complex]
    exact (hgmem (e i)) k

/-- **The rank is exactly `N' - 1`.**  If the `N' - 1` wedge vectors of an invertible integer
matrix all lie in the compound box, then the box spans a hyperplane. -/
theorem span_compBox_eq_wedge {N r : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.det ≠ 0)
    (V : Matrix (Fin N) (Fin N) ℤ) (hV : (Commons.LinearAlgebra.Matrix.compound r V).det ≠ 0)
    (xbar : Idx N r → ℝ) (hxbar : ∑ i, xbar i < 0) (hcard : 2 ≤ Fintype.card (Idx N r))
    (Tstar : Idx N r) (Q₀ : ℝ) (hQ₀1 : 1 ≤ Q₀)
    (hQ₀ : ∀ Q' : ℝ, Q₀ ≤ Q' →
      Module.finrank ℚ (Submodule.span ℚ (intCastVec '' compBox r M xbar Q'))
        ≤ Fintype.card (Idx N r) - 1)
    (Q : ℝ) (hQ : Q₀ ≤ Q)
    (hmem : ∀ S : Idx N r, S ≠ Tstar →
      (fun S' => (Commons.LinearAlgebra.Matrix.compound r V) S' S) ∈ compBox r M xbar Q) :
    Submodule.span ℚ (intCastVec '' compBox r M xbar Q)
      = Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
          intCastVec (fun S' => (Commons.LinearAlgebra.Matrix.compound r V) S' S))) := by
  classical
  set W : Submodule ℚ (Idx N r → ℚ) := Submodule.span ℚ
    (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
      intCastVec (fun S' => (Commons.LinearAlgebra.Matrix.compound r V) S' S))) with hWdef
  set B : Submodule ℚ (Idx N r → ℚ) :=
    Submodule.span ℚ (intCastVec '' compBox r M xbar Q) with hBdef
  -- the wedge vectors are independent, so `W` has `N' - 1` dimensions
  have hli : LinearIndependent ℚ (fun S : {S : Idx N r // S ≠ Tstar} =>
      intCastVec (fun S' => (Commons.LinearAlgebra.Matrix.compound r V) S' S)) := by
    have hdet : ((Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)).det ≠ 0 := by
      rw [show (Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)
          = (Int.castRingHom ℚ).mapMatrix (Commons.LinearAlgebra.Matrix.compound r V) from rfl]
      rw [← RingHom.map_det (Int.castRingHom ℚ) (Commons.LinearAlgebra.Matrix.compound r V)]
      exact fun h => hV (Int.cast_eq_zero.mp h)
    have hunit : IsUnit ((Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hcols := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
    exact hcols.comp _ (fun a b hab => Subtype.ext hab)
  have hWfin : Module.finrank ℚ W = Fintype.card (Idx N r) - 1 := by
    rw [hWdef, finrank_span_eq_card hli,
      Fintype.card_subtype_compl (fun S : Idx N r => S = Tstar), Fintype.card_subtype_eq]
  have hle : W ≤ B := by
    rw [hWdef, Submodule.span_le]
    rintro v ⟨S, rfl⟩
    exact Submodule.subset_span ⟨_, hmem S S.2, rfl⟩
  have hBfin : Module.finrank ℚ B ≤ Fintype.card (Idx N r) - 1 := hQ₀ Q hQ
  have hfinWB : Module.finrank ℚ W ≤ Module.finrank ℚ B := Submodule.finrank_mono hle
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

end Submission.Subspace.RealRank
