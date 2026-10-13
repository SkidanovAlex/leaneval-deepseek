import Mathlib
import Submission.Work.WilE8.Extend

namespace Work.WilE8.Extend

open WilkiesDesign WilkiesDesign.E

/-- `MvPolynomial.rename` along an *injective* map of variables preserves the total degree.

The `≤` direction is `MvPolynomial.totalDegree_rename_le`. For the reverse direction: every
exponent `d` occurring in `Q` maps to the exponent `d.mapDomain f` occurring in `rename f Q`
(because `coeff_rename_mapDomain` computes the coefficient there and `f` is injective), and
`Finsupp.mapDomain` preserves the total degree of an exponent (it just redistributes the sum
over the fibres). -/
theorem totalDegree_rename_of_injective {σ τ : Type*} {R : Type*} [CommSemiring R]
    (f : σ → τ) (hf : Function.Injective f) (Q : MvPolynomial σ R) :
    (MvPolynomial.rename f Q).totalDegree = Q.totalDegree := by
  refine le_antisymm (MvPolynomial.totalDegree_rename_le f Q) ?_
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun d hd => ?_
  have hmem : Finsupp.mapDomain f d ∈ (MvPolynomial.rename f Q).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_rename_mapDomain f hf Q d]
    exact MvPolynomial.mem_support_iff.mp hd
  refine le_trans (le_of_eq ?_) (MvPolynomial.le_totalDegree hmem)
  exact (Finsupp.sum_mapDomain_index (h := fun _ (e : ℕ) => e) (fun _ => rfl)
    (fun _ _ _ => rfl)).symm

/-- Extending an EA polynomial along a variable map does not change its atom degree. -/
theorem atomDeg_extend {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (Q : EAPoly k r) : atomDeg (Work.WilE8.EAPoly.extend e Q) = atomDeg Q := by
  have hf : Function.Injective (Sum.map e id : Fin k ⊕ Fin r → Fin k' ⊕ Fin r) :=
    Sum.map_injective.mpr ⟨he, Function.injective_id⟩
  simp only [atomDeg, Work.WilE8.EAPoly.extend]
  rw [totalDegree_rename_of_injective (Sum.map e id) hf Q]

/-- Extending a basic set along a variable map does not change its degree. -/
theorem basic_deg_extend {k k' r : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (B : Basic k r) : (Work.WilE8.Basic.extend e B).deg = B.deg := by
  have h : (B.eqs ++ B.pos).map (atomDeg ∘ Work.WilE8.EAPoly.extend e)
      = (B.eqs ++ B.pos).map atomDeg :=
    List.map_congr_left fun Q _ => atomDeg_extend he Q
  simp only [Basic.deg, Work.WilE8.Basic.extend]
  rw [← List.map_append, List.map_map, h]

theorem semipf_deg_extend {k k' : ℕ} {e : Fin k → Fin k'} (he : Function.Injective e)
    (X : WilkiesDesign.E.SemiPf k) : (Work.WilE8.SemiPf.extend e X).deg = X.deg := by
  have h : X.basics.map (Basic.deg ∘ Work.WilE8.Basic.extend e) = X.basics.map Basic.deg :=
    List.map_congr_left fun B _ => basic_deg_extend he B
  simp only [SemiPf.deg, Work.WilE8.SemiPf.extend, List.map_map]
  exact congrArg List.sum h

end Work.WilE8.Extend
