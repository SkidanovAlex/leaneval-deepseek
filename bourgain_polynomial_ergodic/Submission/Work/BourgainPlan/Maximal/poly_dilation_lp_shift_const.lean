import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_leading

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set Finset
open scoped ENNReal BigOperators

/-! ## The shift constant `c`

`poly_dilation_lp_leading` gives the `Lᵖ` maximal bound for a single polynomial `P` with positive
leading coefficient.  Here we need the same bound with an *arbitrary* integer shift `c` inserted
inside the polynomial, and — crucially — with a constant `C` **uniform in `c`**.

The point is that adding the constant polynomial `C c` to `P` only translates the values of the
mapped real polynomial by `(c : ℝ)`, and the maximal operator is invariant under translating the
test function: with `ψ'(y) := ψ (y - c)`,

  `ψ'(x - Q(Ns)) = ψ (x - Q(Ns) - c) = ψ (x - (Q(Ns) + c)) = ψ (x - (Q + C c)(Ns))`,

while `∫ (ψ')^p = ∫ ψ^p` by translation invariance of Lebesgue measure.  Hence the bound for
`P + C c` applied to `ψ` is exactly the bound for `P` applied to `ψ'`, with the same constant. -/


theorem poly_dilation_lp_shift_const (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 1 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℤ) (ψ : ℝ → ℝ≥0∞), Measurable ψ → (∀ x : ℝ, ψ x ≠ ⊤) →
      (MeasureTheory.lintegral MeasureTheory.volume (fun x => ENNReal.rpow (ψ x) p) < ⊤) →
      MeasureTheory.lintegral MeasureTheory.volume
          (fun x => ENNReal.rpow (iSup fun N : ℕ =>
            MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))
              (fun s => ψ (x - ((P + Polynomial.C c).map (Int.castRingHom ℝ)).eval ((N : ℝ) * s)))) p)
        ≤ ENNReal.ofReal C *
          MeasureTheory.lintegral MeasureTheory.volume (fun x => ENNReal.rpow (ψ x) p) := by
  obtain ⟨C, hC, hbound⟩ := poly_dilation_lp_leading P hP hd hp
  refine ⟨C, hC, fun c ψ hψ hψfin hH => ?_⟩
  -- translate the test function so that the shift `c` is absorbed
  set ψ' : ℝ → ℝ≥0∞ := fun y => ψ (y - (c : ℝ)) with hψ'def
  have hψ'meas : Measurable ψ' := by
    rw [hψ'def]; exact hψ.comp (measurable_id.sub measurable_const)
  have hψ'fin : ∀ y, ψ' y ≠ ⊤ := fun y => hψfin _
  -- translation invariance of Lebesgue measure
  have hRHS : (∫⁻ y, (ψ' y) ^ p) = ∫⁻ y, (ψ y) ^ p := by
    have h1 : (∫⁻ y, (ψ' y) ^ p) = ∫⁻ y, (ψ (y + (-(c : ℝ)))) ^ p := by
      refine lintegral_congr fun y => ?_
      rw [hψ'def]; simp [sub_eq_add_neg]
    rw [h1, MeasureTheory.lintegral_add_right_eq_self (fun z => (ψ z) ^ p) (-(c : ℝ))]
  have hH' : ∫⁻ y, (ψ' y) ^ p < ⊤ := by rw [hRHS]; exact hH
  have hkey := hbound ψ' hψ'meas hψ'fin hH'
  -- the two maximal operators agree pointwise after the translation
  have hLHS : (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
      ψ (x - ((P + Polynomial.C c).map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))) ^ p)
      = (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
      ψ' (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))) ^ p) := by
    refine lintegral_congr fun x => ?_
    have h1 : (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - ((P + Polynomial.C c).map (Int.castRingHom ℝ)).eval ((N : ℝ) * s)))
      = (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ' (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))) := by
      refine iSup_congr fun N => ?_
      refine lintegral_congr fun s => ?_
      rw [hψ'def, poly_eval_map_add_C]
      congr 1
      ring
    rw [h1]
  calc (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - ((P + Polynomial.C c).map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))) ^ p)
      = (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ' (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s))) ^ p) := hLHS
    _ ≤ ENNReal.ofReal C * (∫⁻ y, (ψ' y) ^ p) := hkey
    _ = ENNReal.ofReal C * (∫⁻ y, (ψ y) ^ p) := by rw [hRHS]

end Work.BourgainPlan.Maximal
