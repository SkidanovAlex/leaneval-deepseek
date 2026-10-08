import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.cmtK0_mulEquiv_hypTorus
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Props.hypTorus_card_sq
import Submission.Work.L2F.Props.isSquare_neg_one_iff_not_isSquare
import Submission.Work.L2F.Props.mod_four_eq_one_iff_isSquare_neg_one
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Mat2.trace_eq_zero_det_eq_neg_of_sq_eq_smul_one
import Submission.Work.L2F.Props.toPGL_mem_ker_iff
import Submission.Work.L2F.Props.card_ker_cmtK0_toPGL
import Submission.Work.L2F.Props.mod_four_eq_one_iff_isSquare_neg_one_card
import Submission.Work.L2F.Props.isCyclic_map_cmtK0

namespace Work.L2F.Props

/-- The image of the torus `cmtK0 F S` in `PGL(2,F)` is cyclic of odd order `(q±1)/2`, the order
being `(q+1)/2` for `q ≡ 1 (mod 4)` and `(q-1)/2` for `q ≡ 3 (mod 4)`.
Hint: `cmtK0 F S ≃* hypTorus F lam` (`Work.L2F.Props.cmtK0_mulEquiv_hypTorus`), which is cyclic
(`Work.L2F.Conic.hypTorus_cyclic`), so the image is cyclic (a quotient); the map `SL → PGL` has
kernel `{±1}` and `-1 ∈ cmtK0 F S`, so `Nat.card (image) = Nat.card (cmtK0 F S) / 2`, and
`Nat.card (cmtK0 F S) = Nat.card (hypTorus F lam)` is `q + 1` (`Work.L2F.Conic.hypTorus_card`,
when `lam` is a nonsquare) or `q - 1` (`Work.L2F.Props.hypTorus_card_sq`, when `lam = c²`);
`det S = -lam` (Cayley–Hamilton, from `S non-scalar` and `S² = lam • 1`) is a nonsquare (`hdet`), so
`lam` is a square iff `-1` is not (`Work.L2F.Props.isSquare_neg_one_iff_not_isSquare`), i.e. iff
`q ≡ 3 (mod 4)` (`FiniteField.isSquare_neg_one_iff` for a general finite field, or
`Work.L2F.Props.mod_four_eq_one_iff_isSquare_neg_one` for `GaloisField`), and in both cases
`(q ± 1)/2` is odd. -/
theorem card_map_cmtK0 (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (q : ℕ)
    (hq : Nat.card F = q) (S : Matrix.GeneralLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hdet : ¬ IsSquare (S : Matrix (Fin 2) (Fin 2) F).det) :
    IsCyclic ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) ∧
    Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) =
      (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2) ∧
    Odd (Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL)) := by
  classical
  -- The image of `cmtK0 F S` is cyclic, being a quotient of the cyclic group `hypTorus F lam`.
  have hcyc : IsCyclic ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) :=
    isCyclic_map_cmtK0 F h2 S lam hS hlam hns
  -- `q` is odd and `-1` is a square iff `q ≡ 1 (mod 4)`.
  obtain ⟨hq4iff, hqodd⟩ := mod_four_eq_one_iff_isSquare_neg_one_card F h2 q hq
  -- Cayley–Hamilton: `det S = -lam`, so `-lam` is a nonsquare.
  obtain ⟨-, hdetS⟩ :=
    Work.L2F.Mat2.trace_eq_zero_det_eq_neg_of_sq_eq_smul_one F
      (S : Matrix (Fin 2) (Fin 2) F) lam hS hns
  have hnotsq : ¬ IsSquare (-lam) := by rw [← hdetS]; exact hdet
  have hnegiff : IsSquare (-1 : F) ↔ ¬ IsSquare lam :=
    Work.L2F.Props.isSquare_neg_one_iff_not_isSquare F h2 lam hnotsq
  -- `cmtK0 F S` and `hypTorus F lam` have the same cardinality.
  have hcard0 : Nat.card (Work.L2F.Props.cmtK0 F S) = Nat.card (Work.L2F.hypTorus F lam) := by
    obtain ⟨e⟩ := Work.L2F.Props.cmtK0_mulEquiv_hypTorus F S lam hS hlam hns
    exact Nat.card_congr e.toEquiv
  -- The restriction of `SL(2,F) → PGL(2,F)` to `cmtK0 F S` is `2`-to-`1`.
  let φ : ↥(Work.L2F.Props.cmtK0 F S) →* Matrix.ProjGenLinGroup (Fin 2) F :=
    (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
      (Work.L2F.Props.cmtK0 F S).subtype
  have hker2 : Nat.card φ.ker = 2 := card_ker_cmtK0_toPGL F h2 S
  have hrange : φ.range = (Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL := by
    change ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
      (Work.L2F.Props.cmtK0 F S).subtype).range =
        Subgroup.map Matrix.SpecialLinearGroup.toPGL (Work.L2F.Props.cmtK0 F S)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkey : Nat.card (Work.L2F.Props.cmtK0 F S) =
      Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) * 2 := by
    have hq' := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have heq : Nat.card (↥(Work.L2F.Props.cmtK0 F S) ⧸ φ.ker) = Nat.card φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [heq, hrange, hker2] at hq'
    exact hq'
  by_cases hsq : IsSquare (-1 : F)
  · -- `q ≡ 1 (mod 4)`: `lam` is a nonsquare, so `|cmtK0| = q + 1`.
    have hq41 : q % 4 = 1 := hq4iff.mpr hsq
    have hnotlam : ¬ IsSquare lam := hnegiff.mp hsq
    have hcardn : Nat.card (Work.L2F.hypTorus F lam) = q + 1 := by
      rw [← hq]
      exact Work.L2F.Conic.hypTorus_card F h2 lam hlam (fun a ha => hnotlam ⟨a, ha.symm⟩)
    have hmul : Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) * 2
        = q + 1 := by
      rw [← hkey, hcard0, hcardn]
    refine ⟨hcyc, ?_, ?_⟩
    · have hif : (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2) = (q + 1) / 2 := by
        simp [hq41]
      rw [hif]
      omega
    · rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hqodd
      omega
  · -- `q ≡ 3 (mod 4)`: `lam = c ^ 2` is a square, so `|cmtK0| = q - 1`.
    have hsql : IsSquare lam := by
      by_contra hcon
      exact hsq (hnegiff.mpr hcon)
    obtain ⟨c, hc⟩ := hsql
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hlam (by simpa using hc)
    have hne41 : q % 4 ≠ 1 := fun h => hsq (hq4iff.mp h)
    have hq43 : q % 4 = 3 := by
      rw [Nat.odd_iff] at hqodd
      omega
    have hcardn : Nat.card (Work.L2F.hypTorus F lam) = q - 1 := by
      rw [← hq]
      exact Work.L2F.Props.hypTorus_card_sq F h2 lam c hc.symm hc0
    have hmul : Nat.card ((Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL) * 2
        = q - 1 := by
      rw [← hkey, hcard0, hcardn]
    refine ⟨hcyc, ?_, ?_⟩
    · have hif : (if q % 4 = 1 then (q + 1) / 2 else (q - 1) / 2) = (q - 1) / 2 := by
        simp [hne41]
      rw [hif]
      omega
    · rw [Nat.odd_iff]
      rw [Nat.odd_iff] at hqodd
      omega

end Work.L2F.Props
