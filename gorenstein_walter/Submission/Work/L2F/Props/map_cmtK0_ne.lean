import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Props.cmtK0_mulEquiv_hypTorus
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Props.hypTorus_card_sq
import Submission.Work.L2F.Mat2.centralizer_sq_neg_one_card
import Submission.Work.L2F.Conic.circle_card
import Submission.Work.L2F.Props.mem_cmtK0_iff_exists
import Submission.Work.L2F.Props.isSquare_neg_one_iff_not_isSquare
import Submission.Work.L2F.Props.le_cmtK0_of_map_toPGL_eq
import Submission.Work.L2F.Props.cmtK0_le_centralizer_of_le
import Submission.Work.L2F.Conic.circle_card_of_isSquare_neg_one
import Submission.Work.L2F.Conic.circle_ncard_conic
import Submission.Work.L2F.Conic.ncard_conic_plus_not

open scoped MatrixGroups
open Matrix

-- `hST` is part of the intended setting but the argument below does not need it.
set_option linter.unusedVariables false

namespace Work.L2F.Props

/-! ## Three bookkeeping lemmas

`cmtK0 F S` has the same cardinality as the norm-one torus `hypTorus F lam`
(`Work.L2F.Props.cmtK0_mulEquiv_hypTorus`), and that cardinality is `q + 1` or `q - 1` according as
`lam` is a nonsquare (`Work.L2F.Conic.hypTorus_card`) or a square
(`Work.L2F.Props.hypTorus_card_sq`).  The corresponding statements for `Nat.card (circle F)` are
`Work.L2F.Conic.circle_card_of_isSquare_neg_one` /
`Work.L2F.Conic.circle_card_of_not_isSquare_neg_one`. -/

/-- `cmtK0 F S` and `hypTorus F lam` have the same number of elements. -/
private theorem card_cmtK0_eq_card_hypTorus (F : Type*) [Field F]
    (S : Matrix.GeneralLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1) :
    Nat.card ↥(Work.L2F.Props.cmtK0 F S) = Nat.card (Work.L2F.hypTorus F lam) := by
  obtain ⟨e⟩ := Work.L2F.Props.cmtK0_mulEquiv_hypTorus F S lam hS hlam hns
  exact Nat.card_congr e.toEquiv

/-- `|hypTorus F lam| = q + 1` when `lam` is a nonsquare. -/
private theorem hypTorus_card_of_not_isSquare (F : Type*) [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (lam : F) (hlam : lam ≠ 0) (h : ¬ IsSquare lam) :
    Nat.card (Work.L2F.hypTorus F lam) = Nat.card F + 1 := by
  refine Work.L2F.Conic.hypTorus_card F h2 lam hlam (fun a ha => h ⟨a, ha.symm⟩)

/-- `|hypTorus F lam| = q - 1` when `lam` is a square. -/
private theorem hypTorus_card_of_isSquare (F : Type*) [Field F] [Fintype F]
    (h2 : (2 : F) ≠ 0) (lam : F) (hlam : lam ≠ 0) (h : IsSquare lam) :
    Nat.card (Work.L2F.hypTorus F lam) = Nat.card F - 1 := by
  obtain ⟨c, hc⟩ := h
  have hc' : c * c = lam := hc.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc'
    exact hlam hc'.symm
  exact Work.L2F.Props.hypTorus_card_sq F h2 lam c hc' hc0

/-- The tori `cmtK0 F S` and `cmtK0 F (S * toGL T)` have *distinct* images in `PGL(2,F)`
(they are the two distinct maximal tori of the application).  `5 ≤ Nat.card F` is needed:
over `F₃` both centralizers are `{±1}` and the claim is false.
Hint: if the images are equal then (kernel `{±1}`, `-1 ∈ cmtK0`) one gets
`cmtK0 F S ≤ cmtK0 F (S * toGL T)`; every element of that intersection commutes with `S`, with
`S * toGL T`, hence with `T`, so `cmtK0 F S ≤ C_{SL}(T)`, whose order is `circle F`
(`Work.L2F.Mat2.centralizer_sq_neg_one_card`).  Now `Nat.card (cmtK0 F S) = Nat.card
(Work.L2F.hypTorus F lam)` (`Work.L2F.Props.cmtK0_mulEquiv_hypTorus`), which is `q + 1` or `q - 1`
(`Work.L2F.Conic.hypTorus_card`, `Work.L2F.Props.hypTorus_card_sq`) according as `lam` is a
nonsquare or a square, while `Nat.card (circle F)` is `q - 1` or `q + 1` according as `-1` is a
square or not (`Work.L2F.Conic.circle_card`).  Since `det S = -lam` is a nonsquare and
`Work.L2F.Props.isSquare_neg_one_iff_not_isSquare` relates the two, the cases are opposite: if
`-1` is a square then `|cmtK0 F S| = q + 1 > q - 1 = |circle F|`, contradicting the inclusion;
if `-1` is not a square then `|cmtK0 F S| = q - 1` must divide `|circle F| = q + 1`, and the two
have coprime halves `(q-1)/2`, `(q+1)/2`, forcing `(q-1)/2 = 1`, i.e. `q = 3`, against `5 ≤ q`. -/
theorem map_cmtK0_ne (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (S : Matrix.GeneralLinearGroup (Fin 2) F)
    (T : Matrix.SpecialLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hdet : ¬ IsSquare (S : Matrix (Fin 2) (Fin 2) F).det)
    (hT2 : (T : Matrix (Fin 2) (Fin 2) F) * (T : Matrix (Fin 2) (Fin 2) F) = -1)
    (hST : Matrix.SpecialLinearGroup.toGL T * S = Work.L2F.Props.negGL F S *
      Matrix.SpecialLinearGroup.toGL T) :
    (Work.L2F.Props.cmtK0 F S).map Matrix.SpecialLinearGroup.toPGL ≠
      (Work.L2F.Props.cmtK0 F (S * Matrix.SpecialLinearGroup.toGL T)).map
        Matrix.SpecialLinearGroup.toPGL := by
  -- Suppose the two images coincide.
  intro hmap
  -- 1. The kernel of `SL(2,F) → PGL(2,F)` is `{±1}` and `-1 ∈ cmtK0`, so `cmtK0 F S` is
  --    contained in `cmtK0 F (S * toGL T)`.
  have hle1 := Work.L2F.Props.le_cmtK0_of_map_toPGL_eq F h2 S
    (S * Matrix.SpecialLinearGroup.toGL T) hmap
  -- 2. Every element of `cmtK0 F S` then commutes with `S` and with `S * toGL T`, hence with `T`.
  have hle2 := Work.L2F.Props.cmtK0_le_centralizer_of_le F S T hle1
  -- 3. Therefore `|cmtK0 F S|` divides `|circle F| = |C_{SL(2,F)}(T)|`.
  have hdvd : Nat.card ↥(Work.L2F.Props.cmtK0 F S) ∣ Nat.card (Work.L2F.circle F) := by
    rw [← Work.L2F.Mat2.centralizer_sq_neg_one_card F h2 T hT2]
    exact Subgroup.card_dvd_of_le hle2
  -- 4. `det S = -lam` and this is a nonsquare; `S` is non-scalar with `S * S = lam • 1`.
  have htr := Work.L2F.Props.trace_eq_zero_of_sq_eq_smul_one F _ lam hS hns
  have hdetS := Work.L2F.Props.det_eq_neg_of_sq_eq_smul_one F _ lam hS htr
  have hnsq : ¬ IsSquare (-lam) := by rw [← hdetS]; exact hdet
  have hiff := Work.L2F.Props.isSquare_neg_one_iff_not_isSquare F h2 lam hnsq
  have hcardK := card_cmtK0_eq_card_hypTorus F S lam hS hlam hns
  -- 5. The two cases are opposite.
  by_cases hs : IsSquare (-1 : F)
  · -- `-1` a square: `lam` is a nonsquare, so `|cmtK0 F S| = q + 1` but `|circle F| = q - 1`.
    have hns_lam : ¬ IsSquare lam := hiff.mp hs
    have hK : Nat.card ↥(Work.L2F.Props.cmtK0 F S) = Nat.card F + 1 := by
      rw [hcardK]
      exact hypTorus_card_of_not_isSquare F h2 lam hlam hns_lam
    have hC : Nat.card (Work.L2F.circle F) = Nat.card F - 1 :=
      Work.L2F.Conic.circle_card_of_isSquare_neg_one F h2 hs
    have hdvd' : Nat.card F + 1 ∣ Nat.card F - 1 := by
      rw [hK, hC] at hdvd
      exact hdvd
    have hle : Nat.card F + 1 ≤ Nat.card F :=
      le_trans (Nat.le_of_dvd (by omega) hdvd') (Nat.sub_le _ _)
    omega
  · -- `-1` not a square: `lam` is a square, so `|cmtK0 F S| = q - 1` divides `|circle F| = q + 1`.
    have hlam_sq : IsSquare lam := by
      by_contra h'
      exact hs (hiff.mpr h')
    have hK : Nat.card ↥(Work.L2F.Props.cmtK0 F S) = Nat.card F - 1 := by
      rw [hcardK]
      exact hypTorus_card_of_isSquare F h2 lam hlam hlam_sq
    have hC : Nat.card (Work.L2F.circle F) = Nat.card F + 1 := by
      rw [Work.L2F.Conic.circle_ncard_conic F]
      exact Work.L2F.Conic.ncard_conic_plus_not F h2 (fun i hi => hs ⟨i, hi.symm⟩)
    have hdvd' : Nat.card F - 1 ∣ Nat.card F + 1 := by
      rw [hK, hC] at hdvd
      exact hdvd
    -- `q - 1` divides `(q + 1) - (q - 1) = 2`, while `q - 1 ≥ 4`.
    have hdvd2 : Nat.card F - 1 ∣ 2 := by
      have h := Nat.dvd_sub hdvd' (dvd_refl (Nat.card F - 1))
      rwa [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at h
    have hle : Nat.card F - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega

end Work.L2F.Props
