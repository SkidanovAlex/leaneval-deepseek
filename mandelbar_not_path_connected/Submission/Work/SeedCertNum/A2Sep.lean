/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The exact-period separation (item A2)

`CBox.sep B C` is a kernel-checkable test that two closed boxes are disjoint (one of the four
axis separations holds); `disjoint_of_sep` is its soundness.  Instantiating it on the boxes
`boxV (pbox x₀ Xt) Xz j` of the orbit of the certified fixed point gives the *exact period* of
`z₁`: the four points `Z_j u` (`0 < j < 5`) lie in boxes disjoint from the box of `Z_0 u`, so
they differ from `z₁`.

## Main results

* `CBox.sep`, `disjoint_of_sep`;
* `krawData_sep` — the four disjointness checks for the emitted certificate.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

noncomputable section

/-- A kernel-checkable test that two closed boxes are disjoint. -/
def CBox.sep (B C : CBox) : Bool :=
  Dya.lt B.rhi C.rlo || Dya.lt C.rhi B.rlo || Dya.lt B.ihi C.ilo || Dya.lt C.ihi B.ilo

theorem disjoint_of_sep {B C : CBox} (h : B.sep C = true) : Disjoint B.toSet C.toSet := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [CBox.mem_toSet] at hz hz'
  have e1 : Dya.lt B.rhi C.rlo = false := by
    cases hl : Dya.lt B.rhi C.rlo with
    | false => rfl
    | true => exact absurd ((Dya.toReal_lt_iff B.rhi C.rlo).mp hl) (by linarith [hz.2.1, hz'.1])
  have e2 : Dya.lt C.rhi B.rlo = false := by
    cases hl : Dya.lt C.rhi B.rlo with
    | false => rfl
    | true => exact absurd ((Dya.toReal_lt_iff C.rhi B.rlo).mp hl) (by linarith [hz.1, hz'.2.1])
  have e3 : Dya.lt B.ihi C.ilo = false := by
    cases hl : Dya.lt B.ihi C.ilo with
    | false => rfl
    | true => exact absurd ((Dya.toReal_lt_iff B.ihi C.ilo).mp hl) (by linarith [hz.2.2.2, hz'.2.2.1])
  have e4 : Dya.lt C.ihi B.ilo = false := by
    cases hl : Dya.lt C.ihi B.ilo with
    | false => rfl
    | true => exact absurd ((Dya.toReal_lt_iff C.ihi B.ilo).mp hl) (by linarith [hz.2.2.1, hz'.2.2.2])
  have hsep : B.sep C = false := by
    simp only [CBox.sep, e1, e2, e3, e4, Bool.or_false]
  exact absurd (hsep ▸ h) Bool.false_ne_true

theorem krawData_sep1 :
    CBox.sep (boxV (pbox krawData.x₀ krawData.Xt) krawData.Xz 1) krawData.Xz = true := by
  decide

theorem krawData_sep2 :
    CBox.sep (boxV (pbox krawData.x₀ krawData.Xt) krawData.Xz 2) krawData.Xz = true := by
  decide

theorem krawData_sep3 :
    CBox.sep (boxV (pbox krawData.x₀ krawData.Xt) krawData.Xz 3) krawData.Xz = true := by
  decide

theorem krawData_sep4 :
    CBox.sep (boxV (pbox krawData.x₀ krawData.Xt) krawData.Xz 4) krawData.Xz = true := by
  decide

end

end Work.SeedCert
