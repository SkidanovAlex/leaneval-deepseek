/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Second-order jets of the holomorphic iterate `(Tsq c)^[n]` (item A3)

Item **A3** of the `SeedCertNum` contract (`NOTES_LEAD_mandelbar_noncusp.md` §2.2) certifies the
*simplicity* of the parabolic point: the second derivative `F''(z₁)` of
`F c = (Tsq c)^[5] = (T_c)^[10]` at the certified fixed point `z₁` is non-zero (the pilot value is
`F''(z₁) ≈ 755.4 + 1136.0 i`, so `|A| = |F''(z₁)|/2 ≈ 682`).

Unlike `T_c`, the map `Tsq c = (fun z => (z^2 + star c)^2 + c)` is a holomorphic polynomial, so no
Wirtinger pair is needed: an ordinary `(value, first derivative, second derivative)` jet suffices,
with the composition rule

  `(G∘H)'' = G''(H)·H'² + G'(H)·H''`,

which is `deriv_comp` applied twice (never Faà di Bruno).

## Contents

* `DJet2` — a triple of complex boxes `(v, d1, d2)`;
* `jet2Step`, `jet2Iter` — the box recursion mirroring `(G∘H)` above, with
  `G = Tsq c` (`G' = 4w(w²+c̄)`, `G'' = 12w²+4c̄`);
* `CBox.avoidsZero` and `not_mem_of_avoidsZero` — the kernel-checkable exclusion of `0` from a box;
* the soundness statement `mem_jet2` (delegated).
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Defs
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- A second-order jet of a holomorphic map, over a box: value, first and second derivative. -/
structure DJet2 where
  v : CBox
  d1 : CBox
  d2 : CBox
deriving DecidableEq, Repr

/-- One composition step with `G = Tsq c = fun w => (w^2 + conj c)^2 + c`, over the parameter box
`Ctyp`:  `v ↦ G v`, `d1 ↦ G'(v)·d1`, `d2 ↦ G''(v)·d1² + G'(v)·d2`. -/
def jet2Step (Ctyp : CBox) (J : DJet2) : DJet2 :=
  let wsa := (J.v.sq).add Ctyp.conj
  let dG := ((J.v.mulScalar (Dya.ofInt 4)).mul wsa)
  let d2G := ((J.v.sq).mulScalar (Dya.ofInt 12)).add (Ctyp.conj.mulScalar (Dya.ofInt 4))
  { v := (wsa.sq).add Ctyp
    d1 := dG.mul J.d1
    d2 := (d2G.mul (J.d1.sq)).add (dG.mul J.d2) }

/-- The `n`-fold jet of `(Tsq c)^[n]` over `Xz × Xt`. -/
def jet2Iter (Ctyp Xz : CBox) : ℕ → DJet2
  | 0 => ⟨Xz, oneBox, ⟨Dya.zero, Dya.zero, Dya.zero, Dya.zero⟩⟩
  | n + 1 => jet2Step Ctyp (jet2Iter Ctyp Xz n)

/-- A kernel-checkable test: the closed box `B` does not contain `0`. -/
def CBox.avoidsZero (B : CBox) : Bool :=
  Dya.pos B.rlo || Dya.negb B.rhi || Dya.pos B.ilo || Dya.negb B.ihi

namespace Dya

theorem toReal_le_zero_iff (a : Dya) : a.toReal ≤ 0 ↔ a.num ≤ 0 := by
  rw [Dya.toReal, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ a.exp), zero_mul]
  exact_mod_cast Iff.rfl

theorem zero_le_toReal_iff (a : Dya) : 0 ≤ a.toReal ↔ 0 ≤ a.num := by
  rw [Dya.toReal, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ a.exp), zero_mul]
  exact_mod_cast Iff.rfl

theorem toReal_lt_zero_iff (a : Dya) : a.toReal < 0 ↔ a.num < 0 := by
  rw [Dya.toReal, div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ a.exp), zero_mul]
  exact_mod_cast Iff.rfl

theorem zero_lt_toReal_iff (a : Dya) : 0 < a.toReal ↔ 0 < a.num := by
  rw [Dya.toReal, lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ a.exp), zero_mul]
  exact_mod_cast Iff.rfl

end Dya

/-- `0` belongs to a complex box exactly when the four numerators straddle zero. -/
theorem mem_zero_iff (B : CBox) :
    (0 : ℂ) ∈ B.toSet ↔ B.rlo.num ≤ 0 ∧ 0 ≤ B.rhi.num ∧ B.ilo.num ≤ 0 ∧ 0 ≤ B.ihi.num := by
  simp only [CBox.mem_toSet, Set.mem_setOf_eq, Complex.zero_re, Complex.zero_im,
    Dya.toReal_le_zero_iff, Dya.zero_le_toReal_iff]

/-- `avoidsZero B` is true exactly when one of the four numerators isolates `0`. -/
theorem avoidsZero_iff (B : CBox) :
    B.avoidsZero = true ↔
      (0 < B.rlo.num ∨ B.rhi.num < 0 ∨ 0 < B.ilo.num ∨ B.ihi.num < 0) := by
  simp only [CBox.avoidsZero, Bool.or_eq_true, Dya.pos, Dya.negb, decide_eq_true_eq]
  tauto

theorem not_mem_of_avoidsZero {B : CBox} (h : B.avoidsZero = true) : (0 : ℂ) ∉ B.toSet := by
  rw [avoidsZero_iff] at h
  rw [mem_zero_iff]
  omega

end

end Work.SeedCert
