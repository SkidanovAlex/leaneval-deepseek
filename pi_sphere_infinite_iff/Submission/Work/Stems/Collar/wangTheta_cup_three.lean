import Mathlib
import Submission.Work.Stems.Collar.WangThetaCupMixed
import Submission.Work.StemsB.Rat.WangThetaCupLow

/-!
# `θ(x · x · x) = 3 x · x · θ(x)` for the Wang transgression

*(Area STEMS.)*  The `C2`-odd step needs, besides `θ(x ⌣ x) = 2 x ⌣ θ(x)`
(`Work.StemsB.Rat.wangTheta_cup_low`) and the derivation property, the mixed-degree
multiplicativity `Work.Stems.Collar.wangTheta_cup_mixed` of the transgression `θ = ρ ∘ Σ ∘ λ_G^*`.

This file derives from the mixed case the cube statement

  `θ_{2b-3}(x ⌣ (x ⌣ x)) = 3 · ((x ⌣ x) ⌣ θ_{b-1}(x))`

for `b` odd (so that `x`, of degree `b - 1`, has even degree, hence the squares and cubes are
unambiguous), in the exact degree bookkeeping in which the statement is requested (the degree
`2 * b - 3` and the target degree `(b - 1) + (b - 1)`, versus the mixed formula's `(b - 2) + b - 1`
and `(b - 1) + ((b - 2) + 1)`).

The transport lemmas `wangTheta_index`, `cupT_transT_right`, `cupT_transT_left` (all proved by
`cases` on the degree equality, hence by `rfl` after the substitution) and `cupT_assoc'` isolate
the index bookkeeping.
-/

namespace Work.Stems.Collar

open Work.StemsB.Rat
open Work.StemsB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

/-- `wangTheta` is insensitive to the spelling of its degree index (all that changes is where the
degree transports sit). -/
private lemma wangTheta_index {b : ℕ} (hb : 2 ≤ b) {E : Type} [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    {n n' : ℕ} (h : n = n') (z : Work.Thom.Coh ℚ (n + b) ↥(p ⁻¹' {OnePoint.infty})) :
    transT ↥(p ⁻¹' {OnePoint.infty}) (congrArg (fun t => t + 1) h)
        (wangTheta b hb p d_G hT_G hT_O n z)
      = wangTheta b hb p d_G hT_G hT_O n'
          (transT ↥(p ⁻¹' {OnePoint.infty}) (congrArg (fun t => t + b) h) z) := by
  cases h
  rw [transT_self, transT_self]

/-- The cup product is compatible with a degree transport in its second variable. -/
private lemma cupT_transT_right {Y : Type} [TopologicalSpace Y] (p : ℕ) {q q' : ℕ} (h : q = q')
    (x : Work.Thom.Coh ℚ p Y) (y : Work.Thom.Coh ℚ q Y) :
    cupT Y p q' x (transT Y h y)
      = transT Y (congrArg (fun t => p + t) h) (cupT Y p q x y) := by
  cases h
  rw [transT_self, transT_self]

/-- The cup product is compatible with a degree transport in its first variable. -/
private lemma cupT_transT_left {Y : Type} [TopologicalSpace Y] {p p' : ℕ} (h : p = p') (q : ℕ)
    (x : Work.Thom.Coh ℚ p Y) (y : Work.Thom.Coh ℚ q Y) :
    cupT Y p' q (transT Y h x) y
      = transT Y (congrArg (fun t => t + q) h) (cupT Y p q x y) := by
  cases h
  rw [transT_self, transT_self]

/-- Associativity of the cup product, in the `transT` spelling. -/
private lemma cupT_assoc' {Y : Type} [TopologicalSpace Y] (n m k : ℕ)
    (x : Work.Thom.Coh ℚ n Y) (y : Work.Thom.Coh ℚ m Y) (z : Work.Thom.Coh ℚ k Y) :
    transT Y (Nat.add_assoc n m k) (cupT Y (n + m) k (cupT Y n m x y) z)
      = cupT Y n (m + k) x (cupT Y m k y z) :=
  (transT_cast _ _).trans
    (Work.Cohomology.cupH'_assoc ℚ (TopCat.toSSet.obj (TopCat.of Y)) n m k x y z)

theorem wangTheta_cup_three (b : ℕ) (hb : 2 ≤ b) (hbodd : Odd b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty})) :
    Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty}) (by omega : (2 * b - 3) + 1 = (b - 1) + (b - 1))
        (Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O (2 * b - 3)
          (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty})
            (by omega : (b - 1) + ((b - 2) + b) = (2 * b - 3) + b)
            (Work.StemsB.Rat.cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) ((b - 2) + b) x
              (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty})
                (by omega : (b - 1) + (b - 1) = (b - 2) + b)
                (Work.StemsB.Rat.cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x)))))
      = 3 • (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty})
              (by omega : ((b - 2) + b) + 0 = (b - 1) + (b - 1))
              (Work.StemsB.Rat.cupT ↥(p ⁻¹' {OnePoint.infty}) ((b - 2) + b) 0
                (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty})
                  (by omega : (b - 1) + (b - 1) = (b - 2) + b)
                  (Work.StemsB.Rat.cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (b - 1) x x))
                (Work.StemsB.Rat.wangThetaLow b hb E p d_G hT_G hT_O x))) := by
  set F := ↥(p ⁻¹' {OnePoint.infty}) with hF
  have h2 : (b - 1) + (b - 1) = (b - 2) + b := by omega
  have h1 : (b - 1) + ((b - 2) + b) = (2 * b - 3) + b := by omega
  have houter : (2 * b - 3) + 1 = (b - 1) + (b - 1) := by omega
  have h3 : ((b - 2) + b) + 0 = (b - 1) + (b - 1) := by omega
  have key : transT F houter (wangTheta b hb p d_G hT_G hT_O (2 * b - 3)
        (transT F h1 (cupT F (b - 1) ((b - 2) + b) x
          (transT F h2 (cupT F (b - 1) (b - 1) x x)))))
      = 3 • transT F h3 (cupT F ((b - 2) + b) 0
          (transT F h2 (cupT F (b - 1) (b - 1) x x))
          (wangThetaLow b hb E p d_G hT_G hT_O x)) := by
    set xx := cupT F (b - 1) (b - 1) x x with hxx
    set y2 := transT F h2 xx with hy2
    set W := cupT F (b - 1) ((b - 2) + b) x y2 with hW
    set Z := transT F h1 W with hZ
    set B := cupT F ((b - 2) + b) 0 y2 (wangThetaLow b hb E p d_G hT_G hT_O x) with hB
    set thL := wangThetaLow b hb E p d_G hT_G hT_O x with hthL
    -- the mixed formula at `m = b - 2`
    have hM1 : ((b - 2) + b - 1) + 1 = (b - 1) + ((b - 2) + 1) := by omega
    have hM2 : (b - 1) + ((b - 2) + b) = ((b - 2) + b - 1) + b := by omega
    have hM3 : ((b - 2) + b) + 0 = (b - 1) + ((b - 2) + 1) := by omega
    have hw : (b - 1) + (b - 1) = (b - 1) + ((b - 2) + 1) := by omega
    have hmix : transT F hM1 (wangTheta b hb p d_G hT_G hT_O ((b - 2) + b - 1) (transT F hM2 W))
        = ((-1 : ℚ) ^ (b - 1)) • cupT F (b - 1) ((b - 2) + 1) x
              (wangTheta b hb p d_G hT_G hT_O (b - 2) y2)
          + ((-1 : ℚ) ^ ((b - 1) * ((b - 2) + b) + ((b - 2) + b))) • transT F hM3 B := by
      have h0 := wangTheta_cup_mixed b hb E p d_G hT_G hT_O (b - 2) x y2
      convert h0 using 2
    -- Step I: put the left-hand side into the mixed formula's shape
    have hdb : 2 * b - 3 = (b - 2) + b - 1 := by omega
    have hZ' : transT F (congrArg (fun t => t + b) hdb) Z = transT F hM2 W := by
      rw [hZ, transT_comp h1 (congrArg (fun t => t + b) hdb) W]
    have hstep : transT F (congrArg (fun t => t + 1) hdb)
          (wangTheta b hb p d_G hT_G hT_O (2 * b - 3) Z)
        = wangTheta b hb p d_G hT_G hT_O ((b - 2) + b - 1) (transT F hM2 W) := by
      have hbase := wangTheta_index hb p d_G hT_G hT_O hdb Z
      rw [hZ'] at hbase
      exact hbase
    have hZA : wangTheta b hb p d_G hT_G hT_O (2 * b - 3) Z
        = transT F (congrArg (fun t => t + 1) hdb).symm
            (wangTheta b hb p d_G hT_G hT_O ((b - 2) + b - 1) (transT F hM2 W)) :=
      (transT_round (congrArg (fun t => t + 1) hdb)
          (wangTheta b hb p d_G hT_G hT_O (2 * b - 3) Z)).trans
        (congrArg (transT F (congrArg (fun t => t + 1) hdb).symm) hstep)
    have hfoldL : transT F hw (transT F houter (wangTheta b hb p d_G hT_G hT_O (2 * b - 3) Z))
        = transT F hM1 (wangTheta b hb p d_G hT_G hT_O ((b - 2) + b - 1) (transT F hM2 W)) := by
      rw [transT_comp houter hw (wangTheta b hb p d_G hT_G hT_O (2 * b - 3) Z), hZA,
        transT_comp (congrArg (fun t => t + 1) hdb).symm (houter.trans hw)
          (wangTheta b hb p d_G hT_G hT_O ((b - 2) + b - 1) (transT F hM2 W))]
    -- Step II: the right-hand side
    have hfoldR : transT F hw (3 • transT F h3 B) = (3 : ℚ) • transT F hM3 B := by
      rw [← Nat.cast_smul_eq_nsmul (R := ℚ) 3 (transT F h3 B)]
      rw [map_smul, transT_comp h3 hw B]
      exact congrArg (fun z => (3 : ℚ) • z) (transT_congr _ hM3 B)
    -- Step III: `A = 2 · X`
    have hL : (b - 2) + 1 = (b - 1) + 0 := by omega
    have hlow : transT F hL (wangTheta b hb p d_G hT_G hT_O (b - 2) y2)
        = (2 : ℚ) • cupT F (b - 1) 0 x thL := by
      have h := wangTheta_cup_low b hb E p d_G hT_G hT_O x
      rw [coeff_odd b hbodd] at h
      convert h using 2
    have hθ : wangTheta b hb p d_G hT_G hT_O (b - 2) y2
        = (2 : ℚ) • transT F hL.symm (cupT F (b - 1) 0 x thL) :=
      (transT_round hL (wangTheta b hb p d_G hT_G hT_O (b - 2) y2)).trans
        ((congrArg (transT F hL.symm) hlow).trans
          (map_smul (transT F hL.symm) (2 : ℚ) (cupT F (b - 1) 0 x thL)))
    have hassoc : transT F (Nat.add_assoc (b - 1) (b - 1) 0)
          (cupT F ((b - 1) + (b - 1)) 0 xx thL)
        = cupT F (b - 1) ((b - 1) + 0) x (cupT F (b - 1) 0 x thL) :=
      cupT_assoc' (b - 1) (b - 1) 0 x x thL
    have hB' : B = transT F (congrArg (fun t => t + 0) h2)
          (cupT F ((b - 1) + (b - 1)) 0 xx thL) :=
      cupT_transT_left h2 0 xx thL
    have hX : transT F hM3 B
        = transT F ((congrArg (fun t => t + 0) h2).trans hM3)
            (cupT F ((b - 1) + (b - 1)) 0 xx thL) := by
      rw [hB', transT_comp (congrArg (fun t => t + 0) h2) hM3 _]
    have hA' : cupT F (b - 1) ((b - 2) + 1) x (transT F hL.symm (cupT F (b - 1) 0 x thL))
        = transT F hM3 B := by
      rw [cupT_transT_right (b - 1) hL.symm x (cupT F (b - 1) 0 x thL), ← hassoc,
        transT_comp (Nat.add_assoc (b - 1) (b - 1) 0) (congrArg (fun t => (b - 1) + t) hL.symm)
          (cupT F ((b - 1) + (b - 1)) 0 xx thL), hX]
    have hA : cupT F (b - 1) ((b - 2) + 1) x (wangTheta b hb p d_G hT_G hT_O (b - 2) y2)
        = (2 : ℚ) • transT F hM3 B := by
      rw [hθ, map_smul]
      exact congrArg (fun z => (2 : ℚ) • z) hA'
    -- Step IV: the coefficients
    have hC1 : ((-1 : ℚ) ^ (b - 1)) = 1 := by
      obtain ⟨k, _⟩ := hbodd
      exact Even.neg_one_pow ⟨k, by omega⟩
    have hC2 : ((-1 : ℚ) ^ ((b - 1) * ((b - 2) + b) + ((b - 2) + b))) = 1 := by
      have hy : Even ((b - 2) + b) := ⟨b - 1, by omega⟩
      exact Even.neg_one_pow ((hy.mul_left (b - 1)).add hy)
    have hcross : ((-1 : ℚ) ^ (b - 1)) • cupT F (b - 1) ((b - 2) + 1) x
              (wangTheta b hb p d_G hT_G hT_O (b - 2) y2)
          + ((-1 : ℚ) ^ ((b - 1) * ((b - 2) + b) + ((b - 2) + b))) • transT F hM3 B
        = (3 : ℚ) • transT F hM3 B := by
      have h3q : (3 : ℚ) = 2 + 1 := by norm_num
      rw [hC1, hC2, one_smul, one_smul, hA, h3q, add_smul, one_smul]
    -- assembly
    have hfin : transT F hw (transT F houter (wangTheta b hb p d_G hT_G hT_O (2 * b - 3) Z))
        = transT F hw (3 • transT F h3 B) :=
      hfoldL.trans (hmix.trans (hcross.trans hfoldR.symm))
    exact (transT_round hw (transT F houter (wangTheta b hb p d_G hT_G hT_O (2 * b - 3) Z))).trans
      ((congrArg (transT F hw.symm) hfin).trans (transT_round hw (3 • transT F h3 B)).symm)
  convert key using 2

end

end Work.Stems.Collar
