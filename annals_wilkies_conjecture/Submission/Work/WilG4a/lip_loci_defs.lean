/-
  WilG4a — the "lipschitz loci" of BNZ Lemma 5.3 as `Ω`-sets: the vocabulary.

  For a family member `f : ℝᵖ × ℝ → ℝ` (viewed through `famFun f`), the loci

    * `(sliceDiff f)ᶜ`      — where the slice `x ↦ f l x` is not differentiable,
    * `(sliceDerivCont f)ᶜ`  — where its derivative is not continuous,
    * `domSet f g`           — where `|∂_x f| ≤ |∂_x g|`,
    * `posSet f`, `negSet f` — the sign of `∂_x f`,
    * `strip p`              — `{0 < x < 1}`

  are all `Ω`-definable with a format independent of `D` and a degree polynomial in `D`.

  The differentiability data is *first-order*: the `ε`-`δ` characterisation of `HasDerivAt`
  shows that the set `Sset` of pairs `(z,s)` with `s` the slice derivative at `z` is defined
  by a first-order (`ε`-`δ`) formula over the graph of the family, hence is an `Ω`-set with
  sharp bounds (`Work.WilG1.Plumb.Sset_omega_aux`).  Every other locus is then obtained from
  `Sset` by projections, complements, finite unions/intersections and coordinate pullbacks.

  This file fixes the *sets* (`sliceDiffC`, `posSetAux`, `domSetAux`, `sliceDerivContAux`,
  ...) and proves the low-level membership lemmas for the polynomial pieces (`posHalf_mem`,
  `cmpSet_mem`, `contLtx_mem`, ...).  The identities with the loci and the composite
  membership lemmas live in sibling modules.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG1.Plumb.junkPartial_mem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesConjecture WilkiesDesign

variable {p : ℕ}

/-! ## 1. The derivative set -/

/-- `derSet f ⊆ ℝ^{p+2}`: the set of pairs `(z,s)` such that `s` is the slice derivative of
`f` at `z`.  It is `Work.WilG1.Plumb.Sset` for the one-variable family `famFun f` in the
direction of the variable. -/
def derSet (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 2) → ℝ) :=
  Work.WilG1.Plumb.Sset (p + 1) (Fin.last p) (famFun f)

/-- Reading `derSet`: `(z,s) ∈ derSet f` iff `s` is the slice derivative of `f` at `z`. -/
theorem mem_derSet (f : (Fin p → ℝ) → ℝ → ℝ) (v : Fin (p + 2) → ℝ) :
    v ∈ derSet f ↔ IsSliceDeriv f (Fin.init v) (v (Fin.last (p + 1))) := by
  rw [derSet, Work.WilG1.Plumb.Sset_char (n := p) (i := Fin.last p) (f := famFun f)]
  simp only [Set.mem_setOf_eq]
  have hfun : (fun t : ℝ =>
        famFun f ((Fin.last p).insertNth t ((Fin.last p).removeNth (Fin.init v))))
      = sliceFun f (Fin.init v) := by
    funext t
    rw [Fin.insertNth_removeNth]
    rfl
  rw [hfun]
  exact Work.WilG1.Plumb.hasDerivAt_iff_epsDeriv.symm

/-! ## 2. Polynomial pieces -/

/-- The positive half-space `{v | 0 < v k}`. -/
def posHalf (n : ℕ) (k : Fin n) : Set (Fin n → ℝ) := {v | 0 < v k}

/-- The negative half-space `{v | v k < 0}`. -/
def negHalf (n : ℕ) (k : Fin n) : Set (Fin n → ℝ) := {v | v k < 0}

theorem posHalf_mem (S : SOMin) (n : ℕ) (k : Fin n) (D : ℕ) :
    posHalf n k ∈ S.Ω (n + 2) ((Polynomial.C 3).eval D) n := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := n) D (MvPolynomial.X k)
  have htd : (MvPolynomial.X k : MvPolynomial (Fin n) ℝ).totalDegree + 2 = 3 := by
    rw [MvPolynomial.totalDegree_X]
  simpa [posHalf, htd, MvPolynomial.eval_X] using h

theorem negHalf_mem (S : SOMin) (n : ℕ) (k : Fin n) (D : ℕ) :
    negHalf n k ∈ S.Ω (n + 2) ((Polynomial.C 3).eval D) n := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := n) D (-(MvPolynomial.X k))
  have htd : (-(MvPolynomial.X k) : MvPolynomial (Fin n) ℝ).totalDegree + 2 = 3 := by
    rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]
  have hset : {x : Fin n → ℝ | 0 < MvPolynomial.eval x (-(MvPolynomial.X k))} = negHalf n k := by
    ext x
    simp [negHalf, MvPolynomial.eval_neg, MvPolynomial.eval_X]
  rw [hset] at h
  simpa [htd] using h

/-! ## 3. The three easy loci -/

/-- `(sliceDiff f)ᶜ`, written as the complement of the projection of `derSet f`. -/
def sliceDiffC (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1) → ℝ) :=
  (projLast (derSet f))ᶜ

/-- `posSet f`, written as the projection of `derSet f ∩ {s > 0}`. -/
def posSetAux (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1) → ℝ) :=
  projLast (derSet f ∩ posHalf (p + 2) (Fin.last (p + 1)))

/-- `negSet f`, written as the projection of `derSet f ∩ {s < 0}`. -/
def negSetAux (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1) → ℝ) :=
  projLast (derSet f ∩ negHalf (p + 2) (Fin.last (p + 1)))

/-! ## 4. The domination locus -/

/-- `(z,s) ↦ (z,s)` inside `ℝ^{p+3}`. -/
def iotaA (p : ℕ) : Fin (p + 2) → Fin (p + 3) := Fin.castSucc

/-- `(z,t) ↦ (z,t)` inside `ℝ^{p+3}`, the `t`-coordinate being the last one. -/
def iotaB (p : ℕ) : Fin (p + 2) → Fin (p + 3) :=
  Fin.lastCases (Fin.last (p + 2)) (Fin.castAdd 2)

/-- The comparison set `{|s| ≤ |t|}` inside `ℝ^{p+3}` (coordinates `(z,s,t)`). -/
def cmpSet (p : ℕ) : Set (Fin (p + 3) → ℝ) :=
  {w | |w (Fin.castSucc (Fin.last (p + 1)))| ≤ |w (Fin.last (p + 2))|}

theorem cmpSet_eq (p : ℕ) :
    cmpSet p = ({w : Fin (p + 3) → ℝ |
      0 < MvPolynomial.eval w ((MvPolynomial.X (Fin.castSucc (Fin.last (p + 1)))) ^ 2 -
        (MvPolynomial.X (Fin.last (p + 2))) ^ 2)})ᶜ := by
  ext w
  simp only [cmpSet, Set.mem_setOf_eq, Set.mem_compl_iff, MvPolynomial.eval_sub,
    MvPolynomial.eval_pow, MvPolynomial.eval_X]
  constructor
  · intro h
    have h2 := sq_le_sq.mpr h
    nlinarith
  · intro h
    have h2 : (w (Fin.castSucc (Fin.last (p + 1)))) ^ 2 ≤ (w (Fin.last (p + 2))) ^ 2 := by
      nlinarith
    exact (sq_le_sq.mp h2)

theorem cmpPoly_totalDegree (p : ℕ) :
    (((MvPolynomial.X (Fin.castSucc (Fin.last (p + 1)))) ^ 2 -
      (MvPolynomial.X (Fin.last (p + 2))) ^ 2 : MvPolynomial (Fin (p + 3)) ℝ)).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]

theorem cmpSet_mem (S : SOMin) (p : ℕ) (D : ℕ) :
    cmpSet p ∈ S.Ω (p + 6) ((Polynomial.C 4).eval D) (p + 3) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 3) D
    ((MvPolynomial.X (Fin.castSucc (Fin.last (p + 1)))) ^ 2 -
      (MvPolynomial.X (Fin.last (p + 2))) ^ 2 : MvPolynomial (Fin (p + 3)) ℝ)
  rw [cmpSet_eq]
  refine S.compl (Work.WilG1.Omega.mono h le_rfl ?_)
  have htd := cmpPoly_totalDegree p
  simp only [Polynomial.eval_C]
  omega

/-- `domSet f g`, written as the double projection of the set of `(z,s,t)` with
`(z,s) ∈ derSet f`, `(z,t) ∈ derSet g` and `|s| ≤ |t|`. -/
def domSetAux (f g : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1) → ℝ) :=
  projLast (projLast (Work.WilG5.coordPre (iotaA p) (derSet f) ∩
    Work.WilG5.coordPre (iotaB p) (derSet g) ∩ cmpSet p))

/-! ## 5. The derivative-continuity locus -/

section Cont

/-- The coordinate of `s` in `ℝ^{p+6}` (the layout is `(z,s,ε,δ,x',s')`). -/
def cS (p : ℕ) : Fin (p + 6) := ⟨p + 1, by omega⟩

/-- The coordinate of `ε` in `ℝ^{p+6}`. -/
def cE (p : ℕ) : Fin (p + 6) := ⟨p + 2, by omega⟩

/-- The coordinate of `δ` in `ℝ^{p+6}`. -/
def cD (p : ℕ) : Fin (p + 6) := ⟨p + 3, by omega⟩

/-- The coordinate of `x'` in `ℝ^{p+6}`. -/
def cP (p : ℕ) : Fin (p + 6) := ⟨p + 4, by omega⟩

/-- The coordinate of `s'` in `ℝ^{p+6}`. -/
def cSP (p : ℕ) : Fin (p + 6) := ⟨p + 5, by omega⟩

/-- The coordinate of the variable `x = z(last)` in `ℝ^{p+6}`. -/
def cX (p : ℕ) : Fin (p + 6) := ⟨p, by omega⟩

/-- `(z,s) ↦ (z,s,ε,δ,x',s')`. -/
def iotaContA (p : ℕ) : Fin (p + 2) → Fin (p + 6) := Fin.castAdd 4

/-- `(z,x',s') ↦ (z,s,ε,δ,x',s')`. -/
def iotaContB (p : ℕ) : Fin (p + 2) → Fin (p + 6) :=
  Fin.lastCases (cSP p) (Fin.lastCases (cP p) (Fin.castAdd 6))

/-- `|x' - x| < δ` as a polynomial condition. -/
def contLtx (p : ℕ) : Set (Fin (p + 6) → ℝ) :=
  {w | (w (cP p) - w (cX p)) ^ 2 < (w (cD p)) ^ 2}

/-- `|s' - s| < ε` as a polynomial condition. -/
def contEps (p : ℕ) : Set (Fin (p + 6) → ℝ) :=
  {w | (w (cSP p) - w (cS p)) ^ 2 < (w (cE p)) ^ 2}

theorem contLtx_eq (p : ℕ) :
    contLtx p = {w : Fin (p + 6) → ℝ |
      0 < MvPolynomial.eval w (((MvPolynomial.X (cD p)) ^ 2 -
        (MvPolynomial.X (cP p) - MvPolynomial.X (cX p)) ^ 2 :
          MvPolynomial (Fin (p + 6)) ℝ))} := by
  ext w
  simp only [contLtx, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]
  constructor <;> intro h <;> nlinarith

theorem contEps_eq (p : ℕ) :
    contEps p = {w : Fin (p + 6) → ℝ |
      0 < MvPolynomial.eval w (((MvPolynomial.X (cE p)) ^ 2 -
        (MvPolynomial.X (cSP p) - MvPolynomial.X (cS p)) ^ 2 :
          MvPolynomial (Fin (p + 6)) ℝ))} := by
  ext w
  simp only [contEps, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]
  constructor <;> intro h <;> nlinarith

theorem contLtxPoly_totalDegree (p : ℕ) :
    (((MvPolynomial.X (cD p)) ^ 2 - (MvPolynomial.X (cP p) - MvPolynomial.X (cX p)) ^ 2 :
      MvPolynomial (Fin (p + 6)) ℝ)).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]
  · have hinner : (MvPolynomial.X (cP p) - MvPolynomial.X (cX p) :
        MvPolynomial (Fin (p + 6)) ℝ).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨le_of_eq (MvPolynomial.totalDegree_X _), le_of_eq (MvPolynomial.totalDegree_X _)⟩
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    omega

theorem contLtx_mem (S : SOMin) (p : ℕ) (D : ℕ) :
    contLtx p ∈ S.Ω (p + 8) ((Polynomial.C 4).eval D) (p + 6) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 6) D
    (((MvPolynomial.X (cD p)) ^ 2 - (MvPolynomial.X (cP p) - MvPolynomial.X (cX p)) ^ 2 :
      MvPolynomial (Fin (p + 6)) ℝ))
  rw [contLtx_eq]
  refine Work.WilG1.Omega.mono h (by omega) ?_
  have htd := contLtxPoly_totalDegree p
  simp only [Polynomial.eval_C]
  omega

theorem contEpsPoly_totalDegree (p : ℕ) :
    (((MvPolynomial.X (cE p)) ^ 2 - (MvPolynomial.X (cSP p) - MvPolynomial.X (cS p)) ^ 2 :
      MvPolynomial (Fin (p + 6)) ℝ)).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]
  · have hinner : (MvPolynomial.X (cSP p) - MvPolynomial.X (cS p) :
        MvPolynomial (Fin (p + 6)) ℝ).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨le_of_eq (MvPolynomial.totalDegree_X _), le_of_eq (MvPolynomial.totalDegree_X _)⟩
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    omega

theorem contEps_mem (S : SOMin) (p : ℕ) (D : ℕ) :
    contEps p ∈ S.Ω (p + 8) ((Polynomial.C 4).eval D) (p + 6) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 6) D
    (((MvPolynomial.X (cE p)) ^ 2 - (MvPolynomial.X (cSP p) - MvPolynomial.X (cS p)) ^ 2 :
      MvPolynomial (Fin (p + 6)) ℝ))
  rw [contEps_eq]
  refine Work.WilG1.Omega.mono h (by omega) ?_
  have htd := contEpsPoly_totalDegree p
  simp only [Polynomial.eval_C]
  omega

/-- The matrix of the `ε`-`δ` formula for "the derivative is continuous at `z`", with the
quantifier-free body `|x' - x| < δ → ((z,s) ∈ Sset ∧ (z,x',s') ∈ Sset ∧ |s' - s| < ε)`. -/
def contM (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 6) → ℝ) :=
  (contLtx p)ᶜ ∪ (Work.WilG5.coordPre (iotaContA p) (derSet f) ∩
    Work.WilG5.coordPre (iotaContB p) (derSet f) ∩ contEps p)

/-- `∃ s'` (innermost). -/
def contN1 (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 5) → ℝ) := projLast (contM f)

/-- `∀ x'`. -/
def contN2 (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 4) → ℝ) :=
  (projLast ((contN1 f)ᶜ))ᶜ

/-- `∃ δ > 0`. -/
def contN3 (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 3) → ℝ) :=
  projLast (posHalf (p + 4) ⟨p + 3, by omega⟩ ∩ contN2 f)

/-- `∀ ε > 0`. -/
def contN4 (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 2) → ℝ) :=
  (projLast (posHalf (p + 3) ⟨p + 2, by omega⟩ ∩ (contN3 f)ᶜ))ᶜ

/-- `sliceDerivCont f`, written with the quantifier chain
`∃s ∀ε>0 ∃δ>0 ∀x' ∃s'` applied to `contM`. -/
def sliceDerivContAux (f : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1) → ℝ) :=
  projLast (contN4 f)

end Cont

/-! ## 6. The strip -/

/-- The strip `{z | 0 < z(last) < 1}`, written as an intersection of two half-spaces. -/
def stripAux (p : ℕ) : Set (Fin (p + 1) → ℝ) :=
  posHalf (p + 1) (Fin.last p) ∩ {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1}

theorem strip_eq (p : ℕ) : stripAux p = strip p := by
  ext z
  simp [stripAux, posHalf, strip, I, Set.mem_Ioo]

theorem strip_mem (S : SOMin) (p : ℕ) (D : ℕ) :
    strip p ∈ S.Ω (p + 4) ((Polynomial.C 6).eval D) (p + 1) := by
  have h1 : posHalf (p + 1) (Fin.last p) ∈ S.Ω (p + 3) ((Polynomial.C 3).eval D) (p + 1) := by
    simpa using posHalf_mem (S := S) (p + 1) (Fin.last p) D
  have h2 : {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1} ∈
      S.Ω (p + 3) ((Polynomial.C 3).eval D) (p + 1) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 1) D
      (1 - (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ))
    have htd : (1 - (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ)).totalDegree ≤ 1 := by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      exact ⟨by rw [MvPolynomial.totalDegree_one]; omega,
        by rw [MvPolynomial.totalDegree_X]⟩
    have hset : {x : Fin (p + 1) → ℝ |
        0 < MvPolynomial.eval x (1 - (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ))}
        = {z : Fin (p + 1) → ℝ | z (Fin.last p) < 1} := by
      have hval : ∀ x : Fin (p + 1) → ℝ,
          MvPolynomial.eval x (1 - (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ))
            = 1 - x (Fin.last p) := by
        intro x
        simp
      ext x
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hval x]
      constructor <;> intro h <;> linarith
    rw [hset] at h
    refine Work.WilG1.Omega.mono h le_rfl ?_
    simp only [Polynomial.eval_C]
    omega
  have h := Work.WilG1.Omega.inter₂ h1 h2
  rw [← strip_eq p]
  refine Work.WilG1.Omega.mono h (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  omega

end Work.WilG4a
