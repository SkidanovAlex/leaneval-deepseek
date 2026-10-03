import Mathlib
import Submission.Work.Peluse.UControl.sumRenameMulXInj
import Submission.Work.Peluse.UControl.eqSlotHistOfMemCubeSet
import Submission.Work.Peluse.UControl.levRoundHoldsV2

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

attribute [local instance] Classical.propDecidable

/-!
# The round of Peluse's Lemma 4.8 (`LevRound`)

This file holds the machinery of the round; the round itself,
`Work.Peluse.UControl.levRoundHolds`, is assembled in `levRoundHolds.lean` from a
`LevCube`-state of degree `D ≥ 2` one reaches, by PET steps, a `LevCube`-state of degree `D - 1`
whose atoms are `C D · (Σ_{s' ∈ P s} atoms_{s'}) · X_s`.

The steps of the round are of three kinds (see the docstring of `LevInv` in `levRoundDefs.lean`):

* *hydra* steps (`HistData.sel` has degree `< D`): the top-degree slots are untouched except that
  they gain the new `ε`-coordinate (with the `ε`-term `D • (β · a_new)`) and lose the reference's
  degree-`(D-1)` coefficient;
* *class-reduction* steps (`sel` has degree `D`, at least two classes alive): the class of `sel` dies
  and the surviving classes' leading coefficients are shifted by the killed class's value;
* the *closing* step (one class left): it turns the degree-`(D-1)` coefficients into the new
  leading coefficients.
-/

variable {d D L : ℕ}

/-! ## The injectivity of the atom sums on the subsets of `A` -/

lemma subSum_inj {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    (hind : LevIndep L A atoms) {ω ω' : Finset (Fin L)} (hω : ω ⊆ A) (hω' : ω' ⊆ A)
    (h : subSum A atoms ω = subSum A atoms ω') : ω = ω' := by
  have h1 : atomSum A atoms (histOf A (0 : Fin L → Bool) ω)
      = atomSum A atoms (histOf A (0 : Fin L → Bool) ω') := by
    rw [subSum_eq_atomSum A atoms ω, subSum_eq_atomSum A atoms ω', h]
  exact histOf_inj hω hω' (hind _ _ (histOf_mem_cube ω) (histOf_mem_cube ω') h1)

/-! ## The slot bookkeeping of one step -/

lemma step_Q {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (x : InitIdx d × (Fin (n + 1) → Bool)) :
    (X.step i₀ h₀ hh).Q x.1 x.2 = X.stepQ i₀ h₀ x.1 x.2 := rfl

lemma init_snoc_eq {n : ℕ} (p : Fin n → Bool) (b : Bool) :
    (Fin.init (Fin.snoc (α := fun _ => Bool) p b) : Fin n → Bool) = p := by
  ext i
  simp [Fin.init, Fin.snoc_castSucc]


lemma mem_stepH_iff {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (x : InitIdx d × (Fin (n + 1) → Bool)) :
    x ∈ X.stepH i₀ h₀ ↔
      (x.1, Fin.init x.2) ∈ X.H ∧ x ≠ (i₀, Fin.snoc h₀ false) ∧
        1 ≤ (X.stepQ i₀ h₀ x.1 x.2).natDegree := by
  simp [HistData.stepH]

lemma stepQ_eq {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (j : InitIdx d) (h' : Fin (n + 1) → Bool) :
    X.stepQ i₀ h₀ j h'
      = (((X.Q j (Fin.init h')).map (histRen n)).comp
          (Polynomial.X + Polynomial.C (stepShift h')))
        - (X.Q i₀ h₀).map (histRen n) := rfl

/-- **The child of a top-degree slot when the reference has smaller degree.** -/
lemma step_top_child {d n D : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (j : InitIdx d) (h' : Fin (n + 1) → Bool)
    (hpar : (X.Q j (Fin.init h')).natDegree = D) (href : (X.Q i₀ h₀).natDegree < D) :
    (X.stepQ i₀ h₀ j h').natDegree = D ∧
      (X.stepQ i₀ h₀ j h').leadingCoeff = histRen n ((X.Q j (Fin.init h')).leadingCoeff) := by
  set A := ((X.Q j (Fin.init h')).map (histRen n)).comp
    (Polynomial.X + Polynomial.C (stepShift h')) with hAdef
  set B := (X.Q i₀ h₀).map (histRen n) with hBdef
  have hA : A.natDegree = D := by
    rw [hAdef, histComp_natDegree, hpar]
  have hB : B.natDegree < D := by
    rw [hBdef, histMap_natDegree]; exact href
  have hlcA : A.leadingCoeff = histRen n ((X.Q j (Fin.init h')).leadingCoeff) := hAdef ▸
    histComp_leadingCoeff (X.Q j (Fin.init h')) (stepShift h')
  refine ⟨?_, ?_⟩
  · rw [stepQ_eq]
    exact (natDegree_sub_eq_of_lt (by rw [hA]; exact hB)).trans hA
  · rw [stepQ_eq]
    exact (leadingCoeff_sub_eq_of_lt (by rw [hA]; exact hB)).trans hlcA

/-- **The child of a top-degree slot of the same class as the reference dies** (its degree drops
below `D`). -/
lemma step_die_child {d n D : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (j : InitIdx d) (h' : Fin (n + 1) → Bool) (hD : 1 ≤ D)
    (hpar : (X.Q j (Fin.init h')).natDegree = D) (href : (X.Q i₀ h₀).natDegree = D)
    (hlc : (X.Q j (Fin.init h')).leadingCoeff = (X.Q i₀ h₀).leadingCoeff) :
    (X.stepQ i₀ h₀ j h').natDegree ≤ D - 1 := by
  have hA : (((X.Q j (Fin.init h')).map (histRen n)).comp
      (Polynomial.X + Polynomial.C (stepShift h'))).natDegree = D := by
    rw [histComp_natDegree, hpar]
  have hB : ((X.Q i₀ h₀).map (histRen n)).natDegree = D := by
    rw [histMap_natDegree, href]
  have hlcA : (((X.Q j (Fin.init h')).map (histRen n)).comp
      (Polynomial.X + Polynomial.C (stepShift h'))).leadingCoeff
      = histRen n ((X.Q i₀ h₀).leadingCoeff) := by
    rw [histComp_leadingCoeff, hlc]
  have hlcB : ((X.Q i₀ h₀).map (histRen n)).leadingCoeff
      = histRen n ((X.Q i₀ h₀).leadingCoeff) := histMap_leadingCoeff
  have hlt : ((((X.Q j (Fin.init h')).map (histRen n)).comp
      (Polynomial.X + Polynomial.C (stepShift h')))
      - (X.Q i₀ h₀).map (histRen n)).natDegree < D :=
    natDegree_sub_lt_of_lc_eq hA hB (by rw [hlcA, hlcB]) hD
  rw [stepQ_eq]
  omega

/-- **The `(D-1)`-coefficient of the child of a top-degree slot.** -/
lemma step_coeff_child {d n D : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (j : InitIdx d) (h' : Fin (n + 1) → Bool) (hpar : (X.Q j (Fin.init h')).natDegree = D) :
    (X.stepQ i₀ h₀ j h').coeff (D - 1)
      = histRen n ((X.Q j (Fin.init h')).coeff (D - 1))
        + D • (histRen n ((X.Q j (Fin.init h')).coeff D) * stepShift h')
        - histRen n ((X.Q i₀ h₀).coeff (D - 1)) := by
  rw [stepQ_eq, Polynomial.coeff_sub, Polynomial.coeff_map,
    histComp_coeff (X.Q j (Fin.init h')) (stepShift h') hpar]

/-- **The `(D-1)`-coefficient of the child of a top-degree slot, with the reference's contribution
folded into the parent's difference.**  This is the form used by the closing step of the round: the
difference `coeff (D-1) (Q_p) - coeff (D-1) (Q_{h₀})` of the parent and of the reference is the
class-`A` recursion of the invariant. -/
lemma step_coeff_child_sub {d n D : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (j : InitIdx d) (h' : Fin (n + 1) → Bool) (hpar : (X.Q j (Fin.init h')).natDegree = D) :
    (X.stepQ i₀ h₀ j h').coeff (D - 1)
      = histRen n ((X.Q j (Fin.init h')).coeff (D - 1) - (X.Q i₀ h₀).coeff (D - 1))
        + D • (histRen n ((X.Q j (Fin.init h')).coeff D) * stepShift h') := by
  rw [step_coeff_child X i₀ h₀ j h' hpar]
  have hsub : (histRen n) ((X.Q j (Fin.init h')).coeff (D - 1))
        - (histRen n) ((X.Q i₀ h₀).coeff (D - 1))
      = (histRen n) ((X.Q j (Fin.init h')).coeff (D - 1) - (X.Q i₀ h₀).coeff (D - 1)) := by
    rw [map_sub]
  rw [← hsub]
  ring

/-- **The difference of the `(D-1)`-coefficients of two children of the same slot.**  If the two
parents have the same degree `D` and the same `y^D`-coefficient, the reference's contribution
cancels. -/
lemma step_coeff_child_diff {d n D : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (j : InitIdx d) (h' h₀' : Fin (n + 1) → Bool) (hpar : (X.Q j (Fin.init h')).natDegree = D)
    (hpar₀ : (X.Q j (Fin.init h₀')).natDegree = D)
    (hc : (X.Q j (Fin.init h')).coeff D = (X.Q j (Fin.init h₀')).coeff D) :
    (X.stepQ i₀ h₀ j h').coeff (D - 1) - (X.stepQ i₀ h₀ j h₀').coeff (D - 1)
      = histRen n ((X.Q j (Fin.init h')).coeff (D - 1) - (X.Q j (Fin.init h₀')).coeff (D - 1))
        + D • (histRen n ((X.Q j (Fin.init h')).coeff D) * (stepShift h' - stepShift h₀')) := by
  rw [stepQ_eq, stepQ_eq]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map,
    histComp_coeff (X.Q j (Fin.init h')) (stepShift h') hpar,
    histComp_coeff (X.Q j (Fin.init h₀')) (stepShift h₀') hpar₀]
  rw [map_sub, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, hc]
  ring

/-- The difference of the `(D-1)`-coefficients of two children, phrased for `HistData.step`. -/
lemma step_coeff_child_diff' {d n D : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (j : InitIdx d) (h' h₀' : Fin (n + 1) → Bool)
    (hpar : (X.Q j (Fin.init h')).natDegree = D)
    (hpar₀ : (X.Q j (Fin.init h₀')).natDegree = D)
    (hc : (X.Q j (Fin.init h')).coeff D = (X.Q j (Fin.init h₀')).coeff D) :
    ((X.step i₀ h₀ hh).Q j h').coeff (D - 1) - ((X.step i₀ h₀ hh).Q j h₀').coeff (D - 1)
      = histRen n ((X.Q j (Fin.init h')).coeff (D - 1) - (X.Q j (Fin.init h₀')).coeff (D - 1))
        + D • (histRen n ((X.Q j (Fin.init h')).coeff D) * (stepShift h' - stepShift h₀')) := by
  rw [step_Q X i₀ h₀ hh (j, h'), step_Q X i₀ h₀ hh (j, h₀')]
  exact step_coeff_child_diff X i₀ h₀ j h' h₀' hpar hpar₀ hc

/-- The degree of a slot of the next state is at most the maximum of the degrees of its parent and
of the reference. -/
lemma stepQ_natDegree_le_max {d n : ℕ} (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (j : InitIdx d) (h' : Fin (n + 1) → Bool) :
    (X.stepQ i₀ h₀ j h').natDegree
      ≤ max ((X.Q j (Fin.init h')).natDegree) ((X.Q i₀ h₀).natDegree) := by
  have hcomp : (((X.Q j (Fin.init h')).map (histRen n)).comp
      (Polynomial.X + Polynomial.C (stepShift h'))).natDegree
      ≤ (X.Q j (Fin.init h')).natDegree := by
    refine le_trans Polynomial.natDegree_comp_le ?_
    rw [Polynomial.natDegree_X_add_C, mul_one, histMap_natDegree]
  have hmap2 : ((X.Q i₀ h₀).map (histRen n)).natDegree ≤ (X.Q i₀ h₀).natDegree := by
    rw [histMap_natDegree]
  rw [stepQ_eq]
  exact le_trans (Polynomial.natDegree_sub_le _ _)
    (max_le (hcomp.trans (le_max_left _ _)) (hmap2.trans (le_max_right _ _)))

/-! ## The renaming lemmas -/

/-- Renaming an atom sum into the next parameter ring. -/
lemma histRen_liftSub (A : Finset (Fin L)) (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ)
    (r : ℕ) (ω : Finset (Fin L)) :
    histRen (L + r) (liftSub A atoms r ω) = liftSub A atoms (r + 1) ω := by
  show (MvPolynomial.rename (Fin.castSucc : Fin (L + r) → Fin (L + r + 1)))
      (liftSub A atoms r ω) = liftSub A atoms (r + 1) ω
  rw [liftSub, liftSub, MvPolynomial.rename_rename]
  rfl

lemma histRen_X_natAdd {r : ℕ} (j : Fin r) :
    histRen (L + r) (MvPolynomial.X (Fin.natAdd L j))
      = MvPolynomial.X (Fin.natAdd L (Fin.castSucc j)) := by
  show (MvPolynomial.rename (Fin.castSucc : Fin (L + r) → Fin (L + r + 1)))
      (MvPolynomial.X (Fin.natAdd L j)) = MvPolynomial.X (Fin.natAdd L (Fin.castSucc j))
  rw [MvPolynomial.rename_X, ← Fin.natAdd_castSucc]

lemma stepShift_eq_X_mul {n : ℕ} (h' : Fin (n + 1) → Bool) :
    stepShift h' = MvPolynomial.X (Fin.last n)
      * (if h' (Fin.last n) then (1 : MvPolynomial (Fin (n + 1)) ℤ) else 0) := by
  rw [stepShift]
  by_cases h : h' (Fin.last n) <;> simp [h]



/-! ## Slot bookkeeping for the steps -/

/-! ## The hydra step -/

/-- **The `(D-1)`-coefficient recursion of the surviving class `A` in one step of the round**, in
the form used by both the hydra step and the class-reduction step: the difference of the
`(D-1)`-coefficients of the two children (of the class-`A` slots at the parameters `w` and `0`) is
the `histRen` of the parents' difference plus the `ε`-term `D • (λ · a_new)`, where
`λ = liftSub r A - liftSub r (σ (last r))` is the class-`A` value. -/
theorem levCoeffStep {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} {r : ℕ} {σ : Fin (r + 1) → Finset (Fin L)}
    {X : HistData d (L + r)} (i₀ : InitIdx d) (h₀ : Fin (L + r) → Bool)
    (hdeg : ∀ w : Fin r → Bool, (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r w)).natDegree = D)
    (hlead : ∀ w : Fin r → Bool, (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r w)).coeff D
      = liftSub A atoms r A - liftSub A atoms r (σ (Fin.last r)))
    (hcoef : ∀ w : Fin r → Bool,
      (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r w)).coeff (D - 1)
        - (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r 0)).coeff (D - 1)
      = ∑ j : Fin r, D • ((liftSub A atoms r A - liftSub A atoms r (σ (Fin.castSucc j)))
          * MvPolynomial.X (Fin.natAdd L j)
          * (if w j then (1 : MvPolynomial (Fin (L + r)) ℤ) else 0))) :
    ∀ w : Fin (r + 1) → Bool,
      (X.stepQ i₀ h₀ (Sum.inr 0) (slotHist (histOf A f₀ A) (r + 1) w)).coeff (D - 1)
        - (X.stepQ i₀ h₀ (Sum.inr 0) (slotHist (histOf A f₀ A) (r + 1) 0)).coeff (D - 1)
      = ∑ j : Fin (r + 1), D • ((liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j))
          * MvPolynomial.X (Fin.natAdd L j)
          * (if w j then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0)) := by
  intro w
  have hP : slotHist (histOf A f₀ A) (r + 1) w
      = Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init w)) (w (Fin.last r)) := by
    conv_lhs => rw [← Fin.snoc_init_self (q := w)]
    exact slotHist_snoc _ _ _
  have hQ0 : slotHist (histOf A f₀ A) (r + 1) (0 : Fin (r + 1) → Bool)
      = Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r 0) false := by
    have h0 : (0 : Fin (r + 1) → Bool) = Fin.snoc (α := fun _ => Bool) (0 : Fin r → Bool) false :=
      histSnocZeroFalse.symm
    rw [h0, slotHist_snoc]
  have hstep : stepShift (Fin.snoc (α := fun _ => Bool)
        (slotHist (histOf A f₀ A) r (Fin.init w)) (w (Fin.last r)))
      - stepShift (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r 0) false)
      = MvPolynomial.X (Fin.last (L + r))
        * (if w (Fin.last r) then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0) := by
    rw [stepShift_eq_X_mul, stepShift_eq_X_mul, Fin.snoc_last, Fin.snoc_last]
    simp
  have hpar₁ : (X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
      (slotHist (histOf A f₀ A) r (Fin.init w)) (w (Fin.last r))))).natDegree = D := by
    rw [Fin.init_snoc]; exact hdeg (Fin.init w)
  have hpar₀ : (X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
      (slotHist (histOf A f₀ A) r 0) false))).natDegree = D := by
    rw [Fin.init_snoc]; exact hdeg 0
  have hc : (X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
        (slotHist (histOf A f₀ A) r (Fin.init w)) (w (Fin.last r))))).coeff D
      = (X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
        (slotHist (histOf A f₀ A) r 0) false))).coeff D := by
    rw [Fin.init_snoc, Fin.init_snoc, hlead (Fin.init w), hlead 0]
  rw [hP, hQ0]
  have hkey := step_coeff_child_diff (D := D) X i₀ h₀ (Sum.inr 0)
    (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init w)) (w (Fin.last r)))
    (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r 0) false)
    hpar₁ hpar₀ hc
  have hite : ∀ (b : Bool), histRen (L + r) (if b then (1 : MvPolynomial (Fin (L + r)) ℤ) else 0)
      = (if b then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0) := fun b => by cases b <;> simp
  rw [hkey, Fin.init_snoc, Fin.init_snoc, hcoef (Fin.init w), hlead (Fin.init w)]
  simp only [map_sub, map_sum, map_mul, map_nsmul, histRen_liftSub, histRen_X_natAdd,
    stepShift_eq_X_mul, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.natAdd_castSucc, Fin.natAdd_last,
    mul_assoc, sub_zero, mul_zero, Bool.false_eq_true, if_false]
  rw [add_right_cancel_iff]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hite ((Fin.init w) x)]
  rfl

/-- **The hydra step of the round.**  If the deterministic selection has degree `< D` (so it is not
a top-degree slot), the invariant is maintained: the classes and the shift are unchanged, the
top-degree slots gain the new `ε`-coordinate, and the degree-`(D-1)` coefficient recursion holds. -/
theorem levInv_step_hydra {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} {r : ℕ}
    {K : Finset (Finset (Fin L))} {σ : Fin (r + 1) → Finset (Fin L)}
    {X : HistData d (L + r)} (hinv : LevInv d D A f₀ atoms r K σ X)
    (hne : X.H.Nonempty) (hlt : (X.Q (X.sel hne).1 (X.sel hne).2).natDegree < D) :
    LevInv d D A f₀ atoms (r + 1) K (Fin.snoc σ (σ (Fin.last r)))
      (X.step (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne)) := by
  obtain ⟨hsub, hneK, hmA, hsz, hss, hsn, hdeg, htop, honly, hcoef⟩ := hinv
  have hmem0 : ((X.sel hne).1, (X.sel hne).2) ∈ X.H := X.sel_mem_H hne
  have hdeg0 : (X.Q (X.sel hne).1 (X.sel hne).2).natDegree < D := hlt
  have hcoeff_eq : ∀ u : Fin (r + 1) → Bool,
      (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r (Fin.init u))).coeff D
        = (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r (Fin.init u))).leadingCoeff := by
    intro u
    rw [← (htop A hmA (Fin.init u)).2.1]
    exact Polynomial.coeff_natDegree
  have hlast : (Fin.snoc σ (σ (Fin.last r)) : Fin (r + 2) → Finset (Fin L)) (Fin.last (r + 1))
      = σ (Fin.last r) := Fin.snoc_last ..
  refine ⟨hsub, hneK, hmA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin (r + 2)) = Fin.castSucc (0 : Fin (r + 1)) from Fin.ext rfl,
      Fin.snoc_castSucc]
    exact hsz
  · intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact hss k
    · rw [Fin.snoc_last]; exact hss (Fin.last r)
  · intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]; exact hsn k
    · rw [Fin.snoc_last]; exact hsn (Fin.last r)
  · intro x hx
    have hx' : x ∈ X.stepH (X.sel hne).1 (X.sel hne).2 := hx
    rw [mem_stepH_iff X (X.sel hne).1 (X.sel hne).2 x] at hx'
    obtain ⟨hxH, -, -⟩ := hx'
    change (X.stepQ (X.sel hne).1 (X.sel hne).2 x.1 x.2).natDegree ≤ D
    refine le_trans (stepQ_natDegree_le_max X (X.sel hne).1 (X.sel hne).2 x.1 x.2) (max_le ?_ ?_)
    · exact hdeg _ hxH
    · exact le_of_lt hdeg0
  · intro ω hω w'
    obtain ⟨hmemP, hdegP, hleadP⟩ := htop ω hω (Fin.init w')
    have hchild : slotHist (histOf A f₀ ω) (r + 1) w'
        = Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w'))
          (w' (Fin.last r)) := by
      conv_lhs => rw [← Fin.snoc_init_self (q := w')]
      exact slotHist_snoc _ _ _
    rw [hchild]
    have hinit : (Fin.init (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w'))
        (w' (Fin.last r))) : Fin (L + r) → Bool) = slotHist (histOf A f₀ ω) r (Fin.init w') :=
      init_snoc_eq _ _
    have hpar : (X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
        (slotHist (histOf A f₀ ω) r (Fin.init w')) (w' (Fin.last r))))).natDegree = D := by
      rw [hinit]; exact hdegP
    obtain ⟨hdegC, hleadC⟩ := step_top_child X (X.sel hne).1 (X.sel hne).2 (Sum.inr 0)
      (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w')) (w' (Fin.last r)))
      hpar hdeg0
    have hmemC : ((Sum.inr 0 : InitIdx d),
        Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w')) (w' (Fin.last r)))
        ∈ X.stepH (X.sel hne).1 (X.sel hne).2 := by
      rw [mem_stepH_iff X (X.sel hne).1 (X.sel hne).2 _]
      rw [hinit]
      refine ⟨hmemP, ?_, ?_⟩
      · intro heq
        have h1 : (Sum.inr 0 : InitIdx d) = (X.sel hne).1 := (Prod.ext_iff.mp heq).1
        have h2 : slotHist (histOf A f₀ ω) r (Fin.init w') = (X.sel hne).2 := by
          have h3 : (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w'))
              (w' (Fin.last r)) : Fin (L + r + 1) → Bool)
              = Fin.snoc (α := fun _ => Bool) ((X.sel hne).2) false := by
            simpa using congrArg Prod.snd heq
          exact (Fin.snoc_inj.mp h3).1
        have hdegsel : (X.Q (X.sel hne).1 (X.sel hne).2).natDegree = D := by
          rw [← h1, ← h2]; exact hdegP
        omega
      · rw [hdegC]; omega
    refine ⟨?_, ?_, ?_⟩
    · exact hmemC
    · rw [step_Q X (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne) (Sum.inr 0,
        Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w')) (w' (Fin.last r)))]
      exact hdegC
    · rw [step_Q X (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne) (Sum.inr 0,
        Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ ω) r (Fin.init w')) (w' (Fin.last r)))]
      rw [hleadC, hinit, hleadP, map_sub, histRen_liftSub, histRen_liftSub, hlast]
  · intro x hx hxdeg
    have hx' : x ∈ X.stepH (X.sel hne).1 (X.sel hne).2 := hx
    rw [mem_stepH_iff X (X.sel hne).1 (X.sel hne).2 x] at hx'
    obtain ⟨hxH, hxne, -⟩ := hx'
    obtain ⟨x1, x2⟩ := x
    simp only at hxH hxne hxdeg
    have hxdeg' : D ≤ (X.stepQ (X.sel hne).1 (X.sel hne).2 x1 x2).natDegree := hxdeg
    have hxpar : (X.Q x1 (Fin.init x2)).natDegree = D := by
      have hle := stepQ_natDegree_le_max X (X.sel hne).1 (X.sel hne).2 x1 x2
      have h2 : max ((X.Q x1 (Fin.init x2)).natDegree) ((X.Q (X.sel hne).1 (X.sel hne).2).natDegree)
          = D := le_antisymm (max_le (hdeg _ hxH) (le_of_lt hdeg0)) (hxdeg'.trans hle)
      omega
    obtain ⟨hx1, ω, hω, w, hxw⟩ := honly (x1, Fin.init x2) hxH (le_of_eq hxpar.symm)
    refine ⟨hx1, ω, hω, Fin.snoc w (x2 (Fin.last (L + r))), ?_⟩
    change x2 = slotHist (histOf A f₀ ω) (r + 1) (Fin.snoc w (x2 (Fin.last (L + r))))
    conv_lhs => rw [← Fin.snoc_init_self (q := x2)]
    rw [show (Fin.init x2 : Fin (L + r) → Bool) = slotHist (histOf A f₀ ω) r w from hxw,
      ← slotHist_snoc]
    rfl
  · -- The degree-`(D-1)` recursion of the survivor: the stand-alone coefficient lemma
    -- `levCoeffStep`, applied with the parents of the two children, followed by the observation
    -- that `(Fin.snoc σ ..) (Fin.castSucc j) = σ j`.
    have hdegA : ∀ u : Fin r → Bool,
        (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r u)).natDegree = D :=
      fun u => (htop A hmA u).2.1
    have hleadA : ∀ u : Fin r → Bool, (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r u)).coeff D
        = liftSub A atoms r A - liftSub A atoms r (σ (Fin.last r)) := fun u => by
      rw [← (htop A hmA u).2.1, Polynomial.coeff_natDegree]
      exact (htop A hmA u).2.2
    intro w'
    rw [step_Q X (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne)
          (Sum.inr 0, slotHist (histOf A f₀ A) (r + 1) w'),
        step_Q X (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne)
          (Sum.inr 0, slotHist (histOf A f₀ A) (r + 1) 0)]
    rw [levCoeffStep (D := D) (X := X) (X.sel hne).1 (X.sel hne).2 hdegA hleadA hcoef w']
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fin.snoc_castSucc]

/-- One PET step at any slot of minimal degree strictly decreases the weight vector. -/
theorem HistData.weightH_step_lt_of_minDegree {d n : ℕ} (X : HistData d n) (hne : X.H.Nonempty)
    (i₀ : InitIdx d) (h₀ : Fin n → Bool) (hh : (i₀, h₀) ∈ X.H)
    (hmin : (X.Q i₀ h₀).natDegree = X.minDeg hne) :
    PetStep.petLt ((X.step i₀ h₀ hh).weightH) X.weightH := by
  classical
  have hW0 : X.weightH ⟨0, Nat.succ_pos d⟩ = 0 := X.weightH_zero_coord
  have hkey : PetStep.petLt
      (((X.toSym).S.step (⟨(i₀, h₀), hh⟩ : (X.toSym).S.ι)).weight d) ((X.toSym).S.weight d) := by
    refine petSymWeight (X.toSym).S (⟨(i₀, h₀), hh⟩ : (X.toSym).S.ι) (d := d)
      (d' := X.minDeg hne) ?_ ?_ ?_ ?_
    · intro i; exact X.hnc i.1 i.2
    · intro i; exact X.hd i.1 i.2
    · intro i _; exact X.minDeg_le hne i.1 i.2
    · show ((X.toSym).S.P (⟨(i₀, h₀), hh⟩ : (X.toSym).S.ι)).natDegree = X.minDeg hne
      exact hmin
  obtain ⟨j₀, hj₀, hjm⟩ := hkey
  have hj0pos : 1 ≤ (j₀ : ℕ) := by
    by_contra hcon
    have h0 : (j₀ : ℕ) = 0 := by omega
    have hj0 : j₀ = ⟨0, Nat.succ_pos d⟩ := Fin.ext h0
    have h1 : (X.toSym).S.weight d j₀ = 0 := by rw [hj0]; exact hW0
    rw [h1] at hj₀
    omega
  refine ⟨j₀, ?_, ?_⟩
  · rw [histWeightStepEq X i₀ h₀ hh j₀ hj0pos]; exact hj₀
  · intro m hm
    rw [histWeightStepEq X i₀ h₀ hh m (by omega)]; exact hjm m hm

/-- The state of one round of the level chain. -/
structure RState (d D L : ℕ) (A : Finset (Fin L)) (f₀ : Fin L → Bool)
    (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ) where
  r : ℕ
  X : HistData d (L + r)
  K : Finset (Finset (Fin L))
  σ : Fin (r + 1) → Finset (Fin L)
  inv : LevInv d D A f₀ atoms r K σ X

namespace RState

variable {A : Finset (Fin L)} {f₀ : Fin L → Bool}
variable {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}

/-- The live set of a round state is nonempty. -/
def hne (S : RState d D L A f₀ atoms) : S.X.H.Nonempty :=
  ⟨((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ A) S.r 0),
    (S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).1⟩

/-- The weight relation of the round recursion. -/
def rel (S T : RState d D L A f₀ atoms) : Prop := PetStep.petLt S.X.weightH T.X.weightH

lemma rel_wf : WellFounded (rel (d := d) (D := D) (L := L) (A := A) (f₀ := f₀)
    (atoms := atoms)) :=
  InvImage.wf (fun S : RState d D L A f₀ atoms => S.X.weightH) (petChainWF d)

/-- The hydra step of the round: step at the selection, keeping the classes and the shift. -/
def hydraStep (S : RState d D L A f₀ atoms)
    (hlt : (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree < D) :
    RState d D L A f₀ atoms where
  r := S.r + 1
  X := S.X.step (S.X.sel S.hne).1 (S.X.sel S.hne).2 (S.X.sel_mem_H S.hne)
  K := S.K
  σ := Fin.snoc S.σ (S.σ (Fin.last S.r))
  inv := levInv_step_hydra S.inv S.hne hlt

/-- The class-reduction step of the round. -/
def killStep (S : RState d D L A f₀ atoms) (ω₀ : Finset (Fin L)) (hω : ω₀ ∈ S.K)
    (hωA : ω₀ ≠ A)
    (hinv : LevInv d D A f₀ atoms (S.r + 1) (S.K.erase ω₀) (Fin.snoc S.σ ω₀)
      (S.X.step (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)
        ((S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).1))) : RState d D L A f₀ atoms where
  r := S.r + 1
  X := S.X.step (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)
    ((S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).1)
  K := S.K.erase ω₀
  σ := Fin.snoc S.σ ω₀
  inv := hinv

end RState

lemma hydraStep_rel {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} (S : RState d D L A f₀ atoms)
    (hlt : (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree < D) :
    RState.rel (RState.hydraStep S hlt) S := by
  change PetStep.petLt ((S.X.step (S.X.sel S.hne).1 (S.X.sel S.hne).2
    (S.X.sel_mem_H S.hne)).weightH) S.X.weightH
  exact HistData.weightH_step_sel_lt S.X S.hne

lemma killStep_rel {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} (S : RState d D L A f₀ atoms)
    (ω₀ : Finset (Fin L)) (hω : ω₀ ∈ S.K) (hωA : ω₀ ≠ A)
    (hinv : LevInv d D A f₀ atoms (S.r + 1) (S.K.erase ω₀) (Fin.snoc S.σ ω₀)
      (S.X.step (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)
        ((S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).1)))
    (hkilldeg : (S.X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)).natDegree
      = S.X.minDeg S.hne) :
    RState.rel (RState.killStep S ω₀ hω hωA hinv) S := by
  change PetStep.petLt ((S.X.step (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)
    ((S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).1)).weightH) S.X.weightH
  exact S.X.weightH_step_lt_of_minDegree S.hne (Sum.inr 0)
    (slotHist (histOf A f₀ ω₀) S.r 0) ((S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).1) hkilldeg

/-- Composition of two `Reach`-chains. -/
lemma Reach.trans {d : ℕ} {L₁ L₃ : ℕ} {X : HistData d L₁} {Z : HistData d L₃} :
    ∀ {L₂ : ℕ} {Y : HistData d L₂}, Reach X Y → Reach Y Z → Reach X Z := by
  intro L₂ Y h1
  induction h1 with
  | refl => intro h2; exact h2
  | step X i₀ h₀ hh _ ih => intro h2; exact Reach.step X i₀ h₀ hh (ih h2)

/-- **The round process**: stepping at the selection while some slot has degree `< D` (hydra
phase), then at a representative of a class `≠ A` (class reduction), reaches a state all of whose
slots have degree `D` and with the single class `{A}`. -/
theorem loop_spec {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} (hind : LevIndep L A atoms)
    (hkill : ∀ {r : ℕ} {K : Finset (Finset (Fin L))} {σ : Fin (r + 1) → Finset (Fin L)}
      {X : HistData d (L + r)} (hinv : LevInv d D A f₀ atoms r K σ X)
      (halldeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D)
      {ω₀ : Finset (Fin L)} (hω : ω₀ ∈ K) (hωA : ω₀ ≠ A),
      LevInv d D A f₀ atoms (r + 1) (K.erase ω₀) (Fin.snoc σ ω₀)
        (X.step (Sum.inr 0) (slotHist (histOf A f₀ ω₀) r 0)
          ((hinv.top_mem ω₀ hω (0 : Fin r → Bool)).1)))
    (S : RState d D L A f₀ atoms) :
    ∃ S' : RState d D L A f₀ atoms, Reach S.X S'.X ∧
      (∀ x ∈ S'.X.H, (S'.X.Q x.1 x.2).natDegree = D) ∧ S'.K = {A} := by
  induction S using WellFounded.induction (RState.rel_wf (d := d) (D := D) (L := L) (A := A)
    (f₀ := f₀) (atoms := atoms)) with
  | h S ih =>
    by_cases hlt : (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree < D
    · -- hydra step
      obtain ⟨S', hreach, hdeg, hK⟩ := ih (RState.hydraStep S hlt) (hydraStep_rel S hlt)
      exact ⟨S', Reach.step S.X (S.X.sel S.hne).1 (S.X.sel S.hne).2 (S.X.sel_mem_H S.hne) hreach, hdeg, hK⟩
    · by_cases hKA : S.K = {A}
      · -- closing-ready state
        have hmin : S.X.minDeg S.hne = D := by
          refine le_antisymm ?_ ?_
          · calc S.X.minDeg S.hne
                ≤ (S.X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) S.r 0)).natDegree :=
                  S.X.minDeg_le S.hne _ ((S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).1)
              _ = D := (S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).2.1
          · calc S.X.minDeg S.hne
                = (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree := (S.X.sel_degree S.hne).symm
              _ ≥ D := not_lt.mp hlt
        have halldeg : ∀ x ∈ S.X.H, (S.X.Q x.1 x.2).natDegree = D := by
          intro x hx
          refine le_antisymm (S.inv.degLe x hx) ?_
          calc D = S.X.minDeg S.hne := hmin.symm
            _ ≤ (S.X.Q x.1 x.2).natDegree := S.X.minDeg_le S.hne x hx
        exact ⟨S, Reach.refl S.X, halldeg, hKA⟩
      · -- class reduction
        obtain ⟨ω₀, hω, hωA⟩ : ∃ ω₀ ∈ S.K, ω₀ ≠ A := by
          by_contra hcon
          push_neg at hcon
          apply hKA
          refine Finset.Subset.antisymm ?_ ?_
          · intro ω hω
            simp only [Finset.mem_singleton]
            exact hcon ω hω
          · intro ω hω
            rw [Finset.mem_singleton] at hω
            rw [hω]
            exact S.inv.memA
        have hmin : S.X.minDeg S.hne = D := by
          refine le_antisymm ?_ ?_
          · calc S.X.minDeg S.hne
                ≤ (S.X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) S.r 0)).natDegree :=
                  S.X.minDeg_le S.hne _ ((S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).1)
              _ = D := (S.inv.top_mem A S.inv.memA (0 : Fin S.r → Bool)).2.1
          · calc S.X.minDeg S.hne
                = (S.X.Q (S.X.sel S.hne).1 (S.X.sel S.hne).2).natDegree := (S.X.sel_degree S.hne).symm
              _ ≥ D := not_lt.mp hlt
        have halldeg : ∀ x ∈ S.X.H, (S.X.Q x.1 x.2).natDegree = D := by
          intro x hx
          refine le_antisymm (S.inv.degLe x hx) ?_
          calc D = S.X.minDeg S.hne := hmin.symm
            _ ≤ (S.X.Q x.1 x.2).natDegree := S.X.minDeg_le S.hne x hx
        have hkilldeg : (S.X.Q (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)).natDegree
            = S.X.minDeg S.hne := by
          rw [hmin]
          exact (S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).2.1
        obtain ⟨S', hreach, hdeg, hK⟩ := ih
          (RState.killStep S ω₀ hω hωA (hkill S.inv halldeg hω hωA))
          (killStep_rel S ω₀ hω hωA (hkill S.inv halldeg hω hωA) hkilldeg)
        exact ⟨S', Reach.step S.X (Sum.inr 0) (slotHist (histOf A f₀ ω₀) S.r 0)
          ((S.inv.top_mem ω₀ hω (0 : Fin S.r → Bool)).1) hreach, hdeg, hK⟩

/-- The fresh coordinates of a round: the last `r` of the `L + r` coordinates. -/
def freshFin (L r : ℕ) : Finset (Fin (L + r)) :=
  Finset.univ.filter (fun i : Fin (L + r) => L ≤ i.1)

/-- The index (among the `r` fresh coordinates) of a fresh coordinate. -/
def freshIdx {L r : ℕ} (s : {s : Fin (L + r) // s ∈ freshFin L r}) : Fin r :=
  ⟨s.1.1 - L, by
    have h1 : L ≤ s.1.1 := (Finset.mem_filter.mp s.2).2
    have h2 : s.1.1 < L + r := s.1.2
    omega⟩

lemma natAdd_freshIdx {L r : ℕ} (s : {s : Fin (L + r) // s ∈ freshFin L r}) :
    Fin.natAdd L (freshIdx s) = s.1 := by
  refine Fin.ext ?_
  have h1 : L ≤ s.1.1 := (Finset.mem_filter.mp s.2).2
  have h2 : s.1.1 < L + r := s.1.2
  simp only [freshIdx, Fin.val_natAdd, Fin.val_mk]
  omega

lemma mem_freshFin {L r : ℕ} {i : Fin (L + r)} : i ∈ freshFin L r ↔ L ≤ i.1 := by
  simp [freshFin]

lemma freshIdx_natAdd {L r : ℕ} (j : Fin r) :
    freshIdx (L := L) (r := r) ⟨Fin.natAdd L j, by rw [mem_freshFin]; exact Nat.le_add_right L j.1⟩ = j := by
  refine Fin.ext ?_
  simp only [freshIdx, Fin.val_natAdd, Fin.val_mk]
  omega

/-- The class attached to a fresh coordinate: the killed class `σ j` removed from `A`. -/
def freshSet {L : ℕ} {r : ℕ} (A : Finset (Fin L)) (σ : Fin (r + 1) → Finset (Fin L))
    (s : {s : Fin (L + (r + 1)) // s ∈ freshFin L (r + 1)}) : Finset {s' // s' ∈ A} :=
  (A \ σ (freshIdx s)).attach.image (fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).1⟩)

/-- The atoms produced by the closing step of a round. -/
def closingAtoms {L : ℕ} (A : Finset (Fin L)) (atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ)
    (D r : ℕ) (σ : Fin (r + 1) → Finset (Fin L)) :
    {s // s ∈ freshFin L (r + 1)} → MvPolynomial (Fin (L + (r + 1))) ℤ :=
  fun s => MvPolynomial.C (D : ℤ) *
    ((∑ s' ∈ freshSet A σ s,
        MvPolynomial.rename (Fin.castLE (Nat.le_add_right L (r + 1))) (atoms s'))
      * MvPolynomial.X s.1)

lemma liftSub_eq_iff {A : Finset (Fin L)} {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}
    {r : ℕ} {ω ω' : Finset (Fin L)} (h : liftSub A atoms r ω = liftSub A atoms r ω') :
    subSum A atoms ω = subSum A atoms ω' :=
  MvPolynomial.rename_injective (Fin.castLE (Nat.le_add_right L r))
    (Fin.castLE_injective (Nat.le_add_right L r)) h

lemma ite_zero_mul {α : Type*} [MulZeroOneClass α] (c : Prop) [Decidable c] (a : α) :
    (if c then a else 0) = a * (if c then 1 else 0) := by
  split_ifs <;> simp

theorem levClosingCoeff {A : Finset (Fin L)} {f₀ : Fin L → Bool}
    {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ} {r : ℕ}
    {K : Finset (Finset (Fin L))} {σ : Fin (r + 1) → Finset (Fin L)}
    {X : HistData d (L + r)} (hinv : LevInv d D A f₀ atoms r K σ X)
    (hind : LevIndep L A atoms) (hD : 2 ≤ D)
    (halldeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D)
    (hK : K = {A}) :
    ∀ u : Fin (r + 1) → Bool, u ≠ 0 →
      (X.stepQ (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
          (slotHist (histOf A f₀ A) (r + 1) u)).natDegree = D - 1
      ∧ (X.stepQ (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
          (slotHist (histOf A f₀ A) (r + 1) u)).leadingCoeff
        = ∑ j : Fin (r + 1), D • ((liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j))
            * MvPolynomial.X (Fin.natAdd L j)
            * (if u j then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0)) := by
  obtain ⟨hsub, hneK, hmA, hsz, hss, hsn, hdeg, htop, honly, hcoef⟩ := hinv
  have hD1 : 1 ≤ D := by omega
  -- the class-`A` data of a parent
  have hdegA : ∀ w : Fin r → Bool, (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r w)).natDegree = D :=
    fun w => (htop A hmA w).2.1
  have hcoeffA : ∀ w : Fin r → Bool, (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r w)).coeff D
      = liftSub A atoms r A - liftSub A atoms r (σ (Fin.last r)) := fun w => by
    rw [← hdegA w, Polynomial.coeff_natDegree]
    exact (htop A hmA w).2.2
  have hleadA : ∀ w : Fin r → Bool, (X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r w)).leadingCoeff
      = liftSub A atoms r A - liftSub A atoms r (σ (Fin.last r)) := fun w => by
    rw [Polynomial.leadingCoeff, hdegA w]
    exact hcoeffA w
  -- the class values are nonzero differences
  have hdiff : ∀ j : Fin (r + 1),
      liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j)
        = liftSub A atoms (r + 1) (A \ σ j) := by
    intro j
    rw [liftSub, liftSub, liftSub, ← map_sub, subSum_sub (hss j)]
  have hne0 : ∀ j : Fin (r + 1), liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j) ≠ 0 := by
    intro j hzero
    rw [hdiff j] at hzero
    have hz' : liftSub A atoms (r + 1) (A \ σ j) = liftSub A atoms (r + 1) (∅ : Finset (Fin L)) := by
      rw [hzero]; simp [liftSub, subSum]
    have h2 : subSum A atoms (A \ σ j) = subSum A atoms (∅ : Finset (Fin L)) := liftSub_eq_iff hz'
    have h3 : A \ σ j = ∅ :=
      subSum_inj hind (Finset.sdiff_subset) (Finset.empty_subset A) h2
    have hsubA : A ⊆ σ j := by
      intro i hi
      by_contra hcon
      have hmem : i ∈ A \ σ j := Finset.mem_sdiff.mpr ⟨hi, hcon⟩
      rw [h3] at hmem
      exact Finset.notMem_empty i hmem
    exact hsn j (Finset.Subset.antisymm (hss j) hsubA)
  intro u hu
  have hsnoc : slotHist (histOf A f₀ A) (r + 1) u
      = Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r)) := by
    conv_lhs => rw [← Fin.snoc_init_self (q := u)]
    exact slotHist_snoc _ _ _
  have hparent : (X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
      (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r))))).natDegree = D := by
    rw [Fin.init_snoc]; exact hdegA (Fin.init u)
  -- Part 1: the coefficient formula
  have hcoefchild : (X.stepQ (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
        (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r)))).coeff (D - 1)
      = ∑ j : Fin (r + 1), D • ((liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j))
          * MvPolynomial.X (Fin.natAdd L j)
          * (if u j then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0)) := by
    rw [step_coeff_child_sub X (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
      (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r))) hparent]
    rw [Fin.init_snoc, hcoef (Fin.init u), hcoeffA (Fin.init u)]
    have hite : ∀ (b : Bool), histRen (L + r) (if b then (1 : MvPolynomial (Fin (L + r)) ℤ) else 0)
        = (if b then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0) := fun b => by cases b <;> simp
    simp only [map_sub, map_sum, map_mul, map_nsmul, histRen_liftSub, histRen_X_natAdd,
      stepShift_eq_X_mul, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.natAdd_castSucc, Fin.natAdd_last,
      mul_assoc, sub_zero, mul_zero, Bool.false_eq_true, if_false]
    rw [add_right_cancel_iff]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hite ((Fin.init u) j)]
    rfl
  -- Part 2: the degree drop
  have hdie : (X.stepQ (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
      (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r)))).natDegree ≤ D - 1 := by
    have h1 : (((X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
        (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r))))).map (histRen (L + r))).comp
        (Polynomial.X + Polynomial.C (stepShift (Fin.snoc (α := fun _ => Bool)
          (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r)))))).natDegree = D := by
      rw [histComp_natDegree, hparent]
    have h2 : ((X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r 0)).map (histRen (L + r))).natDegree = D := by
      rw [histMap_natDegree, hdegA 0]
    have h3 : (((X.Q (Sum.inr 0) (Fin.init (Fin.snoc (α := fun _ => Bool)
        (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r))))).map (histRen (L + r))).comp
        (Polynomial.X + Polynomial.C (stepShift (Fin.snoc (α := fun _ => Bool)
          (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r)))))).leadingCoeff
        = ((X.Q (Sum.inr 0) (slotHist (histOf A f₀ A) r 0)).map (histRen (L + r))).leadingCoeff := by
      rw [histComp_leadingCoeff, histMap_leadingCoeff, Fin.init_snoc, hleadA (Fin.init u), hleadA 0]
    have hlt := natDegree_sub_lt_of_lc_eq h1 h2 h3 hD1
    change (X.stepQ (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
      (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r)))).natDegree ≤ D - 1
    rw [stepQ_eq]
    omega
  -- Part 3: nonzero-ness
  have hsumne : (∑ j : Fin (r + 1), D • ((liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j))
        * MvPolynomial.X (Fin.natAdd L j)
        * (if u j then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0))) ≠ 0 := by
    intro hzero
    -- rewrite the sum into the shape of `sumRenameMulXInj`
    have hconv : (∑ j : Fin (r + 1), D • ((liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j))
          * MvPolynomial.X (Fin.natAdd L j)
          * (if u j then (1 : MvPolynomial (Fin (L + r + 1)) ℤ) else 0)))
        = (fun w : Fin (r + 1) → Bool => ∑ j : Fin (r + 1), if w j then
            MvPolynomial.rename (Fin.castAdd (r + 1)) (MvPolynomial.C (D : ℤ) * subSum A atoms (A \ σ j))
              * MvPolynomial.X (Fin.natAdd L j) else 0) u := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have h1 : liftSub A atoms (r + 1) (A \ σ j)
          = MvPolynomial.rename (Fin.castAdd (r + 1)) (subSum A atoms (A \ σ j)) := by
        rw [liftSub]
        rfl
      rw [hdiff j, h1, nsmul_eq_mul, map_mul, MvPolynomial.rename_C, mvC_natCast]
      split_ifs <;> ring
    rw [hconv] at hzero
    have hc_ne : ∀ j : Fin (r + 1), MvPolynomial.C (D : ℤ) * subSum A atoms (A \ σ j) ≠ 0 := by
      intro j
      refine mul_ne_zero (MvPolynomial.C_ne_zero.mpr (by omega)) ?_
      intro hz
      have h2 : subSum A atoms (A \ σ j) = subSum A atoms (∅ : Finset (Fin L)) := by
        rw [hz]; simp [subSum]
      have h3 : A \ σ j = ∅ :=
        subSum_inj hind (Finset.sdiff_subset) (Finset.empty_subset A) h2
      have hsubA : A ⊆ σ j := by
        intro i hi
        by_contra hcon
        have hmem : i ∈ A \ σ j := Finset.mem_sdiff.mpr ⟨hi, hcon⟩
        rw [h3] at hmem
        exact Finset.notMem_empty i hmem
      exact hsn j (Finset.Subset.antisymm (hss j) hsubA)
    have hinj := sumRenameMulXInj (R := ℤ) (L := L) (N := r + 1)
      (c := fun j => MvPolynomial.C (D : ℤ) * subSum A atoms (A \ σ j)) hc_ne
    have h0val : (fun w : Fin (r + 1) → Bool => ∑ j : Fin (r + 1), if w j then
        MvPolynomial.rename (Fin.castAdd (r + 1)) (MvPolynomial.C (D : ℤ) * subSum A atoms (A \ σ j))
          * MvPolynomial.X (Fin.natAdd L j) else 0) (0 : Fin (r + 1) → Bool) = 0 := by simp
    have hfu : (fun w : Fin (r + 1) → Bool => ∑ j : Fin (r + 1), if w j then
        MvPolynomial.rename (Fin.castAdd (r + 1)) (MvPolynomial.C (D : ℤ) * subSum A atoms (A \ σ j))
          * MvPolynomial.X (Fin.natAdd L j) else 0) u
        = (fun w : Fin (r + 1) → Bool => ∑ j : Fin (r + 1), if w j then
        MvPolynomial.rename (Fin.castAdd (r + 1)) (MvPolynomial.C (D : ℤ) * subSum A atoms (A \ σ j))
          * MvPolynomial.X (Fin.natAdd L j) else 0) (0 : Fin (r + 1) → Bool) := by
      rw [hzero, h0val]
    exact hu (hinj hfu)
  have hdegC : (X.stepQ (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) (Sum.inr 0)
      (Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r)))).natDegree = D - 1 := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdie ?_
    rw [hcoefchild]
    exact hsumne
  refine ⟨?_, ?_⟩
  · rw [hsnoc]
    exact hdegC
  · rw [Polynomial.leadingCoeff, hsnoc, hdegC, ← hcoefchild]

variable {L : ℕ} {A : Finset (Fin L)} {f₀ : Fin L → Bool}
variable {atoms : {s // s ∈ A} → MvPolynomial (Fin L) ℤ}

lemma subSum_eq_sum_attach {ω : Finset (Fin L)} (hω : ω ⊆ A) :
    subSum A atoms ω = ∑ x ∈ ω.attach, atoms ⟨x.1, hω x.2⟩ := by
  rw [subSum, ← Finset.sum_filter]
  refine Finset.sum_bij'
    (i := fun (a : {s // s ∈ A}) (ha : a ∈ Finset.univ.filter fun a => a.1 ∈ ω) =>
      (⟨a.1, (Finset.mem_filter.mp ha).2⟩ : {x // x ∈ ω}))
    (j := fun (b : {x // x ∈ ω}) (_ : b ∈ ω.attach) => (⟨b.1, hω b.2⟩ : {s // s ∈ A}))
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_attach ω _
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩
  · intro a ha
    exact Subtype.ext rfl
  · intro b hb
    exact Subtype.ext rfl
  · intro a ha
    exact congrArg atoms (Subtype.ext rfl)

lemma freshSum_eq {r : ℕ} {σ : Fin (r + 1) → Finset (Fin L)}
    (hss : ∀ j, σ j ⊆ A) (s : {s : Fin (L + (r + 1)) // s ∈ freshFin L (r + 1)}) :
    (∑ s' ∈ freshSet A σ s,
        MvPolynomial.rename (Fin.castLE (Nat.le_add_right L (r + 1))) (atoms s'))
      = MvPolynomial.rename (Fin.castLE (Nat.le_add_right L (r + 1)))
          (subSum A atoms (A \ σ (freshIdx s))) := by
  rw [subSum_eq_sum_attach (atoms := atoms) (A := A) (ω := A \ σ (freshIdx s)) (Finset.sdiff_subset),
    map_sum, freshSet, Finset.sum_image]
  intro x hx y hy hxy
  exact Subtype.ext (congrArg (fun z : {s' // s' ∈ A} => (z : Fin L)) hxy)

def freshEquiv (L r : ℕ) : Fin r ≃ {s : Fin (L + r) // s ∈ freshFin L r} where
  toFun j := ⟨Fin.natAdd L j, by rw [mem_freshFin]; exact Nat.le_add_right L j.1⟩
  invFun s := freshIdx s
  left_inv j := freshIdx_natAdd j
  right_inv s := Subtype.ext (natAdd_freshIdx s)

@[simp] lemma freshEquiv_apply (L r : ℕ) (j : Fin r) :
    (freshEquiv L r j).1 = Fin.natAdd L j := rfl

theorem closingAtomsSpec {f₀ : Fin L → Bool} {D r : ℕ} {σ : Fin (r + 1) → Finset (Fin L)}
    (hind : LevIndep L A atoms) (hss : ∀ j, σ j ⊆ A) (hsn : ∀ j, σ j ≠ A) (hD : 0 < D) :
    LevIndep (L + (r + 1)) (freshFin L (r + 1)) (closingAtoms A atoms D r σ) ∧
    ∀ u : Fin (r + 1) → Bool,
      atomSum (freshFin L (r + 1)) (closingAtoms A atoms D r σ)
          (slotHist (histOf A f₀ A) (r + 1) u)
        = ∑ j : Fin (r + 1), D • ((liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j))
            * MvPolynomial.X (Fin.natAdd L j)
            * (if u j then (1 : MvPolynomial (Fin (L + (r + 1))) ℤ) else 0)) := by
  -- the class difference in `liftSub` form
  have hdiff : ∀ j : Fin (r + 1),
      liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j)
        = liftSub A atoms (r + 1) (A \ σ j) := by
    intro j
    rw [liftSub, liftSub, liftSub, ← map_sub, subSum_sub (hss j)]
  have hcast : (Fin.castLE (Nat.le_add_right L (r + 1)) : Fin L → Fin (L + (r + 1)))
      = Fin.castAdd (r + 1) := rfl
  -- the nonzero-ness of the class values
  have hne0 : ∀ j : Fin (r + 1), liftSub A atoms (r + 1) A - liftSub A atoms (r + 1) (σ j) ≠ 0 := by
    intro j hzero
    rw [hdiff j] at hzero
    have hz' : liftSub A atoms (r + 1) (A \ σ j) = liftSub A atoms (r + 1) (∅ : Finset (Fin L)) := by
      rw [hzero]; simp [liftSub, subSum]
    have h2 : subSum A atoms (A \ σ j) = subSum A atoms (∅ : Finset (Fin L)) :=
      MvPolynomial.rename_injective (Fin.castLE (Nat.le_add_right L (r + 1)))
        (Fin.castLE_injective (Nat.le_add_right L (r + 1))) hz'
    have h3 : A \ σ j = ∅ :=
      subSum_inj hind (Finset.sdiff_subset) (Finset.empty_subset A) h2
    have hsubA : A ⊆ σ j := by
      intro i hi
      by_contra hcon
      have hmem : i ∈ A \ σ j := Finset.mem_sdiff.mpr ⟨hi, hcon⟩
      rw [h3] at hmem
      exact Finset.notMem_empty i hmem
    exact hsn j (Finset.Subset.antisymm (hss j) hsubA)
  -- the coefficient family
  set c : Fin (r + 1) → MvPolynomial (Fin L) ℤ :=
    fun j => MvPolynomial.C (D : ℤ) * subSum A atoms (A \ σ j) with hc
  have hc_ne : ∀ j, c j ≠ 0 := by
    intro j
    rw [hc]
    refine mul_ne_zero (MvPolynomial.C_ne_zero.mpr (by omega)) ?_
    intro hz
    have h2 : subSum A atoms (A \ σ j) = subSum A atoms (∅ : Finset (Fin L)) := by
      rw [hz]; simp [subSum]
    have h3 : A \ σ j = ∅ :=
      subSum_inj hind (Finset.sdiff_subset) (Finset.empty_subset A) h2
    have hsubA : A ⊆ σ j := by
      intro i hi
      by_contra hcon
      have hmem : i ∈ A \ σ j := Finset.mem_sdiff.mpr ⟨hi, hcon⟩
      rw [h3] at hmem
      exact Finset.notMem_empty i hmem
    exact hsn j (Finset.Subset.antisymm (hss j) hsubA)
  -- the closing atoms in terms of `c`
  have hatoms : ∀ j : Fin (r + 1),
      closingAtoms A atoms D r σ (freshEquiv L (r + 1) j)
        = MvPolynomial.rename (Fin.castAdd (r + 1)) (c j) * MvPolynomial.X (Fin.natAdd L j) := by
    intro j
    rw [closingAtoms, freshSum_eq (A := A) (atoms := atoms) hss (freshEquiv L (r + 1) j)]
    rw [show (freshEquiv L (r + 1) j).1 = Fin.natAdd L j from rfl]
    rw [show freshIdx (freshEquiv L (r + 1) j) = j from freshIdx_natAdd j]
    rw [hc, map_mul, MvPolynomial.rename_C, hcast]
    ring
  -- reindex the atom sum over the fresh coordinates
  have hsum : ∀ h : Fin (L + (r + 1)) → Bool,
      atomSum (freshFin L (r + 1)) (closingAtoms A atoms D r σ) h
        = ∑ j : Fin (r + 1), if h (Fin.natAdd L j) then
            MvPolynomial.rename (Fin.castAdd (r + 1)) (c j) * MvPolynomial.X (Fin.natAdd L j) else 0 := by
    intro h
    rw [atomSum]
    rw [← Fintype.sum_equiv (freshEquiv L (r + 1))
      (fun j : Fin (r + 1) => if h (Fin.natAdd L j) then
        MvPolynomial.rename (Fin.castAdd (r + 1)) (c j) * MvPolynomial.X (Fin.natAdd L j) else 0)
      (fun s : {s : Fin (L + (r + 1)) // s ∈ freshFin L (r + 1)} =>
        if h s.1 then closingAtoms A atoms D r σ s else 0)]
    intro j
    rw [freshEquiv_apply, hatoms j]
  refine ⟨?_, ?_⟩
  · -- independence
    intro h h' hh hh' heq
    have hfun : (∑ j : Fin (r + 1), if h (Fin.natAdd L j) then
        MvPolynomial.rename (Fin.castAdd (r + 1)) (c j) * MvPolynomial.X (Fin.natAdd L j) else 0)
        = (∑ j : Fin (r + 1), if h' (Fin.natAdd L j) then
        MvPolynomial.rename (Fin.castAdd (r + 1)) (c j) * MvPolynomial.X (Fin.natAdd L j) else 0) := by
      rw [← hsum h, ← hsum h']
      exact heq
    have hinj := sumRenameMulXInj (R := ℤ) (L := L) (N := r + 1) c hc_ne
    have hw : (fun j => h (Fin.natAdd L j)) = (fun j => h' (Fin.natAdd L j)) := hinj hfun
    -- both histories live in `cubeSet … 0`, so they vanish off the fresh coordinates
    have hzero : ∀ (g : Fin (L + (r + 1)) → Bool), g ∈ cubeSet (L + (r + 1)) (freshFin L (r + 1)) 0 →
        ∀ i : Fin (L + (r + 1)), i ∉ freshFin L (r + 1) → g i = false := by
      intro g hg i hi
      rw [cubeSet, Finset.mem_filter] at hg
      exact hg.2 i hi
    funext i
    by_cases hi : i ∈ freshFin L (r + 1)
    · have h4 : i = Fin.natAdd L (freshIdx ⟨i, hi⟩) := (natAdd_freshIdx ⟨i, hi⟩).symm
      rw [h4, congrFun hw (freshIdx ⟨i, hi⟩)]
    · rw [hzero h hh i hi, hzero h' hh' i hi]
  · -- the identification
    intro u
    rw [hsum (slotHist (histOf A f₀ A) (r + 1) u)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [slotHist_natAdd]
    by_cases huj : u j = true
    · rw [if_pos huj, if_pos huj, hdiff j, hc, liftSub, map_mul, MvPolynomial.rename_C, hcast,
        nsmul_eq_mul, mvC_natCast]
      ring
    · rw [if_neg huj, if_neg huj]
      simp

lemma slotHist_zero_succ {L r : ℕ} (h₀ : Fin L → Bool) :
    slotHist h₀ (r + 1) (0 : Fin (r + 1) → Bool)
      = Fin.snoc (α := fun _ => Bool) (slotHist h₀ r 0) false := by
  have h0 : (0 : Fin (r + 1) → Bool) = Fin.snoc (α := fun _ => Bool) (0 : Fin r → Bool) false :=
    histSnocZeroFalse.symm
  rw [h0, slotHist_snoc]

lemma slotHist_succ_eq {L r : ℕ} (h₀ : Fin L → Bool) (u : Fin (r + 1) → Bool) :
    slotHist h₀ (r + 1) u
      = Fin.snoc (α := fun _ => Bool) (slotHist h₀ r (Fin.init u)) (u (Fin.last r)) := by
  conv_lhs => rw [← Fin.snoc_init_self (q := u)]
  exact slotHist_snoc h₀ (Fin.init u) (u (Fin.last r))

theorem levRoundClosing {r : ℕ} {K : Finset (Finset (Fin L))} {σ : Fin (r + 1) → Finset (Fin L)}
    {X : HistData d (L + r)} (hinv : LevInv d D A f₀ atoms r K σ X)
    (hind : LevIndep L A atoms) (hD : 2 ≤ D)
    (halldeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D) (hK : K = {A}) :
    LevCube d (D - 1) (L + (r + 1)) (freshFin L (r + 1)) (slotHist (histOf A f₀ A) (r + 1) 0)
      (closingAtoms A atoms D r σ)
      (X.step (Sum.inr 0) (slotHist (histOf A f₀ A) r 0)
        ((hinv.top_mem A hinv.memA (0 : Fin r → Bool)).1)) := by
  obtain ⟨hsub, hneK, hmA, hsz, hss, hsn, hdeg, htop, honly, hcoef⟩ := hinv
  have hinv' : LevInv d D A f₀ atoms r K σ X :=
    ⟨hsub, hneK, hmA, hsz, hss, hsn, hdeg, htop, honly, hcoef⟩
  have hD1 : 1 ≤ D := by omega
  have hD0 : 0 < D := by omega
  have hslot : ∀ x ∈ X.H, ∃ w : Fin r → Bool,
      x = ((Sum.inr 0 : InitIdx d), slotHist (histOf A f₀ A) r w) := by
    intro x hx
    obtain ⟨hx1, ω, hω, w, hxw⟩ := honly x hx (le_of_eq (halldeg x hx).symm)
    have hωA : ω = A := by
      have h1 : ω ∈ ({A} : Finset (Finset (Fin L))) := by rw [← hK]; exact hω
      simpa using h1
    exact ⟨w, Prod.ext hx1 (by rw [hxw, hωA])⟩
  have hspec := closingAtomsSpec (A := A) (atoms := atoms) (f₀ := f₀) hind hss hsn hD0
  refine ⟨?_, ?_⟩
  · ext x
    rw [mem_LevH]
    constructor
    · intro hx
      have hx' : x ∈ X.stepH (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) := hx
      rw [mem_stepH_iff X (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) x] at hx'
      obtain ⟨hxH, hxne, -⟩ := hx'
      obtain ⟨w, hxw⟩ := hslot (x.1, Fin.init x.2) hxH
      have hx1 : x.1 = (Sum.inr 0 : InitIdx d) := congrArg Prod.fst hxw
      have hx2 : (Fin.init x.2 : Fin (L + r) → Bool) = slotHist (histOf A f₀ A) r w :=
        congrArg Prod.snd hxw
      refine ⟨hx1, ?_, ?_⟩
      · rw [cubeSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro i hi
        have hL : i.1 < L := by
          rw [mem_freshFin] at hi
          omega
        have hj : i = (Fin.castAdd r (⟨i.1, hL⟩ : Fin L)).castSucc := Fin.ext rfl
        rw [hj]
        conv_lhs => rw [← Fin.snoc_init_self (q := x.2)]
        rw [hx2, slotHist_zero_succ, Fin.snoc_castSucc, Fin.snoc_castSucc,
          slotHist_castAdd, slotHist_castAdd]
      · intro hcontra
        apply hxne
        exact Prod.ext hx1 (by rw [hcontra]; exact slotHist_zero_succ (histOf A f₀ A))
    · rintro ⟨hx1, hx2, hx3⟩
      obtain ⟨u, hu, -⟩ := eqSlotHistOfMemCubeSet (L := L) (r := r + 1)
        (h₀ := histOf A f₀ A) hx2
      have hu_ne : u ≠ 0 := by
        intro hu0
        apply hx3
        rw [hu, hu0, slotHist_zero_succ]
      have hinit : (Fin.init x.2 : Fin (L + r) → Bool)
          = slotHist (histOf A f₀ A) r (Fin.init u) := by
        rw [hu]
        conv_lhs => rw [slotHist_succ_eq]
        exact init_snoc_eq (slotHist (histOf A f₀ A) r (Fin.init u)) (u (Fin.last r))
      change x ∈ X.stepH (Sum.inr 0) (slotHist (histOf A f₀ A) r 0)
      rw [mem_stepH_iff X (Sum.inr 0) (slotHist (histOf A f₀ A) r 0) x]
      refine ⟨?_, ?_, ?_⟩
      · rw [hinit, hx1]
        exact (htop A hmA (Fin.init u)).1
      · intro hcontra
        apply hx3
        have h4 : x.2 = Fin.snoc (α := fun _ => Bool) (slotHist (histOf A f₀ A) r 0) false :=
          congrArg Prod.snd hcontra
        rw [h4, slotHist_zero_succ]
      · rw [hx1, hu]
        rw [(levClosingCoeff (A := A) (f₀ := f₀) (atoms := atoms) hinv' hind hD halldeg hK u hu_ne).1]
        omega
  · intro h hh hne
    obtain ⟨u, hu, -⟩ := eqSlotHistOfMemCubeSet (L := L) (r := r + 1)
      (h₀ := histOf A f₀ A) hh
    have hu_ne : u ≠ 0 := by
      intro hu0
      apply hne
      rw [hu, hu0, slotHist_zero_succ]
    have hkey := levClosingCoeff (A := A) (f₀ := f₀) (atoms := atoms) hinv' hind hD halldeg hK u hu_ne
    rw [hu, step_Q X (Sum.inr 0) (slotHist (histOf A f₀ A) r 0)
      ((htop A hmA (0 : Fin r → Bool)).1) (Sum.inr 0, slotHist (histOf A f₀ A) (r + 1) u)]
    exact ⟨hkey.1, by rw [hkey.2, hspec.2 u]⟩

end

end Work.Peluse.UControl
