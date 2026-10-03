import Mathlib
import Submission.Work.Peluse.UControl.HistPhase1

/-!
# The class-reduction step of a level round (Peluse's Lemma 4.6)

`NOTES_petChapter5_session17.md` §4.2.  A level state carries, for each live slot `h`, a *class*
`lc(Q_h) = A(h) - ref`, where `A(h) = Σ_{s : h s} atom s` is **additive over the Boolean histories**
(`Aatom`) and `ref` is a reference polynomial.  This file proves that a PET step at a slot `h₀`
moves the reference to `A(h₀)` and drops the class of `h₀`:

  `lc(Q'_{h'}) = histRen (A(Fin.init h')) − histRen (A(h₀))`,

one **fewer** class than before (the slot with `Fin.init h' = h₀` — exactly the `(h₀, ·)`-descendant
— falls below the top degree).  That is the paper's Lemma 4.6, and it is what reduces the number of
top-degree classes by one in each sub-round of a round.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-- The additive "atom sum" of a Boolean history: `Σ_{s : h s} atom s`.  This is the shape of the
leading coefficients of a level state (Peluse's `A_j`). -/
def Aatom {n : ℕ} (atom : Fin n → MvPolynomial (Fin n) ℤ) (h : Fin n → Bool) :
    MvPolynomial (Fin n) ℤ :=
  ∑ s ∈ Finset.univ.filter (fun s => h s), atom s

/-- Two polynomials of the same degree `D` with **different** leading coefficients: their difference
still has degree `D`, and its leading coefficient is the difference of the leading coefficients. -/
lemma natDegree_sub_eq_of_lc_ne {R : Type*} [Ring R] {A B : Polynomial R} {D : ℕ}
    (hA : A.natDegree = D) (hB : B.natDegree = D) (hlc : A.leadingCoeff ≠ B.leadingCoeff) :
    (A - B).natDegree = D ∧ (A - B).leadingCoeff = A.leadingCoeff - B.leadingCoeff := by
  have hcoeff : (A - B).coeff D = A.leadingCoeff - B.leadingCoeff := by
    rw [Polynomial.coeff_sub,
      show A.coeff D = A.leadingCoeff from by rw [← hA, Polynomial.coeff_natDegree],
      show B.coeff D = B.leadingCoeff from by rw [← hB, Polynomial.coeff_natDegree]]
  have hne : (A - B).coeff D ≠ 0 := by
    rw [hcoeff]; exact sub_ne_zero.mpr hlc
  have hle : (A - B).natDegree ≤ D :=
    le_trans (Polynomial.natDegree_sub_le _ _) (by rw [hA, hB, max_self])
  have hdeg : (A - B).natDegree = D := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hne
  exact ⟨hdeg, by rw [Polynomial.leadingCoeff, hdeg, hcoeff]⟩

/-- **The class-reduction step** (Peluse's Lemma 4.6).  If every slot `(P0, h)` of `X` has degree
`D ≥ 2` and class `lc(Q_h) = A(h) - ref`, and distinct histories have distinct atom sums, then the
step at `h₀` gives

* `natDegree ≤ D` for every new slot, and
* for `Fin.init h' ≠ h₀`: `natDegree = D` and
  `lc(Q'_{h'}) = histRen (A(Fin.init h')) - histRen (A(h₀))`,

i.e. the reference has moved to `A(h₀)` and the class of `h₀` has been lost. -/
theorem levStepRef {d n D : ℕ} (X : HistData d n) (P0 : InitIdx d)
    (atom : Fin n → MvPolynomial (Fin n) ℤ) (ref : MvPolynomial (Fin n) ℤ)
    (h₀ : Fin n → Bool)
    (hall : ∀ h : Fin n → Bool, (P0, h) ∈ X.H)
    (hdeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D)
    (hlc : ∀ h : Fin n → Bool, (X.Q P0 h).leadingCoeff = Aatom atom h - ref)
    (hinj : ∀ h g : Fin n → Bool, Aatom atom h = Aatom atom g → h = g) :
    ∀ h' : Fin (n + 1) → Bool,
      (X.stepQ P0 h₀ P0 h').natDegree ≤ D
      ∧ (Fin.init h' ≠ h₀ →
          (X.stepQ P0 h₀ P0 h').natDegree = D
          ∧ (X.stepQ P0 h₀ P0 h').leadingCoeff
            = histRen n (Aatom atom (Fin.init h')) - histRen n (Aatom atom h₀)) := by
  intro h'
  have hdegA : (((X.Q P0 (Fin.init h')).map (histRen n)).comp
      (Polynomial.X + Polynomial.C (stepShift h'))).natDegree = D := by
    rw [histComp_natDegree, hdeg _ (hall _)]
  have hlcA : (((X.Q P0 (Fin.init h')).map (histRen n)).comp
      (Polynomial.X + Polynomial.C (stepShift h'))).leadingCoeff
      = histRen n (Aatom atom (Fin.init h') - ref) := by
    rw [histComp_leadingCoeff, hlc (Fin.init h')]
  have hdegB : ((X.Q P0 h₀).map (histRen n)).natDegree = D := by
    rw [histMap_natDegree, hdeg _ (hall h₀)]
  have hlcB : ((X.Q P0 h₀).map (histRen n)).leadingCoeff
      = histRen n (Aatom atom h₀ - ref) := by
    rw [histMap_leadingCoeff, hlc h₀]
  have hsub : X.stepQ P0 h₀ P0 h'
      = (((X.Q P0 (Fin.init h')).map (histRen n)).comp
          (Polynomial.X + Polynomial.C (stepShift h')))
        - ((X.Q P0 h₀).map (histRen n)) := rfl
  refine ⟨?_, ?_⟩
  · rw [hsub]
    exact le_trans (Polynomial.natDegree_sub_le _ _) (by rw [hdegA, hdegB, max_self])
  · intro hne
    have hlcdiff : (((X.Q P0 (Fin.init h')).map (histRen n)).comp
          (Polynomial.X + Polynomial.C (stepShift h'))).leadingCoeff
        ≠ ((X.Q P0 h₀).map (histRen n)).leadingCoeff := by
      rw [hlcA, hlcB]
      intro hcontra
      have h1 : Aatom atom (Fin.init h') = Aatom atom h₀ := by
        have h3 : Aatom atom (Fin.init h') - ref = Aatom atom h₀ - ref :=
          histRen_injective n hcontra
        calc Aatom atom (Fin.init h') = (Aatom atom (Fin.init h') - ref) + ref := by ring
          _ = (Aatom atom h₀ - ref) + ref := by rw [h3]
          _ = Aatom atom h₀ := by ring
      exact hne (hinj _ _ h1)
    obtain ⟨hd, hl⟩ := natDegree_sub_eq_of_lc_ne hdegA hdegB hlcdiff
    refine ⟨?_, ?_⟩
    · rw [hsub]; exact hd
    · rw [hsub, hl, hlcA, hlcB, map_sub, map_sub]
      ring

/-- **The `coeff (D-1)` recursion of a PET step** (Peluse's `C_j^{(k)}` bookkeeping): a step at
`(P0, h₀)` from a state all of whose slots have degree exactly `D` sends

  `coeff (D-1) (Q'_{h'}) = histRen (coeff (D-1) (Q_{Fin.init h'})) + D • (histRen (lc (Q_{Fin.init h'})) · stepShift h')
                            - histRen (coeff (D-1) (Q_{h₀}))`.

The `D • (lc · a_new)` term is the binomial contribution of the new parameter and is exactly what
makes the *new* atoms `D·lc·a_new` appear one level down (cf. `levClose`). -/
theorem levStepRef_coeff {d n D : ℕ} (X : HistData d n) (P0 : InitIdx d)
    (h₀ : Fin n → Bool)
    (hall : ∀ h : Fin n → Bool, (P0, h) ∈ X.H)
    (hdeg : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = D) :
    ∀ h' : Fin (n + 1) → Bool,
      (X.stepQ P0 h₀ P0 h').coeff (D - 1)
        = histRen n ((X.Q P0 (Fin.init h')).coeff (D - 1))
          + D • (histRen n ((X.Q P0 (Fin.init h')).leadingCoeff) * stepShift h')
          - histRen n ((X.Q P0 h₀).coeff (D - 1)) := by
  intro h'
  have hsub : X.stepQ P0 h₀ P0 h'
      = (((X.Q P0 (Fin.init h')).map (histRen n)).comp
          (Polynomial.X + Polynomial.C (stepShift h')))
        - ((X.Q P0 h₀).map (histRen n)) := rfl
  have hlc : (X.Q P0 (Fin.init h')).leadingCoeff
      = (X.Q P0 (Fin.init h')).coeff D := by
    rw [Polynomial.leadingCoeff, hdeg _ (hall _)]
  rw [hsub, Polynomial.coeff_sub,
    histComp_coeff (X.Q P0 (Fin.init h')) (stepShift h') (hdeg _ (hall _)),
    hlc, Polynomial.coeff_map]

end

end Work.Peluse.UControl
