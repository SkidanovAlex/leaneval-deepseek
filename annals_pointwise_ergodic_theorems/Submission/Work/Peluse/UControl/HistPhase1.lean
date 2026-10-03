import Mathlib
import Submission.Work.Peluse.UControl.HistBasic

/-!
# Phase 1 of the history-indexed PET chain

The chain starts at the state `y^1, …, y^(d-1), P` and, as long as some live slot is *not* a
descendant of the top slot `P`, steps at a slot of least degree (Peluse's Lemma 4.4).  This file
proves that

* the phase-1 invariant `Phase1` is preserved (`histPhase1Step`),
* at the end of phase 1 the deterministic selection is the *zero history* of the `P` slot
  (`histPhase1SelZero`),
* and the closing step (Peluse's Lemma 4.5) produces the terminal shape `Phase1Terminal`
  (`histPhase1Terminal`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

/-- The coefficient-ring extension used by one PET step: the old parameters are kept and the new
one is appended. -/
abbrev histRen (n : ℕ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin (n + 1)) ℤ :=
  (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom

lemma histRen_injective (n : ℕ) : Function.Injective (histRen n) :=
  MvPolynomial.rename_injective _ (Fin.castSucc_injective n)

lemma histRen_C {n : ℕ} (a : ℤ) : histRen n (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.rename_C _ _

lemma histMap_natDegree {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℤ)} :
    (p.map (histRen n)).natDegree = p.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (histRen_injective n) p

lemma histMap_leadingCoeff {n : ℕ} {p : Polynomial (MvPolynomial (Fin n) ℤ)} :
    (p.map (histRen n)).leadingCoeff = histRen n p.leadingCoeff :=
  Polynomial.leadingCoeff_map_of_injective (histRen_injective n) p

lemma histComp_natDegree {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℤ))
    (c : MvPolynomial (Fin (n + 1)) ℤ) :
    ((p.map (histRen n)).comp (Polynomial.X + Polynomial.C c)).natDegree = p.natDegree := by
  rw [Polynomial.natDegree_comp, histMap_natDegree, Polynomial.natDegree_X_add_C, mul_one]

lemma histComp_leadingCoeff {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℤ))
    (c : MvPolynomial (Fin (n + 1)) ℤ) :
    ((p.map (histRen n)).comp (Polynomial.X + Polynomial.C c)).leadingCoeff
      = histRen n p.leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (p := p.map (histRen n))
      (q := Polynomial.X + Polynomial.C c) (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
    histMap_leadingCoeff, histMap_natDegree, Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

lemma histComp_coeff {n d : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℤ))
    (c : MvPolynomial (Fin (n + 1)) ℤ) (hdeg : p.natDegree = d) :
    ((p.map (histRen n)).comp (Polynomial.X + Polynomial.C c)).coeff (d - 1)
      = histRen n (p.coeff (d - 1)) + d • (histRen n (p.coeff d) * c) := by
  rw [polyCoeffCompXAddC (p := p.map (histRen n)) c d (by rw [histMap_natDegree, hdeg]),
    Polynomial.coeff_map, Polynomial.coeff_map]

lemma mvC_natCast {σ : Type*} (m : ℕ) : ((m : MvPolynomial σ ℤ)) = MvPolynomial.C (m : ℤ) :=
  (map_natCast MvPolynomial.C m).symm

lemma natDegree_sub_eq_of_lt {R : Type*} [Ring R] {A B : Polynomial R}
    (h : B.natDegree < A.natDegree) : (A - B).natDegree = A.natDegree :=
  Polynomial.natDegree_sub_eq_left_of_natDegree_lt h

lemma leadingCoeff_sub_eq_of_lt {R : Type*} [Ring R] {A B : Polynomial R}
    (h : B.natDegree < A.natDegree) : (A - B).leadingCoeff = A.leadingCoeff := by
  rw [show (A - B).leadingCoeff = (A - B).coeff (A - B).natDegree from rfl,
    natDegree_sub_eq_of_lt h,
    show A.leadingCoeff = A.coeff A.natDegree from rfl,
    Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]

/-- The coefficient `y^(d-1)` of the difference of two degree-`d` polynomials with the same leading
coefficient vanishes, so the difference has degree `< d`. -/
lemma natDegree_sub_lt_of_lc_eq {R : Type*} [Ring R] [NoZeroDivisors R] {A B : Polynomial R}
    {d : ℕ} (hA : A.natDegree = d) (hB : B.natDegree = d) (hlc : A.leadingCoeff = B.leadingCoeff)
    (hd1 : 1 ≤ d) : (A - B).natDegree < d := by
  have hle : (A - B).natDegree ≤ d := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    rw [hA, hB, max_self]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have h1 : A.coeff d = B.coeff d := by
      conv_lhs => rw [← hA]
      conv_rhs => rw [← hB]
      exact hlc
    have hz : (A - B).coeff d = 0 := by rw [Polynomial.coeff_sub, h1, sub_self]
    have hnn : (A - B).leadingCoeff = 0 := by
      rw [show (A - B).leadingCoeff = (A - B).coeff (A - B).natDegree from rfl, h]
      exact hz
    have hzero : A - B = 0 := Polynomial.leadingCoeff_eq_zero.mp hnn
    rw [hzero, Polynomial.natDegree_zero] at h
    omega

/-- The new parameter's shift, as a polynomial. -/
def stepShift {n : ℕ} (h' : Fin (n + 1) → Bool) : MvPolynomial (Fin (n + 1)) ℤ :=
  if h' (Fin.last n) then MvPolynomial.X (Fin.last n) else 0

lemma stepShift_eq {n : ℕ} (h' : Fin (n + 1) → Bool) :
    HistData.shift h' = histRen n (HistData.shift (Fin.init h')) + stepShift h' := by
  rw [stepShift]
  have h1 := HistData.shift_snoc (Fin.init h') (h' (Fin.last n))
  rw [Fin.snoc_init_self] at h1
  exact h1

/-! ## The phase-1 invariant is preserved -/

theorem histPhase1Step' {d n : ℕ} {lc : ℤ} (hd1 : 1 ≤ d) (X : HistData d n)
    (h : Phase1 d n lc X) (i0 : InitIdx d) (h0 : Fin n → Bool) (hh : (i0, h0) ∈ X.H)
    (hi₀ : (X.Q i0 h0).natDegree < d) :
    Phase1 d (n + 1) lc (X.step i0 h0 hh) := by
  classical
  have hi0ne : i0 ≠ (Sum.inr 0 : InitIdx d) := by
    intro heq
    have h1 : (X.Q i0 h0).natDegree = d := by rw [heq]; exact h.pDeg h0
    omega
  have hBd : ((X.Q i0 h0).map (histRen n)).natDegree < d := by
    rw [histMap_natDegree]; exact hi₀
  have hlcP : ∀ (g : Fin n → Bool),
      histRen n ((X.Q (Sum.inr 0 : InitIdx d) g).coeff d) = MvPolynomial.C lc := by
    intro g
    have h2 : (X.Q (Sum.inr 0 : InitIdx d) g).coeff
        ((X.Q (Sum.inr 0 : InitIdx d) g).natDegree) = MvPolynomial.C lc := h.pLc g
    rw [h.pDeg g] at h2
    rw [h2, histRen_C]
  -- the stepped top slots
  have hA : ∀ (h' : Fin (n + 1) → Bool),
      (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
        (Polynomial.X + Polynomial.C (stepShift h'))).natDegree = d := by
    intro h'; rw [histComp_natDegree, h.pDeg (Fin.init h')]
  have hAlc : ∀ (h' : Fin (n + 1) → Bool),
      (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
        (Polynomial.X + Polynomial.C (stepShift h'))).leadingCoeff = MvPolynomial.C lc := by
    intro h'; rw [histComp_leadingCoeff, h.pLc (Fin.init h'), histRen_C]
  have hAcoeff : ∀ (h' : Fin (n + 1) → Bool),
      (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
          (Polynomial.X + Polynomial.C (stepShift h'))).coeff (d - 1)
        = histRen n ((X.Q (Sum.inr 0) (Fin.init h')).coeff (d - 1))
          + MvPolynomial.C (d : ℤ) * (MvPolynomial.C lc * stepShift h') := by
    intro h'
    rw [histComp_coeff (X.Q (Sum.inr 0) (Fin.init h')) (stepShift h') (h.pDeg (Fin.init h')),
      hlcP (Fin.init h'), nsmul_eq_mul, mvC_natCast d]
  -- the coefficient recursion of the top slot
  have hPcoeff : ∀ (h' : Fin n → Bool),
      (X.Q (Sum.inr 0 : InitIdx d) h').coeff (d - 1)
        = (X.Q (Sum.inr 0 : InitIdx d) 0).coeff (d - 1)
          + MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h' := h.pCoeff
  -- the coefficient of a stepped top slot
  have hnewcoeff : ∀ (h' : Fin (n + 1) → Bool),
      (X.stepQ i0 h0 (Sum.inr 0) h').coeff (d - 1)
        = MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h'
          + (histRen n ((X.Q (Sum.inr 0 : InitIdx d) 0).coeff (d - 1))
              - histRen n ((X.Q i0 h0).coeff (d - 1))) := by
    intro h'
    have h1 : (X.stepQ i0 h0 (Sum.inr 0) h')
        = (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
            (Polynomial.X + Polynomial.C (stepShift h')))
          - ((X.Q i0 h0).map (histRen n)) := rfl
    rw [h1, Polynomial.coeff_sub, hAcoeff h', Polynomial.coeff_map,
      hPcoeff (Fin.init h'), stepShift_eq h', map_add, map_mul, map_mul, histRen_C, histRen_C]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- pLive
    intro h'
    show ((Sum.inr 0 : InitIdx d), h') ∈ X.stepH i0 h0
    simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨h.pLive (Fin.init h'), ?_, ?_⟩
    · intro hc
      exact hi0ne (congrArg Prod.fst hc).symm
    · have h1 : (X.stepQ i0 h0 (Sum.inr 0) h')
          = (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
              (Polynomial.X + Polynomial.C (stepShift h')))
            - ((X.Q i0 h0).map (histRen n)) := rfl
      rw [h1, natDegree_sub_eq_of_lt (lt_of_lt_of_eq hBd (hA h').symm), hA h']
      omega
  · -- pDeg
    intro h'
    show (X.stepQ i0 h0 (Sum.inr 0) h').natDegree = d
    have h1 : (X.stepQ i0 h0 (Sum.inr 0) h')
        = (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
            (Polynomial.X + Polynomial.C (stepShift h')))
          - ((X.Q i0 h0).map (histRen n)) := rfl
    rw [h1, natDegree_sub_eq_of_lt (lt_of_lt_of_eq hBd (hA h').symm), hA h']
  · -- pLc
    intro h'
    show (X.stepQ i0 h0 (Sum.inr 0) h').leadingCoeff = MvPolynomial.C lc
    have h1 : (X.stepQ i0 h0 (Sum.inr 0) h')
        = (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
            (Polynomial.X + Polynomial.C (stepShift h')))
          - ((X.Q i0 h0).map (histRen n)) := rfl
    rw [h1, leadingCoeff_sub_eq_of_lt (lt_of_lt_of_eq hBd (hA h').symm), hAlc h']
  · -- pCoeff
    intro h'
    show (X.stepQ i0 h0 (Sum.inr 0) h').coeff (d - 1)
        = (X.stepQ i0 h0 (Sum.inr 0) 0).coeff (d - 1)
          + MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h'
    rw [hnewcoeff h', hnewcoeff 0, HistData.shift_zero, mul_zero]
    ring
  · -- nP
    intro x hx hxne
    change x ∈ X.stepH i0 h0 at hx
    simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxH, -, -⟩ := hx
    show (X.stepQ i0 h0 x.1 x.2).natDegree < d
    have hxd : (X.Q x.1 (Fin.init x.2)).natDegree < d := h.nP _ hxH hxne
    have h1 : (X.stepQ i0 h0 x.1 x.2)
        = (((X.Q x.1 (Fin.init x.2)).map (histRen n)).comp
            (Polynomial.X + Polynomial.C (stepShift x.2)))
          - ((X.Q i0 h0).map (histRen n)) := rfl
    rw [h1]
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt ?_ ?_)
    · rw [histComp_natDegree]; exact hxd
    · rw [histMap_natDegree]; exact hi₀


/-! ## The selection at the end of phase 1 is the zero history -/

theorem histPhase1SelZero {d n : ℕ} {lc : ℤ} (X : HistData d n) (h : Phase1 d n lc X)
    (hdone : Phase1Done X) (hne : X.H.Nonempty) :
    X.sel hne = ((Sum.inr 0 : InitIdx d), 0) := by
  classical
  have hx0mem : ((Sum.inr 0 : InitIdx d), 0) ∈ X.H := h.pLive 0
  have hall : ∀ x ∈ X.H, (X.Q x.1 x.2).natDegree = d := by
    intro x hx
    rw [hdone x hx]
    exact h.pDeg x.2
  have hmin : X.minDeg hne = d := by
    refine le_antisymm ?_ ?_
    · have h1 := X.minDeg_le hne ((Sum.inr 0 : InitIdx d), 0) hx0mem
      rwa [h.pDeg 0] at h1
    · have hmem := X.minDeg_mem hne
      rw [HistData.degImg, Finset.mem_image] at hmem
      obtain ⟨x, hx, hxk⟩ := hmem
      rw [← hxk, hall x hx]
  have hx0slot : ((Sum.inr 0 : InitIdx d), 0) ∈ X.minDegSlots hne := by
    rw [X.mem_minDegSlots]
    exact ⟨hx0mem, by rw [h.pDeg 0, hmin]⟩
  have hle := X.sel_le hne _ hx0slot
  have hval0 : X.selVal ((Sum.inr 0 : InitIdx d), 0) = 0 := by
    simp [HistData.selVal, jval, histVal_eq_zero_iff]
  rw [hval0] at hle
  have hselval : X.selVal (X.sel hne) = 0 := Nat.eq_zero_of_le_zero hle
  have hj : jval (X.sel hne).1 = 0 := by
    have h2 : jval (X.sel hne).1 ≤ X.selVal (X.sel hne) := by
      rw [HistData.selVal]; exact Nat.le_add_left _ _
    omega
  have hhv : histVal (X.sel hne).2 = 0 := by
    have h2 : histVal (X.sel hne).2 * (2 * d + 1) ≤ X.selVal (X.sel hne) := by
      rw [HistData.selVal]; exact Nat.le_add_right _ _
    rw [hselval] at h2
    have h3 : histVal (X.sel hne).2 * (2 * d + 1) = 0 := Nat.eq_zero_of_le_zero h2
    rcases Nat.mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · omega
  have hj' : (X.sel hne).1 = (Sum.inr 0 : InitIdx d) :=
    jval_injective (by rw [hj]; simp [jval])
  refine Prod.ext ?_ ?_
  · show (X.sel hne).1 = (Sum.inr 0 : InitIdx d)
    exact hj'
  · show (X.sel hne).2 = 0
    exact histVal_eq_zero_iff.mp hhv

/-! ## The closing step of phase 1 -/

theorem histPhase1Terminal {d n : ℕ} {lc : ℤ} (hd2 : 2 ≤ d) (hlc : lc ≠ 0) (X : HistData d n)
    (h : Phase1 d n lc X) (hdone : Phase1Done X) (hne : X.H.Nonempty) :
    Phase1Terminal d (n + 1) lc (X.step (Sum.inr 0) 0 (h.pLive 0)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hlcP : ∀ (g : Fin n → Bool),
      histRen n ((X.Q (Sum.inr 0 : InitIdx d) g).coeff d) = MvPolynomial.C lc := by
    intro g
    have h2 : (X.Q (Sum.inr 0 : InitIdx d) g).coeff
        ((X.Q (Sum.inr 0 : InitIdx d) g).natDegree) = MvPolynomial.C lc := h.pLc g
    rw [h.pDeg g] at h2
    rw [h2, histRen_C]
  have hAdeg : ∀ (h' : Fin (n + 1) → Bool),
      (((X.Q (Sum.inr 0 : InitIdx d) (Fin.init h')).map (histRen n)).comp
        (Polynomial.X + Polynomial.C (stepShift h'))).natDegree = d := by
    intro h'; rw [histComp_natDegree, h.pDeg (Fin.init h')]
  have hAlc : ∀ (h' : Fin (n + 1) → Bool),
      (((X.Q (Sum.inr 0 : InitIdx d) (Fin.init h')).map (histRen n)).comp
        (Polynomial.X + Polynomial.C (stepShift h'))).leadingCoeff = MvPolynomial.C lc := by
    intro h'; rw [histComp_leadingCoeff, h.pLc (Fin.init h'), histRen_C]
  have hBdeg : ((X.Q (Sum.inr 0 : InitIdx d) 0).map (histRen n)).natDegree = d := by
    rw [histMap_natDegree, h.pDeg 0]
  have hBlc : ((X.Q (Sum.inr 0 : InitIdx d) 0).map (histRen n)).leadingCoeff
      = MvPolynomial.C lc := by
    rw [histMap_leadingCoeff, h.pLc 0, histRen_C]
  have hstepQ : ∀ (h' : Fin (n + 1) → Bool),
      (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) h')
        = (((X.Q (Sum.inr 0) (Fin.init h')).map (histRen n)).comp
            (Polynomial.X + Polynomial.C (stepShift h')))
          - ((X.Q (Sum.inr 0) 0).map (histRen n)) := fun h' => rfl
  have hcoeff : ∀ (h' : Fin (n + 1) → Bool),
      (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) h').coeff (d - 1)
        = MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h' := by
    intro h'
    rw [hstepQ h', Polynomial.coeff_sub,
      histComp_coeff (X.Q (Sum.inr 0) (Fin.init h')) (stepShift h') (h.pDeg (Fin.init h')),
      hlcP (Fin.init h'), Polynomial.coeff_map, h.pCoeff (Fin.init h'), stepShift_eq h',
      map_add, map_mul, map_mul, histRen_C, histRen_C, nsmul_eq_mul, mvC_natCast d]
    ring
  have hdeg : ∀ (h' : Fin (n + 1) → Bool), h' ≠ 0 →
      (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) h').natDegree = d - 1 := by
    intro h' hh'
    have hlt : (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) h').natDegree < d := by
      rw [hstepQ h']
      exact natDegree_sub_lt_of_lc_eq (hAdeg h') hBdeg (by rw [hAlc h', hBlc]) hd1
    have hle : (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) h').natDegree ≤ d - 1 := by omega
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle ?_
    rw [hcoeff h']
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (histShiftNeZero hh')
    · exact MvPolynomial.C_ne_zero.mpr (by omega)
    · exact MvPolynomial.C_ne_zero.mpr hlc
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ X.stepH (Sum.inr 0) 0 at hx
    simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxH, hxne, -⟩ := hx
    have hx1 : x.1 = (Sum.inr 0 : InitIdx d) := hdone (x.1, Fin.init x.2) hxH
    have hx2 : x.2 ≠ 0 := by
      intro hz
      apply hxne
      have h1 : x = ((Sum.inr 0 : InitIdx d), Fin.snoc (0 : Fin n → Bool) false) := by
        refine Prod.ext ?_ ?_
        · rw [hx1]
        · rw [hz]; exact histSnocZeroFalse.symm
      rw [h1]
    refine ⟨hx1, hx2, ?_, ?_⟩
    · show (X.stepQ (Sum.inr 0) 0 x.1 x.2).natDegree = d - 1
      rw [hx1]
      exact hdeg x.2 hx2
    · show (X.stepQ (Sum.inr 0) 0 x.1 x.2).leadingCoeff
          = MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift x.2
      rw [hx1, show (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) x.2).leadingCoeff
            = (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) x.2).coeff
                (X.stepQ (Sum.inr 0) 0 (Sum.inr 0) x.2).natDegree from rfl,
        hdeg x.2 hx2, hcoeff x.2]
  · intro h' hh'
    change ((Sum.inr 0 : InitIdx d), h') ∈ X.stepH (Sum.inr 0) 0
    simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨h.pLive (Fin.init h'), ?_, ?_⟩
    · intro hc
      apply hh'
      have h1 : h' = Fin.snoc (0 : Fin n → Bool) false := by
        simpa using congrArg Prod.snd hc
      rw [h1, histSnocZeroFalse]
    · rw [hdeg h' hh']; omega

/-- The phase-1 step along the deterministic selection. -/
theorem histPhase1Step {d n : ℕ} {lc : ℤ} (hd1 : 1 ≤ d) (X : HistData d n)
    (h : Phase1 d n lc X) (hne : X.H.Nonempty)
    (hi₀ : (X.Q (X.sel hne).1 (X.sel hne).2).natDegree < d) :
    Phase1 d (n + 1) lc (X.step (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne)) :=
  histPhase1Step' hd1 X h (X.sel hne).1 (X.sel hne).2 (X.sel_mem_H hne) hi₀

end

end Work.Peluse.UControl
