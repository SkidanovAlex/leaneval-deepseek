import Mathlib
import Submission.Work.Peluse.UControl.PetChainIter

/-!
# The history-indexed PET chain (the explicit form needed for the terminal identification)

`Work.Peluse.UControl.petChapter5Holds` needs, beyond the *analytic* PET chain (which works for any
slot-selection rule decreasing Peluse's weight vector, see `PetChainIter`/`petRun`), the
*identification* of the chain's terminal state with the datum's `linFamAvg`.  That identification
needs the terminal slot polynomials to be *known* — which rules out the `Classical.choose`-based
`SymState.minSlot` (an arbitrary least-degree slot) and therefore requires a chain whose states are
indexed *explicitly by the ε-histories* of their slots.

* `InitIdx d` — the initial slots `y^1, …, y^(d-1), P`;
* `histVal` — the value `Σ_i 2^i·[h_i]` of a Boolean history, used to break ties deterministically;
* `HistData d n` — a chain state: a `Finset` of *live* slots `(j, h)` together with their shift
  polynomials `Q j h ∈ ℤ[a_1,…,a_n][y]`;
* `HistData.toSym` — the same state as a `SymState d`, so that the analytic chain (`PetInv`,
  `petRun`) and the weight lemmas apply to it;
* `HistData.stepQ`/`stepH`/`step` — one PET step at a slot `(i₀, h₀)`: the new slot `(j, snoc h ε)`
  carries `Q j h (y + ε a_{n+1}) - Q i₀ h₀`, and the constant slots (`natDegree = 0`) are dropped;
* `HistData.sel` — the deterministic selection: the live slot of least degree, tie-broken by
  `(histVal, jval)` (the all-zero history of the `P` slot is the minimum, which is what makes the
  terminal step produce the clean family `{ℓ·lc P·Σ_{i ∈ ω} a_i}`);
* `HistData.shift` — the shift `Σ_{i : h i} a_i` of a history, the quantity governing the
  degree-`(d-1)` coefficients;
* `Phase1` — the invariant of the first ("4.4") phase of the chain, and `Phase1Terminal` — the shape
  of the state after the closing "4.5" step.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

variable {d n : ℕ}

/-- The value of a Boolean history: `Σ_i 2^i·[h i]`.  The all-zero history is its unique minimum. -/
def histVal {n : ℕ} (h : Fin n → Bool) : ℕ := ∑ i : Fin n, if h i then 2 ^ (i : ℕ) else 0

lemma histVal_eq_zero_iff {n : ℕ} {h : Fin n → Bool} : histVal h = 0 ↔ h = 0 := by
  constructor
  · intro hh
    funext i
    by_contra hi
    have htrue : h i = true := by
      cases hb : h i <;> simp_all
    have hle : (if h i then 2 ^ (i : ℕ) else 0) ≤ histVal h :=
      Finset.single_le_sum (f := fun j : Fin n => if h j then 2 ^ (j : ℕ) else 0)
        (fun j _ => by split <;> simp) (Finset.mem_univ i)
    rw [htrue, hh] at hle
    simp only [if_true] at hle
    have := Nat.one_le_two_pow (n := (i : ℕ))
    omega
  · intro hh
    rw [hh]
    simp [histVal]

/-- The type of the initial slots of the phase-1 chain: `y^1, …, y^(d-1)` and `P`. -/
abbrev InitIdx (d : ℕ) := Fin (d - 1) ⊕ Fin 1

/-- An integer tag of an initial slot, injective and with the `P` slot tagged `0`. -/
def jval {d : ℕ} : InitIdx d → ℕ
  | Sum.inl i => 2 * (i : ℕ) + 1
  | Sum.inr _ => 0

lemma jval_lt {d : ℕ} (j : InitIdx d) : jval j < 2 * d + 1 := by
  rcases j with i | i
  · have : (i : ℕ) < d - 1 := i.isLt
    simp only [jval]
    omega
  · simp [jval]

lemma jval_injective {d : ℕ} : Function.Injective (jval (d := d)) := by
  intro j j' h
  rcases j with i | i <;> rcases j' with i' | i' <;> simp only [jval] at h
  · congr 1; omega
  · omega
  · omega
  · exact congrArg Sum.inr (Subsingleton.elim i i')

/-- A state of the history-indexed PET chain: the live slots `(j, h)` and their shift polynomials. -/
structure HistData (d n : ℕ) where
  H : Finset (InitIdx d × (Fin n → Bool))
  Q : InitIdx d → (Fin n → Bool) → Polynomial (MvPolynomial (Fin n) ℤ)
  hd : ∀ x ∈ H, (Q x.1 x.2).natDegree ≤ d
  hnc : ∀ x ∈ H, 1 ≤ (Q x.1 x.2).natDegree

/-- The chain state as a `SymState`, so that the analytic chain applies to it. -/
def HistData.toSym (X : HistData d n) : SymState d where
  nv := n
  S :=
    { ι := {x : InitIdx d × (Fin n → Bool) // x ∈ X.H}
      finι := inferInstance
      decι := inferInstance
      P := fun x => X.Q x.1.1 x.1.2 }
  hd := fun x => X.hd x.1 x.2

/-- The shift polynomials of the next state. -/
def HistData.stepQ (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool) :
    InitIdx d → (Fin (n + 1) → Bool) → Polynomial (MvPolynomial (Fin (n + 1)) ℤ) :=
  fun j h' =>
    (((X.Q j (Fin.init h')).map (MvPolynomial.rename Fin.castSucc).toRingHom).comp
        (Polynomial.X + Polynomial.C
          (if h' (Fin.last n) then MvPolynomial.X (Fin.last n) else 0)))
      - (X.Q i₀ h₀).map (MvPolynomial.rename Fin.castSucc).toRingHom

/-- The live slots of the next state: the descendants of the live slots, minus the dropped
`(i₀, false)` continuation and minus the constant slots. -/
def HistData.stepH (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool) :
    Finset (InitIdx d × (Fin (n + 1) → Bool)) :=
  Finset.univ.filter (fun x =>
    (x.1, Fin.init x.2) ∈ X.H ∧ x ≠ (i₀, Fin.snoc h₀ false) ∧
      1 ≤ (X.stepQ i₀ h₀ x.1 x.2).natDegree)

/-- One PET step. -/
def HistData.step (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) : HistData d (n + 1) where
  H := X.stepH i₀ h₀
  Q := X.stepQ i₀ h₀
  hd := by
    intro x hx
    simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxH, -, -⟩ := hx
    have hmap : ((X.Q x.1 (Fin.init x.2)).map
        (MvPolynomial.rename Fin.castSucc).toRingHom).natDegree ≤ d :=
      le_trans Polynomial.natDegree_map_le (X.hd _ hxH)
    have hq : (Polynomial.X + Polynomial.C
        (if x.2 (Fin.last n) then MvPolynomial.X (Fin.last n) else 0) :
          Polynomial (MvPolynomial (Fin (n + 1)) ℤ)).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · simp
      · rw [Polynomial.natDegree_C]; omega
    have hcomp := Polynomial.natDegree_comp_le
        (p := (X.Q x.1 (Fin.init x.2)).map (MvPolynomial.rename Fin.castSucc).toRingHom)
        (q := (Polynomial.X + Polynomial.C
          (if x.2 (Fin.last n) then MvPolynomial.X (Fin.last n) else 0)))
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · refine le_trans hcomp ?_
      calc ((X.Q x.1 (Fin.init x.2)).map
              (MvPolynomial.rename Fin.castSucc).toRingHom).natDegree
            * (Polynomial.X + Polynomial.C
                (if x.2 (Fin.last n) then MvPolynomial.X (Fin.last n) else 0)).natDegree
          ≤ ((X.Q x.1 (Fin.init x.2)).map
              (MvPolynomial.rename Fin.castSucc).toRingHom).natDegree * 1 :=
            Nat.mul_le_mul_left _ hq
        _ ≤ d := by rw [mul_one]; exact hmap
    · exact le_trans Polynomial.natDegree_map_le (X.hd _ hh)
  hnc := by
    intro x hx
    simp only [HistData.stepH, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.2.2

/-- The set of degrees of the live slots. -/
def HistData.degImg (X : HistData d n) : Finset ℕ :=
  X.H.image (fun x => (X.Q x.1 x.2).natDegree)

lemma HistData.degImg_nonempty (X : HistData d n) (hne : X.H.Nonempty) :
    X.degImg.Nonempty := Finset.Nonempty.image hne _

/-- The least degree among the live slots. -/
def HistData.minDeg (X : HistData d n) (hne : X.H.Nonempty) : ℕ :=
  X.degImg.min' (X.degImg_nonempty hne)

lemma HistData.minDeg_le (X : HistData d n) (hne : X.H.Nonempty) (x : InitIdx d × (Fin n → Bool))
    (hx : x ∈ X.H) : X.minDeg hne ≤ (X.Q x.1 x.2).natDegree :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)

/-- The least degree is attained. -/
lemma HistData.minDeg_mem (X : HistData d n) (hne : X.H.Nonempty) :
    X.minDeg hne ∈ X.degImg := Finset.min'_mem X.degImg (X.degImg_nonempty hne)

/-- The live slots of least degree. -/
def HistData.minDegSlots (X : HistData d n) (hne : X.H.Nonempty) :
    Finset (InitIdx d × (Fin n → Bool)) :=
  X.H.filter (fun x => (X.Q x.1 x.2).natDegree = X.minDeg hne)

lemma HistData.mem_minDegSlots {X : HistData d n} {hne : X.H.Nonempty}
    {x : InitIdx d × (Fin n → Bool)} :
    x ∈ X.minDegSlots hne ↔ x ∈ X.H ∧ (X.Q x.1 x.2).natDegree = X.minDeg hne := by
  simp [HistData.minDegSlots]

lemma HistData.minDegSlots_nonempty (X : HistData d n) (hne : X.H.Nonempty) :
    (X.minDegSlots hne).Nonempty := by
  have hmem : X.minDeg hne ∈ X.degImg := Finset.min'_mem X.degImg (X.degImg_nonempty hne)
  obtain ⟨x, hx, hxk⟩ := Finset.mem_image.mp hmem
  refine ⟨x, (X.mem_minDegSlots).mpr ⟨hx, ?_⟩⟩
  exact hxk

/-- The tie-breaking value of a slot. -/
def HistData.selVal (X : HistData d n) (x : InitIdx d × (Fin n → Bool)) : ℕ :=
  histVal x.2 * (2 * d + 1) + jval x.1

/-- **The deterministic slot selection**: the live slot of least degree, tie-broken by
`(histVal, jval)` — i.e. the minimum of `selVal` over the slots of least degree. -/
def HistData.sel (X : HistData d n) (hne : X.H.Nonempty) : InitIdx d × (Fin n → Bool) :=
  Classical.choose (Finset.exists_min_image (X.minDegSlots hne) (X.selVal)
    (X.minDegSlots_nonempty hne))

lemma HistData.sel_mem (X : HistData d n) (hne : X.H.Nonempty) : X.sel hne ∈ X.minDegSlots hne :=
  (Classical.choose_spec (Finset.exists_min_image (X.minDegSlots hne) (X.selVal)
    (X.minDegSlots_nonempty hne))).1

lemma HistData.sel_le (X : HistData d n) (hne : X.H.Nonempty) (x : InitIdx d × (Fin n → Bool))
    (hx : x ∈ X.minDegSlots hne) : X.selVal (X.sel hne) ≤ X.selVal x :=
  (Classical.choose_spec (Finset.exists_min_image (X.minDegSlots hne) (X.selVal)
    (X.minDegSlots_nonempty hne))).2 x hx

lemma HistData.sel_mem_H (X : HistData d n) (hne : X.H.Nonempty) : X.sel hne ∈ X.H :=
  (X.mem_minDegSlots.mp (X.sel_mem hne)).1

lemma HistData.sel_degree (X : HistData d n) (hne : X.H.Nonempty) :
    (X.Q (X.sel hne).1 (X.sel hne).2).natDegree = X.minDeg hne :=
  (X.mem_minDegSlots.mp (X.sel_mem hne)).2

/-! ## The history shift and the phase-1 invariant -/

/-- The shift `Σ_{i : h i} a_i` attached to a Boolean history. -/
def HistData.shift {n : ℕ} (h : Fin n → Bool) : MvPolynomial (Fin n) ℤ :=
  ∑ i : Fin n, if h i then MvPolynomial.X i else 0

lemma HistData.shift_zero {n : ℕ} : HistData.shift (0 : Fin n → Bool) = 0 := by
  simp [HistData.shift]

lemma HistData.shift_snoc {n : ℕ} (h : Fin n → Bool) (ε : Bool) :
    HistData.shift (Fin.snoc h ε) =
      MvPolynomial.rename Fin.castSucc (HistData.shift h)
        + (if ε then MvPolynomial.X (Fin.last n) else 0) := by
  classical
  have key : ∀ i : Fin n, (if (Fin.snoc h ε : Fin (n + 1) → Bool) (Fin.castSucc i) then
        (MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (n + 1)) ℤ) else 0)
      = (MvPolynomial.rename Fin.castSucc) (if h i then MvPolynomial.X i else 0) := by
    intro i
    rw [Fin.snoc_castSucc]
    by_cases hi : h i <;> simp [hi]
  have key2 : (if (Fin.snoc h ε : Fin (n + 1) → Bool) (Fin.last n) then
        (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℤ) else 0)
      = (if ε then MvPolynomial.X (Fin.last n) else 0) := by rw [Fin.snoc_last]
  rw [HistData.shift, HistData.shift, Fin.sum_univ_castSucc, key2]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => key i)]
  rw [show (MvPolynomial.rename Fin.castSucc)
        (∑ i : Fin n, (if h i then MvPolynomial.X i else 0))
       = ∑ i : Fin n, (MvPolynomial.rename Fin.castSucc) (if h i then MvPolynomial.X i else 0)
     from map_sum _ _ _]

/-- **The phase-1 invariant.**  While the chain still has a slot whose shift is *not* a descendant
of the top slot, all the top-slot descendants have degree exactly `d` and leading coefficient
`C lc`, the differences of their degree-`(d-1)` coefficients are governed by `shift`, and every other
live slot has degree `< d`. -/
structure Phase1 (d n : ℕ) (lc : ℤ) (X : HistData d n) : Prop where
  pLive : ∀ h : Fin n → Bool, ((Sum.inr 0 : InitIdx d), h) ∈ X.H
  pDeg : ∀ h, (X.Q (Sum.inr 0 : InitIdx d) h).natDegree = d
  pLc : ∀ h, (X.Q (Sum.inr 0 : InitIdx d) h).leadingCoeff = MvPolynomial.C lc
  pCoeff : ∀ h : Fin n → Bool,
    (X.Q (Sum.inr 0 : InitIdx d) h).coeff (d - 1)
      = (X.Q (Sum.inr 0 : InitIdx d) 0).coeff (d - 1)
        + MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift h
  nP : ∀ x ∈ X.H, x.1 ≠ (Sum.inr 0 : InitIdx d) → (X.Q x.1 x.2).natDegree < d

/-- The phase-1 state has no non-descendant slots. -/
def Phase1Done (X : HistData d n) : Prop := ∀ x ∈ X.H, x.1 = (Sum.inr 0 : InitIdx d)

/-- The shape of the state reached by the closing step at the zero history: its live slots are
`(P, h)` with `h ≠ 0`, of degree `d - 1` and leading coefficient `C d · C lc · shift h`. -/
def Phase1Terminal (d n : ℕ) (lc : ℤ) (X : HistData d n) : Prop :=
  (∀ x ∈ X.H, x.1 = (Sum.inr 0 : InitIdx d) ∧ x.2 ≠ 0
      ∧ (X.Q x.1 x.2).natDegree = d - 1
      ∧ (X.Q x.1 x.2).leadingCoeff
          = MvPolynomial.C (d : ℤ) * MvPolynomial.C lc * HistData.shift x.2)
    ∧ (∀ h : Fin n → Bool, h ≠ 0 → ((Sum.inr 0 : InitIdx d), h) ∈ X.H)

/-- Peluse's weight vector of a history state, read through the abstract symbolic companion
`X.toSym` (so that the weight lemmas proved for `PetStateSym` apply with no transport). -/
def HistData.weightH (X : HistData d n) (j : Fin (d + 1)) : ℕ := (X.toSym).S.weight d j

end

end Work.Peluse.UControl
