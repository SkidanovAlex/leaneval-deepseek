import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.pure_pullback_cont
import Submission.Work.A14D.pure_su_extension

/-!
# `Work.A14D` — the `SU`-branches and the "jump" functions of the `(LC)` transfer

Route (see `relation_to_LC_A.lean`): the relation `Σᵢ Pᵢ·fourteenᵢ = 0` is pulled back along
`y = yC z` and continued to the half planes `SU`, `SL`; the *jump* `F^{SU} − F^{SL}` of each of the
fourteen entries is an analytic function on `Om1 = ℂ ∖ (−∞,1]`, and the *jump relation*
`Σᵢ pᵢ(y(z))·(jump of Fᵢ) = 0` holds on `Om1`.  The coefficient of `log (z − 1/9)` of that
relation is `κσ · (LC)`; extracting it (one-sided, with a pole-type remainder:
`Work.A14D.extract_log_half`) gives `κσ · (LC) = 0`.

This file only *defines* the objects:

* `cSU`, `cSL` — base points of `SU`/`SL` at which `‖yC ·‖ < 1/5` (so that the `y`-series of the
  fourteen entries converge there);
* `pureIdxA`, `gIdxA`, `iIdxA` — the slot bookkeeping;
* `GjetA` — the subtracted jets `Σ_{n<i}[yⁿ]G·yⁿ` of the `i`-th integral entry;
* `BUg`, `BUi`, `BUp`, `BU` — the `SU`-branch of the fourteen pullbacks;
* `JFA` — the jump of the fourteen pullbacks (the `G`-slots and the integral slots from the given
  solution `D` of `LZ = 0`, computed as `∂_y^k(D − D∘w)` and as a primitive of
  `y^{-i}y'(D − D∘w)`; the pure slots are `BUp j − (BUp j)∘w`);
* `LF` — the left-hand side `Σᵢ pᵢ(y(z))·JFA D i z` of the jump relation.
-/

namespace Work.A14D

open Complex Metric
open scoped Topology BigOperators

noncomputable section

/-- A base point of `SU` with `‖yC ·‖ < 1/5` and `‖·‖ < 1`. -/
def cSU : ℂ := 1 / 20 + (1 / 8 : ℝ) * Complex.I

/-- A base point of `SL` with `‖yC ·‖ < 1/5` and `‖·‖ < 1`. -/
def cSL : ℂ := 1 / 20 - (1 / 8 : ℝ) * Complex.I

/-- The seven pure slots of the fourteen functions `B₁…B₅, G, G', G'', G''', B₆, B₇, ∫…`. -/
def pureIdxA : Fin 7 → Fin 14 := ![0, 1, 2, 3, 4, 9, 10]

/-- The slot of `∂_y^k G` (`k < 4`). -/
def gIdxA (k : Fin 4) : Fin 14 := ⟨5 + (k : ℕ), by omega⟩

/-- The slot of the `i`-th integral entry. -/
def iIdxA (i : Fin 3) : Fin 14 := ⟨11 + (i : ℕ), by omega⟩

/-- The jets subtracted by `tq i`: `Σ_{n<i} [yⁿ]G · y(z)ⁿ`. -/
def GjetA (a b c : ℤ) (i : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range i,
    ((PowerSeries.coeff n (Submission.CDTPlan.GZ a b c) : ℚ) : ℂ) * (yC z) ^ n

/-- The `SU`-branch of `∂_y^k G`, `G = Sym⁺H`: `∂_y^k (HU + HL∘w)`. -/
def BUg (HU HL : ℂ → ℂ) (k : ℕ) : ℂ → ℂ := DyIter k (fun z => HU z + HL (wC z))

/-- The `SU`-branch of the `i`-th integral entry: the primitive of
`y'(G^{SU} − jets)/y^i` taking at `cSU` the value of the pullback series. -/
def BUi (a b c : ℤ) (HU HL : ℂ → ℂ) (i : Fin 3) : ℂ → ℂ := fun z =>
  (∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c (iIdxA i)) : ℚ) : ℂ)
        * (yC cSU) ^ k)
    + primSeg (fun ζ => dyC ζ * (yC ζ)⁻¹ ^ (i : ℕ)
        * ((HU ζ + HL (wC ζ)) - GjetA a b c (i : ℕ) ζ)) cSU z

/-- The `SU`-branch of the pure entries: the power series of the pullback on the unit disc, and the
continuation given by `pure_pullback_cont` outside. -/
def BUp (j : Fin 7) : ℂ → ℂ := fun z =>
  if ‖z‖ < 1 then
    ∑' k : ℕ, ((PowerSeries.coeff k ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) : ℚ) : ℂ)
      * z ^ k
  else Classical.choose (pure_su_extension j) z


/-- On `SU` the pure branch agrees with the chosen extension of the pullback series. -/
lemma BUp_eq_choose (j : Fin 7) : ∀ z ∈ SU, BUp j z = Classical.choose (pure_su_extension j) z := by
  intro z hz
  by_cases h : ‖z‖ < 1
  · rw [BUp, if_pos h]
    exact ((Classical.choose_spec (pure_su_extension j)).2 z
      ⟨hz, by rwa [Metric.mem_ball, dist_zero_right]⟩).symm
  · rw [BUp, if_neg h]

/-- The pure branch is holomorphic on `SU`. -/
lemma BUp_analytic_SU (j : Fin 7) : DifferentiableOn ℂ (BUp j) SU :=
  (Classical.choose_spec (pure_su_extension j)).1 |>.congr (fun z hz => BUp_eq_choose j z hz)

/-- On the unit disc the pure branch is the pullback series. -/
lemma BUp_series (j : Fin 7) {z : ℂ} (h : ‖z‖ < 1) :
    BUp j z = ∑' k : ℕ,
      ((PowerSeries.coeff k ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) : ℚ) : ℂ)
        * z ^ k := by
  rw [BUp, if_pos h]

/-- The `SU`-branch of the fourteen pullbacks. -/
def BU (a b c : ℤ) (HU HL : ℂ → ℂ) : Fin 14 → ℂ → ℂ :=
  ![BUp 0, BUp 1, BUp 2, BUp 3, BUp 4,
    BUg HU HL 0, BUg HU HL 1, BUg HU HL 2, BUg HU HL 3,
    BUp 5, BUp 6,
    BUi a b c HU HL 0, BUi a b c HU HL 1, BUi a b c HU HL 2]

/-- The jump of the `G`-slots: `∂_y^k (D − D∘w)`. -/
def JFG (D : ℂ → ℂ) (k : ℕ) : ℂ → ℂ := DyIter k (jumpH D)

/-- The jump of the integral slots: the primitive of `y'(D − D∘w)/y^i` vanishing at `cSU`. -/
def JFI (D : ℂ → ℂ) (i : Fin 3) : ℂ → ℂ :=
  primSeg (fun ζ => dyC ζ * (yC ζ)⁻¹ ^ (i : ℕ) * jumpH D ζ) cSU

/-- The `L`-side jump of the `i`-th integral slot: the primitive of `y'(D − D∘w)/y^i` vanishing
at the base point `cSL` of `SL` (the mirror of `JFI`, whose primitive is based at `cSU`). -/
def JFI_L (D : ℂ → ℂ) (i : Fin 3) : ℂ → ℂ :=
  primSeg (fun ζ => dyC ζ * (yC ζ)⁻¹ ^ (i : ℕ) * jumpH D ζ) cSL

/-- The jump of the pure slots (it does not involve `D`). -/
def JFp (j : Fin 7) : ℂ → ℂ := fun z => BUp j z - BUp j (wC z)

/-- The jump of the fourteen pullbacks. -/
def JFA (D : ℂ → ℂ) : Fin 14 → ℂ → ℂ :=
  ![JFp 0, JFp 1, JFp 2, JFp 3, JFp 4,
    JFG D 0, JFG D 1, JFG D 2, JFG D 3,
    JFp 5, JFp 6,
    JFI D 0, JFI D 1, JFI D 2]


/-- A fixed point of the wedge `SU ∩ SL`, used to pin down the constants of the integral jumps. -/
def cWedge : ℂ := 3 + (1 / 10 : ℝ) * Complex.I

/-- The jump of the `i`-th integral entry, with the constant fixed so that it agrees with
`BUi i − (BUi i)∘w` on the wedge. -/
def JFIc (a b c : ℤ) (HU HL D : ℂ → ℂ) (i : Fin 3) : ℂ → ℂ := fun z =>
  (BUi a b c HU HL i cWedge - BUi a b c HU HL i (wC cWedge)) - JFI D i cWedge + JFI D i z

/-- The `L`-side jump of the `i`-th integral entry, recentred at `cWedge` so that it agrees with
`BUi i − (BUi i)∘w` on the wedge `SU ∩ SL`. -/
def JFIc_L (a b c : ℤ) (HU HL D : ℂ → ℂ) (i : Fin 3) : ℂ → ℂ := fun z =>
  (BUi a b c HU HL i cWedge - BUi a b c HU HL i (wC cWedge)) - JFI_L D i cWedge + JFI_L D i z

/-- The jump of the fourteen pullbacks, with the integral constants fixed at `cWedge`. -/
def JFAc (a b c : ℤ) (HU HL D : ℂ → ℂ) : Fin 14 → ℂ → ℂ :=
  ![JFp 0, JFp 1, JFp 2, JFp 3, JFp 4,
    JFG D 0, JFG D 1, JFG D 2, JFG D 3,
    JFp 5, JFp 6,
    JFIc a b c HU HL D 0, JFIc a b c HU HL D 1, JFIc a b c HU HL D 2]

/-- The left-hand side of the jump relation with the corrected integral constants. -/
def LFc (a b c : ℤ) (HU HL : ℂ → ℂ) (P : Fin 14 → Polynomial ℚ) (D : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ i : Fin 14, pAtY (P i) z * JFAc a b c HU HL D i z

/-- The left-hand side of the jump relation: `Σᵢ pᵢ(y(z))·(jump of the i-th entry)`. -/
def LF (P : Fin 14 → Polynomial ℚ) (D : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ i : Fin 14, pAtY (P i) z * JFA D i z

end

end Work.A14D
