/-
  WilE6 (area E6): fibrewise closure and frontier of EA sets (Gabrielov 1998).

  This file: the semialgebraic set `critSA` that encodes the Taylor-closure criterion
  (E3b / Gabrielov–Vorobjov Cor. 4.5) in the `(z', z, h)`-space, in the shifted form
  `z' = z + u` that is needed for the `E4`-application in `Closure.lean`.

  Input: the Taylor polynomials of the atoms (as produced by `eaTaylor_poly_shifted`):
  * `P`  — the Taylor polynomial of the (merged) equation of the basic set,
  * `Gs` — the Taylor polynomials of the positivity atoms.
  Each is a polynomial in the variables `Fin k ⊕ Fin (k+r)` = (u, (z,h)).

  The ambient space of `critSA` is `Fin (BP + FQ)` with
    base  `BP = k + r`  : the `z`-coordinates (k) then the `h`-variables (r),
    fibre `FQ = 2k + 2p + 4` : `u : Fin k`, `t : Fin 1`, `wm : Fin k`, `w0 : Fin 1`,
                              `wb : Fin (2p)`, `we : Fin 2`.

  The fibre point is `(u, t, wm, w0, wb, we)`:
  * `u` is the shift `z' - z`;
  * `t` is the distance `dist z' z` (witnessed polynomially, see `norm_witness_iff`);
  * `wm` witnesses the inequalities `u_i^2 <= t^2` (the sup-norm attaining conditions);
  * `w0` witnesses `0 <= t`;
  * `wb` witnesses the criterion conditions `|u_i| <= t^(κ^2)` for the base-fixing atoms
    `z'_i - z_i = 0` (i < p) of the frozen-base reduction;
  * `we` witnesses the criterion conditions `|P u z h| <= t^(κ^2)` for the equation.

  At the fibre point `0` all these witnesses are determined (they are `0`), which is why the
  slice at `0` of the `E4`-closure can be taken by substituting `0`.
-/
import Submission.Work.WilE6.Base

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE6
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {k r p : ℕ}

/-- The number of base coordinates of the `critSA` ambient space: the `z`-variables (k) and
the chain variables `h` (r). -/
def BP (k r : ℕ) : ℕ := k + r

/-- The number of fibre coordinates: `u` (k), `t` (1), `wm` (k), `w0` (1), `wb` (2p), `we` (2).-/
def FQ (k p : ℕ) : ℕ := 2 * k + 2 * p + 4

/-! ### Accessors for the ambient coordinates -/

@[simp] theorem BP_eq (k r : ℕ) : BP k r = k + r := rfl
@[simp] theorem FQ_eq (k p : ℕ) : FQ k p = 2 * k + 2 * p + 4 := rfl

/-- The `z`-coordinates (the first `k` base coordinates). -/
def idxZ (k r p : ℕ) (i : Fin k) : Fin (BP k r + FQ k p) := ⟨i.1, by simp [BP, FQ]; omega⟩

/-- The `h`-variables (the last `r` base coordinates). -/
def idxH (k r p : ℕ) (j : Fin r) : Fin (BP k r + FQ k p) :=
  ⟨k + j.1, by simp [BP, FQ]; omega⟩

/-- The `u`-coordinates (the shift `z' - z`). -/
def idxU (k r p : ℕ) (i : Fin k) : Fin (BP k r + FQ k p) :=
  ⟨BP k r + i.1, by simp [BP, FQ]; omega⟩

/-- The `t`-coordinate (the distance). -/
def idxT (k r p : ℕ) : Fin (BP k r + FQ k p) :=
  ⟨BP k r + k, by simp [BP, FQ]; omega⟩

/-- The witnesses `wm` for `u_i^2 <= t^2`. -/
def idxWm (k r p : ℕ) (i : Fin k) : Fin (BP k r + FQ k p) :=
  ⟨BP k r + k + 1 + i.1, by simp [BP, FQ]; omega⟩

/-- The witness `w0` for `0 <= t`. -/
def idxW0 (k r p : ℕ) : Fin (BP k r + FQ k p) :=
  ⟨BP k r + 2 * k + 1, by simp [BP, FQ]; omega⟩

/-- The witnesses `wb` for the base-fixing atoms. -/
def idxWb (k r p : ℕ) (j : Fin (2 * p)) : Fin (BP k r + FQ k p) :=
  ⟨BP k r + 2 * k + 2 + j.1, by simp [BP, FQ]; omega⟩

/-- The witnesses `we` for the equation. -/
def idxWe (k r p : ℕ) (j : Fin 2) : Fin (BP k r + FQ k p) :=
  ⟨BP k r + 2 * k + 2 + 2 * p + j.1, by simp [BP, FQ]; omega⟩

/-- The variable map taking the `(u, (z,h))`-variables of the Taylor polynomials into the
`critSA` ambient space. -/
def idxPhi (k r p : ℕ) : Fin k ⊕ Fin (k + r) → Fin (BP k r + FQ k p) :=
  fun x => match x with
    | Sum.inl i => idxU k r p i
    | Sum.inr y => Fin.addCases (fun i => idxZ k r p i) (fun j => idxH k r p j) y

@[simp] theorem idxPhi_inl (i : Fin k) : idxPhi k r p (Sum.inl i) = idxU k r p i := rfl
@[simp] theorem idxPhi_inr_castAdd (i : Fin k) :
    idxPhi k r p (Sum.inr (Fin.castAdd r i)) = idxZ k r p i := by
  simp only [idxPhi, Fin.addCases_left]
@[simp] theorem idxPhi_inr_natAdd (j : Fin r) :
    idxPhi k r p (Sum.inr (Fin.natAdd k j)) = idxH k r p j := by
  simp only [idxPhi, Fin.addCases_right]

/-! ### The polynomials of the criterion set -/

/-- The `z_i`-variable. -/
def polZ (k r p : ℕ) (i : Fin k) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  MvPolynomial.X (idxZ k r p i)
/-- The `h_j`-variable. -/
def polH (k r p : ℕ) (j : Fin r) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  MvPolynomial.X (idxH k r p j)
/-- The `u_i`-variable. -/
def polU (k r p : ℕ) (i : Fin k) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  MvPolynomial.X (idxU k r p i)
/-- The `t`-variable. -/
def polT (k r p : ℕ) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ := MvPolynomial.X (idxT k r p)
/-- The `wm_i`-variable. -/
def polWm (k r p : ℕ) (i : Fin k) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  MvPolynomial.X (idxWm k r p i)
/-- The `w0`-variable. -/
def polW0 (k r p : ℕ) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ := MvPolynomial.X (idxW0 k r p)
/-- The `wb_j`-variable. -/
def polWb (k r p : ℕ) (j : Fin (2 * p)) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  MvPolynomial.X (idxWb k r p j)
/-- The `we_j`-variable. -/
def polWe (k r p : ℕ) (j : Fin 2) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  MvPolynomial.X (idxWe k r p j)

/-- `t^(κ^2)`, the threshold appearing in the criterion for the equations. -/
def polThr2 (k r p : ℕ) (κ : ℕ) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ := polT k r p ^ (κ ^ 2)

/-- `t^κ`, the threshold appearing in the criterion for the positivity atoms. -/
def polThr1 (k r p : ℕ) (κ : ℕ) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ := polT k r p ^ κ

/-- The witness equation `u_i^2 - t^2 + wm_i^2 = 0` (the attains-the-sup-norm condition). -/
def atomMax (k r p : ℕ) (i : Fin k) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  polU k r p i ^ 2 - polT k r p ^ 2 + polWm k r p i ^ 2

/-- The equation `t - w0^2 = 0` (witnessing `0 ≤ t`). -/
def atomT0 (k r p : ℕ) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  polT k r p - polW0 k r p ^ 2

/-- The equation `u_j^2 - t^2 = 0` (the attained `j`-th coordinate). -/
def atomJ (k r p : ℕ) (j : Fin k) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  polU k r p j ^ 2 - polT k r p ^ 2

/-- The equation `t = 0` (the degenerate `k = 0` case). -/
def atomTz (k r p : ℕ) : MvPolynomial (Fin (BP k r + FQ k p)) ℝ := polT k r p

theorem div2_lt {k p : ℕ} (hp : p ≤ k) (j : Fin (2 * p)) : j.1 / 2 < k := by
  have h : j.1 / 2 < p := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
    have := j.2; omega
  omega

/-- The witness equation `±u_i - t^(κ^2) + wb_j^2 = 0` for the base-fixing atoms. -/
def atomWb (k r p : ℕ) (hp : p ≤ k) (κ : ℕ) (j : Fin (2 * p))
    : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  (if (j.1 % 2 == 0) then polU k r p ⟨j.1 / 2, div2_lt hp j⟩
    else -polU k r p ⟨j.1 / 2, div2_lt hp j⟩)
    - polThr2 k r p κ + polWb k r p j ^ 2

/-- The witness equation `±P - t^(κ^2) + we_j^2 = 0` for the (merged) equation. -/
def atomWe (k r p : ℕ) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ) (j : Fin 2)
    : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  (if j = 0 then (MvPolynomial.rename (idxPhi k r p) P) else -(MvPolynomial.rename (idxPhi k r p) P))
    - polThr2 k r p κ + polWe k r p j ^ 2

/-- The strict inequality `t^κ < P_g` for a positivity atom. -/
def atomPos (k r p : ℕ) (κ : ℕ) (G : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    : MvPolynomial (Fin (BP k r + FQ k p)) ℝ :=
  MvPolynomial.rename (idxPhi k r p) G - polThr1 k r p κ

/-! ### The semialgebraic set -/

/-- The basic set (one `DNF` piece) of the criterion: all the witness equations together with
the strict positivity conditions, for a fixed attained index `j`. -/
def critBasic (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (j : Fin (k + 1))
    : Basic (BP k r + FQ k p) 0 :=
  let eqs1 : List (EAPoly (BP k r + FQ k p) 0) :=
    (List.finRange k).map (fun i => saPoly _ (atomMax k r p i))
  let eqs2 : List (EAPoly (BP k r + FQ k p) 0) :=
    (if h : (j : ℕ) < k then [saPoly _ (atomJ k r p ⟨j, h⟩)]
      else [saPoly _ (atomTz k r p)])
  let eqs3 : List (EAPoly (BP k r + FQ k p) 0) := [saPoly _ (atomT0 k r p)]
  let eqs4 : List (EAPoly (BP k r + FQ k p) 0) :=
    (List.finRange (2 * p)).map (fun i => saPoly _ (atomWb k r p hp κ i))
  let eqs5 : List (EAPoly (BP k r + FQ k p) 0) :=
    (List.finRange 2).map (fun i => saPoly _ (atomWe k r p κ P i))
  ⟨eqs1 ++ eqs2 ++ eqs3 ++ eqs4 ++ eqs5, Gs.map (fun G => saPoly _ (atomPos k r p κ G))⟩

/-- The semialgebraic description of the Taylor criterion for the (merged) basic set with
equation `P` and positivity atoms `Gs`. -/
def critSA (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) : SA (BP k r + FQ k p) where
  basics := (List.finRange (k + 1)).map (critBasic (p := p) hp κ P Gs)

/-- The fibre conditions of the `j`-th `DNF` piece of `critSA`, at a point of the ambient
space.  These are the witness equations for the sup-norm attainment, the base-fixing atoms and
the (merged) equation, together with the strict positivity atoms. -/
def critFibreCond (hp : p ≤ k) (κ : ℕ) (P : MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)
    (Gs : List (MvPolynomial (Fin k ⊕ Fin (k + r)) ℝ)) (j : Fin (k + 1))
    (pnt : Fin (BP k r + FQ k p) → ℝ) : Prop :=
  (∀ i, pnt (idxU k r p i) ^ 2 - pnt (idxT k r p) ^ 2 + pnt (idxWm k r p i) ^ 2 = 0) ∧
  (if h : (j : ℕ) < k then pnt (idxU k r p ⟨j, h⟩) ^ 2 - pnt (idxT k r p) ^ 2 = 0
    else pnt (idxT k r p) = 0) ∧
  (pnt (idxT k r p) - pnt (idxW0 k r p) ^ 2 = 0) ∧
  (∀ b : Fin (2 * p), pnt (idxWb k r p b) ^ 2
      + (if (b.1 % 2 == 0) then pnt (idxU k r p ⟨b.1 / 2, div2_lt hp b⟩)
        else -pnt (idxU k r p ⟨b.1 / 2, div2_lt hp b⟩)) - pnt (idxT k r p) ^ (κ ^ 2) = 0) ∧
  (∀ e : Fin 2, pnt (idxWe k r p e) ^ 2
      + (if e = 0 then MvPolynomial.eval (fun i => pnt (idxPhi k r p i)) P
        else -MvPolynomial.eval (fun i => pnt (idxPhi k r p i)) P) - pnt (idxT k r p) ^ (κ ^ 2) = 0) ∧
  (∀ G ∈ Gs, pnt (idxT k r p) ^ κ < MvPolynomial.eval (fun i => pnt (idxPhi k r p i)) G)

end Work.WilE6
