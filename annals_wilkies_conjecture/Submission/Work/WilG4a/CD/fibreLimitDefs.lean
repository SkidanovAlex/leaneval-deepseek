/-
  WilG4a / CD / `fibreLimitDefs` — the vocabulary of `Work.WilG4a.CD.fibreLimitMem`.

  ## The construction

  Fix `p : ℕ` and `A : Set (Fin (p+2) → ℝ)`.  We want to exhibit the set

    `Z = {z : ℝ^{p+1} | ∀ε>0 ∃δ>0, the `A`-values along `t ↦ (init z, t, ·)` in the punctured
      ball of radius `δ` around `c = z (last p)` differ by at most `ε`}`

  as an `Ω`-set with format `F + const` and degree `poly(D)`.

  `Z` is equivalent to the *complement* of the set of `z` for which some `ε > 0` admits
  arbitrarily small `δ > 0` together with witnesses `t, t', v, v'`: this is a first-order
  formula over the reals with the atom `A`, and every connective/quantifier is an axiom of
  `SOMin`.  We lay out the whole formula in the single ambient space `ℝ^{p+7}` with the
  coordinate blocks

    `(z | ε | δ | t | t' | v | v')`,  `p+1 + 1 + 1 + 1 + 1 + 1 + 1 = p+7`,

  i.e. `z` on coordinates `0,…,p`, then `ε` at `p+1`, `δ` at `p+2`, `t` at `p+3`, `t'` at
  `p+4`, `v` at `p+5` and `v'` at `p+6` (the *order of elimination* by `projLast` is therefore
  `v', v, t', t, δ, ε`).

  * `Gset` is the conjunction of the seven atoms in `ℝ^{p+7}`: the two substitutions
    `(init z, t, v) ∈ A` (`iota1_y`) and `(init z, t', v') ∈ A` (`iota2_y`), the two inequalities
    `t ≠ c`, `t' ≠ c`, the two quadratic inequalities `δ² > (t-c)²`, `δ² > (t'-c)²` (which,
    together with `δ > 0`, say `|t-c| < δ` resp. `|t'-c| < δ`), and the disjunction
    `ε < v - v' ∨ ε < v' - v` (i.e. `ε < |v - v'|`).
  * `reading` is the same conjunction *read in the coordinates of a point of the form*
    `snocIt (p+3) 4 (snoc (snoc z ε) δ) w`.
  * `projChain` is the `Ω`-construction: project away `v', v, t', t`, take the complement
    (this is `ψ`), adjoin `δ > 0`, project `δ` away, complement, adjoin `ε > 0`, project `ε`
    away and complement once more.

  The two mathematical facts about this vocabulary are stated, and proved, in the sibling
  modules `Work.WilG4a.CD.fibreLimitReading` (`snocIt_mem_Gset`) and
  `Work.WilG4a.CD.fibreLimitSetEq` (`fibreCauchySet_eq_projChain`); the `Ω`-bookkeeping is in
  `Work.WilG4a.CD.fibreLimitMem` itself.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG0.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-! ## 1. The coordinate indices of `ℝ^{p+7}` -/

/-- The index of the `ε`-coordinate. -/
def iEps (p : ℕ) : Fin (p + 7) := ⟨p + 1, by omega⟩

/-- The index of the `δ`-coordinate. -/
def iDel (p : ℕ) : Fin (p + 7) := ⟨p + 2, by omega⟩

/-- The index of the `t`-coordinate. -/
def iT (p : ℕ) : Fin (p + 7) := ⟨p + 3, by omega⟩

/-- The index of the `t'`-coordinate. -/
def iT' (p : ℕ) : Fin (p + 7) := ⟨p + 4, by omega⟩

/-- The index of the `v`-coordinate. -/
def iV (p : ℕ) : Fin (p + 7) := ⟨p + 5, by omega⟩

/-- The index of the `v'`-coordinate. -/
def iV' (p : ℕ) : Fin (p + 7) := ⟨p + 6, by omega⟩

/-- The index of the last coordinate `c = z (Fin.last p)` of the `z`-block. -/
def iC (p : ℕ) : Fin (p + 7) := ⟨p, by omega⟩

/-! ## 2. The two coordinate substitutions

Both read `(init z, ·, ·)`: the first `p` coordinates of `z`, the `t`-coordinate (resp. the
`t'`-coordinate) and the `v`-coordinate (resp. the `v'`-coordinate).  They are written as
iterated `Fin.snoc` so that `Fin.comp_snoc` computes the composition with `w` for free. -/

/-- The substitution reading `(init z, t, v)` in `ℝ^{p+2}`. -/
def iota1_y (p : ℕ) : Fin (p + 2) → Fin (p + 7) :=
  Fin.snoc (Fin.snoc (fun i : Fin p => Fin.castAdd 6 (Fin.castSucc i)) (iT p)) (iV p)

/-- The substitution reading `(init z, t', v')` in `ℝ^{p+2}`. -/
def iota2_y (p : ℕ) : Fin (p + 2) → Fin (p + 7) :=
  Fin.snoc (Fin.snoc (fun i : Fin p => Fin.castAdd 6 (Fin.castSucc i)) (iT' p)) (iV' p)

/-! ## 3. The seven atoms -/

/-- The pullback of `A` along `iota1_y`: `(init z, t, v) ∈ A`. -/
def bA1 (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 7) → ℝ) :=
  {w | w ∘ iota1_y p ∈ A}

/-- The pullback of `A` along `iota2_y`: `(init z, t', v') ∈ A`. -/
def bA2 (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 7) → ℝ) :=
  {w | w ∘ iota2_y p ∈ A}

/-- The atom `t ≠ c`. -/
def bTne (p : ℕ) : Set (Fin (p + 7) → ℝ) := {w | w (iT p) ≠ w (iC p)}

/-- The atom `t' ≠ c`. -/
def bTne' (p : ℕ) : Set (Fin (p + 7) → ℝ) := {w | w (iT' p) ≠ w (iC p)}

/-- The atom `δ² > (t - c)²` (with `δ > 0` this reads `|t - c| < δ`). -/
def bQ1 (p : ℕ) : Set (Fin (p + 7) → ℝ) :=
  {w | 0 < (w (iDel p)) ^ 2 - (w (iT p) - w (iC p)) ^ 2}

/-- The atom `δ² > (t' - c)²`. -/
def bQ2 (p : ℕ) : Set (Fin (p + 7) → ℝ) :=
  {w | 0 < (w (iDel p)) ^ 2 - (w (iT' p) - w (iC p)) ^ 2}

/-- The atom `ε < |v - v'|`, written as the disjunction `ε < v - v' ∨ ε < v' - v`. -/
def bV (p : ℕ) : Set (Fin (p + 7) → ℝ) :=
  {w | w (iEps p) < w (iV p) - w (iV' p) ∨ w (iEps p) < w (iV' p) - w (iV p)}

/-- The body: the conjunction of the seven atoms, in the ambient space `ℝ^{p+7}`. -/
def Gset (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 7) → ℝ) :=
  bA1 p A ∩ bA2 p A ∩ bTne p ∩ bTne' p ∩ bQ1 p ∩ bQ2 p ∩ bV p

/-! ## 4. Reading the body in the coordinates of a projected point -/

/-- The body `Gset`, read at a point of the shape
`snocIt (p+3) 4 (Fin.snoc (Fin.snoc z ε) δ) w`, i.e. in terms of the parameters
`z, ε, δ` and the four reals `t = w 0`, `t' = w 1`, `v = w 2`, `v' = w 3`. -/
def reading (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) (z : Fin (p + 1) → ℝ) (ε δ t t' v v' : ℝ) :
    Prop :=
  0 < δ ^ 2 - (t - z (Fin.last p)) ^ 2 ∧
    0 < δ ^ 2 - (t' - z (Fin.last p)) ^ 2 ∧
    t ≠ z (Fin.last p) ∧ t' ≠ z (Fin.last p) ∧
    Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A ∧
    Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A ∧
    (ε < v - v' ∨ ε < v' - v)

/-! ## 5. The target set and the `Ω`-construction -/

-- This is the set of the statement of `fibreLimitMem`, written out.
/-- The set of `z` at which the `A`-values along the fibre `t ↦ (init z, t, ·)` form a Cauchy
family as `t` tends to `z (Fin.last p)` (excluding `t = z (Fin.last p)`). -/
def fibreCauchySet (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t t' : ℝ, t ≠ z (Fin.last p) → t' ≠ z (Fin.last p) →
      |t - z (Fin.last p)| < δ → |t' - z (Fin.last p)| < δ →
        ∀ v v' : ℝ, Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A →
          Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A → |v - v'| ≤ ε}

/-- The positivity set `{δ > 0}` in `ℝ^{p+3}` (coordinates `(z | ε | δ)`). -/
def posDelSet (p : ℕ) : Set (Fin (p + 3) → ℝ) := {u | 0 < u (Fin.last (p + 2))}

/-- The positivity set `{ε > 0}` in `ℝ^{p+2}` (coordinates `(z | ε)`). -/
def posEpsSet (p : ℕ) : Set (Fin (p + 2) → ℝ) := {u | 0 < u (Fin.last (p + 1))}

/-- The `Ω`-construction: project away `v', v, t', t` (this leaves `(z, ε, δ)`), complement,
adjoin `δ > 0`, project `δ` away, complement, adjoin `ε > 0`, project `ε` away and complement.
The result is a subset of `ℝ^{p+1}`. -/
def projChain (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  (projLast (posEpsSet p ∩
    (projLast (posDelSet p ∩ (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ))ᶜ))ᶜ

end Work.WilG4a.CD
