import Mathlib
import Submission.Work.EQ.DefsCore

/-!
# Auxiliary definitions for `Work.EQ.charVal_props`

The fan maps `fan a h ε` (Rychlik's stable fan) evaluated at `u = 0` walk on the axis
`-1/2 + 2ℤ`, and the derivative of the second coordinate of `fan a h ε` at `0` is a product of
one real factor per step of that walk (Rychlik (110)).

This file introduces, in a form free of any complex analysis,

* `stIdx n`/`stCtr n`: the centre `-1/2 + 2k` carried by the `n`-th state of the walk, indexed
  so that the walk is a nearest neighbour walk on `ℕ`: state `0` is `A₁ = -1/2`, state `2k-1`
  is the centre `-1/2 + 2k` and state `2k` is the centre `-1/2 - 2k`;
* `stQ a n`: the distance from that centre to `O₁ = -a/2`;
* `upW`/`dnW`: the moduli of the step weights;
* `stp c n`, `wtAux`, `stAux`, `nsAux`: the walk, the product of the moduli of the step
  weights, its final state and the number of non-stationary steps;
* `sgW`/`sgnAux`: the *signed* step weights, whose product is exactly the derivative of the
  second fan coordinate (all factors are negative except the stationary step at `A₁`).
-/

namespace Work.EQ

open Complex

/-- The centre carried by state `n`: state `0` is `A₁ = -1/2`, state `2k-1` is the centre
`-1/2 + 2k` and state `2k` is the centre `-1/2 - 2k` (`k ≥ 1`). Thus `stIdx` is the integer
`k` with `stCtr n = -1/2 + 2k`. -/
def stIdx (n : ℕ) : ℤ := if n % 2 = 1 then ((n + 1) / 2 : ℕ) else -((n / 2 : ℕ) : ℤ)

/-- The `x`-coordinate of the centre carried by state `n`. -/
noncomputable def stCtr (n : ℕ) : ℝ := -1 / 2 + 2 * (stIdx n : ℝ)

/-- The distance from the centre carried by state `n` to `O₁ = -a/2`. -/
noncomputable def stQ (a : ℝ) (n : ℕ) : ℝ := |stCtr n + a / 2|

/-- Modulus of the derivative weight of a non-principal (`F`) step taken from state `n`. -/
noncomputable def upW (a : ℝ) (n : ℕ) : ℝ := eqLam a * (1 + 1 / stQ a n)

/-- The (signed) derivative weight of a principal (`T`) step taken from state `n`; it equals
`-1` at `A₁`, where the principal step is the stationary one. -/
noncomputable def dnW (a : ℝ) (n : ℕ) : ℝ := eqLam a * (1 - 1 / stQ a n)

/-- The next state of the walk after reading the letter `c` in state `n`
(`true` = principal step `T`, `false` = non-principal step `F`). -/
def stp (c : Bool) (n : ℕ) : ℕ := if c then (if n = 0 then 0 else n - 1) else n + 1

/-- Modulus of the weight of the step reading `c` in state `n`. -/
noncomputable def stW (a : ℝ) (c : Bool) (n : ℕ) : ℝ := if c then |dnW a n| else upW a n

/-- The signed weight of the step reading `c` in state `n`; it is the actual quotient of
derivatives contributed by that step. -/
noncomputable def sgW (a : ℝ) (c : Bool) (n : ℕ) : ℝ := if c then -dnW a n else -upW a n

/-- Product of the moduli of the step weights along a word, started in state `n`. -/
noncomputable def wtAux (a : ℝ) : List Bool → ℕ → ℝ
  | [], _ => 1
  | c :: l, n => stW a c n * wtAux a l (stp c n)

/-- Product of the signed step weights along a word, started in state `n`. -/
noncomputable def sgnAux (a : ℝ) : List Bool → ℕ → ℝ
  | [], _ => 1
  | c :: l, n => sgW a c n * sgnAux a l (stp c n)

/-- The final state of the walk started in state `n`. -/
def stAux : List Bool → ℕ → ℕ
  | [], n => n
  | c :: l, n => stAux l (stp c n)

/-- Number of non-stationary steps (`F` steps, and `T` steps taken away from `A₁`) of a word
started in state `n`. -/
def nsAux : List Bool → ℕ → ℕ
  | [], _ => 0
  | c :: l, n => (if c ∧ n = 0 then 0 else 1) + nsAux l (stp c n)

/-- The contracting potential of the walk: `Φ n = ∏_{j<n} upW a j`. -/
noncomputable def Phi (a : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, upW a j

/-- The centre of `fan a h ε` is `stCtr` of the state reached by the letters of `ε` read in
their chronological order, i.e. from the tail of `ε` towards its head. -/
noncomputable def ctrOf (ε : List Bool) : ℝ := stCtr (stAux ε.reverse 0)

@[simp] lemma stAux_nil (n : ℕ) : stAux [] n = n := rfl
@[simp] lemma stAux_cons (c : Bool) (l : List Bool) (n : ℕ) :
    stAux (c :: l) n = stAux l (stp c n) := rfl
@[simp] lemma wtAux_nil (a : ℝ) (n : ℕ) : wtAux a [] n = 1 := rfl
@[simp] lemma wtAux_cons (a : ℝ) (c : Bool) (l : List Bool) (n : ℕ) :
    wtAux a (c :: l) n = stW a c n * wtAux a l (stp c n) := rfl
@[simp] lemma sgnAux_nil (a : ℝ) (n : ℕ) : sgnAux a [] n = 1 := rfl
@[simp] lemma sgnAux_cons (a : ℝ) (c : Bool) (l : List Bool) (n : ℕ) :
    sgnAux a (c :: l) n = sgW a c n * sgnAux a l (stp c n) := rfl
@[simp] lemma nsAux_nil (n : ℕ) : nsAux [] n = 0 := rfl
@[simp] lemma nsAux_cons (c : Bool) (l : List Bool) (n : ℕ) :
    nsAux (c :: l) n = (if c ∧ n = 0 then 0 else 1) + nsAux l (stp c n) := rfl

/-- The walk is a semigroup action: processing `l₁ ++ l₂` from state `n` processes `l₂` from
the state reached after `l₁`. -/
@[simp] lemma stAux_append (l₁ l₂ : List Bool) (n : ℕ) :
    stAux (l₁ ++ l₂) n = stAux l₂ (stAux l₁ n) := by
  induction l₁ generalizing n with
  | nil => rfl
  | cons c l ih => simp [ih]

lemma wtAux_append (a : ℝ) (l₁ l₂ : List Bool) (n : ℕ) :
    wtAux a (l₁ ++ l₂) n = wtAux a l₁ n * wtAux a l₂ (stAux l₁ n) := by
  induction l₁ generalizing n with
  | nil => simp
  | cons c l ih => simp [ih, mul_assoc]

lemma sgnAux_append (a : ℝ) (l₁ l₂ : List Bool) (n : ℕ) :
    sgnAux a (l₁ ++ l₂) n = sgnAux a l₁ n * sgnAux a l₂ (stAux l₁ n) := by
  induction l₁ generalizing n with
  | nil => simp
  | cons c l ih => simp [ih, mul_assoc]

lemma nsAux_append (l₁ l₂ : List Bool) (n : ℕ) :
    nsAux (l₁ ++ l₂) n = nsAux l₁ n + nsAux l₂ (stAux l₁ n) := by
  induction l₁ generalizing n with
  | nil => simp
  | cons c l ih => simp [ih]; omega

end Work.EQ
