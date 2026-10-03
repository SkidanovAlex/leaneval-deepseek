import Mathlib
import Submission.Work.Peluse.SwapE.Defs

/-!
# `cubeMass` — vocabulary for the passage `massAvg ⟹ boxNormPow`

Support module for `Work.Peluse.SwapE.MassToCube` (`Submission/Work/Peluse/SwapE/massToCube.lean`).

The endgame hypothesis is that the average of the cube mass `‖boxMass d (symIcc N) f n‖` over the
slot box `massBox d H M = [±2HM]^d` dominates `θ`; the conclusion is a lower bound for the
`(d+1)`-fold box-norm power of `f` at the slot window `arithIcc 1 (massBoxCard H M)`.

Write `Card := massBoxCard H M = 4HM+1` (so that `arithIcc 1 Card` is a translate of `symIcc (2HM)`
of cardinality `Card`), and

* `aN t f u x = ∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·u)` — the `2^t`-fold cube term of `f` along
  the directions `u` (the `ω = 0` corner at `x`).  It is exactly the summand of
  `Work.Peluse.Concat.Wf t (fun _ => f) u`, so `Wf` is the `∑'_x` of `aN`;
* `Ncard Card v = Card - |v|` — the exact number of pairs `(a,b) ∈ [1,Card]²` with `a - b = v`;
* `Wt Card t u = ∏_i Ncard Card (u i)` — the multiplicity of the difference `u` in the product
  `[1,Card]^t`, i.e. the number of pairs `(h,h')` of tuples with `h - h' = u`;
* `sCard Card = [1-Card, Card-1]` and `Tdir Card t = (sCard Card)^t` — the finite set of differences
  of tuples in `[1,Card]^t`;
* `bNf Card t f u z = ∑_{v ∈ [1,Card]} aN t f u (z + v)` — the Fejér slot of the cube term `aN t f u`.

The whole passage rests on the *fiber identity*: for a finite set `Q` and `Φ : ℤ → ℂ`,
`∑_{a,b∈Q}Φ(a-b) = ∑_v #{(a,b)∈Q² : a-b=v} · Φ(v)`; iterated over the `t` coordinates, with
`Q = [1,Card]` this is `∑_{h,h'}Φ(h-h') = ∑_u Wt Card t u · Φ u`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse

/-- The `2^t`-fold cube term of `f` along the directions `u`, as a function of the corner `x`:
`aN t f u x = ∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·u)`. -/
def aN (t : ℕ) (f : ℤ → ℂ) (u : Fin t → ℤ) : ℤ → ℂ :=
  fun x => ∏ ω : Fin t → Bool,
    (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift u 0 ω))

/-- `Wf` of a constant family is the sum over the corner of `aN`. -/
lemma Wf_const (t : ℕ) (f : ℤ → ℂ) (u : Fin t → ℤ) :
    Work.Peluse.Concat.Wf t (fun _ : Fin t → Bool => f) u = ∑' x : ℤ, aN t f u x := rfl

/-- The number `#{(a,b) ∈ [1,Card]² : a - b = v} = Card - |v|` (interpreted as `0` for `|v| ≥ Card`
through the truncated subtraction). -/
def Ncard (Card : ℕ) (v : ℤ) : ℕ := Card - v.natAbs

/-- The multiplicity of the difference `u` in the product `[1,Card]^t`. -/
def Wt (Card : ℕ) (t : ℕ) (u : Fin t → ℤ) : ℕ := ∏ i : Fin t, Ncard Card (u i)

/-- The one-dimensional set of differences of pairs in `[1,Card]`. -/
def sCard (Card : ℕ) : Finset ℤ := Finset.Icc (1 - (Card : ℤ)) ((Card : ℤ) - 1)

/-- The finite set of differences of tuples in `[1,Card]^t`. -/
def Tdir (Card t : ℕ) : Finset (Fin t → ℤ) := Fintype.piFinset (fun _ : Fin t => sCard Card)

/-- The Fejér slot of the cube term: the sum of `aN t f u` over the window `[1,Card]`. -/
def bNf (Card : ℕ) (t : ℕ) (f : ℤ → ℂ) (u : Fin t → ℤ) : ℤ → ℂ :=
  fun z => ∑ v ∈ arithIcc 1 Card, aN t f u (z + v)

/-- The normalising constant of the box norm at the direction family `Q` and window `S`:
`(|S| ∏_i |Q i|²)⁻¹`, in the parenthesisation used by the fold identity. -/
def boxConst (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) : ℝ :=
  (((S.card : ℝ))⁻¹ * (∏ i, (((Q i).card : ℝ))⁻¹)) * (∏ i, (((Q i).card : ℝ))⁻¹)

/-- The complex version of `boxConst`, in the shape produced by `prodCubeSum_fold_gen`. -/
def boxConstC (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) : ℂ :=
  (((S.card : ℂ))⁻¹ * (∏ i, (((Q i).card : ℂ))⁻¹)) * (∏ i, (((Q i).card : ℂ))⁻¹)

@[simp] lemma mem_sCard {Card : ℕ} {v : ℤ} :
    v ∈ sCard Card ↔ 1 - (Card : ℤ) ≤ v ∧ v ≤ (Card : ℤ) - 1 := Finset.mem_Icc

@[simp] lemma mem_Tdir {Card t : ℕ} {u : Fin t → ℤ} :
    u ∈ Tdir Card t ↔ ∀ i : Fin t, u i ∈ sCard Card := Fintype.mem_piFinset

lemma sCard_card (Card : ℕ) (h : 1 ≤ Card) : (sCard Card).card = 2 * Card - 1 := by
  rw [sCard, Int.card_Icc]
  have h1 : (1 : ℤ) ≤ (Card : ℤ) := by exact_mod_cast h
  have h2n : (1 : ℤ) ≤ (2 : ℤ) * (Card : ℤ) := by linarith
  have h2 : ((Card : ℤ) - 1 + 1 - (1 - (Card : ℤ))) = ((2 * Card - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * Card)]
    push_cast
    ring
  rw [h2, Int.toNat_natCast]

lemma Ncard_eq_zero_of_le {Card : ℕ} {v : ℤ} (h : (Card : ℤ) ≤ |v|) : Ncard Card v = 0 := by
  simp only [Ncard]
  have h' : Card ≤ v.natAbs := by
    have h2 : (((v.natAbs : ℕ)) : ℤ) = |v| := Int.natCast_natAbs v
    omega
  omega

lemma Ncard_nonneg (Card : ℕ) (v : ℤ) : 0 ≤ (Ncard Card v : ℤ) := by
  simp only [Ncard]; positivity

lemma Ncard_pos {Card : ℕ} {v : ℤ} (h : v ∈ sCard Card) : 0 < Ncard Card v := by
  rw [mem_sCard] at h
  simp only [Ncard]
  have h2 : v.natAbs ≤ Card - 1 := by
    have h2' : |v| ≤ ((Card : ℤ) - 1) := abs_le.mpr ⟨by linarith, h.2⟩
    have h3 : (((v.natAbs : ℕ)) : ℤ) = |v| := Int.natCast_natAbs v
    have h4 : (((v.natAbs : ℕ)) : ℤ) ≤ ((Card : ℤ) - 1) := by rw [h3]; exact h2'
    omega
  omega

lemma Ncard_eq {Card : ℕ} {v : ℤ} (h : |v| ≤ (Card : ℤ)) : Ncard Card v = Card - |v|.toNat := by
  simp only [Ncard]
  have h2 : (((v.natAbs : ℕ)) : ℤ) = |v| := Int.natCast_natAbs v
  have : v.natAbs ≤ Card := by omega
  omega

lemma Wt_nonneg (Card t : ℕ) (u : Fin t → ℤ) : 0 ≤ Wt Card t u := by
  simp only [Wt]; positivity

lemma Wt_eq_zero_of_notMem {Card t : ℕ} {u : Fin t → ℤ} (h : u ∉ Tdir Card t) :
    Wt Card t u = 0 := by
  rw [mem_Tdir] at h
  simp only [not_forall] at h
  obtain ⟨i, hi⟩ := h
  rw [mem_sCard, not_and_or] at hi
  rw [Wt]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rcases hi with hi | hi
  · rw [not_le] at hi
    have hle : (Card : ℤ) ≤ |u i| := by
      rw [abs_of_nonpos (by linarith : u i ≤ 0)]
      linarith
    exact Ncard_eq_zero_of_le hle
  · rw [not_le] at hi
    have hle : (Card : ℤ) ≤ |u i| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ u i)]
      linarith
    exact Ncard_eq_zero_of_le hle

end

end Work.Peluse.SwapE
