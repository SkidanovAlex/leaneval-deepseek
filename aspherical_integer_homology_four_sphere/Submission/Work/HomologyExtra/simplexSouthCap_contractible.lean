import Mathlib
import Submission.Work.HomologyExtra.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The south cap of the simplex boundary is contractible

Let `∂Δⁿ⁺¹` be the boundary of the standard `(n+1)`-simplex, modelled as
`boundarySpace (n+1)`.  The **south cap**

`simplexSouthCap n = {x ∈ ∂Δⁿ⁺¹ | x_last < 1}`

is `∂Δⁿ⁺¹` with the vertex `e_last` removed; as `∂Δⁿ⁺¹ ≅ Sⁿ` this is an open
`n`-disk, hence contractible.  Here we give a completely explicit contraction.

Write the weights of `x ∈ ∂Δⁿ⁺¹` as `w` and put `t = w_last ∈ [0,1)`.  The face
`F = {w_last = 0} ≅ Δⁿ` is a closed disk.  The proof contracts the cap in two
stages:

* first it retracts every point to the face `F`, by radially rescaling the
  "away from the last vertex" coordinates, `r(w)_i = w_i/(1-t)` for `i ≠ last`
  and `r(w)_last = 0` (the straight-line homotopy `(1-s) w + s r(w)` stays in
  the boundary, because the zeros of `w` among the coordinates `≠ last` are
  preserved, or else `w_last = 0` persists);
* then it contracts the convex face `F` to the vertex `e_0` by the straight-line
  homotopy `(1-s) r(w) + s e_0`.

Both stages are explicit weight formulas, and the concatenation is a homotopy
from the identity to the constant map at `e_0`.
-/

open scoped BigOperators

namespace Work.HomologyExtra

noncomputable section

open Convexity

/-- A point of the standard simplex, built from its weight function. -/
def mkSimplex {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i) (h2 : ∑ i, g i = 1) :
    Convexity.StdSimplex ℝ (Fin N) :=
  ⟨Finsupp.equivFunOnFinite.symm g, fun i => by simpa using h1 i, by
    rw [Finsupp.sum_fintype]
    · exact h2
    · intro i; simp⟩

@[simp] theorem mkSimplex_weights {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i)
    (h2 : ∑ i, g i = 1) (i : Fin N) : (mkSimplex g h1 h2).weights i = g i := by
  simp [mkSimplex]

/-- Two points of the south cap agree as soon as their underlying simplex points do. -/
theorem southCap_ext {n : ℕ} {x y : ↥(simplexSouthCap n)} (h : x.1.1 = y.1.1) : x = y := by
  apply Subtype.ext; apply Subtype.ext; exact h

/-- The last vertex index is not the zeroth one. -/
theorem last_ne_zero (n : ℕ) : (Fin.last (n+1) : Fin (n+2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_last] at this

/-! ## The retraction of the cap onto the face `{w_last = 0}` -/

/-- Weight function of the "face projection": normalise the coordinates away from the last
vertex, and set the last coordinate to `0`. -/
def southRetrW (n : ℕ) (x : ↥(simplexSouthCap n)) (i : Fin (n+2)) : ℝ :=
  if i = Fin.last (n+1) then 0
  else x.1.1.weights i / (1 - x.1.1.weights (Fin.last (n+1)))

theorem southRetrW_last (n : ℕ) (x : ↥(simplexSouthCap n)) :
    southRetrW n x (Fin.last (n+1)) = 0 := by
  rw [southRetrW, ite_eq_left rfl]

theorem continuous_southRetrW (n : ℕ) (i : Fin (n+2)) :
    Continuous (fun x : ↥(simplexSouthCap n) => southRetrW n x i) := by
  by_cases h : i = Fin.last (n+1)
  · subst h
    simp only [southRetrW, ite_true]
    exact continuous_const
  · rw [show (fun x : ↥(simplexSouthCap n) => southRetrW n x i)
        = (fun x : ↥(simplexSouthCap n) =>
            x.1.1.weights i / (1 - x.1.1.weights (Fin.last (n+1)))) by
      funext x; rw [southRetrW, ite_eq_right h]]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      have ht : x.1.1.weights (Fin.last (n+1)) < 1 := x.2
      linarith

theorem southRetrW_nonneg (n : ℕ) (x : ↥(simplexSouthCap n)) (i : Fin (n+2)) :
    0 ≤ southRetrW n x i := by
  rw [southRetrW]
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact x.1.1.weights_nonneg i
    · have ht : x.1.1.weights (Fin.last (n+1)) < 1 := x.2
      linarith

/-- A single term of a sum over `Fin N` that is zeroed at one index. -/
theorem sum_ite_zero_sub {N : ℕ} (a : Fin N) (f : Fin N → ℝ) :
    (∑ i, (if i = a then (0:ℝ) else f i)) = (∑ i, f i) - f a := by
  have hmem : a ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ a
  have h1 : (∑ i, (if i = a then (0:ℝ) else f i)) = (Finset.univ.erase a).sum f := by
    rw [← Finset.sum_erase_add _ (fun i => if i = a then (0:ℝ) else f i) hmem]
    rw [ite_eq_left rfl, add_zero]
    exact Finset.sum_congr rfl fun x hx => by
      rw [Finset.mem_erase] at hx
      rw [ite_eq_right hx.1]
  have h2 : (Finset.univ.erase a).sum f + f a = ∑ i, f i :=
    Finset.sum_erase_add _ f hmem
  linarith

theorem southRetrW_sum (n : ℕ) (x : ↥(simplexSouthCap n)) :
    ∑ i, southRetrW n x i = 1 := by
  set t := x.1.1.weights (Fin.last (n+1)) with htdef
  have ht : t < 1 := x.2
  have hsum : ∑ i : Fin (n+2), x.1.1.weights i = 1 :=
    Convexity.StdSimplex.total_of_fintype x.1.1
  have hkey : (∑ i, southRetrW n x i) =
      (∑ i, x.1.1.weights i / (1 - t)) - t / (1 - t) := by
    simp only [southRetrW, htdef]
    exact sum_ite_zero_sub _ _
  have h1 : (∑ i, x.1.1.weights i / (1 - t)) = (∑ i, x.1.1.weights i) / (1 - t) := by
    simp only [Finset.sum_div]
  rw [hkey, h1, hsum]
  have hne : (1 : ℝ) - t ≠ 0 := by linarith
  field_simp

/-- The retraction point, as a point of the standard simplex. -/
def southRetrPoint (n : ℕ) (x : ↥(simplexSouthCap n)) : Convexity.StdSimplex ℝ (Fin (n+2)) :=
  mkSimplex (southRetrW n x) (southRetrW_nonneg n x) (southRetrW_sum n x)

theorem southRetrPoint_last (n : ℕ) (x : ↥(simplexSouthCap n)) :
    (southRetrPoint n x).weights (Fin.last (n+1)) = 0 := by
  rw [southRetrPoint, mkSimplex_weights, southRetrW_last]

theorem continuous_southRetrPoint (n : ℕ) :
    Continuous (fun x : ↥(simplexSouthCap n) => southRetrPoint n x) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  have key : (fun x : ↥(simplexSouthCap n) => (southRetrPoint n x).weights i)
      = (fun x : ↥(simplexSouthCap n) => southRetrW n x i) := by
    funext x; rw [southRetrPoint, mkSimplex_weights]
  change Continuous (fun a : ↥(simplexSouthCap n) => (southRetrPoint n a).weights i)
  rw [key]
  exact continuous_southRetrW n i

/-- The retraction point, as a point of the boundary of the simplex. -/
def southRetrFun (n : ℕ) (x : ↥(simplexSouthCap n)) : boundarySpace (n+1) :=
  ⟨southRetrPoint n x, ⟨Fin.last (n+1), southRetrPoint_last n x⟩⟩

/-- The retraction of the south cap onto the face `{w_last = 0}`. -/
def southRetr (n : ℕ) (x : ↥(simplexSouthCap n)) : ↥(simplexSouthCap n) :=
  ⟨southRetrFun n x, by
      show (southRetrFun n x).1.weights (Fin.last (n+1)) < 1
      rw [southRetrFun]; simp [southRetrPoint_last]⟩

theorem continuous_southRetr (n : ℕ) : Continuous (southRetr n) :=
  Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_southRetrPoint n)
      (fun x => ⟨Fin.last (n+1), southRetrPoint_last n x⟩))
    (fun x => by
      show (southRetrFun n x).1.weights (Fin.last (n+1)) < 1
      rw [southRetrFun]; simp [southRetrPoint_last])

/-- The retraction as a continuous map. -/
def southRetrCM (n : ℕ) : C(↥(simplexSouthCap n), ↥(simplexSouthCap n)) :=
  ⟨southRetr n, continuous_southRetr n⟩

/-! ## Stage 1: a homotopy from the identity to the retraction -/

/-- Weight function of the first stage homotopy: the straight line from `x` to `r x`. -/
def H1W (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) (i : Fin (n+2)) : ℝ :=
  (1 - (q.1:ℝ)) * q.2.1.1.weights i + (q.1:ℝ) * southRetrW n q.2 i

theorem H1W_nonneg (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) (i : Fin (n+2)) :
    0 ≤ H1W n q i := by
  show (0:ℝ) ≤ (1 - (q.1:ℝ)) * q.2.1.1.weights i + (q.1:ℝ) * southRetrW n q.2 i
  have hs0 : (0:ℝ) ≤ (q.1:ℝ) := q.1.2.1
  have hs1 : (q.1:ℝ) ≤ 1 := q.1.2.2
  have h1 : 0 ≤ 1 - (q.1:ℝ) := by linarith
  have h2 : 0 ≤ q.2.1.1.weights i := q.2.1.1.weights_nonneg i
  have h3 : 0 ≤ southRetrW n q.2 i := southRetrW_nonneg n q.2 i
  have ha := mul_nonneg h1 h2
  have hb := mul_nonneg hs0 h3
  linarith

theorem H1W_sum (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    ∑ i, H1W n q i = 1 := by
  have hsplit : (∑ i, H1W n q i)
      = (∑ i, (1 - (q.1:ℝ)) * q.2.1.1.weights i)
        + (∑ i, (q.1:ℝ) * southRetrW n q.2 i) := by
    simp only [H1W, Finset.sum_add_distrib]
  rw [hsplit, ← Finset.mul_sum, ← Finset.mul_sum,
    Convexity.StdSimplex.total_of_fintype, southRetrW_sum n q.2]
  ring

theorem continuous_H1W (n : ℕ) (i : Fin (n+2)) :
    Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => H1W n q i) := by
  have hs : Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hw : Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => q.2.1.1.weights i) := by
    fun_prop
  have hr : Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => southRetrW n q.2 i) :=
    (continuous_southRetrW n i).comp continuous_snd
  show Continuous (fun q : unitInterval × ↥(simplexSouthCap n) =>
    (1 - (q.1:ℝ)) * q.2.1.1.weights i + (q.1:ℝ) * southRetrW n q.2 i)
  exact ((continuous_const.sub hs).mul hw).add (hs.mul hr)

def H1Point (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    Convexity.StdSimplex ℝ (Fin (n+2)) :=
  mkSimplex (H1W n q) (H1W_nonneg n q) (H1W_sum n q)

theorem continuous_H1Point (n : ℕ) :
    Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => H1Point n q) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  have key : (fun q : unitInterval × ↥(simplexSouthCap n) => (H1Point n q).weights i)
      = (fun q => H1W n q i) := by
    funext q; rw [H1Point, mkSimplex_weights]
  change Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => (H1Point n q).weights i)
  rw [key]
  exact continuous_H1W n i

theorem H1W_last (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    H1W n q (Fin.last (n+1)) = (1 - (q.1:ℝ)) * q.2.1.1.weights (Fin.last (n+1)) := by
  show (1 - (q.1:ℝ)) * q.2.1.1.weights (Fin.last (n+1))
      + (q.1:ℝ) * southRetrW n q.2 (Fin.last (n+1)) = _
  rw [southRetrW_last, mul_zero, add_zero]

theorem H1Point_boundary (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    H1Point n q ∈ simplexBoundary (n+1) := by
  show ∃ i, (H1Point n q).weights i = 0
  by_cases h : (1 - (q.1:ℝ)) * q.2.1.1.weights (Fin.last (n+1)) = 0
  · exact ⟨Fin.last (n+1), by rw [H1Point, mkSimplex_weights, H1W_last]; exact h⟩
  · obtain ⟨i₀, hi₀⟩ := q.2.1.2
    have hne : i₀ ≠ Fin.last (n+1) := by
      rintro rfl
      exact h (by rw [hi₀, mul_zero])
    refine ⟨i₀, ?_⟩
    rw [H1Point, mkSimplex_weights]
    show (1 - (q.1:ℝ)) * q.2.1.1.weights i₀ + (q.1:ℝ) * southRetrW n q.2 i₀ = 0
    rw [hi₀, mul_zero, zero_add, southRetrW, ite_eq_right hne, hi₀, zero_div, mul_zero]

theorem H1Point_cap (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    (H1Point n q).weights (Fin.last (n+1)) < 1 := by
  rw [H1Point, mkSimplex_weights, H1W_last]
  have hs0 : (0:ℝ) ≤ (q.1:ℝ) := q.1.2.1
  have hs1 : (q.1:ℝ) ≤ 1 := q.1.2.2
  have ht : q.2.1.1.weights (Fin.last (n+1)) < 1 := q.2.2
  have ht0 : 0 ≤ q.2.1.1.weights (Fin.last (n+1)) := q.2.1.1.weights_nonneg _
  have h1 : (1 - (q.1:ℝ)) * q.2.1.1.weights (Fin.last (n+1))
      ≤ q.2.1.1.weights (Fin.last (n+1)) :=
    mul_le_of_le_one_left ht0 (by linarith)
  linarith

/-- The first stage map, into the boundary of the simplex. -/
def H1FunB (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) : boundarySpace (n+1) :=
  ⟨H1Point n q, H1Point_boundary n q⟩

/-- The first stage map, into the south cap. -/
def H1Map (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) : ↥(simplexSouthCap n) :=
  ⟨H1FunB n q, by
      show (H1FunB n q).1.weights (Fin.last (n+1)) < 1
      rw [H1FunB]; exact H1Point_cap n q⟩

theorem continuous_H1Map (n : ℕ) : Continuous (H1Map n) :=
  Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_H1Point n) (fun q => H1Point_boundary n q))
    (fun q => by
      show (H1FunB n q).1.weights (Fin.last (n+1)) < 1
      rw [H1FunB]; exact H1Point_cap n q)

/-! ## Stage 2: a homotopy from the retraction to the constant map -/

theorem sum_ite_eq_zero_one (n : ℕ) :
    ∑ i : Fin (n+2), (if i = (0 : Fin (n+2)) then (1:ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq']
  simp

/-- The vertex `e_0` of the simplex. -/
def southPointStd (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+2)) :=
  mkSimplex (fun i => if i = (0 : Fin (n+2)) then 1 else 0)
    (fun i => by split_ifs <;> norm_num) (sum_ite_eq_zero_one n)

theorem southPointStd_last (n : ℕ) :
    (southPointStd n).weights (Fin.last (n+1)) = 0 := by
  rw [southPointStd, mkSimplex_weights]
  exact ite_eq_right (last_ne_zero n)

/-- The vertex `e_0` of the simplex, as a point of the boundary. -/
def southPointB (n : ℕ) : boundarySpace (n+1) :=
  ⟨southPointStd n, ⟨Fin.last (n+1), southPointStd_last n⟩⟩

/-- The vertex `e_0` of the simplex, as a point of the south cap. -/
def southPoint (n : ℕ) : ↥(simplexSouthCap n) :=
  ⟨southPointB n, by
      show (southPointB n).1.weights (Fin.last (n+1)) < 1
      rw [southPointB]; simp [southPointStd_last]⟩

/-- Weight function of the second stage homotopy: the straight line from `r x` to `e_0`. -/
def H2W (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) (i : Fin (n+2)) : ℝ :=
  (1 - (q.1:ℝ)) * southRetrW n q.2 i + (q.1:ℝ) * (if i = 0 then 1 else 0)

theorem H2W_nonneg (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) (i : Fin (n+2)) :
    0 ≤ H2W n q i := by
  show (0:ℝ) ≤ (1 - (q.1:ℝ)) * southRetrW n q.2 i + (q.1:ℝ) * (if i = 0 then 1 else 0)
  have hs0 : (0:ℝ) ≤ (q.1:ℝ) := q.1.2.1
  have hs1 : (q.1:ℝ) ≤ 1 := q.1.2.2
  have h3 : 0 ≤ southRetrW n q.2 i := southRetrW_nonneg n q.2 i
  have h4 : 0 ≤ (if i = 0 then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have ha := mul_nonneg (by linarith : 0 ≤ 1 - (q.1:ℝ)) h3
  have hb := mul_nonneg hs0 h4
  linarith

theorem H2W_sum (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    ∑ i, H2W n q i = 1 := by
  have hsplit : (∑ i, H2W n q i)
      = (∑ i, (1 - (q.1:ℝ)) * southRetrW n q.2 i)
        + (∑ i, (q.1:ℝ) * (if i = (0 : Fin (n+2)) then (1:ℝ) else 0)) := by
    simp only [H2W, Finset.sum_add_distrib]
  rw [hsplit, ← Finset.mul_sum, ← Finset.mul_sum, southRetrW_sum n q.2, sum_ite_eq_zero_one n]
  ring

theorem continuous_H2W (n : ℕ) (i : Fin (n+2)) :
    Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => H2W n q i) := by
  have hs : Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hr : Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => southRetrW n q.2 i) :=
    (continuous_southRetrW n i).comp continuous_snd
  show Continuous (fun q : unitInterval × ↥(simplexSouthCap n) =>
    (1 - (q.1:ℝ)) * southRetrW n q.2 i + (q.1:ℝ) * (if i = (0 : Fin (n+2)) then 1 else 0))
  exact ((continuous_const.sub hs).mul hr).add (hs.mul continuous_const)

def H2Point (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    Convexity.StdSimplex ℝ (Fin (n+2)) :=
  mkSimplex (H2W n q) (H2W_nonneg n q) (H2W_sum n q)

theorem continuous_H2Point (n : ℕ) :
    Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => H2Point n q) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  have key : (fun q : unitInterval × ↥(simplexSouthCap n) => (H2Point n q).weights i)
      = (fun q => H2W n q i) := by
    funext q; rw [H2Point, mkSimplex_weights]
  change Continuous (fun q : unitInterval × ↥(simplexSouthCap n) => (H2Point n q).weights i)
  rw [key]
  exact continuous_H2W n i

theorem H2W_last (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    H2W n q (Fin.last (n+1)) = 0 := by
  show (1 - (q.1:ℝ)) * southRetrW n q.2 (Fin.last (n+1))
      + (q.1:ℝ) * (if (Fin.last (n+1) : Fin (n+2)) = 0 then 1 else 0) = 0
  rw [southRetrW_last, mul_zero, ite_eq_right (last_ne_zero n), mul_zero, add_zero]

theorem H2Point_boundary (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    H2Point n q ∈ simplexBoundary (n+1) := by
  show ∃ i, (H2Point n q).weights i = 0
  exact ⟨Fin.last (n+1), by rw [H2Point, mkSimplex_weights, H2W_last]⟩

theorem H2Point_cap (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) :
    (H2Point n q).weights (Fin.last (n+1)) < 1 := by
  rw [H2Point, mkSimplex_weights, H2W_last]; norm_num

/-- The second stage map, into the boundary of the simplex. -/
def H2FunB (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) : boundarySpace (n+1) :=
  ⟨H2Point n q, H2Point_boundary n q⟩

/-- The second stage map, into the south cap. -/
def H2Map (n : ℕ) (q : unitInterval × ↥(simplexSouthCap n)) : ↥(simplexSouthCap n) :=
  ⟨H2FunB n q, by
      show (H2FunB n q).1.weights (Fin.last (n+1)) < 1
      rw [H2FunB]; exact H2Point_cap n q⟩

theorem continuous_H2Map (n : ℕ) : Continuous (H2Map n) :=
  Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_H2Point n) (fun q => H2Point_boundary n q))
    (fun q => by
      show (H2FunB n q).1.weights (Fin.last (n+1)) < 1
      rw [H2FunB]; exact H2Point_cap n q)

/-! ## Endpoints and assembly -/

theorem H1W_zero (n : ℕ) (x : ↥(simplexSouthCap n)) (i : Fin (n+2)) :
    H1W n ((0 : unitInterval), x) i = x.1.1.weights i := by
  show (1 - ((0 : unitInterval):ℝ)) * x.1.1.weights i
      + ((0 : unitInterval):ℝ) * southRetrW n x i = x.1.1.weights i
  simp

theorem H1W_one (n : ℕ) (x : ↥(simplexSouthCap n)) (i : Fin (n+2)) :
    H1W n ((1 : unitInterval), x) i = southRetrW n x i := by
  show (1 - ((1 : unitInterval):ℝ)) * x.1.1.weights i
      + ((1 : unitInterval):ℝ) * southRetrW n x i = southRetrW n x i
  simp

theorem H2W_zero (n : ℕ) (x : ↥(simplexSouthCap n)) (i : Fin (n+2)) :
    H2W n ((0 : unitInterval), x) i = southRetrW n x i := by
  show (1 - ((0 : unitInterval):ℝ)) * southRetrW n x i
      + ((0 : unitInterval):ℝ) * (if i = 0 then 1 else 0) = southRetrW n x i
  simp

theorem H2W_one (n : ℕ) (x : ↥(simplexSouthCap n)) (i : Fin (n+2)) :
    H2W n ((1 : unitInterval), x) i = (southPointStd n).weights i := by
  show (1 - ((1 : unitInterval):ℝ)) * southRetrW n x i
      + ((1 : unitInterval):ℝ) * (if i = 0 then 1 else 0) = (southPointStd n).weights i
  rw [southPointStd, mkSimplex_weights]
  simp

theorem H1Map_zero (n : ℕ) (x : ↥(simplexSouthCap n)) :
    H1Map n ((0 : unitInterval), x) = x := by
  apply southCap_ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  show (H1Point n ((0 : unitInterval), x)).weights i = x.1.1.weights i
  rw [H1Point, mkSimplex_weights, H1W_zero]

theorem H1Map_one (n : ℕ) (x : ↥(simplexSouthCap n)) :
    H1Map n ((1 : unitInterval), x) = southRetr n x := by
  apply southCap_ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  show (H1Point n ((1 : unitInterval), x)).weights i = (southRetrPoint n x).weights i
  rw [H1Point, mkSimplex_weights, H1W_one, southRetrPoint, mkSimplex_weights]

theorem H2Map_zero (n : ℕ) (x : ↥(simplexSouthCap n)) :
    H2Map n ((0 : unitInterval), x) = southRetr n x := by
  apply southCap_ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  show (H2Point n ((0 : unitInterval), x)).weights i = (southRetrPoint n x).weights i
  rw [H2Point, mkSimplex_weights, H2W_zero, southRetrPoint, mkSimplex_weights]

theorem H2Map_one (n : ℕ) (x : ↥(simplexSouthCap n)) :
    H2Map n ((1 : unitInterval), x) = southPoint n := by
  apply southCap_ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  show (H2Point n ((1 : unitInterval), x)).weights i = (southPointStd n).weights i
  rw [H2Point, mkSimplex_weights, H2W_one]

/-- The first stage homotopy: from the identity to the retraction. -/
def H1Hom (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(simplexSouthCap n)) (southRetrCM n) where
  toContinuousMap := ⟨H1Map n, continuous_H1Map n⟩
  map_zero_left := fun x => by
    show H1Map n ((0 : unitInterval), x) = x
    exact H1Map_zero n x
  map_one_left := fun x => by
    show H1Map n ((1 : unitInterval), x) = southRetr n x
    exact H1Map_one n x

/-- The second stage homotopy: from the retraction to the constant map at `e_0`. -/
def H2Hom (n : ℕ) :
    ContinuousMap.Homotopy (southRetrCM n)
      (ContinuousMap.const ↥(simplexSouthCap n) (southPoint n)) where
  toContinuousMap := ⟨H2Map n, continuous_H2Map n⟩
  map_zero_left := fun x => by
    show H2Map n ((0 : unitInterval), x) = southRetr n x
    exact H2Map_zero n x
  map_one_left := fun x => by
    show H2Map n ((1 : unitInterval), x) = southPoint n
    exact H2Map_one n x

theorem simplexSouthCap_contractible (n : ℕ) :
    ContractibleSpace (TopCat.of (Work.HomologyExtra.simplexSouthCap n)) := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨southPoint n, ⟨(H1Hom n).trans (H2Hom n)⟩⟩

end

end Work.HomologyExtra
