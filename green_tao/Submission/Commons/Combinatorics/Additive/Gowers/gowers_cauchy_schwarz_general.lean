import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gcs_digit_step_at
import Submission.Commons.Combinatorics.Additive.Gowers.gowers_cube_sum_const_nonneg

open scoped BigOperators

namespace Commons.Combinatorics.Additive.Gowers

/-!
# The Gowers–Cauchy–Schwarz inequality (Green–Tao 2008, §5, inequality (gcz))

The `d`-dimensional Gowers inner product of a family `F` of real functions on a
finite abelian group `G`,
`⟨F⟩_d = ∑_{h : Fin d → G} ∑_{x : G} ∏_{ω : Fin d → Bool} F ω (x + ω·h)`,
is bounded by the product of the `d`-dimensional cube sums (`2^d`-th powers of the
Gowers norms) of the members of the family.

## Proof structure

We iterate the *one-digit* Cauchy–Schwarz step
`Commons.Combinatorics.Additive.Gowers.gcs_digit_step_at`, which splits a cube sum
along one coordinate and applies the ordinary Cauchy–Schwarz inequality in the
corresponding shift variable:

`(∑_F)^2 ≤ (∑_{F₀}) * (∑_{F₁})`,

where `F₀` (resp. `F₁`) is `F` with the chosen coordinate of the vertex `ω`
overwritten by `false` (resp. `true`).  Applying this step `d` times, once for each
coordinate, splits the single cube sum into the `2^d` (absolute values of) families
that are *constant* in the vertex variable, i.e. into the `2^d` cube sums of the
individual members `F ω` of the family.  This is the content of `gcs_iter`; the
final constant-family cube sums are non-negative by
`gowers_cube_sum_const_nonneg`.
-/

section Aux

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The `d`-dimensional Gowers cube sum of a family of functions (local notation). -/
private def gcsSum (d : ℕ) (F : (Fin d → Bool) → G → ℝ) : ℝ :=
  ∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
    F ω (x + ∑ i : Fin d, (if ω i then h i else 0))

/-- Overwrite the coordinate of *value* `k` of a vertex `ω` by `b`. -/
private def setCoordAt {d : ℕ} (k : ℕ) (b : Bool) (ω : Fin d → Bool) : Fin d → Bool :=
  fun i => if i.val = k then b else ω i

/-- `setCoordAt` at a `Fin` index is the usual coordinate overwrite. -/
private lemma setCoordAt_eq (d : ℕ) (ℓ : Fin d) (b : Bool) (ω : Fin d → Bool) :
    setCoordAt ℓ.val b ω = (fun i => if i = ℓ then b else ω i) := by
  funext i
  by_cases h : i = ℓ
  · subst h; simp [setCoordAt]
  · rw [if_neg h]
    simp only [setCoordAt]
    rw [if_neg (by intro hv; exact h (Fin.ext hv))]

/-- Congruence for the cube sum in the family. -/
private lemma gcsSum_congr {d : ℕ} {F F' : (Fin d → Bool) → G → ℝ}
    (h : ∀ ω, F ω = F' ω) : gcsSum d F = gcsSum d F' := by
  unfold gcsSum
  apply Finset.sum_congr rfl; intro _hh _
  apply Finset.sum_congr rfl; intro _x _
  apply Finset.prod_congr rfl; intro ω _
  rw [h ω]

/-- Non-negativity of the cube sum of a constant family (from the commons). -/
private lemma gcsSum_const_nonneg (d : ℕ) (hd : 0 < d) (f : G → ℝ) :
    0 ≤ gcsSum d (fun _ => f) :=
  gowers_cube_sum_const_nonneg f d hd

/-- **One-digit Gowers–Cauchy–Schwarz**, value-indexed form: split the cube sum of `F`
along the coordinate of value `k` and apply Cauchy–Schwarz in that shift variable. -/
private theorem digit_step_val (d : ℕ) (F : (Fin d → Bool) → G → ℝ) (k : ℕ) (hk : k < d) :
    (gcsSum d F)^2
      ≤ gcsSum d (fun ω => F (setCoordAt k false ω))
        * gcsSum d (fun ω => F (setCoordAt k true ω)) := by
  have h : (gcsSum d F)^2
      ≤ gcsSum d (fun ω => F (fun i => if i = (⟨k, hk⟩ : Fin d) then false else ω i))
        * gcsSum d (fun ω => F (fun i => if i = (⟨k, hk⟩ : Fin d) then true else ω i)) :=
    gcs_digit_step_at d F ⟨k, hk⟩
  have hF : ∀ b : Bool,
      gcsSum d (fun ω => F (fun i => if i = (⟨k, hk⟩ : Fin d) then b else ω i))
        = gcsSum d (fun ω => F (setCoordAt k b ω)) := by
    intro b
    apply gcsSum_congr
    intro ω
    congr 1
    exact (setCoordAt_eq d ⟨k, hk⟩ b ω).symm
  rw [hF false, hF true] at h
  exact h

/-! ## The splitting vertex

`vertex d s p ω` is the vertex obtained from `ω` by overwriting its last `s`
coordinates with the pattern `p`.  Splitting successively over the coordinates
`d-1, d-2, …, d-s` produces the `2^s` families `ω ↦ F (vertex d s p ω)`,
`p : Fin s → Bool`. -/

/-- The vertex obtained from `ω` by overwriting its last `s` coordinates with `p`. -/
private def vertex (d : ℕ) : (s : ℕ) → (Fin s → Bool) → (Fin d → Bool) → Fin d → Bool
  | 0, _, ω => ω
  | s+1, p, ω => setCoordAt (d - (s+1)) (p 0) (vertex d s (Fin.tail p) ω)

private lemma vertex_zero (d : ℕ) (p : Fin 0 → Bool) (ω : Fin d → Bool) :
    vertex d 0 p ω = ω := rfl

private lemma vertex_succ (d s : ℕ) (p : Fin (s+1) → Bool) (ω : Fin d → Bool) :
    vertex d (s+1) p ω = setCoordAt (d - (s+1)) (p 0) (vertex d s (Fin.tail p) ω) := rfl

private lemma vertex_succ_cons (d s : ℕ) (b : Bool) (p : Fin s → Bool) (ω : Fin d → Bool) :
    vertex d (s+1) (Fin.cons b p) ω = setCoordAt (d - (s+1)) b (vertex d s p ω) := by
  rw [vertex_succ, Fin.cons_zero, Fin.tail_cons]

/-- Description of the splitting vertex: the first `d - (n+1)` coordinates are read off
from `ω` and the last `n+1` are given by the pattern `p`. -/
private lemma vertex_eq : ∀ (n d : ℕ), n + 1 ≤ d → ∀ (p : Fin (n+1) → Bool) (ω : Fin d → Bool),
    vertex d (n+1) p ω
      = fun i => if i.val < d - (n+1) then ω i else p ⟨i.val - (d - (n+1)), by omega⟩ := by
  intro n
  induction n with
  | zero =>
    intro d _h p ω
    funext i
    rw [vertex_succ, vertex_zero]
    dsimp only [setCoordAt]
    by_cases hh : i.val = d - (0+1)
    · rw [if_pos hh]
      have h2 : ¬ i.val < d - (0+1) := by omega
      rw [if_neg h2]
      congr 1
      exact Fin.ext (by simp only [Fin.val_zero]; omega)
    · rw [if_neg hh]
      have h2 : i.val < d - (0+1) := by omega
      rw [if_pos h2]
  | succ n ih =>
    intro d h p ω
    funext i
    rw [vertex_succ, ih d (by omega) (Fin.tail p) ω]
    dsimp only [setCoordAt]
    by_cases h1 : i.val = d - ((n+1)+1)
    · rw [if_pos h1]
      have h2 : ¬ i.val < d - ((n+1)+1) := by omega
      rw [if_neg h2]
      congr 1
      exact Fin.ext (by simp only [Fin.val_zero]; omega)
    · rw [if_neg h1]
      by_cases h2 : i.val < d - (n+1)
      · rw [if_pos h2]
        have h3 : i.val < d - ((n+1)+1) := by omega
        rw [if_pos h3]
      · rw [if_neg h2]
        have h3 : ¬ i.val < d - ((n+1)+1) := by omega
        rw [if_neg h3]
        show p (Fin.succ ⟨i.val - (d - (n+1)), by omega⟩) = _
        congr 1
        exact Fin.ext (by simp only [Fin.val_succ]; omega)

/-- After all `d` coordinates have been overwritten the vertex is the pattern `p`. -/
private lemma vertex_self (d : ℕ) (hd : 1 ≤ d) (p : Fin d → Bool) (ω : Fin d → Bool) :
    vertex d d p ω = p := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, (Nat.sub_add_cancel hd).symm⟩
  funext i
  rw [show vertex (e+1) (e+1) p ω i
        = (if i.val < (e+1) - (e+1) then ω i
            else p ⟨i.val - ((e+1) - (e+1)), by omega⟩) from
      congrFun (vertex_eq e (e+1) (by omega) p ω) i]
  simp only [Nat.sub_self, Nat.not_lt_zero, if_false, Nat.sub_zero]

/-- `Fin (s+1) → Bool` splits as `Bool × (Fin s → Bool)` by `Fin.cons`. -/
private def consEquiv (s : ℕ) : Bool × (Fin s → Bool) ≃ (Fin (s+1) → Bool) where
  toFun q := Fin.cons q.1 q.2
  invFun p := (p 0, Fin.tail p)
  left_inv q := by obtain ⟨b, t⟩ := q; simp [Fin.cons_zero, Fin.tail_cons]
  right_inv p := Fin.cons_self_tail p

private lemma pow_le_abs_pow (x : ℝ) (n : ℕ) : x^n ≤ |x|^n := by
  calc x^n ≤ |x^n| := le_abs_self _
    _ = |x|^n := abs_pow x n

/-- The `s`-fold Cauchy–Schwarz splitting of the cube sum: after overwriting the last `s`
coordinates, the `2^s`-th power of the absolute value of the cube sum of `F` is bounded
by the product of the absolute values of the cube sums of the `2^s` families obtained. -/
private theorem gcs_iter (s : ℕ) : ∀ (d : ℕ) (_hs : s ≤ d) (F : (Fin d → Bool) → G → ℝ),
    |gcsSum d F|^(2^s)
      ≤ ∏ p : Fin s → Bool, |gcsSum d (fun ω => F (vertex d s p ω))| := by
  induction s with
  | zero =>
    intro d _hs F
    have hprod : (∏ p : Fin 0 → Bool, |gcsSum d (fun ω => F (vertex d 0 p ω))|)
        = ∏ _p : Fin 0 → Bool, |gcsSum d F| := by
      apply Finset.prod_congr rfl
      intro p _
      rw [show (fun ω : Fin d → Bool => F (vertex d 0 p ω)) = F from by
        funext ω; rw [vertex_zero]]
    rw [hprod, Finset.prod_const,
      show (Finset.univ : Finset (Fin 0 → Bool)).card = 1 by simp]
    simp
  | succ s ih =>
    intro d hs F
    have hs' : s ≤ d := by omega
    let F0 : (Fin d → Bool) → G → ℝ := fun ω => F (setCoordAt (d - (s+1)) false ω)
    let F1 : (Fin d → Bool) → G → ℝ := fun ω => F (setCoordAt (d - (s+1)) true ω)
    have hstep : (gcsSum d F)^2 ≤ gcsSum d F0 * gcsSum d F1 :=
      digit_step_val d F (d - (s+1)) (by omega)
    have ih0 := ih d hs' F0
    have ih1 := ih d hs' F1
    have hleaf0 : ∀ p : Fin s → Bool,
        (fun ω : Fin d → Bool => F0 (vertex d s p ω))
          = (fun ω => F (vertex d (s+1) (Fin.cons false p) ω)) := by
      intro p
      funext ω
      rw [vertex_succ_cons d s false p ω]
    have hleaf1 : ∀ p : Fin s → Bool,
        (fun ω : Fin d → Bool => F1 (vertex d s p ω))
          = (fun ω => F (vertex d (s+1) (Fin.cons true p) ω)) := by
      intro p
      funext ω
      rw [vertex_succ_cons d s true p ω]
    have hA : (∏ p : Fin s → Bool, |gcsSum d (fun ω => F0 (vertex d s p ω))|)
        = ∏ p : Fin s → Bool,
            |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons false p) ω))| := by
      apply Finset.prod_congr rfl
      intro p _
      rw [hleaf0 p]
    have hB : (∏ p : Fin s → Bool, |gcsSum d (fun ω => F1 (vertex d s p ω))|)
        = ∏ p : Fin s → Bool,
            |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons true p) ω))| := by
      apply Finset.prod_congr rfl
      intro p _
      rw [hleaf1 p]
    have hcombine :
        (∏ p : Fin s → Bool, |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons false p) ω))|)
          * (∏ p : Fin s → Bool,
              |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons true p) ω))|)
        = ∏ p' : Fin (s+1) → Bool, |gcsSum d (fun ω => F (vertex d (s+1) p' ω))| := by
      rw [mul_comm]
      rw [← Fintype.prod_bool (fun b : Bool => ∏ p : Fin s → Bool,
        |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons b p) ω))|)]
      rw [← Fintype.prod_prod_type (fun q : Bool × (Fin s → Bool) =>
        |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons q.1 q.2) ω))|)]
      exact Fintype.prod_equiv (consEquiv s)
        (fun q : Bool × (Fin s → Bool) =>
          |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons q.1 q.2) ω))|)
        (fun p' : Fin (s+1) → Bool =>
          |gcsSum d (fun ω => F (vertex d (s+1) p' ω))|)
        (fun _q => rfl)
    have hpow : |gcsSum d F|^(2^(s+1)) = ((gcsSum d F)^2)^(2^s) := by
      rw [show (2:ℕ)^(s+1) = 2 * 2^s by rw [pow_succ]; ring]
      rw [pow_mul, sq_abs]
    calc |gcsSum d F|^(2^(s+1))
        = ((gcsSum d F)^2)^(2^s) := hpow
      _ ≤ (gcsSum d F0 * gcsSum d F1)^(2^s) :=
          pow_le_pow_left₀ (sq_nonneg _) hstep (2^s)
      _ ≤ |gcsSum d F0 * gcsSum d F1|^(2^s) := pow_le_abs_pow _ _
      _ = |gcsSum d F0|^(2^s) * |gcsSum d F1|^(2^s) := by
          rw [abs_mul, mul_pow]
      _ ≤ (∏ p : Fin s → Bool, |gcsSum d (fun ω => F0 (vertex d s p ω))|)
            * (∏ p : Fin s → Bool, |gcsSum d (fun ω => F1 (vertex d s p ω))|) :=
          mul_le_mul ih0 ih1 (pow_nonneg (abs_nonneg _) _)
            (Finset.prod_nonneg fun _p _ => abs_nonneg _)
      _ = (∏ p : Fin s → Bool, |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons false p) ω))|)
            * (∏ p : Fin s → Bool,
                |gcsSum d (fun ω => F (vertex d (s+1) (Fin.cons true p) ω))|) := by
          rw [hA, hB]
      _ = ∏ p' : Fin (s+1) → Bool, |gcsSum d (fun ω => F (vertex d (s+1) p' ω))| :=
          hcombine

/-- **Gowers–Cauchy–Schwarz** in the cube-sum normalisation: the `2^d`-th power of the
`d`-dimensional Gowers inner product is bounded by the product of the `d`-dimensional cube
sums of the members of the family. -/
private theorem gcs_general_aux (d : ℕ) (F : (Fin d → Bool) → G → ℝ) :
    (gcsSum d F)^(2^d) ≤ ∏ ω : Fin d → Bool, gcsSum d (fun _ => F ω) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hcard : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 := by simp
    have hconst : ∀ ω : Fin 0 → Bool, gcsSum 0 (fun _ => F ω) = gcsSum 0 F := by
      intro ω
      unfold gcsSum
      apply Finset.sum_congr rfl; intro _h _
      apply Finset.sum_congr rfl; intro _x _
      apply Finset.prod_congr rfl; intro ω' _
      rw [Subsingleton.elim ω' ω]
    rw [show (2:ℕ)^0 = 1 from rfl, pow_one]
    have hrew : (∏ ω : Fin 0 → Bool, gcsSum 0 (fun _ => F ω))
        = ∏ _ω : Fin 0 → Bool, gcsSum 0 F := by
      apply Finset.prod_congr rfl
      intro ω _
      exact hconst ω
    rw [hrew, Finset.prod_const, hcard, pow_one]
  · have hiter := gcs_iter d d le_rfl F
    have habs : (gcsSum d F)^(2^d) ≤ |gcsSum d F|^(2^d) := pow_le_abs_pow _ _
    have hprod : (∏ p : Fin d → Bool, |gcsSum d (fun ω => F (vertex d d p ω))|)
        = ∏ p : Fin d → Bool, gcsSum d (fun _ => F p) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [show (fun ω : Fin d → Bool => F (vertex d d p ω)) = (fun _ : Fin d → Bool => F p) from by
        funext ω; rw [vertex_self d hd p ω]]
      exact abs_of_nonneg (gcsSum_const_nonneg d hd (F p))
    exact le_trans habs (le_trans hiter (le_of_eq hprod))

end Aux

/-- **Gowers–Cauchy–Schwarz inequality.**  The `d`-dimensional Gowers inner product of a
family `F` of real functions on a finite abelian group is bounded by the product of the
`d`-dimensional cube sums (`2^d`-th powers of the Gowers norms) of the members of the
family.  This is Green–Tao (2008), inequality (gcz) of §5, and the key ingredient in
showing that the Gowers uniformity norms are indeed norms. -/
theorem gowers_cauchy_schwarz_general {G : Type*} [AddCommGroup G] [Fintype G]
    (d : ℕ) (F : (Fin d → Bool) → G → ℝ) :
    (∑ h : Fin d → G, ∑ x : G, ∏ ω : Fin d → Bool,
        F ω (x + ∑ i : Fin d, (if ω i then h i else 0)))^(2^d)
      ≤ ∏ ω : Fin d → Bool, ∑ h : Fin d → G, ∑ x : G, ∏ ω' : Fin d → Bool,
          F ω (x + ∑ i : Fin d, (if ω' i then h i else 0)) := by
  change (gcsSum d F)^(2^d) ≤ ∏ ω : Fin d → Bool, gcsSum d (fun _ => F ω)
  exact gcs_general_aux d F

end Commons.Combinatorics.Additive.Gowers
