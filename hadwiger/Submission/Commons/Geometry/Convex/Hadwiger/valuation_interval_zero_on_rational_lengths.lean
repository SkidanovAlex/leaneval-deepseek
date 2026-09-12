import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.RCLike.Basic
import Submission.Commons.Geometry.Convex.Hadwiger.interval_interior_empty_iff

open Set
open scoped Classical
set_option linter.unusedVariables false

namespace Commons.Geometry.Convex.Hadwiger

/-- The canonical convex body `[a, b]` in `ℝ` (falls back to `[0, 1]` when `b < a`; it is
only ever used in the case `a ≤ b`). -/
noncomputable def intervalBody (a b : ℝ) : ConvexBody ℝ :=
  if h : a ≤ b then
    ⟨Set.Icc a b, convex_Icc a b, (isCompact_Icc : IsCompact (Set.Icc a b)),
      (Set.nonempty_Icc.mpr h : (Set.Icc a b).Nonempty)⟩
  else
    ⟨Set.Icc (0 : ℝ) 1, convex_Icc (0 : ℝ) 1, (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)),
      (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1) : (Set.Icc (0 : ℝ) 1).Nonempty)⟩

lemma intervalBody_coe {a b : ℝ} (h : a ≤ b) : (intervalBody a b : Set ℝ) = Set.Icc a b := by
  simp [intervalBody, h]

lemma intervalBody_congr {a b a' b' : ℝ} (ha : a = a') (hb : b = b') :
    intervalBody a b = intervalBody a' b' := by
  subst a'; subst b'; rfl

/-- A body whose underlying set is the interval `[a, b]` equals the canonical body. -/
lemma intervalBody_eq_of_coe {K : ConvexBody ℝ} {a b : ℝ} (hab : a ≤ b)
    (hK : (K : Set ℝ) = Set.Icc a b) : K = intervalBody a b := by
  apply ConvexBody.ext
  rw [hK, intervalBody_coe hab]

/-- The point body at `0` is simple (vanishes under `φ`): `φ [0,0] = 0`. -/
lemma intervalBody_point_zero (φ : ConvexBody ℝ → ℝ)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0) :
    φ (intervalBody 0 0) = 0 := by
  apply hsimple
  rw [intervalBody_coe (le_refl 0)]
  exact (interval_interior_empty_iff (le_refl 0)).mpr rfl

/-- A simple valuation is additive over a dissection of an interval: `φ [a,b] = φ [a,c] + φ [c,b]`
when `a ≤ c ≤ b`. -/
lemma interval_valuation_split
    (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    φ (intervalBody a b) = φ (intervalBody a c) + φ (intervalBody c b) := by
  have hU : ((intervalBody a b : ConvexBody ℝ) : Set ℝ) =
      ((intervalBody a c : ConvexBody ℝ) : Set ℝ) ∪
        ((intervalBody c b : ConvexBody ℝ) : Set ℝ) := by
    rw [intervalBody_coe (le_trans hac hcb), intervalBody_coe hac, intervalBody_coe hcb]
    exact (Set.Icc_union_Icc_eq_Icc hac hcb).symm
  have hI : ((intervalBody c c : ConvexBody ℝ) : Set ℝ) =
      ((intervalBody a c : ConvexBody ℝ) : Set ℝ) ∩
        ((intervalBody c b : ConvexBody ℝ) : Set ℝ) := by
    rw [intervalBody_coe (le_refl c), intervalBody_coe hac, intervalBody_coe hcb]
    rw [Set.Icc_inter_Icc]
    rw [sup_eq_right.mpr hac, inf_eq_left.mpr hcb]
  have hφ := hadd (intervalBody a b) (intervalBody c c) (intervalBody a c) (intervalBody c b) hU hI
  have hB : φ (intervalBody c c) = 0 := by
    apply hsimple
    rw [intervalBody_coe (le_refl c)]
    exact (interval_interior_empty_iff (le_refl c)).mpr rfl
  linarith

/-- Translation invariance for interval bodies: `φ [a, b] = φ [a + t, b + t]`. -/
lemma interval_valuation_translate
    (φ : ConvexBody ℝ → ℝ)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    {a b t : ℝ} (hab : a ≤ b) :
    φ (intervalBody a b) = φ (intervalBody (a + t) (b + t)) := by
  refine htrans (intervalBody a b) (intervalBody (a + t) (b + t)) t ?_
  rw [intervalBody_coe (add_le_add hab (le_refl t)), intervalBody_coe hab]
  exact (Set.image_add_const_Icc t a b).symm

/-- Length additivity from the origin: for `0 ≤ t, s`, `φ [0, t+s] = φ [0, t] + φ [0, s]`. -/
lemma interval_valuation_add
    (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    φ (intervalBody 0 (t + s)) = φ (intervalBody 0 t) + φ (intervalBody 0 s) := by
  have hsplit := interval_valuation_split φ hadd hsimple (a := 0) (b := t + s) (c := t) ht (by linarith)
  have htr := interval_valuation_translate φ htrans (a := t) (b := t + s) (t := -t) (by linarith)
  have hbody : intervalBody (t + -t) (t + s + -t) = intervalBody 0 s := by
    refine intervalBody_congr ?_ ?_
    · ring
    · ring
  calc
    φ (intervalBody 0 (t + s)) = φ (intervalBody 0 t) + φ (intervalBody t (t + s)) := hsplit
    _ = φ (intervalBody 0 t) + φ (intervalBody (t + -t) (t + s + -t)) := by rw [htr]
    _ = φ (intervalBody 0 t) + φ (intervalBody 0 s) := by rw [hbody]

/-- `φ` of an interval of integer length times a step is the corresponding multiple of `φ` of
the unit step: `φ [0, k·h] = k · φ [0, h]` for every natural `k` and `0 ≤ h`. -/
lemma interval_valuation_mul
    (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    {h : ℝ} (hh : 0 ≤ h) :
    ∀ k : ℕ, φ (intervalBody 0 ((k : ℝ) * h)) = (k : ℝ) * φ (intervalBody 0 h) := by
  intro k
  induction k with
  | zero =>
      have hb : intervalBody 0 ((↑(0 : ℕ) : ℝ) * h) = intervalBody 0 0 := intervalBody_congr rfl (by norm_num)
      have hval : φ (intervalBody 0 ((↑(0 : ℕ) : ℝ) * h)) = 0 := by
        rw [hb]
        exact intervalBody_point_zero φ hsimple
      rw [hval]
      simp
  | succ k ih =>
      calc
        φ (intervalBody 0 ((↑(Nat.succ k) : ℝ) * h)) =
            φ (intervalBody 0 ((k : ℝ) * h + h)) := by
          apply congrArg φ
          apply intervalBody_congr rfl
          rw [Nat.cast_succ]
          ring
        _ = φ (intervalBody 0 ((k : ℝ) * h)) + φ (intervalBody 0 h) := by
          exact interval_valuation_add φ hadd hsimple htrans (mul_nonneg (Nat.cast_nonneg k) hh) hh
        _ = (k : ℝ) * φ (intervalBody 0 h) + φ (intervalBody 0 h) := by rw [ih]
        _ = ((k : ℝ) + 1) * φ (intervalBody 0 h) := by ring
        _ = (↑(Nat.succ k) : ℝ) * φ (intervalBody 0 h) := by rw [Nat.cast_succ]

/-- The unit interval has value zero, and this forces the interval of reciprocal length
`1/n` to vanish: `φ [0, 1/n] = 0` for `n ≠ 0`. -/
lemma interval_valuation_one_div
    (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0)
    {n : ℕ} (hn : n ≠ 0) :
    φ (intervalBody 0 (1 / (n : ℝ))) = 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hh : 0 ≤ 1 / (n : ℝ) := le_of_lt (div_pos zero_lt_one hpos)
  have hrec := interval_valuation_mul φ hadd hsimple htrans hh n
  -- φ (intervalBody 0 ((n : ℝ) * (1 / (n : ℝ)))) = (n : ℝ) * φ (intervalBody 0 (1 / (n : ℝ)))
  have hbody : intervalBody 0 ((n : ℝ) * (1 / (n : ℝ))) = intervalBody 0 1 := by
    refine intervalBody_congr rfl ?_
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn]
  have hunit1 : φ (intervalBody 0 1) = 0 := hunit (intervalBody 0 1) (intervalBody_coe (by norm_num))
  have hprod : (n : ℝ) * φ (intervalBody 0 (1 / (n : ℝ))) = 0 := by
    rw [← hrec]
    rw [hbody]
    exact hunit1
  exact (mul_eq_zero.mp hprod).resolve_left (by exact_mod_cast hn)

theorem valuation_interval_zero_on_rational_lengths
    (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    (htrans : ∀ A B : ConvexBody ℝ, ∀ t : ℝ,
        (B : Set ℝ) = (fun x : ℝ => x + t) '' (A : Set ℝ) → φ A = φ B)
    (hunit : ∀ U : ConvexBody ℝ, (U : Set ℝ) = Set.Icc 0 1 → φ U = 0) :
    ∀ (q : ℚ) (hq : 0 ≤ q) (K : ConvexBody ℝ),
      (K : Set ℝ) = Set.Icc 0 (q : ℝ) → φ K = 0 := by
  intro q hq K hK
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hKcanon : K = intervalBody 0 (q : ℝ) := by
    apply ConvexBody.ext
    rw [hK]
    exact (intervalBody_coe hq0).symm
  rw [hKcanon]
  -- now prove φ (intervalBody 0 (q : ℝ)) = 0 for rational q ≥ 0
  let n0 : ℕ := q.den
  let m : ℕ := q.num.toNat
  have hn0pos : 0 < n0 := by
    dsimp [n0]
    exact Rat.den_pos q
  have hn0R : (n0 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn0pos)
  have hsteppos : (0 : ℝ) < 1 / (n0 : ℝ) := by
    exact div_pos zero_lt_one (by exact_mod_cast hn0pos)
  have hstep : 0 ≤ 1 / (n0 : ℝ) := le_of_lt hsteppos
  have hnum0 : 0 ≤ q.num := (Rat.num_nonneg).mpr hq
  -- (q : ℝ) = (m : ℝ) / (n0 : ℝ)
  have hnum : ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by
    rw [← Int.cast_natCast (q.num.toNat)]
    exact congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnum0)
  have hqnum : (q : ℝ) = (m : ℝ) / (n0 : ℝ) := by
    have hnd := Rat.num_div_den q
    have hcast : (↑(((q.num : ℚ) / (q.den : ℚ))) : ℝ) = (q : ℝ) :=
      congrArg (fun z : ℚ => (z : ℝ)) hnd
    rw [Rat.cast_div] at hcast
    norm_num at hcast
    rw [← hcast]
    dsimp [m, n0]
    rw [hnum]
  -- φ (intervalBody 0 (1/(n0:ℝ))) = 0
  have hsmall : φ (intervalBody 0 (1 / (n0 : ℝ))) = 0 := by
    exact interval_valuation_one_div φ hadd hsimple htrans hunit (n := n0) (ne_of_gt hn0pos)
  -- recursion at m
  have hrec := interval_valuation_mul φ hadd hsimple htrans hstep m
  -- φ (intervalBody 0 ((m : ℝ) * (1/(n0:ℝ)))) = (m : ℝ) * φ (intervalBody 0 (1/(n0:ℝ)))
  have hmain : φ (intervalBody 0 ((m : ℝ) * (1 / (n0 : ℝ)))) = 0 := by
    rw [hrec, hsmall]
    ring
  -- (m : ℝ) * (1 / (n0 : ℝ)) = (q : ℝ)
  have hmul : (m : ℝ) * (1 / (n0 : ℝ)) = (q : ℝ) := by
    rw [hqnum]
    field_simp [hn0R]
  -- rewrite body of intervalBody 0 ((m:ℝ) * h) to intervalBody 0 (q:ℝ)
  rw [← hmul]
  exact hmain

end Commons.Geometry.Convex.Hadwiger