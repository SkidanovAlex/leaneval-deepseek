import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# Strict polynomial inequalities lie in `Ω` (area H, Omega cluster)

For a sharply o-minimal structure `S` and a real polynomial `P` in `n` variables we
show that the *strict* sublevel set `{x | P x < 0}` belongs to `S.Ω (n+3) (deg P + 2) n`.

The idea is to trade the strict inequality for one extra existentially quantified
variable: for `a : ℝ`,

`a < 0 ↔ ∃ t : ℝ, a * t ^ 2 + 1 = 0`

(if `a < 0`, take `t = (Real.sqrt (-a))⁻¹`; conversely `a * t ^ 2 = -1` forces `a < 0`
as `t ^ 2 ≥ 0`).  Consequently, with `Q x t := P x * t ^ 2 + 1`, we have

`{x | P x < 0} = projLast {z : ℝⁿ⁺¹ | Q z = 0}`.

The polynomial `Q` is the "pad `P` with one variable and one monomial `t ^ 2`" of
`omegaStrictPoly P`, whose total degree is at most `deg P + 2`.  The zero set of `Q`
is in `S.Ω (n+1) (deg Q) (n+1)` by the axiom `hyp`, projection costs one `F` and one
ambient dimension (`S.Ω (n+2) (deg Q) n`), monotonicity in the degree costs nothing
and gives the stated `deg P + 2`, and monotonicity in `F` produces the stated `n + 3`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Omega

open WilkiesDesign

/-- Monotonicity of `S.Ω` in the `F` (number-of-quantifiers) slot, iterated. -/
lemma omega_mono_F (S : SOMin) {F F' D n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (hle : F ≤ F') : X ∈ S.Ω F' D n :=
  Nat.le_induction h (fun _ _ ih => S.mono_F ih) F' hle

/-- Monotonicity of `S.Ω` in the `D` (degree) slot, iterated. -/
lemma omega_mono_D (S : SOMin) {F D D' n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (hle : D ≤ D') : X ∈ S.Ω F D' n :=
  Nat.le_induction h (fun _ _ ih => S.mono_D ih) D' hle

/-- `P` padded with one extra variable `t` and the monomial `t ^ 2`:
`omegaStrictPoly P = P(x) * t ^ 2 + 1` in the variables `Fin (n+1) → ℝ`. -/
def omegaStrictPoly {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n+1)) ℝ :=
  MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n+1)) P * MvPolynomial.X (Fin.last n) ^ 2 + 1

/-- Evaluation of the padded polynomial. -/
lemma omegaStrictPoly_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (t : ℝ) :
    (omegaStrictPoly P).eval (Fin.snoc x t) = P.eval x * t ^ 2 + 1 := by
  have hcomp : (Fin.snoc x t ∘ Fin.castSucc : Fin n → ℝ) = x := by
    funext i; exact Fin.snoc_castSucc (α := fun _ => ℝ) t x i
  simp only [omegaStrictPoly, map_add, map_mul, map_pow, MvPolynomial.eval_rename,
    MvPolynomial.eval_X, Fin.snoc_last, map_one, hcomp]

/-- The padded polynomial adds at most `2` to the total degree. -/
lemma omegaStrictPoly_totalDegree_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (omegaStrictPoly P).totalDegree ≤ P.totalDegree + 2 := by
  rw [omegaStrictPoly]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [MvPolynomial.totalDegree_one]
  refine max_le ?_ (Nat.zero_le _)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X_pow]
  exact Nat.add_le_add_right (MvPolynomial.totalDegree_rename_le _ _) 2

/-- The zero set of the padded polynomial projects exactly onto the strict sublevel
set of `P`. -/
lemma projLast_omegaStrictPoly (n : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    projLast {z : Fin (n+1) → ℝ | (omegaStrictPoly P).eval z = 0}
      = {x : Fin n → ℝ | P.eval x < 0} := by
  ext x
  simp only [projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [omegaStrictPoly_eval] at ht
    by_contra h
    have hge : 0 ≤ P.eval x := not_lt.mp h
    have h2 := mul_nonneg hge (sq_nonneg t)
    linarith
  · intro h
    have hpos : 0 < -(P.eval x) := neg_pos.mpr h
    have hs : Real.sqrt (-(P.eval x)) ^ 2 = -(P.eval x) := Real.sq_sqrt hpos.le
    have hne : P.eval x ≠ 0 := ne_of_lt h
    refine ⟨(Real.sqrt (-(P.eval x)))⁻¹, ?_⟩
    rw [omegaStrictPoly_eval]
    have ht2 : ((Real.sqrt (-(P.eval x)))⁻¹) ^ 2 = -(P.eval x)⁻¹ := by
      rw [inv_pow, hs, inv_neg]
    rw [ht2, mul_neg, mul_inv_cancel₀ hne]
    ring

theorem omega_poly_lt (S : WilkiesDesign.SOMin) (n : ℕ) (P : MvPolynomial (Fin n) ℝ) : {x : Fin n → ℝ | P.eval x < 0} ∈ S.Ω (n + 3) (P.totalDegree + 2) n := by
  have hmemQ : {z : Fin (n+1) → ℝ | (omegaStrictPoly P).eval z = 0} ∈
      S.Ω (n+1) (omegaStrictPoly P).totalDegree (n+1) := S.hyp (n+1) (omegaStrictPoly P)
  have hproj : projLast {z : Fin (n+1) → ℝ | (omegaStrictPoly P).eval z = 0} ∈
      S.Ω (n+2) (omegaStrictPoly P).totalDegree n := S.proj hmemQ
  rw [projLast_omegaStrictPoly] at hproj
  have h1 : {x : Fin n → ℝ | P.eval x < 0} ∈ S.Ω (n+2) (P.totalDegree + 2) n :=
    omega_mono_D S hproj (omegaStrictPoly_totalDegree_le P)
  exact omega_mono_F S h1 (by omega)

end Work.WilkiesH.Omega
