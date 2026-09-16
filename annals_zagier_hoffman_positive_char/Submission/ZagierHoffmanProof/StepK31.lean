import Submission.ZagierHoffmanProof.StepK30

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K31: the s=1 collapse assembly (`collapse1`, `Hsum_collapse1`)

The s=1 instance of the E-assembly (mirror of `Hsum_collapse0` with `D1`/`D2` in the
role of `monicPd`/`D1`):

  collapse1 (m) : Σ_{t : Fin(m+1)→F} inv(cast(D1 (m+1) t))
      = (X − X^{q²})⁻¹ · Σ_{u : Fin m→F} inv(cast(D2 m u))
    [collapse1_split (step 1) + collapse1_csum (step 2, D1_cons_add_zero) +
     collapse1_inner (per-u inner collapse via Hsum_one_subst at Z(u)) +
     D1_D2_glue (Z(u) − Z(u)^q = (X−X^{q²})·D2 m u) + factor extraction
     (mul_inv_rev/mul_comm; map_mul targeted rw)]
  Hsum_collapse1 (m) : Hsum F (m+2) 1 = (X−X^q)⁻¹·(X−X^{q²})⁻¹·Σ_{u:Fin m→F} inv(cast(D2 m u))
    [Hsum_collapse0 (m+1) composed with collapse1]

All sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ THE s=1 COLLAPSE: the stage-1 state-sum collapses with the factor `(X−X^{q²})⁻¹`
leaving the stage-2 denominator `D2`. -/
lemma collapse1 (m : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ t : Fin (m + 1) → F, ((((D1 F (m + 1) t : F[X]) : F[X]) : RatFunc F)⁻¹)) =
      ((((X - X ^ ((Nat.card F) ^ 2) : F[X]) : F[X]) : RatFunc F)⁻¹) *
        (∑ u : Fin m → F, ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let A2cast : RatFunc F := (((X - X ^ ((Nat.card F) ^ 2) : F[X]) : F[X]) : RatFunc F)
  calc
    (∑ t : Fin (m + 1) → F, ((((D1 F (m + 1) t : F[X]) : F[X]) : RatFunc F)⁻¹))
        = ∑ c : F, ∑ u : Fin m → F, ((((D1 F (m + 1) (Fin.cons c u) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
            rw [collapse1_split F m]
    _ = ∑ u : Fin m → F, ∑ c : F, ((((C c + D1 F (m + 1) (Fin.cons 0 u) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
            rw [collapse1_csum F m]
    _ = ∑ u : Fin m → F, ((((D1 F (m + 1) (Fin.cons 0 u) - (D1 F (m + 1) (Fin.cons 0 u)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact collapse1_inner F m u
    _ = A2cast⁻¹ * (∑ u : Fin m → F, ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
          have hfac (u : Fin m → F) :
              ((((D1 F (m + 1) (Fin.cons 0 u) - (D1 F (m + 1) (Fin.cons 0 u)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) =
                A2cast⁻¹ * ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹) := by
            have hg := D1_D2_glue F m u
            have hc' : ((((D1 F (m + 1) (Fin.cons 0 u) - (D1 F (m + 1) (Fin.cons 0 u)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)) =
                A2cast * ((((D2 F m u : F[X]) : F[X]) : RatFunc F)) := by
              dsimp [A2cast]
              have h := congrArg (algebraMap (F[X]) (RatFunc F)) hg
              rw [map_mul] at h
              exact h
            calc
              ((((D1 F (m + 1) (Fin.cons 0 u) - (D1 F (m + 1) (Fin.cons 0 u)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹)
                  = (A2cast * ((((D2 F m u : F[X]) : F[X]) : RatFunc F)))⁻¹ := by rw [hc']
              _ = A2cast⁻¹ * ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹) := by
                    rw [mul_inv_rev, mul_comm]
          calc
            (∑ u : Fin m → F, ((((D1 F (m + 1) (Fin.cons 0 u) - (D1 F (m + 1) (Fin.cons 0 u)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹))
                = ∑ u : Fin m → F, (A2cast⁻¹ * ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  exact hfac u
            _ = A2cast⁻¹ * (∑ u : Fin m → F, ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
                  rw [Finset.mul_sum]

/-- ★ THE s=1 INSTANCE: `Hsum F (m+2) 1 = (X−X^q)⁻¹·(X−X^{q²})⁻¹·Σ_{u:Fin m→F} inv(D2 m u)`. -/
lemma Hsum_collapse1 (m : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    Hsum F (m + 2) 1 =
      ((((X - X ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) *
        (((((X - X ^ ((Nat.card F) ^ 2) : F[X]) : F[X]) : RatFunc F)⁻¹) *
          (∑ u : Fin m → F, ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹))) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h0 := Hsum_collapse0 F (m + 1)
  have h1 := collapse1 F m
  calc
    Hsum F (m + 2) 1
        = ((((X - X ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) *
            (∑ t : Fin (m + 1) → F, ((((D1 F (m + 1) t : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
            exact h0
    _ = ((((X - X ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) *
          (((((X - X ^ ((Nat.card F) ^ 2) : F[X]) : F[X]) : RatFunc F)⁻¹) *
            (∑ u : Fin m → F, ((((D2 F m u : F[X]) : F[X]) : RatFunc F)⁻¹))) := by
            rw [h1]

end ZagierHoffmanPositiveChar
