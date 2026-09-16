import Submission.ZagierHoffmanProof.StepK23

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K24: the s=0 collapse assembly (`Hsum_collapse0`)

The first block of the E-assembly (PLAN SESSION 156), fully assembled:

  sum_cons_split (n) (f) : Σ_{a : Fin(n+1)→F} f a = Σ_{c:F} Σ_{t:Fin n→F} f (Fin.cons c t)
      [Fintype.sum_equiv finSuccSplit — the per-element equality is
      `Equiv.symm_apply_apply e a` (NOT `e.left_inv a`: rw cannot see through the
      `e.symm`/`e.invFun` notation); then Fintype.sum_prod_type]
  D1 (n) (t) : F[X] := Σ_{m<n+1} coeffSeq(n+1)(cons 0 t)(m+1)·hh 0 2 m   (the stage-1
      denominator)
  ★★★ Hsum_collapse0 (n) :
      Hsum F (n+1) 1 = (X−X^q)⁻¹ · Σ_{t : Fin n → F} inv(cast(D1 n t))
    [calc: Hsum_tuple F (n+1); sum_cons_split + sum_prod_type (Σ_c Σ_t);
     per (c,t): monicPd (n+1)(cons c t) = C c + Z₀(t) via congrArg of Inv.inv over
     congrArg of the cast over monicPd_cons_add_zero (the casts are NOT defeq to the
     polynomial equality — apply congrArg);
     swap the sums (Finset.sum_comm) and collapse the inner c-sum by
     Hsum_collapse0_inner;
     per t: inv(cast(Z₀−Z₀^q)) = Acast⁻¹·inv(cast(D1 t)) via stage0_factor +
     congrArg cast (rewrite ONLY the RHS with `rw [map_mul]` — `simp [map_mul,
     map_sub,…]` over-expands the LHS whole-cast) + mul_inv_rev + mul_comm;
     factor Acast⁻¹ out (Finset.mul_sum)]

This is the template for every stage s = 1..n−1 of the EvalU-∀d iteration (each stage:
same theorem shape on the next head coefficient with the hh-variable count growing).
All lemmas here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]




/-- reindexing a function-sum by the coordinate split `Fin.cons`. -/
lemma sum_cons_split (n : ℕ) (f : (Fin (n + 1) → F) → RatFunc F) :
    letI : Fintype F := Fintype.ofFinite F
    (∑ a : Fin (n + 1) → F, f a) = ∑ ct : F × (Fin n → F), f (Fin.cons ct.1 ct.2) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let e : (Fin (n + 1) → F) ≃ (F × (Fin n → F)) := finSuccSplit F n
  have h1 : (∑ a : Fin (n + 1) → F, f a) = ∑ ct : F × (Fin n → F), f (e.symm ct) := by
    exact Fintype.sum_equiv e f (fun ct => f (e.symm ct)) (fun a => by
      rw [Equiv.symm_apply_apply e a])
  rw [h1]
  apply Finset.sum_congr rfl
  intro ct hct
  rfl

/-- the stage-1 denominator polynomial of the collapse: `D₁(t)`. -/
noncomputable def D1 (n : ℕ) (t : Fin n → F) : F[X] :=
  ∑ m ∈ Finset.range (n + 1), C (coeffSeq F (n + 1) (Fin.cons 0 t) (m + 1)) * hh F 0 2 m

/-- ★ THE s=0 COLLAPSE (first block of the E-assembly):
`Hsum F (n+1) 1 = (X−X^q)⁻¹ · Σ_{t : Fin n → F} inv(cast(D₁(t)))`. -/
lemma Hsum_collapse0 (n : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    Hsum F (n + 1) 1 =
      (((X - X ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹ *
        (∑ t : Fin n → F, ((((D1 F n t : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : DecidableEq F := Classical.decEq F
  let Acast : RatFunc F := (((X - X ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)
  calc
    Hsum F (n + 1) 1 = ∑ a : Fin (n + 1) → F, ((((monicPd F (n + 1) a : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          rw [Hsum_tuple F (n + 1)]
    _ = ∑ c : F, ∑ t : Fin n → F, ((((monicPd F (n + 1) (Fin.cons c t) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          rw [sum_cons_split F n (fun a : Fin (n + 1) → F =>
            ((((monicPd F (n + 1) a : F[X]) : F[X]) : RatFunc F)⁻¹))]
          rw [Fintype.sum_prod_type]
    _ = ∑ c : F, ∑ t : Fin n → F, ((((C c + monicPd F (n + 1) (Fin.cons 0 t) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro t ht
          apply congrArg (fun x : RatFunc F => x⁻¹)
          have hm := congrArg (fun p : F[X] => (((p : F[X]) : F[X]) : RatFunc F)) (monicPd_cons_add_zero F n c t)
          simpa using hm
    _ = ∑ t : Fin n → F, ((((monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) := by
          -- swap the sums and collapse the inner c-sum
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t ht
          exact Hsum_collapse0_inner F n t
    _ = Acast⁻¹ * (∑ t : Fin n → F, ((((D1 F n t : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
          -- per t: inv(cast(Z₀ − Z₀^q)) = inv(Acast·Dcast) = Acast⁻¹·Dcast⁻¹ via stage0_factor
          have hfac (t : Fin n → F) :
              ((((monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹) =
                Acast⁻¹ * ((((D1 F n t : F[X]) : F[X]) : RatFunc F)⁻¹) := by
            have hsf := stage0_factor F n t
            -- hsf : Z₀ − Z₀^q = (X−X^q)·(D₁-poly)
            have hc := congrArg (algebraMap (F[X]) (RatFunc F)) hsf
            -- cast(Z₀−Z₀^q) = Acast·Dcast
            have hc' : ((((monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)) =
                Acast * ((((D1 F n t : F[X]) : F[X]) : RatFunc F)) := by
              dsimp [Acast, D1]
              have h := congrArg (algebraMap (F[X]) (RatFunc F)) hsf
              rw [map_mul] at h
              exact h
            calc
              ((((monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹)
                  = (Acast * ((((D1 F n t : F[X]) : F[X]) : RatFunc F)))⁻¹ := by rw [hc']
              _ = Acast⁻¹ * ((((D1 F n t : F[X]) : F[X]) : RatFunc F)⁻¹) := by
                    rw [mul_inv_rev, mul_comm]
          calc
            (∑ t : Fin n → F, ((((monicPd F (n + 1) (Fin.cons 0 t) - (monicPd F (n + 1) (Fin.cons 0 t)) ^ (Nat.card F) : F[X]) : F[X]) : RatFunc F)⁻¹))
                = ∑ t : Fin n → F, (Acast⁻¹ * ((((D1 F n t : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  exact hfac t
            _ = Acast⁻¹ * (∑ t : Fin n → F, ((((D1 F n t : F[X]) : F[X]) : RatFunc F)⁻¹)) := by
                  rw [Finset.mul_sum]


end ZagierHoffmanPositiveChar
