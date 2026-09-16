import Submission.ZagierHoffmanProof.DescentLevel
import Submission.ZagierHoffmanProof.TmApply

/-!
# Dac §5.2, Step 2, complete: all the coefficients `B̃` of the second relation vanish

`TmApply.tmABP_a_leading` produces, from the ABP criterion applied to the merged `t`-motive, a
polynomial row `P` with `P·ψ = 0` and `P(θ) = ρ`, together with the leading-weight relation.  This
file closes Step 2: using the second relation (`TmApply.tmB_relation`), the weight iteration
(`DescentLevel.descent_B_zero_all`) and Chang's MZ property (`DescentIndependent.descent_B_zero`),
**every** coefficient `B̃_t = tmB F w S cf P (some t)` of the second relation vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

section Step2

variable {γ : ℚᵐ⁰} {ω : PowerSeries (Ambient F)}
variable {w : ℕ} {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- **Dac §5.2, Step 2, complete.**  Given the ABP output `P` (`P·ψ = 0`), the `K^{perf}`-membership
of its coefficients, the height bound `twWeight ≤ w` and condition (LW) at every weight level, all
the coefficients `B̃_t = tmB F w S cf P (some t)` of the second relation vanish. -/
theorem step2_B_zero (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    (hΩ0 : (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω).coeff 0 ≠ 0)
    (hΩ1 : ∀ j : ℕ, 2 ≤ j →
      evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
        ((ambTheta F) ^ (Nat.card F) ^ j) = 0)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0)
    (hw : ∀ s ∈ S, tmWeight s = w)
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (hfe : tmPsiColA F ω w S cf h0 a
      = (coeHom (K := Ambient F)).mapMatrix
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
        frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a))
    (hLW : ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w'} => tmZ (F := F) ω t.1.1))
    {P : Option ↥(tmI S) → Polynomial (Ambient F)}
    (hPmem : ∀ j k, (P j).coeff k ∈ ambKperf F)
    (hP : ∑ j, coeHom (K := Ambient F) (P j) * tmPsiColA F ω w S cf h0 a j = 0) :
    ∀ t : ↥(tmI S), tmB F w S cf P (some t) = 0 := by
  classical
  have hΩne : frobTwist (R := Ambient F) (p := Nat.card F) 1 ω ≠ 0 := by
    intro hz
    have h : PowerSeries.coeff 0 (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) = 0 := by
      rw [hz, map_zero]
    exact hΩ0 h
  -- ## (1) the polynomial relation, split into the `none` and the `some` parts
  have hrel := tmB_relation F (w := w) (S := S) (cf := cf) hA hfe hP
  rw [Fintype.sum_option] at hrel
  have hnone : coeHom (K := Ambient F) (tmB F w S cf P none)
      * frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) none = 0 := by
    rw [tmB_none, map_zero, zero_mul]
  rw [hnone, zero_add] at hrel
  -- ## (2) pull out the entries of the twisted column
  have hterm : ∀ t : ↥(tmI S), coeHom (K := Ambient F) (tmB F w S cf P (some t))
      * frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) (some t)
      = coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1)) := by
    intro t
    rw [frobTwistVec_apply, tmPsiColA_some, frobTwist_mul, frobTwist_pow]
  have hrel' : (∑ t ∈ (Finset.univ : Finset ↥(tmI S)),
      coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω) ^ (w - tmWeight t.1))) = 0 := by
    rw [← hrel]
    exact Finset.sum_congr rfl fun t _ => (hterm t).symm
  -- ## (3) the `K^{perf}`-membership of the coefficients
  have hTwist : ∀ {p : Polynomial (Ambient F)}, (∀ m, p.coeff m ∈ ambKperf F) → ∀ m,
      (polyTwist (q := Nat.card F) 1 p).coeff m ∈ ambKperf F := by
    intro p hp m
    rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply]
    exact Subfield.pow_mem _ (hp m) _
  have hSum : ∀ (j : Option ↥(tmI S)) (m : ℕ),
      ((∑ i, P i * (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j))).coeff m
        ∈ ambKperf F := by
    intro j m
    rw [Polynomial.finsetSum_coeff]
    refine Subfield.sum_mem _ fun i _ => ?_
    rw [Polynomial.coeff_mul]
    exact Subfield.sum_mem _ fun x _ =>
      Subfield.mul_mem _ (hPmem i x.1) (ambA_subset_ambKperf F 0 (hA i j x.2))
  have hBmem : ∀ (t : ↥(tmI S)) (m : ℕ), (tmB F w S cf P (some t)).coeff m ∈ ambKperf F := by
    intro t m
    rw [tmB, Polynomial.coeff_sub, Polynomial.coeff_mul, Polynomial.coeff_mul]
    refine Subfield.sub_mem _ ?_ ?_
    · exact Subfield.sum_mem _ fun x _ =>
        Subfield.mul_mem _ (hPmem none x.1) (hTwist (hPmem (some t)) x.2)
    · exact Subfield.sum_mem _ fun x _ =>
        Subfield.mul_mem _ (hTwist (hPmem none) x.1) (hSum (some t) x.2)
  -- ## (4) the weight iteration
  have hwle : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w := fun t =>
    tmWeight_le_of_mem_tmI (S := S) (w := w) t.2 (fun s hs => hw s hs)
  exact descent_B_zero_all (F := F) hγ0 hγ harch hq hω hωse hc hωfe hΩ1 hΩne
    hsm hSse hpos hQmem hLW hwle hBmem hrel'

end Step2

end ZagierHoffmanPositiveChar
