import Mathlib
import Submission.FixedUDefs
import Submission.Deep
import Submission.DeepCore
import Submission.Case2Count
set_option maxRecDepth 20000

/-!
# Case-2 fibre bound and weighted sum

Given the *per-(A0,C0) V-count* `case2_Vcount` (proved in Case2Count.lean),
we derive the fibre-level bound and then bound the weighted case-2 sum.

## Notation
- `Fbound X U v r := (X.card)/((X\U).card) · (1 + (X\U).card/(v·r))`
- 𝒱 := cardSubsets (X\U) v,  C(N,v) := |𝒱|.
- case2Fiber(s,t) := {(V,A) ∈ 𝒱×S : sVal A = s ∧ tVal V A = t ∧ case2p}.
- idxSet k, wfib(s,t) = exp(26t−20s), rho = 2^16.

## theorem case2Fiber_le
  |case2Fiber(s,t)| ≤ |S| · C(s,t) · C(N,v) · rho^{-s} · Fbound^{s-t}

### Proof sketch (case2Fiber_le)
1. case2Fiber(s,t) counts pairs (V,A) with case2p; each such pair has some
   witness C ⊆ χ(A,U), |C| = t, φ(s,t) < |τ(C,V∪χ(A,U),s)|.  Hence
     |case2Fiber| ≤ Σ_{A ∈ S} Σ_{C ∈ (χ(A,U)).powersetCard t}
                       #{V ∈ 𝒱 : φ(s,t) < |τ(C,V∪χ(A,U),s)|}.
   (Sum over all A ∈ S: for A with sVal A ≠ s there are no pairs, the bound
   still holds because we multiply by the indicator of membership; the proof
   can simply show the inequality for the sum restricted to pairs.)
   In real sums:
     ((case2Fiber(s,t)).card : ℝ)
       ≤ (𝒱).sum (fun V => S.sum (fun A => Σ_{C ∈ (χ(A,U)).powersetCard t}
            (if φ < |τ(...)| then 1 else 0)))           -- overcounts fine
       = (S).sum (fun A => ((χ(A,U)).powersetCard t).card •
            #{V : φ<|τ|})  -- hmm careful: do it as: ≤ Σ_A (#P(A))·(max V count)
2. For each (A,C): #{V: φ<|τ|} ≤ C(N,v)·rho^{-s}·Fbound^{s-t}
   by `case2_Vcount` (its hypotheses: A∈S, (chi S U A).card = s, C ⊆ χ, |C| = t,
   1 ≤ t, spreadness, k-uniformity, U⊆X, members⊆X, 0<v, 0<|X|, 1≤r, v≤N).
   Apply with s := sVal A.  For A with sVal A ≠ s we may ignore (use
   `if sVal A = s then ... else 0` indicators); for A with sVal A = s we get
   the bound.
3. #((χ(A,U)).powersetCard t) = (χ(A,U)).card.choose t = s.choose t when
   sVal A = s (use `Finset.card_powersetCard`).
4. Σ_{A ∈ S, sVal A = s} 1 ≤ |S|.  Hence ≤ |S|·(s.choose t)·C(N,v)·rho^{-s}·Fbound^{s-t}.

## theorem case2Sum_le
  Σ_{j ∈ idxSet k} wfib(j)·|case2Fiber(j.1,j.2)| ≤ 2·|S|·C(N,v)

### Proof sketch (case2Sum_le)
1. From case2Fiber_le per fibre (1 ≤ j.2 ≤ j.1 via membership in idxSet):
     Σ_j wfib·fiber ≤ Σ_j wfib(j)·|S|·C(j.1,j.2)·C(N,v)·rho^{-j.1}·Fbound^{j.1-j.2}
2. Σ over j = Σ_{s ∈ Icc 1 k} Σ_{t ∈ Icc 1 s}.  Per s:
     Σ_{t ≤ s} C(s,t)·Fbound^{s-t}·exp(26t) ≤ (Fbound + exp 26)^s
   (binomial theorem; the t=0 term is dropped, so ≤).
3. Hence Σ_j ... ≤ |S|·C(N,v)·Σ_{s∈Icc1k} x^s with
     x := (Fbound + exp 26)·exp(-20)·rho^{-1}.
4. Numeric: Fbound ≤ 4 (prove it in this file or import; statement gives the
   hypotheses 8·U.card ≤ X.card, U⊆X, ...), so x ≤ 1/2 via
   `x2_ratio_le_half` (FixedUDefs), and Σ_{s∈Icc1k} x^s ≤ 1 via
   `sum_x_Icc_le_one`.  Conclude ≤ |S|·C(N,v).
   (If you prefer an easier bound with a factor of 2 that is also fine —
   conclude ≤ 2·|S|·C(N,v).)
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- the F-factor appearing in the case-2 bound -/
noncomputable def Fbound (X U : Finset α) (v : ℕ) (r : ℝ) : ℝ :=
  ((X.card : ℝ) / ((X \ U).card : ℝ)) *
    (1 + ((X \ U).card : ℝ) / ((v : ℝ) * r))

/-- case-2 fibre bound from the per-(A0,C0) V-count -/
theorem case2Fiber_le {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k : ℕ} {r : ℝ} {s t : ℕ}
    (huni : ∀ A ∈ S, A.card = k) (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hr1 : 1 ≤ r) (hv : 0 < v) (hn : 0 < X.card) (hvn : v ≤ (X \ U).card)
    (ht1 : 1 ≤ t) (hts : t ≤ s) :
    (((case2Fiber X S U v r k s t).card : ℝ) ≤
      (S.card : ℝ) * ((s.choose t : ℕ) : ℝ) * (cardSubsets (X \ U) v).card *
        (((rho : ℝ) ^ s)⁻¹) * (Fbound X U v r) ^ (s - t)) := by
  classical
  let VV : Finset (Finset α) := cardSubsets (X \ U) v
  let F : Finset (Finset α × Finset α) := case2Fiber X S U v r k s t
  let Sf : Finset (Finset α) := S.filter (fun A : Finset α => sVal S U A = s)
  let Cnt : Finset α → Finset (Finset α) := fun A0 =>
    VV.filter (fun V => sVal S U A0 = s ∧ tVal S U V A0 = t ∧ case2p S X U V A0 r k v)
  let PC : Finset α → Finset (Finset α) := fun A0 => (chi S U A0).powersetCard t
  let VCnt : Finset α → Finset α → Finset (Finset α) := fun A0 C =>
    VV.filter (fun V => phiVal r k X v s t < ((tau S U C (V ∪ chi S U A0) s).card : ℝ))
  let SC : ℝ := ((s.choose t : ℕ) : ℝ)
  let bd : ℝ := (VV.card : ℝ) * (((rho : ℝ) ^ s)⁻¹) * (Fbound X U v r) ^ (s - t)
  have hNpos : 0 < (X \ U).card := by omega
  have hNcast : 0 < ((X \ U).card : ℝ) := by exact_mod_cast hNpos
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hFB0 : 0 ≤ Fbound X U v r := by
    unfold Fbound
    positivity
  have hrho : 0 < (rho : ℝ) := by unfold rho; positivity
  have hbd0 : 0 ≤ bd := by
    dsimp [bd]
    positivity
  have hov : F.card ≤ ∑ A0 ∈ Sf, (Cnt A0).card := by
    have hfiber : F.card = ∑ A0 ∈ Sf, ((F.filter (fun p : Finset α × Finset α => p.2 = A0)).card) := by
      refine Finset.card_eq_sum_card_fiberwise (s := F) (t := Sf)
        (f := fun p : Finset α × Finset α => p.2) ?_
      intro p hp
      rcases p with ⟨V, A⟩
      have hpF : (V, A) ∈ case2Fiber X S U v r k s t := by
        dsimp [F] at hp
        exact hp
      have hpF' := hpF
      rw [case2Fiber, Finset.mem_filter] at hpF'
      rcases hpF' with ⟨hpP, hpCond⟩
      have hAS : A ∈ S := by
        have hP' : (V, A) ∈ pairSet X S U v := hpP
        unfold pairSet at hP'
        exact (Finset.mem_product.mp hP').2
      have hcond : sVal S U A = s ∧ tVal S U V A = t ∧ case2p S X U V A r k v := by
        simpa using hpCond
      simpa [Sf] using ⟨hAS, hcond.1⟩
    calc
      F.card = ∑ A0 ∈ Sf, ((F.filter (fun p : Finset α × Finset α => p.2 = A0)).card) := hfiber
      _ ≤ ∑ A0 ∈ Sf, (Cnt A0).card := by
        apply Finset.sum_le_sum
        intro A0 hA0
        refine Finset.card_le_card_of_injOn (fun p : Finset α × Finset α => p.1) ?_ ?_
        · intro p hp
          rcases p with ⟨V, A⟩
          have hpF : (V, A) ∈ F := (Finset.mem_filter.mp hp).1
          have hA0eq : A = A0 := by
            simpa using (Finset.mem_filter.mp hp).2
          subst A0
          have hpF' : (V, A) ∈ case2Fiber X S U v r k s t := by
            dsimp [F] at hpF
            exact hpF
          have hpF'' := hpF'
          rw [case2Fiber, Finset.mem_filter] at hpF''
          rcases hpF'' with ⟨hpP, hpCond⟩
          have hVv : V ∈ cardSubsets (X \ U) v := by
            have hP' : (V, A) ∈ pairSet X S U v := hpP
            unfold pairSet at hP'
            exact (Finset.mem_product.mp hP').1
          have hcond : sVal S U A = s ∧ tVal S U V A = t ∧ case2p S X U V A r k v := by
            simpa using hpCond
          simpa [Cnt, VV] using ⟨hVv, hcond⟩
        · intro p hp q hq hpq
          have hp2 : p.2 = A0 := (Finset.mem_filter.mp hp).2
          have hq2 : q.2 = A0 := (Finset.mem_filter.mp hq).2
          ext x <;> simp [hpq, hp2, hq2]
  have hA0b : ∀ A0 ∈ Sf, ((Cnt A0).card : ℝ) ≤ SC * bd := by
    intro A0 hA0
    have hA0S : A0 ∈ S := (Finset.mem_filter.mp hA0).1
    have hA0s : sVal S U A0 = s := (Finset.mem_filter.mp hA0).2
    have hχs : (chi S U A0).card = s := by simpa [sVal] using hA0s
    have hcnt_le_sum : (Cnt A0).card ≤ ∑ C ∈ PC A0, (VCnt A0 C).card := by
      calc
        (Cnt A0).card ≤ (((PC A0).biUnion (fun C : Finset α => VCnt A0 C))).card := by
          apply Finset.card_le_card
          intro V hV
          have hVv : V ∈ VV := (Finset.mem_filter.mp hV).1
          rcases (Finset.mem_filter.mp hV).2 with ⟨hsA, htA, hc2⟩
          rcases hc2 with ⟨C, hCsub, hCcard, hphi⟩
          rw [Finset.mem_biUnion]
          refine ⟨C, ?_, ?_⟩
          · rw [Finset.mem_powersetCard]
            exact ⟨hCsub, by simpa [htA] using hCcard⟩
          · rw [Finset.mem_filter]
            exact ⟨hVv, by simpa [hsA, htA] using hphi⟩
        _ ≤ ∑ C ∈ PC A0, (VCnt A0 C).card := Finset.card_biUnion_le
    have hCb : ∀ C ∈ PC A0, ((VCnt A0 C).card : ℝ) ≤ bd := by
      intro C hC
      have hCsub : C ⊆ chi S U A0 := (Finset.mem_powersetCard.mp hC).1
      have hCt : C.card = t := (Finset.mem_powersetCard.mp hC).2
      have hvc := case2_Vcount (X := X) (S := S) (U := U) (A0 := A0) (C0 := C) (v := v) (k := k)
        (s := s) (t := t) (r := r) hspread huni hU hS hA0S hχs hCsub hCt ht1 hv hn hr1 hvn
      simpa [VCnt, VV, bd, Fbound] using hvc
    calc
      ((Cnt A0).card : ℝ) ≤ (∑ C ∈ PC A0, ((VCnt A0 C).card : ℝ)) := by exact_mod_cast hcnt_le_sum
      _ ≤ (∑ C ∈ PC A0, bd) := by
        apply Finset.sum_le_sum
        intro C hC
        exact hCb C hC
      _ = ((PC A0).card : ℝ) * bd := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
      _ = SC * bd := by
        have hpc : (PC A0).card = s.choose t := by
          calc
            (PC A0).card = (chi S U A0).card.choose t := by simp [PC]
            _ = s.choose t := by rw [hχs]
        rw [hpc]
  calc
    ((case2Fiber X S U v r k s t).card : ℝ)
        = (F.card : ℝ) := by rfl
    _ ≤ (∑ A0 ∈ Sf, (Cnt A0).card : ℝ) := by
        exact_mod_cast hov
    _ ≤ (∑ A0 ∈ Sf, SC * bd) := by
        apply Finset.sum_le_sum
        intro A0 hA0
        exact hA0b A0 hA0
    _ = ((Sf.card : ℕ) : ℝ) * (SC * bd) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
    _ ≤ (S.card : ℝ) * (SC * bd) := by
        have hle : (Sf.card : ℝ) ≤ (S.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun A : Finset α => sVal S U A = s) S)
        exact mul_le_mul_of_nonneg_right hle (by
          have hSC0 : 0 ≤ SC := by dsimp [SC]; positivity
          exact mul_nonneg hSC0 hbd0)
    _ = (S.card : ℝ) * ((s.choose t : ℕ) : ℝ) * (cardSubsets (X \ U) v).card *
        (((rho : ℝ) ^ s)⁻¹) * (Fbound X U v r) ^ (s - t) := by
        dsimp [SC, bd, VV]
        ring

private lemma c2sum_ite_Icc_le_s_aux {s k : ℕ} (hs1 : 1 ≤ s) (hsk : s ≤ k) (f : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 k, if t ≤ s then f t else 0) = ∑ t ∈ Finset.Icc 1 s, f t := by
  classical
  calc
    (∑ t ∈ Finset.Icc 1 k, if t ≤ s then f t else 0)
        = ∑ t ∈ (Finset.Icc 1 k).filter (fun t => t ≤ s), f t := by
          rw [Finset.sum_filter]
    _ = ∑ t ∈ Finset.Icc 1 s, f t := by
          congr 1
          ext t
          constructor
          · intro ht
            have h := Finset.mem_filter.mp ht
            have h1 : 1 ≤ t := (Finset.mem_Icc.mp h.1).1
            exact Finset.mem_Icc.mpr ⟨h1, h.2⟩
          · intro ht
            have h := Finset.mem_Icc.mp ht
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_Icc.mpr ⟨h.1, le_trans h.2 hsk⟩, h.2⟩

private lemma c2sum_idxSet_aux {k : ℕ} (f : ℕ × ℕ → ℝ) :
    (∑ j ∈ idxSet k, f j) = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s, f (s, t) := by
  classical
  calc
    (∑ j ∈ idxSet k, f j) = ∑ j ∈ ((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).filter (fun (s,t) => t ≤ s), f j := by
        rfl
    _ = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 k, if t ≤ s then f (s, t) else 0 := by
        rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s, f (s, t) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
          have hsk : s ≤ k := (Finset.mem_Icc.mp hs).2
          exact c2sum_ite_Icc_le_s_aux (s := s) (k := k) hs1 hsk (fun t => f (s, t))

private lemma c2wfib_eq_exp (s t : ℕ) :
    wfib (s, t) = (Real.exp (-20)) ^ s * (Real.exp 26) ^ t := by
  have h1 : Real.exp ((26 : ℝ) * (t : ℝ)) = (Real.exp 26) ^ t := by
    have h : (26 : ℝ) * (t : ℝ) = ((t : ℕ) : ℝ) * (26 : ℝ) := by ring
    rw [h]
    exact Real.exp_nat_mul (26 : ℝ) t
  have h2 : Real.exp (-((20 : ℝ) * (s : ℝ))) = (Real.exp (-20)) ^ s := by
    have h : -((20 : ℝ) * (s : ℝ)) = ((s : ℕ) : ℝ) * (-20 : ℝ) := by ring
    rw [h]
    exact Real.exp_nat_mul (-20 : ℝ) s
  calc
    wfib (s, t) = Real.exp ((26 : ℝ) * (t : ℝ) - (20 : ℝ) * (s : ℝ)) := rfl
    _ = Real.exp ((26 : ℝ) * (t : ℝ)) * Real.exp (-((20 : ℝ) * (s : ℝ))) := by
        rw [show (26 : ℝ) * (t : ℝ) - (20 : ℝ) * (s : ℝ) = (26 : ℝ) * (t : ℝ) + (-((20 : ℝ) * (s : ℝ))) by ring]
        rw [Real.exp_add]
    _ = (Real.exp 26) ^ t * (Real.exp (-20)) ^ s := by rw [h1, h2]
    _ = (Real.exp (-20)) ^ s * (Real.exp 26) ^ t := by ring

private lemma c2binom_le {s : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ t ∈ Finset.Icc 1 s, ((s.choose t : ℕ) : ℝ) * a ^ t * b ^ (s - t)) ≤ (a + b) ^ s := by
  classical
  calc
    (∑ t ∈ Finset.Icc 1 s, ((s.choose t : ℕ) : ℝ) * a ^ t * b ^ (s - t))
        ≤ (∑ t ∈ Finset.range (s + 1), ((s.choose t : ℕ) : ℝ) * a ^ t * b ^ (s - t)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hf
          · intro t ht
            have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
            have hts : t ≤ s := (Finset.mem_Icc.mp ht).2
            rw [Finset.mem_range]
            omega
          · intro t ht htn
            exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg ha t)) (pow_nonneg hb (s - t))
    _ = (a + b) ^ s := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro t ht
          ring

private lemma c2inner_le {s : ℕ} {FB : ℝ} (hFB0 : 0 ≤ FB) :
    (∑ t ∈ Finset.Icc 1 s,
        wfib (s, t) * ((s.choose t : ℕ) : ℝ) * (((rho : ℝ) ^ s)⁻¹) * (FB ^ (s - t)))
      ≤ ((FB + Real.exp 26) * Real.exp (-20) / (rho : ℝ)) ^ s := by
  classical
  let A : ℝ := (Real.exp (-20)) ^ s * ((rho : ℝ) ^ s)⁻¹
  have hbin := c2binom_le (s := s) (a := Real.exp 26) (b := FB) (by positivity) hFB0
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (pow_nonneg (by positivity) s) (inv_nonneg.mpr (pow_nonneg (by unfold rho; positivity) s))
  calc
    (∑ t ∈ Finset.Icc 1 s, wfib (s,t) * ((s.choose t : ℕ) : ℝ) * ((rho : ℝ)^s)⁻¹ * FB ^ (s - t))
        = ∑ t ∈ Finset.Icc 1 s, A * (((Real.exp 26) ^ t) * ((s.choose t : ℕ) : ℝ) * FB ^ (s - t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          dsimp [A]
          rw [c2wfib_eq_exp s t]
          ring
    _ = A * (∑ t ∈ Finset.Icc 1 s, ((Real.exp 26) ^ t) * ((s.choose t : ℕ) : ℝ) * FB ^ (s - t)) := by
          rw [← Finset.mul_sum]
    _ ≤ A * (Real.exp 26 + FB) ^ s := by
          have hbin' : (∑ t ∈ Finset.Icc 1 s, ((Real.exp 26) ^ t) * ((s.choose t : ℕ) : ℝ) * FB ^ (s - t)) ≤ (Real.exp 26 + FB) ^ s := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hbin
          exact mul_le_mul_of_nonneg_left hbin' hA0
    _ = ((FB + Real.exp 26) * Real.exp (-20) / (rho : ℝ)) ^ s := by
          dsimp [A]
          have h1 : ((rho : ℝ) ^ s)⁻¹ = ((rho : ℝ)⁻¹) ^ s := by rw [inv_pow]
          rw [h1, ← mul_pow, ← mul_pow]
          congr 1
          rw [div_eq_mul_inv]
          ring

/-- the case-2 weighted sum ≤ 2·|S|·C(N,v) -/
theorem case2Sum_le {X : Finset α} {S : Finset (Finset α)} {U : Finset α} {v k : ℕ} {r : ℝ}
    (huni : ∀ A ∈ S, A.card = k) (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X)
    (h8u : 8 * U.card ≤ X.card)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hr1 : 1 ≤ r) (hv : 0 < v) (hn : 0 < X.card) (hvn : v ≤ (X \ U).card)
    (huv : U.card + v ≤ X.card)
    (hkap : (kap * (X.card : ℝ)) / r ≤ (v : ℝ)) :
    (∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card)
      ≤ 2 * (S.card : ℝ) * (cardSubsets (X \ U) v).card := by
  classical
  let Cc : ℝ := ((cardSubsets (X \ U) v).card : ℝ)
  let FB : ℝ := Fbound X U v r
  let Q : ℕ × ℕ → ℝ := fun j => wfib j * ((j.1.choose j.2 : ℕ) : ℝ) * ((rho : ℝ)^j.1)⁻¹ * FB^(j.1 - j.2)
  let x : ℝ := (FB + Real.exp 26) * Real.exp (-20) / (rho : ℝ)
  have hNpos : 0 < (X \ U).card := by omega
  have hNcast : 0 < ((X \ U).card : ℝ) := by exact_mod_cast hNpos
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hFB0 : 0 ≤ FB := by
    dsimp [FB]
    unfold Fbound
    positivity
  have hFBle4 : FB ≤ 4 := by
    have hfl := F_le_four (X := X) (U := U) (v := v) (r := r) hU h8u hr1 hv hn huv hkap
    simpa [FB, Fbound] using hfl
  have hrhopos : 0 < (rho : ℝ) := by unfold rho; positivity
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx12 : x ≤ 1 / 2 := by
    have h := x2_ratio_le_half (F := FB) hFBle4 hFB0
    simpa [x, rho] using h
  have hsumx : (∑ s ∈ Finset.Icc 1 k, x ^ s) ≤ 1 := sum_q_Icc_le_one (s := k) (q := x) hx0 hx12
  have hS0 : 0 ≤ (S.card : ℝ) := by positivity
  have hC0 : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hScc0 : 0 ≤ (S.card : ℝ) * Cc := mul_nonneg hS0 hC0
  have hterm : ∀ j ∈ idxSet k,
      wfib j * ((case2Fiber X S U v r k j.1 j.2).card : ℝ)
        ≤ wfib j * (S.card : ℝ) * ((j.1.choose j.2 : ℕ) : ℝ) * Cc * ((rho : ℝ)^j.1)⁻¹ * FB^(j.1 - j.2) := by
    intro j hj
    have hm := mem_idxSet_iff.mp hj
    have hb := case2Fiber_le (X := X) (S := S) (U := U) (v := v) (k := k) (r := r)
      (s := j.1) (t := j.2) huni hU hS hspread hr1 hv hn hvn hm.2.2.1 hm.2.2.2
    have hw0 : 0 ≤ wfib j := by unfold wfib; positivity
    calc
      wfib j * ((case2Fiber X S U v r k j.1 j.2).card : ℝ)
          ≤ wfib j * ((S.card : ℝ) * ((j.1.choose j.2 : ℕ) : ℝ) * (cardSubsets (X \ U) v).card *
              (((rho : ℝ)^j.1)⁻¹) * (Fbound X U v r)^(j.1 - j.2)) := by
              exact mul_le_mul_of_nonneg_left hb hw0
      _ = wfib j * (S.card : ℝ) * ((j.1.choose j.2 : ℕ) : ℝ) * Cc * ((rho : ℝ)^j.1)⁻¹ * FB^(j.1 - j.2) := by
              dsimp [Cc, FB]
              ring
  calc
    (∑ j ∈ idxSet k, wfib j * (case2Fiber X S U v r k j.1 j.2).card)
        ≤ (∑ j ∈ idxSet k, wfib j * (S.card : ℝ) * ((j.1.choose j.2 : ℕ) : ℝ) * Cc * ((rho : ℝ)^j.1)⁻¹ * FB^(j.1 - j.2)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hterm j hj
    _ = (S.card : ℝ) * Cc * (∑ j ∈ idxSet k, Q j) := by
          calc
            (∑ j ∈ idxSet k, wfib j * (S.card : ℝ) * ((j.1.choose j.2 : ℕ) : ℝ) * Cc * ((rho : ℝ)^j.1)⁻¹ * FB^(j.1 - j.2))
                = (∑ j ∈ idxSet k, (S.card : ℝ) * Cc * Q j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  dsimp [Q]
                  ring
            _ = (S.card : ℝ) * Cc * (∑ j ∈ idxSet k, Q j) := by
                  rw [← Finset.mul_sum]
    _ = (S.card : ℝ) * Cc * (∑ s ∈ Finset.Icc 1 k, ∑ t ∈ Finset.Icc 1 s, Q (s, t)) := by
          rw [c2sum_idxSet_aux]
    _ ≤ (S.card : ℝ) * Cc * (∑ s ∈ Finset.Icc 1 k, x ^ s) := by
          apply mul_le_mul_of_nonneg_left ?_ hScc0
          apply Finset.sum_le_sum
          intro s hs
          have hle := c2inner_le (s := s) (FB := FB) hFB0
          simpa [Q, x] using hle
    _ ≤ (S.card : ℝ) * Cc * 1 := by
          exact mul_le_mul_of_nonneg_left hsumx hScc0
    _ = (S.card : ℝ) * Cc := by ring
    _ ≤ 2 * (S.card : ℝ) * Cc := by nlinarith [hScc0]

end Submission.Sun
