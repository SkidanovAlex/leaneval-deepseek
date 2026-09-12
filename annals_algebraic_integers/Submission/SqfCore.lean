import Mathlib
import Submission.Contracts
import Submission.Contract1Core
import Submission.SecondSqueeze
import Submission.WnormLower
import Submission.GcdInt
import Submission.NocommonGeneral
import Submission.Nocommon
import Submission.RemezComplex
import Submission.Cwnorm
import Submission.RootData
import Submission.ArithmeticAssembly
import Submission.EnergyNeg
import Submission.MinkLower
import Submission.SqfChain
import Submission.SqfNumeric
import Submission.SqfAbsorb
import Submission.SqfStage2

/-!
# Core assembly of Theorem squarefree (Contract 1)

This module contains the long constructive proof of
`Submission.Contracts.SquarefreeContract` from the four module theorems
(Hilbert, second squeeze, weak lower bound, complex Remez), the arithmeticity
(`serre_arithmetic`), and three elementary helper facts supplied as explicit
hypotheses (so this module can be developed and compiled in parallel with the
children proving those helpers):

* `hsort`: any real-valued function on `Fin (N+1)` admits a permutation making
  it nondecreasing (`Submission.SqfSort.exists_sorted_perm`);
* `hchain`: the iterated complex-Remez division bound
  (`Submission.SqfRemez.remez_chain`);
* `hsqfree`: the squarefree-in-ℤ lemma for a primitive part times integer
  linear factors (`Submission.SqfSqfree.squarefree_mul_primPart`).

`Submission/SqfAssembly.lean` instantiates this theorem with the module
results and those three helpers.
-/

noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators
open Polynomial
open MeasureTheory

namespace Submission.SqfCore

open Submission.Contracts
open Submission.MinkBox
open Submission.MinkLower
open Submission.Nocommon
open Submission.Cwnorm
open Submission.SqfChain
open Submission.SecondSqueeze
open Submission.WnormToolkit
open Submission.SerreExample

/-! ## Small reindexing and product lemmas -/

-- Splitting a product over `Fin (n+1)` into the prefix `Fin (m+1)` (values
-- `0..m`) and the tail `Fin (n−m)` (values `m+1..n`). -/
lemma prod_split_prefix_tail {n m : ℕ} (hmn : m ≤ n) {M : Type*} [CommMonoid M]
    (f : Fin (n + 1) → M) :
    (∏ i : Fin (n + 1), f i) =
      (∏ i : Fin (m + 1), f ⟨i.val, by omega⟩) *
        ∏ j : Fin (n - m), f ⟨m + 1 + j.val, by omega⟩ := by
  classical
  have hsum : m + 1 + (n - m) = n + 1 := by omega
  have hD : (∏ k : Fin (m + 1 + (n - m)), f ⟨k.val, by omega⟩) = ∏ i : Fin (n + 1), f i := by
    refine (Fin.prod_congr' (a := m + 1 + (n - m)) (b := n + 1)
      (f := fun i : Fin (n + 1) => f i) hsum).trans ?_
    · apply Finset.prod_congr rfl
      intro i hi
      congr 1
  have hsplit := Fin.prod_univ_add (a := m + 1) (b := n - m)
    (f := fun k : Fin (m + 1 + (n - m)) => f ⟨k.val, by omega⟩)
  rw [← hD]
  rw [hsplit]
  simp

/-- values of a permutation-invariant product do not change when the family is
precomposed with an equivalence. -/
lemma prod_comp_equiv {N : ℕ} {M : Type*} [CommMonoid M] (f : Fin (N + 1) → M)
    (σ : Equiv.Perm (Fin (N + 1))) : (∏ i : Fin (N + 1), f (σ i)) = ∏ i : Fin (N + 1), f i := by
  simpa using (Equiv.prod_comp σ f)

/-- Truncating ℚ-vectors with a common support bound preserves linear
independence. -/
lemma coeffVec_trunc_linIndep {L M : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → ℕ → ℚ)
    (hv : LinearIndependent ℚ (fun i : ι => (fun t : Fin (L + 1) => v i t.val)))
    (hsupp : ∀ (i : ι) (t : ℕ), M < t → v i t = 0) :
    LinearIndependent ℚ (fun i : ι => (fun t : Fin (M + 1) => v i t.val)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hrel
  have hfull : (∑ i : ι, g i • (fun t : Fin (L + 1) => v i t.val)) = 0 := by
    funext t
    by_cases ht : t.val ≤ M
    · have ht1 : t.val < M + 1 := by omega
      calc
        (∑ i : ι, g i • (fun t : Fin (L + 1) => v i t.val)) t
            = ∑ i : ι, g i * v i t.val := by
                simp [Pi.smul_apply, mul_comm]
        _ = (∑ i : ι, g i • (fun t : Fin (M + 1) => v i t.val)) ⟨t.val, ht1⟩ := by
                simp [Pi.smul_apply, mul_comm]
        _ = 0 := by exact congrFun hrel ⟨t.val, ht1⟩
    · have htbig : M < t.val := by omega
      calc
        (∑ i : ι, g i • (fun t : Fin (L + 1) => v i t.val)) t
            = ∑ i : ι, g i * v i t.val := by
                simp [Pi.smul_apply, mul_comm]
        _ = ∑ i : ι, g i * 0 := by
                congr 1
                ext i
                congr 1
                exact hsupp i t.val htbig
        _ = 0 := by simp
  exact (Fintype.linearIndependent_iff.mp hv) g hfull

/-- The degree of a quotient by a nonzero divisor is at most the degree of the
numerator (both nonzero, integral domain). -/
lemma natDegree_quot_le {A B : Polynomial ℤ} (hA : A ≠ 0) (hB : B ≠ 0) (C : Polynomial ℤ)
    (hAB : A = B * C) (hC : C ≠ 0) : C.natDegree ≤ A.natDegree := by
  have hdeg : A.natDegree = B.natDegree + C.natDegree := by
    rw [hAB]
    exact Polynomial.natDegree_mul hB hC
  omega


/-- copies of independence helpers (kept local to avoid importing SqfAssembly) -/
lemma full_indep_of_lin_indep_int {n : ℕ} {Q : Fin (n + 1) → Polynomial ℤ}
    (hQ : LinIndepInt (n + 1) Q) (hdeg : ∀ i, (Q i).natDegree ≤ n) :
    FullIndepPoly (n + 1) Q := by
  classical
  rw [FullIndepPoly]
  rw [Fintype.linearIndependent_iff]
  intro g hrel
  have hvec : (∑ i : Fin (n + 1), g i • coeffVec (n + 1) (Q i)) = 0 := by
    funext t
    calc
      (∑ i : Fin (n + 1), g i • coeffVec (n + 1) (Q i)) t
          = ∑ i : Fin (n + 1), g i * ((Q i).coeff t.val : ℚ) := by
              simp [coeffVec, Pi.smul_apply, mul_comm]
      _ = ((∑ i : Fin (n + 1), g i • (Q i).map (algebraMap ℤ ℚ)).coeff t.val) := by
              simp [Polynomial.coeff_map]
      _ = 0 := by
              rw [hrel]
              simp
  exact (Fintype.linearIndependent_iff.mp hQ) g hvec

/-- coefficient-vector independence (length M+1) + degree ≤ M ⇒ full polynomial ℚ-independence -/
lemma full_poly_indep_of_coeffVec {ι : Type*} [Fintype ι] {M : ℕ} (P : ι → Polynomial ℤ)
    (hv : LinearIndependent ℚ (fun i : ι => (fun t : Fin (M + 1) => ((P i).coeff t.val : ℚ))))
    (hdeg : ∀ i, (P i).natDegree ≤ M) :
    LinearIndependent ℚ (fun i : ι => (P i).map (algebraMap ℤ ℚ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hrel
  have hvec : (∑ i : ι, g i • (fun t : Fin (M + 1) => ((P i).coeff t.val : ℚ))) = 0 := by
    funext t
    calc
      (∑ i : ι, g i • (fun t : Fin (M + 1) => ((P i).coeff t.val : ℚ))) t
          = ∑ i : ι, g i * ((P i).coeff t.val : ℚ) := by
              simp [Pi.smul_apply, mul_comm]
      _ = ((∑ i : ι, g i • (P i).map (algebraMap ℤ ℚ)).coeff t.val) := by
              simp [Polynomial.coeff_map]
      _ = 0 := by
              rw [hrel]
              simp
  exact (Fintype.linearIndependent_iff.mp hv) g hvec

/-- THE core theorem: Theorem squarefree assembled from the ingredients. -/
theorem core_squarefree
    (hsort : ∀ {N : ℕ} (g : Fin (N + 1) → ℝ),
      ∃ σ : Equiv.Perm (Fin (N + 1)),
        ∀ ⦃i j : Fin (N + 1)⦄, i.val ≤ j.val → g (σ i) ≤ g (σ j))
    (hchain : ∀ (C : ℝ), 0 < C →
      (∀ (N m : ℕ), 1 ≤ m → ∀ (P : Polynomial ℂ), P.natDegree = m → ∀ α : ℂ,
        P.eval α = 0 → ∃ Q : Polynomial ℂ,
          P = (Polynomial.X - Polynomial.C α) * Q ∧
            cwnorm N Q ≤ ((2 * max N m : ℕ) : ℝ) ^ C * cwnorm N P) →
      ∀ {n : ℕ}, 2 ≤ n → ∀ (H A : Polynomial ℂ), H ≠ 0 → A ≠ 0 →
        (H * A).natDegree ≤ n → 1 ≤ ‖H.leadingCoeff‖ →
          cwnorm n A ≤ ((2 * n : ℕ) : ℝ) ^ (C * (H.natDegree : ℝ)) * cwnorm n (H * A))
    (hsqfree : ∀ {A : Polynomial ℤ}, A ≠ 0 →
      (A.map (algebraMap ℤ ℂ)).Separable → ∀ (S : Finset ℕ),
        (∀ s ∈ S, ¬ Polynomial.aeval (s : ℂ) (A.map (algebraMap ℤ ℂ)) = 0) →
          Squarefree (A.primPart * S.prod (fun s : ℕ =>
            (Polynomial.X - Polynomial.C (s : ℤ))))) :
    SquarefreeContract := by
  classical
  rcases Contract1Core.hilbert with ⟨Ch, hChpos, hhilb⟩
  rcases SecondSqueeze.second_squeeze with ⟨C2, hC2pos, hss⟩
  rcases WnormLower.wnorm_lower with ⟨Cw, hCwpos, hwl⟩
  rcases RemezComplex.complex_remez with ⟨CR, hCRpos, hcr⟩
  have hserre : ∀ G : Polynomial ℤ, G ≠ 0 →
      0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x G| ∂muSerre := by
    intro G hG
    exact ArithmeticAssembly.serre_arithmetic G hG
  have hEn : Submission.EnergyHalf.energy ≤ 0 := Contract1Core.energy_nonpos
  let B : ℝ := Submission.SerreExample.bSerre
  have hB : 0 ≤ B := le_of_lt Submission.SerreExample.bSerre_pos
  let Cb : ℝ := Ch + C2 + Cw
  let Cbig : ℝ := Cb + 2 * CR + 1 + Real.log (1 + B) / Real.log 2 + 5 / Real.sqrt 2
  refine ⟨Cbig, ?_, ?_⟩
  · -- 0 < Cbig
    dsimp [Cbig]
    have h1 : 0 ≤ Real.log (1 + B) / Real.log 2 := by
      apply div_nonneg
      · exact Real.log_nonneg (by linarith)
      · exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have h2 : 0 < (5 / Real.sqrt 2 : ℝ) := by positivity
    have h3 : 0 < Cb := by
      dsimp [Cb]
      nlinarith [hChpos, hC2pos, hCwpos]
    nlinarith [hCRpos, h3, h1, h2]
  · -- main: for every n ≥ 2 build the squarefree polynomial
    intro n hn2
    -- STEP A: Hilbert family, then sort by norms
    rcases hhilb n hn2 with ⟨Qraw, hQrawLin, hQrawDeg, hQrawProd⟩
    let g0 : Fin (n + 1) → ℝ := fun i => wnorm n (zmap (Qraw i))
    rcases hsort g0 with ⟨σ, hsortσ⟩
    let Q : Fin (n + 1) → Polynomial ℤ := fun i => Qraw (σ i)
    have hQlin : LinIndepInt (n + 1) Q := by
      dsimp [Q, LinIndepInt]
      exact hQrawLin.comp σ σ.injective
    have hQdeg : ∀ i : Fin (n + 1), (Q i).natDegree ≤ n := by
      intro i
      exact hQrawDeg (σ i)
    have hQnz : ∀ i : Fin (n + 1), Q i ≠ 0 := by
      intro i
      exact MinkLower.Q_ne_zero_of_LinIndepInt Q hQlin i
    have hQprod : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
        (n : ℝ) ^ (Ch * (n : ℝ)) *
          Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * Submission.EnergyHalf.energy) := by
      calc
        (∏ i : Fin (n + 1), wnorm n (zmap (Q i)))
            = ∏ i : Fin (n + 1), wnorm n (zmap (Qraw (σ i))) := by rfl
        _ = ∏ i : Fin (n + 1), wnorm n (zmap (Qraw i)) := by
            exact prod_comp_equiv (fun i : Fin (n + 1) => wnorm n (zmap (Qraw i))) σ
        _ ≤ (n : ℝ) ^ (Ch * (n : ℝ)) *
            Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * Submission.EnergyHalf.energy) := hQrawProd
    have hQsort : ∀ ⦃i j : Fin (n + 1)⦄, i.val ≤ j.val →
        wnorm n (zmap (Q i)) ≤ wnorm n (zmap (Q j)) := by
      intro i j hij
      simpa [Q, g0] using (hsortσ (i := i) (j := j) hij)
    have hwpos : ∀ i : Fin (n + 1), 0 < wnorm n (zmap (Q i)) := by
      intro i
      exact EnergyNeg.wnorm_zmap_pos n (Q i) (hQnz i)
    let w : Fin (n + 1) → ℝ := fun i => wnorm n (zmap (Q i))
    have hwnat : ∀ (a : ℕ) (ha : a ≤ n), 0 < wnorm n (zmap (Q ⟨a, Nat.lt_succ_of_le ha⟩)) := by
      intro a ha
      exact hwpos ⟨a, Nat.lt_succ_of_le ha⟩
    have hwsortNat : ∀ ⦃a b : ℕ⦄ (ha : a ≤ n) (hb : b ≤ n), a ≤ b →
        wnorm n (zmap (Q ⟨a, Nat.lt_succ_of_le ha⟩)) ≤
          wnorm n (zmap (Q ⟨b, Nat.lt_succ_of_le hb⟩)) := by
      intro a b ha hb hab
      exact hQsort (i := ⟨a, Nat.lt_succ_of_le ha⟩) (j := ⟨b, Nat.lt_succ_of_le hb⟩) hab
    -- ============ TAIL (dev) ============
    -- (0) constants & basic real facts
    have hn1 : 1 ≤ n := by omega
    let s : ℕ := Nat.ceil (Real.sqrt (n : ℝ))
    have hs_le_n : s ≤ n := by simpa [s] using SqfNumeric.ceil_sqrt_le_self_nat hn1
    have hs_pos : 0 < s := by simpa [s] using SqfNumeric.ceil_sqrt_pos hn1
    have hs_ge_sqrt : Real.sqrt (n : ℝ) ≤ (s : ℝ) := by simpa [s] using (Nat.le_ceil (Real.sqrt (n : ℝ)))
    have hnR2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnRpos : 0 < (n : ℝ) := by positivity
    have hEnE : Submission.EnergyHalf.energy ≤ 0 := hEn
    -- (1) prefix gcd chain: total function mfn
    have hFull : FullIndepPoly (n + 1) Q := full_indep_of_lin_indep_int hQlin hQdeg
    let mfn : ℕ → ℕ := fun j => if h : j ≤ n then mJ Q h else 0
    have mfn_eq : ∀ j (hj : j ≤ n), mfn j = mJ Q hj := by
      intro j hj
      dsimp [mfn]
      rw [dif_pos hj]
    have emb_inj : ∀ {j : ℕ} (hj : j ≤ n), Function.Injective (emb hj) := by
      intro j hj a b hab
      apply Fin.ext
      have hv : (emb hj a).val = (emb hj b).val := congrArg Fin.val hab
      simpa [emb] using hv
    have hpre_indep : ∀ j (hj : j ≤ n), LinearIndependent ℚ (fun i : Fin (j + 1) =>
        (Q (emb hj i)).map (algebraMap ℤ ℚ)) := by
      intro j hj
      have hcomp : LinearIndependent ℚ (fun i : Fin (j + 1) =>
          coeffVec (n + 1) (Q (emb hj i))) := by
        change LinearIndependent ℚ (fun i : Fin (j + 1) => coeffVec (n + 1) (Q (emb hj i)))
        exact hQlin.comp (emb hj) (emb_inj hj)
      exact full_poly_indep_of_coeffVec (P := fun i : Fin (j + 1) => Q (emb hj i)) (M := n)
        hcomp (fun i => hQdeg (emb hj i))
    have hmfn_le : ∀ j (hj : j ≤ n), mfn j ≤ n := by
      intro j hj
      rw [mfn_eq j hj]
      exact mJ_le_n Q hj hQnz hQdeg
    have hmfn_ge : ∀ j (hj : j ≤ n), j ≤ mfn j := by
      intro j hj
      rw [mfn_eq j hj]
      exact mJ_ge_j Q hj hQnz (hpre_indep j hj)
    have hmfn_mono : ∀ ⦃j1 j2 : ℕ⦄ (hj1 : j1 ≤ n) (hj2 : j2 ≤ n), j1 ≤ j2 → mfn j1 ≤ mfn j2 := by
      intro j1 j2 hj1 hj2 hle
      rw [mfn_eq j1 hj1, mfn_eq j2 hj2]
      exact mJ_mono_le Q hQnz hj1 hj2 hle
    have hgdeg : ∀ j (hj : j ≤ n), (gJ Q hj).natDegree ≤ n - mfn j := by
      intro j hj
      rw [mfn_eq j hj]
      exact gJ_deg_le Q hj hQnz hQdeg
    have hmfn0 : mfn 0 = 0 := by
      have h00 : 0 ≤ n := Nat.zero_le n
      rw [mfn_eq 0 h00]
      -- single member prefix: quotient is a unit
      unfold mJ
      have huniv : (Finset.univ : Finset (Fin (0 + 1))) = {0} := by
        ext x
        fin_cases x
        simp
      rw [huniv]
      simp
      let S : Polynomial ℤ := sJ Q (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)
      let G : Polynomial ℤ := gJ Q (show 0 ≤ n from Nat.zero_le n)
      have hdiv : Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)) = G * S := by
        dsimp [S, G]
        exact sJ_div Q (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)
      have hQ0dvdG : Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)) ∣ G := by
        dsimp [G]
        exact gJ_max Q (show 0 ≤ n from Nat.zero_le n) (Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)))
          (by intro i; fin_cases i; rfl)
      rcases hQ0dvdG with ⟨T, hT⟩
      have hQ0nz : Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)) ≠ 0 :=
        hQnz (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1))
      have hTS : T * S = 1 := by
        apply mul_left_cancel₀ hQ0nz
        calc
          Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)) * (T * S)
              = (Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)) * T) * S := by ring
          _ = G * S := by rw [hT]
          _ = Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)) := hdiv.symm
          _ = Q (emb (show 0 ≤ n from Nat.zero_le n) (0 : Fin 1)) * 1 := by ring
      have hSunit : IsUnit S := by
        rw [isUnit_iff_exists_inv]
        exact ⟨T, by simpa [mul_comm] using hTS⟩
      have hdegS : S.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hSunit
      simpa [S] using hdegS
    -- (2) crossing index: j0 minimal with n−s < mfn j0; k0 := j0 − 1
    have hex_j0 : ∃ j : ℕ, n - s < mfn j := by
      refine ⟨n, ?_⟩
      have hmn_n : n ≤ mfn n := hmfn_ge n le_rfl
      have hslt : n - s < n := Nat.sub_lt (by omega : 0 < n) hs_pos
      exact lt_of_lt_of_le hslt hmn_n
    let j0 : ℕ := Nat.find hex_j0
    have hj0_spec : n - s < mfn j0 := by
      dsimp [j0]
      exact Nat.find_spec hex_j0
    have hj0_min : ∀ j : ℕ, n - s < mfn j → j0 ≤ j := by
      intro j hj
      dsimp [j0]
      exact Nat.find_min' hex_j0 hj
    have hj0_le_n : j0 ≤ n := by
      dsimp [j0]
      exact Nat.find_le (p := fun j : ℕ => n - s < mfn j) (h := hex_j0) (n := n) (by
        have hmn_n : n ≤ mfn n := hmfn_ge n le_rfl
        have hslt : n - s < n := Nat.sub_lt (by omega : 0 < n) hs_pos
        exact lt_of_lt_of_le hslt hmn_n)
    have hj0_pos : 0 < j0 := by
      by_contra h
      have hj00 : j0 = 0 := by omega
      have hnot : ¬ n - s < mfn 0 := by
        intro hb
        have h01 : mfn 0 = 0 := hmfn0
        rw [h01] at hb
        omega
      exact hnot (by simpa [hj00] using hj0_spec)
    let k0 : ℕ := j0 - 1
    have hk0_lt_j0 : k0 < j0 := by
      dsimp [k0]
      omega
    have hk0_le_n : k0 ≤ n := by omega
    have hk0_succ_le_n : k0 + 1 ≤ n := by
      dsimp [k0]
      omega
    have hk0_below : mfn k0 ≤ n - s := by
      have hnm : ¬ n - s < mfn k0 := by
        intro hb
        have : j0 ≤ k0 := hj0_min k0 hb
        omega
      exact le_of_not_gt hnm
    have hj0_above : n - s < mfn (k0 + 1) := by
      have hkj : k0 + 1 = j0 := by
        dsimp [k0]
        omega
      simpa [hkj] using hj0_spec
    have hk0_ge_j : k0 ≤ mfn k0 := hmfn_ge k0 hk0_le_n
    have hk0_cases : k0 = 0 ∨ 1 ≤ k0 := by omega
    -- m := mfn k0 ; M := mfn (mfn k0 + 1)
    let m : ℕ := mfn k0
    have hm_le_n : m ≤ n := by
      dsimp [m]
      exact hmfn_le k0 hk0_le_n
    have hm_le_ns : m ≤ n - s := by
      dsimp [m]
      exact hk0_below
    have hm_lt_n : m < n := by
      have hs1 : 1 ≤ s := hs_pos
      omega
    have hm_succ_le_n : m + 1 ≤ n := by omega
    have hsqrt_le_nm : Real.sqrt (n : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      dsimp [m]
      exact SqfNumeric.sqrt_le_sub_of_mem hn1 hk0_below
    have hmm_ge : n - s < mfn (m + 1) := by
      have hm_ge_k : m + 1 ≥ k0 + 1 := by
        dsimp [m]
        omega
      -- mfn (m+1) ≥ mfn (k0+1) by monotonicity
      have hmk : mfn (m + 1) ≥ mfn (k0 + 1) := hmfn_mono (by omega) (by omega) hm_ge_k
      exact lt_of_lt_of_le hj0_above hmk
    have hmm_le_n : m + 1 ≤ n := by
      dsimp [m]
      omega
    have hM_spec : n - s < mfn (m + 1) := hmm_ge
    -- deg G_{m+1} ≤ s − 1 and ≤ √n;  n − M ≤ s−1
    let M : ℕ := mfn (m + 1)
    have hM_gt : n - s < M := by
      dsimp [M]
      exact hmm_ge
    have hM_le_n : M ≤ n := by
      dsimp [M]
      exact hmfn_le (m + 1) hmm_le_n
    have hdegG_le : (gJ Q (show m + 1 ≤ n from hmm_le_n)).natDegree ≤ s - 1 := by
      have hd := hgdeg (m + 1) hmm_le_n
      have hd1 : (gJ Q (show m + 1 ≤ n from hmm_le_n)).natDegree ≤ n - M := by
        dsimp [M]
        exact hd
      have hsub : n - M ≤ s - 1 := by omega
      omega
    have hdegG_le_sqrt : ((gJ Q (show m + 1 ≤ n from hmm_le_n)).natDegree : ℝ) ≤
        Real.sqrt (n : ℝ) := by
      have hs1 : 1 ≤ s := hs_pos
      have hcast0 : ((gJ Q (show m + 1 ≤ n from hmm_le_n)).natDegree : ℝ) ≤
          ((s - 1 : ℕ) : ℝ) := by
        exact_mod_cast hdegG_le
      have hcast : ((gJ Q (show m + 1 ≤ n from hmm_le_n)).natDegree : ℝ) ≤ (s : ℝ) - 1 := by
        calc
          ((gJ Q (show m + 1 ≤ n from hmm_le_n)).natDegree : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := hcast0
          _ = (s : ℝ) - 1 := by rw [Nat.cast_sub hs1]; norm_num
      exact le_trans hcast (SqfNumeric.ceil_sqrt_sub_one_le_sqrt (n := n))
    have hsize_le : (n - M : ℕ) ≤ s - 1 := by omega
    have hsize_le_sqrt : ((n - M : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
      exact SqfNumeric.nat_le_sqrt_of_le_ceil_sub_one hsize_le
    -- (3) product split: full = prefix · tail
    let pf : ℝ := ∏ i : Fin (m + 1), wnorm n (zmap (Q ⟨i.val, by omega⟩))
    let tl : ℝ := ∏ j : Fin (n - m), wnorm n (zmap (Q ⟨m + 1 + j.val, by omega⟩))
    have hsplit : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) = pf * tl := by
      have h := prod_split_prefix_tail (n := n) (m := m) (f := fun i : Fin (n + 1) => wnorm n (zmap (Q i))) hm_le_n
      simpa [pf, tl] using h
    have hpf_pos : 0 < pf := by
      dsimp [pf]
      exact Finset.prod_pos (by intro i hi; exact hwpos ⟨i.val, by omega⟩)
    have htl_pos : 0 < tl := by
      dsimp [tl]
      exact Finset.prod_pos (by intro j hj; exact hwpos ⟨m + 1 + j.val, by omega⟩)
    -- (4) prefix lower bound (uniform shape) via second squeeze / wnorm lower
    let Qp : Fin (m + 1) → Polynomial ℤ := fun t => Q ⟨t.val, by omega⟩
    have hQpFull : FullIndepPoly (m + 1) Qp := by
      dsimp [FullIndepPoly]
      have hemb : Function.Injective (fun t : Fin (m + 1) => (⟨t.val, by omega⟩ : Fin (n + 1))) := by
        intro a b hab
        apply Fin.ext
        simpa using congrArg Fin.val hab
      have hcomp : LinearIndependent ℚ (fun t : Fin (m + 1) =>
          coeffVec (n + 1) (Q ⟨t.val, by omega⟩)) := by
        exact hQlin.comp (fun t : Fin (m + 1) => (⟨t.val, by omega⟩ : Fin (n + 1))) hemb
      exact full_poly_indep_of_coeffVec (P := Qp) (M := n) hcomp (fun i => hQdeg ⟨i.val, by omega⟩)
    have hQpdeg : ∀ i : Fin (m + 1), (Qp i).natDegree ≤ n := by
      intro i
      dsimp [Qp]
      exact hQdeg ⟨i.val, by omega⟩
    have hQpOrd : ∀ i : Fin m, wnorm n (zmap (Qp (Fin.castSucc i))) ≤
        wnorm n (zmap (Qp (Fin.succ i))) := by
      intro i
      change wnorm n (zmap (Q ⟨(Fin.castSucc i).val, by omega⟩)) ≤
        wnorm n (zmap (Q ⟨(Fin.succ i).val, by omega⟩))
      change wnorm n (zmap (Q ⟨i.val, by omega⟩)) ≤
        wnorm n (zmap (Q ⟨i.val + 1, by omega⟩))
      have hm : i.val < m := i.isLt
      have hmn1 : m + 1 ≤ n := hm_succ_le_n
      have hsum : i.val + 1 ≤ n := by omega
      exact hQsort (i := ⟨i.val, by omega⟩) (j := ⟨i.val + 1, by omega⟩) (by
        change i.val ≤ i.val + 1
        omega)
    let Ck : ℝ := if h : 1 ≤ k0 then C2 else Cw
    have hCk_pos : 0 < Ck := by
      dsimp [Ck]
      by_cases hk1 : 1 ≤ k0
      · simp [hk1]
        exact hC2pos
      · simp [hk1]
        exact hCwpos
    have hCk_le_Cb : Ch + Ck ≤ Cb := by
      dsimp [Cb, Ck]
      by_cases hk1 : 1 ≤ k0
      · simp [hk1]
        nlinarith [hCwpos]
      · simp [hk1]
        nlinarith [hC2pos]
    have hpf_lower : (n : ℝ) ^ (-Ck * (n : ℝ)) *
        Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
          Submission.EnergyHalf.energy) ≤ pf := by
      by_cases hk1 : 1 ≤ k0
      · -- k0 ≥ 1 : second squeeze applied to the prefix family
        have hk0_le_m : k0 ≤ m := by
          dsimp [m]
          exact hk0_ge_j
        have hGne : gJ Q (show k0 ≤ n from hk0_le_n) ≠ 0 :=
          gJ_ne_zero Q (show k0 ≤ n from hk0_le_n) hQnz
        have hGint : 0 ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x (gJ Q (show k0 ≤ n from hk0_le_n))|
            ∂muSerre := hserre (gJ Q (show k0 ≤ n from hk0_le_n)) hGne
        let S : Fin (k0 + 1) → Polynomial ℤ := fun i => sJ Q (show k0 ≤ n from hk0_le_n) i
        have hdivS : ∀ i : Fin (k0 + 1),
            Qp (pre hk0_le_m i) = gJ Q (show k0 ≤ n from hk0_le_n) * S i := by
          intro i
          have h := sJ_div Q (show k0 ≤ n from hk0_le_n) i
          dsimp [S]
          rw [← h]
          apply congrArg Q
          ext
          simp [Qp, pre, emb]
        have hncS : ∀ z : ℂ, ¬ (∀ i : Fin (k0 + 1), Polynomial.aeval z (S i) = 0) := by
          intro z
          exact sJ_no_common_root Q (show k0 ≤ n from hk0_le_n) hQnz z
        have hdegS : ∀ i : Fin (k0 + 1), (S i).natDegree ≤ m := by
          intro i
          dsimp [S]
          have hd := sJ_deg_le_mJ Q (show k0 ≤ n from hk0_le_n) i
          rw [← mfn_eq k0 (show k0 ≤ n from hk0_le_n)] at hd
          dsimp [m]
          exact hd
        have hleadS : ∃ i₀ : Fin (k0 + 1), (S i₀).natDegree = m := by
          rcases mJ_deg_att Q (show k0 ≤ n from hk0_le_n) with ⟨i₀, hi₀⟩
          refine ⟨i₀, ?_⟩
          dsimp [S]
          rw [← mfn_eq k0 (show k0 ≤ n from hk0_le_n)] at hi₀
          dsimp [m]
          exact hi₀
        have hres := hss k0 (mfn k0) n hk1 hk0_le_m hm_le_n hn2 Qp hQpFull hQpdeg hQpOrd
          (gJ Q (show k0 ≤ n from hk0_le_n)) hGne hGint S hdivS hncS hdegS hleadS
        have hres' : (n : ℝ) ^ (-C2 * (n : ℝ)) *
            Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
              Submission.EnergyHalf.energy) ≤ pf := by
          simpa [pf, Qp] using hres
        -- rewrite Ck → C2
        have hck : Ck = C2 := by
          dsimp [Ck]
          simp [hk1]
        rwa [hck]
      · -- k0 = 0 : single member lower bound via wnorm_lower
        have hk00 : k0 = 0 := by omega
        have hm0 : m = 0 := by
          dsimp [m]
          rw [hk00, hmfn0]
        have hwl0 := hwl n hn2 (Q (0 : Fin (n + 1))) (hQnz (0 : Fin (n + 1))) (hQdeg (0 : Fin (n + 1)))
        -- pf = wnorm of Q0
        have hck : Ck = Cw := by
          dsimp [Ck]
          simp [hk1]
        have hpf_eq0 : pf = wnorm n (zmap (Q (0 : Fin (n + 1)))) := by
          dsimp [pf]
          dsimp [m]
          have hmk0 : mfn k0 = 0 := by rw [hk00, hmfn0]
          let a : Fin (mfn k0 + 1) := ⟨0, by omega⟩
          have hmem : a ∈ (Finset.univ : Finset (Fin (mfn k0 + 1))) := by simp
          have hone : ∀ b ∈ (Finset.univ : Finset (Fin (mfn k0 + 1))), b ≠ a →
              wnorm n (zmap (Q ⟨b.val, by omega⟩)) = 1 := by
            intro b hb hbne
            exfalso
            apply hbne
            apply Fin.ext
            have hb0 : b.val = 0 := by
              have hb1 : b.val < mfn k0 + 1 := b.isLt
              omega
            simpa [a] using hb0
          rw [Finset.prod_eq_single_of_mem a hmem hone]
          simpa [a]
        have hres : (n : ℝ) ^ (-Cw * (n : ℝ)) ≤ pf := by
          rw [hpf_eq0]
          exact hwl0
        -- exp term is 1
        have hexp0 : Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
            Submission.EnergyHalf.energy) = 1 := by
          rw [hm0]
          simp
        calc
          (n : ℝ) ^ (-Ck * (n : ℝ)) *
              Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                Submission.EnergyHalf.energy)
              = (n : ℝ) ^ (-Ck * (n : ℝ)) * 1 := by rw [hexp0]
          _ = (n : ℝ) ^ (-Cw * (n : ℝ)) := by rw [hck]; rw [mul_one]
          _ ≤ pf := hres
    -- (5) tail bound: full = pf·tl ≤ U;  pf ≥ L
    let U : ℝ := (n : ℝ) ^ (Ch * (n : ℝ)) *
        Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * Submission.EnergyHalf.energy)
    have hfull_le_U : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤ U := by
      dsimp [U]
      exact hQprod
    have hU_pos : 0 < U := by
      dsimp [U]
      exact mul_pos (Real.rpow_pos_of_pos hnRpos _) (Real.exp_pos _)
    have hU_nonneg : 0 ≤ U := le_of_lt hU_pos
    let L : ℝ := (n : ℝ) ^ (-Ck * (n : ℝ)) *
        Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
          Submission.EnergyHalf.energy)
    have hL_le_pf : L ≤ pf := by
      dsimp [L]
      exact hpf_lower
    have hL_pos : 0 < L := by
      dsimp [L]
      exact mul_pos (Real.rpow_pos_of_pos hnRpos _) (Real.exp_pos _)
    have htl_le_L : tl ≤ U / L := by
      have hprod_le : pf * tl ≤ U := by
        rw [← hsplit]
        exact hfull_le_U
      have h1 : tl ≤ U / pf := by
        refine (le_div_iff₀ hpf_pos).2 ?_
        rw [mul_comm]
        exact hprod_le
      have h2 : U / pf ≤ U / L := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ hpf_pos hL_pos).2 hL_le_pf) hU_nonneg
      exact le_trans h1 h2
    have hCb_nonneg : 0 ≤ Cb := by
      dsimp [Cb]
      positivity
    have htl_le : tl ≤ (n : ℝ) ^ (Cb * (n : ℝ)) := by
      have hfinal : U / L ≤ (n : ℝ) ^ (Cb * (n : ℝ)) := by
        rw [div_le_iff₀ hL_pos]
        dsimp [U, L] at ⊢
        have hL' : (n : ℝ) ^ (Cb * (n : ℝ)) * ((n : ℝ) ^ (-Ck * (n : ℝ)) *
            Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
              Submission.EnergyHalf.energy))
            = (n : ℝ) ^ ((Cb - Ck) * (n : ℝ)) *
              Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                Submission.EnergyHalf.energy) := by
          calc
            (n : ℝ) ^ (Cb * (n : ℝ)) * ((n : ℝ) ^ (-Ck * (n : ℝ)) *
                Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                  Submission.EnergyHalf.energy))
                = ((n : ℝ) ^ (Cb * (n : ℝ)) * (n : ℝ) ^ (-Ck * (n : ℝ))) *
                  Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                    Submission.EnergyHalf.energy) := by ring
            _ = (n : ℝ) ^ ((Cb - Ck) * (n : ℝ)) *
                Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                  Submission.EnergyHalf.energy) := by
                  congr 1
                  rw [← Real.rpow_add hnRpos]
                  congr 1
                  ring
        rw [← mul_assoc] at hL' ⊢
        rw [hL']
        have hpow : (n : ℝ) ^ (Ch * (n : ℝ)) ≤ (n : ℝ) ^ ((Cb - Ck) * (n : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le hnR1 ?_
          have hCh : Ch ≤ Cb - Ck := by
            dsimp [Ck] at hCk_le_Cb ⊢
            linarith
          exact mul_le_mul_of_nonneg_right hCh (le_of_lt hnRpos)
        have hexp : Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * Submission.EnergyHalf.energy) ≤
            Real.exp ((((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
              Submission.EnergyHalf.energy) := by
          exact Real.exp_le_exp.mpr (by
            have hsq : 0 ≤ (1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ)) ^ 2 := by positivity
            have hid : (1 / 2 : ℝ) * (n : ℝ) ^ 2 * Submission.EnergyHalf.energy -
                (((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                  Submission.EnergyHalf.energy
                = (1 / 2 : ℝ) * ((n : ℝ) - (m : ℝ)) ^ 2 * Submission.EnergyHalf.energy := by ring
            have hle0 : (1 / 2 : ℝ) * (n : ℝ) ^ 2 * Submission.EnergyHalf.energy -
                (((m : ℝ) * (n : ℝ)) - (1 / 2 : ℝ) * (m : ℝ) ^ 2) *
                  Submission.EnergyHalf.energy ≤ 0 := by
              rw [hid]
              exact mul_nonpos_of_nonneg_of_nonpos hsq hEn
            linarith)
        exact mul_le_mul hpow hexp (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hnRpos) _)
      exact le_trans htl_le_L hfinal
    -- (6) power bound on a := ‖Q_{m+1}‖
    let a : ℝ := wnorm n (zmap (Q ⟨m + 1, by omega⟩))
    have ha_pos : 0 < a := by
      dsimp [a]
      exact hwnat (m + 1) hm_succ_le_n
    have hpow_id : a ^ (n - m) = ∏ j : Fin (n - m), a := by
      dsimp [a]
      rw [Finset.prod_const]
      simp
    have ha_pow_le_tl : a ^ (n - m) ≤ tl := by
      rw [hpow_id]
      -- each tail factor ≥ a
      have hle_fact : ∀ j : Fin (n - m), a ≤ wnorm n (zmap (Q ⟨m + 1 + j.val, by omega⟩)) := by
        intro j
        dsimp [a]
        exact hwsortNat hm_succ_le_n (by omega) (by omega)
      have hnonneg : ∀ j : Fin (n - m), 0 ≤ a := by
        intro j
        exact le_of_lt ha_pos
      have hstep1 : (∏ j : Fin (n - m), a) ≤
          ∏ j : Fin (n - m), wnorm n (zmap (Q ⟨m + 1 + j.val, by omega⟩)) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro j hj
          exact le_of_lt ha_pos
        · intro j hj
          exact hle_fact j
      have htl_eq : (∏ j : Fin (n - m), wnorm n (zmap (Q ⟨m + 1 + j.val, by omega⟩))) = tl := by
        dsimp [tl]
      exact le_trans hstep1 (le_of_eq htl_eq)
    have ha_pow_le : a ^ (n - m) ≤ (n : ℝ) ^ (Cb * (n : ℝ)) :=
      le_trans ha_pow_le_tl htl_le
    have ha_le_sqrt : a ≤ (n : ℝ) ^ (Cb * Real.sqrt (n : ℝ)) := by
      let d : ℕ := n - m
      have hd_pos_nat : 0 < d := by
        dsimp [d]
        omega
      have hd_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos_nat
      have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
      have hdnm : (d : ℝ) = (n : ℝ) - (m : ℝ) := by
        dsimp [d]
        exact SqfNumeric.nat_sub_real hm_le_n
      have ha_rpow : (a : ℝ) ^ (d : ℝ) = a ^ d := by
        exact Real.rpow_natCast a d
      have hB : (a : ℝ) ^ (d : ℝ) ≤ (n : ℝ) ^ (Cb * (n : ℝ)) := by
        rw [ha_rpow]
        exact ha_pow_le
      have hA : a = (a ^ (d : ℝ)) ^ ((d : ℝ)⁻¹) := by
        symm
        calc
          (a ^ (d : ℝ)) ^ ((d : ℝ)⁻¹) = a ^ ((d : ℝ) * (d : ℝ)⁻¹) := by
                rw [Real.rpow_mul ha_pos.le (d : ℝ) ((d : ℝ)⁻¹)]
          _ = a ^ (1 : ℝ) := by rw [mul_inv_cancel₀ hd_ne]
          _ = a := by rw [Real.rpow_one]
      have hstep2 : ((n : ℝ) ^ (Cb * (n : ℝ))) ^ ((d : ℝ)⁻¹)
          = (n : ℝ) ^ ((Cb * (n : ℝ)) / (d : ℝ)) := by
        rw [← Real.rpow_mul (le_of_lt hnRpos) (Cb * (n : ℝ)) ((d : ℝ)⁻¹)]
        ring_nf
      have hmid : a ≤ (n : ℝ) ^ ((Cb * (n : ℝ)) / (d : ℝ)) := by
        rw [hA]
        calc
          (a ^ (d : ℝ)) ^ ((d : ℝ)⁻¹)
              ≤ ((n : ℝ) ^ (Cb * (n : ℝ))) ^ ((d : ℝ)⁻¹) :=
                Real.rpow_le_rpow (Real.rpow_nonneg ha_pos.le (d : ℝ)) hB (by positivity)
          _ = (n : ℝ) ^ ((Cb * (n : ℝ)) / (d : ℝ)) := hstep2
      have hexp_le : (Cb * (n : ℝ)) / (d : ℝ) ≤ Cb * Real.sqrt (n : ℝ) := by
        have hsq_d : Real.sqrt (n : ℝ) ≤ (d : ℝ) := by
          rwa [← hdnm] at hsqrt_le_nm
        have hrew : (Cb * (n : ℝ)) / (d : ℝ) = Cb * ((n : ℝ) / (d : ℝ)) := by ring
        rw [hrew]
        exact Submission.SqfNumeric.div_le_sqrt_mul hCb_nonneg hd_pos hsq_d (le_of_lt hnRpos)
      exact le_trans hmid (Real.rpow_le_rpow_of_exponent_le hnR1 hexp_le)
    -- =================== STAGE 2: nocommon on quotients by G_{m+1} ===================
    let Sq : Fin (m + 2) → Polynomial ℤ := fun i => sJ Q (show m + 1 ≤ n from hmm_le_n) i
    have hSq_ne : ∀ i : Fin (m + 2), Sq i ≠ 0 := by
      intro i
      dsimp [Sq]
      exact sJ_ne_zero Q (show m + 1 ≤ n from hmm_le_n) hQnz i
    have hSq_deg : ∀ i : Fin (m + 2), (Sq i).natDegree ≤ M := by
      intro i
      dsimp [Sq]
      have hd := sJ_deg_le_mJ Q (show m + 1 ≤ n from hmm_le_n) i
      rw [← mfn_eq (m + 1) hmm_le_n] at hd
      dsimp [M]
      exact hd
    have hSq_lead : ∃ i₀ : Fin (m + 2), (Sq i₀).natDegree = M := by
      rcases mJ_deg_att Q (show m + 1 ≤ n from hmm_le_n) with ⟨i₀, hi₀⟩
      refine ⟨i₀, ?_⟩
      dsimp [Sq]
      rw [← mfn_eq (m + 1) hmm_le_n] at hi₀
      dsimp [M]
      exact hi₀
    have hSq_nc : ∀ z : ℂ, ¬ (∀ i : Fin (m + 2), Polynomial.aeval z (Sq i) = 0) := by
      intro z
      exact sJ_no_common_root Q (show m + 1 ≤ n from hmm_le_n) hQnz z
    have hKpos : 1 ≤ m + 1 := by omega
    rcases NocommonGeneral.nocommon_general (m := M) (K := m + 1) hKpos Sq hSq_ne hSq_deg
      hSq_lead hSq_nc with ⟨i₀, b, hdeg_i0, hb1, hb_le, hDist⟩
    let Qc : Polynomial ℤ := ∑ i : Fin (m + 2), Polynomial.C (((b i : ℕ) : ℤ)) * Sq i
    have hQc_deg : Qc.natDegree = M := by
      dsimp [Qc]
      exact hDist.1
    have hQc_sep : (Qc.map (algebraMap ℤ ℂ)).Separable := by
      dsimp [Qc]
      exact hDist.2
    have hQc_ne : Qc ≠ 0 := by
      intro hz
      have hMpos : 0 < M := by
        have hMs : n - s + 1 ≤ M := by omega
        omega
      have : Qc.natDegree = M := hQc_deg
      rw [hz] at this
      simp at this
      omega
    let G : Polynomial ℤ := gJ Q (show m + 1 ≤ n from hmm_le_n)
    have hQcG_id : Qc * G = ∑ i : Fin (m + 2),
        Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i) := by
      dsimp [Qc, G]
      calc
        (∑ i : Fin (m + 2), Polynomial.C (((b i : ℕ) : ℤ)) * sJ Q (show m + 1 ≤ n from hmm_le_n) i) *
            gJ Q (show m + 1 ≤ n from hmm_le_n)
            = ∑ i : Fin (m + 2),
                (Polynomial.C (((b i : ℕ) : ℤ)) * sJ Q (show m + 1 ≤ n from hmm_le_n) i) *
                  gJ Q (show m + 1 ≤ n from hmm_le_n) := by
                rw [Finset.sum_mul]
      _ = ∑ i : Fin (m + 2),
                Polynomial.C (((b i : ℕ) : ℤ)) *
                  (sJ Q (show m + 1 ≤ n from hmm_le_n) i * gJ Q (show m + 1 ≤ n from hmm_le_n)) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = ∑ i : Fin (m + 2), Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i) := by
                apply Finset.sum_congr rfl
                intro i hi
                congr 2
                rw [sJ_div Q (show m + 1 ≤ n from hmm_le_n) i]
                ring
    -- norm bound on Qc·G
    have hQcG_norm : wnorm n (zmap (Qc * G)) ≤ ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) * a := by
      have hzmap : zmap (Qc * G) =
          ∑ i : Fin (m + 2), zmap (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i)) := by
        rw [hQcG_id]
        simp [zmap, Polynomial.map_sum]
      have hterm : ∀ i : Fin (m + 2),
          wnorm n (zmap (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i)))
            = (b i : ℝ) * wnorm n (zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))) := by
        intro i
        have hz : zmap (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i))
            = Polynomial.C ((b i : ℕ) : ℝ) * zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i)) := by
          simp [zmap, Polynomial.map_mul, Polynomial.map_C]
        calc
          wnorm n (zmap (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i)))
              = wnorm n (Polynomial.C ((b i : ℕ) : ℝ) * zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))) := by rw [hz]
          _ = wnorm n (((b i : ℕ) : ℝ) • zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))) := by
              rw [← Polynomial.smul_eq_C_mul]
          _ = (b i : ℝ) * wnorm n (zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))) := by
              exact wnorm_smul_nonneg n ((b i : ℝ)) (by exact_mod_cast (Nat.zero_le (b i)))
                (zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i)))
      have hle_a : ∀ i : Fin (m + 2), wnorm n (zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))) ≤ a := by
        intro i
        dsimp [a]
        exact hQsort (i := emb (show m + 1 ≤ n from hmm_le_n) i) (j := ⟨m + 1, by omega⟩) (by
          have hiv : (emb (show m + 1 ≤ n from hmm_le_n) i).val = i.val := by simp [emb]
          have hle : i.val ≤ m + 1 := by omega
          simpa [hiv] using hle)
      have hb_bound : ∀ i : Fin (m + 2), (b i : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by
        intro i
        exact_mod_cast hb_le i
      have hsum_le : (∑ i : Fin (m + 2), (b i : ℝ) *
            wnorm n (zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))))
          ≤ ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) * a := by
        calc
          (∑ i : Fin (m + 2), (b i : ℝ) *
              wnorm n (zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))))
              ≤ ∑ i : Fin (m + 2), (b i : ℝ) * a := by
                  refine Finset.sum_le_sum ?_
                  intro i hi
                  exact mul_le_mul_of_nonneg_left (hle_a i) (by exact_mod_cast (Nat.zero_le (b i)))
          _ = (∑ i : Fin (m + 2), (b i : ℝ)) * a := by rw [Finset.sum_mul]
          _ ≤ (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * a := by
                  have hbsum : (∑ i : Fin (m + 2), (b i : ℝ)) ≤ ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) := by
                    calc
                      (∑ i : Fin (m + 2), (b i : ℝ)) ≤ ∑ i : Fin (m + 2), ((2 * M + 1 : ℕ) : ℝ) := by
                            exact Finset.sum_le_sum (fun i hi => hb_bound i)
                      _ = ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) := by
                            simp [Finset.sum_const, Fintype.card_fin]
                            ring
                  exact mul_le_mul_of_nonneg_right hbsum (le_of_lt ha_pos)
      calc
        wnorm n (zmap (Qc * G)) = wnorm n (∑ i : Fin (m + 2),
            zmap (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i))) := by
              rw [hzmap]
        _ ≤ ∑ i : Fin (m + 2),
            wnorm n (zmap (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i))) := by
              exact wnorm_sum_le n (Finset.univ) (fun i : Fin (m + 2) =>
                zmap (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i)))
        _ = ∑ i : Fin (m + 2), (b i : ℝ) * wnorm n (zmap (Q (emb (show m + 1 ≤ n from hmm_le_n) i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm i
        _ ≤ ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) * a := hsum_le
    -- ============ STAGE 2b ============
    -- (0) local abbreviations
    let sqR : ℝ := Real.sqrt (n : ℝ)
    let ell : ℝ := Real.log (1 + B) / Real.log 2
    let Gc : Polynomial ℂ := G.map (algebraMap ℤ ℂ)
    let Qcc : Polynomial ℂ := Qc.map (algebraMap ℤ ℂ)
    have hQccdeg : Qcc.natDegree = M := by
      change (Qc.map (algebraMap ℤ ℂ)).natDegree = M
      rw [Polynomial.natDegree_map_eq_of_injective RootData.algebraMap_int_complex_injective Qc]
      exact hQc_deg
    have hCR0 : 0 ≤ CR := le_of_lt hCRpos
    have hGne : G ≠ 0 := gJ_ne_zero Q (show m + 1 ≤ n from hmm_le_n) hQnz
    -- (1) degree of Qc·G is ≤ n
    have hdegQcG : (Qc * G).natDegree ≤ n := by
      have hterms : ∀ i : Fin (m + 2),
          ((Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i))).natDegree ≤ n := by
        intro i
        by_cases hb0 : b i = 0
        · have hz : Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i) = 0 := by
            simp [hb0]
          rw [hz]
          simp
        · have hdegQ : (Q (emb (show m + 1 ≤ n from hmm_le_n) i)).natDegree ≤ n :=
            hQdeg (emb (show m + 1 ≤ n from hmm_le_n) i)
          have hci : ((b i : ℕ) : ℤ) ≠ 0 := by
            intro hz
            apply hb0
            exact_mod_cast hz
          calc
            (Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i)).natDegree
                = (Q (emb (show m + 1 ≤ n from hmm_le_n) i)).natDegree := Polynomial.natDegree_C_mul hci
            _ ≤ n := hdegQ
      rw [hQcG_id]
      exact Polynomial.natDegree_sum_le_of_forall_le
        (Finset.univ : Finset (Fin (m + 2)))
        (fun i : Fin (m + 2) => Polynomial.C (((b i : ℕ) : ℤ)) * Q (emb (show m + 1 ≤ n from hmm_le_n) i))
        (fun i hi => hterms i)
    -- (2) complexified polynomials are nonzero
    have hGc_ne : Gc ≠ 0 := by
      intro hz
      exact hGne ((Polynomial.map_eq_zero_iff RootData.algebraMap_int_complex_injective).mp hz)
    have hQcc_ne : Qcc ≠ 0 := by
      intro hz
      exact hQc_ne ((Polynomial.map_eq_zero_iff RootData.algebraMap_int_complex_injective).mp hz)
    -- (3) (H·A).natDegree ≤ n  for the Remez chain
    have hdegHA : (Gc * Qcc).natDegree ≤ n := by
      have hmap : Gc * Qcc = (Qc * G).map (algebraMap ℤ ℂ) := by
        calc
          Gc * Qcc = (G * Qc).map (algebraMap ℤ ℂ) := by
            simp [Gc, Qcc, Polynomial.map_mul]
          _ = (Qc * G).map (algebraMap ℤ ℂ) := by
            congr 1
            exact mul_comm G Qc
      calc
        (Gc * Qcc).natDegree = ((Qc * G).map (algebraMap ℤ ℂ)).natDegree := by rw [hmap]
        _ = (Qc * G).natDegree := by
          exact Polynomial.natDegree_map_eq_of_injective RootData.algebraMap_int_complex_injective (Qc * G)
        _ ≤ n := hdegQcG
    -- (4) the leading coefficient of H has norm ≥ 1
    have hlc1 : 1 ≤ ‖(G.leadingCoeff : ℂ)‖ := by
      have hlc_ne : G.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).mpr hGne
      rw [Complex.norm_intCast]
      exact_mod_cast (Int.one_le_abs hlc_ne)
    have hlcGc : 1 ≤ ‖Gc.leadingCoeff‖ := by
      have hlcEq : Gc.leadingCoeff = (G.leadingCoeff : ℂ) := by
        simpa [Gc] using (Polynomial.leadingCoeff_map_of_injective RootData.algebraMap_int_complex_injective G)
      rw [hlcEq]
      exact hlc1
    -- (5) apply the chain
    have hchainRes := hchain CR hCRpos hcr hn2 Gc Qcc hGc_ne hQcc_ne hdegHA hlcGc
    -- (6) bridges between cwnorm and wnorm
    have hbridge1 : wnorm n (zmap Qc) = cwnorm n Qcc := by
      have hz : (zmap Qc).map (algebraMap ℝ ℂ) = Qcc := by
        simpa [Qcc] using (SqfStage2.zmap_map_eq_map Qc)
      calc
        wnorm n (zmap Qc) = cwnorm n ((zmap Qc).map (algebraMap ℝ ℂ)) := by
          exact (cwnorm_map_eq_wnorm n (zmap Qc)).symm
        _ = cwnorm n Qcc := by rw [hz]
    have hbridge2 : wnorm n (zmap (Qc * G)) = cwnorm n (Gc * Qcc) := by
      have hz : (zmap (Qc * G)).map (algebraMap ℝ ℂ) = Gc * Qcc := by
        have h1 := SqfStage2.zmap_map_eq_map (Qc * G)
        have h2 : (Qc * G).map (algebraMap ℤ ℂ) = Gc * Qcc := by
          calc
            (Qc * G).map (algebraMap ℤ ℂ) = (G * Qc).map (algebraMap ℤ ℂ) := by
              congr 1
              exact mul_comm Qc G
            _ = Gc * Qcc := by
              simp [Gc, Qcc, Polynomial.map_mul]
        rw [h1]
        exact h2
      calc
        wnorm n (zmap (Qc * G)) = cwnorm n ((zmap (Qc * G)).map (algebraMap ℝ ℂ)) := by
          exact (cwnorm_map_eq_wnorm n (zmap (Qc * G))).symm
        _ = cwnorm n (Gc * Qcc) := by rw [hz]
    -- (7) the exponent `CR · deg G` is at most `CR · √n`
    have hGdeg_le_sq : (Gc.natDegree : ℝ) ≤ sqR := by
      dsimp [Gc]
      calc
        ((G.map (algebraMap ℤ ℂ)).natDegree : ℝ) = (G.natDegree : ℝ) := by
          congr 1
          exact Polynomial.natDegree_map_eq_of_injective RootData.algebraMap_int_complex_injective G
        _ ≤ sqR := by
          simpa [G, sqR] using hdegG_le_sqrt
    have hbase1 : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      have hn1' : (1 : ℕ) ≤ 2 * n := by omega
      exact_mod_cast hn1'
    have hbase0 : 0 ≤ ((2 * n : ℕ) : ℝ) := by positivity
    have hqterm0 : 0 ≤ (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * a := by
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (le_of_lt ha_pos)
    -- (8) weighted norm of Qc alone
    have hQc_w : wnorm n (zmap Qc) ≤ ((2 * n : ℕ) : ℝ) ^ (CR * sqR) *
        (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) * a) := by
      calc
        wnorm n (zmap Qc) = cwnorm n Qcc := hbridge1
        _ ≤ ((2 * n : ℕ) : ℝ) ^ (CR * (Gc.natDegree : ℝ)) * cwnorm n (Gc * Qcc) := hchainRes
        _ = ((2 * n : ℕ) : ℝ) ^ (CR * (Gc.natDegree : ℝ)) * wnorm n (zmap (Qc * G)) := by
          rw [hbridge2]
        _ ≤ ((2 * n : ℕ) : ℝ) ^ (CR * (Gc.natDegree : ℝ)) *
            (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) * a) := by
          exact mul_le_mul_of_nonneg_left hQcG_norm
            (Real.rpow_nonneg hbase0 (CR * (Gc.natDegree : ℝ)))
        _ ≤ ((2 * n : ℕ) : ℝ) ^ (CR * sqR) *
            (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) * a) := by
          have hexp : CR * (Gc.natDegree : ℝ) ≤ CR * sqR := by
            exact mul_le_mul_of_nonneg_left hGdeg_le_sq hCR0
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le hbase1 hexp) hqterm0
    -- (9) choose the root-free set S ⊆ {0,…,n−1} of size n − M
    rcases SqfStage2.exists_nonroot_subset hQcc_ne n with ⟨Sset, hSset_range, hSset_card, hSset_nonroot⟩
    -- R := Qc.primPart · ∏_{s∈S}(X − C s)
    let P : Polynomial ℤ := Sset.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))
    let R : Polynomial ℤ := Qc.primPart * P
    have hsq : Squarefree R := by
      dsimp [R]
      exact hsqfree hQc_ne hQc_sep Sset hSset_nonroot
    have hdegR : R.natDegree = n := by
      dsimp [R, P]
      have hd := SqfStage2.natDegree_primPart_mul_linear Qc hQc_ne Sset
      rw [hd, hQc_deg, hSset_card, hQccdeg]
      exact Nat.add_sub_of_le hM_le_n
    -- (10) norm of R: drop content, multiply linear factors
    have hR_w1 : wnorm n (zmap R) ≤ wnorm n (zmap (Qc * P)) := by
      dsimp [R]
      exact SqfStage2.wnorm_primPart_mul_le n Qc hQc_ne P
    have hzmap_prod : zmap (Qc * P) =
        zmap Qc * Sset.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ)) := by
      dsimp [P]
      calc
        zmap (Qc * Sset.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ)))
            = zmap Qc * zmap (Sset.prod (fun s : ℕ => (X - C (s : ℤ) : Polynomial ℤ))) := by
                simp [zmap, Polynomial.map_mul]
        _ = zmap Qc * (Sset.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ))) := by
                congr 1
                simp [zmap, Polynomial.map_prod]
    have hVfact : ∀ x : ℝ, x ∈ Set.Icc Submission.SerreExample.aSerre Submission.SerreExample.bSerre → ∀ s ∈ Sset, |x - (s : ℝ)| ≤ B + (n : ℝ) := by
      intro x hx s hs
      have hs' : s < n := Finset.mem_range.mp (hSset_range hs)
      simpa [B] using (SqfStage2.abs_sub_le_bSerre_add_n hx hs')
    have hV0 : 0 ≤ B + (n : ℝ) := by nlinarith
    have hR_w2 : wnorm n (zmap Qc * Sset.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ))) ≤
        wnorm n (zmap Qc) * (B + (n : ℝ)) ^ Sset.card := by
      exact SqfStage2.wnorm_linear_prod_le (k := n) (zmap Qc) (B + (n : ℝ)) hV0 Sset hVfact
    have hRbound : wnorm n (zmap R) ≤ wnorm n (zmap Qc) * (B + (n : ℝ)) ^ (n - M) := by
      calc
        wnorm n (zmap R) ≤ wnorm n (zmap (Qc * P)) := hR_w1
        _ = wnorm n (zmap Qc * Sset.prod (fun s : ℕ => (X - C (s : ℝ) : Polynomial ℝ))) := by
            rw [hzmap_prod]
        _ ≤ wnorm n (zmap Qc) * (B + (n : ℝ)) ^ Sset.card := hR_w2
        _ = wnorm n (zmap Qc) * (B + (n : ℝ)) ^ (n - M) := by
            rw [hSset_card, hQccdeg]
    -- (11) assemble the four factors
    have hm2 : m + 2 ≤ 2 * n := by omega
    have hM3 : 2 * M + 1 ≤ 3 * n := by omega
    have hbound : wnorm n (zmap R) ≤
        (B + (n : ℝ)) ^ (n - M) * ((2 * n : ℕ) : ℝ) ^ (CR * sqR) *
          (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * a := by
      have hpow0 : 0 ≤ (B + (n : ℝ)) ^ (n - M) := pow_nonneg hV0 (n - M)
      calc
        wnorm n (zmap R) ≤ wnorm n (zmap Qc) * (B + (n : ℝ)) ^ (n - M) := hRbound
        _ ≤ (((2 * n : ℕ) : ℝ) ^ (CR * sqR) *
              (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) * a)) * (B + (n : ℝ)) ^ (n - M) := by
              exact mul_le_mul_of_nonneg_right hQc_w hpow0
        _ = (B + (n : ℝ)) ^ (n - M) * ((2 * n : ℕ) : ℝ) ^ (CR * sqR) *
            (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * a := by
            ring
    -- (12) four exponent bounds
    have hF1 : (B + (n : ℝ)) ^ (n - M) ≤
        (n : ℝ) ^ ((1 + ell) * sqR) := by
      simpa [ell, sqR] using (SqfAbsorb.B_add_n_pow_bound (n := n) (M := M) hn2 (B := B) hB hsize_le_sqrt)
    have hF2 : ((2 * n : ℕ) : ℝ) ^ (CR * sqR) ≤ (n : ℝ) ^ ((2 * CR) * sqR) := by
      simpa [sqR] using (SqfAbsorb.two_n_rpow_bound (n := n) hn2 (CR := CR) hCR0)
    have hF3 : (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) ≤
        (n : ℝ) ^ ((5 / Real.sqrt 2) * sqR) := by
      simpa [sqR] using (SqfAbsorb.quad_rpow_bound (n := n) (m := m) (M := M) hn2 hm2 hM3)
    have hF4 : a ≤ (n : ℝ) ^ (Cb * sqR) := by
      simpa [sqR] using ha_le_sqrt
    have hF10 : 0 ≤ (B + (n : ℝ)) ^ (n - M) := pow_nonneg hV0 (n - M)
    have hF20 : 0 ≤ ((2 * n : ℕ) : ℝ) ^ (CR * sqR) := Real.rpow_nonneg hbase0 (CR * sqR)
    have hF30 : 0 ≤ ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (by positivity)
    have hF40 : 0 ≤ a := le_of_lt ha_pos
    have hprod_le : (B + (n : ℝ)) ^ (n - M) * ((2 * n : ℕ) : ℝ) ^ (CR * sqR) *
          (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * a ≤
        (n : ℝ) ^ ((1 + ell) * sqR + (2 * CR) * sqR + (5 / Real.sqrt 2) * sqR + Cb * sqR) := by
      exact SqfAbsorb.four_bound_le_rpow (x := (n : ℝ)) hnR1
        (c1 := (1 + ell) * sqR) (c2 := (2 * CR) * sqR)
        (c3 := (5 / Real.sqrt 2) * sqR) (c4 := Cb * sqR)
        (F1 := (B + (n : ℝ)) ^ (n - M))
        (F2 := ((2 * n : ℕ) : ℝ) ^ (CR * sqR))
        (F3 := ((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ))
        (F4 := a) hF1 hF2 hF3 hF4 hF10 hF20 hF30 hF40
    have hexpsum : (1 + ell) * sqR + (2 * CR) * sqR + (5 / Real.sqrt 2) * sqR + Cb * sqR = Cbig * sqR := by
      dsimp [Cbig, ell]
      ring
    have htoNpow : wnorm n (zmap R) ≤ npow n Cbig := by
      calc
        wnorm n (zmap R) ≤ (B + (n : ℝ)) ^ (n - M) * ((2 * n : ℕ) : ℝ) ^ (CR * sqR) *
            (((m + 2 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ)) * a := hbound
        _ ≤ (n : ℝ) ^ ((1 + ell) * sqR + (2 * CR) * sqR + (5 / Real.sqrt 2) * sqR + Cb * sqR) := hprod_le
        _ = (n : ℝ) ^ (Cbig * sqR) := by rw [hexpsum]
        _ = npow n Cbig := by
            simp [npow, sqR]
    refine ⟨R, hsq, hdegR, htoNpow⟩

end Submission.SqfCore
