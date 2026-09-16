import Submission.ZagierHoffmanProof.PowerSum
import Submission.ZagierHoffmanProof.StepA
import Submission.ZagierHoffmanProof.StepB4
import Submission.ZagierHoffmanProof.StepB7
import Submission.ZagierHoffmanProof.StepK4
import Submission.ZagierHoffmanProof.StepK7
import Submission.ZagierHoffmanProof.StepK10
import Submission.ZagierHoffmanProof.StepK16
import Submission.ZagierHoffmanProof.StepK33
import Mathlib.Order.Interval.Finset.Nat

/-!
# Thakur's power sums in the second block (PORT of the commons lemma)

This is the workspace port of `Commons.NumberTheory.PowerSum.second_block` (which cannot be
imported here: that file shadows the workspace's `ZagierHoffmanPositiveChar` namespace and
therefore clashes with the main chain).  The statement is unchanged:

for `q < n ≤ 2q-2` written `n = q + k - 1` with `1 ≤ k ≤ q-1`,
`P_d(n) · (∏_{i<d}(θ - θ^(q^(i+1))))^n = k - (k-1)·(θ^(q^(d+1)) - θ)/(θ^q - θ)`.

It is the arithmetic input (`α_n(θ,θ^(q^d))/Γ_n = ambEll(d)^n P_d(n)`) of the bridge (4.2).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial
open ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar.PSB

/-! ## Part 1: the first-block evaluation `P_d(n) = ℓ_d^{-n}` for `1 ≤ n ≤ q` -/

section Part1

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma P_eq_pow_card (d : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) :
    P F d n = (P F d oneExp) ^ (n : ℕ) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    rw [P_zero_eq_one F n, P_zero_eq_one F oneExp, one_pow]
  · obtain ⟨m, hm⟩ := n
    have hmain : ∀ m : ℕ, 1 ≤ m → m ≤ Nat.card F → ∀ (hm : 0 < m),
        P F d ⟨m, hm⟩ = (P F d oneExp) ^ m := by
      intro m
      induction m with
      | zero => intro h1; exact absurd h1 (by omega)
      | succ j ih =>
        intro hj hq hpos
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          rw [pow_one]
          congr 1
        · have ih' : P F d ⟨j, h0⟩ = (P F d oneExp) ^ j := ih (by omega) (by omega) h0
          have hpure := P_pure F d hd ⟨j, h0⟩ oneExp (by
            show j + 1 ≤ Nat.card F
            omega)
          have hp : P F d ⟨j + 1, hpos⟩ = P F d ⟨j, h0⟩ * P F d oneExp := hpure.symm
          rw [hp, ih', pow_succ]
    exact hmain m hm hn hm

end Part1


/-! ## Part 2: the telescoping identity `Σ_j (ℓ_d/ℓ_j)^{q-1} = ρ_d - 1` -/

section Part2

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- the factor `X - X^{q^{i+1}}` of `ℓ_d`. -/
noncomputable def ufac (i : ℕ) : F[X] := X - X ^ ((Nat.card F) ^ (i + 1))

/-- `S e = Σ_{j<e} (∏_{j ≤ i < e} (X - X^{q^{i+1}}))^{q-1}`. -/
noncomputable def Sfun (e : ℕ) : F[X] :=
  ∑ j ∈ Finset.range e, (∏ i ∈ Finset.Ico j e, ufac F i) ^ (Nat.card F - 1)

lemma Sfun_succ (e : ℕ) :
    Sfun F (e + 1) = ufac F e ^ (Nat.card F - 1) * (Sfun F e + 1) := by
  classical
  rw [Sfun]
  rw [Finset.sum_range_succ]
  have hlast : (∏ i ∈ Finset.Ico e (e + 1), ufac F i) = ufac F e := by
    rw [Nat.Ico_succ_singleton, Finset.prod_singleton]
  have hstep : ∀ j ∈ Finset.range e,
      (∏ i ∈ Finset.Ico j (e + 1), ufac F i) = ufac F e * (∏ i ∈ Finset.Ico j e, ufac F i) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.Ico_succ_right_eq_insert_Ico (by omega : j ≤ e), Finset.prod_insert]
    intro hmem
    rw [Finset.mem_Ico] at hmem
    omega
  rw [hlast]
  rw [Finset.sum_congr rfl (fun j hj => by rw [hstep j hj, mul_pow])]
  rw [← Finset.mul_sum]
  rw [Sfun]
  ring

lemma Sfun_mul (e : ℕ) :
    ufac F 0 * Sfun F e = X ^ (Nat.card F) - X ^ ((Nat.card F) ^ (e + 1)) := by
  induction e with
  | zero => simp [Sfun]
  | succ e ih =>
    rw [Sfun_succ]
    have h1 : (X ^ Nat.card F - X ^ ((Nat.card F) ^ (e + 1))) + ufac F 0 = ufac F e := by
      unfold ufac; simp only [Nat.zero_add, pow_one]; ring
    have h2 : ufac F e ^ (Nat.card F - 1) * ufac F e = ufac F e ^ (Nat.card F) := by
      rw [← pow_succ, Nat.sub_add_cancel (by have := card_ge_two F; omega : 1 ≤ Nat.card F)]
    calc ufac F 0 * (ufac F e ^ (Nat.card F - 1) * (Sfun F e + 1))
        = ufac F e ^ (Nat.card F - 1) * (ufac F 0 * (Sfun F e + 1)) := by ring
      _ = ufac F e ^ (Nat.card F - 1) * (ufac F 0 * Sfun F e + ufac F 0) := by rw [mul_add, mul_one]
      _ = ufac F e ^ (Nat.card F - 1)
            * ((X ^ Nat.card F - X ^ ((Nat.card F) ^ (e + 1))) + ufac F 0) := by rw [ih]
      _ = ufac F e ^ (Nat.card F - 1) * ufac F e := by rw [h1]
      _ = ufac F e ^ (Nat.card F) := h2
      _ = X ^ (Nat.card F) - X ^ ((Nat.card F) ^ (e + 2)) := by
            rw [show ufac F e = (X - X ^ ((Nat.card F) ^ (e + 1)) : F[X]) from rfl,
              X_sub_X_pow_card_iter]

end Part2


/-! ## Part 3: `C_d = ℓ_d^{q-1} Σ_{j<d} ℓ_j^{-(q-1)}` and its closed form -/

section Part3

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `θ` inside the completion. -/
noncomputable def thK : RatFunc.CompletionAtInfty F :=
  algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (RatFunc.X : RatFunc F)

lemma thK_eq_coe : thK F = ((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  rw [thK, rat_cast_eq_algebraMap]

lemma ufac_ne_zero (i : ℕ) : ufac F i ≠ 0 := by
  intro h
  have hm : 2 ≤ (Nat.card F) ^ (i + 1) := by
    have h2 := card_ge_two F
    calc 2 ≤ Nat.card F := h2
      _ = (Nat.card F) ^ 1 := (pow_one _).symm
      _ ≤ (Nat.card F) ^ (i + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hd : (ufac F i).natDegree = (Nat.card F) ^ (i + 1) := by
    rw [ufac]
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · rw [Polynomial.natDegree_X_pow]
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; omega
  rw [h] at hd
  simp at hd
  omega

lemma ufac_cast (i : ℕ) :
    (((ufac F i : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)
      = thK F - (thK F) ^ ((Nat.card F) ^ (i + 1)) := by
  have h : ((ufac F i : F[X]) : RatFunc F)
      = RatFunc.X - RatFunc.X ^ ((Nat.card F) ^ (i + 1)) := by
    change algebraMap F[X] (RatFunc F) (ufac F i) = _
    rw [ufac, map_sub, map_pow, RatFunc.algebraMap_X]
  rw [h]
  change algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
      (RatFunc.X - RatFunc.X ^ ((Nat.card F) ^ (i + 1))) = _
  rw [map_sub, map_pow]
  rfl

/-- the factorization `ℓ_d = ℓ_j · ∏_{j ≤ i < d} (X - X^{q^{i+1}})`. -/
lemma lFact_mul_prod_Ico (j d : ℕ) (h : j ≤ d) :
    lFact F d = lFact F j * ∏ i ∈ Finset.Ico j d, ufac F i := by
  classical
  have h1 : lFact F d = ∏ i ∈ Finset.range d, ufac F i := rfl
  have h2 : lFact F j = ∏ i ∈ Finset.range j, ufac F i := rfl
  rw [h1, h2, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le j) h, Finset.prod_union]
  exact Finset.Ico_disjoint_Ico_consecutive 0 j d

/-- `lFact` is nonzero. -/
lemma lFact_ne_zero (d : ℕ) : lFact F d ≠ 0 := by
  rw [show lFact F d = ∏ i ∈ Finset.range d, ufac F i from rfl]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => ufac_ne_zero F i

/-- `lK d ≠ 0`. -/
lemma lK_ne_zero' (d : ℕ) : lK F d ≠ 0 := by
  intro h
  have h2 : algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
      (algebraMap F[X] (RatFunc F) (lFact F d)) = algebraMap (RatFunc F)
        (RatFunc.CompletionAtInfty F) (0 : RatFunc F) := by
    simpa [lK, rat_cast_eq_algebraMap, poly_cast_eq_algebraMap] using h
  have h3 : ((lFact F d : F[X]) : RatFunc F) = (0 : RatFunc F) :=
    rat_embed_injective F h2
  apply lFact_ne_zero F d
  have h4 : algebraMap F[X] (RatFunc F) (lFact F d) = algebraMap F[X] (RatFunc F) (0 : F[X]) := by
    simpa [poly_cast_eq_algebraMap] using h3
  exact RatFunc.algebraMap_injective F h4

/-- **The core `C_d`**: `C_d = ℓ_d^{q-1} Σ_{j<d} ℓ_j^{-(q-1)}`. -/
noncomputable def CK (d : ℕ) : RatFunc.CompletionAtInfty F :=
  (lK F d) ^ (Nat.card F - 1)
    * ∑ j ∈ Finset.range d, ((lK F j) ^ (Nat.card F - 1))⁻¹

lemma lK_mul_inv_eq (j d : ℕ) (h : j ≤ d) :
    lK F d * (lK F j)⁻¹
      = ((((∏ i ∈ Finset.Ico j d, ufac F i : F[X]) : RatFunc F) :
          RatFunc.CompletionAtInfty F)) := by
  have hcast : lK F d = lK F j
      * ((((∏ i ∈ Finset.Ico j d, ufac F i : F[X]) : RatFunc F) :
          RatFunc.CompletionAtInfty F)) := by
    have h0 : lK F d = ((((lFact F j * ∏ i ∈ Finset.Ico j d, ufac F i : F[X]) : F[X])
        : RatFunc F) : RatFunc.CompletionAtInfty F) := by
      rw [← lFact_mul_prod_Ico F j d h]
      rfl
    rw [h0]
    exact coe_K_poly_mul F (lFact F j) (∏ i ∈ Finset.Ico j d, ufac F i)
  rw [hcast, mul_comm (lK F j)
      ((((∏ i ∈ Finset.Ico j d, ufac F i : F[X]) : RatFunc F) :
        RatFunc.CompletionAtInfty F)), mul_assoc,
    mul_inv_cancel₀ (lK_ne_zero' F j), mul_one]

lemma CK_eq_Sfun (d : ℕ) :
    CK F d = (((Sfun F d : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := by
  classical
  have hterm : ∀ j ∈ Finset.range d,
      (lK F d) ^ (Nat.card F - 1) * ((lK F j) ^ (Nat.card F - 1))⁻¹
        = ((((∏ i ∈ Finset.Ico j d, ufac F i : F[X]) : RatFunc F) :
            RatFunc.CompletionAtInfty F)) ^ (Nat.card F - 1) := by
    intro j hj
    have hle : j < d := Finset.mem_range.mp hj
    have hle' : j ≤ d := le_of_lt hle
    have hfac := lK_mul_inv_eq F j d hle'
    have hne : lK F j ≠ 0 := lK_ne_zero' F j
    rw [show (lK F d) ^ (Nat.card F - 1) * ((lK F j) ^ (Nat.card F - 1))⁻¹
        = ((lK F d) * (lK F j)⁻¹) ^ (Nat.card F - 1) from by
      rw [mul_pow, inv_pow]]
    rw [hfac]
  have hR : (((Sfun F d : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)
      = ∑ j ∈ Finset.range d,
          ((((∏ i ∈ Finset.Ico j d, ufac F i : F[X]) : RatFunc F) :
            RatFunc.CompletionAtInfty F)) ^ (Nat.card F - 1) := by
    rw [Sfun]
    simp only [poly_cast_eq_algebraMap, rat_cast_eq_algebraMap, map_sum, map_pow]
  rw [CK, Finset.mul_sum, hR, Finset.sum_congr rfl hterm]

end Part3


/-! ## Part 4: closed form of `C_d` -/

section Part4

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- the ring hom `F[X] → K∞`. -/
noncomputable def kc : F[X] →+* RatFunc.CompletionAtInfty F :=
  (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)).comp (algebraMap F[X] (RatFunc F))

lemma kc_apply (p : F[X]) :
    kc F p = (((p : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) := rfl

lemma kc_injective : Function.Injective (kc F) := by
  intro p q h
  have h' : algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
      (algebraMap F[X] (RatFunc F) p) = algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
      (algebraMap F[X] (RatFunc F) q) := h
  exact RatFunc.algebraMap_injective F (rat_embed_injective F h')

lemma kc_X : kc F X = thK F := by
  rw [kc_apply, poly_cast_eq_algebraMap, RatFunc.algebraMap_X]
  rfl

lemma kc_ufac (i : ℕ) :
    kc F (ufac F i) = thK F - thK F ^ ((Nat.card F) ^ (i + 1)) := by
  rw [kc_apply, ufac_cast F i]

lemma kc_ufac_zero : kc F (ufac F 0) = thK F - thK F ^ (Nat.card F) := by
  rw [kc_ufac F 0]; simp

lemma kc_D1 : kc F (carlitzOne F) = thK F ^ (Nat.card F) - thK F := by
  unfold carlitzOne
  rw [map_sub, map_pow, kc_X]

lemma carlitzOne_ne_zero : carlitzOne F ≠ 0 := by
  intro h
  have hd := carlitzOne_natDegree F
  rw [h] at hd
  simp at hd
  have := card_ge_two F
  omega

lemma D1c_ne_zero : thK F ^ (Nat.card F) - thK F ≠ 0 := by
  rw [← kc_D1 F]
  intro h
  refine carlitzOne_ne_zero F (kc_injective F ?_)
  rw [h, map_zero]

lemma kc_Sfun (d : ℕ) : CK F d = kc F (Sfun F d) := by
  rw [CK_eq_Sfun F d, kc_apply]

/-- **The closed form of `C_d`**: `C_d = ρ_d - 1`. -/
lemma CK_eq_rho (d : ℕ) :
    CK F d = (thK F ^ ((Nat.card F) ^ (d + 1)) - thK F)
      / (thK F ^ (Nat.card F) - thK F) - 1 := by
  have hB : thK F ^ (Nat.card F) - thK F ≠ 0 := D1c_ne_zero F
  have hA : thK F - thK F ^ (Nat.card F) ≠ 0 := fun h =>
    hB (by have := congrArg Neg.neg h; simpa using this)
  have hmain : (thK F - thK F ^ (Nat.card F)) * CK F d
      = thK F ^ (Nat.card F) - thK F ^ ((Nat.card F) ^ (d + 1)) := by
    conv_lhs => rw [← kc_ufac_zero (F := F)]
    rw [kc_Sfun, ← map_mul, Sfun_mul F d, map_sub, map_pow, map_pow, kc_X]
  have hCK : CK F d = (thK F ^ (Nat.card F) - thK F ^ ((Nat.card F) ^ (d + 1)))
      / (thK F - thK F ^ (Nat.card F)) := by
    rw [eq_div_iff hA, mul_comm]
    exact hmain
  rw [hCK]
  field_simp
  ring

end Part4


/-! ## Part 5: the recursion `T(m) = T(m-1) - C_d` and the main theorem -/

section Part5

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `P_d(1) = ℓ_d^{-1}`. -/
lemma P_one_eq_inv_lK (d : ℕ) : P F d oneExp = (lK F d)⁻¹ := by
  have h := uEval_mul_lK F d (EvalU_all F d)
  rw [uEval] at h
  exact eq_inv_of_mul_eq_one_left h

/-- **First block**: `P_d(n) = (ℓ_d^n)^{-1}` for `1 ≤ n ≤ q`. -/
lemma P_eq_inv_lK_pow (d : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) :
    P F d n = ((lK F d) ^ (n : ℕ))⁻¹ := by
  rw [P_eq_pow_card F d n hn, P_one_eq_inv_lK F d, inv_pow]

/-- `T_d(n) = P_d(n)·ℓ_d^n`. -/
noncomputable def T (d : ℕ) (n : ℕ+) : RatFunc.CompletionAtInfty F :=
  P F d n * (lK F d) ^ (n : ℕ)

lemma ChenDeltaZ_eq_zero_of_not_dvd (a b i : ℕ) (h : ¬ (Nat.card F - 1) ∣ i) :
    ChenDeltaZ F a b i = 0 := by
  unfold ChenDeltaZ
  rw [if_neg h]

lemma ChenDeltaZ_one (m : ℕ) (hm : Nat.card F + 1 ≤ m) :
    ChenDeltaZ F 1 (m - 1) (Nat.card F - 1) = 1 := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  unfold ChenDeltaZ
  rw [if_pos (dvd_refl _)]
  have he : Even (1 - 1 : ℕ) := by simp
  rw [if_pos he]
  have hc0 : Nat.choose ((Nat.card F - 1) - 1) (1 - 1) = 1 := by simp
  have hc1 : Nat.choose ((Nat.card F - 1) - 1) ((m - 1) - 1) = 0 := by
    apply Nat.choose_eq_zero_of_lt
    omega
  rw [hc0, hc1]
  ring

/-- If `(q-1) ∣ i`, `0 < i` and `i ≤ 2(q-1) - 1` then `i = q - 1`. -/
lemma dvd_eq_card_sub_one (i : ℕ) (hpos : 0 < i) (hdiv : (Nat.card F - 1) ∣ i)
    (hlt : i ≤ 2 * (Nat.card F - 1) - 1) : i = Nat.card F - 1 := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  obtain ⟨c, hc⟩ := hdiv
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; rw [mul_zero] at hc; omega
    · exact h
  have hle : c ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ c := by omega
    have h1 : (Nat.card F - 1) * 2 ≤ i := by
      rw [hc]; exact Nat.mul_le_mul_left _ h2
    omega
  have hc1' : c = 1 := by omega
  rw [hc1', mul_one] at hc
  exact hc

/-- **First block** (ℕ-indexed form): `P_d(n) = (ℓ_d^n)^{-1}` for `1 ≤ n ≤ q`. -/
lemma P_eq_inv_lK_pow' (d : ℕ) (n : ℕ) (hn : n ≤ Nat.card F) (hnpos : 0 < n) :
    P F d ⟨n, hnpos⟩ = ((lK F d) ^ n)⁻¹ :=
  P_eq_inv_lK_pow F d ⟨n, hnpos⟩ hn

lemma T_step (d m : ℕ) (hd : 1 ≤ d) (hm : 0 < m)
    (hnq : Nat.card F < m) (hn2 : m ≤ 2 * Nat.card F - 2) :
    T F d ⟨m, hm⟩ = T F d ⟨m - 1, by have := card_ge_two F; omega⟩ - CK F d := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hK : Nat.card F - 1 ≤ m := by omega
  have hb : 0 < m - 1 := by omega
  have hmq2 : m - (Nat.card F - 1) ≤ Nat.card F := by omega
  have hq1 : 1 ≤ Nat.card F - 1 := Nat.le_sub_of_add_le (a := 1) (b := 1) (c := Nat.card F) hq
  let a1 : ℕ+ := ⟨1, Nat.one_pos⟩
  let b1 : ℕ+ := ⟨m - 1, hb⟩
  -- restate the shuffle in explicit form
  have hSh' : P F d a1 * P F d b1
      = P F d ⟨1 + (m - 1), by omega⟩
        + ∑ i : {i : ℕ // i ∈ Finset.Icc 1 (1 + (m - 1) - 1)},
            ((ChenDeltaZ F 1 (m - 1) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega) (thakurExp 1 (m - 1) i) d :=
    thakur_prod_one F d hd a1 b1
  have hmem : (Nat.card F - 1) ∈ Finset.Icc 1 (1 + (m - 1) - 1) := by
    rw [Finset.mem_Icc]; constructor <;> omega
  let i0 : {i : ℕ // i ∈ Finset.Icc 1 (1 + (m - 1) - 1)} := ⟨Nat.card F - 1, hmem⟩
  have hRed : (∑ i : {i : ℕ // i ∈ Finset.Icc 1 (1 + (m - 1) - 1)},
        ((ChenDeltaZ F 1 (m - 1) i.1 : ℤ) : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega) (thakurExp 1 (m - 1) i) d)
      = ((ChenDeltaZ F 1 (m - 1) i0.1 : ℤ) : RatFunc.CompletionAtInfty F) *
          S F 2 (by omega) (thakurExp 1 (m - 1) i0) d := by
    refine Fintype.sum_eq_single i0 ?_
    intro b hbne
    have hbd : ¬ (Nat.card F - 1) ∣ b.1 := by
      intro hdiv
      have hmem1 : 1 ≤ b.1 := (Finset.mem_Icc.mp b.2).1
      have hmem2 : b.1 ≤ m - 1 := by
        have h : b.1 ≤ 1 + (m - 1) - 1 := (Finset.mem_Icc.mp b.2).2
        omega
      have hbf : b.1 ≠ Nat.card F - 1 := fun h => hbne (Subtype.ext h)
      exact hbf (dvd_eq_card_sub_one F b.1 (by omega) hdiv (by omega))
    rw [ChenDeltaZ_eq_zero_of_not_dvd F 1 (m - 1) b.1 hbd]
    simp
  have hCsingle : ChenDeltaZ F 1 (m - 1) i0.1 = 1 :=
    ChenDeltaZ_one F m (by omega)
  have hi0 : (i0.1 : ℕ) = Nat.card F - 1 := rfl
  have hSlt_aux : S_lt F 1 (by omega) (fun _ : Fin 1 => (⟨i0.1, by omega⟩ : ℕ+)) d
      = ∑ l ∈ Finset.range d, P F l ⟨Nat.card F - 1, by omega⟩ := by
    rw [show S_lt F 1 (by omega) (fun _ : Fin 1 => (⟨i0.1, by omega⟩ : ℕ+)) d
        = ∑ l ∈ Finset.range d, S F 1 (by omega)
            (fun _ : Fin 1 => (⟨i0.1, by omega⟩ : ℕ+)) l from
      S_lt_eq_sum_levels F 1 (by omega) (fun _ : Fin 1 => (⟨i0.1, by omega⟩ : ℕ+)) d]
    refine Finset.sum_congr rfl fun l hl => ?_
    exact S_one_eq_P F l (by omega) (fun _ : Fin 1 => (⟨i0.1, by omega⟩ : ℕ+))
  have hPidx : P F d ⟨1 + (m - 1) - i0.1, by omega⟩
      = P F d ⟨m - (Nat.card F - 1), by omega⟩ := by
    have he : (⟨1 + (m - 1) - i0.1, by omega⟩ : ℕ+) = ⟨m - (Nat.card F - 1), by omega⟩ := by
      refine Subtype.ext ?_
      show 1 + (m - 1) - (i0.1 : ℕ) = m - (Nat.card F - 1)
      omega
    rw [he]
  have hEval : ((ChenDeltaZ F 1 (m - 1) i0.1 : ℤ) : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp 1 (m - 1) i0) d
      = P F d ⟨m - (Nat.card F - 1), by omega⟩ *
          (∑ l ∈ Finset.range d, P F l ⟨Nat.card F - 1, by omega⟩) := by
    have hS2 : S F 2 (by omega) (thakurExp 1 (m - 1) i0) d
        = P F d ⟨1 + (m - 1) - i0.1, by omega⟩ *
            S_lt F 1 (by omega) (fun _ : Fin 1 => (⟨i0.1, by omega⟩ : ℕ+)) d :=
      thakur_S_two_eq F d 1 (m - 1) i0
    rw [hCsingle, hS2]
    have hone : ((1 : ℤ) : RatFunc.CompletionAtInfty F) = 1 := by norm_num
    rw [hone, one_mul, hPidx, hSlt_aux]
  have hkey : P F d ⟨m, hm⟩ = P F d a1 * P F d b1
      - P F d ⟨m - (Nat.card F - 1), by omega⟩ *
          (∑ l ∈ Finset.range d, P F l ⟨Nat.card F - 1, by omega⟩) := by
    have h2 : P F d ⟨1 + (m - 1), by omega⟩ = P F d ⟨m, hm⟩ := by
      have he : (⟨1 + (m - 1), by omega⟩ : ℕ+) = ⟨m, hm⟩ := by
        refine Subtype.ext ?_
        show 1 + (m - 1) = m
        omega
      rw [he]
    have h1 : P F d a1 * P F d b1
        = P F d ⟨m, hm⟩
          + P F d ⟨m - (Nat.card F - 1), by omega⟩ *
              (∑ l ∈ Finset.range d, P F l ⟨Nat.card F - 1, by omega⟩) := by
      rw [h2] at hSh'
      rw [hSh', hRed, hEval]
    rw [h1]; ring
  change P F d ⟨m, hm⟩ * (lK F d) ^ (m : ℕ)
      = P F d ⟨m - 1, by have := card_ge_two F; omega⟩ * (lK F d) ^ (m - 1) - CK F d
  rw [hkey]
  have hp1 : P F d a1 = (lK F d)⁻¹ := by
    rw [show a1 = oneExp from rfl]
    exact P_one_eq_inv_lK F d
  have hp3 : P F d ⟨m - (Nat.card F - 1), by omega⟩
      = ((lK F d) ^ (m - (Nat.card F - 1)))⁻¹ :=
    P_eq_inv_lK_pow' F d (m - (Nat.card F - 1)) hmq2 (by omega)
  have hp4 : (∑ l ∈ Finset.range d, P F l ⟨Nat.card F - 1, by omega⟩)
      = ∑ l ∈ Finset.range d, ((lK F l) ^ (Nat.card F - 1))⁻¹ :=
    Finset.sum_congr rfl fun l hl =>
      P_eq_inv_lK_pow' F l (Nat.card F - 1) (by omega) hq1
  rw [hp1, hp3, hp4]
  rw [CK]
  set X := lK F d with hXdef
  set S := ∑ l ∈ Finset.range d, ((lK F l) ^ (Nat.card F - 1))⁻¹ with hSdef
  have hX : X ≠ 0 := lK_ne_zero' F d
  have e2 : X ^ (m - (Nat.card F - 1)) * X ^ (Nat.card F - 1) = X ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hK]
  have hA : X⁻¹ * X ^ m = X ^ (m - 1) := by
    conv_lhs => rw [show X ^ m = X * X ^ (m - 1) from by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]]
    rw [← mul_assoc, inv_mul_cancel₀ hX, one_mul]
  have hA' : (X⁻¹ * P F d b1) * X ^ m = P F d b1 * X ^ (m - 1) := by
    rw [mul_assoc, mul_comm (P F d b1) (X ^ m), ← mul_assoc, hA, mul_comm]
  have h2' : (X ^ (m - (Nat.card F - 1)))⁻¹ * X ^ m = X ^ (Nat.card F - 1) := by
    rw [← e2, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hX), one_mul]
  have h3' : ((X ^ (m - (Nat.card F - 1)))⁻¹ * S) * X ^ m
      = X ^ (Nat.card F - 1) * S := by
    rw [mul_assoc, mul_comm S (X ^ m), ← mul_assoc, h2']
  rw [sub_mul, hA', h3']

end Part5


/-! ## Part 6: the main theorem -/

section Part6

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `ρ_d = (θ^{q^{d+1}} - θ)/(θ^q - θ)` in the completion. -/
noncomputable def rho (d : ℕ) : RatFunc.CompletionAtInfty F :=
  (thK F ^ ((Nat.card F) ^ (d + 1)) - thK F) / (thK F ^ (Nat.card F) - thK F)

lemma CK_eq_rho' (d : ℕ) : CK F d = rho F d - 1 :=
  CK_eq_rho F d

lemma rho_eq_coe (d : ℕ) :
    rho F d = ((((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) ^ ((Nat.card F) ^ (d+1))
        - ((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F))
      / (((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (Nat.card F)
        - ((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F))) := by
  unfold rho
  rw [thK_eq_coe]

/-- `T_d(q) = 1`. -/
lemma T_base (d : ℕ) : T F d ⟨Nat.card F, by have := card_ge_two F; omega⟩ = 1 := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hqn : 0 < Nat.card F := by omega
  have hP : P F d ⟨Nat.card F, hqn⟩ = ((lK F d) ^ (Nat.card F))⁻¹ :=
    P_eq_inv_lK_pow' F d (Nat.card F) (le_refl _) hqn
  change P F d ⟨Nat.card F, hqn⟩ * (lK F d) ^ (Nat.card F) = 1
  rw [hP, inv_mul_cancel₀ (pow_ne_zero _ (lK_ne_zero' F d))]

/-- **The second block** (in `T`-form): for `0 ≤ j ≤ q-2`,
`T_d(q+j) = (j+1) - j·ρ_d`. -/
lemma T_fam (d : ℕ) (hd : 1 ≤ d) :
    ∀ j : ℕ, j ≤ Nat.card F - 2 →
      T F d ⟨Nat.card F + j, by have := card_ge_two F; omega⟩
        = ((j + 1 : ℕ) : RatFunc.CompletionAtInfty F)
          - ((j : ℕ) : RatFunc.CompletionAtInfty F) * rho F d := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [show (⟨Nat.card F + 0, by have := card_ge_two F; omega⟩ : ℕ+)
        = ⟨Nat.card F, by have := card_ge_two F; omega⟩ from Subtype.ext (by simp)]
    rw [T_base]
    norm_num
  | succ j ih =>
    intro hj
    have hj' : j ≤ Nat.card F - 2 := by omega
    have hq : 2 ≤ Nat.card F := card_ge_two F
    have hm : 0 < Nat.card F + (j + 1) := by omega
    have hstep := T_step F d (Nat.card F + (j + 1)) hd hm (by omega) (by omega)
    have hidx : (⟨Nat.card F + (j + 1) - 1, by omega⟩ : ℕ+)
        = ⟨Nat.card F + j, by have := card_ge_two F; omega⟩ := by
      refine Subtype.ext ?_
      show Nat.card F + (j + 1) - 1 = Nat.card F + j
      omega
    rw [hidx] at hstep
    rw [hstep, ih hj', CK_eq_rho']
    push_cast
    ring

end Part6


theorem second_block (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] (d k : ℕ)
    (hk : 1 ≤ k) (hk2 : k ≤ Nat.card F - 1) :
    (∑' a : {p : Polynomial F // p.Monic ∧ p.natDegree = d},
        (((algebraMap (Polynomial F) (RatFunc F) a.1 : RatFunc F) : RatFunc.CompletionAtInfty F)
          ^ (Nat.card F + k - 1))⁻¹)
      * (∏ i ∈ Finset.range d,
          (((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F)
            - (((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (Nat.card F ^ (i + 1)))))
          ^ (Nat.card F + k - 1)
      = (k : RatFunc.CompletionAtInfty F)
        - ((k - 1 : ℕ) : RatFunc.CompletionAtInfty F)
          * ((((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (Nat.card F ^ (d + 1))
              - ((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F))
            / (((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (Nat.card F)
              - ((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F))) := by
  have hq : 2 ≤ Nat.card F := card_ge_two F
  have hn : 0 < Nat.card F + k - 1 := by omega
  let n0 : ℕ+ := ⟨Nat.card F + k - 1, hn⟩
  have hsum : (∑' a : {p : Polynomial F // p.Monic ∧ p.natDegree = d},
        (((algebraMap (Polynomial F) (RatFunc F) a.1 : RatFunc F) : RatFunc.CompletionAtInfty F)
          ^ (Nat.card F + k - 1))⁻¹)
      = P F d n0 := by
    have hb : P F d n0 = (∑' b : {p : Polynomial F // p ∈ MonicDeg F d},
        (((b.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n0 : ℕ))⁻¹) := rfl
    rw [hb, ← Equiv.tsum_eq
      (Equiv.subtypeEquivRight
        (p := fun p : Polynomial F => p.Monic ∧ p.natDegree = d)
        (q := fun p : Polynomial F => p ∈ MonicDeg F d) (fun p => Iff.rfl))
      (fun b : {p : Polynomial F // p ∈ MonicDeg F d} =>
        (((b.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n0 : ℕ))⁻¹)]
    exact tsum_congr (fun a => rfl)
  have hprod : (∏ i ∈ Finset.range d,
        (((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F)
          - (((RatFunc.X : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (Nat.card F ^ (i + 1)))))
      = lK F d := by
    simp only [rat_cast_eq_algebraMap, poly_cast_eq_algebraMap, lK, lFact,
      RatFunc.algebraMap_X, map_prod, map_sub, map_pow]
  rw [hsum, hprod]
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    have hlK0 : lK F 0 = 1 := by
      rw [lK, lFact_zero]
      change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
        ((algebraMap (F[X]) (RatFunc F)) (1 : F[X])) = 1
      simp
    rw [P_zero_eq_one, hlK0, one_mul, one_pow]
    have hrho0 : rho F 0 = 1 := by
      unfold rho
      rw [show (Nat.card F) ^ (0 + 1) = Nat.card F by simp, div_self (D1c_ne_zero F)]
    rw [← rho_eq_coe F 0]
    rw [hrho0, mul_one]
    have h1 : (k : RatFunc.CompletionAtInfty F)
        = ((k - 1 : ℕ) : RatFunc.CompletionAtInfty F) + 1 := by
      conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm]
      rw [Nat.cast_add, Nat.cast_one]
    rw [h1]
    ring
  · have hT := T_fam F d hd (k - 1) (by omega)
    rw [Nat.sub_add_cancel hk] at hT
    rw [← rho_eq_coe F d]
    change T F d n0 = (k : RatFunc.CompletionAtInfty F)
          - ((k - 1 : ℕ) : RatFunc.CompletionAtInfty F) * rho F d
    have hidx : n0 = (⟨Nat.card F + (k - 1), by have := card_ge_two F; omega⟩ : ℕ+) := by
      refine Subtype.ext ?_
      show Nat.card F + k - 1 = Nat.card F + (k - 1)
      exact Nat.add_sub_assoc hk (Nat.card F)
    rw [hidx]
    exact hT

end ZagierHoffmanPositiveChar.PSB
