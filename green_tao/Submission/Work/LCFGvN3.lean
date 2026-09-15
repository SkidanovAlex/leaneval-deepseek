import Mathlib
import Submission.Work.LCFGvN2
import Submission.Work.LFCPmCopy
import Submission.Commons.Combinatorics.Transference.lfc_cube_free
import Submission.Commons.Combinatorics.Transference.Unorm_smul_of_nonneg
import Submission.Commons.Combinatorics.Transference.lfc_half
import Submission.Commons.Combinatorics.Transference.lfc_weight_moment_shift3

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The `p`-uniform generalised von Neumann theorem with arbitrary Gowers-uniform slot,
from the linear forms condition

This file composes

* `GTTrans.gvn_puniform_kept` (the arbitrary-index form, `Submission/Work/LCFGvN2.lean`),
* `Commons.Combinatorics.Transference.lfc_cube_free` (the `hA0` cube average),
* `Commons.Combinatorics.Transference.lfc_weight_moment_shift3` (the `hA2` second moment),
* `LFCPmCopy.lfc_Pm_le_shift2` (the `hPm` bound; a `gC`-renamed local copy of the commons
  lemma `lfc_Pm_le_shift2`, needed because the commons files `lfc_Pm_le_inj` and
  `lfc_weight_moment_inj` both declare a top-level `gC` and therefore cannot be imported
  together),

all from `LinFormsCond p ν (k * 2^(k-1)) (3k-4) k ε` — the linear forms condition of Green–Tao
`k`-pseudorandomness.

CONCLUSION: if `‖f j‖_{U^{k-1}} ≤ γ` for the index `j = σ 0` of an arbitrary permutation `σ`, then
`|∑_x ∑_r ∏_i f i (x + i r)| ≤ p² · 16 · (γ + ε^{2^{-k}})`.
-/

open Finset
open scoped BigOperators
open GVNW
open GVNgen
open Commons.NumberTheory.Sieve
open Commons.Combinatorics.Transference

namespace GTTrans

variable {p : ℕ} [Fact p.Prime]

/-! ## The bridges to the inlined forms -/

lemma wAC_eq (k : ℕ) (ν : ZMod p → ℝ) (x : ZMod p) (h : Fin (k-1) → ZMod p) :
    wAC k ν x h = ∏ ω : Fin (k-1) → Bool,
      ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j) := by
  rw [wAC]
  apply Finset.prod_congr rfl
  intro ω _
  simp only [wsigC]

lemma wArgC_cast (k : ℕ) (cInt : Fin k → ℤ) (x s : ZMod p) (h : Fin (k-1) → ZMod p)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) :
    wArgC k (fun m => ((cInt m : ℤ) : ZMod p)) x s h i ω
      = x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
          - ((cInt ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
            * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                * (((cInt ⟨j.val+1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹) := by
  simp only [wArgC, wsigC, wtauC]

lemma wVC_cast (k : ℕ) (cInt : Fin k → ℤ) (ν : ZMod p → ℝ) (x s : ZMod p)
    (h : Fin (k-1) → ZMod p) :
    wVC k (fun m => ((cInt m : ℤ) : ZMod p)) ν x s h
      = ∏ i : Fin (k-1),
          ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
            ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
              - ((cInt ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
                * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                    * (((cInt ⟨j.val+1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹)) := by
  rw [wVC]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro ω _
  rw [wArgC_cast]

/-! ## The theorem -/

/-- **The `p`-uniform generalised von Neumann theorem with the Gowers-uniform factor in an
arbitrary slot, from the linear forms condition.** -/
theorem gvn_puniform_kept_lfc {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    {ν : ZMod p → ℝ} (hνpos : ∀ x, 0 < ν x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hLFC : LinFormsCond p ν (k * 2 ^ (k-1)) (3 * k - 4) k ε)
    (σ : Fin k ≃ Fin k) (hk0 : 0 < k)
    (f : Fin k → ZMod p → ℝ) (hf : ∀ i x, |f i x| ≤ ν x)
    (γ : ℝ) (hγ : 0 ≤ γ) (hU : Unorm (k-1) (f (σ ⟨0, hk0⟩)) ≤ γ) :
    |∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r)|
      ≤ (p:ℝ)^2 * 16 * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by
  have hν0 : ∀ x, 0 ≤ ν x := fun x => le_of_lt (hνpos x)
  set cInt : Fin k → ℤ := fun m => ((σ m).val : ℤ) - ((σ ⟨0, hk0⟩).val : ℤ) with hcInt
  have hcb : ∀ m, (cInt m).natAbs ≤ k := by
    intro m
    have h1 : |cInt m| ≤ (k : ℤ) := by
      have h2 : |(((σ m).val : ℤ) - ((σ ⟨0, hk0⟩).val : ℤ))| ≤ (k : ℤ) := by
        rw [abs_le]
        have hm := (σ m).isLt
        have h0 := (σ ⟨0, hk0⟩).isLt
        constructor <;> omega
      simpa only [hcInt] using h2
    have h3 : ((cInt m).natAbs : ℤ) ≤ (k:ℤ) := by rw [Int.natCast_natAbs]; exact h1
    exact_mod_cast h3
  have hdiam1 : ∀ m m', |cInt m - cInt m'| ≤ (k : ℤ) - 1 := by
    intro m m'
    have h2 : |(((σ m).val : ℤ) - ((σ ⟨0, hk0⟩).val : ℤ))
        - (((σ m').val : ℤ) - ((σ ⟨0, hk0⟩).val : ℤ))| ≤ (k : ℤ) - 1 := by
      rw [show (((σ m).val : ℤ) - ((σ ⟨0, hk0⟩).val : ℤ))
          - (((σ m').val : ℤ) - ((σ ⟨0, hk0⟩).val : ℤ))
          = ((σ m).val : ℤ) - ((σ m').val : ℤ) from by ring]
      rw [abs_le]
      have hm := (σ m).isLt
      have h0 := (σ m').isLt
      constructor <;> omega
    simpa only [hcInt] using h2
  have hdiam : ∀ m m', |cInt m - cInt m'| ≤ k := by
    intro m m'
    have h := hdiam1 m m'
    linarith
  have hinj : Function.Injective (fun m : Fin k => ((cInt m : ℤ) : ZMod p)) := by
    intro a b hab
    have hab' : ((cInt a : ℤ) : ZMod p) = ((cInt b : ℤ) : ZMod p) := hab
    have hsub : ((cInt a - cInt b : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hab', sub_self]
    have hdvd : (p : ℤ) ∣ (cInt a - cInt b) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (cInt a - cInt b) p).mp hsub
    have habs : |cInt a - cInt b| < (p : ℤ) := by
      have h1 : |cInt a - cInt b| ≤ (k : ℤ) - 1 := hdiam1 a b
      have h2 : (k : ℤ) - 1 < (p : ℤ) := by
        have hk1 : 1 ≤ k := by omega
        have hlt : k - 1 < p := by
          have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
          omega
        have hcast : ((k - 1 : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hlt
        rwa [Nat.cast_sub hk1, Nat.cast_one] at hcast
      linarith
    have hzero : cInt a - cInt b = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
    have hval : (σ a).val = (σ b).val := by
      have h : ((σ a).val : ℤ) = ((σ b).val : ℤ) := by
        simp only [hcInt] at hzero
        linarith
      exact_mod_cast h
    exact σ.injective (Fin.ext hval)
  have hcne : ∀ m : Fin k, 1 ≤ m.val → cInt m ≠ 0 := by
    intro m hm h0
    have h0' : ((σ m).val : ℤ) = ((σ ⟨0, hk0⟩).val : ℤ) := by
      simp only [hcInt] at h0
      linarith
    have h1 : (σ m).val = (σ ⟨0, hk0⟩).val := by exact_mod_cast h0'
    have h2 : σ m = σ ⟨0, hk0⟩ := Fin.ext h1
    have h3 : m = ⟨0, hk0⟩ := σ.injective h2
    have hmv : m.val = 0 := by rw [h3]
    omega
  have hc_eq : (fun m : Fin k => (((σ m).val : ℕ) : ZMod p)
        - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p))
      = (fun m => ((cInt m : ℤ) : ZMod p)) := by
    funext m
    simp only [hcInt]
    push_cast
    ring
  -- ## the linear-forms-condition hypotheses in the parameters of the three lemmas
  have hm1 : 2 ^ (k-1) ≤ k * 2 ^ (k-1) := by
    calc 2 ^ (k-1) = 1 * 2 ^ (k-1) := (one_mul _).symm
      _ ≤ k * 2 ^ (k-1) := Nat.mul_le_mul_right _ (by omega)
  have ht1 : k - 1 + 1 ≤ 3 * k - 4 := by omega
  have hL1 : 1 ≤ k := by omega
  have ht2 : k + 2 ≤ 3 * k - 4 := by omega
  have hLFC1 : LinFormsCond p ν (2 ^ (k-1)) (k - 1 + 1) 1 ε :=
    linFormsCond_mono hLFC hm1 ht1 hL1
  have hLFC2 : LinFormsCond p ν (k * 2 ^ (k-1)) (k+2) k ε :=
    linFormsCond_mono hLFC le_rfl ht2 le_rfl
  have hLFC3 : LinFormsCond p ν (2 ^ (k-1)) (2 * k - 4) k ε :=
    linFormsCond_mono hLFC hm1 (by omega) le_rfl
  -- ## hA0
  have hcube := lfc_cube_free (p := p) (d := k-1) (by omega) (ν := ν) (ε := ε) hLFC1
  have hA0 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h
      ≤ (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ) := by
    have hcard : (Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ)
        = (p:ℝ)^(k-1) * (p:ℝ) := by
      simp only [Fintype.card_prod, ZMod.card, Fintype.card_fun, Fintype.card_fin]
      push_cast
      ring
    have hsum : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h)
        = ∑ y : ZMod p × (Fin (k-1) → ZMod p),
            ∏ ω : Fin (k-1) → Bool,
              ν (y.1 + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * y.2 j) := by
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      rw [wAC_eq]
    have h1 : |((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ))⁻¹
        * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h) - 1| ≤ ε := by
      rw [hsum]; exact hcube
    have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hcardpos : (0:ℝ) < (Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ) := by
      rw [hcard]; exact mul_pos (pow_pos hppos _) hppos
    have h2 : ((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ))⁻¹
        * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h) ≤ 1 + ε := by
      have h := (abs_le.mp h1).2
      linarith
    have h3 : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h)
        ≤ (1 + ε) * ((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ)) := by
      have hle := mul_le_mul_of_nonneg_left h2 (le_of_lt hcardpos)
      have hbez : ((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ))
          * (((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ)))⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt hcardpos)
      rw [← mul_assoc, hbez, one_mul] at hle
      calc (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h)
          ≤ ((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ)) * (1 + ε) := hle
        _ = (1 + ε) * ((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ)) := by ring
    calc (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, wAC k ν x h)
        ≤ (1 + ε) * ((Fintype.card (ZMod p × (Fin (k-1) → ZMod p)) : ℝ)) := h3
      _ = (1 + ε) * (p:ℝ)^(k-1) * (p:ℝ) := by rw [hcard]; ring
  -- ## hA2
  have hA2raw := lfc_weight_moment_shift3 (p := p) hk hν0 hε0 cInt k hcb hdiam hinj hcne hLFC2
  have hA2 : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wAC k ν x h * (wWC k (fun m => ((cInt m : ℤ) : ZMod p)) ν x h - 1)^2
      ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ) := by
    have h := hA2raw
    rw [show (p : ℝ) ^ (k - 1 + 1) = (p:ℝ)^(k-1) * (p:ℝ) from by rw [pow_succ]] at h
    rw [← mul_assoc] at h
    simpa only [wAC_eq, wWC, wVC_cast] using h
  -- ## hPm
  have hPmraw := LFCPmCopy.lfc_Pm_le_shift2 (p := p) hk cInt k hcb hdiam hinj hcne hLFC3
  have hPm : ∀ i ∈ Finset.range (k-1),
      Pm (ZMod p) k (phiC (p:=p) k (fun m => ((cInt m : ℤ) : ZMod p))) ν i ≤ 1 + ε := by
    intro i hi
    exact hPmraw i hi
  -- ## the arbitrary-index theorem with the family written as a `ZMod p`-difference
  have hA2' : ∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        wAC k ν x h * (wWC k (fun m => (((σ m).val : ℕ) : ZMod p)
            - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p)) ν x h - 1)^2
      ≤ 4 * ε * (p:ℝ)^(k-1) * (p:ℝ) := by
    rw [hc_eq]; exact hA2
  have hPm' : ∀ i ∈ Finset.range (k-1),
      Pm (ZMod p) k (phiC (p:=p) k (fun m => (((σ m).val : ℕ) : ZMod p)
          - (((σ ⟨0, hk0⟩).val : ℕ) : ZMod p))) ν i ≤ 1 + ε := by
    intro i hi
    rw [hc_eq]; exact hPm i hi
  exact gvn_puniform_kept hk hkp hνpos hε0 hε1 σ hk0 hA0 hA2' hPm' f hf γ hγ hU


/-! ## Green–Tao Proposition 5.1 in the form used by §7 (`|f_i| ≤ ν + 1`)

The relative Szemerédi assembly decomposes `f = f_{U^⊥} + f_U` with `|f_{U^⊥}| ≤ 1 + τ` and
`|f_U| ≤ ν + (1+τ)`, so the pieces are bounded by `ν + 1` rather than by `ν`.  Green–Tao handle
this by replacing `ν` by `ν' = (ν+1)/2` and `f_i` by `f_i/2` (Lemma 3.1); the linear forms
condition for `ν'` is supplied by the commons lemma
`Commons.Combinatorics.Transference.lfc_half`. -/

/-- **Green–Tao Proposition 5.1 with the bound `|f_i| ≤ ν + 1`**, with the linear forms condition
for the halved weight `ν' = (ν+1)/2` supplied as a hypothesis (it is produced from an LFC for `ν`
by `lfc_half`). -/
theorem gvn_puniform_half {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    {ν : ZMod p → ℝ} (hν0 : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hLFC : LinFormsCond p (fun x => (ν x + 1) / 2) (k * 2 ^ (k-1)) (3 * k - 4) k ε)
    (σ : Fin k ≃ Fin k) (hk0 : 0 < k)
    (f : Fin k → ZMod p → ℝ) (hf : ∀ i x, |f i x| ≤ ν x + 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hU : Unorm (k-1) (f (σ ⟨0, hk0⟩)) ≤ γ) :
    |∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r)|
      ≤ (p:ℝ)^2 * (16 * (2:ℝ)^k) * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by
  set F : Fin k → ZMod p → ℝ := fun i x => f i x / 2 with hF
  have hν'pos : ∀ x, 0 < (ν x + 1) / 2 := by
    intro x; have := hν0 x; linarith
  have hFb : ∀ i x, |F i x| ≤ (ν x + 1) / 2 := by
    intro i x
    have h1 : |F i x| = |f i x| / 2 := by rw [hF, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [h1]
    have h2 := hf i x
    linarith [abs_nonneg (f i x)]
  have hFU : Unorm (k-1) (F (σ ⟨0, hk0⟩)) ≤ γ / 2 := by
    have h1 : F (σ ⟨0, hk0⟩) = fun x => (2:ℝ)⁻¹ * f (σ ⟨0, hk0⟩) x := by
      funext x; rw [hF]; simp only [div_eq_inv_mul]
    rw [h1, Unorm_smul_of_nonneg (d := k - 1) (by omega) (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
    linarith [hU]
  have hmain := gvn_puniform_kept_lfc hk hkp hν'pos hε0 hε1 hLFC σ hk0 F hFb (γ / 2)
    (by linarith) hFU
  have hprod : ∀ x r : ZMod p, (∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r))
      = (2:ℝ)^k * ∏ i : Fin k, F i (x + ((i : ℕ) : ZMod p) * r) := by
    intro x r
    rw [show (2:ℝ)^k = ∏ _i : Fin k, (2:ℝ) from by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [hF]
    simp only [div_eq_inv_mul]
    field_simp
  have hsum : (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r))
      = (2:ℝ)^k * ∑ x : ZMod p, ∑ r : ZMod p,
          ∏ i : Fin k, F i (x + ((i : ℕ) : ZMod p) * r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [hprod x r]
  have hq : 0 ≤ ε ^ (((2^k : ℕ) : ℝ))⁻¹ := Real.rpow_nonneg hε0 _
  have h2k0 : (0:ℝ) ≤ (2:ℝ)^k := by positivity
  rw [hsum, abs_mul, abs_of_nonneg h2k0]
  calc (2:ℝ)^k * |∑ x : ZMod p, ∑ r : ZMod p,
          ∏ i : Fin k, F i (x + ((i : ℕ) : ZMod p) * r)|
      ≤ (2:ℝ)^k * ((p:ℝ)^2 * 16 * (γ / 2 + ε ^ (((2^k : ℕ) : ℝ))⁻¹)) :=
        mul_le_mul_of_nonneg_left hmain h2k0
    _ = (p:ℝ)^2 * (16 * (2:ℝ)^k) * (γ / 2 + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by ring
    _ ≤ (p:ℝ)^2 * (16 * (2:ℝ)^k) * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith


/-- **Green–Tao Proposition 5.1 with the bound `|f_i| ≤ ν + 1`**, from the linear forms condition
for `ν` itself (Green–Tao Lemma 3.1, commons lemma
`Commons.Combinatorics.Transference.lfc_half`, supplies the halved weight `ν' = (ν+1)/2`). -/
theorem gvn_puniform_of_lfc {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    {ν : ZMod p → ℝ} (hν0 : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hLFC : LinFormsCond p ν (k * 2 ^ (k-1)) (3 * k - 4) k ε)
    (σ : Fin k ≃ Fin k) (hk0 : 0 < k)
    (f : Fin k → ZMod p → ℝ) (hf : ∀ i x, |f i x| ≤ ν x + 1)
    (γ : ℝ) (hγ : 0 ≤ γ) (hU : Unorm (k-1) (f (σ ⟨0, hk0⟩)) ≤ γ) :
    |∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f i (x + ((i : ℕ) : ZMod p) * r)|
      ≤ (p:ℝ)^2 * (16 * (2:ℝ)^k) * (γ + ε ^ (((2^k : ℕ) : ℝ))⁻¹) :=
  gvn_puniform_half hk hkp hν0 hε0 hε1
    (Commons.Combinatorics.Transference.lfc_half (p := p) hε0 hLFC) σ hk0 f hf γ hγ hU

end GTTrans
