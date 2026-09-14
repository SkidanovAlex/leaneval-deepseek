import Mathlib
import Submission.Vdw.LocalField.Completion
import Submission.Vdw.LocalField.ModuleFinite
import Submission.Vdw.LocalField.AdicComplete
import Submission.Vdw.LocalField.RamificationCompat
import Submission.Vdw.LocalField.KpVal
import Submission.Vdw.LocalField.KpFree
import Submission.Commons.NumberTheory.NumberField.adicCompletionIntegers_maximalIdeal_eq_map

open scoped NumberField Valued WithZero Topology
open IsDedekindDomain
open IsLocalRing
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false

/-!
# Local-field chapter ((f)-transport): the global↔local quotient identification

This module establishes the **contraction/quotient identification** between the
global number-ring quotients `𝓞 K ⧸ P^N` and the quotients of the completed
integer ring `kpInt p P` by powers of its maximal ideal `𝔪` — the connection
named in Roadmap Sessions 120/122/123 as the transport target of the S1
`hwild` gate (the global↔local identification of `𝒪K`-quotients with
`kpInt`-quotients at the prime `P`).

The mathematical content:

1. **local valuation dictionary** (`val_uniformizer`,
   `mem_maximalIdeal_pow_iff_val_le`): in the completed valuation ring
   `A := kpInt p P` with maximal ideal `𝔪` and uniformizer `ϖ`, the valuation
   `Valued.v : L → ℤᵐ⁰` (`L := kpAdic p P`) satisfies `Valued.v ϖ = exp(-1)`
   and hence
   `y ∈ 𝔪^N ⟺ Valued.v y ≤ exp (-(N : ℤ))` for every `y : A`, `N : ℕ`
   (the DVR decomposition `y = u·ϖ^(kpVal y)` + `log` arithmetic).

2. **global dictionary** (`val_coe_eq_intVal`, `mem_P_pow_iff_valEmbedding_le`):
   for `x : 𝓞 K`, the completion's valuation on the embedded element equals the
   height-one `intValuation`, and
   `x ∈ P^N ⟺ Valued.v (x : L) ≤ exp (-(N : ℤ))`
   (Mathlib `intValuation_le_pow_iff_mem`).

3. **the contraction** (`mem_comap_maximalIdeal_pow`): the natural map
   `φ : 𝓞 K →+* kpInt p P` satisfies `x ∈ P^N ⟺ φ x ∈ 𝔪^N`, i.e. the ideal
   `𝔪^N` contracts to `P^N` — the exact kernel computation making the induced
   map `𝓞 K ⧸ P^N →+* kpInt p P ⧸ 𝔪^N` injective.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ## Part 1: the local valuation dictionary on the completed ring -/

/-- In `ℤᵐ⁰`, below `1 = exp 0` implies `≤ exp (-1)` (discreteness of the
value group). -/
lemma val_le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx0 : x = 0
  · rw [hx0]
    exact le_of_lt (WithZero.exp_pos (a := (-1 : ℤ)))
  · have hloglt : WithZero.log x < (0 : ℤ) := by
      rw [← WithZero.exp_log hx0, ← WithZero.exp_zero] at hx
      exact WithZero.exp_lt_exp.mp hx
    have hlogle : WithZero.log x ≤ -1 := by omega
    calc
      x = WithZero.exp (WithZero.log x) := (WithZero.exp_log hx0).symm
      _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr hlogle

/-- A global uniformizer of the height-one prime `kprime p P` (element of
`𝓞 K` of `intValuation` value `exp (-1)`). -/
noncomputable def gPi (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] : 𝓞 K :=
  Classical.choose (IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer (kprime p P))

/-- The chosen global uniformizer has `intValuation` value `exp (-1)`. -/
lemma gPi_val (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (kprime p P).intValuation (gPi p P) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec (IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer (kprime p P))

/-- Its value in the completion is `exp (-1)` (field-valued dictionary). -/
lemma gPi_val_completion (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Valued.v ((gPi p P : K) : kpAdic p P) = WithZero.exp (-1 : ℤ) := by
  have h1 : Valued.v (((gPi p P : K) : kpAdic p P)) = (kprime p P).valuation K (gPi p P : K) := by
    simpa using (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (R := 𝓞 K) (K := K) (v := kprime p P) (r := gPi p P))
  rw [h1]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (R := 𝓞 K) (K := K)
    (v := kprime p P) (r := gPi p P)]
  exact gPi_val p P

/-- Same fact through the integer-ring algebraMap `𝓞 K →+* kpInt p P`. -/
lemma gPi_val_completion_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Valued.v ((algebraMap (𝓞 K) (kpInt p P) (gPi p P) : kpInt p P) : kpAdic p P) =
      WithZero.exp (-1 : ℤ) := by
  have hco : ((algebraMap (𝓞 K) (kpInt p P) (gPi p P) : kpInt p P) : kpAdic p P) =
      ((gPi p P : K) : kpAdic p P) := by
    rfl
  rw [hco]
  exact gPi_val_completion p P

/-- The global uniformizer lies in `P`. -/
lemma gPi_mem (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    gPi p P ∈ P := by
  have hval : (kprime p P).intValuation (gPi p P) < 1 := by
    rw [gPi_val p P]
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  exact ((kprime p P).intValuation_lt_one_iff_mem (gPi p P)).mp hval

/-- The local uniformizer has valuation `≤ exp (-1)` (it lies in 𝔪). -/
lemma val_uniformizer_le (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Valued.v ((uniformizer p P : kpInt p P) : kpAdic p P) ≤ WithZero.exp (-1 : ℤ) := by
  have hmem : uniformizer p P ∈ maximalIdeal (kpInt p P) := by
    rw [maximalIdeal_eq_span_uniformizer]
    rw [Ideal.mem_span_singleton']
    exact ⟨1, by simp⟩
  have hlt : Valued.v ((uniformizer p P : kpInt p P) : kpAdic p P) < 1 := by
    exact (mem_maximalIdeal_iff_val_lt_one p P (uniformizer p P)).mp hmem
  exact val_le_exp_neg_one_of_lt_one hlt

/-- Units of the completed integer ring have valuation `1`. -/
lemma unit_val_eq_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (u : (kpInt p P)ˣ) :
    Valued.v ((u : kpInt p P) : kpAdic p P) = 1 := by
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    (K := K) (v := kprime p P) (a := (u : kpInt p P))).mp u.isUnit

/-- The local uniformizer has valuation `≥ exp (-1)` (via the global
uniformizer `φπ ∈ 𝔪`, which generates 𝔪). -/
lemma exp_neg_one_le_val_uniformizer (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    WithZero.exp (-1 : ℤ) ≤ Valued.v ((uniformizer p P : kpInt p P) : kpAdic p P) := by
  classical
  let ϖ : kpInt p P := uniformizer p P
  have hvϖ_ne : Valued.v ((ϖ : kpInt p P) : kpAdic p P) ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mpr (by
      intro hz
      apply uniformizer_ne_zero p P
      exact Subtype.coe_injective (by simpa using hz))
  have hπmem : (algebraMap (𝓞 K) (kpInt p P) (gPi p P) : kpInt p P) ∈
      maximalIdeal (kpInt p P) := by
    rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_maximalIdeal_eq_map
      (K := K) (kprime p P)]
    exact Ideal.mem_map_of_mem (algebraMap (𝓞 K) (kpInt p P)) (by
      change gPi p P ∈ (kprime p P).asIdeal
      exact ((kprime p P).intValuation_lt_one_iff_mem (gPi p P)).mp (by
        rw [gPi_val p P]
        rw [← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by norm_num)))
  have hφπ_ne : (algebraMap (𝓞 K) (kpInt p P) (gPi p P) : kpInt p P) ≠ 0 := by
    intro hz
    have hv0 : Valued.v ((0 : kpAdic p P)) = WithZero.exp (-1 : ℤ) := by
      simpa [hz] using gPi_val_completion_algebraMap p P
    rw [map_zero] at hv0
    exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) hv0.symm
  have hgen : maximalIdeal (kpInt p P) = Ideal.span ({ϖ} : Set (kpInt p P)) := by
    simpa [ϖ] using maximalIdeal_eq_span_uniformizer p P
  have hφπ_span : (algebraMap (𝓞 K) (kpInt p P) (gPi p P) : kpInt p P) ∈
      Ideal.span ({ϖ} : Set (kpInt p P)) := by
    rwa [← hgen]
  obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton' (α := kpInt p P)
    (x := (algebraMap (𝓞 K) (kpInt p P) (gPi p P) : kpInt p P)) (y := ϖ)).mp hφπ_span
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hφπ_ne
    rw [← hc, hc0, zero_mul]
  let e : kpInt p P := (algebraMap (𝓞 K) (kpInt p P) (gPi p P) : kpInt p P)
  have hce : e = c * ϖ := by simpa [e] using hc.symm
  have hve_ne : Valued.v ((e : kpInt p P) : kpAdic p P) ≠ 0 := by
    dsimp [e]
    rw [gPi_val_completion_algebraMap]
    exact WithZero.exp_ne_zero
  have hvc_ne : Valued.v ((c : kpInt p P) : kpAdic p P) ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mpr (by
      intro hz
      apply hc_ne
      exact Subtype.coe_injective (by simpa using hz))
  have hlogϖ : (-1 : ℤ) ≤ WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)) := by
    have hloge : WithZero.log (Valued.v ((e : kpInt p P) : kpAdic p P)) = -1 := by
      dsimp [e]
      rw [gPi_val_completion_algebraMap]
      rfl
    have hmain : WithZero.log (Valued.v ((e : kpInt p P) : kpAdic p P)) =
        WithZero.log (Valued.v ((c : kpInt p P) : kpAdic p P)) +
          WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)) := by
      calc
        WithZero.log (Valued.v ((e : kpInt p P) : kpAdic p P))
            = WithZero.log (Valued.v (((c * ϖ) : kpInt p P) : kpAdic p P)) := by
              have harg : ((e : kpInt p P) : kpAdic p P) = (((c * ϖ) : kpInt p P) : kpAdic p P) := by
                exact congrArg (fun z : kpInt p P => (z : kpAdic p P)) hce
              rw [harg]
        _ = WithZero.log (Valued.v ((c : kpInt p P) : kpAdic p P) *
              Valued.v ((ϖ : kpInt p P) : kpAdic p P)) := by
              have hmap : Valued.v ((((c * ϖ) : kpInt p P) : kpAdic p P)) =
                  Valued.v (((c : kpInt p P) : kpAdic p P)) *
                    Valued.v (((ϖ : kpInt p P) : kpAdic p P)) := by
                simpa using (map_mul Valued.v ((c : kpInt p P) : kpAdic p P)
                  ((ϖ : kpInt p P) : kpAdic p P))
              rw [hmap]
        _ = WithZero.log (Valued.v ((c : kpInt p P) : kpAdic p P)) +
              WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)) :=
              WithZero.log_mul hvc_ne hvϖ_ne
    have hlogc_le : WithZero.log (Valued.v ((c : kpInt p P) : kpAdic p P)) ≤ 0 := by
      have hcle : Valued.v ((c : kpInt p P) : kpAdic p P) ≤ 1 := (c : kpInt p P).2
      rw [← WithZero.exp_zero] at hcle
      exact (WithZero.log_le_iff_le_exp hvc_ne).mpr hcle
    calc
      (-1 : ℤ) = WithZero.log (Valued.v ((e : kpInt p P) : kpAdic p P)) := by rw [hloge]
      _ = WithZero.log (Valued.v ((c : kpInt p P) : kpAdic p P)) +
            WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)) := hmain
      _ ≤ WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)) := by
            calc
              WithZero.log (Valued.v ((c : kpInt p P) : kpAdic p P)) + WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P))
                  ≤ 0 + WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)) := by
                    exact add_le_add_left hlogc_le
                      (WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)))
              _ = WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P)) := by simp
  calc
    WithZero.exp (-1 : ℤ) ≤ WithZero.exp (WithZero.log (Valued.v ((ϖ : kpInt p P) : kpAdic p P))) :=
      WithZero.exp_le_exp.mpr hlogϖ
    _ = Valued.v ((ϖ : kpInt p P) : kpAdic p P) := WithZero.exp_log hvϖ_ne

/-- **The local uniformizer has valuation exactly `exp (-1)`.** -/
theorem val_uniformizer (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Valued.v ((uniformizer p P : kpInt p P) : kpAdic p P) = WithZero.exp (-1 : ℤ) :=
  le_antisymm (val_uniformizer_le p P) (exp_neg_one_le_val_uniformizer p P)

/-- `exp(-1)^m = exp(-(m : ℤ))` in `ℤᵐ⁰`. -/
lemma exp_neg_one_pow (m : ℕ) :
    (WithZero.exp (-1 : ℤ)) ^ m = WithZero.exp (-(m : ℤ)) := by
  rw [← WithZero.exp_nsmul m (-1 : ℤ)]
  congr 1
  simp

/-- Valuation of a power of the local uniformizer. -/
lemma val_uniformizer_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (m : ℕ) :
    Valued.v ((uniformizer p P ^ m : kpInt p P) : kpAdic p P) =
      WithZero.exp (-(m : ℤ)) := by
  calc
    Valued.v ((uniformizer p P ^ m : kpInt p P) : kpAdic p P)
        = Valued.v (((uniformizer p P : kpInt p P) : kpAdic p P) ^ m) := by
          have hco : ((uniformizer p P ^ m : kpInt p P) : kpAdic p P) =
              (((uniformizer p P : kpInt p P) : kpAdic p P) ^ m) := by rfl
          rw [hco]
    _ = (Valued.v ((uniformizer p P : kpInt p P) : kpAdic p P)) ^ m := by
          rw [map_pow]
    _ = (WithZero.exp (-1 : ℤ)) ^ m := by
          rw [val_uniformizer p P]
    _ = WithZero.exp (-(m : ℤ)) := exp_neg_one_pow m

/-- Valuation of a nonzero element of the completed ring equals
`exp (-kpVal)`. -/
lemma val_eq_exp_neg_kpVal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (y : kpInt p P) (hy : y ≠ 0) :
    Valued.v ((y : kpInt p P) : kpAdic p P) = WithZero.exp (-(kpVal p P y : ℤ)) := by
  classical
  let u : (kpInt p P)ˣ := kpUnit p P y hy
  have hspec : y = (u : kpInt p P) * uniformizer p P ^ kpVal p P y := by
    simpa [u] using (kpVal_spec p P y hy)
  calc
    Valued.v ((y : kpInt p P) : kpAdic p P)
        = Valued.v ((((u : kpInt p P) * uniformizer p P ^ kpVal p P y) : kpInt p P) : kpAdic p P) := by
          congr 1
          exact congrArg (fun z : kpInt p P => (z : kpAdic p P)) hspec
    _ = Valued.v (((u : kpInt p P) : kpAdic p P) *
          ((uniformizer p P ^ kpVal p P y : kpInt p P) : kpAdic p P)) := by rfl
    _ = Valued.v (((u : kpInt p P) : kpAdic p P)) *
          Valued.v (((uniformizer p P ^ kpVal p P y : kpInt p P) : kpAdic p P)) := by
          rw [map_mul]
    _ = WithZero.exp (-(kpVal p P y : ℤ)) := by
          rw [unit_val_eq_one p P u]
          rw [val_uniformizer_pow p P (kpVal p P y)]
          simp

/-- Membership in a maximal-ideal power is `M ≤ kpVal` (nonzero elements). -/
lemma mem_maximalIdeal_pow_iff_kpVal_ge (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (y : kpInt p P) (hy : y ≠ 0) (M : ℕ) :
    y ∈ (maximalIdeal (kpInt p P)) ^ M ↔ M ≤ kpVal p P y := by
  classical
  constructor
  · intro hmem
    by_contra hnot
    have hlt : kpVal p P y < M := lt_of_not_ge hnot
    have hsub : (maximalIdeal (kpInt p P)) ^ M ≤ (maximalIdeal (kpInt p P)) ^ (kpVal p P y + 1) :=
      Ideal.pow_le_pow_right (by omega : kpVal p P y + 1 ≤ M)
    exact (kpVal_exact p P y hy).2 (hsub hmem)
  · intro hge
    have hmem' : y ∈ (maximalIdeal (kpInt p P)) ^ kpVal p P y := (kpVal_exact p P y hy).1
    exact (Ideal.pow_le_pow_right hge) hmem'

/-- **Membership in a maximal-ideal power is `Valued.v y ≤ exp (-(M : ℤ))`** —
the valuation characterisation of the 𝔪-adic filtration of the completed
ring of integers. -/
theorem mem_maximalIdeal_pow_iff_val_le (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (y : kpInt p P) (M : ℕ) :
    y ∈ (maximalIdeal (kpInt p P)) ^ M ↔
      Valued.v ((y : kpInt p P) : kpAdic p P) ≤ WithZero.exp (-(M : ℤ)) := by
  by_cases hy : y = 0
  · subst y
    constructor
    · intro _
      simpa using (le_of_lt (WithZero.exp_pos (a := -(M : ℤ))))
    · intro _
      by_cases hM : M = 0
      · simp [hM]
      · exact Submodule.zero_mem _
  · have hiff1 : y ∈ (maximalIdeal (kpInt p P)) ^ M ↔ M ≤ kpVal p P y :=
      mem_maximalIdeal_pow_iff_kpVal_ge p P y hy M
    have hval := val_eq_exp_neg_kpVal p P y hy
    have hiff2 : Valued.v ((y : kpInt p P) : kpAdic p P) ≤ WithZero.exp (-(M : ℤ)) ↔
        M ≤ kpVal p P y := by
      rw [hval]
      rw [WithZero.exp_le_exp]
      omega
    exact hiff1.trans hiff2.symm

/-! ## Part 2: the global dictionary and the contraction -/

/-- For `x : 𝓞 K`, the completion's valuation on the embedded element equals
the height-one `intValuation`. -/
lemma val_coe_eq_intVal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : 𝓞 K) :
    Valued.v (((x : K) : kpAdic p P)) = (kprime p P).intValuation x := by
  have h1 : Valued.v (((x : K) : kpAdic p P)) = (kprime p P).valuation K (x : K) := by
    simpa using (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation
      (R := 𝓞 K) (K := K) (v := kprime p P) (r := x))
  rw [h1]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (R := 𝓞 K) (K := K)
    (v := kprime p P) (r := x)

/-- **Global membership dictionary**: `x ∈ P^M ⟺ Valued.v (x : L) ≤ exp(-M)`.
-/
theorem mem_P_pow_iff_valEmbedding_le (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : 𝓞 K) (M : ℕ) :
    x ∈ P ^ M ↔ Valued.v (((x : K) : kpAdic p P)) ≤ WithZero.exp (-(M : ℤ)) := by
  rw [val_coe_eq_intVal p P x]
  exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem (kprime p P) x M).symm

/-- The underlying value of `ringOfIntegersToKpInt` is the field-embedding
coefficient. -/
lemma ringOfIntegersToKpInt_coe (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : 𝓞 K) :
    ((ringOfIntegersToKpInt p P x : kpInt p P) : kpAdic p P) =
      ((x : K) : kpAdic p P) := by
  rfl

/-- **THE CONTRACTION**: for the natural map `φ : 𝓞 K →+* kpInt p P`,
`x ∈ P^M ⟺ φ x ∈ 𝔪^M` — the ideal `𝔪^M` contracts to `P^M`. -/
theorem mem_comap_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : 𝓞 K) (M : ℕ) :
    x ∈ P ^ M ↔
      (ringOfIntegersToKpInt p P x : kpInt p P) ∈ (maximalIdeal (kpInt p P)) ^ M := by
  rw [mem_maximalIdeal_pow_iff_val_le p P (ringOfIntegersToKpInt p P x) M]
  rw [ringOfIntegersToKpInt_coe p P x]
  exact mem_P_pow_iff_valEmbedding_le p P x M

/-- The ideal `𝔪^M` of the completed ring contracts to `P^M` (ideal form). -/
theorem comap_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (M : ℕ) :
    ((maximalIdeal (kpInt p P)) ^ M).comap (ringOfIntegersToKpInt p P) = P ^ M := by
  ext x
  exact (mem_comap_maximalIdeal_pow p P x M).symm


/-! ## Part 3: the induced quotient identification

With the contraction (`mem_comap_maximalIdeal_pow`) in place the natural map
`φ : 𝓞 K →+* kpInt p P` descends to an injective map
`𝓞 K ⧸ P^M →+* kpInt p P ⧸ 𝔪^M`.  Surjectivity follows from density
(the image of `𝓞 K` is dense in `kpInt` — fleet L102 — and the quotient by
the open ideal `𝔪^M` is discrete).  The result is the **global↔local
quotient identification**:

* `denseRange_ringOfIntegersToKpInt` — the image of `𝓞 K` in `kpInt` is dense;
* `isOpen_maximalIdeal_pow` / `discreteTopology_quotient_maximalIdeal_pow` —
  `𝔪^M` is an open additive subgroup (it contains the open unit-ball
  neighbourhood `{y | ‖y‖ < ‖ϖ‖^M}` of `0`), so the quotient is discrete;
* `quotientToKpInt_surjective` / `ker_quotientToKpInt` — the map
  `q ∘ φ : 𝓞 K →+* kpInt ⧸ 𝔪^M` is surjective with kernel `P^M`;
* `quotientRingOfIntegersIso` — **`𝓞 K ⧸ P^M ≃+* kpInt p P ⧸ 𝔪^M`**;
* `globalLocal_quotientIso` — the transport form
  **`𝓞 K ⧸ P^(e·n) ≃+* kpInt p P ⧸ (p^n)`** (via
  `kpInt_span_pow_eq_maximalIdeal_pow`, `e := P.ramificationIdx ℤ`).
-/

/-- The image of the ring of integers under the completion map is dense in
`kpInt p P` (subtype form of the fleet L102 ambient density). -/
lemma denseRange_ringOfIntegersToKpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Dense (Set.range (ringOfIntegersToKpInt p P)) := by
  rw [Dense]
  intro x
  have hc : closure (Set.range (ringOfIntegersToKpInt p P)) =
      (fun y : kpInt p P => (y : kpAdic p P)) ⁻¹' closure
        ((fun y : kpInt p P => (y : kpAdic p P)) '' Set.range (ringOfIntegersToKpInt p P)) :=
    subtype_closure_preimage (s := Set.range (ringOfIntegersToKpInt p P))
  rw [hc]
  have hset : ((fun y : kpInt p P => (y : kpAdic p P)) '' Set.range (ringOfIntegersToKpInt p P))
      = {y : kpAdic p P | ∃ r : 𝓞 K, (algebraMap K (kpAdic p P) (r : K)) = y} := by
    ext y
    constructor
    · rintro ⟨a, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨ringOfIntegersToKpInt p P r, ⟨r, rfl⟩, rfl⟩
  rw [hset]
  exact kpInt_mem_closure_ringOfIntegers p P x

/-- The maximal-ideal power `𝔪^M` is an open additive subgroup of the
completed ring (it contains the open ball `{y | ‖y‖ < ‖ϖ‖^M}` of `0`). -/
lemma isOpen_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (M : ℕ) :
    IsOpen (((maximalIdeal (kpInt p P)) ^ M : Ideal (kpInt p P)) : Set (kpInt p P)) := by
  classical
  by_cases hM : M = 0
  · simp [hM]
  · let U : AddSubgroup (kpInt p P) := ((maximalIdeal (kpInt p P)) ^ M).toAddSubgroup
    have hball : {y : kpInt p P | ‖y‖ < ‖uniformizer p P‖ ^ M} ⊆
        (((maximalIdeal (kpInt p P)) ^ M : Ideal (kpInt p P)) : Set (kpInt p P)) := by
      intro y hy
      exact (mem_maximalIdeal_pow_iff_norm_le p P y M).mpr (le_of_lt hy)
    have hmem : (((maximalIdeal (kpInt p P)) ^ M : Ideal (kpInt p P)) : Set (kpInt p P)) ∈
        𝓝 (0 : kpInt p P) := by
      refine Filter.mem_of_superset ?_ hball
      have h0 : (0 : kpInt p P) ∈ {y : kpInt p P | ‖y‖ < ‖uniformizer p P‖ ^ M} := by
        have hpos : 0 < ‖uniformizer p P‖ ^ M := pow_pos (uniformizer_norm_pos p P) M
        simpa using hpos
      exact isOpen_iff_mem_nhds.mp (isOpen_lt continuous_norm continuous_const) (0 : kpInt p P) h0
    have hU : (U : Set (kpInt p P)) ∈ 𝓝 (0 : kpInt p P) := by
      simpa [U] using hmem
    have hopen : IsOpen (U : Set (kpInt p P)) :=
      AddSubgroup.isOpen_of_mem_nhds U (g := 0) hU
    simpa [U] using hopen

/-- The quotient `kpInt p P ⧸ 𝔪^M` is discrete (quotient by the open
additive subgroup `𝔪^M`). -/
lemma discreteTopology_quotient_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (M : ℕ) : DiscreteTopology (kpInt p P ⧸ (maximalIdeal (kpInt p P)) ^ M) := by
  let U : AddSubgroup (kpInt p P) := ((maximalIdeal (kpInt p P)) ^ M).toAddSubgroup
  have hU : IsOpen (U : Set (kpInt p P)) := by simpa [U] using isOpen_maximalIdeal_pow p P M
  change DiscreteTopology (kpInt p P ⧸ U)
  exact QuotientAddGroup.discreteTopology hU

/-- **Surjectivity of the quotient map**: every element of
`kpInt ⧸ 𝔪^M` is hit by an element of `𝓞 K` (dense image of `𝓞 K` in the
compact/discrete quotient). -/
theorem quotientToKpInt_surjective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (M : ℕ) :
    Function.Surjective ((Ideal.Quotient.mk ((maximalIdeal (kpInt p P)) ^ M)).comp
      (ringOfIntegersToKpInt p P)) := by
  classical
  letI : DiscreteTopology (kpInt p P ⧸ (maximalIdeal (kpInt p P)) ^ M) :=
    discreteTopology_quotient_maximalIdeal_pow p P M
  let q : kpInt p P →+* (kpInt p P ⧸ (maximalIdeal (kpInt p P)) ^ M) :=
    Ideal.Quotient.mk ((maximalIdeal (kpInt p P)) ^ M)
  have hqcont : Continuous q := by
    exact Submodule.continuous_mkQ (S := ((maximalIdeal (kpInt p P)) ^ M : Ideal (kpInt p P)))
  have hqsurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  intro t
  -- the image q (range φ) is dense in the discrete quotient, hence everything
  have hcl : q '' closure (Set.range (ringOfIntegersToKpInt p P)) ⊆
      closure (q '' Set.range (ringOfIntegersToKpInt p P)) :=
    image_closure_subset_closure_image hqcont
  have hdenφ : closure (Set.range (ringOfIntegersToKpInt p P)) = Set.univ :=
    Set.eq_univ_iff_forall.mpr (denseRange_ringOfIntegersToKpInt p P)
  have huniv : Set.univ ⊆ closure (q '' Set.range (ringOfIntegersToKpInt p P)) := by
    calc
      Set.univ = q '' closure (Set.range (ringOfIntegersToKpInt p P)) := by
        rw [hdenφ, Set.image_univ, hqsurj.range_eq]
      _ ⊆ closure (q '' Set.range (ringOfIntegersToKpInt p P)) := hcl
  have hclos : closure (q '' Set.range (ringOfIntegersToKpInt p P)) =
      q '' Set.range (ringOfIntegersToKpInt p P) := by
    simp
  have hfull : q '' Set.range (ringOfIntegersToKpInt p P) = Set.univ := by
    exact le_antisymm (Set.subset_univ _) (by simpa [hclos] using huniv)
  have ht : t ∈ q '' Set.range (ringOfIntegersToKpInt p P) := by
    simpa [hfull]
  rcases ht with ⟨a, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, rfl⟩

/-- **The kernel of the quotient map is `P^M`** (the contraction). -/
theorem ker_quotientToKpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (M : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk ((maximalIdeal (kpInt p P)) ^ M)).comp
      (ringOfIntegersToKpInt p P)) = P ^ M := by
  ext x
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk ((maximalIdeal (kpInt p P)) ^ M) (ringOfIntegersToKpInt p P x) = 0
    ↔ x ∈ P ^ M
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (mem_comap_maximalIdeal_pow p P x M).symm

/-- **THE GLOBAL↔LOCAL QUOTIENT IDENTIFICATION**:
`𝓞 K ⧸ P^M ≃+* kpInt p P ⧸ 𝔪^M` for every `M : ℕ` (ring isomorphism). -/
noncomputable def quotientRingOfIntegersIso (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (M : ℕ) :
    (𝓞 K ⧸ P ^ M) ≃+* (kpInt p P ⧸ (maximalIdeal (kpInt p P)) ^ M) := by
  classical
  let f : 𝓞 K →+* (kpInt p P ⧸ (maximalIdeal (kpInt p P)) ^ M) :=
    (Ideal.Quotient.mk ((maximalIdeal (kpInt p P)) ^ M)).comp (ringOfIntegersToKpInt p P)
  have hsurj : Function.Surjective f := quotientToKpInt_surjective p P M
  have hker : RingHom.ker f = P ^ M := ker_quotientToKpInt p P M
  exact ((Ideal.quotEquivOfEq hker).symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

/-- **The transport form**: `𝓞 K ⧸ P^(e·n) ≃+* kpInt p P ⧸ (p^n)` with
`e := P.ramificationIdx ℤ` — via
`kpInt_span_pow_eq_maximalIdeal_pow` (`(p^n)·kpInt = 𝔪^(e·n)`). -/
noncomputable def globalLocal_quotientIso (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℕ) :
    (𝓞 K ⧸ P ^ (P.ramificationIdx ℤ * n)) ≃+*
      (kpInt p P ⧸ (Ideal.span ({((p ^ n : ℕ) : kpInt p P)} : Set (kpInt p P)))) := by
  exact (quotientRingOfIntegersIso p P (P.ramificationIdx ℤ * n)).trans
    (kpInt_quot_eq_quot_maximalIdeal_pow p P n).symm

end
end Submission.Vdw.LocalField
