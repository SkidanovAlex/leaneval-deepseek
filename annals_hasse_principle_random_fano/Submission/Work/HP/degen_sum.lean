import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DiagDefs
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.Diag.ell_single_count
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.lam_basic

/-!
# `Work.HP.degen_sum`

The "degenerate" single-vector sum of Browning--Le Boudec--Sawin, *The Hasse principle for
random Fano hypersurfaces* (Annals 197 (3), 2023), proof of Theorem 1.1: the contribution
`M^{(2)}_{d,n}(A,B)` of the vectors `x ∈ Ξ_{d,n}(B)` with `μ(x) > A`, where
`μ(x) = n‖x‖/𝔡₂(x)`.

We prove the two bounds

* `Σ_{x ∈ Ξ(B), μ(x) > A} μ(x)^{n-1}/‖ν(x)‖ ≤ K A^{n-1} B`,
* `#{x ∈ Ξ(B) : μ(x) > A} ≤ K A^n B`,

for `B ≥ B₀` and `A ≥ B/log B`, by a dyadic layer-cake over `𝔡₂(x)` and the single-vector lattice
point count `ℓ_{2,n}(X;Δ) ≪ X²Δ^n log(2Δ)` (`Work.HP.FM.dmin_count`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Finset Filter

namespace Work.HP

/-! ## Plumbing -/

/-- A primitive vector is nonzero. -/
lemma isPrim_ne_zero' {n : ℕ} {v : Fin (n + 1) → ℤ} (hv : IsPrim v) : v ≠ 0 := by
  intro h
  have h0 : Finset.univ.gcd v = 0 := by
    rw [Finset.gcd_eq_zero_iff]
    intro i _
    rw [h]
    rfl
  rw [IsPrim] at hv
  omega

/-- `𝔡₂(x) ≥ 1` for `x ≠ 0`: every rank-two lattice containing `x` has covolume at least `1`. -/
lemma one_le_dmin_two_single (n : ℕ) (hn : 2 ≤ n) (x : Fin (n + 1) → ℤ) (hx : x ≠ 0) :
    1 ≤ dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext fun i => by simpa using h i)
  obtain ⟨i, hij⟩ : ∃ i : Fin (n + 1), i ≠ j := by
    have : 1 < Fintype.card (Fin (n+1)) := by simp; omega
    exact Fintype.exists_ne_of_one_lt_card this j
  let y : Fin (n + 1) → ℤ := Pi.single i 1
  have hyj : y j = 0 := by simp [y, hij]
  have hyi : y i = 1 := by simp [y]
  have hind : LinearIndependent ℤ ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 : a * x j + b * y j = 0 := by
      have := congrFun hab j; simpa using this
    rw [hyj, mul_zero, add_zero] at h1
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hj
    subst ha
    have h2 : b * y i = 0 := by
      have := congrFun hab i; simpa using this
    exact ⟨rfl, by simpa [hyi] using h2⟩
  refine le_csInf ⟨detL (Submodule.span ℤ (Set.range ![x, y])),
    Submodule.span ℤ (Set.range ![x, y]), ?_, ?_, rfl⟩ ?_
  · rw [rk, Module.finrank_eq_card_basis (Module.Basis.span hind)]; simp
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Submodule.subset_span ⟨0, rfl⟩
  · rintro D ⟨L', -, -, rfl⟩
    exact MDEstimates.detL_one_le L'

/-! ## Dyadic shell index -/

/-- `shIdx s` is the exponent of the dyadic shell containing `s`: for `s ≥ 1`,
`s ≤ 2^{shIdx s} ≤ 4s`. -/
private def shIdx (s : ℝ) : ℕ := Nat.log 2 ⌈s⌉₊ + 1

private lemma le_two_pow_shIdx (s : ℝ) : s ≤ (2:ℝ)^(shIdx s) := by
  have h1 : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have h2 : (⌈s⌉₊ : ℝ) < (2:ℝ)^(shIdx s) := by
    have h := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) ⌈s⌉₊
    have hcast : (((2:ℕ)^(Nat.log 2 ⌈s⌉₊ + 1) : ℕ) : ℝ) = (2:ℝ)^(shIdx s) := by
      rw [shIdx]; push_cast; ring
    rw [← hcast]; exact_mod_cast h
  linarith

private lemma two_pow_shIdx_le (s : ℝ) (hs : 1 ≤ s) : (2:ℝ)^(shIdx s) ≤ 4*s := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hcne : ⌈s⌉₊ ≠ 0 := by
    have : 1 ≤ ⌈s⌉₊ := Nat.one_le_ceil_iff.mpr hs0
    omega
  have h1 : (2:ℕ)^(Nat.log 2 ⌈s⌉₊) ≤ ⌈s⌉₊ := Nat.pow_log_le_self 2 hcne
  have h1r : (2:ℝ)^(Nat.log 2 ⌈s⌉₊) ≤ (⌈s⌉₊ : ℝ) := by exact_mod_cast h1
  have h2 : (⌈s⌉₊ : ℝ) < s + 1 := Nat.ceil_lt_add_one (le_of_lt hs0)
  have h3 : (2:ℝ)^(shIdx s) = 2 * (2:ℝ)^(Nat.log 2 ⌈s⌉₊) := by rw [shIdx, pow_succ]; ring
  rw [h3]; linarith

/-- `#(s.filter p) = Σ_{x ∈ s} 1_{p x}` with the indicator read in `ℝ`. -/
private lemma card_filter_cast {α : Type*} (T : Finset α) (p : α → Prop) [DecidablePred p] :
    ((T.filter p).card : ℝ) = ∑ x ∈ T, (if p x then (1:ℝ) else 0) := by
  rw [Finset.card_filter]; push_cast
  exact Finset.sum_congr rfl fun x _ => by split <;> simp

/-- The dyadic layer-cake sum: `Σ_{i ≤ M} 2^i log(2·2^i) ≤ 2^{M+1}(M+1)`. -/
private lemma dyadic_log_sum_le (M : ℕ) :
    ∑ i ∈ Finset.range (M+1), (2:ℝ)^i * Real.log (2*(2:ℝ)^i) ≤ 2^(M+1) * (M+1) := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  calc ∑ i ∈ Finset.range (M+1), (2:ℝ)^i * Real.log (2*(2:ℝ)^i)
      = ∑ i ∈ Finset.range (M+1), (2:ℝ)^i * ((i+1) * Real.log 2) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have : (2:ℝ)*(2:ℝ)^i = (2:ℝ)^(i+1) := by rw [pow_succ]; ring
        rw [this, Real.log_pow]; push_cast; ring
    _ ≤ ∑ i ∈ Finset.range (M+1), (2:ℝ)^i * ((i+1) * 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h1 : 0 ≤ ((i:ℝ)+1) := by positivity
        have h2 : 0 ≤ (2:ℝ)^i := by positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog2 h1) h2
    _ = ∑ i ∈ Finset.range (M+1), (i+1) * (2:ℝ)^i := by
        refine Finset.sum_congr rfl fun i hi => by ring
    _ ≤ ∑ i ∈ Finset.range (M+1), (M+1) * (2:ℝ)^i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < M+1 := Finset.mem_range.mp hi
        have h1 : ((i:ℝ)+1) ≤ ((M:ℝ)+1) := by
          have : i + 1 ≤ M + 1 := by omega
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (M+1) * ∑ i ∈ Finset.range (M+1), (2:ℝ)^i := by rw [Finset.mul_sum]
    _ = (M+1) * (2^(M+1) - 1) := by
        rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]; norm_num
    _ ≤ 2^(M+1) * (M+1) := by
        have hM1 : (0:ℝ) ≤ (M:ℝ)+1 := by positivity
        have hle : (2:ℝ)^(M+1) - 1 ≤ (2:ℝ)^(M+1) := by linarith
        calc (M+1) * ((2:ℝ)^(M+1) - 1) ≤ (M+1) * (2:ℝ)^(M+1) := mul_le_mul_of_nonneg_left hle hM1
          _ = 2^(M+1) * (M+1) := by ring

/-! ## Logarithmic domination -/

/-- For `k ≥ 1`, `(log B)^m ≪ B^k` for large `B`. -/
private lemma log_pow_le_pow (m k : ℕ) (hk : 1 ≤ k) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → (Real.log B)^m ≤ K * B^k := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, 1, one_pos, one_pos, fun B hB => ?_⟩
    have hB1 : (1:ℝ) ≤ B := by linarith
    simpa using one_le_pow₀ hB1 (n := k)
  · set ε : ℝ := (k:ℝ) / (2 * (m:ℝ)) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    have hεm : ε * (m:ℝ) = (k:ℝ)/2 := by rw [hεdef]; field_simp
    refine ⟨1/ε^m, 1, by positivity, one_pos, fun B hB => ?_⟩
    have hB1 : 1 ≤ B := by linarith
    have hB0 : 0 ≤ B := by linarith
    have hlog0 : 0 ≤ Real.log B := Real.log_nonneg hB1
    have h1 : Real.log B ≤ B^ε/ε := Real.log_le_rpow_div hB0 hεpos
    have h2 : (Real.log B)^m ≤ (B^ε/ε)^m := pow_le_pow_left₀ hlog0 h1 m
    have hdiv : (B^ε/ε)^m = B^(ε*(m:ℝ))/ε^m := by
      rw [div_pow, ← Real.rpow_natCast (B^ε) m, ← Real.rpow_mul hB0]
    rw [hdiv, hεm] at h2
    have h4 : B^((k:ℝ)/2) ≤ B^k := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      have h := Real.rpow_le_rpow_of_exponent_le hB1 (show (k:ℝ)/2 ≤ (k:ℝ) by linarith)
      rwa [Real.rpow_natCast] at h
    have h5 : B^((k:ℝ)/2)/ε^m ≤ B^k/ε^m :=
      div_le_div_of_nonneg_right h4 (pow_nonneg (le_of_lt hεpos) m)
    refine le_trans h2 (le_trans h5 (le_of_eq (by ring)))

/-! ## The dyadic layer-cake over `𝔡₂` -/

/-- `Σ_{x : x ≠ 0, ‖x‖ ≤ R, 𝔡₂(x) ≤ Δ₀} 1/𝔡₂(x)^{n-1} ≪ R² Δ₀ (log Δ₀ + 1)`. -/
private lemma delta_inv_sum_le (n : ℕ) (hn : 2 ≤ n) (KA : ℝ) (hKA : 0 < KA)
    (hcnt : ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      ((({x : Fin (n+1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧
          dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ}).ncard : ℕ) : ℝ)
        ≤ KA * X^2 * Δ^n * Real.log (2*Δ))
    {R Δ₀ : ℝ} (hR : 1 ≤ R) (hΔ₀ : 1 ≤ Δ₀) :
    (∑ᶠ x ∈ ({x : Fin (n+1) → ℤ | x ≠ 0 ∧ eNorm x ≤ R ∧
        dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ₀} : Set _),
        1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1))
      ≤ 32 * 4^(n-1) * KA * R^2 * Δ₀ * (shIdx Δ₀ + 1) := by
  classical
  set T : Finset (Fin (n+1) → ℤ) := (MDBasic.finite_eNorm_le (ι := Fin (n+1)) R).toFinset.filter
      (fun x => x ≠ 0 ∧ dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ₀) with hTdef
  have hTmem : ∀ x, x ∈ T ↔ eNorm x ≤ R ∧ x ≠ 0 ∧ dmin 2 ({x} : Set _) ≤ Δ₀ := by
    intro x; rw [hTdef]; simp only [Finset.mem_filter, Set.Finite.mem_toFinset]; tauto
  have hTcoe : ({x : Fin (n+1) → ℤ | x ≠ 0 ∧ eNorm x ≤ R ∧
      dmin 2 ({x} : Set _) ≤ Δ₀} : Set _) = ↑T := by
    ext y; simp only [Set.mem_ofPred_eq, Finset.mem_coe, hTmem y]; tauto
  rw [hTcoe, finsum_mem_coe_finset]
  have hpt : ∀ x ∈ T, 1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) ≤
      4^(n-1) * ∑ i ∈ Finset.range (shIdx Δ₀ + 1), (1/2:ℝ)^(i*(n-1)) *
        (if dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ (2:ℝ)^i then (1:ℝ) else 0) := by
    intro x hx
    obtain ⟨hxR, hx0, hxΔ⟩ := (hTmem x).mp hx
    set δ := dmin 2 ({x} : Set (Fin (n+1) → ℤ)) with hδdef
    have hδ1 : 1 ≤ δ := by rw [hδdef]; exact one_le_dmin_two_single n hn x hx0
    have hδpos : 0 < δ := lt_of_lt_of_le one_pos hδ1
    have hshle : shIdx δ ≤ shIdx Δ₀ := by
      rw [shIdx, shIdx]
      exact Nat.add_le_add_right (Nat.log_mono_right (Nat.ceil_mono (by rw [hδdef]; exact hxΔ))) 1
    have hmem : shIdx δ ∈ Finset.range (shIdx Δ₀ + 1) := Finset.mem_range.mpr (by omega)
    have hcond : δ ≤ (2:ℝ)^(shIdx δ) := le_two_pow_shIdx δ
    have hsingle := Finset.single_le_sum (f := fun i => (1/2:ℝ)^(i*(n-1)) *
        (if δ ≤ (2:ℝ)^i then (1:ℝ) else 0)) (fun i _ => by split <;> positivity) hmem
    rw [if_pos hcond, mul_one] at hsingle
    have hδ4 : (1:ℝ)/δ ≤ 4 / (2:ℝ)^(shIdx δ) := by
      rw [div_le_div_iff₀ hδpos (by positivity)]
      have := two_pow_shIdx_le δ hδ1
      linarith
    have hpow : (1/δ)^(n-1) ≤ (4/(2:ℝ)^(shIdx δ))^(n-1) :=
      pow_le_pow_left₀ (by positivity) hδ4 (n-1)
    have hkey : (4/(2:ℝ)^(shIdx δ))^(n-1) = 4^(n-1) * (1/2:ℝ)^(shIdx δ*(n-1)) := by
      rw [div_pow, div_eq_mul_inv, ← pow_mul, one_div, inv_pow]
    rw [hkey] at hpow
    have hlhs : 1 / δ^(n-1) = (1/δ)^(n-1) := (one_div_pow δ (n-1)).symm
    rw [hlhs]
    calc (1/δ)^(n-1) ≤ 4^(n-1) * (1/2:ℝ)^(shIdx δ*(n-1)) := hpow
      _ ≤ 4^(n-1) * ∑ i ∈ Finset.range (shIdx Δ₀ + 1), (1/2:ℝ)^(i*(n-1)) *
            (if δ ≤ (2:ℝ)^i then (1:ℝ) else 0) :=
          mul_le_mul_of_nonneg_left hsingle (by positivity)
  have hcard : ∀ i ∈ Finset.range (shIdx Δ₀ + 1),
      ((T.filter (fun x => dmin 2 ({x} : Set _) ≤ (2:ℝ)^i)).card : ℝ)
        ≤ KA * R^2 * ((2:ℝ)^i)^n * Real.log (2*(2:ℝ)^i) := by
    intro i hi
    have h2i : (1:ℝ) ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num) (n := i)
    have hsub : ((T.filter (fun x => dmin 2 ({x} : Set _) ≤ (2:ℝ)^i) : Finset _) : Set _) ⊆
        {x : Fin (n+1) → ℤ | x ≠ 0 ∧ eNorm x ≤ R ∧ dmin 2 ({x} : Set _) ≤ (2:ℝ)^i} := by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx
      obtain ⟨hxT, hxi⟩ := hx
      obtain ⟨hxR, hx0, -⟩ := (hTmem x).mp hxT
      exact ⟨hx0, hxR, hxi⟩
    have hfin : ({x : Fin (n+1) → ℤ | x ≠ 0 ∧ eNorm x ≤ R ∧
        dmin 2 ({x} : Set _) ≤ (2:ℝ)^i}).Finite :=
      (MDBasic.finite_eNorm_le (ι := Fin (n+1)) R).subset (fun x hx => hx.2.1)
    have hthis := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at hthis
    exact le_trans (by exact_mod_cast hthis) (hcnt R ((2:ℝ)^i) hR h2i)
  have hkey2 : ∀ i : ℕ, (1/2:ℝ)^(i*(n-1)) * (KA * R^2 * ((2:ℝ)^i)^n * Real.log (2*(2:ℝ)^i))
      = (KA * R^2) * ((2:ℝ)^i * Real.log (2*(2:ℝ)^i)) := by
    intro i
    have hinner : (1/2:ℝ)^(i*(n-1)) * ((2:ℝ)^i)^n = (2:ℝ)^i := by
      have h1 : ((2:ℝ)^i)^n = (2:ℝ)^(i*n) := by rw [pow_mul]
      have h2 : (1/2:ℝ)^(i*(n-1)) = ((2:ℝ)^(i*(n-1)))⁻¹ := by rw [one_div, inv_pow]
      have h3 : i*n = i*(n-1) + i := by
        conv_lhs => rw [show n = (n-1)+1 by omega]
        rw [Nat.mul_add, Nat.mul_one]
      have h4 : (0:ℝ) < (2:ℝ)^(i*(n-1)) := by positivity
      rw [h2, h1, h3, pow_add]
      field_simp
    calc (1/2:ℝ)^(i*(n-1)) * (KA * R^2 * ((2:ℝ)^i)^n * Real.log (2*(2:ℝ)^i))
        = (KA * R^2 * Real.log (2*(2:ℝ)^i)) * ((1/2:ℝ)^(i*(n-1)) * ((2:ℝ)^i)^n) := by ring
      _ = (KA * R^2) * ((2:ℝ)^i * Real.log (2*(2:ℝ)^i)) := by rw [hinner]; ring
  calc ∑ x ∈ T, 1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)
      ≤ ∑ x ∈ T, 4^(n-1) * ∑ i ∈ Finset.range (shIdx Δ₀ + 1), (1/2:ℝ)^(i*(n-1)) *
          (if dmin 2 ({x} : Set _) ≤ (2:ℝ)^i then (1:ℝ) else 0) := Finset.sum_le_sum hpt
    _ = 4^(n-1) * ∑ i ∈ Finset.range (shIdx Δ₀ + 1), (1/2:ℝ)^(i*(n-1)) *
          ((T.filter (fun x => dmin 2 ({x} : Set _) ≤ (2:ℝ)^i)).card : ℝ) := by
        have hL : (∑ x ∈ T, 4^(n-1) * ∑ i ∈ Finset.range (shIdx Δ₀ + 1), (1/2:ℝ)^(i*(n-1)) *
            (if dmin 2 ({x} : Set _) ≤ (2:ℝ)^i then (1:ℝ) else 0))
          = 4^(n-1) * ∑ x ∈ T, ∑ i ∈ Finset.range (shIdx Δ₀ + 1), (1/2:ℝ)^(i*(n-1)) *
            (if dmin 2 ({x} : Set _) ≤ (2:ℝ)^i then (1:ℝ) else 0) := by rw [Finset.mul_sum]
        rw [hL]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [card_filter_cast, Finset.mul_sum]
    _ ≤ 4^(n-1) * ∑ i ∈ Finset.range (shIdx Δ₀ + 1), (1/2:ℝ)^(i*(n-1)) *
          (KA * R^2 * ((2:ℝ)^i)^n * Real.log (2*(2:ℝ)^i)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
        intro i hi
        exact mul_le_mul_of_nonneg_left (hcard i hi) (by positivity)
    _ = 4^(n-1) * ((KA * R^2) * ∑ i ∈ Finset.range (shIdx Δ₀ + 1),
          (2:ℝ)^i * Real.log (2*(2:ℝ)^i)) := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => hkey2 i
    _ ≤ 4^(n-1) * ((KA * R^2) * (2^(shIdx Δ₀+1) * ((shIdx Δ₀:ℝ) + 1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (dyadic_log_sum_le (shIdx Δ₀)) (by positivity)) (by positivity)
    _ ≤ 4^(n-1) * ((KA * R^2) * (8 * Δ₀ * ((shIdx Δ₀:ℝ) + 1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        have h8 : (2:ℝ)^(shIdx Δ₀+1) ≤ 8 * Δ₀ := by
          have h := two_pow_shIdx_le Δ₀ hΔ₀
          rw [pow_succ]; linarith
        exact mul_le_mul_of_nonneg_right h8 (by positivity)
    _ ≤ 32 * 4^(n-1) * KA * R^2 * Δ₀ * ((shIdx Δ₀:ℝ) + 1) := by
        have h8' : (8:ℝ) ≤ 32 := by norm_num
        calc 4^(n-1) * ((KA * R^2) * (8 * Δ₀ * ((shIdx Δ₀:ℝ) + 1)))
            = 8 * (4^(n-1) * KA * R^2 * Δ₀ * ((shIdx Δ₀:ℝ) + 1)) := by ring
          _ ≤ 32 * (4^(n-1) * KA * R^2 * Δ₀ * ((shIdx Δ₀:ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right h8' (by positivity)
          _ = 32 * 4^(n-1) * KA * R^2 * Δ₀ * ((shIdx Δ₀:ℝ) + 1) := by ring


/-! ## Pointwise bounds for the summand -/

/-- Case `d ≤ n-1`: the summand is `≪ R^{n-1-d}/𝔡₂(x)^{n-1}`. -/
private lemma ptwise_lo (d n : ℕ) (hn : 2 ≤ n) (Kc R : ℝ) (hKcpos : 0 < Kc)
    (hKc : ∀ y : Fin (n+1) → ℤ, Kc * eNorm y ^ d ≤ eNorm (veronese d n y))
    (hdln : d ≤ n - 1) {x : Fin (n+1) → ℤ} (hx : x ≠ 0) (hxR : eNorm x ≤ R) :
    (mu1 d n x)^(n-1) / eNorm (veronese d n x)
      ≤ (n:ℝ)^(n-1)/Kc * R^(n-1-d) * (1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)) := by
  have hrpos : 0 < eNorm x := lt_of_lt_of_le one_pos (one_le_eNorm hx)
  have hδ1 : 1 ≤ dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := one_le_dmin_two_single n hn x hx
  have hver := hKc x
  have hhu : (mu1 d n x)^(n-1)
      = (n:ℝ)^(n-1) * eNorm x^(n-1) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by
    rw [show mu1 d n x = (n:ℝ) * eNorm x / dmin 2 ({x} : Set (Fin (n+1) → ℤ)) from rfl,
      div_pow, mul_pow]
  have hrdiv : eNorm x^(n-1) / eNorm x^d = eNorm x^(n-1-d) := by
    rw [div_eq_mul_inv, ← pow_sub₀ (eNorm x) (ne_of_gt hrpos) hdln]
  have h1ν : 1 / eNorm (veronese d n x) ≤ 1 / (Kc * eNorm x^d) :=
    one_div_le_one_div_of_le (by positivity) hver
  rw [hhu, div_eq_mul_one_div]
  calc ((n:ℝ)^(n-1) * eNorm x^(n-1) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1))
        * (1 / eNorm (veronese d n x))
      ≤ ((n:ℝ)^(n-1) * eNorm x^(n-1) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1))
        * (1 / (Kc * eNorm x^d)) := mul_le_mul_of_nonneg_left h1ν (by positivity)
    _ = (n:ℝ)^(n-1)/Kc * (eNorm x^(n-1) / eNorm x^d)
          / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by ring
    _ = (n:ℝ)^(n-1)/Kc * eNorm x^(n-1-d) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by
        rw [hrdiv]
    _ ≤ (n:ℝ)^(n-1)/Kc * R^(n-1-d) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hrpos) hxR (n-1-d)) (by positivity)
    _ = (n:ℝ)^(n-1)/Kc * R^(n-1-d) * (1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)) := by
        ring

/-- Case `d = n`: the summand is `≪ 1/(A 𝔡₂(x)^{n-1})`. -/
private lemma ptwise_eq (d n : ℕ) (hn : 2 ≤ n) (Kc A : ℝ) (hKcpos : 0 < Kc) (hA : 0 < A)
    (hKc : ∀ y : Fin (n+1) → ℤ, Kc * eNorm y ^ d ≤ eNorm (veronese d n y))
    (hdn' : d = n) {x : Fin (n+1) → ℤ} (hx : x ≠ 0) (hμ : A < mu1 d n x) :
    (mu1 d n x)^(n-1) / eNorm (veronese d n x)
      ≤ (n:ℝ)^n / (Kc * A) * (1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)) := by
  have hrpos : 0 < eNorm x := lt_of_lt_of_le one_pos (one_le_eNorm hx)
  have hδ1 : 1 ≤ dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := one_le_dmin_two_single n hn x hx
  have hδpos : 0 < dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := lt_of_lt_of_le one_pos hδ1
  have hver := hKc x
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hμ' : A < (n:ℝ) * eNorm x / dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := hμ
  have hrn : (n:ℝ) * eNorm x / dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ (n:ℝ) * eNorm x := by
    rw [div_le_iff₀ hδpos]
    calc (n:ℝ) * eNorm x = (n:ℝ) * eNorm x * 1 := by ring
      _ ≤ (n:ℝ) * eNorm x * dmin 2 ({x} : Set (Fin (n+1) → ℤ)) :=
          mul_le_mul_of_nonneg_left hδ1 (by positivity)
  have hμn : A < (n:ℝ) * eNorm x := lt_of_lt_of_le hμ' hrn
  have h1r : 1 / eNorm x ≤ (n:ℝ) / A := by
    rw [div_le_div_iff₀ hrpos hA]; linarith
  have hhu : (mu1 d n x)^(n-1)
      = (n:ℝ)^(n-1) * eNorm x^(n-1) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by
    rw [show mu1 d n x = (n:ℝ) * eNorm x / dmin 2 ({x} : Set (Fin (n+1) → ℤ)) from rfl,
      div_pow, mul_pow]
  have hEd : eNorm x^d = eNorm x^n := by
    rw [hdn']
  have hnpow : (n:ℝ)^n = (n:ℝ)^(n-1) * (n:ℝ) := by
    have h1 : (n:ℝ)^((n-1)+1) = (n:ℝ)^n := by
      rw [Nat.sub_add_cancel (show 1 ≤ n by omega)]
    rw [← h1, pow_succ]
  have hrdiv : eNorm x^(n-1) / eNorm x^d = 1 / eNorm x := by
    rw [hEd]
    have hEd' : eNorm x^n = eNorm x^(n-1) * eNorm x := by
      have h1 : (eNorm x)^((n-1)+1) = (eNorm x)^n := by
        rw [Nat.sub_add_cancel (show 1 ≤ n by omega)]
      rw [← h1, pow_succ]
    rw [hEd']
    field_simp
  have h1ν : 1 / eNorm (veronese d n x) ≤ 1 / (Kc * eNorm x^d) :=
    one_div_le_one_div_of_le (by positivity) hver
  rw [hhu, div_eq_mul_one_div]
  calc ((n:ℝ)^(n-1) * eNorm x^(n-1) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1))
        * (1 / eNorm (veronese d n x))
      ≤ ((n:ℝ)^(n-1) * eNorm x^(n-1) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1))
        * (1 / (Kc * eNorm x^d)) := mul_le_mul_of_nonneg_left h1ν (by positivity)
    _ = (n:ℝ)^(n-1)/Kc * (eNorm x^(n-1) / eNorm x^d)
          / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by ring
    _ = (n:ℝ)^(n-1)/Kc * (1 / eNorm x) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by
        rw [hrdiv]
    _ ≤ (n:ℝ)^(n-1)/Kc * ((n:ℝ) / A) / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h1r (by positivity)
    _ = (n:ℝ)^n / (Kc * A) * (1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)) := by
        rw [hnpow]
        ring

/-! ## The arithmetic consequences of the two layer-cake bounds -/

/-- Counting arithmetic: `R² Δ₀^n log(2Δ₀) ≪ n^n (log(2n)+1) K₃ A^n B`. -/
private lemma count_arith (n : ℕ) (hn : 2 ≤ n) (K₃ : ℝ) (hK₃ : 0 ≤ K₃)
    {A B R Δ₀ : ℝ} (hA : 0 < A) (hB : 0 < B) (hR1 : 1 ≤ R) (hRB : R ≤ B)
    (hlB : 0 < Real.log B) (hΔeq : Δ₀ = (n:ℝ)*R/A) (hΔ1 : 1 ≤ Δ₀)
    (hAB : B / Real.log B ≤ A)
    (hlog3 : (Real.log B)^(2*n+1) ≤ K₃ * B^(n-1))
    (hlogΔ : Real.log (2*Δ₀) ≤ (Real.log (2*(n:ℝ)) + 1) * Real.log B) :
    R^2 * Δ₀^n * Real.log (2*Δ₀)
      ≤ ((n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃) * A^n * B := by
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h2n1 : (1:ℝ) ≤ 2*(n:ℝ) := by linarith
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hΔpos : 0 < Δ₀ := lt_of_lt_of_le one_pos hΔ1
  have hlogΔ0 : 0 ≤ Real.log (2*Δ₀) := Real.log_nonneg (by linarith)
  have hlog2n : (0:ℝ) ≤ Real.log (2*(n:ℝ)) := Real.log_nonneg h2n1
  have hLp : 0 ≤ Real.log (2*(n:ℝ)) + 1 := by linarith
  have hXp : 0 ≤ (n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) := by positivity
  have hR2Δ : R^2 * Δ₀^n ≤ (n:ℝ)^n * B^(n+2) / A^n := by
    have h1 : Δ₀^n = (n:ℝ)^n * R^n / A^n := by rw [hΔeq, div_pow, mul_pow]
    have h2 : R^2 * ((n:ℝ)^n * R^n / A^n) = (n:ℝ)^n * R^(n+2) / A^n := by
      rw [show R^(n+2) = R^2 * R^n by rw [show n+2 = 2+n by omega, pow_add]]
      ring
    rw [h1, h2]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hRpos) hRB (n+2)) (by positivity))
      (by positivity)
  have hmain : B^(n+1) * Real.log B ≤ K₃ * A^(2*n) := by
    have hXpos : (0:ℝ) < (Real.log B)^(2*n) := by positivity
    have hb2n : B^(2*n) ≤ A^(2*n) * (Real.log B)^(2*n) := by
      have h := pow_le_pow_left₀ (le_of_lt (div_pos hB hlB)) hAB (2*n)
      rw [div_pow] at h
      rwa [div_le_iff₀ hXpos] at h
    have h2 : B^(n+1) * Real.log B * (Real.log B)^(2*n)
        ≤ K₃ * A^(2*n) * (Real.log B)^(2*n) := by
      calc B^(n+1) * Real.log B * (Real.log B)^(2*n)
          = B^(n+1) * (Real.log B)^(2*n+1) := by
            rw [show (Real.log B)^(2*n+1) = (Real.log B)^(2*n) * Real.log B by rw [pow_succ]]
            ring
        _ ≤ B^(n+1) * (K₃ * B^(n-1)) := mul_le_mul_of_nonneg_left hlog3 (by positivity)
        _ = K₃ * B^(2*n) := by
            rw [show B^(n+1) * (K₃ * B^(n-1)) = K₃ * (B^(n+1) * B^(n-1)) by ring,
              show B^(n+1) * B^(n-1) = B^(2*n) by rw [← pow_add]; congr 1; omega]
        _ ≤ K₃ * (A^(2*n) * (Real.log B)^(2*n)) := mul_le_mul_of_nonneg_left hb2n hK₃
        _ = K₃ * A^(2*n) * (Real.log B)^(2*n) := by ring
    have h3 := div_le_div_of_nonneg_right h2 (le_of_lt hXpos)
    rwa [mul_div_cancel_right₀ _ (ne_of_gt hXpos), mul_div_cancel_right₀ _ (ne_of_gt hXpos)] at h3
  calc R^2 * Δ₀^n * Real.log (2*Δ₀)
      ≤ ((n:ℝ)^n * B^(n+2) / A^n) * ((Real.log (2*(n:ℝ)) + 1) * Real.log B) :=
        mul_le_mul hR2Δ hlogΔ hlogΔ0 (by positivity)
    _ = (n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * (B^(n+1) * Real.log B) * B / A^n := by
        rw [show B^(n+2) = B^(n+1) * B by rw [show n+2 = (n+1)+1 by omega, pow_succ]]
        ring
    _ ≤ (n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * (K₃ * A^(2*n)) * B / A^n := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hXp) (le_of_lt hB)
    _ = ((n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃) * A^n * B := by
        have hAne : A ^ n ≠ 0 := by positivity
        rw [show (2:ℕ)*n = n+n by omega]
        rw [pow_add]
        field_simp <;> try ring

/-- Sum arithmetic, case `d ≤ n-1`: `B (n R/A) log B ≪ n K₁ A^{n-1} B`. -/
private lemma sum_arith_lo (n : ℕ) (hn : 2 ≤ n) (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    {A B R : ℝ} (hA : 0 < A) (hB : 0 < B) (hlB : 0 < Real.log B)
    (hRB : R ≤ B) (hAB : B / Real.log B ≤ A)
    (hlog1 : (Real.log B)^(n+1) ≤ K₁ * B^(n-1)) :
    B * ((n:ℝ) * R / A) * Real.log B ≤ (n:ℝ) * K₁ * A^(n-1) * B := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hRA : R / A ≤ Real.log B := by
    rw [div_le_iff₀ hA]
    have h := (div_le_iff₀ hlB).mp hAB
    linarith
  have hAnn : B^(n-1) / (Real.log B)^(n-1) ≤ A^(n-1) := by
    have h := pow_le_pow_left₀ (le_of_lt (div_pos hB hlB)) hAB (n-1)
    rwa [div_pow] at h
  have hlog2 : Real.log B * Real.log B ≤ K₁ * A^(n-1) := by
    have hX : (0:ℝ) < (Real.log B)^(n-1) := by positivity
    have h1 : Real.log B * Real.log B ≤ K₁ * (B^(n-1) / (Real.log B)^(n-1)) := by
      rw [show K₁ * (B^(n-1) / (Real.log B)^(n-1)) = K₁ * B^(n-1) / (Real.log B)^(n-1) by ring]
      rw [le_div_iff₀ hX]
      have h2 : Real.log B * Real.log B * (Real.log B)^(n-1) = (Real.log B)^(n+1) := by
        rw [show n+1 = 2 + (n-1) by omega, pow_add]; ring
      rw [h2]
      exact hlog1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hAnn hK₁)
  calc B * ((n:ℝ) * R / A) * Real.log B
      = (n:ℝ) * B * (R / A) * Real.log B := by ring
    _ ≤ (n:ℝ) * B * Real.log B * Real.log B := by
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hlB)
        exact mul_le_mul_of_nonneg_left hRA (by positivity)
    _ = (n:ℝ) * B * (Real.log B * Real.log B) := by ring
    _ ≤ (n:ℝ) * B * (K₁ * A^(n-1)) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ = (n:ℝ) * K₁ * A^(n-1) * B := by ring

/-- Sum arithmetic, case `d = n`: `B³ log B / A² ≪ K₂ A^{n-1} B`. -/
private lemma sum_arith_eq (n : ℕ) (hn : 2 ≤ n) (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hlB : 0 < Real.log B)
    (hAB : B / Real.log B ≤ A)
    (hlog2 : (Real.log B)^(n+2) ≤ K₂ * B^(n-1)) :
    B^3 * Real.log B / A^2 ≤ K₂ * A^(n-1) * B := by
  have hkey : B^2 * Real.log B ≤ K₂ * A^(n+1) := by
    have hX : (0:ℝ) < (Real.log B)^(n+1) := by positivity
    have h1 : B^2 * Real.log B * (Real.log B)^(n+1) ≤ K₂ * B^(n+1) := by
      have h2 : B^2 * Real.log B * (Real.log B)^(n+1) = B^2 * (Real.log B)^(n+2) := by
        rw [show n+2 = (n+1)+1 by omega, pow_succ]; ring
      rw [h2]
      calc B^2 * (Real.log B)^(n+2) ≤ B^2 * (K₂ * B^(n-1)) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = K₂ * B^(n+1) := by
            rw [show B^2 * (K₂ * B^(n-1)) = K₂ * (B^2 * B^(n-1)) by ring,
              show B^2 * B^(n-1) = B^(n+1) by rw [← pow_add]; congr 1; omega]
    have h4 : B^(n+1) ≤ A^(n+1) * (Real.log B)^(n+1) := by
      have h := pow_le_pow_left₀ (le_of_lt (div_pos hB hlB)) hAB (n+1)
      rw [div_pow] at h
      rwa [div_le_iff₀ hX] at h
    have h3 : K₂ * B^(n+1) ≤ K₂ * A^(n+1) * (Real.log B)^(n+1) := by
      calc K₂ * B^(n+1) ≤ K₂ * (A^(n+1) * (Real.log B)^(n+1)) := mul_le_mul_of_nonneg_left h4 hK₂
        _ = K₂ * A^(n+1) * (Real.log B)^(n+1) := by ring
    have h5 := div_le_div_of_nonneg_right (le_trans h1 h3) (le_of_lt hX)
    rwa [mul_div_cancel_right₀ _ (ne_of_gt hX), mul_div_cancel_right₀ _ (ne_of_gt hX)] at h5
  have hA2 : (0:ℝ) < A^2 := by positivity
  calc B^3 * Real.log B / A^2 = B * (B^2 * Real.log B) / A^2 := by ring
    _ ≤ B * (K₂ * A^(n+1)) / A^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (le_of_lt hB)) (le_of_lt hA2)
    _ = K₂ * A^(n-1) * B := by
        rw [show A^(n+1) = A^(n-1) * A^2 by rw [show n+1 = (n-1)+2 by omega, pow_add]]
        field_simp <;> try ring

/-! ## The main theorem -/

theorem degen_sum (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A →
      (∑ᶠ x ∈ ({x ∈ Xi d n B | A < mu1 d n x} : Set (Fin (n + 1) → ℤ)),
          (mu1 d n x) ^ (n - 1) / eNorm (veronese d n x))
          ≤ K * A ^ (n - 1) * B ∧
      ((({x ∈ Xi d n B | A < mu1 d n x} : Set (Fin (n + 1) → ℤ)).ncard : ℝ))
          ≤ K * A ^ n * B := by
  classical
  have hn : 2 ≤ n := le_trans hd hdn
  obtain ⟨Kc, Kc₂, hKcpos, hKc₂pos, hKc⟩ := eNorm_veronese_bounds d n (by omega : 1 ≤ d)
  obtain ⟨KA, hKApos, hKA'⟩ := Diag.ell_single_count n hn
  have hKA : ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      ((({x : Fin (n+1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧
          dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ}).ncard : ℕ) : ℝ)
        ≤ KA * X^2 * Δ^n * Real.log (2*Δ) := by
    intro X Δ hX hΔ
    have hsub : ({x : Fin (n+1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧
        dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ}) ⊆
        {x : Fin (n+1) → ℤ | 0 < eNorm x ∧ eNorm x ≤ X ∧
          dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ} := by
      intro x hx
      exact ⟨lt_of_lt_of_le one_pos (one_le_eNorm hx.1), hx.2.1, hx.2.2⟩
    have hfin : ({x : Fin (n+1) → ℤ | 0 < eNorm x ∧ eNorm x ≤ X ∧
        dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ}).Finite :=
      (MDBasic.finite_eNorm_le (ι := Fin (n+1)) X).subset (fun x hx => hx.2.1)
    have h := Set.ncard_le_ncard hsub hfin
    exact le_trans (by exact_mod_cast h) (hKA' X Δ hX hΔ)
  obtain ⟨K₃, B₃, hK₃pos, hB₃pos, hlog3⟩ := log_pow_le_pow (2*n+1) (n-1) (by omega)
  obtain ⟨K₁, B₁, hK₁pos, hB₁pos, hlog1⟩ := log_pow_le_pow (n+1) (n-1) (by omega)
  obtain ⟨K₂, B₂, hK₂pos, hB₂pos, hlog2⟩ := log_pow_le_pow (n+2) (n-1) (by omega)
  set Kval : ℝ := max 1 (max (KA * (n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃)
      (max (32 * 4^(n-1) * (n:ℝ)^n * ((n:ℝ)+2) * KA * K₁ / Kc)
           (32 * 4^(n-1) * (n:ℝ)^(n+1) * ((n:ℝ)+2) * KA * K₂ / Kc))) with hKdef
  have hKpos : 0 < Kval := by
    rw [hKdef]
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨Kval, max (max (max B₃ B₁) (max B₂ (Real.exp 2))) 4, hKpos, ?_, ?_⟩
  · positivity
  · intro A B hB hA
    have hB3 : B₃ ≤ B :=
      le_trans (le_trans (le_trans (le_max_left B₃ B₁) (le_max_left _ _)) (le_max_left _ _)) hB
    have hB1' : B₁ ≤ B :=
      le_trans (le_trans (le_trans (le_max_right B₃ B₁) (le_max_left _ _)) (le_max_left _ _)) hB
    have hB2' : B₂ ≤ B :=
      le_trans (le_trans (le_trans (le_max_left B₂ (Real.exp 2)) (le_max_right _ _))
        (le_max_left _ _)) hB
    have hexp2 : Real.exp 2 ≤ B :=
      le_trans (le_trans (le_trans (le_max_right B₂ (Real.exp 2)) (le_max_right _ _))
        (le_max_left _ _)) hB
    have hlogB2 : 2 ≤ Real.log B := by
      have h := Real.log_le_log (Real.exp_pos 2) hexp2
      rwa [Real.log_exp] at h
    have hlogB0 : 0 < Real.log B := by linarith
    have hBpos : 0 < B := by
      have : (0:ℝ) < Real.exp 2 := Real.exp_pos 2
      linarith
    have hA0 : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogB0) hA
    have hdnR : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
    have hB1le : (1:ℝ) ≤ B :=
      le_trans (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2)) hexp2
    have hBA : B ≤ A * Real.log B := (div_le_iff₀ hlogB0).mp hA
    have hAnn : (0:ℝ) ≤ A := le_of_lt hA0
    have hBnn : (0:ℝ) ≤ B := le_of_lt hBpos
    have hKnn : (0:ℝ) ≤ Kval := le_of_lt hKpos
    have hAn : (0:ℝ) ≤ A^n := by positivity
    have hAnm1 : (0:ℝ) ≤ A^(n-1) := by positivity
    have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hexppos : 0 < (n:ℝ) + 1 - d := by
      have : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
      linarith
    set R : ℝ := B ^ (1 / ((n:ℝ) + 1 - d)) with hRdef
    have hRge1 : 1 ≤ R := by
      rw [hRdef]
      exact Real.one_le_rpow hB1le (by positivity)
    have hRpos : 0 < R := lt_of_lt_of_le one_pos hRge1
    have hRnn : (0:ℝ) ≤ R := le_of_lt hRpos
    have hRleB : R ≤ B := by
      rw [hRdef]
      have hxz : 1 / ((n:ℝ) + 1 - d) ≤ 1 := by
        rw [div_le_one hexppos]; linarith
      calc B ^ (1/((n:ℝ)+1-d)) ≤ B ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hB1le hxz
        _ = B := Real.rpow_one B
    have hRpow : R ^ (n+1-d) = B := by
      rw [(Real.rpow_natCast R (n+1-d)).symm, hRdef, ← Real.rpow_mul (le_of_lt hBpos)]
      have hcast : (((n+1-d:ℕ)):ℝ) = (n:ℝ)+1-d := by
        rw [Nat.cast_sub (show d ≤ n+1 by omega)]
        push_cast
        ring
      rw [hcast, one_div, inv_mul_cancel₀ (ne_of_gt hexppos), Real.rpow_one]
    set Δ₀ : ℝ := (n:ℝ) * R / A with hΔ₀def
    set Sf : Finset (Fin (n+1) → ℤ) :=
      (Xi_finite d n B).toFinset.filter (fun x => A < mu1 d n x) with hSfdef
    have hSfcoe : ((Sf : Set (Fin (n+1) → ℤ))) = {x ∈ Xi d n B | A < mu1 d n x} := by
      rw [hSfdef]; ext x; simp
    have hSfmem : ∀ x ∈ Sf, x ∈ Xi d n B ∧ A < mu1 d n x := by
      intro x hx
      rw [hSfdef] at hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      exact ⟨(Set.Finite.mem_toFinset (Xi_finite d n B)).mp hx1, hx2⟩
    by_cases hΔ : 1 ≤ Δ₀
    · rw [← hSfcoe, finsum_mem_coe_finset, Set.ncard_coe_finset]
      have hmem : ∀ x ∈ Sf, x ≠ 0 ∧ eNorm x ≤ R ∧ dmin 2 ({x} : Set (Fin (n+1) → ℤ)) ≤ Δ₀ := by
        intro x hx
        obtain ⟨hxXi, hxμ⟩ := hSfmem x hx
        obtain ⟨hxprim, hxR⟩ := hxXi
        have hx0 : x ≠ 0 := isPrim_ne_zero' hxprim
        have hδ1 : 1 ≤ dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := one_le_dmin_two_single n hn x hx0
        have hδpos : 0 < dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := lt_of_lt_of_le one_pos hδ1
        have hμ : A < (n:ℝ) * eNorm x / dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := hxμ
        have hδA : A * dmin 2 ({x} : Set (Fin (n+1) → ℤ)) < (n:ℝ) * eNorm x :=
          (lt_div_iff₀ hδpos).mp hμ
        have hδlt : dmin 2 ({x} : Set (Fin (n+1) → ℤ)) < (n:ℝ) * eNorm x / A := by
          rw [lt_div_iff₀ hA0]; linarith
        refine ⟨hx0, by rw [hRdef]; exact hxR, ?_⟩
        refine le_trans (le_of_lt hδlt) ?_
        rw [hΔ₀def]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxR hnR) (le_of_lt hA0)
      set Tset : Set (Fin (n+1) → ℤ) :=
        {x | x ≠ 0 ∧ eNorm x ≤ R ∧ dmin 2 ({x} : Set _) ≤ Δ₀} with hTset
      have hTfin : Tset.Finite := by
        rw [hTset]
        exact (MDBasic.finite_eNorm_le (ι := Fin (n+1)) R).subset (fun x hx => hx.2.1)
      have hSfT : (Sf : Set _) ⊆ Tset := fun x hx => by rw [hTset]; exact hmem x hx
      have hdelta : ∑ᶠ x ∈ Tset, 1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)
          ≤ 32 * 4^(n-1) * KA * R^2 * Δ₀ * ((shIdx Δ₀ : ℝ) + 1) := by
        rw [hTset]
        exact delta_inv_sum_le n hn KA hKApos hKA hRge1 hΔ
      have hΔ₀le : Δ₀ ≤ (n:ℝ) * Real.log B := by
        rw [hΔ₀def]
        have h1 : R / A ≤ Real.log B := by
          rw [div_le_iff₀ hA0]
          nlinarith [hBA, hRleB, hlogB0]
        calc (n:ℝ) * R / A = (n:ℝ) * (R/A) := mul_div_assoc _ _ _
          _ ≤ (n:ℝ) * Real.log B := mul_le_mul_of_nonneg_left h1 hnR
      have hshIdx : (shIdx Δ₀ : ℝ) + 1 ≤ ((n:ℝ)+2) * Real.log B := by
        have hlogle : ((Nat.log 2 ⌈Δ₀⌉₊ : ℕ) : ℝ) ≤ (⌈Δ₀⌉₊ : ℝ) := by
          exact_mod_cast Nat.log_le_self 2 ⌈Δ₀⌉₊
        have hceil : (⌈Δ₀⌉₊ : ℝ) + 1 ≤ Δ₀ + 2 := by
          have hΔpos : 0 < Δ₀ := lt_of_lt_of_le one_pos hΔ
          have := Nat.ceil_lt_add_one (le_of_lt hΔpos); linarith
        have hcast : (shIdx Δ₀ : ℝ) = ((Nat.log 2 ⌈Δ₀⌉₊ : ℕ) : ℝ) + 1 := by
          simp only [shIdx]; push_cast; ring
        rw [hcast]
        nlinarith [hlogle, hceil, hΔ₀le, hlogB2, hnR]
      have hlogΔle : Real.log (2*Δ₀) ≤ (Real.log (2*(n:ℝ)) + 1) * Real.log B := by
        have hΔpos : 0 < Δ₀ := lt_of_lt_of_le one_pos hΔ
        have h2Δpos : 0 < 2 * Δ₀ := by linarith
        have hle : 2 * Δ₀ ≤ 2 * ((n:ℝ) * Real.log B) := by
          have h2 : (0:ℝ) ≤ 2 := by norm_num
          have := mul_le_mul_of_nonneg_left hΔ₀le h2
          linarith [this]
        have hs : Real.log (2 * Δ₀) ≤ Real.log (2 * ((n:ℝ) * Real.log B)) :=
          Real.log_le_log h2Δpos hle
        have heq : 2 * ((n:ℝ) * Real.log B) = (2*(n:ℝ)) * Real.log B := by ring
        have h2n1 : (1:ℝ) ≤ 2*(n:ℝ) := by
          have h2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
          linarith
        have hlog2n : (0:ℝ) ≤ Real.log (2*(n:ℝ)) := Real.log_nonneg h2n1
        rw [heq, Real.log_mul (by positivity : (2:ℝ)*(n:ℝ) ≠ 0) (ne_of_gt hlogB0)] at hs
        have hll : Real.log (Real.log B) ≤ Real.log B := by
          have := Real.log_le_sub_one_of_pos hlogB0; linarith
        nlinarith [hs, hll, hlog2n, hlogB2]
      have hcnt1 : ((Sf.card : ℕ) : ℝ) ≤ KA * R^2 * Δ₀^n * Real.log (2*Δ₀) := by
        have hnc := Set.ncard_le_ncard hSfT hTfin
        rw [Set.ncard_coe_finset] at hnc
        exact le_trans (by exact_mod_cast hnc) (hKA R Δ₀ hRge1 hΔ)
      have hcount : ((Sf.card : ℕ) : ℝ) ≤ Kval * A^n * B := by
        have hcore := count_arith n hn K₃ (le_of_lt hK₃pos) hA0 hBpos hRge1 hRleB hlogB0
          hΔ₀def hΔ hA (hlog3 B hB3) hlogΔle
        have hKle : KA * ((n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃) ≤ Kval := by
          rw [hKdef]
          have he : KA * ((n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃)
              = KA * (n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃ := by ring
          rw [he]
          exact le_trans (le_max_left _ _) (le_max_right _ _)
        calc ((Sf.card : ℕ) : ℝ)
            ≤ KA * (((n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃) * A^n * B) := by
              refine le_trans hcnt1 ?_
              have h2 : KA * R^2 * Δ₀^n * Real.log (2*Δ₀)
                  = KA * (R^2 * Δ₀^n * Real.log (2*Δ₀)) := by ring
              rw [h2]
              exact mul_le_mul_of_nonneg_left hcore (le_of_lt hKApos)
          _ = (KA * ((n:ℝ)^n * (Real.log (2*(n:ℝ)) + 1) * K₃)) * A^n * B := by ring
          _ ≤ Kval * A^n * B :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKle hAn) hBnn
      have hSf_le_T : ∑ x ∈ Sf, 1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)
          ≤ ∑ᶠ x ∈ Tset, 1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1) := by
        rw [finsum_mem_of_finite Tset hTfin]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro x hx
          rw [(Set.Finite.mem_toFinset hTfin)]
          exact hSfT hx
        · intro i hi hni
          rw [(Set.Finite.mem_toFinset hTfin)] at hi
          obtain ⟨hi0, -, -⟩ := hi
          have hδ1 : 1 ≤ dmin 2 ({i} : Set (Fin (n+1) → ℤ)) := one_le_dmin_two_single n hn i hi0
          rw [one_div]
          exact inv_nonneg.mpr (pow_nonneg (le_trans zero_le_one hδ1) _)
      have hW : ∑ x ∈ Sf, 1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)
          ≤ 32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * R^3 * Real.log B / A := by
        refine le_trans hSf_le_T (le_trans hdelta ?_)
        calc 32 * 4^(n-1) * KA * R^2 * Δ₀ * ((shIdx Δ₀ : ℝ) + 1)
            ≤ 32 * 4^(n-1) * KA * R^2 * Δ₀ * (((n:ℝ)+2) * Real.log B) :=
              mul_le_mul_of_nonneg_left hshIdx (by positivity)
          _ = 32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * R^3 * Real.log B / A := by
              rw [hΔ₀def]; ring
      have hKsumLo : 32 * 4^(n-1) * (n:ℝ)^n * ((n:ℝ)+2) * KA * K₁ / Kc ≤ Kval := by
        rw [hKdef]
        exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hKsumEq : 32 * 4^(n-1) * (n:ℝ)^(n+1) * ((n:ℝ)+2) * KA * K₂ / Kc ≤ Kval := by
        rw [hKdef]
        exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hNP1 : (n:ℝ)^n = (n:ℝ)^(n-1) * (n:ℝ) := by
        have h1 : (n:ℝ)^((n-1)+1) = (n:ℝ)^n := by
          rw [Nat.sub_add_cancel (show 1 ≤ n by omega)]
        rw [← h1, pow_succ]
      have hsum : ∑ x ∈ Sf, (mu1 d n x)^(n-1) / eNorm (veronese d n x) ≤ Kval * A^(n-1) * B := by
        rcases eq_or_ne d n with hdeq | hdne
        · have hRd : R = B := by
            rw [hRdef]
            have h0 : (n:ℝ) + 1 - d = 1 := by rw [hdeq]; ring
            rw [h0, div_one, Real.rpow_one]
          have hW' : ∑ x ∈ Sf, 1 / (dmin 2 ({x} : Set (Fin (n+1) → ℤ)))^(n-1)
              ≤ 32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * B^3 * Real.log B / A := by
            refine le_trans hW (le_of_eq ?_)
            rw [hRd]
          have hpt : ∀ x ∈ Sf, (mu1 d n x)^(n-1) / eNorm (veronese d n x)
              ≤ (n:ℝ)^n / (Kc * A) * (1 / (dmin 2 ({x} : Set _))^(n-1)) := by
            intro x hx
            obtain ⟨hx0, -, -⟩ := hmem x hx
            obtain ⟨-, hxμ⟩ := hSfmem x hx
            exact ptwise_eq d n hn Kc A hKcpos hA0 (fun y => (hKc y).1) hdeq hx0 hxμ
          have hNbound := sum_arith_eq n hn K₂ (le_of_lt hK₂pos) hA0 hBpos hlogB0 hA (hlog2 B hB2')
          have hconst : (0:ℝ) ≤ (n:ℝ)^n / (Kc * A) := by positivity
          have h3 : (n:ℝ)^n / (Kc * A) * (32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * B^3 * Real.log B / A)
              = (32 * 4^(n-1) * KA * (n:ℝ)^(n+1) * ((n:ℝ)+2) / Kc) * (B^3 * Real.log B / A^2) := by
            rw [show (n:ℝ)^(n+1) = (n:ℝ)^n * (n:ℝ) by rw [pow_succ]]
            ring
          have hC : (0:ℝ) ≤ 32 * 4^(n-1) * KA * (n:ℝ)^(n+1) * ((n:ℝ)+2) / Kc := by positivity
          have h5 : (32 * 4^(n-1) * KA * (n:ℝ)^(n+1) * ((n:ℝ)+2) / Kc) * (K₂ * A^(n-1) * B)
              = (32 * 4^(n-1) * (n:ℝ)^(n+1) * ((n:ℝ)+2) * KA * K₂ / Kc) * A^(n-1) * B := by ring
          calc ∑ x ∈ Sf, (mu1 d n x)^(n-1) / eNorm (veronese d n x)
              ≤ ∑ x ∈ Sf, (n:ℝ)^n / (Kc * A) * (1 / (dmin 2 ({x} : Set _))^(n-1)) :=
                Finset.sum_le_sum hpt
            _ = (n:ℝ)^n / (Kc * A) * ∑ x ∈ Sf, 1 / (dmin 2 ({x} : Set _))^(n-1) :=
                (Finset.mul_sum Sf (fun x => 1 / (dmin 2 ({x} : Set _))^(n-1))
                  ((n:ℝ)^n / (Kc * A))).symm
            _ ≤ (n:ℝ)^n / (Kc * A) * (32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * B^3 * Real.log B / A) :=
                mul_le_mul_of_nonneg_left hW' hconst
            _ = (32 * 4^(n-1) * KA * (n:ℝ)^(n+1) * ((n:ℝ)+2) / Kc) * (B^3 * Real.log B / A^2) := h3
            _ ≤ (32 * 4^(n-1) * KA * (n:ℝ)^(n+1) * ((n:ℝ)+2) / Kc) * (K₂ * A^(n-1) * B) :=
                mul_le_mul_of_nonneg_left hNbound hC
            _ = (32 * 4^(n-1) * (n:ℝ)^(n+1) * ((n:ℝ)+2) * KA * K₂ / Kc) * A^(n-1) * B := h5
            _ ≤ Kval * A^(n-1) * B :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKsumEq hAnm1) hBnn
        · have hdln : d ≤ n - 1 := by omega
          have hpt : ∀ x ∈ Sf, (mu1 d n x)^(n-1) / eNorm (veronese d n x)
              ≤ (n:ℝ)^(n-1)/Kc * R^(n-1-d) * (1 / (dmin 2 ({x} : Set _))^(n-1)) := by
            intro x hx
            obtain ⟨hx0, hxR, -⟩ := hmem x hx
            exact ptwise_lo d n hn Kc R hKcpos (fun y => (hKc y).1) hdln hx0 hxR
          have hNbound := sum_arith_lo n hn K₁ (le_of_lt hK₁pos) hA0 hBpos hlogB0 hRleB hA (hlog1 B hB1')
          have hconst : (0:ℝ) ≤ (n:ℝ)^(n-1)/Kc * R^(n-1-d) := by positivity
          have h3 : (n:ℝ)^(n-1) / Kc * R^(n-1-d)
                * (32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * R^3 * Real.log B / A)
              = (32 * 4^(n-1) * KA * (n:ℝ)^(n-1) * ((n:ℝ)+2) / Kc)
                  * (B * ((n:ℝ) * R / A) * Real.log B) := by
            have hR3 : R^(n-1-d) * R^3 = R^(n+1-d) * R := by
              rw [← pow_add, show (n-1-d)+3 = (n+1-d)+1 by omega, pow_succ]
            rw [show (n:ℝ)^(n-1) / Kc * R^(n-1-d)
                  * (32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * R^3 * Real.log B / A)
                = 32 * 4^(n-1) * KA * (n:ℝ)^(n-1) * ((n:ℝ)+2) / Kc
                    * (R^(n-1-d) * R^3 * ((n:ℝ) * Real.log B / A)) by ring]
            rw [hR3, hRpow]
            ring
          have hC : (0:ℝ) ≤ 32 * 4^(n-1) * KA * (n:ℝ)^(n-1) * ((n:ℝ)+2) / Kc := by positivity
          have h5 : (32 * 4^(n-1) * KA * (n:ℝ)^(n-1) * ((n:ℝ)+2) / Kc) * ((n:ℝ) * K₁ * A^(n-1) * B)
              = (32 * 4^(n-1) * (n:ℝ)^n * ((n:ℝ)+2) * KA * K₁ / Kc) * A^(n-1) * B := by
            rw [hNP1]
            ring
          calc ∑ x ∈ Sf, (mu1 d n x)^(n-1) / eNorm (veronese d n x)
              ≤ ∑ x ∈ Sf, (n:ℝ)^(n-1)/Kc * R^(n-1-d) * (1 / (dmin 2 ({x} : Set _))^(n-1)) :=
                Finset.sum_le_sum hpt
            _ = (n:ℝ)^(n-1)/Kc * R^(n-1-d) * ∑ x ∈ Sf, 1 / (dmin 2 ({x} : Set _))^(n-1) :=
                (Finset.mul_sum Sf (fun x => 1 / (dmin 2 ({x} : Set _))^(n-1))
                  ((n:ℝ)^(n-1)/Kc * R^(n-1-d))).symm
            _ ≤ (n:ℝ)^(n-1)/Kc * R^(n-1-d)
                  * (32 * 4^(n-1) * KA * (n:ℝ) * ((n:ℝ)+2) * R^3 * Real.log B / A) :=
                mul_le_mul_of_nonneg_left hW hconst
            _ = (32 * 4^(n-1) * KA * (n:ℝ)^(n-1) * ((n:ℝ)+2) / Kc)
                  * (B * ((n:ℝ) * R / A) * Real.log B) := h3
            _ ≤ (32 * 4^(n-1) * KA * (n:ℝ)^(n-1) * ((n:ℝ)+2) / Kc) * ((n:ℝ) * K₁ * A^(n-1) * B) :=
                mul_le_mul_of_nonneg_left hNbound hC
            _ = (32 * 4^(n-1) * (n:ℝ)^n * ((n:ℝ)+2) * KA * K₁ / Kc) * A^(n-1) * B := h5
            _ ≤ Kval * A^(n-1) * B :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKsumLo hAnm1) hBnn
      exact ⟨hsum, hcount⟩
    · have hSempty : ({x ∈ Xi d n B | A < mu1 d n x} : Set (Fin (n+1) → ℤ)) = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxXi hxμ
        obtain ⟨hxprim, hxR⟩ := hxXi
        have hx0 : x ≠ 0 := isPrim_ne_zero' hxprim
        have hδ1 : 1 ≤ dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := one_le_dmin_two_single n hn x hx0
        have hδpos : 0 < dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := lt_of_lt_of_le one_pos hδ1
        have hμ : A < (n:ℝ) * eNorm x / dmin 2 ({x} : Set (Fin (n+1) → ℤ)) := hxμ
        have hδA : A * dmin 2 ({x} : Set (Fin (n+1) → ℤ)) < (n:ℝ) * eNorm x :=
          (lt_div_iff₀ hδpos).mp hμ
        have hxR' : eNorm x ≤ R := by rw [hRdef]; exact hxR
        have hle : (n:ℝ) * eNorm x / A ≤ Δ₀ := by
          rw [hΔ₀def]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxR' hnR) (le_of_lt hA0)
        have hδlt : dmin 2 ({x} : Set (Fin (n+1) → ℤ)) < (n:ℝ) * eNorm x / A := by
          rw [lt_div_iff₀ hA0]; linarith
        have hΔlt : Δ₀ < 1 := lt_of_not_ge hΔ
        linarith
      rw [hSempty]
      constructor
      · have h0 : (∑ᶠ x ∈ (∅ : Set (Fin (n+1) → ℤ)),
            (mu1 d n x)^(n-1) / eNorm (veronese d n x)) = 0 := by simp
        rw [h0]
        exact mul_nonneg (mul_nonneg hKnn (by positivity)) hBnn
      · have h0 : ((∅ : Set (Fin (n+1) → ℤ)).ncard : ℝ) = 0 := by simp
        rw [h0]
        exact mul_nonneg (mul_nonneg hKnn (by positivity)) hBnn

end Work.HP
