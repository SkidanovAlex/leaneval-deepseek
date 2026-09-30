import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.closed_walk_lower
import Submission.Work.N8.walk_products_close
import Submission.Work.N8.cycle_congruence
import Submission.Work.BMF.newton_series
import Submission.Work.N8.step6_defs
import Submission.Work.N8.step6v2_defs
import Submission.Work.N8.step6v2_walk_lower
import Submission.Work.N8.step6v2_hq0arith
import Submission.Work.N8.step6v2_walk_fiber
import Submission.Work.N8.step6v2_tuple_prime
import Submission.Work.N8.step6v2_tuple_congruent
import Submission.Work.N8.step6v2_tuple_close

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Step 6 (`q₀ ≪ 1`) of the N8 assembly, `200·L` variant

Assembly of `Work.N8.step6_q0_bound_v2` from the pieces proved elsewhere in this directory:

* `step6v2_walk_lower`: closed walks of length `ℓ` dominate `((c_E/c₂)(P/log P)²)^ℓ`;
* `step6v2_hq0arith`: per vertex `v ∈ T` a coefficient index `mF v ≤ k` and a modulus
  `qF v ≥ q₀^{1/k}/(k!)²`, whose prime divisors all divide `k!·q₀`, such that any integral
  difference `γ_v(A·) - γ_v(B·)` forces `qF v ∣ A^{mF v} - B^{mF v}`;
* `step6v2_tuple_prime` / `step6v2_tuple_congruent` / `step6v2_tuple_close`: the pair of prime
  tuples read along a closed walk starting at `u` lies in `step6S ℓ P N (step6C0v2 ℓ) (mF u) (qF u)`;
* `step6v2_walk_fiber`: at most `4^ℓ K^ℓ` walks with a fixed start share a fixed tuple pair.

The assembly bounds the number of walks starting at `u` by `4^ℓ K^ℓ · #S(u)` (pigeonhole over
the tuple-pair map), bounds `#S(u)` by `hN4`, converts `qF u ≥ q₀^{1/k}/(k!)²` into the
`q₀^{-1/(2k)}` factor via `hCklem`, sums over `u ∈ T` using `#T ≤ c₂N`, and cancels the common
factor `(P/log P)^{2ℓ}` against the lower bound.
-/

set_option maxHeartbeats 8000000

namespace Work.N8

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Arithmetic of the modulus.**  If `qb ≥ q₀^{1/k}/(k!)²` then
`1/√qb ≤ k!·q₀^{-1/(2k)}`. -/
lemma step6v2_inv_sqrt_le (k : ℕ) (hk : 1 ≤ k) {q₀ qb : ℕ} (hq₀ : 1 ≤ q₀) (hqb : 1 ≤ qb)
    (hlow : (q₀ : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2 ≤ (qb : ℝ)) :
    1 / Real.sqrt (qb : ℝ) ≤ (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := by
  have hq₀R : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast hq₀
  have hqbR : (0 : ℝ) < (qb : ℝ) := by exact_mod_cast hqb
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hfac2 : (0 : ℝ) < ((k.factorial : ℝ)) ^ 2 := by positivity
  have hnum : (0 : ℝ) < (q₀ : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := Real.rpow_pos_of_pos hq₀R _
  set A : ℝ := (q₀ : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2 with hA
  have hApos : 0 < A := by rw [hA]; exact div_pos hnum hfac2
  have hnat : (((k.factorial : ℝ)) ^ 2) ^ (-(1 / (2 : ℝ)))
      = ((k.factorial : ℝ))⁻¹ := by
    have h2 : ((↑(2 : ℕ) : ℝ)) * (-(1 / (2 : ℝ))) = (-1 : ℝ) := by norm_num
    rw [← Real.rpow_natCast (k.factorial : ℝ) 2, ← Real.rpow_mul (le_of_lt hfac), h2,
      Real.rpow_neg_one]
  have hexp : (1 / (k : ℝ)) * (-(1 / (2 : ℝ))) = -(1 / (2 * (k : ℝ))) := by
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
    field_simp
    try ring
  have hrpow : ((q₀ : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ (-(1 / (2 : ℝ)))
      = (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := by
    rw [← Real.rpow_mul (le_of_lt hq₀R), hexp]
  have hval : A ^ (-(1 / (2 : ℝ))) = (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := by
    rw [hA, Real.div_rpow (le_of_lt hnum) (le_of_lt hfac2), hrpow, hnat,
      div_inv_eq_mul, mul_comm]
  calc 1 / Real.sqrt (qb : ℝ)
      = (qb : ℝ) ^ (-(1 / (2 : ℝ))) := by
        rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg (le_of_lt hqbR) (1 / (2 : ℝ))]
    _ ≤ A ^ (-(1 / (2 : ℝ))) := Real.rpow_le_rpow_of_nonpos hApos hlow (by norm_num)
    _ = (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := hval

/-- `step6C0v2 ℓ` is nonnegative. -/
lemma step6C0v2_nonneg (ℓ : ℕ) : 0 ≤ step6C0v2 ℓ := le_of_lt (step6C0v2_pos ℓ)

/-- **The tuple pair of a walk lies in the `hN4`-counted set.** -/
lemma step6v2_mem_S (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ) (γ : V → Polynomial ℝ)
    (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (P N L D : ℝ)
    (hD : 0 < D) (hL : 0 < L) (hP : 1 ≤ P) (hN : 0 < N)
    (hLDN : N * L ≤ 10 * D) (k : ℕ) (hk : 1 ≤ k) (hPfac : (k.factorial : ℝ) < P)
    (q₀ : ℕ) (mF qF : V → ℕ) (u : V)
    (hcop : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' → ¬ (pr v v').1 ∣ q₀ ∧ ¬ (pr v v').2 ∣ q₀)
    (hqFcop : ∀ p : ℕ, p.Prime → ¬ p ∣ k.factorial → ¬ p ∣ q₀ → ¬ p ∣ qF u)
    (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2 ∧
      Work.BMF.IntegralOn 1 (Work.BMF.dil (((pr v v').2 : ℕ) : ℝ) (γ v) -
        Work.BMF.dil (((pr v v').1 : ℕ) : ℝ) (γ v')))
    (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 200 * L)
    (hposD : ∀ v ∈ T, D ≤ pos v)
    (hqFdvd : ∀ A B : ℕ, Work.BMF.IntegralOn 1
      (Work.BMF.dil (A : ℝ) (γ u) - Work.BMF.dil (B : ℝ) (γ u)) →
      (qF u : ℤ) ∣ ((A : ℤ) ^ (mF u) - (B : ℤ) ^ (mF u)))
    (w : Fin ℓ → V) (hw : w ∈ step6Walks Adj T ℓ) (hw0 : w ⟨0, by omega⟩ = u) :
    (step6Tuple1 ℓ pr w, step6Tuple2 ℓ pr w) ∈ step6S ℓ P N (step6C0v2 ℓ) (mF u) (qF u) := by
  have hhedge2 : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2 :=
    fun v hv v' hv' hadj => ⟨(hedge v hv v' hv' hadj).1, (hedge v hv v' hv' hadj).2.1⟩
  have hprime := step6v2_tuple_prime (Adj := Adj) (T := T) (pr := pr) (ℓ := ℓ) hℓ2
    (P := P) (k := k) hk hPfac (q₀ := q₀) (qb := qF u) hcop hqFcop hhedge2 w hw
  have hclose := step6v2_tuple_close (Adj := Adj) (T := T) (pos := pos) (pr := pr) (ℓ := ℓ) hℓ2
    (P := P) (N := N) (L := L) (D := D) hD hL hP hN hLDN hhedge2 hgeo hposD w hw
  have huT : u ∈ T := by
    rw [← hw0]
    exact (mem_step6Walks.mp hw).1 ⟨0, by omega⟩
  have hcong := step6v2_tuple_congruent (Adj := Adj) (T := T) (pr := pr) (γ := γ) (ℓ := ℓ) hℓ2
    (P := P) (u := u) huT (mw := mF u) (qw := qF u) hedge hqFdvd w hw hw0
  rw [step6S, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨by rw [Fintype.mem_piFinset]; exact hprime.1,
          by rw [Fintype.mem_piFinset]; exact hprime.2⟩, hclose, hcong⟩

/-- **Walks with a fixed start are counted by the `hN4` set.** -/
lemma step6v2_count_u (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ) (γ : V → Polynomial ℝ)
    (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (P N L D : ℝ)
    (hD : 0 < D) (hL : 0 < L) (hP : 1 ≤ P) (hN : 0 < N)
    (hLDN : N * L ≤ 10 * D) (k : ℕ) (hk : 1 ≤ k) (hPfac : (k.factorial : ℝ) < P)
    (q₀ : ℕ) (mF qF : V → ℕ) (K : ℕ) (u : V) (hu : u ∈ T)
    (hcop : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' → ¬ (pr v v').1 ∣ q₀ ∧ ¬ (pr v v').2 ∣ q₀)
    (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2 ∧
      Work.BMF.IntegralOn 1 (Work.BMF.dil (((pr v v').2 : ℕ) : ℝ) (γ v) -
        Work.BMF.dil (((pr v v').1 : ℕ) : ℝ) (γ v')))
    (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 200 * L)
    (hfib : ∀ y : ℝ, ((T.filter (fun v ↦ pos v = y)).card : ℝ) ≤ (K : ℝ))
    (hsep : ∀ v ∈ T, ∀ v' ∈ T, pos v ≠ pos v' → 500 * L ≤ |pos v - pos v'|)
    (hposD : ∀ v ∈ T, D ≤ pos v)
    (hqFcop : ∀ p : ℕ, p.Prime → ¬ p ∣ k.factorial → ¬ p ∣ q₀ → ¬ p ∣ qF u)
    (hqFdvd : ∀ A B : ℕ, Work.BMF.IntegralOn 1
      (Work.BMF.dil (A : ℝ) (γ u) - Work.BMF.dil (B : ℝ) (γ u)) →
      (qF u : ℤ) ∣ ((A : ℤ) ^ (mF u) - (B : ℤ) ^ (mF u))) :
    (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, by omega⟩ = u)).card : ℝ) ≤
      (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * step6Scard ℓ P N (step6C0v2 ℓ) (mF u) (qF u) := by
  have hhedge2 : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2 :=
    fun v hv v' hv' hadj => ⟨(hedge v hv v' hv' hadj).1, (hedge v hv v' hv' hadj).2.1⟩
  have hfiberR : ∀ v ∈ step6S ℓ P N (step6C0v2 ℓ) (mF u) (qF u),
      ((((step6Walks Adj T ℓ).filter (fun w => w ⟨0, by omega⟩ = u)).filter
        (fun w => (step6Tuple1 ℓ pr w, step6Tuple2 ℓ pr w) = v)).card ≤ 4 ^ ℓ * K ^ ℓ) := by
    intro v hv
    have hset : ((step6Walks Adj T ℓ).filter (fun w => w ⟨0, by omega⟩ = u)).filter
          (fun w => (step6Tuple1 ℓ pr w, step6Tuple2 ℓ pr w) = v)
        = Finset.univ.filter (fun w : Fin ℓ → V => w ∈ step6Walks Adj T ℓ ∧
            w ⟨0, by omega⟩ = u ∧ step6Tuple1 ℓ pr w = v.1 ∧ step6Tuple2 ℓ pr w = v.2) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      tauto
    have hR := step6v2_walk_fiber (Adj := Adj) (T := T) (pos := pos) (pr := pr) (ℓ := ℓ) hℓ2
      (P := P) (L := L) hL (K := K) hhedge2 hgeo hfib hsep u hu v.1 v.2
    rw [← hset] at hR
    have hcast : ((4 ^ ℓ * K ^ ℓ : ℕ) : ℝ) = (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      norm_num
    rw [← hcast] at hR
    exact_mod_cast hR
  have hmaps2 : ∀ w ∈ (step6Walks Adj T ℓ).filter (fun w => w ⟨0, by omega⟩ = u),
      (step6Tuple1 ℓ pr w, step6Tuple2 ℓ pr w) ∈ step6S ℓ P N (step6C0v2 ℓ) (mF u) (qF u) :=
    fun w hw => step6v2_mem_S (Adj := Adj) (T := T) (pos := pos) (pr := pr) (γ := γ) (ℓ := ℓ)
      hℓ2 (P := P) (N := N) (L := L) (D := D) hD hL hP hN hLDN k hk hPfac q₀ mF qF u
      (fun v hv v' hv' hadj => hcop v hv v' hv' hadj) hqFcop hedge hgeo hposD hqFdvd
      w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  have hmain := Finset.card_le_mul_card_image_of_maps_to hmaps2 (4 ^ ℓ * K ^ ℓ) hfiberR
  have hcast2 : ((((step6Walks Adj T ℓ).filter (fun w => w ⟨0, by omega⟩ = u)).card : ℕ) : ℝ)
      ≤ ((4 ^ ℓ * K ^ ℓ : ℕ) : ℝ) *
        (((step6S ℓ P N (step6C0v2 ℓ) (mF u) (qF u)).card : ℕ) : ℝ) := by
    exact_mod_cast hmain
  have hcast : ((4 ^ ℓ * K ^ ℓ : ℕ) : ℝ) = (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    norm_num
  rw [hcast] at hcast2
  rw [step6Scard]
  exact hcast2

/-- **Per-vertex bound.**  The number of walks of length `ℓ` starting at `u ∈ T` is at most
`4^ℓ K^ℓ` times the `hN4` count at the per-vertex exponent and modulus, with the `hCklem` and
arithmetic bounds applied. -/
lemma step6v2_per_u (Adj : V → V → Prop) [DecidableRel Adj]
    (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ) (γ : V → Polynomial ℝ)
    (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (P N L D : ℝ)
    (hD : 0 < D) (hL : 0 < L) (hP : 1 ≤ P) (hN : 0 < N)
    (hLDN : N * L ≤ 10 * D) (k : ℕ) (hk : 1 ≤ k) (hPfac : (k.factorial : ℝ) < P)
    (q₀ : ℕ) (hq₀ : 1 ≤ q₀) (mF qF : V → ℕ) (K : ℕ) (u : V) (hu : u ∈ T)
    (G B Ck : ℝ) (hG : 0 < G) (hB : 0 < B) (hCk : 0 < Ck) (hBP : B ≤ P) (c₂ : ℝ)
    (hm1 : 1 ≤ mF u) (hmk : mF u ≤ k) (hq1 : 1 ≤ qF u)
    (hqlow : (q₀ : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2 ≤ (qF u : ℝ))
    (hcop : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' → ¬ (pr v v').1 ∣ q₀ ∧ ¬ (pr v v').2 ∣ q₀)
    (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2 ∧
      Work.BMF.IntegralOn 1 (Work.BMF.dil (((pr v v').2 : ℕ) : ℝ) (γ v) -
        Work.BMF.dil (((pr v v').1 : ℕ) : ℝ) (γ v')))
    (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
      |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 200 * L)
    (hfib : ∀ y : ℝ, ((T.filter (fun v ↦ pos v = y)).card : ℝ) ≤ (K : ℝ))
    (hsep : ∀ v ∈ T, ∀ v' ∈ T, pos v ≠ pos v' → 500 * L ≤ |pos v - pos v'|)
    (hposD : ∀ v ∈ T, D ≤ pos v)
    (hqFcop : ∀ p : ℕ, p.Prime → ¬ p ∣ k.factorial → ¬ p ∣ q₀ → ¬ p ∣ qF u)
    (hqFdvd : ∀ A B : ℕ, Work.BMF.IntegralOn 1
      (Work.BMF.dil (A : ℝ) (γ u) - Work.BMF.dil (B : ℝ) (γ u)) →
      (qF u : ℤ) ∣ ((A : ℤ) ^ (mF u) - (B : ℤ) ^ (mF u)))
    (hN4S : ∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (P' N' C₀ : ℝ) (q : ℕ),
        B ≤ P' → 3 ≤ N' → N' ≤ P' ^ (ℓ - 1) → 1 / Real.log P' ≤ C₀ → 1 ≤ q →
        step6Scard ℓ P' N' C₀ m q ≤ G * C₀ * (P' / Real.log P') ^ (2 * ℓ) / N' *
          ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) + 1 / Real.log N'))
    (hCklem : ∀ (m q : ℕ), 1 ≤ m → m ≤ k → 1 ≤ q →
      ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) ≤ Ck / Real.sqrt (q : ℝ)))
    (hN3 : 3 ≤ N) (hNℓ : N ≤ P ^ (ℓ - 1)) (hPlog : 1 ≤ Real.log P) :
    (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, by omega⟩ = u)).card : ℝ) ≤
      (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
        (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
          (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) := by
  have hcount := step6v2_count_u (Adj := Adj) (T := T) (pos := pos) (pr := pr) (γ := γ) (ℓ := ℓ)
    hℓ2 (P := P) (N := N) (L := L) (D := D) hD hL hP hN hLDN k hk hPfac q₀ mF qF K u hu
    hcop hedge hgeo hfib hsep hposD hqFcop hqFdvd
  have hlogC : 1 / Real.log P ≤ step6C0v2 ℓ := by
    have h1 : 1 / Real.log P ≤ 1 := by
      rw [one_div]
      exact inv_le_one_of_one_le₀ (by linarith [hPlog])
    linarith [h1, one_le_step6C0v2 ℓ]
  have hSbound := hN4S (mF u) hm1 hmk P N (step6C0v2 ℓ) (qF u) hBP hN3 hNℓ hlogC hq1
  have hCk' := hCklem (mF u) (qF u) hm1 hmk hq1
  have hsqrt := step6v2_inv_sqrt_le k hk hq₀ hq1 hqlow
  have hmid : (((2 * mF u : ℕ) : ℝ) ^ (qF u).primeFactors.card / ((qF u).totient : ℝ))
      ≤ Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := by
    have h' : Ck / Real.sqrt (qF u : ℝ)
        ≤ Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := by
      rw [div_eq_mul_one_div]
      have h2 := mul_le_mul_of_nonneg_left hsqrt (le_of_lt hCk)
      calc Ck * (1 / Real.sqrt (qF u : ℝ))
          ≤ Ck * ((k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ))))) := h2
        _ = Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := by ring
    linarith [hCk', h']
  have hSunif : step6Scard ℓ P N (step6C0v2 ℓ) (mF u) (qF u) ≤
      G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
        (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := by
    refine le_trans hSbound ?_
    have hstep : ((((2 * mF u : ℕ) : ℝ) ^ (qF u).primeFactors.card / ((qF u).totient : ℝ))
        + 1 / Real.log N)
        ≤ Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N := by
      linarith [hmid]
    refine mul_le_mul_of_nonneg_left hstep ?_
    have h0 : 0 < step6C0v2 ℓ := step6C0v2_pos ℓ
    positivity
  calc (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, by omega⟩ = u)).card : ℝ)
      ≤ (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * step6Scard ℓ P N (step6C0v2 ℓ) (mF u) (qF u) := hcount
    _ ≤ (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
          (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
            (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) :=
        mul_le_mul_of_nonneg_left hSunif (by positivity)

theorem step6_q0_bound_v2 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ Abound : ℕ → ℝ → ℝ → ℝ → ℝ,
      (∀ ℓ c₂ G Ck, 0 < Abound ℓ c₂ G Ck) ∧
      ∀ (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (hℓeven : ∃ m : ℕ, ℓ = 2 * m)
        {V : Type} [Fintype V] [DecidableEq V]
        (Adj : V → V → Prop) [DecidableRel Adj] (hsym : ∀ a b, Adj a b ↔ Adj b a)
        (T : Finset V) (pos : V → ℝ) (pr : V → V → ℕ × ℕ)
        (γ : V → Polynomial ℝ) (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
        (P N L D c_E c₂ G B Ck : ℝ) (K : ℕ)
        (hG : 0 < G) (hB : 0 < B) (hCk : 0 < Ck) (hBP : B ≤ P)
        (hN4 : ∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (P' N' C₀ : ℝ) (q : ℕ),
          B ≤ P' → 3 ≤ N' → N' ≤ P' ^ (ℓ - 1) → 1 / Real.log P' ≤ C₀ → 1 ≤ q →
          ((((Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P' (2 * P')).filter
                (fun p ↦ ¬ p ∣ q)) ×ˢ
            (Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P' (2 * P')).filter
                (fun p ↦ ¬ p ∣ q))).filter
            (fun v ↦ |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P' ^ ℓ / N' ∧
              (∏ i, v.2 i) ^ m ≡ (∏ i, v.1 i) ^ m [MOD q])).card : ℝ)
          ≤ G * C₀ * (P' / Real.log P') ^ (2 * ℓ) / N' *
            ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) + 1 / Real.log N'))
        (hCklem : ∀ (m q : ℕ), 1 ≤ m → m ≤ k → 1 ≤ q →
          ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) ≤ Ck / Real.sqrt (q : ℝ)))
        (hdeg : ∀ v ∈ T, (γ v).natDegree ≤ k)
        (hint : ∀ v ∈ T, Work.BMF.IntegralOn (q₀ : ℝ) (γ v))
        (hmin : ∀ v ∈ T, ∀ r : ℕ, 1 ≤ r → Work.BMF.IntegralOn (r : ℝ) (γ v) → q₀ ≤ r)
        (hcop : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' → ¬ (pr v v').1 ∣ q₀ ∧ ¬ (pr v v').2 ∣ q₀)
        (hedge : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
          Work.BMF.IsPrimeIn P (2 * P) (pr v v').1 ∧ Work.BMF.IsPrimeIn P (2 * P) (pr v v').2 ∧
          Work.BMF.IntegralOn 1 (Work.BMF.dil (((pr v v').2 : ℕ) : ℝ) (γ v) -
            Work.BMF.dil (((pr v v').1 : ℕ) : ℝ) (γ v')))
        (hgeo : ∀ v ∈ T, ∀ v' ∈ T, Adj v v' →
          |pos v - (((pr v v').2 : ℕ) : ℝ) / (((pr v v').1 : ℕ) : ℝ) * pos v'| ≤ 200 * L)
        (hfib : ∀ y : ℝ, ((T.filter (fun v ↦ pos v = y)).card : ℝ) ≤ (K : ℝ))
        (hsep : ∀ v ∈ T, ∀ v' ∈ T, pos v ≠ pos v' → 500 * L ≤ |pos v - pos v'|)
        (hposD : ∀ v ∈ T, D ≤ pos v)
        (hD : 0 < D) (hL : 0 < L) (hP1 : 1 ≤ P) (hPlog : 1 ≤ Real.log P)
        (hPfac : (k.factorial : ℝ) < P)
        (hLDN : N * L ≤ 10 * D) (hN3 : 3 ≤ N) (hNℓ : N ≤ P ^ (ℓ - 1))
        (hd : (P / Real.log P) ^ ℓ ≥ N ^ (2 + ε))
        (hcE : 0 < c_E) (hc2 : 0 < c₂)
        (hTlow : c_E * N ≤ (T.card : ℝ)) (hThigh : (T.card : ℝ) ≤ c₂ * N)
        (hedges : c_E * (P / Real.log P) ^ 2 * N ≤
          ((Finset.univ.filter (fun p : V × V ↦ p.1 ∈ T ∧ p.2 ∈ T ∧ Adj p.1 p.2)).card : ℝ)) ,
        (c_E / c₂) ^ ℓ ≤
          Abound ℓ c₂ G Ck * (K : ℝ) ^ ℓ * ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := by
  have hkfact : (1 : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  refine ⟨fun ℓ c₂ G Ck =>
    (|c₂| + 1) * (|G| + 1) * step6Wv2 ℓ * (|Ck| * (k.factorial : ℝ) + 1) + 1, ?_, ?_⟩
  · intro ℓ c₂ G Ck
    have h1 : (0 : ℝ) < |c₂| + 1 := by positivity
    have h2 : (0 : ℝ) < |G| + 1 := by positivity
    have h3 : (0 : ℝ) < |Ck| * (k.factorial : ℝ) + 1 := by positivity
    have h4 : (0 : ℝ) < step6Wv2 ℓ := step6Wv2_pos ℓ
    positivity
  · intro ℓ hℓ2 hℓeven V _instV _instV' Adj _instAdj hsym T pos pr γ q₀ hq₀ P N L D c_E c₂ G B Ck K
    intro hG hB hCk hBP hN4 hCklem hdeg hint hmin hcop hedge hgeo hfib hsep hposD hD hL hP1 hPlog
      hPfac hLDN hN3 hNℓ hd hcE hc2 hTlow hThigh hedges
    have hℓ0 : 0 < ℓ := by omega
    have hNpos : 0 < N := by linarith
    have hPpos : 0 < P := by linarith
    have hPgt1 : 1 < P := lt_of_le_of_lt hkfact hPfac
    have hlogPpos : 0 < Real.log P := Real.log_pos hPgt1
    have hXpos : 0 < (P / Real.log P) ^ 2 := pow_pos (div_pos hPpos hlogPpos) _
    have hXnn : 0 ≤ (P / Real.log P) ^ 2 := le_of_lt hXpos
    have hC0nn : 0 ≤ step6C0v2 ℓ := step6C0v2_nonneg ℓ
    have hC0pos : 0 < step6C0v2 ℓ := step6C0v2_pos ℓ
    have hKnn : 0 ≤ (K : ℝ) ^ ℓ := by positivity
    have hfacnn : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
    have hq0nn : 0 ≤ (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) := Real.rpow_nonneg (by positivity) _
    have hlogN : (0 : ℝ) < Real.log N := Real.log_pos (by linarith)
    have hBnn : 0 ≤ (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N :=
      add_nonneg hq0nn (by positivity)
    -- per-vertex data
    obtain ⟨mF, qF, hm1, hmk, hq1, hqlow, hqcop, hqdvd⟩ :=
      step6v2_hq0arith k hk T γ q₀ hq₀ hdeg hint hmin
    -- restatement of `hN4` through `step6Scard`
    have hN4S : ∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (P' N' C₀ : ℝ) (q : ℕ),
        B ≤ P' → 3 ≤ N' → N' ≤ P' ^ (ℓ - 1) → 1 / Real.log P' ≤ C₀ → 1 ≤ q →
        step6Scard ℓ P' N' C₀ m q ≤ G * C₀ * (P' / Real.log P') ^ (2 * ℓ) / N' *
          ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) + 1 / Real.log N') := by
      intro m hm1' hmk' P' N' C₀ q h1 h2 h3 h4 h5
      rw [step6Scard]
      exact hN4 m hm1' hmk' P' N' C₀ q h1 h2 h3 h4 h5
    -- the per-start bound
    have hper : ∀ u ∈ T, (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, hℓ0⟩ = u)).card : ℝ) ≤
        (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
          (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
            (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) := by
      intro u hu
      exact step6v2_per_u (Adj := Adj) (T := T) (pos := pos) (pr := pr) (γ := γ) (ℓ := ℓ) hℓ2
        (P := P) (N := N) (L := L) (D := D) hD hL hP1 hNpos hLDN k hk hPfac q₀ hq₀ mF qF K u hu
        G B Ck hG hB hCk hBP c₂ (hm1 u hu) (hmk u hu) (hq1 u hu) (hqlow u hu) hcop hedge hgeo
        hfib hsep hposD (hqcop u hu) (hqdvd u hu) hN4S hCklem hN3 hNℓ hPlog
    -- split the walk count by the starting vertex
    have hmapsT : Set.MapsTo (fun w : Fin ℓ → V => w ⟨0, hℓ0⟩) ↑(step6Walks Adj T ℓ) ↑T :=
      fun w hw => (mem_step6Walks.mp hw).1 ⟨0, hℓ0⟩
    have hsplit : ((step6Walks Adj T ℓ).card : ℝ)
        = ∑ u ∈ T, (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, hℓ0⟩ = u)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hmapsT, Nat.cast_sum]
    -- upper bound, with the window factor `(P/log P)^{2ℓ}` written as `((P/log P)^2)^ℓ`
    have hup0 : ((step6Walks Adj T ℓ).card : ℝ)
        ≤ (K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
          (P / Real.log P) ^ (2 * ℓ) *
          ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := by
      rw [hsplit]
      have hstep1 : ∑ u ∈ T, (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, hℓ0⟩ = u)).card : ℝ)
          ≤ (T.card : ℝ) * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
              (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
                (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) := by
        calc ∑ u ∈ T, (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, hℓ0⟩ = u)).card : ℝ)
            ≤ ∑ _u ∈ T, ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
                (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
                  (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) :=
              Finset.sum_le_sum hper
          _ = (T.card : ℝ) * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
                (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
                  (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hXnn' : 0 ≤ (P / Real.log P) ^ (2 * ℓ) :=
        pow_nonneg (div_nonneg (le_of_lt hPpos) (le_of_lt hlogPpos)) _
      have hbrnn : 0 ≤ Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N :=
        add_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCk) hfacnn) hq0nn) (by positivity)
      have hpos1 : 0 ≤ (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * (G * step6C0v2 ℓ *
            (P / Real.log P) ^ (2 * ℓ) *
            (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) := by
        have h0 : 0 < step6C0v2 ℓ := hC0pos
        positivity
      have hCkf : 0 ≤ Ck * (k.factorial : ℝ) := mul_nonneg (le_of_lt hCk) hfacnn
      have hbr : Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N
          ≤ (Ck * (k.factorial : ℝ) + 1) *
            ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := by
        have hL : 0 ≤ 1 / Real.log N := by positivity
        have hCL : 0 ≤ Ck * (k.factorial : ℝ) * (1 / Real.log N) := mul_nonneg hCkf hL
        nlinarith [hq0nn, hL, hCkf, hCL]
      have hbr' : (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * (G * step6C0v2 ℓ *
            (P / Real.log P) ^ (2 * ℓ) *
            (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))
          ≤ (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * (G * step6C0v2 ℓ *
            (P / Real.log P) ^ (2 * ℓ) *
            ((Ck * (k.factorial : ℝ) + 1) *
              ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) := by
        gcongr
      have hfact : (T.card : ℝ) * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
            (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
              (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)))
          = ((T.card : ℝ) / N) * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
            (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) *
              (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) := by
        field_simp
      have hTdiv : (T.card : ℝ) / N ≤ c₂ := by
        rw [div_le_iff₀ hNpos]
        linarith [hThigh]
      have hpos2 : 0 ≤ (4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * (G * step6C0v2 ℓ *
          (P / Real.log P) ^ (2 * ℓ)) := by
        have h0 : 0 < step6C0v2 ℓ := hC0pos
        positivity
      calc ∑ u ∈ T, (((step6Walks Adj T ℓ).filter (fun w => w ⟨0, hℓ0⟩ = u)).card : ℝ)
          ≤ (T.card : ℝ) * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ *
              (G * step6C0v2 ℓ * (P / Real.log P) ^ (2 * ℓ) / N *
                (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) := hstep1
        _ = ((T.card : ℝ) / N) * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * (G * step6C0v2 ℓ *
              (P / Real.log P) ^ (2 * ℓ) *
              (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) := hfact
        _ ≤ c₂ * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * (G * step6C0v2 ℓ *
              (P / Real.log P) ^ (2 * ℓ) *
              (Ck * (k.factorial : ℝ) * (q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N))) :=
            mul_le_mul_of_nonneg_right hTdiv hpos1
        _ ≤ c₂ * ((4 : ℝ) ^ ℓ * (K : ℝ) ^ ℓ * (G * step6C0v2 ℓ *
              (P / Real.log P) ^ (2 * ℓ) *
              ((Ck * (k.factorial : ℝ) + 1) *
                ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)))) :=
            mul_le_mul_of_nonneg_left hbr' (le_of_lt hc2)
        _ = (K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
              (P / Real.log P) ^ (2 * ℓ) *
              ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := by
            rw [step6Wv2]
            ring
    have hup : ((step6Walks Adj T ℓ).card : ℝ)
        ≤ ((K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
          ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) * ((P / Real.log P) ^ 2) ^ ℓ := by
      have h2 : (P / Real.log P) ^ (2 * ℓ) = ((P / Real.log P) ^ 2) ^ ℓ := pow_mul _ _ _
      have h := hup0
      rw [h2] at h
      calc ((step6Walks Adj T ℓ).card : ℝ)
          ≤ (K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
              ((P / Real.log P) ^ 2) ^ ℓ *
              ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := h
        _ = ((K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
              ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) *
              ((P / Real.log P) ^ 2) ^ ℓ := by ring
    -- lower bound
    have hlow0 : ((c_E / c₂) * (P / Real.log P) ^ 2) ^ ℓ
        ≤ ((step6Walks Adj T ℓ).card : ℝ) :=
      step6v2_walk_lower (Adj := Adj) (T := T) (ℓ := ℓ) hsym hℓ2 hℓeven (c_E := c_E) (c₂ := c₂)
        (P := P) (N := N) hcE hc2 hP1 hNpos hTlow hThigh hedges
    have hlow : (c_E / c₂) ^ ℓ * ((P / Real.log P) ^ 2) ^ ℓ
        ≤ ((step6Walks Adj T ℓ).card : ℝ) := by
      rwa [mul_pow] at hlow0
    -- combine
    have hAb : c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)
        ≤ (|c₂| + 1) * (|G| + 1) * step6Wv2 ℓ * (|Ck| * (k.factorial : ℝ) + 1) + 1 := by
      have h1 : |c₂| = c₂ := abs_of_pos hc2
      have h2 : |G| = G := abs_of_pos hG
      have h3 : |Ck| = Ck := abs_of_pos hCk
      rw [h1, h2, h3]
      have hW : 0 < step6Wv2 ℓ := step6Wv2_pos ℓ
      have hCkf : 0 ≤ Ck * (k.factorial : ℝ) := mul_nonneg (le_of_lt hCk) hfacnn
      nlinarith [mul_nonneg (le_of_lt hc2) (le_of_lt hG), mul_nonneg hfacnn zero_le_one,
        mul_nonneg (le_of_lt hW) (add_nonneg hCkf zero_le_one)]
    have hstepA : (c_E / c₂) ^ ℓ * ((P / Real.log P) ^ 2) ^ ℓ
        ≤ ((K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
            ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) * ((P / Real.log P) ^ 2) ^ ℓ :=
      le_trans hlow hup
    have hdiv : (c_E / c₂) ^ ℓ
        ≤ (K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
            ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) :=
      le_of_mul_le_mul_right hstepA (pow_pos hXpos ℓ)
    have hstepB : (K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
          ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)
        ≤ ((|c₂| + 1) * (|G| + 1) * step6Wv2 ℓ * (|Ck| * (k.factorial : ℝ) + 1) + 1) *
          (K : ℝ) ^ ℓ * ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := by
      have h := mul_le_mul_of_nonneg_right hAb hBnn
      have hKf : 0 ≤ (K : ℝ) ^ ℓ := hKnn
      calc (K : ℝ) ^ ℓ * (c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
            ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)
          = (K : ℝ) ^ ℓ * ((c₂ * G * step6Wv2 ℓ * (Ck * (k.factorial : ℝ) + 1)) *
              ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) := by ring
        _ ≤ (K : ℝ) ^ ℓ * (((|c₂| + 1) * (|G| + 1) * step6Wv2 ℓ *
              (|Ck| * (k.factorial : ℝ) + 1) + 1) *
              ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N)) :=
            mul_le_mul_of_nonneg_left h hKf
        _ = ((|c₂| + 1) * (|G| + 1) * step6Wv2 ℓ * (|Ck| * (k.factorial : ℝ) + 1) + 1) *
            (K : ℝ) ^ ℓ * ((q₀ : ℝ) ^ (-(1 / (2 * (k : ℝ)))) + 1 / Real.log N) := by ring
    exact le_trans hdiv hstepB


end Work.N8
