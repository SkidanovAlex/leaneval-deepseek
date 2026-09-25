import Mathlib
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF

/-!
# Unboundedness of the colossally-abundant family `N_ε` (Nicolas (4.11))

For a prime `p` and a real parameter `ε > 0` write

  μ(p,ε) := log((p^{1+ε} − 1) / (p^{1+ε} − p)) / log p   (the (4.11) exponent)
  a(p,ε) := ⌊μ(p,ε)⌋₊ ,   N_ε := ∏_{p prime, p < bound(ε)} p^{a(p,ε)}

with `bound(ε) = ⌈exp(2/ε)⌉ + 2` (a finite truncation of the infinite CA product).

`ca_Neps_unbounded` records that the family `N_ε` is unbounded as `ε → 0⁺`:
for every natural `B` there is `ε > 0` with `B ≤ N_ε`.

Strategy (Nicolas, Lemme 4 / 1983): pick `ε₀ := F(2, B+1)` where
`F(p,k) := log((p^{k+1}−1)/(p^{k+1}−p))/log p`.  Then `B+1 ≤ a(2,ε₀)` (because
`a(p,ε) ≥ k ⟺ ε ≤ F(p,k)`, and here `ε₀ = F(2,B+1)`), so the factor `2^{a(2,ε₀)}`
of `N_{ε₀}` already exceeds `2^{B+1} ≥ B`; all other prime factors are `≥ 1`.

The definitions below are module-private mirrors of the CA core used in the
companion development (`Submission/Work/NumberTheory/Robin/caCore.lean`); the
published statement is written out in full.
-/

open scoped BigOperators

namespace Commons.NumberTheory.Robin

noncomputable section

/-- `μ(p,ε) = log((p^{1+ε}−1)/(p^{1+ε}−p))/log p`, the (4.11)-exponent parameter. -/
private def caMu (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The exponent of the prime `p` in the CA number `N_ε`: `⌊μ(p,ε)⌋₊`. -/
private def caExp (p : ℕ) (ε : ℝ) : ℕ := ⌊caMu p ε⌋₊

/-- `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` for `k ≥ 1` (Nicolas (4.5)). -/
private def caF (p : ℕ) (k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)

/-- A finite bound for the support of `p ↦ caExp p ε` (see `caExp_eq_zero_of_ge_bound`):
`caEpsBound ε = ⌈exp(2/ε)⌉ + 2` for `ε > 0`. -/
private def caEpsBound (ε : ℝ) : ℕ := if 0 < ε then Nat.ceil (Real.exp (2 / ε)) + 2 else 3

/-- The (truncated) CA number `N_ε = ∏_{p < caEpsBound ε, p prime} p^{caExp p ε}` (Nicolas (4.11)). -/
private def Nε (ε : ℝ) : ℕ :=
  Finset.prod ((Finset.range (caEpsBound ε)).filter Nat.Prime) (fun p => p ^ caExp p ε)

/-- `F(p,k) > 0` for `p ≥ 2`, `k ≥ 1`. -/
private lemma caF_pos {p : ℕ} {k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) : 0 < caF p k := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  unfold caF
  have hpk1 : 1 < (p : ℝ) ^ (k + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : k + 1 ≠ 0)
  have hpk : 1 < (p : ℝ) ^ k := by
    have hle : (p : ℝ) ^ 1 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (le_of_lt hp1r) (by omega : 1 ≤ k)
    exact lt_of_lt_of_le (by simpa using hp1r) hle
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpm : (p : ℝ) < (p : ℝ) * (p : ℝ) ^ k := by
    simpa using (mul_lt_mul_of_pos_left hpk hp0)
  have hden : 0 < (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) := by
    have hpm' : (p : ℝ) * (p : ℝ) ^ k = (p : ℝ) ^ (k + 1 : ℕ) := by
      rw [pow_succ']
    linarith
  have hnum : 0 < (p : ℝ) ^ (k + 1 : ℕ) - 1 := by linarith
  have hquot : 1 < ((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)) := by
    rw [one_lt_div hden]
    linarith
  exact div_pos (Real.log_pos hquot) hlogp

/-- For every `ε > 0` the bound `⌈exp(2/ε)⌉ + 2` exceeds `2`, so the prime `2`
occurs among the truncated product's support. -/
private lemma two_lt_caEpsBound {ε : ℝ} (hε : 0 < ε) : (2 : ℕ) < caEpsBound ε := by
  unfold caEpsBound
  rw [if_pos hε]
  have h2div : 0 < 2 / ε := by positivity
  have hcex : (1 : ℕ) ≤ Nat.ceil (Real.exp (2 / ε)) := by
    have hexp : (1 : ℝ) ≤ Real.exp (2 / ε) := by
      have hle : Real.exp (0 : ℝ) ≤ Real.exp (2 / ε) := (Real.exp_le_exp).mpr (le_of_lt h2div)
      simpa using hle
    simpa using (Nat.ceil_mono hexp : Nat.ceil (1 : ℝ) ≤ Nat.ceil (Real.exp (2 / ε)))
  omega

/-- `N_ε ≥ 2^{a(2,ε)}` for every `ε > 0` (the factor `2` contributes, all other
prime-power factors are `≥ 1`). -/
private lemma Nε_ge_two_pow_caExp {ε : ℝ} (hε : 0 < ε) : 2 ^ caExp 2 ε ≤ Nε ε := by
  unfold Nε
  have hlt : (2 : ℕ) < caEpsBound ε := two_lt_caEpsBound hε
  have hmem : 2 ∈ (Finset.range (caEpsBound ε)).filter Nat.Prime := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, Nat.prime_two⟩
  let S : Finset ℕ := (Finset.range (caEpsBound ε)).filter Nat.Prime
  have hsplit : Finset.prod S (fun p => p ^ caExp p ε) =
      2 ^ caExp 2 ε * Finset.prod (S.erase 2) (fun p => p ^ caExp p ε) := by
    rw [← Finset.mul_prod_erase (s := S) (f := fun p => p ^ caExp p ε) (a := 2) hmem]
  have hrestpos : 0 < Finset.prod (S.erase 2) (fun p => p ^ caExp p ε) := by
    apply Finset.prod_pos
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
    exact pow_pos (Nat.Prime.pos hp') (caExp p ε)
  calc
    2 ^ caExp 2 ε ≤ 2 ^ caExp 2 ε * Finset.prod (S.erase 2) (fun p => p ^ caExp p ε) := by
      exact Nat.le_mul_of_pos_right _ hrestpos
    _ = Finset.prod S (fun p => p ^ caExp p ε) := by rw [hsplit]

/-- The CA numbers `N_ε` are unbounded as `ε → 0⁺`: for every `B : ℕ` there is
`ε > 0` with `B ≤ N_ε` (Nicolas 1983; Lagarias' criterion, CA-family lower bound). -/
theorem ca_Neps_unbounded (B : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      B ≤ Finset.prod ((Finset.range (if 0 < ε then Nat.ceil (Real.exp (2 / ε)) + 2 else 3)).filter Nat.Prime)
        (fun p : ℕ => p ^ Nat.floor
          (Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ))) := by
  let ε₀ : ℝ := caF 2 (B + 1)
  have hk1 : (1 : ℕ) ≤ B + 1 := by omega
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact caF_pos (p := 2) (k := B + 1) (by norm_num) hk1
  refine ⟨ε₀, hε₀, ?_⟩
  have hBpow : B ≤ 2 ^ (B + 1) := by
    have hm : B + 1 ≤ 2 ^ (B + 1) := by
      have hmain : ∀ m : ℕ, m ≤ 2 ^ m := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih =>
          by_cases hm0 : m = 0
          · subst m; norm_num
          · have h1 : 1 ≤ 2 ^ m := Nat.succ_le_of_lt (pow_pos (by norm_num : (0:ℕ) < 2) m)
            calc
              m + 1 ≤ 2 ^ m + 1 := by omega
              _ ≤ 2 ^ m + 2 ^ m := by omega
              _ = 2 ^ (m + 1) := by rw [pow_succ]; ring
      simpa using hmain (B + 1)
    omega
  have hExp : B + 1 ≤ caExp 2 ε₀ := by
    dsimp [ε₀]
    unfold caExp
    apply Nat.le_floor
    have hεF : 0 < caF 2 (B + 1) := caF_pos (p := 2) (k := B + 1) (by norm_num) hk1
    have hmu_iff := Commons.NumberTheory.Robin.caMu_ge_iff_caF (p := 2) (ε := caF 2 (B + 1))
      (k := B + 1) (by norm_num) hεF hk1
    exact (hmu_iff.mpr (by
      unfold caF
      exact le_rfl))
  have hpow : 2 ^ (B + 1) ≤ 2 ^ caExp 2 ε₀ :=
    pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hExp
  have hN : 2 ^ caExp 2 ε₀ ≤ Nε ε₀ := Nε_ge_two_pow_caExp hε₀
  have hChain : B ≤ Nε ε₀ := by
    calc
      B ≤ 2 ^ (B + 1) := hBpow
      _ ≤ 2 ^ caExp 2 ε₀ := hpow
      _ ≤ Nε ε₀ := hN
  have hEq : Nε ε₀ =
      Finset.prod ((Finset.range (if 0 < ε₀ then Nat.ceil (Real.exp (2 / ε₀)) + 2 else 3)).filter Nat.Prime)
        (fun p : ℕ => p ^ Nat.floor
          (Real.log (((p : ℝ) ^ (1 + ε₀) - 1) / (((p : ℝ) ^ (1 + ε₀)) - (p : ℝ))) / Real.log (p : ℝ))) := by
    unfold Nε caEpsBound caExp caMu
    rw [if_pos hε₀]
  exact le_trans hChain (le_of_eq hEq)

end
end Commons.NumberTheory.Robin
