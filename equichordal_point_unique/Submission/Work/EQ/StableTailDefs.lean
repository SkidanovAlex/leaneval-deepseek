import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germC_facts

/-! # The tail index of a chain and its elementary properties

Vocabulary for `Work.EQ.stable_tail_uniform`.  A chain datum `q` is a *chain*
(`IsChain a h q`) when its forward tail is the principal stable leaf `n ↦ germC a h (λⁿ ψ₁ q)`
from some index on.  `TailP a h q N` records that this holds from `N`, and `tailIdx a h q` is
the least such index.

The lemmas here are elementary: monotonicity of `TailP`, the characterisation of `tailIdx`,
invariance of `IsChain`/`H0` under the shift and its inverse `hInv`, and the behaviour of
`tailIdx` under the shift: `tailIdx (σ q) = tailIdx q - 1` and `tailIdx (σ⁻¹ q) = tailIdx q + 1`
for positive `tailIdx`.
-/

namespace Work.EQ

open Filter _root_.Topology
open Complex
open Classical

noncomputable section

/-! ## The principal tail -/

/-- `TailP a h q N`: from the index `N` on, the chain datum `q` follows the principal stable
leaf, `q.1 n = germC a h (λⁿ ψ₁ q)`. -/
def TailP (a : ℝ) (h : ℂ → ℂ) (q : ChainData) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q.2.1)

lemma TailP_mono {a : ℝ} {h : ℂ → ℂ} {q : ChainData} {N N' : ℕ} (hN : TailP a h q N)
    (hNN : N ≤ N') : TailP a h q N' := fun n hn => hN n (le_trans hNN hn)

lemma tailP_of_isChain {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : IsChain a h q) :
    ∃ N : ℕ, TailP a h q N := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hq.2.2.2.1
  exact ⟨N, fun n hn => hN n hn⟩

/-- The tail index: the least index from which the forward tail is the principal leaf.  For a
non-chain we set it to `0`. -/
noncomputable def tailIdx (a : ℝ) (h : ℂ → ℂ) (q : ChainData) : ℕ :=
  if hq : ∃ N : ℕ, TailP a h q N then Nat.find hq else 0

lemma tailIdx_eq_find {a : ℝ} {h : ℂ → ℂ} {q : ChainData}
    (hq : ∃ N : ℕ, TailP a h q N) : tailIdx a h q = Nat.find hq := by
  rw [tailIdx, dif_pos hq]

lemma TailP_tailIdx {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : ∃ N : ℕ, TailP a h q N) :
    TailP a h q (tailIdx a h q) := by
  rw [tailIdx_eq_find hq]
  exact Nat.find_spec hq

lemma tailIdx_le {a : ℝ} {h : ℂ → ℂ} {q : ChainData} {N : ℕ}
    (hq : ∃ N' : ℕ, TailP a h q N') (hN : TailP a h q N) : tailIdx a h q ≤ N := by
  rw [tailIdx_eq_find hq]
  exact Nat.find_min' hq hN

lemma tailIdx_le_iff {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : ∃ N : ℕ, TailP a h q N)
    {N : ℕ} : tailIdx a h q ≤ N ↔ TailP a h q N :=
  ⟨fun h => TailP_mono (TailP_tailIdx hq) h, fun h => tailIdx_le hq h⟩

/-! ## Chains from `H0` -/

/-- Every point of `H0` is a chain. -/
lemma isChain_of_mem_H0 {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) :
    IsChain a h q := by
  obtain ⟨ε, hε, f, hcont, hf0, hf⟩ := hq
  have hmem : q.2.1 ∈ Metric.ball q.2.1 ε := by
    rw [Metric.mem_ball, dist_self]; exact hε
  rw [← hf0]
  exact (hf q.2.1 hmem).1

lemma TailP_of_isChain {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : IsChain a h q) :
    TailP a h q (tailIdx a h q) := TailP_tailIdx (tailP_of_isChain hq)

lemma tailIdx_le_of_isChain {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : IsChain a h q) {N : ℕ}
    (hN : TailP a h q N) : tailIdx a h q ≤ N := tailIdx_le (tailP_of_isChain hq) hN

/-! ## The shift and its inverse -/

/-- The inverse of the shift `hShift a` on chain data: `Pₙ ↦ Pₙ₋₁`, `ψ₁ ↦ ψ₁/λ`, `ψ₂ ↦ λψ₂`. -/
noncomputable def hInv (a : ℝ) (q : ChainData) : ChainData :=
  (fun n => q.1 (n - 1), q.2.1 / (eqLam a : ℂ), (eqLam a : ℂ) * q.2.2)

@[simp] lemma hShift_fst (a : ℝ) (q : ChainData) (n : ℤ) : (hShift a q).1 n = q.1 (n + 1) := rfl
@[simp] lemma hShift_psi1 (a : ℝ) (q : ChainData) :
    (hShift a q).2.1 = (eqLam a : ℂ) * q.2.1 := rfl
@[simp] lemma hShift_psi2 (a : ℝ) (q : ChainData) :
    (hShift a q).2.2 = q.2.2 / (eqLam a : ℂ) := rfl
@[simp] lemma hInv_fst (a : ℝ) (q : ChainData) (n : ℤ) : (hInv a q).1 n = q.1 (n - 1) := rfl
@[simp] lemma hInv_psi1 (a : ℝ) (q : ChainData) : (hInv a q).2.1 = q.2.1 / (eqLam a : ℂ) := rfl
@[simp] lemma hInv_psi2 (a : ℝ) (q : ChainData) : (hInv a q).2.2 = (eqLam a : ℂ) * q.2.2 := rfl

lemma eqLamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : (eqLam a : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj, eqLam]
  exact ne_of_gt (div_pos (by linarith) (by linarith))

lemma hInv_hShift {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) :
    hInv a (hShift a q) = q := by
  have hl := eqLamC_ne_zero ha0 ha1
  refine Prod.ext ?_ ?_
  · funext n
    simp only [hInv, hShift]
    rw [show n - 1 + 1 = n by ring]
  · refine Prod.ext ?_ ?_
    · simp only [hInv, hShift]
      rw [mul_div_cancel_left₀ q.2.1 hl]
    · simp only [hInv, hShift]
      field_simp

lemma hShift_hInv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) :
    hShift a (hInv a q) = q := by
  have hl := eqLamC_ne_zero ha0 ha1
  refine Prod.ext ?_ ?_
  · funext n
    simp only [hInv, hShift]
    rw [show n + 1 - 1 = n by ring]
  · refine Prod.ext ?_ ?_
    · simp only [hInv, hShift]
      rw [mul_div_cancel₀ q.2.1 hl]
    · simp only [hInv, hShift]
      rw [mul_div_cancel_left₀ q.2.2 hl]

/-! ## `TailP` under the inverse shift -/

lemma TailP_hInv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {q : ChainData} {N : ℕ}
    (hN : TailP a h q N) :
    TailP a h (hInv a q) (N + 1) := by
  intro n hn
  have hn1 : N ≤ n - 1 := by omega
  have h1 : q.1 ((n - 1 : ℕ) : ℤ) = germC a h ((eqLam a : ℂ) ^ (n - 1) * q.2.1) :=
    hN (n - 1) hn1
  show q.1 ((n : ℤ) - 1) = germC a h ((eqLam a : ℂ) ^ n * (q.2.1 / (eqLam a : ℂ)))
  have hidx : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
  rw [hidx, h1]
  congr 1
  rw [show n = (n - 1) + 1 by omega, pow_succ]
  have hl := eqLamC_ne_zero ha0 ha1
  field_simp
  rw [show n - 1 + 1 - 1 = n - 1 by omega, mul_comm]

lemma TailP_of_hInv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {q : ChainData} {N : ℕ}
    (hN : TailP a h (hInv a q) N) : TailP a h q (N - 1) := by
  intro n hn
  have hn1 : N ≤ n + 1 := by omega
  have h1 : q.1 ((n : ℤ) + 1 - 1) =
      germC a h ((eqLam a : ℂ) ^ (n + 1) * (q.2.1 / (eqLam a : ℂ))) := by
    have h2 : (hInv a q).1 (((n + 1 : ℕ)) : ℤ) =
        germC a h ((eqLam a : ℂ) ^ (n + 1) * (hInv a q).2.1) := hN (n + 1) hn1
    have hidx : (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [hidx] at h2
    simpa only [hInv_fst, hInv_psi1] using h2
  rw [show (n : ℤ) + 1 - 1 = n by ring] at h1
  rw [h1]
  congr 1
  rw [show n + 1 = n + 1 by rfl, pow_succ]
  have hl := eqLamC_ne_zero ha0 ha1
  field_simp

end

end Work.EQ
