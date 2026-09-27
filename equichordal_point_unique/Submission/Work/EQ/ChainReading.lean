import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_invParam_ge

/-! # Reading a chain of `⁰H` over an annulus

A chain `p` of `⁰H` whose forward tail is the stable germ `germC` from index `N` on and whose
backward tail is the unstable germ `ugermC` from index `-N` on has a *stable word* `ε` of length
`N` and an *unstable word* `η` of length `N` with

* `p 0 = fan a h ε (ψ₁ p)`, and
* `p (-N) = eqMirror (fan a h η (λ^N ψ₂ p))`.

This is the reading used in the compactness argument of Rychlik's Theorem 8; it is shared by
`Submission.Work.EQ.exists_compact_regular_cycle` and
`Submission.Work.EQ.compact_mod_punctures_of_tails` (neither of which may import the other).
-/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- **A chain is a fan value, with a word of the prescribed length.** -/
theorem chain_eq_fan_len {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} :
    ∀ (N : ℕ) (p : ChainData), IsChain a h p →
      (∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1)) →
      ∃ ε : List Bool, ε.length = N ∧ p.1 0 = fan a h ε p.2.1 := by
  intro N
  induction N with
  | zero =>
    intro p hp htail
    exact ⟨[], rfl, by simpa [fan] using htail 0 le_rfl⟩
  | succ N ih =>
    intro p hp htail
    have hp' : IsChain a h (shiftZ a 1 p) := isChain_shiftZ ha0 ha1 hp 1
    have htail' : ∀ n : ℕ, N ≤ n →
        (shiftZ a 1 p).1 (n : ℤ) =
          germC a h (((eqLam a : ℝ) : ℂ) ^ n * (shiftZ a 1 p).2.1) := by
      intro n hn
      rw [shiftZ_fst, shiftZ_psi1, zpow_one,
        show p.1 ((n : ℤ) + 1) = germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * p.2.1)
          from htail (n + 1) (by omega)]
      congr 1
      rw [pow_succ]; ring
    obtain ⟨ε, hlen, hε⟩ := ih (shiftZ a 1 p) hp' htail'
    have hfst : p.1 1 = fan a h ε (((eqLam a : ℝ) : ℂ) * p.2.1) := by
      have h1 : (shiftZ a 1 p).1 0 = p.1 1 := by simp [shiftZ]
      have h2 : (shiftZ a 1 p).2.1 = ((eqLam a : ℝ) : ℂ) * p.2.1 := by simp [shiftZ]
      rw [← h1, hε, h2]
    have hreg0 : RegPair a (p.1 0) (p.1 1) := by
      simpa using hp.1 0
    rcases H0_invParam_ge_exists_invBranch hreg0.1 hreg0.2.2 with h | h
    · refine ⟨true :: ε, by simp [hlen], ?_⟩
      rw [show p.1 0 = invBranch a true (p.1 1) from h, hfst]
      rfl
    · refine ⟨false :: ε, by simp [hlen], ?_⟩
      rw [show p.1 0 = invBranch a false (p.1 1) from h, hfst]
      rfl

/-- `eqMirror` is an involution. -/
@[simp] theorem eqMirror_involutive (P : ℂ × ℂ) : eqMirror (eqMirror P) = P := by
  simp [eqMirror]

/-- **The unstable end of a chain is a mirrored fan value.** -/
theorem chain_read_bwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {p : ChainData} (hp : IsChain a h p)
    (htail : ∀ n : ℕ, N ≤ n → p.1 (-(n : ℤ)) =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    ∃ η : List Bool, p.1 (-(N : ℤ)) =
      eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * p.2.2)) := by
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj, eqLam]
    exact div_ne_zero (by linarith) (by linarith)
  set q : ChainData := mirrorChain (shiftZ a (-(N : ℤ)) p) with hqdef
  have hq1 : q.2.1 = ((eqLam a : ℝ) : ℂ) ^ N * p.2.2 := by
    rw [hqdef]; simp only [mirrorChain_psi1, shiftZ_psi2]
    rw [div_eq_mul_inv, zpow_neg, inv_inv, zpow_natCast, mul_comm]
  have hqchain : IsChain a h q := isChain_mirrorChain (isChain_shiftZ ha0 ha1 hp (-(N : ℤ)))
  have hqtail : ∀ n : ℕ, 0 ≤ n →
      q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1) := by
    intro n _
    have h1 : q.1 (n : ℤ) = eqMirror (p.1 (-(((n + N : ℕ)) : ℤ))) := by
      rw [hqdef, mirrorChain_fst, shiftZ_fst]
      congr 1
      push_cast
      ring
    rw [h1, show p.1 (-(((n + N : ℕ)) : ℤ)) =
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ (n + N) * p.2.2)
      from htail (n + N) (by omega), hq1, ugermC, eqMirror_involutive]
    congr 1
    rw [pow_add]; ring
  obtain ⟨η, -, hη⟩ := chain_eq_fan_len ha0 ha1 0 q hqchain hqtail
  refine ⟨η, ?_⟩
  have hq0 : q.1 0 = eqMirror (p.1 (-(N : ℤ))) := by
    rw [hqdef, mirrorChain_fst]
    norm_num
  rw [hη, hq1] at hq0
  rw [hq0, eqMirror_involutive]

/-- **The stable and unstable words of a chain over the annulus.** -/
theorem chain_read {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ} {p : ChainData}
    (hp : IsChain a h p)
    (hfwd : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1))
    (hbwd : ∀ n : ℕ, N ≤ n → p.1 (-(n : ℤ)) =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    (∃ ε : List Bool, ε.length = N ∧ p.1 0 = fan a h ε p.2.1) ∧
      ∃ η : List Bool, p.1 (-(N : ℤ)) =
        eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * p.2.2)) :=
  ⟨chain_eq_fan_len ha0 ha1 N p hp hfwd, chain_read_bwd ha0 ha1 hp hbwd⟩

/-- **The unstable end of a chain is a mirrored fan value, with a word of prescribed length.** -/
theorem chain_read_bwd_len {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {p : ChainData} (hp : IsChain a h p)
    (htail : ∀ n : ℕ, N ≤ n → p.1 (-(n : ℤ)) =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    ∃ η : List Bool, η.length = N ∧ p.1 (-(N : ℤ)) =
      eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * p.2.2)) := by
  set q : ChainData := mirrorChain (shiftZ a (-(N : ℤ)) p) with hqdef
  have hq1 : q.2.1 = ((eqLam a : ℝ) : ℂ) ^ N * p.2.2 := by
    rw [hqdef]; simp only [mirrorChain_psi1, shiftZ_psi2]
    rw [div_eq_mul_inv, zpow_neg, inv_inv, zpow_natCast, mul_comm]
  have hqchain : IsChain a h q := isChain_mirrorChain (isChain_shiftZ ha0 ha1 hp (-(N : ℤ)))
  have hqtail : ∀ n : ℕ, N ≤ n →
      q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1) := by
    intro n hn
    have h1 : q.1 (n : ℤ) = eqMirror (p.1 (-(((n + N : ℕ)) : ℤ))) := by
      rw [hqdef, mirrorChain_fst, shiftZ_fst]
      congr 1
      push_cast
      ring
    rw [h1, show p.1 (-(((n + N : ℕ)) : ℤ)) =
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ (n + N) * p.2.2)
      from htail (n + N) (by omega), hq1, ugermC, eqMirror_involutive]
    congr 1
    rw [pow_add]; ring
  obtain ⟨η, hlen, hη⟩ := chain_eq_fan_len ha0 ha1 N q hqchain hqtail
  refine ⟨η, hlen, ?_⟩
  have hq0 : q.1 0 = eqMirror (p.1 (-(N : ℤ))) := by
    rw [hqdef, mirrorChain_fst]
    norm_num
  rw [hη, hq1] at hq0
  rw [hq0, eqMirror_involutive]

/-- **The reading of a chain whose tails are the germs from depth `N` on.** -/
theorem reading_of_tailBounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {q : ChainData} (hq : IsChain a h q)
    (hfwd : ∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1))
    (hbwd : ∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h
      (((eqLam a : ℝ) : ℂ) ^ n * q.2.2)) :
    ∃ e : List Bool × List Bool, e.1.length = N ∧ e.2.length = N ∧
      q.1 0 = fan a h e.1 q.2.1 ∧
      q.1 (-(N : ℤ)) = eqMirror (fan a h e.2 (((eqLam a : ℝ) : ℂ) ^ N * q.2.2)) := by
  obtain ⟨ε, hlen, hval⟩ := chain_eq_fan_len ha0 ha1 N q hq hfwd
  obtain ⟨η, hlen', hval'⟩ := chain_read_bwd_len ha0 ha1 hq hbwd
  exact ⟨(ε, η), hlen, hlen', hval, hval'⟩


end

end Work.EQ
