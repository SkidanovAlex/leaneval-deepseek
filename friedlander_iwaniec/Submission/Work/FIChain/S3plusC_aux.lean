/-
# `Submission.Work.FIChain.S3plusC_aux` — auxiliary lemmas for the `λ⁺`-half
(`NOTES_S3plusC_route.md`)

Currently: the `(R′)`-information in the single-modulus form needed by the route.
-/
import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.S3plusC_lamPlus_identity

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `(R′)` for a single modulus: for `ζ ≤ ⌈x^{7/10}⌉` squarefree and every `m ≤ x`,
`τ(ζ)^5·|r̃(ζ,m)| ≤ Ã(x)(log x)^{-3}`. -/
theorem rtilde_single_le :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ m ζ : ℕ, m ≤ x →
      ζ ≤ ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ → Squarefree ζ →
      ((ζ.divisors.card : ℝ)) ^ 5
          * |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa ζ m|
        ≤ Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(3 : ℝ)) := by
  obtain ⟨X₀, hX₀⟩ := Work.FIChain.remainder_all_at_07
  refine ⟨max X₀ 2, ?_⟩
  intro x hx m ζ hm hζ hsf
  have hx' : X₀ ≤ x := le_trans (le_max_left _ _) hx
  have h1 := hX₀ x hx' m hm
  have hmem : ζ ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => by
      rw [h] at hsf
      exact absurd hsf (by simp)), hζ⟩, hsf⟩
  have h2 : ((ζ.divisors.card : ℝ)) ^ 5 *
      |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
        Submission.ASP.FIgtil Submission.ASP.FIa ζ m|
      ≤ ∑ d ∈ (Finset.Icc 1 ⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ 5 *
            |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
              Submission.ASP.FIgtil Submission.ASP.FIa d m| := by
    exact Finset.single_le_sum (f := fun d => ((d.divisors.card : ℝ)) ^ 5 *
        |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
          Submission.ASP.FIgtil Submission.ASP.FIa d m|)
      (fun i _ => by positivity) hmem
  rw [Work.FIChain.AcountAtilC, Work.FITop.AcountAtil] at h1 ⊢
  rw [Submission.ASP.RemainderSum] at h1
  exact le_trans h2 h1

/-! ## 4. The integral form of the inner sum (from the proved identity) -/

/-- **`S3plusInnerC` is the integral form.**  For a sequence supported on squarefree integers,
every `c` in the summation range of `S3plusInnerC` is squarefree (since `ℓc` then is), and on
squarefree `c` the proved `S3plusC_lamPlus_identity` gives
`μ(c)·λ⁺(c) = ∫_1^{c/Cm}ρ(c;u)du/u`. -/
theorem S3plusInnerC_eq_s3InnerInt (a : ℕ → ℝ) (N ℓ Cm : ℕ) (z sz : ℝ)
    (ha : ∀ n : ℕ, ¬ Squarefree n → a n = 0)
    (hCm : 1 ≤ Cm) (hz2 : (2 : ℝ) ≤ z) (hzCm : ((Cm : ℕ) : ℝ) < z) :
    S3plusInnerC a N ℓ z sz (Cm : ℝ) = s3InnerInt a N ℓ Cm z sz := by
  rw [S3plusInnerC, s3InnerInt]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hcz, hcsz, hcl⟩ := hc
  have hc_gt : (Cm : ℝ) < (c : ℝ) := lt_of_lt_of_le hzCm (le_of_lt hcz)
  have hc2 : 2 ≤ c := by
    have : (2 : ℝ) ≤ (c : ℝ) := le_trans hz2 (le_of_lt hcz)
    exact_mod_cast this
  by_cases hsf : Squarefree c
  · have hid := S3plusC_lamPlus_identity c Cm hc2 hsf hCm (by exact_mod_cast hc_gt)
    rw [hid]; ring
  · have hlc : ¬ Squarefree (ℓ * c) :=
      fun h => hsf (h.squarefree_of_dvd (⟨ℓ, by ring⟩ : c ∣ ℓ * c))
    rw [ha (ℓ * c) hlc]
    simp

end

end Work.FIChain
