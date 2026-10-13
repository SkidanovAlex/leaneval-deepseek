import Mathlib
import Submission.Work.DSG4b.pBasis.pBasis_pow_basis

/-!
# Decomposition of an element along a `p ^ n`-basis

Let `L` be a field of characteristic a prime `p`, let `Λ ⊆ L` be a `p`-basis of `L` over `L ^ p`
(exhibited by the monomial basis `b` of `L` over `(frobenius L p).fieldRange`), and let `n : ℕ`.
By `pBasis_pow_basis` the monomials with exponents `< p ^ n` over `Λ` form a basis of `L` over the
subfield `L ^ (p ^ n)` of `p ^ n`-th powers.  Writing an arbitrary `x : L` in this basis and
lifting each coefficient from `K L p n` to a `p ^ n`-th root gives the decomposition
`x = ∑_e d_e ^ (p ^ n) * ∏ a ^ (e a)`.
-/

namespace Work.DSG4b.gonfPerfect.pbPow

theorem pow_decomp (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (Λ : Set L)
    (b : Module.Basis {e : Λ →₀ ℕ // ∀ a : Λ, e a < p} ((frobenius L p).fieldRange) L)
    (hb : ∀ e, (b e : L) = (e.1).prod (fun a k => ((a : L) ^ k)))
    (n : ℕ) (x : L) :
    ∃ s : {e : Λ →₀ ℕ // ∀ a : Λ, e a < p ^ n} →₀ L,
      x = s.sum (fun e d => d ^ p ^ n * e.1.prod (fun a k => ((a : L) ^ k))) := by
  classical
  obtain ⟨b', hb'⟩ := Work.DSG4b.pBasis.pBasis_pow_basis L p Λ b hb n
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hpn : p ^ n ≠ 0 := pow_ne_zero n hp0
  -- lift each coefficient in `K L p n` to a `p ^ n`-th root, sending `0` to `0`
  let f : Work.DSG4b.pBasis.K L p n → L :=
    fun c => if c = 0 then 0 else Classical.choose ((Work.DSG4b.pBasis.mem_K n ((c : L))).mp c.2)
  have hf : f 0 = 0 := by simp [f]
  have hfv : ∀ c : Work.DSG4b.pBasis.K L p n, (f c) ^ p ^ n = (c : L) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      rw [hf, zero_pow hpn]
      rfl
    · simp only [f, hc, ite_false]
      exact Classical.choose_spec (((Work.DSG4b.pBasis.mem_K n ((c : L))).mp c.2))
  -- the expansion of `x` in the basis `b'`
  have h1 : x = (b'.repr x).sum (fun e c => (c : L) * e.1.prod (fun a k => ((a : L) ^ k))) := by
    conv_lhs => rw [← Module.Basis.linearCombination_repr b' x]
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr (fun e _ => ?_)
    rw [hb' e, Algebra.smul_def, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply]
  refine ⟨(b'.repr x).mapRange f hf, ?_⟩
  have key : ((b'.repr x).mapRange f hf).sum
      (fun e d => d ^ p ^ n * e.1.prod (fun a k => ((a : L) ^ k))) = x := by
    rw [Finsupp.sum_mapRange_index (fun e => by rw [zero_pow hpn, zero_mul])]
    conv_rhs => rw [h1]
    refine Finsupp.sum_congr (fun e _ => ?_)
    rw [hfv ((b'.repr x) e)]
  exact key.symm

end Work.DSG4b.gonfPerfect.pbPow
