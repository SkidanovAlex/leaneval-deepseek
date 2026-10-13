import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSM5b.rootKillTransport
import Submission.Work.DSM5b.H0Defs

universe a

namespace Work.DSM5b

-- the machinery of `phiPC`/`phiPow`/`psiPow` on the explicit perfected complex is in
-- `Submission.Work.DSM5b.rootKillTransport` (as `Work.DSM5b.Work.DSM5b.…`)
open Work.DSM5b.Work.DSM5b

/-- **Semilinearity of the iterated Frobenius on the explicit perfected complex.**  `phiPow p t m e`
is the componentwise `p^e`-th power map, so on a scalar multiple
`(r · z)^{p^e} = r^{p^e} · z^{p^e}`.

(Companion of `Work.DSM5b.Work.DSM5b.psiPow_smul`, which gives the same statement for the root
map, with `r ^ (1/p^e)` in place of `r ^ (p^e)`.) -/
lemma phiPow_smul (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R)
    (m e : ℕ) (r : R) (z : PCX p t m) :
    phiPow p t m e (r • z) = r ^ (p ^ e) • phiPow p t m e z := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [phiPow_succ, ih, phiPC_smul, pow_succ, pow_mul, phiPow_succ]

/-- **The `p^k`-th power of the `k`-th root of `T` is `T`.**  For the frozen root tower
`k ↦ (frobeniusEquiv R p).symm^[k] T` of `Work.DSM5b.IsRootTower.frozen`. -/
lemma iterate_frobSymm_pow_eq (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] (T : R) (k : ℕ) :
    (((frobeniusEquiv R p).symm)^[k] T) ^ (p ^ k) = T := by
  simpa only [Nat.zero_add, Function.iterate_zero, id_eq] using
    (IsRootTower.frozen p R T).pow_pow 0 k

/-- **Root killing from the zero-th root.**  Suppose a fixed `T : R` already kills the cohomology of
the explicit perfected chart Čech complex `PCX p t ·`/`PCd p t ·` in every positive degree:  every
cycle `z` in degree `n+1` becomes a boundary after multiplying by `T`
(`h0`).  Then the same holds for each `p^k`-th root `(frobeniusEquiv R p).symm^[k] T` of `T`.

The proof is the Frobenius conjugation of the hypothesis.  The componentwise `p^k`-th power map
`phiPow p t · k` is a bijection of `PCX p t ·` commuting with `PCd` (`PCd_phiPow`, `psiPow_phiPow`,
`psiPow_PCd`) and is `R`-semilinear with `phiPow (r • z) = r ^ (p ^ k) • phiPow z` (`phiPow_smul`).
Given a cycle `z`, the element `phiPow p t (n+1) k z` is again a cycle, so `h0` yields
`T • phiPow z = PCd y`; but `T = (ϖ k) ^ (p ^ k)` (`iterate_frobSymm_pow_eq`) and hence this is the
`phiPow`-image of `ϖ k • z`, `ϖ k = (frobeniusEquiv R p).symm^[k] T`.  Applying the inverse root map
`psiPow p t · k` — which likewise commutes with `PCd` — gives `ϖ k • z = PCd (psiPow p t n k y)`. -/
theorem rootKillingFromZeroRoot (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e)
    (h0 : ∀ (n : ℕ) (z : Work.DSM5b.PCX p t (n + 1)), Work.DSM5b.PCd p t (n + 1) z = 0 →
      ∃ y : Work.DSM5b.PCX p t n, T • z = Work.DSM5b.PCd p t n y) :
    ∀ (k n : ℕ) (z : Work.DSM5b.PCX p t (n + 1)), Work.DSM5b.PCd p t (n + 1) z = 0 →
      ∃ y : Work.DSM5b.PCX p t n,
        ((frobeniusEquiv R p).symm^[k] T) • z = Work.DSM5b.PCd p t n y := by
  intro k n z hz
  -- the `p^k`-th power of the cycle is a cycle, so the hypothesis applies to it
  obtain ⟨y, hy⟩ := h0 n (phiPow p t (n + 1) k z)
    (by rw [PCd_phiPow p t (n + 1) k, hz, phiPow_zero_zero])
  refine ⟨psiPow p t n k y, ?_⟩
  -- conjugate the killing equation by the root map
  calc ((frobeniusEquiv R p).symm^[k] T) • z
      = psiPow p t (n + 1) k
          (phiPow p t (n + 1) k (((frobeniusEquiv R p).symm^[k] T) • z)) :=
        (psiPow_phiPow p t (n + 1) k _).symm
    _ = psiPow p t (n + 1) k (T • phiPow p t (n + 1) k z) := by
        rw [phiPow_smul, iterate_frobSymm_pow_eq]
    _ = psiPow p t (n + 1) k (PCd p t n y) := by rw [hy]
    _ = PCd p t n (psiPow p t n k y) := psiPow_PCd p t n k y

end Work.DSM5b
