import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open BigOperators

/-- Pointwise form of the orthogonality of the Dirichlet characters modulo `q`: for a
natural number `p`, the real part of `∑_χ χ(p)/p` is `φ(q)/p` when `p ≡ 1 (mod q)` and
`0` otherwise.  The imaginary part is discarded by `Complex.re_sum`/`Complex.natCast_re`,
which is harmless since `∑_χ χ(p)` is a real number (`φ(q)` or `0`). -/
lemma char_sum_re_pointwise (q : ℕ+) (p : ℕ) :
    (∑ χ : DirichletCharacter ℂ (q:ℕ), ((χ p : ℂ) / (p : ℂ)).re)
      = if p ≡ 1 [MOD (q:ℕ)] then ((q:ℕ).totient : ℝ) * ((1:ℝ)/(p:ℝ)) else 0 := by
  classical
  have h1 : (∑ χ : DirichletCharacter ℂ (q:ℕ), ((χ p : ℂ) / (p : ℂ)).re)
      = (∑ χ : DirichletCharacter ℂ (q:ℕ), (χ p : ℂ)).re / (p : ℝ) := by
    rw [← Complex.re_sum]
    rw [← Finset.sum_div]
    rw [← Complex.ofReal_natCast p]
    rw [Complex.div_ofReal_re]
  rw [h1]
  have h2 : (∑ χ : DirichletCharacter ℂ (q:ℕ), (χ p : ℂ))
      = if (p : ZMod (q:ℕ)) = 1 then ((q:ℕ).totient : ℂ) else 0 :=
    DirichletCharacter.sum_characters_eq ℂ (p : ZMod (q:ℕ))
  rw [h2]
  by_cases h : (p : ZMod (q:ℕ)) = 1
  · have h' : (p : ZMod (q:ℕ)) = ((1:ℕ) : ZMod (q:ℕ)) := by rw [h]; simp
    have hp : p ≡ 1 [MOD (q:ℕ)] := (ZMod.natCast_eq_natCast_iff p 1 (q:ℕ)).mp h'
    rw [ite_eq_left hp, ite_eq_left h]
    simp only [Complex.natCast_re]
    rw [div_eq_mul_inv, one_div]
  · have h' : ¬ ((p : ZMod (q:ℕ)) = ((1:ℕ) : ZMod (q:ℕ))) := by
      intro hh; exact h (by rw [hh]; simp)
    have hp : ¬ (p ≡ 1 [MOD (q:ℕ)]) :=
      fun hh => h' ((ZMod.natCast_eq_natCast_iff p 1 (q:ℕ)).mpr hh)
    rw [ite_eq_right hp, ite_eq_right h]
    rw [Complex.zero_re, zero_div]

/-- Orthogonality of the Dirichlet characters modulo `q`, in the form needed for
`∑_{p ≤ x, p ≡ 1 (mod q)} 1/p`: summing the reciprocal prime sums `∑_p χ(p)/p` over all
characters mod `q` and passing to real parts recovers `φ(q) · ∑_{p ≤ x, p ≡ 1 (mod q)} 1/p`.
Use `DirichletCharacter.sum_characters_eq` (or the local
`Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj`, a proved module of this workspace)
together with `ZMod.natCast_eq_natCast_iff` and `Complex.re_sum`. -/
theorem sum_char_recip_re_eq (q : ℕ+) (x : ℝ) :
    (∑ χ : DirichletCharacter ℂ (q : ℕ), (∑ p ∈ (⌊x⌋₊).primesLE, (χ p : ℂ) / (p : ℂ)).re)
      = ((q : ℕ).totient : ℝ) *
          ∑ p ∈ (⌊x⌋₊).primesLE.filter (fun p ↦ p ≡ 1 [MOD (q : ℕ)]), (1 : ℝ) / (p : ℝ) := by
  classical
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun p _ => char_sum_re_pointwise q p)]
  rw [Finset.mul_sum, ← Finset.sum_filter]

end Work.BMF.liouville
