import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.relT_defs
import Submission.Work.LT.relT_chi
import Submission.Work.LT.chi_basic
import Submission.Work.LT.chi_orth
import Submission.Work.LT.relT_sl3E_basic
import Submission.Work.LT.relT_l2
import Submission.Work.LT.relT_fhat_eigen
import Submission.Work.LT.relT_fhat_inversion
import Submission.Work.LT.l2sq_sum_orthogonal

namespace Work.LT

/-! **Fourier decomposition along the column subgroup `U = {E_ac(s)E_bc(t)} ≅ (ℤ/p)²`.**

`G = SL₃(ℤ/p)`, and `fhat p a b c z f` is the `χ_z`-isotypic component of `f` for left
translation by `U`, `u(s,t) = colU p a b c (s,t)`, `chi p z (s,t) = ω^{z₁s+z₂t}` with
`ω = ZMod.stdAddChar` (see `relT_defs`).

The three conjuncts are

* the inversion formula `∑_z fhat_z f = f` (`relT_fhat_inversion`),
* the sub-sum Plancherel identity `l2sq (∑_{z∈B} fhat_z h) = ∑_{z∈B} l2sq (fhat_z h)`,
* the eigenrelation `fhat_z f (u(st)·g) = χ_z(st) · fhat_z f g` (`relT_fhat_eigen`).

The Plancherel identity is proved by expanding the `ℓ²`-norm of the finite sum into the double
sum of Hermitian pairings `ip` and observing that the off-diagonal pairings vanish.
Indeed `fhat_z f` is `χ_z`-equivariant for the left action of `U` (the eigenrelation); if
`φ` is `χ_z`-equivariant and `ψ` is `χ_{z'}`-equivariant with `z ≠ z'`, then for every `st`

`ip φ ψ = ∑_g conj(φ g) ψ g = ∑_g conj(φ (u(st)·g)) ψ (u(st)·g) = conj(χ_z(st)) χ_{z'}(st) · ip φ ψ`,

and summing over `st` gives `p² · ip φ ψ = (∑_st conj(χ_z st) χ_{z'} st) · ip φ ψ = 0`
(the character sum vanishes for `z ≠ z'`, `chi_parseval`/`chi_orth`), whence `ip φ ψ = 0`.
Pythagoras for pairwise orthogonal families (`l2sq_sum_orthogonal`) then finishes the job. -/

/-- **Orthogonality of `U`-eigenfunctions with different characters.**
If `φ` is `χ_z`-equivariant, `ψ` is `χ_{z'}`-equivariant and `z ≠ z'`, then `ip φ ψ = 0`. -/
lemma relT_fourier_ip_orthogonal (p : ℕ) [NeZero p] {a b c : Fin 3}
    (φ ψ : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) (z z' : ZMod p × ZMod p)
    (hzz : z ≠ z')
    (hφ : ∀ (st : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
        φ (colU p a b c st * g) = chi p z st * φ g)
    (hψ : ∀ (st : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
        ψ (colU p a b c st * g) = chi p z' st * ψ g) :
    ip φ ψ = 0 := by
  have hp2 : (p : ℂ) ^ 2 ≠ 0 := by
    have : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
    exact pow_ne_zero 2 this
  -- Reindexing `g ↦ u(st)·g` turns the pairing into a multiple of itself.
  have key : ∀ st : ZMod p × ZMod p,
      ip φ ψ = (star (chi p z st) * chi p z' st) * ip φ ψ := by
    intro st
    have hre : (∑ g, star (φ (colU p a b c st * g)) * ψ (colU p a b c st * g))
        = ∑ g, star (φ g) * ψ g :=
      Equiv.sum_comp (Equiv.mulLeft (colU p a b c st)) (fun g => star (φ g) * ψ g)
    calc ip φ ψ = ∑ g, star (φ g) * ψ g := rfl
      _ = ∑ g, star (φ (colU p a b c st * g)) * ψ (colU p a b c st * g) := hre.symm
      _ = ∑ g, (star (chi p z st) * chi p z' st) * (star (φ g) * ψ g) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [hφ st g, hψ st g, star_mul]
            ring
      _ = (star (chi p z st) * chi p z' st) * ∑ g, star (φ g) * ψ g := by
            rw [Finset.mul_sum]
      _ = (star (chi p z st) * chi p z' st) * ip φ ψ := rfl
  -- The character sum over `st` vanishes for `z ≠ z'`.
  have hsumchi : (∑ st : ZMod p × ZMod p, star (chi p z st) * chi p z' st) = 0 := by
    have hterm : ∀ st : ZMod p × ZMod p, star (chi p z st) * chi p z' st = chi p (z' - z) st := by
      intro st
      rw [(chi_basic p).2.2.2.1 z st, ← (chi_basic p).2.1 (-z) z' st]
      congr 1
      abel
    simp only [hterm]
    rw [(chi_orth p).2.1 (z' - z)]
    have : z' - z ≠ 0 := fun h0 => hzz (sub_eq_zero.mp h0).symm
    simp [this]
  -- Sum the identity `ip φ ψ = (…) * ip φ ψ` over `st`.
  have hsum := Finset.sum_congr rfl (fun st (_ : st ∈ Finset.univ) => key st)
  have h1 : (∑ st : ZMod p × ZMod p, ip φ ψ) = (p : ℂ) ^ 2 * ip φ ψ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
    push_cast
    ring
  have h2 : (∑ st : ZMod p × ZMod p, (star (chi p z st) * chi p z' st) * ip φ ψ) = 0 := by
    rw [← Finset.sum_mul, hsumchi, zero_mul]
  rw [h1, h2] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hp2

theorem relT_fourier :
    ∀ (p : ℕ) [NeZero p] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ,
        (∀ g, ∑ z : ZMod p × ZMod p, fhat p a b c z f g = f g)
      ∧ (∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
             (B : Finset (ZMod p × ZMod p)),
            l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g)
              = ∑ z ∈ B, l2sq (fhat p a b c z h))
      ∧ (∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
            fhat p a b c z f (colU p a b c st * g) = chi p z st * fhat p a b c z f g) := by
  intro p _ a b c hab hac hbc f
  refine ⟨?_, ?_, ?_⟩
  · -- Inversion formula.
    exact relT_fhat_inversion p hab hac hbc f
  · -- Sub-sum Plancherel / Pythagoras for the orthogonal family `z ↦ fhat_z h`.
    intro h B
    exact l2sq_sum_orthogonal B (fun z => fhat p a b c z h) (fun z _ z' _ hzz =>
      relT_fourier_ip_orthogonal p (fhat p a b c z h) (fhat p a b c z' h) z z' hzz
        (fun st g => relT_fhat_eigen p hab hac hbc h st z g)
        (fun st g => relT_fhat_eigen p hab hac hbc h st z' g))
  · -- Eigenrelation.
    exact relT_fhat_eigen p hab hac hbc f

end Work.LT
