import Mathlib
import Submission.Work.LT.relT_defs
import Submission.Work.LT.relT_chi
import Submission.Work.LT.relT_sl3E_basic
import Submission.Work.LT.relT_fhat_colU_diff

namespace Work.LT

/-! **The `U`-eigenrelation for the column Fourier coefficients.**

For the column subgroup `U = {u(st) = colU p a b c st : st ∈ (ℤ/p)²} ≅ (ℤ/p)²` and the
isotypic component `fhat_z f g = (1/p²) ∑_{st} conj(χ_z(st)) · f(u(st)·g)`, one has

`fhat_z f (u(st)·g) = χ_z(st) · fhat_z f g`.

Equivalently: the `χ_z`-isotypic component spans the one-dimensional representation
`U ∋ u(st) ↦ χ_z(st) ∈ ℂ` of `U`. This is the basic eigenvector identity used in the
Kazhdan argument of `sl3_relT_column`.

ROUTE. A direct computation. The right translation `st' ↦ st' + st` is a bijection of `(ℤ/p)²`,
`u(st')·u(st) = u(st' + st)`, and `conj(χ_z(st' - st)) = χ_z(st)·conj(χ_z(st'))`, so the sum
`∑_{st'} conj(χ_z(st')) f(u(st')u(st)g)` reindexes to `χ_z(st) · ∑_{x} conj(χ_z(x)) f(u(x)g)`. -/

/-- The character shift identity `conj(χ_z(x + (-st))) = χ_z(st)·conj(χ_z(x))` behind the
reindexing: `χ_z` is multiplicative and `χ_z(-st) = conj(χ_z(st))`. -/
lemma relT_fhat_eigen_shift (p : ℕ) [NeZero p] (z st x : ZMod p × ZMod p) :
    star (chi p z (x + -st)) = chi p z st * star (chi p z x) := by
  have h : chi p z (x + -st) = chi p z x * star (chi p z st) := by
    rw [(chi_basic p).2.2.1 z x (-st), ← chi_neg_star p z st]
  rw [h, star_mul, star_star]

/-- The reindexing identity: for any `F`,
`∑_{st'} conj(χ_z(st')) · F(st' + st) = χ_z(st) · ∑_x conj(χ_z(x)) · F(x)`.
This is the content of the eigenrelation, isolated from `fhat`. -/
lemma relT_fhat_eigen_sum (p : ℕ) [NeZero p] (z st : ZMod p × ZMod p)
    (F : ZMod p × ZMod p → ℂ) :
    (∑ st' : ZMod p × ZMod p, star (chi p z st') * F (st' + st))
      = chi p z st * ∑ x, star (chi p z x) * F x := by
  -- reindex the sum by the bijection `st' ↦ st' + st`
  have key := Equiv.sum_comp (Equiv.addRight st)
    (fun y : ZMod p × ZMod p => star (chi p z (y - st)) * F y)
  simp only [Equiv.coe_addRight] at key
  simp only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero] at key
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [relT_fhat_eigen_shift p z st x]
  ring

theorem relT_fhat_eigen :
    ∀ (p : ℕ) [NeZero p] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
        (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
        fhat p a b c z f (colU p a b c st * g) = chi p z st * fhat p a b c z f g := by
  intro p hp a b c hab hac hbc f st z g
  -- the argument of `f` inside the Fourier sum: `u(st')·(u(st)·g) = u(st' + st)·g`
  have hmul : ∀ st' : ZMod p × ZMod p,
      colU p a b c st' * (colU p a b c st * g) = colU p a b c (st' + st) * g := by
    intro st'
    rw [← mul_assoc, relT_fhat_colU_diff_mul a b c hab hac hbc st' st]
  have hsum : (∑ st' : ZMod p × ZMod p,
        star (chi p z st') * f (colU p a b c (st' + st) * g))
      = chi p z st * ∑ x : ZMod p × ZMod p,
          star (chi p z x) * f (colU p a b c x * g) :=
    relT_fhat_eigen_sum p z st (fun x => f (colU p a b c x * g))
  simp only [fhat]
  rw [show (∑ st' : ZMod p × ZMod p,
          star (chi p z st') * f (colU p a b c st' * (colU p a b c st * g)))
        = ∑ st' : ZMod p × ZMod p,
            star (chi p z st') * f (colU p a b c (st' + st) * g) from
      Finset.sum_congr rfl (fun st' _ => by rw [hmul st'])]
  rw [hsum, mul_div_assoc]

end Work.LT
