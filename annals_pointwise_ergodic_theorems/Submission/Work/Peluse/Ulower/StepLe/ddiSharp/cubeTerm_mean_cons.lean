/-
# The cube term of an average: peeling the first coordinate

The quantity of interest is the cube term (`Work.Peluse.cubeTerm`)

`∏_{ω : Fin t → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')`

of the *average* `f y = |Z|⁻¹ ∑_z G z y` of a finite family of functions
`G : Z → ℤ → ℂ`, at a shift pair whose first coordinates are singled out as
`(Fin.cons a h, Fin.cons b h')`.  Because the cube term is multiplicative in `f`, the `2^{σ+1}`
vertices of the cube split into the two halves `ω 0 = false` and `ω 0 = true`:

* the `ω 0 = false` half gives the cube term of `f` at the point `x + b`;
* the `ω 0 = true` half gives the conjugate of the cube term of `f` at the point `x + a`.

Since `f` is an average over `z`, expanding the product of the two averages `f (y+b)` and
`star (f (y+a))` (one index per corner, `2^σ` corners) turns it into the average over pairs
`(z,z')`, i.e.

`cubeTerm (a :: h) (b :: h') (|Z|⁻¹ ∑_z G z ·) x
   = cubeTerm h h' (|Z×Z|⁻¹ ∑_{p : Z×Z} G p.1 (· + b) · conj (G p.2 (· + a))) x`,

which is `cubeTerm_mean_cons` below.  This is the bookkeeping identity by which the cube term of
the *averaged* dual function is read as the cube term of a *bilinear* expression of the slices;
it is used in the sharp (density-free) dual--difference interchange of `ddiSharp` to keep the
normalisation `|Z|` exact through the recursion `σ → σ + 1`.

The auxiliary lemmas are `private`: they are local plumbing (multiplicativity of the cube term,
compatibility with `star`, and the shift of the evaluation point).
-/
import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.Defs
import Submission.Work.Peluse.Ulower.Defs

namespace Work.Peluse.Ulower.StepLe.ddiSharp

open scoped BigOperators

noncomputable section

/-- **Peluse's cube recursion** in terms of `Work.Peluse.cubeTerm`: splitting the vertex `ω` of the
cube at its first coordinate. -/
private theorem cubeTerm_cons_apply {k : ℕ} (a b : ℤ) (h h' : Fin k → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm (Fin.cons a h) (Fin.cons b h') f x
      = Work.Peluse.cubeTerm h h' f (x + b) * star (Work.Peluse.cubeTerm h h' f (x + a)) := by
  have h1 := Work.Peluse.BoxNorm.cubeTerm_cons a b h h' f x
  simpa only [Work.Peluse.cubeTerm] using h1

/-- `Work.Peluse.cubeTerm` is multiplicative in the function. -/
private theorem cubeTerm_mul {t : ℕ} (h h' : Fin t → ℤ) (f g : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => f y * g y) x
      = Work.Peluse.cubeTerm h h' f x * Work.Peluse.cubeTerm h h' g x := by
  simp only [Work.Peluse.cubeTerm, Work.Peluse.Ulower.starIterate_mul, Finset.prod_mul_distrib]

/-- The iterated conjugate of a conjugate is the conjugate of the iterated conjugate. -/
private theorem starIterate_star (n : ℕ) (z : ℂ) : (star^[n]) (star z) = star ((star^[n]) z) := by
  rw [← Function.iterate_succ_apply star n z, Function.iterate_succ_apply' star n z]

/-- The cube term of the pointwise conjugate is the conjugate of the cube term. -/
private theorem cubeTerm_star {t : ℕ} (h h' : Fin t → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => star (f y)) x
      = star (Work.Peluse.cubeTerm h h' f x) := by
  rw [Work.Peluse.cubeTerm, Work.Peluse.cubeTerm, star_prod]
  exact Finset.prod_congr rfl (fun ω _ => starIterate_star _ _)

/-- Shifting the function is the same as shifting the evaluation point. -/
private theorem cubeTerm_shift {t : ℕ} (h h' : Fin t → ℤ) (f : ℤ → ℂ) (c x : ℤ) :
    Work.Peluse.cubeTerm h h' (fun y => f (y + c)) x
      = Work.Peluse.cubeTerm h h' f (x + c) := by
  rw [Work.Peluse.cubeTerm, Work.Peluse.cubeTerm]
  exact Finset.prod_congr rfl (fun ω _ => by rw [add_right_comm])

theorem cubeTerm_mean_cons {σ : ℕ} {Z : Type} [Fintype Z] (G : Z → ℤ → ℂ) (a b : ℤ)
    (h h' : Fin σ → ℤ) (x : ℤ) :
    Work.Peluse.cubeTerm (Fin.cons a h) (Fin.cons b h')
        (fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y) x
      = Work.Peluse.cubeTerm h h' (fun y => ((Fintype.card (Z × Z) : ℂ))⁻¹ *
          ∑ p : Z × Z, (G p.1 (y + b) * star (G p.2 (y + a)))) x := by
  classical
  -- abbreviate the averaged function
  set F : ℤ → ℂ := fun y => ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z y with hF
  -- the pointwise expansion of the averaged product into the average over pairs
  have hpt : ∀ y : ℤ, ((Fintype.card (Z × Z) : ℂ))⁻¹ *
        ∑ p : Z × Z, (G p.1 (y + b) * star (G p.2 (y + a))) =
      F (y + b) * star (F (y + a)) := by
    intro y
    simp only [hF]
    have h1 : star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (y + a))
        = ((Fintype.card Z : ℂ))⁻¹ * ∑ z, star (G z (y + a)) := by
      rw [star_mul, star_sum]
      rw [show star (((Fintype.card Z : ℂ))⁻¹) = ((Fintype.card Z : ℂ))⁻¹ from by
            rw [Complex.star_def, map_inv₀, map_natCast]]
      ring
    have hprod : (∑ p : Z × Z, G p.1 (y + b) * star (G p.2 (y + a)))
        = (∑ z : Z, G z (y + b)) * (∑ z : Z, star (G z (y + a))) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    have hconst : (Fintype.card (Z × Z) : ℂ) =
        (Fintype.card Z : ℂ) * (Fintype.card Z : ℂ) := by
      rw [Fintype.card_prod]; push_cast; ring
    rw [hprod, h1, hconst, mul_inv_rev]
    ring
  -- replace the bilinear function appearing on the right by `fun y => F (y+b) * star (F (y+a))`
  rw [show (fun y : ℤ => ((Fintype.card (Z × Z) : ℂ))⁻¹ *
        ∑ p : Z × Z, (G p.1 (y + b) * star (G p.2 (y + a)))) =
      (fun y => F (y + b) * star (F (y + a))) from funext hpt]
  -- peel the first coordinate, then push `star` and the shifts through the cube term
  rw [cubeTerm_cons_apply a b h h' F x]
  conv_rhs => rw [cubeTerm_mul, cubeTerm_star, cubeTerm_shift, cubeTerm_shift]

end

end Work.Peluse.Ulower.StepLe.ddiSharp
