/-
The **two-shift product identity** for the general box form.

`gHalf n Y β u z z' x a` is the `ω`-product `∏_ω C^{|ω|} u_ω (x + gtotal (gcorner z z') ω + a)`,
i.e. the "half" of the cube term built from a single function; the box form of a product of two
shifted functions splits as the product of the two half products:

  `gWinForm (u(· + a) · conj (v(· + a'))) = ∑_{z,z'} ∑_{x ∈ W} gHalf u z z' x a · conj (gHalf v z z' x a')`.

The only ingredient is the pointwise identity

  `(star^[k]) (A * star B) = (star^[k]) A * star ((star^[k]) B)`

(conjugation iterate of a product whose second factor is already conjugated), together with
multiplicativity of `star^[k]` (`Work.Peluse.BoxNorm.star_iterate_mul`) and of `star`
(`star_prod`).  Both `star^[k]` and `star` preserve products, so the `ω`-product distributes.
-/
import Mathlib
import Submission.Work.Peluse.SwapC.GDefs

namespace Work.Peluse.SwapC

/-- Conjugation iterate of a product whose second factor is conjugated: the iterate acts on each
factor separately, and only the second factor picks up the extra `star`. -/
private lemma star_iterate_mul_star (k : ℕ) (a b : ℂ) :
    (star^[k]) (a * star b) = (star^[k]) a * star ((star^[k]) b) := by
  rw [Work.Peluse.BoxNorm.star_iterate_mul, Work.Peluse.BoxNorm.star_iterate_conj]

theorem gWinForm_shift_prod_two {n : ℕ} (Y : Fin n → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin n) → Y i → ℤ) (W : Finset ℤ)
    (u v : (Fin n → Bool) → ℤ → ℂ) (a a' : ℤ) :
    Work.Peluse.SwapC.gWinForm n Y β W (fun ω y => u ω (y + a) * star (v ω (y + a')))
      = ∑ z : Work.Peluse.SwapC.GIdx n Y, ∑ z' : Work.Peluse.SwapC.GIdx n Y, ∑ x ∈ W,
          Work.Peluse.SwapC.gHalf n Y β u z z' x a * star (Work.Peluse.SwapC.gHalf n Y β v z z' x a')
      := by
  simp only [Work.Peluse.SwapC.gWinForm, Work.Peluse.SwapC.gHalf, star_iterate_mul_star,
    Finset.prod_mul_distrib, star_prod]

end Work.Peluse.SwapC
