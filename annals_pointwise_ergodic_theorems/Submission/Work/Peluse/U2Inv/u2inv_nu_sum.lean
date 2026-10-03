import Mathlib
import Submission.Work.Peluse.U2Inv.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Summing the weight `ν_m` against a test function

This module proves the "averaging" identity for Peluse's weight `ν_m` on the auxiliary cyclic
group `ZMod (Gmod L)`: `ν_m` is the distribution of `u - u'` for two independent uniform points
`u, u'` of `{1, …, m}`, so summing it against a test function `g` on the group gives the average
of `g` over the differences `u - u'`.  Written with Peluse's weight `μ_m` on `ℤ` (finitely
supported in `(-m, m)`, and *a fortiori* in the symmetric interval `symIcc (m-1)`), the identity
reads

`∑_z ν_m(z) g(z) = ∑_{a ∈ symIcc (m-1)} μ_m(a) g(a)`.

Both sides are shown to equal `m^{-2} ∑_{u,u' ∈ [1,m]} g(u - u')`, by regrouping the sum over the
pairs `(u, u') ∈ {1, …, m}²` according to the difference `u - u'` — on the left via the fibres of
the difference map in the group, on the right via the fibres of the difference map in `ℤ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

open Finset

/-- Regrouping a sum weighted by the size of the fibres of a map into a group `ZMod N` into a sum
over the source. -/
lemma sum_card_filter_mul_zmod {N : ℕ} [NeZero N] {α : Type*} (s : Finset α)
    (d : α → ZMod N) (f : ZMod N → ℂ) :
    ∑ z : ZMod N, ((s.filter fun p => d p = z).card : ℂ) * f z = ∑ p ∈ s, f (d p) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.univ)
      (g := d) (fun i _ => Finset.mem_univ _) (fun i => f (d i))]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
    nsmul_eq_mul]

/-- Regrouping a sum weighted by the size of the fibres of a map into `ℤ` into a sum over the
source. -/
lemma sum_card_filter_mul_int {α : Type*} (s : Finset α) (t : Finset ℤ) (d : α → ℤ)
    (F : ℤ → ℂ) (h : ∀ p ∈ s, d p ∈ t) :
    ∑ a ∈ t, ((s.filter fun p => d p = a).card : ℂ) * F a = ∑ p ∈ s, F (d p) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := t) (g := d) h (fun i => F (d i))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
    Finset.sum_const, nsmul_eq_mul]

/-- Peluse's weight `μ_m` as the distribution of the difference of two points of `{1, …, m}`. -/
lemma muL_eq_card (m : ℕ) (a : ℤ) :
    (muL m a : ℂ) = ((m : ℂ) ^ 2)⁻¹ *
      ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
        (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = a)).card : ℂ) := by
  simp only [muL]
  push_cast
  ring

/-- The difference of two points of `{1, …, m}` lies in the symmetric interval `[-m+1, m-1]`. -/
lemma mem_prod_dif_symIcc (m : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m)) :
    (p.1 : ℤ) - (p.2 : ℤ) ∈ symIcc (m - 1) := by
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hp2
  rw [mem_symIcc_iff]
  constructor <;> omega

/-- Summing `ν_m` against a test function on `ZMod (Gmod L)` recovers the average of the test
function over the differences of two points of `{1, …, m}`; equivalently, against Peluse's weight
`μ_m` on `ℤ`. -/
theorem u2inv_nu_sum (L m : ℕ) (hm : m ≤ L) (g : ZMod (Work.Peluse.U2Inv.Gmod L) → ℂ) :
    (∑ z : ZMod (Work.Peluse.U2Inv.Gmod L), Work.Peluse.U2Inv.nu L m z * g z)
      = ∑ a ∈ Work.Peluse.symIcc (m - 1),
          (Work.Peluse.muL m a : ℂ) * g (a : ZMod (Work.Peluse.U2Inv.Gmod L)) := by
  classical
  -- the left-hand side, as an average over the `m²` differences
  have hL : (∑ z : ZMod (Gmod L), nu L m z * g z) = ((m : ℂ) ^ 2)⁻¹ *
      ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
        g ((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) := by
    have h1 : (∑ z : ZMod (Gmod L), nu L m z * g z) = ((m : ℂ) ^ 2)⁻¹ *
        ∑ z : ZMod (Gmod L),
          ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
            (fun p : ℕ × ℕ =>
              ((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) = z)).card : ℂ) * g z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [nu]
      ring
    have h2 : ((m : ℂ) ^ 2)⁻¹ * ∑ z : ZMod (Gmod L),
          ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
            (fun p : ℕ × ℕ =>
              ((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) = z)).card : ℂ) * g z
        = ((m : ℂ) ^ 2)⁻¹ *
          ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
            g ((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) := by
      rw [sum_card_filter_mul_zmod
        (s := (Finset.Icc 1 m).product (Finset.Icc 1 m))
        (d := fun p : ℕ × ℕ => (p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) (f := g)]
    exact h1.trans h2
  -- the right-hand side, as the same average over the `m²` differences
  have hR : (∑ a ∈ symIcc (m - 1), (muL m a : ℂ) * g (a : ZMod (Gmod L))) = ((m : ℂ) ^ 2)⁻¹ *
      ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
        g ((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) := by
    have h1 : (∑ a ∈ symIcc (m - 1), (muL m a : ℂ) * g (a : ZMod (Gmod L))) =
        ((m : ℂ) ^ 2)⁻¹ * ∑ a ∈ symIcc (m - 1),
          ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = a)).card : ℂ)
            * g (a : ZMod (Gmod L)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [muL_eq_card]
      ring
    have h2 : (∑ a ∈ symIcc (m - 1),
          ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = a)).card : ℂ)
            * g (a : ZMod (Gmod L)))
        = ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
            g ((p.1 : ZMod (Gmod L)) - (p.2 : ZMod (Gmod L))) := by
      rw [sum_card_filter_mul_int (s := (Finset.Icc 1 m).product (Finset.Icc 1 m))
        (t := symIcc (m - 1)) (d := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))
        (F := fun a : ℤ => g (a : ZMod (Gmod L)))
        (fun i hi => mem_prod_dif_symIcc m i hi)]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [Int.cast_sub, Int.cast_natCast]
    exact h1.trans (congrArg (fun x => ((m : ℂ) ^ 2)⁻¹ * x) h2)
  rw [hL, hR]

end

end Work.Peluse.U2Inv
