import Mathlib
import Submission.Work.Peluse.U2Inv.u2inv_nu_sum
import Submission.Work.Peluse.U2Inv.u2inv_DeltaG_sum

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The group weighted difference sum `gW` equals the interval sum `T3`

This module proves

`gW L m f = ((Gmod L) ^ 3)⁻¹ * T3 L m f`

for `f` supported in `[-L,L]` and `m ≤ L`.

Unfolding the definition of `gW`, this is the statement that the group average
`(Gmod L)⁻³ ∑_{x,a,b ∈ ZMod (Gmod L)} ν_m(a) ν_m(b) Δ_{a,b}(pF L f) x`
agrees with the interval sum
`T3 L m f = ∑_{x ∈ symIcc L} ∑_{a,b ∈ symIcc (m-1)} μ_m(a) μ_m(b) Δ_{a,b} f x`.

The two building blocks are

* `Work.Peluse.U2Inv.u2inv_nu_sum`: the weight `ν_m` on the group is the transport of Peluse's
  weight `μ_m` on `ℤ`, so summing against it may be replaced by summing over `symIcc (m-1)`;
* `Work.Peluse.U2Inv.u2inv_DeltaG_sum`: the group difference operator applied to the zero
  extension `pF L f` sums to the interval difference operator applied to `f`.

The rest of the proof is the bookkeeping of the three commuting sums (`x`, `a`, `b`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-- The order of summation of a triple sum over the group `ZMod N` may be reversed: `x` outermost
becomes `x` innermost. -/
private lemma u2inv_sum3_comm_zmod (N : ℕ) [NeZero N] (F : ZMod N → ZMod N → ZMod N → ℂ) :
    (∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N, F x a b)
      = ∑ a : ZMod N, ∑ b : ZMod N, ∑ x : ZMod N, F x a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

/-- The order of summation of a triple sum over `ℤ`-indexed `Finset`s may be reversed. -/
private lemma u2inv_sum3_comm_int (s t : Finset ℤ) (F : ℤ → ℤ → ℤ → ℂ) :
    (∑ x ∈ s, ∑ a ∈ t, ∑ b ∈ t, F x a b) = ∑ a ∈ t, ∑ b ∈ t, ∑ x ∈ s, F x a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

/-- `gW` is the normalised group weighted difference sum, and `T3` is its interval counterpart;
the two agree. -/
theorem u2inv_gW_eq_triple (L m : ℕ) (f : ℤ → ℂ) (hf : Work.Peluse.SupportIn f L)
    (hm : m ≤ L) :
    Work.Peluse.U2Inv.gW L m f
      = (((Work.Peluse.U2Inv.Gmod L : ℂ)) ^ 3)⁻¹ * Work.Peluse.U2Inv.T3 L m f := by
  unfold gW T3
  congr 1
  have hS : (∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
        nu L m a * nu L m b * DeltaG a b (pF L f) x)
      = ∑ a ∈ Work.Peluse.symIcc (m - 1), (Work.Peluse.muL m a : ℂ) *
          (∑ b ∈ Work.Peluse.symIcc (m - 1), (Work.Peluse.muL m b : ℂ) *
            (∑ x ∈ Work.Peluse.symIcc L, DeltaZ a b f x)) := by
    have h₁ : (∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
          nu L m a * nu L m b * DeltaG a b (pF L f) x)
        = ∑ a : ZMod (Gmod L), nu L m a * (∑ b : ZMod (Gmod L),
            nu L m b * (∑ x : ZMod (Gmod L), DeltaG a b (pF L f) x)) := by
      rw [u2inv_sum3_comm_zmod (Gmod L)
        (fun x a b => nu L m a * nu L m b * DeltaG a b (pF L f) x)]
      simp only [Finset.mul_sum, mul_assoc]
    rw [h₁, u2inv_nu_sum L m hm (fun a => ∑ b : ZMod (Gmod L),
          nu L m b * (∑ x : ZMod (Gmod L), DeltaG a b (pF L f) x))]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    congr 1
    rw [u2inv_nu_sum L m hm (fun b => ∑ x : ZMod (Gmod L),
          DeltaG (a : ZMod (Gmod L)) b (pF L f) x)]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [u2inv_DeltaG_sum L m f hf hm a b ha hb]
  have hT : (∑ x ∈ Work.Peluse.symIcc L, ∑ a ∈ Work.Peluse.symIcc (m - 1),
        ∑ b ∈ Work.Peluse.symIcc (m - 1), (Work.Peluse.muL m a : ℂ) *
          (Work.Peluse.muL m b : ℂ) * DeltaZ a b f x)
      = ∑ a ∈ Work.Peluse.symIcc (m - 1), (Work.Peluse.muL m a : ℂ) *
          (∑ b ∈ Work.Peluse.symIcc (m - 1), (Work.Peluse.muL m b : ℂ) *
            (∑ x ∈ Work.Peluse.symIcc L, DeltaZ a b f x)) := by
    rw [u2inv_sum3_comm_int (Work.Peluse.symIcc L) (Work.Peluse.symIcc (m - 1))
      (fun x a b => (Work.Peluse.muL m a : ℂ) * (Work.Peluse.muL m b : ℂ) * DeltaZ a b f x)]
    simp only [Finset.mul_sum, mul_assoc]
  rw [hS, hT]

end

end Work.Peluse.U2Inv
