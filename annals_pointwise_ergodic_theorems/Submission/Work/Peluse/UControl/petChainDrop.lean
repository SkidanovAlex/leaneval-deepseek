import Mathlib
import Submission.Work.Peluse.UControl.PetStepChain

/-!
# Dropping the constant slots of a PET state

`PetStateP.drop S J` removes the slots `i ∈ J` from the index set `ι` and multiplies the — now
`y`-independent — values `S.F i (x + (S.P i a).eval 0)` into the base function `f a x`.  The
correlation `PetStateP.lam` is unchanged, because for a constant slot the factor
`S.F i (x + (S.P i a).eval (y : ℤ))` equals `S.F i (x + (S.P i a).eval 0)` for every `y`, so the
product over the slots factors into the `J`-part (independent of `y`, hence pulled out of the
`y`-sum) and the `Jᶜ`-part.

The two steps are `drop_prod_eq` (the pointwise factorisation of the slot product) and
`drop_summand` (the resulting identity of the `y`-summands), after which the equality of the
correlations is a `Finset.sum_congr` / `tsum_congr`.
-/

open scoped BigOperators

namespace Work.Peluse.UControl.PetStep

/-- **Pointwise factorisation of the slot product.**  Multiplying the `Jᶜ`-product of a dropped
state by the `y`-independent `J`-product `∏_{i ∈ J} S.F i (x + (S.P i a).eval 0)` recovers the full
product over `S.ι`; this is where the hypothesis that the slots in `J` are constant in `y` is
used. -/
private lemma drop_prod_eq (S : PetStateP) (J : Finset S.ι)
    (hc : ∀ i ∈ J, ∀ a y, (S.P i a).eval y = (S.P i a).eval 0)
    (a : S.Ω) (x y : ℤ) :
    (∏ i ∈ J, S.F i (x + (S.P i a).eval 0)) *
        (∏ i : (S.drop J).ι, (S.drop J).F i (x + ((S.drop J).P i a).eval y))
      = ∏ i : S.ι, S.F i (x + (S.P i a).eval y) := by
  have hH : (∏ i : (S.drop J).ι, (S.drop J).F i (x + ((S.drop J).P i a).eval y))
        = ∏ i ∈ Jᶜ, S.F i (x + (S.P i a).eval y) :=
    Finset.prod_coe_sort (Jᶜ) (fun i => S.F i (x + (S.P i a).eval y))
  have hJ : (∏ i ∈ J, S.F i (x + (S.P i a).eval 0)) =
      ∏ i ∈ J, S.F i (x + (S.P i a).eval y) :=
    Finset.prod_congr rfl (fun i hi => by rw [hc i hi a y])
  rw [hH, hJ, Finset.prod_mul_prod_compl]

/-- **The `y`-summand identity.**  The summand of the dropped state equals that of the original
state: the `J`-product is pulled out of the `y`-sum (`Finset.mul_sum`) and then absorbed by
`drop_prod_eq`. -/
private lemma drop_summand (S : PetStateP) (J : Finset S.ι)
    (hc : ∀ i ∈ J, ∀ a y, (S.P i a).eval y = (S.P i a).eval 0)
    (a : S.Ω) (M : ℕ) (x : ℤ) :
    (S.drop J).f a x *
        (∑ y ∈ Finset.Icc 1 M, ∏ i, (S.drop J).F i (x + ((S.drop J).P i a).eval (y:ℤ)))
      = S.f a x * ∑ y ∈ Finset.Icc 1 M, ∏ i, S.F i (x + (S.P i a).eval (y:ℤ)) := by
  have hkey : ∀ y : ℤ, (∏ i ∈ J, S.F i (x + (S.P i a).eval 0)) *
      (∏ i : (S.drop J).ι, (S.drop J).F i (x + ((S.drop J).P i a).eval y))
      = ∏ i : S.ι, S.F i (x + (S.P i a).eval y) := fun y => drop_prod_eq S J hc a x y
  have hf : (S.drop J).f a x = S.f a x * ∏ i ∈ J, S.F i (x + (S.P i a).eval 0) := rfl
  rw [hf]
  calc (S.f a x * ∏ i ∈ J, S.F i (x + (S.P i a).eval 0)) *
        (∑ y ∈ Finset.Icc 1 M,
          ∏ i : (S.drop J).ι, (S.drop J).F i (x + ((S.drop J).P i a).eval ↑y))
      = S.f a x * ((∏ i ∈ J, S.F i (x + (S.P i a).eval 0)) *
        (∑ y ∈ Finset.Icc 1 M,
          ∏ i : (S.drop J).ι, (S.drop J).F i (x + ((S.drop J).P i a).eval ↑y))) := by ring
    _ = S.f a x * (∑ y ∈ Finset.Icc 1 M, (∏ i ∈ J, S.F i (x + (S.P i a).eval 0)) *
          (∏ i : (S.drop J).ι, (S.drop J).F i (x + ((S.drop J).P i a).eval ↑y))) := by
        rw [Finset.mul_sum]
    _ = S.f a x * ∑ y ∈ Finset.Icc 1 M, ∏ i : S.ι, S.F i (x + (S.P i a).eval ↑y) := by
        congr 1
        exact Finset.sum_congr rfl (fun y _ => hkey y)

end Work.Peluse.UControl.PetStep

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep

/-- **Dropping constant slots leaves the correlation unchanged.**  If every slot `i ∈ J` has a
shift polynomial that is constant in `y` (`hc`), then removing those slots and multiplying their
`y`-independent values into the base function does not change `PetStateP.lam`. -/
theorem petChainDrop (S : Work.Peluse.UControl.PetStep.PetStateP) (J : Finset S.ι)
    (hc : ∀ i ∈ J, ∀ a y, (S.P i a).eval y = (S.P i a).eval 0) (N M : ℕ) :
    (S.drop J).lam N M = S.lam N M := by
  classical
  unfold PetStateP.lam
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (S.drop J).ν a = S.ν a from rfl]
  rw [show (∑' (x : ℤ), (S.drop J).f a x * ∑ y ∈ Finset.Icc 1 M,
              ∏ i, (S.drop J).F i (x + ((S.drop J).P i a).eval (y:ℤ)))
        = ∑' (x : ℤ), S.f a x * ∑ y ∈ Finset.Icc 1 M,
              ∏ i, S.F i (x + (S.P i a).eval (y:ℤ)) from
      tsum_congr (fun x => drop_summand S J hc a M x)]

end Work.Peluse.UControl
