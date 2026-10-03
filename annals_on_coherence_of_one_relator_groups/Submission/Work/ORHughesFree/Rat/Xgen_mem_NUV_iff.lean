import Mathlib
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.Ugen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- `Rat.A V` is closed under multiplication. -/
private lemma A_mul_mem' {V : Subgroup U} {x y : RatU U} (hx : x ∈ A V) (hy : y ∈ A V) :
    x * y ∈ A V := by
  obtain ⟨β, rfl⟩ := hx
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨β * γ, map_mul (RatU.ofSubgroup V) β γ⟩

/-- `ofGroup u ∈ Rat.A V` for `u ∈ V`. -/
private lemma ofGroup_mem_A' {V : Subgroup U} {u : U} (hu : u ∈ V) :
    RatU.ofGroup u ∈ A V :=
  ⟨RatU.ofGroup ⟨u, hu⟩, ofSubgroup_ofGroup V ⟨u, hu⟩⟩

/-- **A single `X`-letter lies in the `V`-part of `U ♮ X` exactly when it is a `V`-letter.**

The reverse implication is the generator `Orbit.Xgen_mem_NUV`.  For the forward implication apply
the quotient-level first-letter recursion `Xgen_mem_closure_iff` to the product `Xgen a * 1`: it
produces `v : U` with `actR v a ∈ Rat.A V` and `Ugen v⁻¹ ∈ NUV V`.  By `Ugen_mem_NUV_iff` the
latter says `v ∈ V`, and then `a = ofGroup v * actR v a` is a product of two elements of `Rat.A V`,
hence lies in `Rat.A V`. -/
theorem Xgen_mem_NUV_iff {U : Type} [Group U] (V : Subgroup U) (a : Work.ORHughesFree.RatU U) :
    Work.ORHughesFree.Rat.FreeProduct.NU.Xgen a ∈ Work.ORHughesFree.Rat.Orbit.NUV V ↔
      a ∈ Work.ORHughesFree.Rat.A V := by
  constructor
  · intro h
    have h' : FreeProduct.NU.Xgen a * 1 ∈ NUV V := by rw [mul_one]; exact h
    obtain ⟨v, hv1, hv2⟩ := (Xgen_mem_closure_iff V a 1).mp h'
    have hvmem : FreeProduct.NU.Ugen v⁻¹ ∈ Orbit.NUV V := by
      rw [mul_one] at hv2; exact hv2
    have hvinv : v⁻¹ ∈ V := (Ugen_mem_NUV_iff V v⁻¹).mp hvmem
    have hv : v ∈ V := by simpa using inv_mem hvinv
    have ha : a = RatU.ofGroup v * FreeProduct.actR v a := by
      rw [FreeProduct.actR, ← mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one,
        one_mul]
    rw [ha]
    exact A_mul_mem' (ofGroup_mem_A' hv) hv1
  · intro ha
    exact Orbit.Xgen_mem_NUV ha

end Work.ORHughesFree.Rat
