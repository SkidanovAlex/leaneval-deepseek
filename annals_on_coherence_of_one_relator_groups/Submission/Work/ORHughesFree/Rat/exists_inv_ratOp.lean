import Mathlib
import Submission.Work.ORHughesFree.Rat.exists_source_subgroup_weak
import Submission.Work.ORHughesFree.Rat.mem_FL_iff_exists
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.mem_ofGroup_mul_A_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.Ugen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Weak.SVPart

/-!
# The `⋄`-branch of the induction of [DHS04, Theorem 5.7]

The invariant `Rat.Inv x S` of `Rat/exists_source_subgroup_weak.lean` says that `S` is the least
element of `Rat.F x` and that the *right* tail set

`Orbit.T (supp (Psi x)) V = {u : U | ∀ p ∈ supp (Psi x), p * Ugen u ∈ NUV V}`

of `x` at any `V ∈ Rat.F x` grows out of the tail set at `S` only by right multiplication by `V`.

Because of the `⋄`-duality `Rat.F (⋄x) = Rat.FL x`, the `⋄`-branch of the induction has to feed the
invariant at `⋄x` from the *left* family `Rat.FL x`.  The bridge is the identity

`Psi (⋄x) = single (Xgen x) 1`

(`FreeProduct.Psi_ratOp`), so the support of `Psi (⋄x)` is the single `X`-letter `Xgen x`, and

`u ∈ Orbit.T {Xgen x} V ↔ Xgen x * Ugen u ∈ NUV V ↔ Xgen (actR u x) ∈ NUV V ↔ actR u x ∈ A V`,

i.e. `u ∈ Orbit.T (supp (Psi (⋄x))) V` iff the *left* translate `φ u⁻¹ · x` lies in `Rat.A V`.
With `mem_ofGroup_mul_A_iff` the latter is exactly `u⁻¹ ∈ LT x V`, where

`LT x V = {u : U | ∀ p ∈ supp (Psi x), Ugen u * p ∈ NUV V}`

is the set of *left tails* of `x` appearing in the hypothesis of the theorem.  This file proves that
identity (`mem_T_ratOp`) and then converts the left-tail law postulated for `x` at the least element
of `Rat.FL x` into the right tail law required for `⋄x`, by inversion of the parameter.
-/

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- The set of **left tails** of `x` at level `V`: the group elements `u` with `Ugen u` shifting the
whole support of `Psi x` into the `V`-part `Orbit.NUV V` of `U ♮ X`.  By `mem_ofGroup_mul_A_iff`
this is the set of `u` with `φu · x ∈ Rat.A V`. -/
def LT (x : RatU U) (V : Subgroup U) : Set U :=
  {u : U | ∀ p ∈ (FreeProduct.Psi x).coeff.support,
    FreeProduct.NU.Ugen u * p ∈ Orbit.NUV V}

/-- `LT x V` is the set of `u` with `φu · x ∈ Rat.A V`. -/
theorem mem_LT_iff (x : RatU U) (V : Subgroup U) (u : U) :
    u ∈ LT x V ↔ RatU.ofGroup u * x ∈ A V :=
  (mem_ofGroup_mul_A_iff V x u).symm

/-- The group element `ofGroup v` absorbs `actR v a` back to `a`. -/
theorem ofGroup_mul_actR' (v : U) (a : RatU U) :
    RatU.ofGroup v * FreeProduct.actR v a = a := by
  simp only [FreeProduct.actR]
  rw [← mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, one_mul]

/-- **No junk for a single `X`-letter**: the `V`-part `Orbit.NUV V` of `U ♮ X` meets the
`X`-letters exactly in the letters over `Rat.A V`.

The forward implication is the first-letter recursion `Xgen_mem_closure_iff` at `q = 1` together
with `Ugen_mem_NUV_iff`; the backward implication is a generator. -/
theorem Xgen_mem_NUV_iff' (V : Subgroup U) (a : RatU U) :
    FreeProduct.NU.Xgen a ∈ Orbit.NUV V ↔ a ∈ A V := by
  constructor
  · intro h
    have h' : FreeProduct.NU.Xgen a * (1 : FreeProduct.NU U) ∈ Orbit.NUV V := by
      rw [mul_one]; exact h
    rw [Orbit.NUV] at h'
    obtain ⟨v, hv1, hv2⟩ := Xgen_mem_closure_iff V a 1 |>.mp h'
    have hv' : v⁻¹ ∈ V := by
      rw [← Ugen_mem_NUV_iff V v⁻¹, Orbit.NUV]
      simpa using hv2
    have hv : v ∈ V := (inv_mem_iff).mp hv'
    have hvU : RatU.ofGroup v ∈ A V :=
      ⟨RatU.ofGroup ⟨v, hv⟩, Rat.ofSubgroup_ofGroup V ⟨v, hv⟩⟩
    have hmem := (Weak.ASub V).mul_mem hvU hv1
    rwa [ofGroup_mul_actR'] at hmem
  · intro ha
    exact Submonoid.subset_closure (Or.inr ⟨a, ha, rfl⟩)

/-- **The bridge of the `⋄`-branch**: the right tail set of `Psi (⋄x)` is the set of inverses of
the left tails of `x`. -/
theorem mem_T_ratOp (x : RatU U) (hx : x ≠ 0) (V : Subgroup U) (u : U) :
    u ∈ Orbit.T ((FreeProduct.Psi (RatU.ratOp x)).coeff.support) V ↔ u⁻¹ ∈ LT x V := by
  have hsupp : (FreeProduct.Psi (RatU.ratOp x)).coeff.support
      = {FreeProduct.NU.Xgen x} := by
    rw [FreeProduct.Psi_ratOp hx]
    exact support_single_one_eq _
  rw [hsupp]
  have hsingle : u ∈ Orbit.T ({FreeProduct.NU.Xgen x} : Finset (FreeProduct.NU U)) V ↔
      FreeProduct.NU.Xgen x * FreeProduct.NU.Ugen u ∈ Orbit.NUV V := by
    simp [Orbit.T]
  rw [hsingle, FreeProduct.NU.Xgen_mul_Ugen, Xgen_mem_NUV_iff']
  show RatU.ofGroup u⁻¹ * x ∈ A V ↔ u⁻¹ ∈ LT x V
  exact mem_ofGroup_mul_A_iff V x u⁻¹

/-- **The bridge of the `⋄`-branch**, as an identity of sets. -/
theorem T_ratOp_eq (x : RatU U) (hx : x ≠ 0) (V : Subgroup U) :
    Orbit.T ((FreeProduct.Psi (RatU.ratOp x)).coeff.support) V = {u : U | u⁻¹ ∈ LT x V} :=
  Set.ext fun u => mem_T_ratOp x hx V u

/-- **The group-theoretic inversion step.**  If the left tails at `V` are `V` times the left tails
at `S`, then the set of inverses of the tails at `V` is the set of inverses of the tails at `S`
multiplied on the right by `V`. -/
theorem inv_setOp' {S V : Subgroup U} (L : Subgroup U → Set U)
    (h : L V = {u : U | ∃ v ∈ V, ∃ s ∈ L S, u = v * s}) :
    {u : U | u⁻¹ ∈ L V} = {u : U | ∃ s ∈ {t : U | t⁻¹ ∈ L S}, ∃ v ∈ V, u = s * v} := by
  ext u
  simp only [Set.mem_ofPred_eq]
  rw [h]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, s, hs, hvs⟩
    refine ⟨s⁻¹, ?_, v⁻¹, V.inv_mem hv, ?_⟩
    · rw [inv_inv]; exact hs
    · have h3 : u = (v * s)⁻¹ := by rw [← hvs, inv_inv]
      rw [h3, mul_inv_rev]
  · rintro ⟨s, hs, v, hv, rfl⟩
    exact ⟨v⁻¹, V.inv_mem hv, s⁻¹, hs, by rw [mul_inv_rev]⟩

theorem exists_inv_ratOp {U : Type} [Group U] {x : Work.ORHughesFree.RatU U} (hx0 : x ≠ 0)
    {Sx : Subgroup U}
    (hx : Sx ∈ Work.ORHughesFree.Rat.FL x ∧
      (∀ V : Subgroup U, V ∈ Work.ORHughesFree.Rat.FL x → Sx ≤ V) ∧
      ∀ V : Subgroup U, V ∈ Work.ORHughesFree.Rat.FL x →
        {u : U | ∀ p ∈ (Work.ORHughesFree.Rat.FreeProduct.Psi x).coeff.support,
            Work.ORHughesFree.Rat.FreeProduct.NU.Ugen u * p ∈ Work.ORHughesFree.Rat.Orbit.NUV V} =
          {u : U | ∃ v ∈ V, ∃ s ∈ {u : U | ∀ p ∈ (Work.ORHughesFree.Rat.FreeProduct.Psi x).coeff.support,
              Work.ORHughesFree.Rat.FreeProduct.NU.Ugen u * p ∈ Work.ORHughesFree.Rat.Orbit.NUV Sx},
            u = v * s}) :
    ∃ S : Subgroup U, Work.ORHughesFree.Rat.Inv (Work.ORHughesFree.RatU.ratOp x) S := by
  refine ⟨Sx, ?_, ?_, ?_⟩
  · rw [F_ratOp_eq_FL]
    exact hx.1
  · intro V hV
    rw [F_ratOp_eq_FL] at hV
    exact hx.2.1 V hV
  · intro V hV
    rw [F_ratOp_eq_FL] at hV
    have hLV : LT x V = {u : U | ∃ v ∈ V, ∃ s ∈ LT x Sx, u = v * s} := hx.2.2 V hV
    rw [T_ratOp_eq x hx0 V, T_ratOp_eq x hx0 Sx, inv_setOp' (LT x) hLV]

end Work.ORHughesFree.Rat
