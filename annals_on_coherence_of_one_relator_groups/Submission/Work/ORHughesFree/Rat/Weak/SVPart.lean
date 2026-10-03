import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.WordModel.Defs
import Submission.Work.ORHughesFree.Rat.WordModel.sigma_rho

/-!
# The `V`-part of the word model (a self-contained copy)

`Rat/WordModel/VPart.lean` and `Rat/WordModel/rho_ofSubgroup_mem.lean` prove, for the
Dicks–Herbera–Sánchez word model `ℕ[U ♮ X]` of `Rat(U)`:

* `Rat.A V` is the carrier of a subsemiring (`Rat.ASub`);
* `Rat.A V` is closed under `⋄` (`Rat.A_ratOp`), and contains the image of `V` (`Rat.A_ofGroup_mem`);
* `Rat.A V = {x | rho x ∈ SV V}` where `SV V` is the `V`-part of `ℕ[U ♮ X]`.

Those files import `Rat/exists_source_subgroup_weak.lean` (for the definitions of `Rat.A`,
`Rat.B`, `Rat.F`), which would create a cycle if the target theorem's proof wanted to use them.
This file therefore repeats the *definitions* and the *elementary* part of that theory in the
namespace `Work.ORHughesFree.Rat.Weak`, importing only `Rat/SourceFrame.lean` and the word model
`Rat/WordModel/Defs.lean`.  The hard analytic steps (`rho (A V) ⊆ SV V`, `A_ofGroup`, `A_ratOp`,
`A_add_left`) are separate modules, so that the target theorem can import all of them.
-/

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel
open MonoidAlgebra

variable {U : Type} [Group U]

/-- `Rat.A V` is the carrier of a subsemiring of `Rat(U)`: it is the image of the ring
homomorphism `Rat(V) → Rat(U)`. -/
noncomputable def ASub (V : Subgroup U) : Subsemiring (RatU U) where
  carrier := Rat.A V
  mul_mem' := by
    rintro a b ⟨β, rfl⟩ ⟨γ, rfl⟩
    exact ⟨β * γ, by rw [map_mul]⟩
  add_mem' := by
    rintro a b ⟨β, rfl⟩ ⟨γ, rfl⟩
    exact ⟨β + γ, by rw [map_add]⟩
  zero_mem' := ⟨0, map_zero _⟩
  one_mem' := ⟨1, map_one _⟩

/-- A finite sum of elements of `Rat.A V` lies in `Rat.A V`. -/
theorem sum_mem_A {V : Subgroup U} (s : Finset (Mword U)) (f : Mword U → RatU U)
    (h : ∀ w ∈ s, f w ∈ Rat.A V) : s.sum f ∈ Rat.A V := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact (ASub V).zero_mem
  · intro a s has ih h
    rw [Finset.sum_insert has]
    exact (ASub V).add_mem (h a (Finset.mem_insert_self a s))
      (ih (fun w hw => h w (Finset.mem_insert_of_mem hw)))

theorem A_ofGroup_mem {V : Subgroup U} {v : U} (hv : v ∈ V) : RatU.ofGroup v ∈ Rat.A V :=
  ⟨RatU.ofGroup ⟨v, hv⟩, Rat.ofSubgroup_ofGroup V ⟨v, hv⟩⟩

/-- `Rat.A V` is closed under the rational operation `⋄`. -/
theorem A_ratOp_mem {V : Subgroup U} {a : RatU U} (ha : a ∈ Rat.A V) : RatU.ratOp a ∈ Rat.A V := by
  obtain ⟨β, rfl⟩ := ha
  exact ⟨RatU.ratOp β, (RatU.ofSubgroup_isHom V).map_rat β⟩

/-- A word of `M` is a `V`-word iff its value in `Rat(U)` lies in `Rat.A V`. -/
def InV (V : Subgroup U) (w : Mword U) : Prop := Mval w ∈ Rat.A V

/-- The `V`-part of `ℕ[M]`: the elements whose support consists of `V`-words. -/
def SV (V : Subgroup U) : Set (S U) := {z | ∀ w ∈ z.coeff.support, InV V w}

/-- **The `V`-part of `ℕ[M]` is additively pure**: with coefficients in `ℕ` the support of a sum
contains the supports of the summands. -/
theorem SV.add_pure {V : Subgroup U} {z z' : S U} (h : z + z' ∈ SV V) : z ∈ SV V := by
  intro w hw
  refine h w ?_
  rw [Finsupp.mem_support_iff] at hw
  rw [MonoidAlgebra.coeff_add, Finsupp.mem_support_iff, Finsupp.add_apply]
  exact fun h0 => hw (by omega)

/-- `0` lies in the `V`-part. -/
theorem SV_zero (V : Subgroup U) : (0 : S U) ∈ SV V := by
  intro w hw
  simp at hw

/-- A monomial at a `V`-word lies in the `V`-part. -/
theorem SV_single {V : Subgroup U} {w : Mword U} (hw : InV V w) (c : ℕ) :
    (single w c : S U) ∈ SV V := by
  intro w' hw'
  rw [MonoidAlgebra.coeff_single] at hw'
  have h : w' = w := Finset.mem_singleton.mp (Finsupp.support_single_subset hw')
  subst h
  exact hw

/-- The trivial word is a `V`-word. -/
theorem InV_one (V : Subgroup U) : InV V 1 := by
  show Mval (1 : Mword U) ∈ Rat.A V
  rw [Mval_one]
  exact Rat.A_one V

/-- `V`-words are closed under multiplication. -/
theorem InV_mul {V : Subgroup U} {a b : Mword U} (ha : InV V a) (hb : InV V b) :
    InV V (a * b) := by
  show Mval (a * b) ∈ Rat.A V
  rw [Mval_mul]
  exact (ASub V).mul_mem ha hb

/-- The word `u` attached to a group element `u ∈ V` is a `V`-word. -/
theorem InV_Mu {V : Subgroup U} {u : U} (hu : u ∈ V) : InV V (Mu u) := by
  show Mval (Mu u) ∈ Rat.A V
  rw [Mval_Mu]
  exact A_ofGroup_mem hu

/-- `1` lies in the `V`-part. -/
theorem SV_one (V : Subgroup U) : (1 : S U) ∈ SV V := by
  rw [MonoidAlgebra.one_def]
  exact SV_single (InV_one V) 1

/-- The `V`-part is closed under addition. -/
theorem SV_add {V : Subgroup U} {z z' : S U} (hz : z ∈ SV V) (hz' : z' ∈ SV V) :
    z + z' ∈ SV V := by
  intro w hw
  rw [Finsupp.mem_support_iff, MonoidAlgebra.coeff_add, Finsupp.add_apply] at hw
  by_cases h : z.coeff w = 0
  · rw [h, zero_add] at hw
    exact hz' w (by rwa [Finsupp.mem_support_iff])
  · exact hz w (by rwa [Finsupp.mem_support_iff])

/-- The `V`-part is closed under finite sums. -/
theorem SV_finset_sum {V : Subgroup U} {ι : Type} (s : Finset ι) (g : ι → S U)
    (h : ∀ i ∈ s, g i ∈ SV V) : s.sum g ∈ SV V := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact SV_zero V
  · intro a s has ih h
    rw [Finset.sum_insert has]
    exact SV_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The `V`-part is closed under multiplication. -/
theorem SV_mul {V : Subgroup U} {z z' : S U} (hz : z ∈ SV V) (hz' : z' ∈ SV V) :
    z * z' ∈ SV V := by
  classical
  rw [MonoidAlgebra.mul_def]
  simp only [Finsupp.sum]
  refine SV_finset_sum _ _ (fun p hp => ?_)
  exact SV_finset_sum _ _ (fun q hq => SV_single (InV_mul (hz p hp) (hz' q hq)) _)

/-- **`σ` maps the `V`-part of `ℕ[M]` into `Rat(V)`.** -/
theorem sigma_mem_A {V : Subgroup U} {z : S U} (h : z ∈ SV V) : sigma z ∈ Rat.A V := by
  rw [sigma_apply, Finsupp.sum_of_support_subset z.coeff (subset_refl _) _
    (fun i _ => by simp)]
  exact sum_mem_A _ _ (fun w hw => (ASub V).nsmul_mem (h w hw) (z.coeff w))

end Work.ORHughesFree.Rat.Weak
