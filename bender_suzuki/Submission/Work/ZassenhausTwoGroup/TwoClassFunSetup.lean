import Mathlib
import Submission.Work.Induction.All
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Setup for the two-double-coset induction computation (`ZassenhausTwoGroup`)

This module provides the small pieces of vocabulary used by
`Work.ZassenhausTwoGroup.cfInner_indFun_twoClassFun_twoDoubleCoset` and by the lemmas
that compute the individual contributions to it.

* `Work.ZassenhausTwoGroup.extFun H f` is the extension by zero to `G` of a function
  `f : H → ℂ` on a subgroup `H ≤ G`; the defining summand of `indFun` is `extFun H f`
  evaluated at `x * g * x⁻¹`.
* `Work.ZassenhausTwoGroup.dcos H t` is the double coset `H t H` as a set.
-/

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise

namespace Work.ZassenhausTwoGroup

variable {G : Type*} [Group G]

/-- Extension by zero to `G` of a complex-valued function on a subgroup `H ≤ G`: the
function which agrees with `f` on `H` and vanishes outside `H`. -/
def extFun (H : Subgroup G) (f : H → ℂ) : G → ℂ :=
  fun g => if hg : g ∈ H then f ⟨g, hg⟩ else 0

theorem extFun_of_mem {H : Subgroup G} {f : H → ℂ} {g : G} (hg : g ∈ H) :
    extFun H f g = f ⟨g, hg⟩ := dif_pos hg

theorem extFun_of_notMem {H : Subgroup G} {f : H → ℂ} {g : G} (hg : g ∉ H) :
    extFun H f g = 0 := dif_neg hg

/-- `extFun H f` is invariant under conjugation by elements of `H` when `f` is a class
function on `H`. -/
theorem extFun_conj {H : Subgroup G} {f : H → ℂ} (hf : Work.CharCore.IsClassFun f)
    (a : H) (v : G) : extFun H f ((a : G) * v * (a : G)⁻¹) = extFun H f v := by
  by_cases hv : v ∈ H
  · have hav : (a : G) * v * (a : G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem a.2 hv) (H.inv_mem a.2)
    have he : (⟨(a : G) * v * (a : G)⁻¹, hav⟩ : H) = a * ⟨v, hv⟩ * a⁻¹ :=
      Subtype.ext (by simp)
    rw [extFun_of_mem hav, extFun_of_mem hv, he]
    exact hf ⟨v, hv⟩ a
  · have hav : (a : G) * v * (a : G)⁻¹ ∉ H := by
      intro hmem
      have hmem' : v ∈ H := by
        have hmem'' : (a : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * (a : G) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem a.2) hmem) a.2
        rwa [show (a : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * (a : G) = v from by group] at hmem''
      exact hv hmem'
    rw [extFun_of_notMem hav, extFun_of_notMem hv]

/-- The defining summand of `indFun` is `extFun` evaluated at the conjugate. -/
theorem indFun_eq_sum_extFun (H : Subgroup G) [Fintype G] [Fintype H] (φ : H → ℂ) (g : G) :
    Work.Induction.indFun H φ g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extFun H φ (x * g * x⁻¹) := by
  simp only [Work.Induction.indFun_apply_def, extFun]

/-- Summing `extFun H f g * F g` over `g : G` is the same as summing `f h * F h` over `h : H`. -/
theorem sum_extFun_mul (H : Subgroup G) [Fintype G] [Fintype H] (f : H → ℂ) (F : G → ℂ) :
    (∑ g : G, extFun H f g * F g) = ∑ h : H, f h * F h := by
  have h1 : (∑ g : G, extFun H f g * F g)
      = ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ H), extFun H f g * F g := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases hg : g ∈ H <;> simp [extFun, hg]
  rw [h1]
  rw [show (∑ g ∈ Finset.univ.filter (fun g : G => g ∈ H), extFun H f g * F g)
        = ∑ g : Subtype (fun g : G => g ∈ H), extFun H f g * F g from
      Finset.sum_subtype _ (fun g => by simp) _]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [extFun_of_mem h.2]

/-- The double coset `H t H` as a set of elements of `G`. -/
def dcos (H : Subgroup G) (t : G) : Set G := {z : G | ∃ a b : H, z = (a : G) * t * (b : G)}

theorem mem_dcos_iff {H : Subgroup G} {t z : G} :
    z ∈ dcos H t ↔ ∃ a b : H, z = (a : G) * t * (b : G) := Iff.rfl

end Work.ZassenhausTwoGroup
