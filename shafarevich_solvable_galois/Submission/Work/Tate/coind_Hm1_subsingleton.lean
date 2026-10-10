import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.CoindModule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

section CoindVanishing

variable {G : Type*} [Group G] [Fintype G] {R : Type*} [AddCommGroup R]

/-- The point mass at `h ∈ G` with value `r ∈ R`, i.e. the function `G → R` that takes the value
`r` at `h` and `0` everywhere else. -/
noncomputable def pt (h : G) (r : R) : G → R := fun x => if x = h then r else 0

theorem pt_self (h : G) (r : R) : pt h r h = r := by
  show (if h = h then r else 0) = r
  exact if_pos rfl

theorem pt_eq_zero_of_ne {h x : G} (hx : x ≠ h) (r : R) : pt h r x = 0 := by
  show (if x = h then r else 0) = 0
  exact if_neg hx

/-- The coinduced action permutes the point masses. -/
theorem coind_smul_pt (g h : G) (r : R) : g • pt h r = pt (h * g⁻¹) r := by
  funext x
  rw [coind_smul_eq]
  show (if x * g = h then r else 0) = (if x = h * g⁻¹ then r else 0)
  by_cases hx : x * g = h
  · have hxx : x = h * g⁻¹ := by rw [← hx]; group
    rw [if_pos hx, if_pos hxx]
  · have hxx : x ≠ h * g⁻¹ := by intro hc; exact hx (by rw [hc]; group)
    rw [if_neg hx, if_neg hxx]

/-- The difference of two point masses with the same value is an element of the augmentation
submodule. -/
theorem pt_sub_pt_one_mem_augmentation (h : G) (r : R) :
    pt h r - pt 1 r ∈ augmentation G (G → R) := by
  have h1 : h⁻¹ • pt 1 r = pt h r := by rw [coind_smul_pt]; simp
  have h2 := smul_sub_self_mem_augmentation (G := G) (A := G → R) h⁻¹ (pt 1 r)
  rwa [h1] at h2

/-- Every function is the sum of the point masses describing its values. -/
theorem sum_pt_eq_self (f : G → R) : (∑ h : G, pt h (f h)) = f := by
  funext x
  rw [Finset.sum_apply, Finset.sum_eq_single x]
  · simp [pt_self]
  · intro b _ hb
    exact pt_eq_zero_of_ne (fun hc => hb hc.symm) (f b)
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- The augmentation submodule of the coinduced module is exactly the kernel of the norm. -/
theorem coind_augmentation_eq_ker_norm :
    augmentation G (G → R) = (norm G (G → R)).ker := by
  apply le_antisymm
  · exact augmentation_le_ker_norm
  · intro f hf
    have hsum : (∑ h : G, f h) = 0 := by
      have h1 := congrFun hf 1
      rw [norm_apply] at h1
      simpa [Finset.sum_apply, coind_smul_eq] using h1
    have hdecomp : f = ∑ h : G, (pt h (f h) - pt 1 (f h)) := by
      funext x
      rw [Finset.sum_apply]
      simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib]
      have h1 : (∑ h : G, pt h (f h) x) = f x := by
        rw [Finset.sum_eq_single x]
        · simp [pt_self]
        · intro b _ hb; exact pt_eq_zero_of_ne (fun hc => hb hc.symm) (f b)
        · intro hx; exact absurd (Finset.mem_univ x) hx
      have h2 : (∑ h : G, pt 1 (f h) x) = 0 := by
        by_cases hx : x = 1
        · subst hx
          rw [show (∑ h : G, pt (1 : G) (f h) 1) = ∑ h : G, f h from
            Finset.sum_congr rfl (fun h _ => by simp [pt])]
          exact hsum
        · have hz : ∀ h : G, pt 1 (f h) x = 0 := by
            intro h
            show (if x = (1 : G) then f h else 0) = 0
            exact if_neg hx
          rw [show (∑ h : G, pt (1 : G) (f h) x) = ∑ _h : G, (0 : R) from
            Finset.sum_congr rfl (fun h _ => hz h)]
          simp
      rw [h1, h2, sub_zero]
    rw [hdecomp]
    exact AddSubgroup.sum_mem _ (fun h _ => pt_sub_pt_one_mem_augmentation h (f h))

/-- `Ĥ⁻¹(G, G → R) = 0` for a finite group `G` and an additive commutative group `R`. -/
theorem coind_Hm1_subsingleton {G : Type*} [Group G] [Fintype G] {R : Type*} [AddCommGroup R] :
    Subsingleton (Work.Tate.Hm1 G (G → R)) :=
  ⟨fun x y => by
    have hzero : ∀ x : Work.Tate.Hm1 G (G → R), x = 0 := fun x =>
      Hm1_induction_on (C := fun y : Work.Tate.Hm1 G (G → R) => y = 0) x
        (fun a => (Hm1π_eq_zero_iff a).mpr
          (coind_augmentation_eq_ker_norm.ge (AddMonoidHom.mem_ker.mp a.2)))
    rw [hzero x, hzero y]⟩

end CoindVanishing

end Work.Tate
