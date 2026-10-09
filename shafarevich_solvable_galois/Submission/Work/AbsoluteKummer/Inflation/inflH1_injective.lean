import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Inflation

open Work.AbsoluteKummer

theorem inflH1_injective {G : Type*} [TopologicalSpace G] [Group G] {A : Type*} [Group A] {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction A M] (p : G →* A) (hpc : Work.AbsoluteKummer.IsLocallyConstant p) (hsurj : Function.Surjective p) (hact : ∀ (g : G) (m : M), g • m = p g • m) (f : Work.GroupCohomology.Z1 A M) : (∃ F : Work.AbsoluteKummer.Z1 G M, (F : G → M) = fun x : G => (f : A → M) (p x)) ∧ (∀ F : Work.AbsoluteKummer.Z1 G M, (F : G → M) = (fun x : G => (f : A → M) (p x)) → Work.AbsoluteKummer.H1π G M F = 0 → (f : A → M) ∈ Work.GroupCohomology.B1 A M) := by
  have hf : Work.GroupCohomology.IsCrossedHom A M (f : A → M) :=
    (Work.GroupCohomology.mem_Z1_iff A M (f : A → M)).mp f.2
  constructor
  · refine ⟨⟨fun g => (f : A → M) (p g), Work.AbsoluteKummer.mem_Z1_of ?_ ?_⟩, rfl⟩
    · intro g h
      show (f : A → M) (p (g * h)) = g • (f : A → M) (p h) + (f : A → M) (p g)
      rw [map_mul, hf (p g) (p h), hact g ((f : A → M) (p h))]
    · exact IsLocallyConstant.map (fun a : A => (f : A → M) a) hpc
  · intro F hF hF0
    rw [Work.AbsoluteKummer.H1π_eq_zero_iff F] at hF0
    obtain ⟨a, ha⟩ := (Work.AbsoluteKummer.mem_B1_iff (F : G → M)).mp hF0
    refine (Work.GroupCohomology.mem_B1_iff A M (f : A → M)).mpr ⟨a, ?_⟩
    funext x
    obtain ⟨g, rfl⟩ := hsurj x
    have hd0 : g • a - a = (F : G → M) g := by
      have h := congrFun ha g
      simpa only [Work.GroupCohomology.d0_apply] using h
    have hFg : (F : G → M) g = (f : A → M) (p g) := congrFun hF g
    show p g • a - a = (f : A → M) (p g)
    rw [← hact g a]
    exact hd0.trans hFg

end Work.AbsoluteKummer.Inflation
