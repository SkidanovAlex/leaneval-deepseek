import Mathlib
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann

namespace Work.Rep.Ore

/-- If `v * h = r` with `h`, `r ∈ N(G)` and `h` of dense range, then `v ∈ N(G)`: both sides of
`v * ρ g = ρ g * v`, composed with the dense-range map `h`, agree, so `DenseRange.equalizer`
(or `ContinuousLinearMap.ext` plus density) gives the claim. -/
theorem mem_groupVonNeumann_of_mul_eq {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (v h r : Work.ORVonNeumann.boundedEnd G) (hh : h ∈ Work.ORVonNeumann.groupVonNeumann G) (hr : r ∈ Work.ORVonNeumann.groupVonNeumann G) (hd : DenseRange h) (hv : v * h = r) : v ∈ Work.ORVonNeumann.groupVonNeumann G := by
  rw [Work.ORVonNeumann.mem_groupVonNeumann_iff]
  intro g
  set ρg : Work.ORVonNeumann.boundedEnd G := Work.ORVonNeumann.Rep.rightRegHom g with hρg
  have hcomm : h * ρg = ρg * h :=
    (Work.ORVonNeumann.mem_groupVonNeumann_iff h).mp hh g
  have rcomm : r * ρg = ρg * r :=
    (Work.ORVonNeumann.mem_groupVonNeumann_iff r).mp hr g
  have h1 : (ρg * v) * h = ρg * r := by rw [mul_assoc, hv]
  have h2 : (v * ρg) * h = ρg * r := by
    rw [mul_assoc, ← hcomm, ← mul_assoc, hv, rcomm]
  have key : (ρg * v - v * ρg) * h = 0 := by rw [sub_mul, h1, h2, sub_self]
  have hcomp : ⇑(ρg * v) ∘ ⇑h = ⇑(v * ρg) ∘ ⇑h := by
    funext x
    have hx := congrArg (fun T : Work.ORVonNeumann.boundedEnd G => T x) key
    simp only [mul_apply_eq_comp, sub_apply, zero_apply] at hx
    exact sub_eq_zero.mp hx
  have heq : ⇑(ρg * v) = ⇑(v * ρg) :=
    DenseRange.equalizer hd (ρg * v).continuous (v * ρg).continuous hcomp
  have heq_clm : ρg * v = v * ρg := ContinuousLinearMap.ext fun x => congrFun heq x
  rw [hρg]
  exact heq_clm.symm

end Work.Rep.Ore
