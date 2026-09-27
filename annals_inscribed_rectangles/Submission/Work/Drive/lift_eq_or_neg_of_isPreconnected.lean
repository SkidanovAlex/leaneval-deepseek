import Mathlib
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.isCoveringMap_projOfUnitSphere

namespace Work.Drive

namespace Work.Drive

open scoped Manifold ContDiff

/-! ### Two local helpers -/

/-- **The antipodal map has no fixed point on the unit sphere.**  If `a = -a` on `Sⁿ` then `a = 0`,
contradicting `‖a‖ = 1`; equivalently `dist a (-a) = 2 ≠ 0`.  This is the only non-degeneracy fact
needed to turn the pointwise dichotomy `v y = ± u y` into a dichotomy of *disjoint* loci. -/
lemma unitSphere_ne_negSphere {n : ℕ} (a : unitSphere n) : a ≠ negSphere a := by
  intro h
  have hd : dist a (negSphere a) = 2 := by
    rw [Subtype.dist_eq, negSphere_coe, dist_eq_norm]
    have h2 : a.1 - -a.1 = (2 : ℝ) • a.1 := by module
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      norm_coe_unitSphere a]
    norm_num
  rw [← h, dist_self] at hd
  norm_num at hd

/-- **The fibre dichotomy of `S³ → ℝP³`**: two unit vectors with the same image in `ℝP³` are equal
or antipodal.  This is the forward direction of the fibre computation
`Work.Drive.sphere_quotient_projective` for `projOfUnitSphere`, proved here directly (rather than
through the copy in `Work.Drive.isCoveringMap_projOfUnitSphere`) so that this file depends only on
the stable interface `projOfUnitSphere_eq` of `Work.Drive.ProjectiveTopology`. -/
lemma projOfUnitSphere_eq_or_eq_negSphere {a b : unitSphere 3}
    (h : projOfUnitSphere a = projOfUnitSphere b) : a = b ∨ a = negSphere b := by
  rw [projOfUnitSphere_eq a, projOfUnitSphere_eq b,
    sphere_quotient_projective.2 a.1 b.1 (norm_coe_unitSphere a) (norm_coe_unitSphere b)] at h
  rcases h with h | h
  · exact Or.inl (Subtype.ext h.symm)
  · refine Or.inr (Subtype.ext ?_)
    show a.1 = -b.1
    rw [h, neg_neg]

/-- **Two continuous unit lifts of the same map into `ℝP³` on a connected set agree up to sign.**
If `S` is preconnected and `v, u : ℝ² → S³` are continuous on `S` with
`projOfUnitSphere (v y) = projOfUnitSphere (u y)` for all `y ∈ S`, then either `v = u` on `S` or
`v = -u` on `S`.  (`projOfUnitSphere_eq_iff` gives the pointwise dichotomy, and the sign is
constant because `S` is preconnected.) -/
theorem lift_eq_or_neg_of_isPreconnected
    (hcov : IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3)))
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : IsPreconnected S)
    {v u : EuclideanSpace ℝ (Fin 2) → Work.Drive.unitSphere 3}
    (hv : ContinuousOn v S) (hu : ContinuousOn u S)
    (hvu : ∀ y ∈ S, Work.Drive.projOfUnitSphere (v y) = Work.Drive.projOfUnitSphere (u y))
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ S) :
    (∀ y ∈ S, v y = u y) ∨ (∀ y ∈ S, v y = Work.Drive.negSphere (u y)) := by
  -- pointwise dichotomy: `v y` and `u y` differ by at most a sign
  have hdich : ∀ y : S, v y.1 = u y.1 ∨ v y.1 = negSphere (u y.1) := fun y =>
    projOfUnitSphere_eq_or_eq_negSphere (hvu y.1 y.2)
  have hV : Continuous (fun y : S => v y.1) := hv.domRestrict
  have hU : Continuous (fun y : S => u y.1) := hu.domRestrict
  -- the "same sign" and "opposite sign" loci, as subsets of the (topological) space `S`
  let A : Set S := {y | v y.1 = u y.1}
  let B : Set S := {y | v y.1 = negSphere (u y.1)}
  have hclA : IsClosed A := isClosed_eq hV hU
  have hclB : IsClosed B := isClosed_eq hV (continuous_negSphere.comp hU)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro y hyA hyB
    exact unitSphere_ne_negSphere (u y.1) (by rw [← hyB, hyA])
  have hcover : A ∪ B = Set.univ := by
    ext y
    exact ⟨fun _ => trivial, fun _ => hdich y⟩
  -- `A` and `B` partition `S`, so each of them is clopen
  have hAcompl : A = Bᶜ := by
    ext y
    constructor
    · intro hy
      simp only [Set.mem_compl_iff]
      intro hyB
      exact Set.disjoint_left.mp hdisj hy hyB
    · intro hy
      have h : y ∈ A ∪ B := by rw [hcover]; trivial
      rcases h with h | h
      · exact h
      · exact absurd h hy
  have hAclopen : IsClopen A := ⟨hclA, by rw [hAcompl]; exact hclB.isOpen_compl⟩
  have hBcompl : B = Aᶜ := by rw [hAcompl, compl_compl]
  have hBclopen : IsClopen B := ⟨hclB, by rw [hBcompl]; exact hclA.isOpen_compl⟩
  -- on a preconnected space a clopen set is empty or everything
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace hS
  rcases hdich ⟨p, hp⟩ with hpu | hpn
  · left
    have hmem : (⟨p, hp⟩ : S) ∈ A := hpu
    have hsub := (isPreconnected_univ (α := S)).subset_isClopen hAclopen ⟨⟨p, hp⟩, trivial, hmem⟩
    intro y hy
    have hmem' : (⟨y, hy⟩ : S) ∈ A := hsub (Set.mem_univ _)
    exact hmem'
  · right
    have hmem : (⟨p, hp⟩ : S) ∈ B := hpn
    have hsub := (isPreconnected_univ (α := S)).subset_isClopen hBclopen ⟨⟨p, hp⟩, trivial, hmem⟩
    intro y hy
    have hmem' : (⟨y, hy⟩ : S) ∈ B := hsub (Set.mem_univ _)
    exact hmem'

end Work.Drive

/-- The statement under the name the requester asked for,
`Work.Drive.lift_eq_or_neg_of_isPreconnected`.  The declaration above sits in the *doubly* nested
namespace `Work.Drive.Work.Drive` because the generated file repeated the `namespace Work.Drive`
line carried by the requested statement; this alias exposes the same statement, by the same proof,
at the plain name. -/
theorem lift_eq_or_neg_of_isPreconnected
    (hcov : IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3)))
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : IsPreconnected S)
    {v u : EuclideanSpace ℝ (Fin 2) → Work.Drive.unitSphere 3}
    (hv : ContinuousOn v S) (hu : ContinuousOn u S)
    (hvu : ∀ y ∈ S, Work.Drive.projOfUnitSphere (v y) = Work.Drive.projOfUnitSphere (u y))
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ S) :
    (∀ y ∈ S, v y = u y) ∨ (∀ y ∈ S, v y = Work.Drive.negSphere (u y)) :=
  _root_.Work.Drive.Work.Drive.lift_eq_or_neg_of_isPreconnected hcov hS hv hu hvu hp
