import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.ColourSubgroup

/-!
# The colour-subgroup of a tree has finite index

Fix a `Bool`-valued 2-colouring `c` of a tree `V` (so the two ends of every edge have different
colours, `Work.ORBassSerre.Tree.Walk.bipartition_exists`).  The subgroup

`colourSubgroup c = {g : G | ∀ w, c (g • w) = c w}`

of elements preserving `c` has index at most two: the `G`-orbit of `c` inside the set of
colourings consists of at most two colourings, since, `V` being connected, a colouring is
determined by its value at a single vertex (`Work.ORBassSerre.Tree.Walk.bipartition_eq_of_agree`).

Concretely, if `g₁ H` and `g₂ H` are two left cosets whose "translated colourings agree at a base
vertex `v₀`", then those two translated colourings agree everywhere, which forces
`g₂⁻¹ g₁ ∈ H` and hence `g₁ H = g₂ H`.  Thus the map `g H ↦ c (g⁻¹ • v₀)` from `G ⧸ colourSubgroup c`
to `Bool` is injective, so the quotient is finite and the subgroup has finite index.
-/

namespace Work.ORBassSerre.Action.Structure

theorem finiteIndex_colourSubgroup {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) {c : V → Bool}
    (hc : ∀ e : Quiver.Total V, c e.left ≠ c e.right) :
    (Work.ORBassSerre.Action.Structure.colourSubgroup (G := G) c).FiniteIndex := by
  by_cases hV : Nonempty V
  · -- Nonempty case: inject the quotient into `Bool` via the colour at a base vertex.
    obtain ⟨v₀⟩ := hV
    let H := colourSubgroup (G := G) c
    -- The value of the translate `w ↦ c (g⁻¹ • w)` at the base vertex.
    let φ : G → Bool := fun g => c (g⁻¹ • v₀)
    -- `φ` is constant on left cosets of `H`.
    have hφ : ∀ g₁ g₂ : G, (QuotientGroup.leftRel H) g₁ g₂ → φ g₁ = φ g₂ := by
      intro g₁ g₂ hrel
      rw [QuotientGroup.leftRel_apply] at hrel
      have hmem : ∀ w : V, c ((g₁⁻¹ * g₂) • w) = c w := hrel
      show c (g₁⁻¹ • v₀) = c (g₂⁻¹ • v₀)
      have h := hmem (g₂⁻¹ • v₀)
      rw [mul_smul, smul_inv_smul] at h
      exact h
    -- Hence it descends to the quotient.
    let F : G ⧸ H → Bool := Quotient.lift φ hφ
    -- ... and the descended map is injective.
    have hF : Function.Injective F := by
      intro x y
      refine Quotient.inductionOn x (fun g₁ => ?_)
      refine Quotient.inductionOn y (fun g₂ => ?_)
      intro hxy
      change φ g₁ = φ g₂ at hxy
      show Quotient.mk _ g₁ = Quotient.mk _ g₂
      -- The two translated colourings agree at `v₀`, ...
      have hv : (fun w => c (g₁⁻¹ • w)) v₀ = (fun w => c (g₂⁻¹ • w)) v₀ := hxy
      -- ... so, both being 2-colourings of the tree, they agree everywhere.
      have hcc : (fun w => c (g₁⁻¹ • w)) = (fun w => c (g₂⁻¹ • w)) :=
        Work.ORBassSerre.Tree.Walk.bipartition_eq_of_agree
          (c := fun w => c (g₁⁻¹ • w)) (c' := fun w => c (g₂⁻¹ • w)) hT
          (colouring_smul hc g₁⁻¹) (colouring_smul hc g₂⁻¹) hv
      have hg2g1 : g₂⁻¹ * g₁ ∈ H := by
        show ∀ w : V, c ((g₂⁻¹ * g₁) • w) = c w
        intro w
        have h := congrFun hcc (g₁ • w)
        rw [inv_smul_smul] at h
        rw [← mul_smul] at h
        exact h.symm
      apply Quotient.sound
      change (QuotientGroup.leftRel H) g₁ g₂
      rw [QuotientGroup.leftRel_apply]
      rw [show g₁⁻¹ * g₂ = (g₂⁻¹ * g₁)⁻¹ by group]
      exact H.inv_mem hg2g1
    -- An injective map into the finite type `Bool` makes the quotient finite.
    exact Subgroup.finiteIndex_iff_finite_quotient.mpr
      (@Finite.of_fintype (G ⧸ H) (Fintype.ofInjective F hF))
  · -- Empty case: `colourSubgroup c = ⊤` vacuously.
    have htop : colourSubgroup (G := G) c = ⊤ := by
      ext g
      constructor
      · intro _; trivial
      · intro _ w; exact (hV ⟨w⟩).elim
    rw [htop]
    infer_instance

end Work.ORBassSerre.Action.Structure
