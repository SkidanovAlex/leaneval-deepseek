import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.exists_conjAction
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **The conjugation action of the two-point stabiliser `D = H ⊓ Hᵗ` on the root group `Q`
of a split rank-one Zassenhaus configuration**, as a homomorphism
`ρ : D →* MulAut Q`, `d ↦ (x ↦ d x d⁻¹)`, which is fixed-point-free on `Q` away from `1`:
for `d ≠ 1` in `D`, `ρ d` has no non-trivial fixed point on `Q`.

The homomorphism is `exists_conjAction h` (conjugation inside the normaliser `N_G(Q)`, in
which `D ≤ H ≤ N_G(Q)`).  The fixed-point-freeness is `dStab_fpf_on_Q H Q t h hZ`: a
non-identity `d ∈ D` fixing `1 ≠ x ∈ Q` would fix the three pairwise distinct points
`H`, `tH`, `x tH` of `Ω = G ⧸ H`, contradicting `IsZassenhaus H`. -/
theorem QSZ_fpf_conj_action {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H) :
    ∃ ρ : ↥(Submission.Blueprint.twoPoint H t) →* MulAut ↥Q,
      (∀ d : ↥(Submission.Blueprint.twoPoint H t), ∀ x : ↥Q,
        ((ρ d x : ↥Q) : G) = (d : G) * (x : G) * (d : G)⁻¹) ∧
      (∀ d : ↥(Submission.Blueprint.twoPoint H t), d ≠ 1 → ∀ x : ↥Q, ρ d x = x → x = 1) := by
  obtain ⟨ρ, hρ⟩ := exists_conjAction (H := H) (Q := Q) (t := t) h
  refine ⟨ρ, hρ, ?_⟩
  intro d hd1 x hx
  -- `ρ d x = x` says that `d` fixes `(x : G)` under conjugation
  have hconj : (d : G) * (x : G) * (d : G)⁻¹ = (x : G) := by
    calc (d : G) * (x : G) * (d : G)⁻¹ = ((ρ d x : ↥Q) : G) := (hρ d x).symm
      _ = (x : G) := by rw [hx]
  have hdval : (d : G) ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hxone : (x : G) = 1 :=
    Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t h hZ (d : G) d.2 hdval (x : G) x.2 hconj
  exact Subtype.ext (by simpa using hxone)

end Work.ZassenhausSuzuki
