import Mathlib
import Submission.Work.Tubular.TubeClass.PunctComplReduction
import Submission.Work.Tubular.TubeClass.ComplPointMan8All
import Submission.Work.Tubular.onePoint_compl_zero
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.onePoint_cokernel_pi_compl_point_bijective
import Submission.Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

/-!
# From the vanishing of the punctured normal pair to the vanishing of `H_{8+k}(ν⁺ ∖ {x₀})`

The hypothesis `h` is the vanishing of the relative homology `H_{8+k}(P, Q)` of the **punctured
normal pair**

* `P = ν ∖ {x₀}` — the normal total space with the point `x₀ = 0_{v₀}` of the zero section removed,
* `Q = {p ∈ P | ‖p‖ ≠ 0}` — the further removal of the zero section,

which is the "local degree" input of the tubular chapter
(`Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing`).

The conclusion is the vanishing of `H_{8+k}(ν⁺ ∖ {x₀})`, where `ν⁺ = OnePoint (NormaTotal E)` is the
Thom space.  The two are equivalent, and this file proves the implication used in the chapter.

## Proof

Write `X = ν⁺ ∖ {x₀}`, `A = onePointNonzero E = ν⁺ ∖ (zero section)` and `Z = {∞}` (the point at
infinity of the Thom space).  Then

* `H_{8+k}(X) ≅ H_{8+k}(X, A)`: the long exact sequence of the pair `(X, A)`, whose neighbouring
  terms vanish because `A` is contractible
  (`Work.Tubular.TubeClass.punctComplTopHomologyVanishing_of_isZero_pair`);
* `H_{8+k}(X, A) ≅ H_{8+k}(X ∖ {∞}, A ∖ {∞})`: **excision** of `{∞}` — `A` is open in `X` (its
  complement is the trace of the compact zero section), so `interior A = A ⊇ {∞} = closure {∞}`
  (`Work.Cohomology.excision`);
* `H_{8+k}(X ∖ {∞}, A ∖ {∞}) ≅ H_{8+k}(P, Q)`: the homeomorphism of pairs `X ∖ {∞} ≅ P` which is
  `Work.Tubular.TubeClass.homeomorph_punctPair`; it identifies `A ∖ {∞} = (ν ∖ 0)` with `Q`
  (`Work.Tubular.nonempty_relChains_homology_homeo`).

Chaining the three isomorphisms gives `H_{8+k}(X, A) ≅ H_{8+k}(P, Q)`, so `h` transports to
`H_{8+k}(X, A) = 0` and hence to `H_{8+k}(X) = 0`.
-/

namespace Work.Tubular.PuncturedDiscPair

open CategoryTheory Limits
open scoped Topology

noncomputable section

theorem punctCompl_of_pairVanishing {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (h : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of {p : Work.Tubular.NormalTotal E //
        p ≠ Work.Tubular.TubeClass.zeroNormalPt E v₀})
      {q | Work.Tubular.normalNorm E q.1 ≠ 0}).homology (8 + k))) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Tubular.PunctCompl E v₀))).homology (8 + k)) := by
  -- the relative set `A = onePointNonzero E` inside `X = ν⁺ ∖ {x₀}`
  let A : Set (Work.Tubular.PunctCompl E v₀) :=
    {q | (q : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E}
  -- the point at infinity of the Thom space
  let Z : Set (Work.Tubular.PunctCompl E v₀) :=
    {q | (q : OnePoint (Work.Tubular.NormalTotal E)) = OnePoint.infty}
  have hAopen : IsOpen A := (Work.Tubular.isOpen_onePointNonzero E).preimage continuous_subtype_val
  have hZclosed : IsClosed Z := (OnePoint.isClosed_infty).preimage continuous_subtype_val
  -- excision hypothesis: `{∞}` is closed and contained in the open set `A`
  have hcl : closure Z ⊆ interior A := by
    rw [hZclosed.closure_eq, hAopen.interior_eq]
    intro q hq
    change (q : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E
    rw [show (q : OnePoint (Work.Tubular.NormalTotal E)) = OnePoint.infty from hq]
    exact Work.Tubular.mem_onePointNonzero.mpr (Or.inl rfl)
  obtain ⟨eExc⟩ := Work.Cohomology.excision (TopCat.of (Work.Tubular.PunctCompl E v₀)) A Z hcl
    (8 + k)
  -- the homeomorphism of pairs sends `q` to the unique point of `ν` whose image in `ν⁺` is `q`
  have hsome : ∀ q : {x : Work.Tubular.PunctCompl E v₀ | x ∉ Z},
      OnePoint.some (Work.Tubular.TubeClass.homeomorph_punctPair E v₀ q :
        Work.Tubular.NormalTotal E) = (q : OnePoint (Work.Tubular.NormalTotal E)) := by
    intro q
    have happ : (Work.Tubular.TubeClass.homeomorph_punctPair E v₀ q :
        Work.Tubular.NormalTotal E)
        = ((Work.Tubular.onePointRangeHomeo (Work.Tubular.NormalTotal E)).symm
            (⟨(q : OnePoint (Work.Tubular.NormalTotal E)), q.2⟩ :
              ↥({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))) := rfl
    rw [happ]
    exact congrArg Subtype.val
      ((Work.Tubular.onePointRangeHomeo (Work.Tubular.NormalTotal E)).apply_symm_apply
        (⟨(q : OnePoint (Work.Tubular.NormalTotal E)), q.2⟩ :
          ↥({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))))
  -- the homeomorphism carries `A ∖ {∞}` onto `Q`
  have hAB : ∀ q : {x : Work.Tubular.PunctCompl E v₀ | x ∉ Z},
      q ∈ {y : {x : Work.Tubular.PunctCompl E v₀ | x ∉ Z} |
            (y : Work.Tubular.PunctCompl E v₀) ∈ A}
        ↔ Work.Tubular.TubeClass.homeomorph_punctPair E v₀ q ∈
          {q : {p : Work.Tubular.NormalTotal E //
              p ≠ Work.Tubular.TubeClass.zeroNormalPt E v₀} |
            Work.Tubular.normalNorm E q.1 ≠ 0} := by
    intro q
    constructor
    · intro hq
      change (q : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E at hq
      rcases (Work.Tubular.mem_onePointNonzero.mp hq) with hinf | ⟨w, hw, hwe⟩
      · exact absurd hinf q.2
      · have hw' : (Work.Tubular.TubeClass.homeomorph_punctPair E v₀ q :
            Work.Tubular.NormalTotal E) = w :=
          OnePoint.coe_injective (by rw [hsome q, hwe])
        change Work.Tubular.normalNorm E (Work.Tubular.TubeClass.homeomorph_punctPair E v₀ q :
          Work.Tubular.NormalTotal E) ≠ 0
        rw [hw']; exact hw
    · intro hq
      change Work.Tubular.normalNorm E (Work.Tubular.TubeClass.homeomorph_punctPair E v₀ q :
        Work.Tubular.NormalTotal E) ≠ 0 at hq
      change (q : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E
      refine Work.Tubular.mem_onePointNonzero.mpr (Or.inr ⟨_, hq, ?_⟩)
      rw [← hsome q]
  obtain ⟨eHomeo⟩ := Work.Tubular.nonempty_relChains_homology_homeo
    (X := TopCat.of {x : Work.Tubular.PunctCompl E v₀ | x ∉ Z})
    (Y := TopCat.of {p : Work.Tubular.NormalTotal E //
      p ≠ Work.Tubular.TubeClass.zeroNormalPt E v₀})
    (Work.Tubular.TubeClass.homeomorph_punctPair E v₀) hAB (8 + k)
  have key : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
      (TopCat.of (Work.Tubular.PunctCompl E v₀)) A).homology (8 + k)) :=
    CategoryTheory.Limits.IsZero.of_iso h (eExc ≪≫ eHomeo)
  exact Work.Tubular.TubeClass.punctComplTopHomologyVanishing_of_isZero_pair E v₀ key

end

end Work.Tubular.PuncturedDiscPair
