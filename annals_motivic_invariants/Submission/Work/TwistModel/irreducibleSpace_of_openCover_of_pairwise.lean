import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.TwistModel

/-- If a space is covered by a family of open subsets, each of which is irreducible
(in the subspace topology), and any two members of the family meet, then the whole
space is irreducible. -/
theorem irreducibleSpace_of_openCover_of_pairwise {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Nonempty ι] (U : ι → TopologicalSpace.Opens X) (hcover : iSup U = ⊤)
    (hirr : ∀ i, IrreducibleSpace (U i)) (hpair : ∀ i j, ∃ x : X, x ∈ U i ∧ x ∈ U j) :
    IrreducibleSpace X := by
  -- Each `U i` is a preirreducible subset of `X`.
  have hUi : ∀ i, IsPreirreducible (U i : Set X) := fun i => by
    have := hirr i
    exact IsPreirreducible.of_subtype
  -- `X` is nonempty: it is covered by a nonempty irreducible piece.
  have hne : (⊤ : Set X).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have hI := hirr i
    obtain ⟨x⟩ := (inferInstance : Nonempty (U i))
    exact ⟨x.1, trivial⟩
  -- It suffices to show that any two nonempty opens meet.
  have hpre : PreirreducibleSpace X :=
    PreirreducibleSpace.of_forall_nonempty_inter fun u v hu hv hu' hv' => by
      obtain ⟨x, hxu⟩ := hu'
      obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show x ∈ (⨆ i, U i : TopologicalSpace.Opens X) by rw [hcover]; trivial)
      obtain ⟨y, hyv⟩ := hv'
      obtain ⟨j, hyj⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show y ∈ (⨆ i, U i : TopologicalSpace.Opens X) by rw [hcover]; trivial)
      -- `U i` and `U j` meet by hypothesis.
      obtain ⟨z, hzi, hzj⟩ := hpair i j
      -- `u` meets `U i`, hence (by irreducibility of `U i`) also `U j`.
      have h1 : ((U i : Set X) ∩ u).Nonempty := ⟨x, hxi, hxu⟩
      have h2 : ((U i : Set X) ∩ (U j : Set X)).Nonempty := ⟨z, hzi, hzj⟩
      obtain ⟨p, -, hpu, hpj⟩ := hUi i u (U j) hu (U j).isOpen h1 h2
      -- Now both `u` and `v` meet `U j`, so by irreducibility of `U j` they meet.
      have h3 : ((U j : Set X) ∩ u).Nonempty := ⟨p, hpj, hpu⟩
      have h4 : ((U j : Set X) ∩ v).Nonempty := ⟨y, hyj, hyv⟩
      obtain ⟨q, -, hqu, hqv⟩ := hUi j u v hu hv h3 h4
      exact ⟨q, hqu, hqv⟩
  exact (irreducibleSpace_def X).mpr ⟨hne, hpre.isPreirreducible_univ⟩

end Work.TwistModel
