import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot
import Submission.NK.NUV2.RouteC.map_norm_eq_zero

/-!
# The norm endomorphism kills the positive cohomology of a finite group

For a finite group `G` and a `Rep ℤ G` `A`, the norm endomorphism `A.norm` (the sum of the
group action, `a ↦ ∑_g g · a`) induces the zero map on `Hⁿ(G, A)` for every `n ≥ 1`.

The two low cases `n = 1` and `n = 2` are proved in
`Submission/Work/NUV2/RouteC/map_norm_eq_zero.lean` by explicit cochain computations.  Here we
obtain the general case by **dimension shifting**, inducting downwards along the exact sequence

`0 ⟶ A ⟶η Coind_{1}^{G}(Res_{1}^{G} A) ⟶ C ⟶ 0`

where `η` is the unit of the restriction ⊣ coinduction adjunction.  The middle term is coinduced
from the trivial subgroup, hence acyclic in positive degrees (Shapiro's lemma,
`groupCohomology.coindIso`, and `isZero_groupCohomology_succ_of_subsingleton`; packaged in the
commons as `isZero_groupCohomology_coind_bot`).  The connecting isomorphism
`δ : Hⁿ(G, C) ≅ Hⁿ⁺¹(G, A)` is natural (`groupCohomology.δ_naturality`) and the norm is a natural
endomorphism of the identity functor (`Rep.norm_comm`), so that

`δ ≫ map (A.norm) = map (C.norm) ≫ δ`,

which turns the vanishing in degree `n` for `C` into the vanishing in degree `n + 1` for `A`.
-/

open CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.NUV2.RouteC

variable {G : Type} [Group G] [Fintype G]

/-- The unit `A ⟶ Coind_{1}^{G}(Res_{1}^{G} A)` of the coinduction adjunction, for the trivial
subgroup. -/
noncomputable abbrev coindUnit (A : Rep ℤ G) :
    A ⟶ Rep.coind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A) :=
  (Rep.resCoindAdjunction ℤ (⊥ : Subgroup G).subtype).unit.app A

/-- **The unit of the coinduction adjunction evaluated at `1` is the identity** (it is the map
sending `a` to the function `g ↦ ρ g a`). -/
lemma coindUnit_apply_one (A : Rep ℤ G) (a : A) : ((coindUnit A).hom a).1 1 = a := by
  rw [show coindUnit A = Rep.resCoindToHom (⊥ : Subgroup G).subtype A
      (Rep.res (⊥ : Subgroup G).subtype A) (𝟙 (Rep.res (⊥ : Subgroup G).subtype A)) from rfl]
  rw [Rep.resCoindToHom_hom_apply_coe]
  simp

/-- The unit of the coinduction adjunction is injective (evaluate at `1`). -/
lemma coindUnit_injective (A : Rep ℤ G) : Function.Injective (coindUnit A).hom := by
  intro a b hab
  have h1 := coindUnit_apply_one A a
  have h2 := coindUnit_apply_one A b
  rw [hab] at h1
  exact h1.symm.trans h2

/-- **The dimension-shifting induction step.**  If the norm kills `Hⁿ⁺¹(G, -)` for every
representation, then it kills `Hⁿ⁺²(G, A)`. -/
theorem map_norm_eq_zero_step (A : Rep ℤ G) (m : ℕ)
    (ih : ∀ A' : Rep ℤ G, groupCohomology.map (MonoidHom.id G) A'.norm (m + 1) = 0) :
    groupCohomology.map (MonoidHom.id G) A.norm (m + 2) = 0 := by
  -- the short exact sequence `0 ⟶ A ⟶ Coind_1(Res_1 A) ⟶ cokernel ⟶ 0`
  let B : Rep ℤ (⊥ : Subgroup G) := Rep.res (⊥ : Subgroup G).subtype A
  let ψ : A ⟶ Rep.coind (⊥ : Subgroup G).subtype B := coindUnit A
  let C : Rep ℤ G := cokernel ψ
  have hmono : Mono ψ := (Rep.mono_iff_injective ψ).2 (coindUnit_injective A)
  have hX : (ShortComplex.cokernelSequence ψ).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact ψ) hmono inferInstance
  -- the middle term is acyclic in positive degrees
  have hM1 : IsZero (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype B) (m + 1)) :=
    Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot B m
  have hM2 : IsZero (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype B) (m + 2)) :=
    Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot B (m + 1)
  -- hence the connecting map is an isomorphism
  haveI hδ : IsIso (groupCohomology.δ hX (m + 1) (m + 2) rfl) :=
    groupCohomology.isIso_δ_of_isZero hX (m + 1) hM1 hM2
  -- the norm is natural, so it gives an endomorphism of the short exact sequence
  let F : ShortComplex.cokernelSequence ψ ⟶ ShortComplex.cokernelSequence ψ :=
    { τ₁ := A.norm
      τ₂ := (Rep.coind (⊥ : Subgroup G).subtype B).norm
      τ₃ := C.norm
      comm₁₂ := (Rep.norm_comm ψ).symm
      comm₂₃ := (Rep.norm_comm (cokernel.π ψ)).symm }
  have hnat : (groupCohomology.δ hX (m + 1) (m + 2) rfl) ≫
      groupCohomology.map (MonoidHom.id G) A.norm (m + 2) =
      groupCohomology.map (MonoidHom.id G) C.norm (m + 1) ≫
        (groupCohomology.δ hX (m + 1) (m + 2) rfl) :=
    groupCohomology.δ_naturality hX hX F (m + 1) (m + 2) rfl
  have hih : groupCohomology.map (MonoidHom.id G) C.norm (m + 1) = 0 := ih C
  -- cancel the connecting isomorphism
  have hcancel : inv (groupCohomology.δ hX (m + 1) (m + 2) rfl) ≫
      groupCohomology.δ hX (m + 1) (m + 2) rfl ≫
      groupCohomology.map (MonoidHom.id G) A.norm (m + 2) =
      groupCohomology.map (MonoidHom.id G) A.norm (m + 2) :=
    IsIso.inv_hom_id_assoc _ _
  have hih' : groupCohomology.map (MonoidHom.id G) C.norm (m + 1) =
      (0 : groupCohomology C (m + 1) ⟶ groupCohomology C (m + 1)) := hih
  have hzero : groupCohomology.δ hX (m + 1) (m + 2) rfl ≫
      groupCohomology.map (MonoidHom.id G) A.norm (m + 2) = 0 := by
    rw [hnat, hih']
    exact zero_comp (f := groupCohomology.δ hX (m + 1) (m + 2) rfl)
  have hf : groupCohomology.map (MonoidHom.id G) A.norm (m + 2) =
      inv (groupCohomology.δ hX (m + 1) (m + 2) rfl) ≫ 0 :=
    hcancel.symm.trans
      (congrArg (fun x => inv (groupCohomology.δ hX (m + 1) (m + 2) rfl) ≫ x) hzero)
  rw [hf]
  exact comp_zero

/-- **The norm endomorphism of a representation kills the positive cohomology of a finite group.**

For a finite group `G`, a `Rep ℤ G` `A` and `n ≥ 1`, the `Rep ℤ G`-endomorphism `A.norm`
(underlying map `a ↦ ∑_g g·a`) induces the zero map on `H^n(G, A)`.

Both low cases are **already proved** in this workspace, in
`Submission/Work/NUV2/RouteC/map_norm_eq_zero.lean` (axiom-clean):

* `NK.NUV2.RouteC.map_norm_eq_zero_one` (`n = 1`): the proof is *exact* — for a 1-cocycle (a
  derivation) `d` the cocycle identity gives `A.ρ h (d g) = d (h*g) - d h`, so
  `A.norm (d g) = ∑_h (d (h*g) - d h) = 0` because `h ↦ h*g` is a bijection; then `H1π_comp_map`;
* `NK.NUV2.RouteC.map_norm_eq_zero_two` (`n = 2`): the pointwise norm of a 2-cocycle is an
  *explicit* 2-coboundary with primitive `b t = ∑_g f (g,t)`; then `H2π_comp_map`.

Reviewers of this statement (both "looks correct as stated") recommend the dimension-shift for
general `n`, now anchored on the proved `n = 1` case: along
`0 → A → Coind_{ℤ[G]}(A) → C → 0` (coinduced modules are acyclic in positive degrees — Shapiro,
`Mathlib/RepresentationTheory/Homological/GroupCohomology/Shapiro.lean`), the connecting isomorphism
`H^{n+1}(G,A) ≅ H^n(G,C)` (Mathlib's `LongExactSequence.lean` for the long exact sequence of a
short exact sequence of `Rep`s) is natural and intertwines the norm maps, giving induction on `n`.
If the naturality of the connecting map w.r.t. a coefficient endomorphism is out of reach, a proof
for `n = 2` alone is already useful — please say so rather than abandoning. -/
theorem map_norm_eq_zero_general {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) (n : ℕ)
    (hn : 1 ≤ n) :
    groupCohomology.map (MonoidHom.id G) A.norm n = 0 := by
  have hmain : ∀ k : ℕ, ∀ A' : Rep ℤ G,
      groupCohomology.map (MonoidHom.id G) A'.norm (k + 1) = 0 := by
    intro k
    induction k with
    | zero => intro A'; exact map_norm_eq_zero_one A'
    | succ k ih => intro A'; exact map_norm_eq_zero_step A' k ih
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact hmain k A

end NK.NUV2.RouteC
