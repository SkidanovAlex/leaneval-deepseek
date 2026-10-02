import Mathlib
import Submission.Work.Gen.chernRootDefs
import Submission.Work.LerayHirsch.nonempty_bundleIso_twist_whitneySum
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

namespace Work.Gen

/-!
# The twist `ℓ^* ⊗ π^*(⊕ᵢ Lᵢ)` of an iterated direct sum of line bundles

For a complex bundle `W = lineSumCore n M` over `B` with projectivisation `P = ProjSpace W`,
tautological line `ℓ` and projection `π`, the rank-`n` twist
`Work.Gen.twistTautTop W = ℓ^* ⊗ π^*W` is the direct sum of the `n` line bundles
`Work.Gen.twistTaut W (M i) = ℓ^* ⊗ π^*M i`:

  `ℓ^* ⊗ π^*(M 0 ⊕ ⋯ ⊕ M (n-1)) ≅ (ℓ^* ⊗ π^*M 0) ⊕ ⋯ ⊕ (ℓ^* ⊗ π^*M (n-1))`.

Both the tensor product with a line bundle and the pullback distribute over the direct sum
(`Work.LerayHirsch.nonempty_bundleIso_twist_whitneySum`, `Work.Whitney.whitneySum_bundleComap`), so
the statement follows by induction on `n`; the base case `n = 0` is the rank-zero bundle, all of
whose fibres are subsingletons.
-/

section

set_option backward.isDefEq.respectTransparency false

/-! ## Elementary facts about rank-zero bundles -/

/-- The total-space map of the zero fibrewise linear map is continuous. -/
theorem twistIsoAux_zero_totalSpaceMap {B : Type} [TopologicalSpace B] {F F' : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F'] [NormedSpace ℂ F']
    {ι ι' : Type} (Z : VectorBundleCore ℂ B F ι) (Z' : VectorBundleCore ℂ B F' ι') :
    Continuous fun p : Z.TotalSpace =>
      (⟨p.1, (0 : F →L[ℂ] F') p.2⟩ : Z'.TotalSpace) := by
  refine Work.Thom.continuous_totalSpaceMap_clm_gen (𝕜 := ℂ) Z Z' (ContinuousMap.id B)
    (fun _ => 0) ?_
  intro i₁ i₂
  have hfun : (fun b : B => Z'.coordChange (Z'.indexAt ((ContinuousMap.id B) b)) i₂
      ((ContinuousMap.id B) b) ∘SL (0 : F →L[ℂ] F') ∘SL Z.coordChange i₁ (Z.indexAt b) b)
      = (fun _ : B => (0 : F →L[ℂ] F')) := by
    funext b
    ext v
    simp
  rw [hfun]
  exact continuousOn_const

/-- **A bundle whose fibres are a subsingleton is isomorphic to the trivial bundle.**  Every
fibrewise linear map is `0`, and the constant fibrewise zero map has continuous induced map. -/
theorem twistIsoAux_trivial_of_subsingleton {B : Type} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Subsingleton F] {ι : Type}
    (Z : VectorBundleCore ℂ B F ι) {ι' : Type} [Inhabited ι'] :
    Nonempty (Work.Thom.BundleIso Z (trivialVectorBundleCore ℂ B F ι')) := by
  refine ⟨{ hom := fun _ => 0, inv := fun _ => 0,
            left_inv := fun b _ => by
              haveI : Subsingleton (Z.Fiber b) := ‹Subsingleton F›
              exact Subsingleton.elim _ _
            right_inv := fun b _ => by
              haveI : Subsingleton ((trivialVectorBundleCore ℂ B F ι').Fiber b) :=
                ‹Subsingleton F›
              exact Subsingleton.elim _ _
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · simpa using twistIsoAux_zero_totalSpaceMap Z (trivialVectorBundleCore ℂ B F ι')
  · simpa using twistIsoAux_zero_totalSpaceMap (trivialVectorBundleCore ℂ B F ι') Z

/-! ## The tensor product with a line bundle commutes with the iterated direct sum -/

/-- **`L ⊗ (⊕ᵢ Lᵢ) ≅ ⊕ᵢ (L ⊗ Lᵢ)`** for a complex line bundle `L` and line bundles `Lᵢ`. -/
theorem twistIsoAux_twistCore_lineSumCore {P : Type} [TopologicalSpace P] {ιL ι : Type} :
    ∀ (n : ℕ) (E : VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ιL)
      (L : Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι),
    Nonempty (Work.Thom.BundleIso
      (Work.LerayHirsch.twistCore E (Work.LerayHirsch.lineSumCore n L))
      (Work.LerayHirsch.lineSumCore n (fun i => Work.LerayHirsch.twistCore E (L i)))) := by
  intro n
  induction n with
  | zero =>
    intro E L
    rw [Work.LerayHirsch.lineSumCore_zero, Work.LerayHirsch.lineSumCore_zero]
    exact twistIsoAux_trivial_of_subsingleton (ι' := PUnit) _
  | succ n ih =>
    intro E L
    rw [Work.LerayHirsch.lineSumCore_succ, Work.LerayHirsch.lineSumCore_succ]
    obtain ⟨e₁⟩ := Work.LerayHirsch.nonempty_bundleIso_twist_whitneySum E
      (Work.LerayHirsch.lineSumCore n (L ∘ Fin.castSucc)) (L (Fin.last n))
    obtain ⟨e₂⟩ := ih E (L ∘ Fin.castSucc)
    obtain ⟨e₃⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_first
      (Work.LerayHirsch.twistCore E (Work.LerayHirsch.lineSumCore n (L ∘ Fin.castSucc)))
      (Work.LerayHirsch.lineSumCore n
        (fun i => Work.LerayHirsch.twistCore E ((L ∘ Fin.castSucc) i)))
      (Work.LerayHirsch.twistCore E (L (Fin.last n))) e₂
    exact ⟨e₁.trans e₃⟩

/-! ## The pullback commutes with the iterated direct sum -/

/-- **`f^*(⊕ᵢ Lᵢ) = ⊕ᵢ (f^*Lᵢ)`** for an iterated sum of line bundles. -/
theorem twistIsoAux_bundleComap_lineSumCore {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] {ι : Type} :
    ∀ (n : ℕ) (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
      (f : C(B', B)),
    Work.Thom.bundleComap (Work.LerayHirsch.lineSumCore n M) f
      = Work.LerayHirsch.lineSumCore n (fun i => Work.Thom.bundleComap (M i) f) := by
  intro n
  induction n with
  | zero =>
    intro M f
    rw [Work.LerayHirsch.lineSumCore_zero, Work.LerayHirsch.lineSumCore_zero]
    refine Work.Thom.bundleCore_ext (funext fun p => ?_) rfl (fun p q x => rfl)
    exact Set.preimage_univ
  | succ n ih =>
    intro M f
    rw [Work.LerayHirsch.lineSumCore_succ, Work.LerayHirsch.lineSumCore_succ,
        Work.Whitney.whitneySum_bundleComap, ih]
    rfl

end

/- ## The target -/

theorem twist_lineSumCore_iso {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] (n : ℕ)
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Nonempty (Work.Thom.BundleIso
      (twistTautTop (Work.LerayHirsch.lineSumCore n M))
      (Work.LerayHirsch.lineSumCore n
        (fun i => twistTaut (Work.LerayHirsch.lineSumCore n M) (M i)))) := by
  have h1 := twistIsoAux_bundleComap_lineSumCore n M
    (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore n M))
  unfold twistTautTop twistTaut
  rw [h1]
  exact twistIsoAux_twistCore_lineSumCore n
    (Work.Gen.dualLineCore (Work.LerayHirsch.tautLine (Work.LerayHirsch.lineSumCore n M)))
    (fun i => Work.Thom.bundleComap (M i)
      (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore n M)))

end Work.Gen
