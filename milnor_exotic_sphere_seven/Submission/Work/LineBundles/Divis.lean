import Submission.Work.LineBundles.Defs
import Submission.Work.Gen.chernClass_tensorLine_of_nowhereZeroSection
import Submission.Work.Whitney.TautSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The divisibility lemma for `c₁` of line bundles

`Work.LineBundles.divisibility : Work.LineBundles.Divisibility`: for complex line bundles `L`, `M`
over an arbitrary topological base, `c₁(L ⊗ M) - c₁(M)` is a multiple of `c₁(L)` by a class in
`H⁰(B;ℤ)`.

The proof is the Gysin argument of the chapter README: pull both sides back to the punctured total
space `X` of the realification of `L`, where `π^*L` acquires the tautological nowhere-zero section
(so that `c₁(π^*(L ⊗ M)) = c₁(π^*M)` by
`Work.Gen.chernClass_tensorLine_of_nowhereZeroSection`), and conclude by the exactness
`range (· ∪ e) = ker (π^*)` (`Work.Thom.gysin_exact_at_base`) together with
`e(L_ℝ) = c₁(L)` (`Work.Thom.chernClass_one_top`).
-/

namespace Work.LineBundles

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- The pullback of `c₁` along a continuous map is the `c₁` of the pullback bundle. -/
theorem c1_bundleComap {B' : Type} [TopologicalSpace B'] (L : LineCore B ι₁) (f : C(B', B)) :
    (CohMap f ℤ 2).hom (c1 L) = c1 (bundleComap L f) :=
  (Work.Thom.chernClass_comap (m := 1) (j := 1) L f).symm

theorem divisibility : Divisibility := by
  intro B _ ι₁ ι₂ _ _ L M
  set Z : RealBundle B (EuclideanSpace ℂ (Fin 1)) ι₁ := Work.Thom.realification L with hZ
  set ρ : C(↥(Work.Thom.zeroComplement Z), B) :=
    (Work.Thom.bundleProj Z).comp (Work.Thom.subtypeMap (Work.Thom.zeroComplement Z)) with hρ
  set T : Work.Thom.ThomClass Z 2 := Work.Thom.thomClassRank 1 le_rfl L with hT
  -- `gysinπ Z 2` is the pullback along `ρ`.
  have hgysin : ∀ x : Coh ℤ 2 B, Work.Thom.gysinπ Z 2 x = (CohMap ρ ℤ 2).hom x := by
    intro x
    rw [Work.Thom.gysinπ, hρ, Work.Thom.CohMap_comp]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  -- the tautological section of the pullback of `L` to the punctured total space
  have hsec : c1 (Work.Gen.tensorLine (bundleComap L ρ) (bundleComap M ρ))
      = c1 (bundleComap M ρ) := by
    refine Work.Gen.chernClass_tensorLine_of_nowhereZeroSection (bundleComap L ρ)
      (bundleComap M ρ) ?_ ?_
    · -- the tautological section, transported along `realification_bundleComap`
      have hcore : Work.Thom.realification (Work.Thom.bundleComap L ρ) = Work.Thom.bundleComap Z ρ := by
        rw [Work.Thom.realification_bundleComap L ρ]
      refine ⟨fun x => ⟨⟨x, (x : Z.TotalSpace).snd⟩, x.2⟩, ?_⟩
      exact hcore ▸ (Work.Whitney.continuous_tautologicalSection Z).subtype_mk (fun x => x.2)
    · intro x
      rfl
  -- the pulled back classes agree
  have hstep : (CohMap ρ ℤ 2).hom (c1 (Work.Gen.tensorLine L M))
      = (CohMap ρ ℤ 2).hom (c1 M) := by
    rw [c1_bundleComap (Work.Gen.tensorLine L M) ρ, c1_bundleComap M ρ,
      Work.Gen.tensorLine_bundleComap]
    exact hsec
  -- hence the difference is killed by `π^*`
  have hker : Work.Thom.gysinπ Z 2 (c1 (Work.Gen.tensorLine L M) - c1 M) = 0 := by
    rw [map_sub, hgysin, hgysin, hstep, sub_self]
  -- Gysin exactness produces the witness
  have hmem : c1 (Work.Gen.tensorLine L M) - c1 M ∈ Set.range (Work.Thom.gysinEuler T 0) := by
    rw [Work.Thom.gysin_exact_at_base T 0]
    exact hker
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have he : T.eulerClass = c1 L := (Work.Thom.chernClass_one_top L).symm
  have hcup : (Work.Thom.gysinEuler T 0) x = cup₀₂ B x (c1 L) := by
    rw [Work.Thom.gysinEuler_eq_cupEuler T 0 x, he, cup₀₂_apply, Work.Whitney.cupChern_def,
      Subsingleton.elim (Nat.mul_add 2 0 1).symm rfl, Work.Thom.cohTransport_rfl]
  rw [← hcup, hx, add_comm, sub_add_cancel]

end

end Work.LineBundles
