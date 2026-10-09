import Mathlib
import Submission.Work.SSGRoute.TwoTwoModelDefs
import Submission.Work.Shrinking.PCentral
import Submission.Work.SSGRoute.tt_model_comm_of_gens
import Submission.Work.SSGRoute.tt_model_pCentralSeries_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Properties of the "two-two" detector `ttDetector`

We record the three structural properties of the detector homomorphism
`ttDetector ι : FreeGroup ι →* TTModel ι` that the `p = 2` correction of Shafarevich's
theorem needs:

1. it sends each basic commutator `⁅x_i, x_j⁆` of the free group to the "matrix"
   `pairElt i j = E_{ij} + E_{ji}` (separating property);
2. its kernel contains the third term `P₃` of the descending `2`-central series of `FreeGroup ι`;
3. it is equivariant for the automorphism induced by a permutation `σ` of the generators,
   `ttDetector (freeGroupCongr σ x) = permAut σ (ttDetector x)`.
-/

namespace Work.SSGRoute

open scoped commutatorElement

/-! ## Functoriality of the descending `p`-central series

A local copy of the standard fact that an arbitrary group homomorphism `f : P →* Q` carries the
`n`-th term of the descending `p`-central series of `P` into that of `Q`.  It is used only through
`P₃` of the free group. -/

private theorem tt_map_powSubgroup_le {P Q : Type*} [Group P] [Group Q] (p : ℕ) (ψ : P →* Q)
    (H : Subgroup P) :
    (Work.Shrinking.powSubgroup p H).map ψ ≤ Work.Shrinking.powSubgroup p (H.map ψ) := by
  unfold Work.Shrinking.powSubgroup
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨ψ z, Subgroup.mem_map_of_mem ψ hz, by rw [map_pow]⟩

private theorem tt_powSubgroup_mono {P : Type*} [Group P] (p : ℕ) {H K : Subgroup P}
    (h : H ≤ K) : Work.Shrinking.powSubgroup p H ≤ Work.Shrinking.powSubgroup p K := by
  unfold Work.Shrinking.powSubgroup
  exact Subgroup.closure_mono (Set.image_mono h)

private theorem tt_map_commutator_top_le {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q)
    (H : Subgroup P) : (⁅H, ⊤⁆ : Subgroup P).map ψ ≤ ⁅H.map ψ, ⊤⁆ := by
  rw [Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_rfl le_top

private theorem map_pCentralSeries_le_tt {P Q : Type*} [Group P] [Group Q] (p : ℕ)
    (ψ : P →* Q) (n : ℕ) :
    (Work.Shrinking.pCentralSeries p P n).map ψ ≤ Work.Shrinking.pCentralSeries p Q n := by
  induction n with
  | zero =>
    rw [Work.Shrinking.pCentralSeries_zero, Work.Shrinking.pCentralSeries_zero]
    exact le_top
  | succ n ih =>
    rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralSeries_succ,
      Work.Shrinking.pCentralStep, Work.Shrinking.pCentralStep, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · exact (tt_map_powSubgroup_le p ψ (Work.Shrinking.pCentralSeries p P n)).trans
        ((tt_powSubgroup_mono p ih).trans le_sup_left)
    · exact (tt_map_commutator_top_le ψ (Work.Shrinking.pCentralSeries p P n)).trans
        ((Subgroup.commutator_mono ih le_rfl).trans le_sup_right)

/-! ## The automorphism `permAut`

Computation rules and the key fact that `permAut` sends the generalised generator `of i` to
`of (σ i)`. -/

@[simp] theorem permAut_fst {ι : Type*} (σ : ι ≃ ι) (x : TTModel ι) (i : ι) :
    (TTModel.permAut σ x).fst i = x.fst (σ.symm i) := rfl

@[simp] theorem permAut_snd {ι : Type*} (σ : ι ≃ ι) (x : TTModel ι) (p : ι × ι) :
    (TTModel.permAut σ x).snd p = x.snd (σ.symm p.1, σ.symm p.2) := rfl

theorem permAut_of {ι : Type*} [DecidableEq ι] (σ : ι ≃ ι) (i : ι) :
    TTModel.permAut σ (TTModel.of i) = TTModel.of (σ i) := by
  refine TTModel.ext' ?_ ?_
  · intro j
    rw [permAut_fst, TTModel.of_fst, TTModel.of_fst]
    simp only [Pi.single_apply, Equiv.symm_apply_eq]
  · intro p
    simp [permAut_snd, TTModel.of_snd]

/-- `freeGroupCongr` on a generator. -/
theorem freeGroupCongr_of {ι : Type*} (σ : ι ≃ ι) (i : ι) :
    FreeGroup.freeGroupCongr σ (FreeGroup.of i) = FreeGroup.of (σ i) := by
  rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]

/-! ## The main statement -/

theorem tt_detector_props (ι : Type*) [DecidableEq ι] :
    (∀ i j : ι, Work.SSGRoute.ttDetector ι ⁅FreeGroup.of i, FreeGroup.of j⁆ =
      Work.SSGRoute.TTModel.pairElt i j) ∧
    (Work.Shrinking.pCentralSeries 2 (FreeGroup ι) 2 ≤ (Work.SSGRoute.ttDetector ι).ker) ∧
    (∀ (σ : ι ≃ ι) (x : FreeGroup ι),
      Work.SSGRoute.ttDetector ι (FreeGroup.freeGroupCongr σ x) =
        Work.SSGRoute.TTModel.permAut σ (Work.SSGRoute.ttDetector ι x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [map_commutatorElement (ttDetector ι), ttDetector_of, ttDetector_of]
    exact tt_model_comm_of_gens i j
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hmem : ttDetector ι x ∈
        (Work.Shrinking.pCentralSeries 2 (FreeGroup ι) 2).map (ttDetector ι) :=
      Subgroup.mem_map_of_mem _ hx
    have hle := map_pCentralSeries_le_tt 2 (ttDetector ι) 2
    have hthis : ttDetector ι x ∈ Work.Shrinking.pCentralSeries 2 (TTModel ι) 2 := hle hmem
    rw [tt_model_pCentralSeries_two] at hthis
    simpa using hthis
  · intro σ x
    have key : (ttDetector ι).comp (FreeGroup.freeGroupCongr σ).toMonoidHom =
        (TTModel.permAut σ).toMonoidHom.comp (ttDetector ι) := by
      apply FreeGroup.ext_hom
      intro i
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, freeGroupCongr_of,
        ttDetector_of, permAut_of]
    have := congrArg (fun g : FreeGroup ι →* TTModel ι => g x) key
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using this

end Work.SSGRoute
