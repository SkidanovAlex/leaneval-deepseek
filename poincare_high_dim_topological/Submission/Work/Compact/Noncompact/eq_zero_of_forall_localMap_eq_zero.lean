import Mathlib
import Submission.Work.Compact.Noncompact.Basic
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.Assembly
import Submission.Work.Compact.Noncompact.mem_suppS_iff_of_expansion
import Submission.Work.Compact.Noncompact.goodC_final
import Submission.Work.Compact.Noncompact.hatClass_natural
import Submission.Work.Compact.Noncompact.hatClass_of_d_eq_zero
import Submission.Work.Compact.Noncompact.exists_sub_bdry_of_hatClass_eq_zero
import Submission.Work.Compact.Noncompact.suppS_empty
import Submission.Work.Compact.Noncompact.exists_suppS_isCompact_closure
import Submission.Work.Compact.Noncompact.exists_isCompact_closure_mem
import Submission.Work.Compact.Noncompact.eq_zero_of_mem_suppS_of_disjoint

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

/-- The composite `∂ ∘ ∂` of two consecutive singular boundaries vanishes. -/
lemma bdry_bdry {X : TopCat} (k : ℕ) (c : Ch X (k + 2)) :
    bdry X k (bdry X (k + 1) c) = 0 := by
  have h := HomologicalComplex.d_comp_d (Work.Cohomology.singularChains ℤ X) (k + 2) (k + 1) k
  have h2 := congrArg (fun (f : Ch X (k + 2) ⟶ Ch X k) => f.hom c) h
  rw [ModuleCat.comp_apply, ModuleCat.hom_zero] at h2
  exact h2

/-- The localization map at `x` is the map in homology induced by the projection onto the relative
chains `C_*(X)/C_*(X∖{x})`. -/
theorem localMap_eq_homologyMap_cokernel {X : TopCat} {n : ℕ} (x : X) :
    localMap (X := X) n x =
      HomologicalComplex.homologyMap
        (cokernel.π (Work.Cohomology.inclChains X ({x}ᶜ : Set X))) n := by
  simp only [localMap, relMapHom]
  rw [← HomologicalComplex.homologyMap_comp,
    cokernel_π_relMap (Set.empty_subset ({x}ᶜ : Set X)), Category.id_comp]

/-- Hatcher, *Algebraic Topology*, Prop. 3.29 (i = n case) / Lemma 3.27(a): for a connected
`n`-manifold (`n ≥ 1`) the localization map `H_n(M;ℤ) → H_n(M, M∖{x};ℤ)` detects top classes.
Equivalently: `H_n(M) → ∏_{x∈M} H_n(M, M∖{x})` is injective.

Suggested route (Hatcher's proof).  Let `A ⊆ M` be compact, `u ∈ H_n(RC M (Aᶜ))`; say `u` is
*locally trivial* if its image in `H_n(RC M ({x}ᶜ))` is `0` for all `x ∈ A`.  Prove by induction
on the minimal number `m` of open Euclidean chart pieces needed to cover `A` that a locally
trivial `u` is `0`; the induction step uses the Mayer–Vietoris middle exactness for the two
complementary open sets `Aᶜ`, `Bᶜ`, and the base case `m = 1` (A inside a single chart) is
Hatcher's Lemma 3.27 steps (3)+(4).

Here this is formalised via the chain-level statement `Work.Compact.Noncompact.GoodC`
(see `Submission/Work/Compact/Noncompact/Good.lean`) for all compact sets
(`Work.Compact.Noncompact.goodC_final`); the final step follows Hatcher's proof of
Prop. 3.29 for `i = n`: pick an open neighbourhood `U` of the support of a representing cycle
with compact closure, let `V = M∖Ū`, `D = Ū∖U`; the vanishing of the localization
(`GoodC` at `Ū`) makes the cycle a sum of a boundary and a chain supported in `V`; the vanishing
`H_{n+1}(M, M∖D) = 0` (`GoodC` at `D`) upgrades this to `z = ∂a + c` with `a` supported in
`Dᶜ = U ∪ V`; `Dᶜ` is a disjoint union of the two open sets `U`, `V`, so `a = a_U + a_V` and
`z - ∂a_U` is supported in both `U` and `V`, hence vanishes. -/
theorem eq_zero_of_forall_localMap_eq_zero {n : ℕ} (hn : 1 ≤ n) {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (α : (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n)
    (h : ∀ x : M, localMap (X := TopCat.of M) n x α = 0) : α = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  classical
  -- (0) a cycle representing `α`
  obtain ⟨ζ, hζ⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.singularChains ℤ (TopCat.of M)).homologyπ (m + 1))).mp inferInstance α
  obtain ⟨z, hzdef⟩ : ∃ z : Ch (TopCat.of M) (m + 1),
      z = ((Work.Cohomology.singularChains ℤ (TopCat.of M)).iCycles (m + 1)).hom ζ := ⟨_, rfl⟩
  have hzcyc : bdry (TopCat.of M) m z = 0 := by
    rw [hzdef]
    show ((Work.Cohomology.singularChains ℤ (TopCat.of M)).d (m + 1) m).hom
        (((Work.Cohomology.singularChains ℤ (TopCat.of M)).iCycles (m + 1)).hom ζ) = 0
    have h1 := congrArg (fun (f : (Work.Cohomology.singularChains ℤ (TopCat.of M)).cycles (m + 1) ⟶
        (Work.Cohomology.singularChains ℤ (TopCat.of M)).X m) => f.hom ζ)
      (HomologicalComplex.iCycles_d (Work.Cohomology.singularChains ℤ (TopCat.of M)) (m + 1) m)
    rw [ModuleCat.comp_apply, ModuleCat.hom_zero] at h1
    exact h1
  -- (1) the hypothesis, expressed through the projection to the relative chains
  have h' : ∀ x : M, HomologicalComplex.homologyMap
      (cokernel.π (Work.Cohomology.inclChains (TopCat.of M) ({x}ᶜ : Set M))) (m + 1) α = 0 := by
    intro x
    rw [← localMap_eq_homologyMap_cokernel (X := TopCat.of M) (n := m + 1) x]
    exact h x
  -- (2) an open neighbourhood `U` of the support of `z` with compact closure
  obtain ⟨U, hUopen, hUcomp, hzU⟩ := exists_suppS_isCompact_closure (X := TopCat.of M)
    (fun x => exists_isCompact_closure_mem (n := m + 1) x) (m + 1) z
  -- the class of `z` in `H_{m+1}(M, M∖Ū)` vanishes
  have hzA : bdry (TopCat.of M) m z ∈ suppS (TopCat.of M) ((closure U)ᶜ) m := by
    rw [hzcyc]; exact Submodule.zero_mem _
  obtain ⟨-, huniqA, -⟩ := goodC_final (k := m) (M := M) (closure U) hUcomp
  have hhatA : hatClass (X := TopCat.of M) ((closure U)ᶜ) m z hzA = 0 := by
    apply huniqA
    intro x hx
    have hzTx : bdry (TopCat.of M) m z ∈ suppS (TopCat.of M) (({x}ᶜ : Set M)) m := by
      rw [hzcyc]; exact Submodule.zero_mem _
    rw [hatClass_natural (X := TopCat.of M)
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)) m z hzA hzTx]
    rw [hatClass_of_d_eq_zero (X := TopCat.of M) ({x}ᶜ) m z hzcyc hzTx ζ hzdef.symm]
    rw [hζ]
    exact h' x
  -- (3) chain-level triviality modulo `M∖Ū`
  obtain ⟨w, hw⟩ := exists_sub_bdry_of_hatClass_eq_zero (X := TopCat.of M) ((closure U)ᶜ) m z hzA hhatA
  obtain ⟨c, hc, hcdef⟩ : ∃ c : Ch (TopCat.of M) (m + 1),
      c ∈ suppS (TopCat.of M) ((closure U)ᶜ) (m + 1) ∧
        c = z - bdry (TopCat.of M) (m + 1) w := ⟨_, hw, rfl⟩
  -- (4) the compact set `D = Ū∖U`, with `Dᶜ = U ∪ Ūᶜ`
  have hDcomp : IsCompact ((closure U \ U) : Set M) := hUcomp.diff hUopen
  have hDc : ((closure U \ U : Set M))ᶜ = U ∪ (closure U)ᶜ := Set.compl_sdiff
  obtain ⟨-, -, hvanD⟩ := goodC_final (k := m) (M := M) (closure U \ U) hDcomp
  have hzeroD : IsZero (hatH (TopCat.of M) (closure U \ U) (m + 2)) := hvanD (m + 2) (by omega)
  haveI : Subsingleton (hatH (TopCat.of M) (closure U \ U) (m + 2)) :=
    ModuleCat.isZero_iff_subsingleton.mp hzeroD
  have hwD : bdry (TopCat.of M) (m + 1) w ∈ suppS (TopCat.of M) ((closure U \ U)ᶜ) (m + 1) := by
    rw [hDc]
    rw [show bdry (TopCat.of M) (m + 1) w
        = z - (z - bdry (TopCat.of M) (m + 1) w) from by abel]
    exact Submodule.sub_mem _ (suppS_mono Set.subset_union_left (m + 1) hzU)
      (suppS_mono Set.subset_union_right (m + 1) hw)
  have hhatD : hatClass (X := TopCat.of M) ((closure U \ U)ᶜ) (m + 1) w hwD = 0 :=
    Subsingleton.elim _ _
  obtain ⟨w', hw'⟩ := exists_sub_bdry_of_hatClass_eq_zero (X := TopCat.of M) ((closure U \ U)ᶜ)
    (m + 1) w hwD hhatD
  obtain ⟨a, ha, hadef⟩ : ∃ a : Ch (TopCat.of M) (m + 2),
      a ∈ suppS (TopCat.of M) ((closure U \ U)ᶜ) (m + 2) ∧
        a = w - bdry (TopCat.of M) (m + 2) w' := ⟨_, hw', rfl⟩
  -- (5) `z = ∂a + c`
  have hzc : z = bdry (TopCat.of M) (m + 1) a + c := by
    rw [hadef, map_sub, bdry_bdry (X := TopCat.of M) (m + 1) w', sub_zero, hcdef]
    abel
  -- (6) split `a` along `Dᶜ = U ⊔ Ūᶜ`
  have hdisj : Disjoint (U : Set M) ((closure U)ᶜ : Set M) := by
    rw [Set.disjoint_left]
    exact fun y hy hyc => hyc (subset_closure hy)
  have ha_split : a ∈ suppS (TopCat.of M) U (m + 2) ⊔
      suppS (TopCat.of M) ((closure U)ᶜ) (m + 2) := by
    rw [hDc] at ha
    exact suppS_union_le_sup hUopen isClosed_closure.isOpen_compl hdisj (m + 2) ha
  obtain ⟨aU, haU, aT, haT, haUaT⟩ := Submodule.mem_sup.mp ha_split
  -- (7) `z - ∂aU` is supported in both `U` and `Ūᶜ`, hence vanishes
  have hzeq' : z - bdry (TopCat.of M) (m + 1) aU = bdry (TopCat.of M) (m + 1) aT + c := by
    rw [hzc]
    rw [show bdry (TopCat.of M) (m + 1) a
        = bdry (TopCat.of M) (m + 1) aU + bdry (TopCat.of M) (m + 1) aT from by
      rw [← haUaT, map_add]]
    abel
  have hcancel : z - bdry (TopCat.of M) (m + 1) aU = 0 := by
    refine eq_zero_of_mem_suppS_of_disjoint (X := TopCat.of M) hdisj (m + 1) ?_ ?_
    · exact Submodule.sub_mem _ hzU (bdry_mem_suppS (m + 1) haU)
    · rw [hzeq']; exact Submodule.add_mem _ (bdry_mem_suppS (m + 1) haT) hc
  have hz_bdry : z = bdry (TopCat.of M) (m + 1) aU := sub_eq_zero.mp hcancel
  -- (8) `ζ` is the cycle of the boundary `∂aU`, so `α = 0`
  have hζzed : (Work.Cohomology.singularChains ℤ (TopCat.of M)).toCycles (m + 2) (m + 1) aU = ζ := by
    apply (ModuleCat.mono_iff_injective
      ((Work.Cohomology.singularChains ℤ (TopCat.of M)).iCycles (m + 1))).mp inferInstance
    have h1 : ((Work.Cohomology.singularChains ℤ (TopCat.of M)).iCycles (m + 1)).hom
        ((Work.Cohomology.singularChains ℤ (TopCat.of M)).toCycles (m + 2) (m + 1) aU)
        = bdry (TopCat.of M) (m + 1) aU := by
      have h2 := congrArg (fun (f : Ch (TopCat.of M) (m + 2) ⟶ Ch (TopCat.of M) (m + 1)) =>
          f.hom aU)
        (HomologicalComplex.toCycles_i (Work.Cohomology.singularChains ℤ (TopCat.of M))
          (m + 2) (m + 1))
      rw [ModuleCat.comp_apply] at h2
      exact h2
    rw [h1, ← hz_bdry]
    exact hzdef
  have hzero : ModuleCat.Hom.hom
      ((Work.Cohomology.singularChains ℤ (TopCat.of M)).homologyπ (m + 1)) ζ = 0 := by
    rw [← hζzed]
    have h2 := congrArg (fun (f : Ch (TopCat.of M) (m + 2) ⟶
        (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology (m + 1)) => f.hom aU)
      (HomologicalComplex.toCycles_comp_homologyπ (Work.Cohomology.singularChains ℤ (TopCat.of M))
        (m + 2) (m + 1))
    rw [ModuleCat.comp_apply, ModuleCat.hom_zero] at h2
    exact h2
  rw [← hζ]
  exact hzero

end

end Work.Compact.Noncompact
