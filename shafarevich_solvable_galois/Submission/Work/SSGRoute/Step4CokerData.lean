import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.stage3Defs
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.CohomologicalShrinking.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The *data* part of the coker side of Step 4, and the datum `y`

`Work.SSGRoute.Step4CokerSide` (`step4CokerSideDefs.lean`) is the whole coker side of Step 4 of
Schmidt–Wingberg §5.  This module splits it into

* `Step4CokerData p K n i j` — the *data*, free of arithmetic: the level `m ≥ n` with its stage-3
  data `(φm, ψm)`, the operator map `Φ : F(m) ↠ F(n)`, the field `Λ` of the push-down of `ψm`, the
  sets `S` (one place per prime over `Ram(Λ) ∪ {p}`) and `T⁰` (Chebotarev), and the section `sec`.
  It is produced from `hP : ∀ m, IsProperStage p K m i j` by `exists_stage3_data_at_level`,
  `exists_field_of_flowKernel`, `ramifiedPlaces_finite`, `exists_T0_split_generating` and
  `exists_section_restrict_one`.

* `Step4YData D y` — the *datum* `y` of the shrinking: the `1`-cocycle on `G_K` with the
  prescribed local behaviour (`hyS`, `hyT`, `hy0`), the vanishing `hyT0` of the formal corestriction
  on the decomposition groups of `T⁰`, together with the *local targets* at the places of new
  ramification — the finite set `Tnew ⊆ S` of the chosen prolongations, the functions `η_A` of
  `Work.SSGRoute.step4_local_target` with their five clauses, and the agreement
  `cor y|D_A = η_A`.

  The last item is what makes `hreal` provable: at `A ∈ Tnew` the twist `flowTwistE x ψ` agrees with
  `flowTwistE η_A ψ` on `D_A` (because `x = cor y = η_A` there), and `η_A` was chosen precisely so
  that this twist is cyclic with the inertia generating (`step4_local_target`).  At the other places
  where the twist ramifies the local clause is vacuous or transfers by conjugation
  (`Work.SSGRoute.hreal_conj_transfer`).

`Step4YData` is what `Work.SSGRoute.step4_y_exists` (a separate module) produces; the class `x` of
Theorem 13 is then produced from it by `SSGRoute.shafarevich_existence`, and the two local clauses
`hreal`, `hdich` are `Work.SSGRoute.step4_local_clauses`. -/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

/-- **The data part of the coker side of Step 4.**  Everything in `Step4CokerSide` except the
datum `y`, the class `x` and the two local clauses.

The clause `hSdisj` (the places of `S` are pairwise non-conjugate) is not asked for by
`Step4CokerSide`, but both `SSGRoute.coker_obstruction` and `SSGRoute.shafarevich_existence` need it
(their local data live at one place per prime), so it is recorded here.  `hSmin` says that `S` has no
superfluous elements, and `hT0unram` that the places of `T⁰` are unramified for `ψ` (they are split
in the τ-field and unramified in the τ+1-field); both are consequences of the constructions named in
the module docstring, and both are needed by the local clause check. -/
structure Step4CokerData (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) where
  m : ℕ
  hm : 1 ≤ m
  hnm : n ≤ m
  Φ : OperatorMap (K ≃ₐ[ℚ] K) m n
  φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j
  ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2
  data : IsProperStageData p K m i j φm ψm
  Λ : IntermediateField ℚ SSGRoute.QBar
  fdΛ : FiniteDimensional ℚ Λ
  galΛ : IsGalois ℚ Λ
  hKΛ : K ≤ Λ
  hΛker : ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm).ker
    = Λ.fixingSubgroup
  S : Finset (ValuationSubring SSGRoute.QBar)
  T0 : Finset (ValuationSubring SSGRoute.QBar)
  sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ
  hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A
  hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ℚ A B → A = B
  hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
    (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
    ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B
  hSmin : ∀ A ∈ S, A ∈ T0 ∨ SSGRoute.IsRamifiedIn ℚ Λ A ∨
    A.valuation (p : SSGRoute.QBar) < 1
  hsec : ∀ s : K ≃ₐ[ℚ] K, AlgEquiv.restrictNormalHom K (sec s) = s
  hT0S : ∀ A ∈ T0, A ∈ S
  hT0split : ∀ A ∈ T0, SSGRoute.IsSplitIn ℚ K A
  hT0unram : ∀ A ∈ T0, ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
    ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ = 1
  hT0gen : (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map
      ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm))
    = flowEKer p (K ≃ₐ[ℚ] K) n i j
  hT0cyc : ∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map
      ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm))

/-- **Plumbing for the composite field.**  `IsGalois ℚ K` is *not* found by `inferInstance` for a
`K : IntermediateField ℚ SSGRoute.QBar` satisfying `[FiniteDimensional ℚ K]`/`[Normal ℚ K]`,
although it holds (separability is automatic over `ℚ`, normality is the hypothesis).  Both
`SSGRoute.coker_obstruction` and `SSGRoute.shafarevich_existence` take it as an instance argument,
so provide it explicitly:

    haveI : IsGalois ℚ K := isGalois_of_normal K
    haveI : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ

(`Fintype (K ≃ₐ[ℚ] K)` follows from `FiniteDimensional ℚ K`.) -/
theorem isGalois_of_normal (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    [Normal ℚ K] : IsGalois ℚ K := IsGalois.mk

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-- The level-`n` stage-`τ+1` map of a coker-side datum. -/
noncomputable def Step4CokerData.psi (D : Step4CokerData p K n i j) :
    SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
  (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 D.Φ).comp D.ψm

/-- The level-`n` stage-`τ` map of a coker-side datum. -/
noncomputable def Step4CokerData.phi (D : Step4CokerData p K n i j) :
    SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
  (flowGroupMap p (K ≃ₐ[ℚ] K) i j D.Φ).comp D.φm

/-- **The datum `y` of the coker side, with the local targets at the places of new ramification.**

`Tnew` is the finite set of *chosen prolongations*: one place per prime whose prolongations to `K`
are ramified in the field `Λ` of `ψ` but not in the field of `φ` (the field cut out by `φ`; by
`hTnewcov` every place where `ψ` ramifies over `K`, is conjugate to an element of `S`, is not a
`T⁰`-place and has `φ` trivial on its decomposition group is a conjugate of a place of `Tnew`).
`ηt A hA` is the local target of `Work.SSGRoute.step4_local_target` at `A ∈ Tnew`: it vanishes on
the inertia of `A` and its twist with `ψ` has cyclic local group `= ` the image of the inertia.

The clause `hηtx` is the point of the whole construction: the *formal corestriction*
`∑_s s • y ((sec s)⁻¹ σ sec s)` agrees with `ηt A` on `D_A`.  Together with the coboundary clause
`hxsplit` of the coker side (which forces `x = cor y` on `D_A`, the action of `D_A ≤ G_K` being
trivial) this gives `x = η_A` on `D_A`, which is the last clause of `hreal`. -/
def Step4YData (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (D : Step4CokerData p K n i j)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j) : Prop :=
  (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ) ∧
  SSGRoute.IsLocConstOn K.fixingSubgroup y ∧
  (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
    (∀ A ∈ D.S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ D.Λ B →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0) ∧
  (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
    (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0) ∧
  (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
    (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
    (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0) ∧
  (∀ A ∈ D.T0, ∀ σ ∈ SSGRoute.decomp ℚ A,
    (∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * σ * D.sec s)) = 0) ∧
  -- the datum is `0` at the places where `φ` (the level-`n` stage-`τ` solution) ramifies: this is
  -- the paper's prescription `x_℘ = 0` for `℘ ∈ Ram(N_τ) ∪ S_p ∪ S_1 ∪ T⁰` (SW p. 30), and it
  -- is what makes the coboundary branch of `hdich` available at the places of *old* ramification
  -- (see `H9_STATUS.md` §12)
  (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
    (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
    (∃ σ, SSGRoute.IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1) →
    ∀ σ ∈ SSGRoute.decomp ℚ B, y σ = 0) ∧
  ∃ (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j),
    (∀ A ∈ Tnew, A ∈ D.S) ∧
    (∀ A ∈ Tnew, SSGRoute.IsFinPlace ℚ A) ∧
    (∀ A ∈ Tnew, ¬ A.valuation (p : SSGRoute.QBar) < 1) ∧
    (∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) ∧
    (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ D.T0 →
      (∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) →
      ∃ P ∈ Tnew, SSGRoute.IsConjPlace ℚ P A) ∧
    (∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A,
        ηt A hA (σ * τ) = ηt A hA σ + ηt A hA τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (ηt A hA) ∧
      (∀ σ, SSGRoute.IsInertia ℚ A σ → ηt A hA σ = 0) ∧
      IsCyclic (Subgroup.closure
        ((flowTwistE p K n i j (ηt A hA) D.psi) ''
          (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        flowTwistE p K n i j (ηt A hA) D.psi τ =
        flowTwistE p K n i j (ηt A hA) D.psi σ)) ∧
    (∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      ∀ σ ∈ SSGRoute.decomp ℚ A,
      (∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * σ * D.sec s)) = ηt A hA σ)

end Work.SSGRoute
