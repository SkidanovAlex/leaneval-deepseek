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

/-! # The coker side of Step 4, in the form in which it is provable

The shrinking of `Work.CohomologicalShrinking.exists_shrinking_H1` (Prop 7(ii)) is applied to an
obstruction class in `H₁(Gal(N_m/K), E_m ⊗ μ_p^∨)` at a level `m ≥ n` *chosen by the shrinking*, and
the identification of the level-`n` obstruction with it uses a surjection `Φ : F(m) ↠ F(n)`
presenting the level-`n` data.  The level-`n` data of this node (obtained from
`hP : ∀ m, IsProperStage p K m i j`) does have such a presentation — it is produced by
`properStage_of_solvableStage` through `properStageAssemblyData`, which pushes down from a level
`m ≥ n` — but the presentation is not recoverable from the level-`n` data alone.  The coker side is
therefore stated here with `m`, `Φ` and the level-`m` stage-3 data as part of the existential, and
all its clauses are phrased for the push-downs `Φ ∘ φm`, `Φ ∘ ψm`.

The bundle that this input produces is consumed by
`Work.SSGRoute.step4_bundle_of_sha13` (see `Submission/Work/SSGRoute/step4_bundle_assembly.lean`). -/

/-! ## !! KNOWN DEFECT of `hreal` below (2026-09-26, H9 lane) — read `H9_STATUS.md` §3

A prover working on `Work.SSGRoute.step4CokerSide_holds` returned **declare_false** for this exact
statement.  The `hreal` clause is *too strong*: its guard only asks that `φ` be trivial on `D_A`,
but the paper imposes the cyclic / inertia-generated condition only at the places of *new
ramification* (where the twist is ramified).  It is the `T⁰` places that expose this: they are split
in `N_τ` and **unramified** in `N_{τ+1}`, so `M(I_{A}) = 1` while `M(D_A) ≅ ℤ/p` for some
`A₀ ∈ T⁰`; `hxsplit` + `hyT0` then force `x = 0` on `D_{A₀}` and on all its conjugates `A'`, and
`hreal` applied at a conjugate `A' ∉ T⁰` forces `M(D_{A'}) = M(I_{A'}) = 1` — contradiction.

Repair: add to `hreal`'s hypothesis the same guard that `hdich` uses,
`∃ σ ∈ decomp ℚ A, IsInertia ℚ A σ ∧ (flowTwistE p K n i j x ψ) σ ≠ 1`, and consume the corrected
side against `Work.SSGRoute.isScholzSolution_flowTwistEHom` (in `scholz_succ_of_properStage.lean`)
rather than through `Work.SSGRoute.step4_bundle_of_sha13`, which takes the strong shape.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

/-- **The coker side of Step 4** (SW pp. 30–31): at some level `m ≥ n`, presented at level `n` by an
operator map `Φ : F(m) ↠ F(n)`, the stage-3 data `(φm, ψm)`; the field `Λ` of the push-down of
`ψm`; the finite set `S` of places over `Ram(Λ) ∪ {p}`; the finite set `T⁰` (Chebotarev); a section
`sec`; the datum `y` (the local targets over `K` realised by a global cocycle) and the class `x`
with Theorem 13's clauses, together with the local-target realisation `hreal` and the local
dichotomy `hdich`. -/
def Step4CokerSide (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    [Normal ℚ K] (n i j : ℕ) : Prop :=
  ∃ (m : ℕ) (_ : 1 ≤ m) (_ : n ≤ m) (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2),
    IsProperStageData p K m i j φm ψm ∧
  ∃ (Λ : IntermediateField ℚ SSGRoute.QBar) (_ : FiniteDimensional ℚ Λ) (_ : IsGalois ℚ Λ)
    (_ : K ≤ Λ)
    (hΛker : ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm).ker
      = Λ.fixingSubgroup)
    (S T0 : Finset (ValuationSubring SSGRoute.QBar)) (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ)
    (y x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
      (((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ)
      = Work.SSGRoute.restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ),
    (∀ A ∈ S, SSGRoute.IsFinPlace ℚ A) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) ∧
    (∀ s : K ≃ₐ[ℚ] K, AlgEquiv.restrictNormalHom K (sec s) = s) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0) ∧
    (∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A,
      (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) = 0) ∧
    (∀ A ∈ T0, A ∈ S) ∧
    (∀ A ∈ T0, SSGRoute.IsSplitIn ℚ K A) ∧
    (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map
      ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm))
      = flowEKer p (K ≃ₐ[ℚ] K) n i j ∧
    (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map
      ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm))) ∧
    SSGRoute.IsLocConstOn ⊤ x ∧
    (∀ A ∈ S, SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s))) ∧
    (∀ A ∈ S, ¬ SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0) ∧
    (∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (Subgroup.zpowers c) x) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) →
      ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ SSGRoute.decomp ℚ B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ B ⊓ V) x) ∧
    (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x
          ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)
          hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A,
        ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm) σ = 1) →
      ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
        (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
        IsCyclic (Subgroup.closure
          ((flowTwistE p K n i j η
            ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm))
            '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          flowTwistE p K n i j η
            ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) τ
            = flowTwistE p K n i j η
              ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ) ∧
    (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      -- !! the `ψ`-guard: see `H9_STATUS.md` §11 -- without it this clause is FALSE (at the
      -- places of `ZDataGeneral`'s `IsGoodPlace` where `x` but not `ψ` ramifies)
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ ≠ 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x
          ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)
          hψquot hxmul) σ ≠ 1) →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x ∨
        ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
          (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
          IsCyclic (Subgroup.closure
            ((flowTwistE p K n i j η
              ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm))
              '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            flowTwistE p K n i j η
              ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) τ
              = flowTwistE p K n i j η
                ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)

end Work.SSGRoute
