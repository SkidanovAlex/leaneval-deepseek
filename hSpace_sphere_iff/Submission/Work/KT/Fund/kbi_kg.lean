import Mathlib
import Submission.Work.KT.Fund.kbi_defs
import Submission.Work.KT.Fund.kbi_hopf2

/-!
# `Work.KT.Fund.kbi_kg` — the two-disc decomposition is compatible with the pullback along `X`

`pullAlg2 X` is the fibre product of the two disc algebras `C(X × D, ℂ)` over the circle algebra
`C(X × S¹, ℂ)`, and `k0Glue X : K₀ C(X × S², ℂ) ≃ K₀ ↥(pullAlg2 X)` is the induced isomorphism
(`Work.KT.Fund.Pullback`).  The present file records how it interacts with pullback along the
projection `X × S² → X`:

* `kbi_kg_glue_natural` — the *naturality* of `k0Glue` with respect to `X`: for any matrix `M` over
  `C(X, ℂ)` the class of the pullback `fst^*(M)` along the first projection is the class of `M`
  pushed forward along the diagonal pullback `KBI.diagPull X : C(X, ℂ) →+* ↥(pullAlg2 X)`
  (the ring homomorphism `C(X, ℂ) → C(X × S², ℂ) → ↥(pullAlg2 X)`).
* `kbi_kg` assembles this for `M = P` and `M = 1 - P`, together with the Hopf conjunct
  `KBI.hopf`-style statement (proved in `Work.KT.Fund.kbi_hopf2`).

The two easy conjuncts are unconditional in the matrix `M`; the argument is purely formal
(`K₀`-functoriality) except for one point: when `M` is *not* idempotent, `K₀.map` sends `cls M` to
`0`, so one must know that `M.map (diagPull X)` is not idempotent either — which holds because
`diagPull X` is injective (`kbi_kg_diagPull_injective`).  This is also what makes the statement
of `kbi_kg` correct without any idempotence hypothesis on `P`.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

/-! ## Idempotence of matrices, backwards along an injective ring map -/

/-- Idempotence of `p.map φ` implies idempotence of `p` when `φ` is injective (as a function). -/
lemma kbi_kg_isIdem_of_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S)
    (hφ : Function.Injective φ) {p : Work.KT.Mat R} (h : (p.map φ).IsIdem) : p.IsIdem := by
  have h' : (p.2 * p.2).map ⇑φ = p.2.map ⇑φ := by
    rw [Matrix.map_mul]
    exact h
  show p.2 * p.2 = p.2
  ext i j
  exact hφ (by
    have := congrFun (congrFun h' i) j
    simpa [Matrix.map_apply] using this)

/-- `K₀` of a matrix under an injective coefficient ring map: `[p] ↦ [p.map φ]`, unconditionally
(no idempotence hypothesis), because an injective ring map reflects non-idempotence. -/
lemma kbi_kg_map_cls_of_injective {R S : Type} [Ring R] [Ring S] (φ : R →+* S)
    (hφ : Function.Injective φ) (p : Work.KT.Mat R) :
    Work.KT.K0.map φ (Work.KT.cls p) = Work.KT.cls (p.map φ) := by
  rw [Work.KT.K0.map_cls']
  by_cases hp : p.IsIdem
  · rw [Work.KT.mapCls_of_idem φ hp]
  · rw [show Work.KT.mapCls φ p = 0 from by unfold Work.KT.mapCls; rw [if_neg hp]]
    exact (Work.KT.cls_of_not_idem (fun hh => hp (kbi_kg_isIdem_of_map φ hφ hh))).symm

/-! ## Injectivity of the diagonal pullback -/

/-- The diagonal pullback `KBI.diagPull X : C(X, ℂ) →+* ↥(pullAlg2 X)` is injective: its first
component is the pullback along `X × D → X`, and `X × D → X` is surjective. -/
lemma kbi_kg_diagPull_injective (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    Function.Injective (KBI.diagPull X) := by
  have hcomp : ∀ x : C(X, ℂ),
      (↑(KBI.diagPull X x) : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)).1
        = pullUp X (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)) x) := fun x => rfl
  intro f g h
  have h1 := congrArg (fun z : ↥(pullAlg2 X) =>
    (↑z : C(X × Ball ℂ, ℂ) × C(X × Ball ℂ, ℂ)).1) h
  rw [hcomp f, hcomp g] at h1
  have h2 : Work.KT.pullAlg (ContinuousMap.fst : C(X × Ball ℂ, X)) f
      = Work.KT.pullAlg (ContinuousMap.fst : C(X × Ball ℂ, X)) g := by
    ext p
    have := congrArg (fun (u : C(X × Ball ℂ, ℂ)) => u p) h1
    simpa [pullUp_apply, Work.KT.Fund.pullAlg_apply'] using this
  ext x
  have := congrArg (fun (u : C(X × Ball ℂ, ℂ)) =>
    u (x, (⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩ : Ball ℂ))) h2
  simpa [Work.KT.Fund.pullAlg_apply'] using this

/-! ## Naturality of `k0Glue` with respect to the base `X` -/

/-- **`k0Glue` is natural along the projection `X × S² → X`.**  For any matrix `M` over `C(X, ℂ)`,
the class of its pullback along `fst` is the class of `M` pushed along the diagonal pullback
`KBI.diagPull X`. -/
lemma kbi_kg_glue_natural (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (k0Glue X) (Work.KT.K0.mapA (Work.KT.pullAlg
        (ContinuousMap.fst : C(X × Work.KT.S2, X)))
        (Work.KT.cls (⟨n, M⟩ : Work.KT.Mat C(X, ℂ))))
      = Work.KT.cls (⟨n, M.map (KBI.diagPull X)⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
  -- `k0Glue` is `K₀` of `glueEquiv`, and `KBI.diagPull X = glueEquiv ∘ pullAlg fst`.
  show Work.KT.K0.map (glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X)
      (Work.KT.K0.map ((Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom)
        (Work.KT.cls (⟨n, M⟩ : Work.KT.Mat C(X, ℂ)))) = _
  rw [← Work.KT.K0.map_comp_apply ((Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X))).toRingHom)
    (glueEquiv X : C(X × S2, ℂ) →+* pullAlg2 X) (Work.KT.cls (⟨n, M⟩ : Work.KT.Mat C(X, ℂ)))]
  exact kbi_kg_map_cls_of_injective (KBI.diagPull X)
    (kbi_kg_diagPull_injective X) (⟨n, M⟩ : Work.KT.Mat C(X, ℂ))

/-! ## The theorem -/

theorem kbi_kg (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : (Work.KT.Fund.KBI.h1e X).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (Work.KT.Fund.KBI.h2e X).map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    ((Work.KT.Fund.k0Glue X) (Work.KT.K0.mapA (Work.KT.pullAlg
        (ContinuousMap.fst : C(X × Work.KT.S2, X)))
          (Work.KT.cls (⟨n, P⟩ : Work.KT.Mat C(X, ℂ))))
        = Work.KT.cls (⟨n, Work.KT.Fund.KBI.PR X n P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) ∧
      ((Work.KT.Fund.k0Glue X) (Work.KT.K0.mapA (Work.KT.pullAlg
        (ContinuousMap.fst : C(X × Work.KT.S2, X)))
          (Work.KT.cls (⟨n, 1 - P⟩ : Work.KT.Mat C(X, ℂ))))
        = Work.KT.cls (⟨n, Work.KT.Fund.KBI.QR X n P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))) ∧
      ((Work.KT.Fund.k0Glue X) (Work.KT.K0.mapA (Work.KT.pullAlg
        (ContinuousMap.snd : C(X × Work.KT.S2, Work.KT.S2)))
          (Work.KT.cls Work.KT.hopfIdem))
        = Work.KT.cls (Work.KT.Fund.pairIdem X (Work.KT.Fund.KBI.h1e X)
            (Work.KT.Fund.KBI.h2e X) h)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact kbi_kg_glue_natural X n P
  · exact kbi_kg_glue_natural X n (1 - P)
  · exact kbi_hopf2 X h

end

end Work.KT.Fund
