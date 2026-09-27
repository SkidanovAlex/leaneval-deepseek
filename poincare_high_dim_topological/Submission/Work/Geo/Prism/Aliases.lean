import Submission.Work.Geo.Prism.PushRel.prism_push_rel
import Submission.Work.Geo.Prism.Join.join_simplex_prism
import Submission.Work.Geo.Prism.Convex.prism_convex_piece

/-!
# Blueprint names for the three main results of area A1

The results proved in the subdirectories carry their path-derived names
(`Work.Geo.Prism.PushRel.prism_push_rel`, `Work.Geo.Prism.Join.join_simplex_prism`,
`Work.Geo.Prism.Convex.prism_convex_piece`).  This file re-exports them under the names used
in the blueprint (`Submission/Work/NOTES_LEAD_poincare_blueprint.md` §2 G1', G2, §5 A1.6)
and in `Submission/Work/Engulf/Tools.lean` (`PrismPushRelForm`, `JoinPrismForm`).
-/

open Set Metric
open scoped Topology

namespace Work.Geo.Prism

/-- Blueprint name of G1' (`PrismPushRelForm` of `Work.Engulf`). -/
theorem prism_push_rel {a b : ℕ} (F J : Set (PL.E b)) (hF : IsCompact F) (hJ : IsClosed J)
    (hJF : J ⊆ F) (γ₀ γ₁ : PL.E b → ℝ) (h₀ : Continuous γ₀) (h₁ : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z) (hfr : ∀ z ∈ frontier F, γ₀ z = γ₁ z)
    (U W A : Set (Pr a b)) (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hbase : ∀ z ∈ F, ((0 : PL.E a), z, γ₀ z) ∈ U)
    (hJU : ∀ z ∈ J, ∀ t ∈ Icc (γ₀ z) (γ₁ z), ((0 : PL.E a), z, t) ∈ U)
    (hS : ∀ z ∈ F, ∀ t ∈ Icc (γ₀ z) (γ₁ z), ((0 : PL.E a), z, t) ∈ W)
    (hAS : ∀ z ∈ F, ∀ t ∈ Icc (γ₀ z) (γ₁ z),
      ((0 : PL.E a), z, t) ∈ A → t = γ₀ z ∨ z ∈ J) :
    ∃ h : Pr a b ≃ₜ Pr a b, PL.CSupp h W ∧ (∀ x ∈ A, h x = x) ∧
      ∀ z ∈ F, ∀ t ∈ Icc (γ₀ z) (γ₁ z), ((0 : PL.E a), z, t) ∈ h '' U :=
  PushRel.prism_push_rel F J hF hJ hJF γ₀ γ₁ h₀ h₁ hle hfr U W A hU hW hA hAU hbase hJU hS hAS

/-- Blueprint name of G2 (`JoinPrismForm` of `Work.Engulf`). -/
theorem join_simplex_prism {n q : ℕ} (hq : q + 1 ≤ n) (τ₀ τ₁ : Finset (PL.E n))
    (hne₀ : τ₀.Nonempty) (hne₁ : τ₁.Nonempty) (hdisj : Disjoint τ₀ τ₁)
    (hcard : (τ₀ ∪ τ₁).card = q + 2)
    (hind : AffineIndependent ℝ (fun v : (τ₀ ∪ τ₁ : Finset (PL.E n)) => (v : PL.E n))) :
    ∃ (T : PL.E n ≃ᵃ[ℝ] Pr (n - q - 1) q) (F : Set (PL.E q)) (γ₀ γ₁ : PL.E q → ℝ),
      IsCompact F ∧ Convex ℝ F ∧ Continuous γ₀ ∧ Continuous γ₁ ∧
      ConvexPL γ₀ ∧ ConcavePL γ₁ ∧
      (∀ z ∈ F, γ₀ z ≤ γ₁ z) ∧ (∀ z ∈ frontier F, γ₀ z = γ₁ z) ∧
      T '' PL.simp (τ₀ ∪ τ₁) = {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} ∧
      T '' (⋃ w ∈ τ₁, PL.simp ((τ₀ ∪ τ₁).erase w)) =
        {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1} ∧
      T '' (⋃ w ∈ τ₀, PL.simp ((τ₀ ∪ τ₁).erase w)) =
        {x | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₁ x.2.1} :=
  Join.join_simplex_prism hq τ₀ τ₁ hne₀ hne₁ hdisj hcard hind

/-- Blueprint name of `prism_convex_piece` (§5 item A1.6). -/
theorem prism_convex_piece {q : ℕ} (j : Set (PL.E q)) (d : ℤ) (hj : Convex ℝ j)
    (hjc : IsCompact j) (hjd : PL.DomDim j d) {γ₀ γ₁ : PL.E q → ℝ}
    (h₀ : ConvexPL γ₀) (h₁ : ConcavePL γ₁) :
    Convex ℝ {p : PL.E q × ℝ | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ∧ p.2 ≤ γ₁ p.1} ∧
      DomDim₂ {p : PL.E q × ℝ | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ∧ p.2 ≤ γ₁ p.1} (d + 1) :=
  Convex.prism_convex_piece j d hj hjc hjd h₀ h₁

end Work.Geo.Prism
