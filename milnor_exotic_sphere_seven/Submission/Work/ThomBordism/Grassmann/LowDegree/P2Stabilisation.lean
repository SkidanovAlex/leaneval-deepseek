import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.TangentClasses.Bundle
import Submission.Work.Projective.Basic
import Submission.Work.ThomBordism.Grassmann.CohMap_p2_incl
import Submission.Work.ThomBordism.Grassmann.Probe2.AddLineGauge
import Submission.Work.Thom.realSumStable
import Submission.Work.Thom.pontryaginClass_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# Stabilisation of the `p₂`-probe

`p₂(γ_{k,m})` is pulled back to itself by the two stabilisation maps of the Grassmannian (adding a
trivial line, and enlarging the ambient space).  Hence a probe detecting `p₂` at the base case
`(k₀,m₀) = (4,8)` — the plane `ℝ-span{Λ(z), iΛ(z), Λ'(z), iΛ'(z)} ⊂ ℂ⁶ = ℝ¹²` of
`Submission/Work/ThomBordism/Grassmann/LowDegree/P2Frame.lean` — gives, after composing with the
stabilisation `Ψ : G̃r₄(ℝ¹²) → G̃r_k(ℝ^{k+m})` of `chainP2`, a probe for every `k ≥ 4`, `m ≥ 8`.

The two one-step lemmas are ports of the corresponding lemmas of `LowDegree/p1SqProbe.lean`
(which proves the same statement for `p₁²` and `p₂` simultaneously, starting at `(2,8)`).
-/

namespace Work.ThomBordism.Grassmann.LowDegree

open Work.TangentClasses Work.Projective

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Stability of the Pontryagin classes under adding a trivial real line -/

/-- **Stability of `p_i` under adding a trivial real line summand**: if `Z' ≅ Z ⊕ ε¹` then
`p_i(Z') = p_i(Z)`. -/
theorem pontryaginClass_sumEpsR (i : ℕ) (ι₀ : Type) [Inhabited ι₀] {ι : Type} [Fintype ι]
    [Fintype ι₀] {k : ℕ} {ι' : Type} [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin (k + 1))) ι')
    (e : Work.Thom.BundleIso (Work.Thom.sumEpsR ι₀ Z) Z') :
    Work.Thom.pontryaginClass i Z' = Work.Thom.pontryaginClass i Z := by
  have h : Work.Thom.chernClass (k + 1) (2 * i) (Work.Thom.complexificationCore Z')
      = Work.Thom.chernClass k (2 * i) (Work.Thom.complexificationCore Z) :=
    Work.Thom.chernClass_complexification_sumEpsR ι₀ Z Z' e (2 * i)
  unfold Work.Thom.pontryaginClass
  exact congrArg (fun c => Work.Thom.cohTransport (show 2 * (2 * i) = 4 * i from by ring)
    (((-1 : ℤ) ^ i) • c)) h

/-! ## The one-step stabilisations for `p₂` -/

/-- The `k`-step, for an explicit bundle isomorphism. -/
theorem addLine_p2 {k m : ℕ} (φ : C(OG k m, OG (k + 1) m))
    (e : Work.Thom.BundleIso (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
      (Work.Thom.sumEpsR (Fin 1) (tautologicalBundle k m))) :
    (Work.Thom.CohMap φ ℤ 8).hom (p2 (k + 1) m) = p2 k m := by
  have hstab : Work.Thom.pontryaginClass 2
        (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
      = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) :=
    pontryaginClass_sumEpsR 2 (Fin 1) (tautologicalBundle k m)
      (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ) e.symm
  have hnat := (Work.Thom.pontryaginClass_comap (i := 2)
    (tautologicalBundle (k + 1) m) φ).symm
  rw [show p2 (k + 1) m = Work.Thom.pontryaginClass 2 (tautologicalBundle (k + 1) m)
        from rfl,
      show p2 k m = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) from rfl]
  rw [hnat, hstab]

/-- **The `k`-step**: the "add a line" map pulls `p₂(γ)` back to itself. -/
theorem stabilisation_addLine (k m : ℕ) :
    ∃ φ : C(OG k m, OG (k + 1) m),
      (Work.Thom.CohMap φ ℤ 8).hom (p2 (k + 1) m) = p2 k m := by
  obtain ⟨φ, ⟨e⟩⟩ := Probe2.addLineBundleIso k m (Fin 1)
  exact ⟨φ, addLine_p2 φ e⟩

/-- **The `m`-step**: the ambient inclusion pulls `p₂(γ)` back to itself. -/
theorem stabilisation_incl (k m : ℕ) :
    ∃ φ : C(OG k m, OG k (m + 1)),
      (Work.Thom.CohMap φ ℤ 8).hom (p2 k (m + 1)) = p2 k m :=
  CohMap_p2_incl k m

/-! ## The stabilisation from `(4,8)` to `(k,m)` -/

/-- **Stabilisation of `p₂`**: for `4 ≤ k`, `8 ≤ m` there is `Ψ : G̃r₄(ℝ¹²) → G̃r_k(ℝ^{k+m})`
pulling `p₂(γ_{k,m})` back to `p₂(γ_{4,8})`. -/
theorem chainP2 (k m : ℕ) (hk : 4 ≤ k) (hm : 8 ≤ m) :
    ∃ Ψ : C(OG 4 8, OG k m),
      (Work.Thom.CohMap Ψ ℤ 8).hom (p2 k m) = p2 4 8 := by
  have hstepM : ∀ (e : ℕ), ∃ Ψ : C(OG 4 8, OG 4 (8 + e)),
      (Work.Thom.CohMap Ψ ℤ 8).hom (p2 4 (8 + e)) = p2 4 8 := by
    intro e
    induction e with
    | zero =>
      refine ⟨ContinuousMap.id _, ?_⟩
      rw [Work.Thom.CohMap_id]
      rfl
    | succ e ih =>
      obtain ⟨Ψ, h2⟩ := ih
      obtain ⟨φ, hφ2⟩ := stabilisation_incl 4 (8 + e)
      refine ⟨φ.comp Ψ, ?_⟩
      change (Work.Thom.CohMap (φ.comp Ψ) ℤ 8).hom (p2 4 (8 + e + 1)) = p2 4 8
      rw [Work.Thom.CohMap_comp Ψ φ ℤ 8]
      change (Work.Thom.CohMap Ψ ℤ 8).hom
        ((Work.Thom.CohMap φ ℤ 8).hom (p2 4 (8 + e + 1))) = p2 4 8
      rw [hφ2, h2]
  have hstepK : ∀ (m d : ℕ), ∃ Ψ : C(OG 4 m, OG (4 + d) m),
      (Work.Thom.CohMap Ψ ℤ 8).hom (p2 (4 + d) m) = p2 4 m := by
    intro m d
    induction d with
    | zero =>
      refine ⟨ContinuousMap.id _, ?_⟩
      rw [Work.Thom.CohMap_id]
      rfl
    | succ d ih =>
      obtain ⟨Ψ, h2⟩ := ih
      obtain ⟨φ, hφ2⟩ := stabilisation_addLine (4 + d) m
      refine ⟨φ.comp Ψ, ?_⟩
      change (Work.Thom.CohMap (φ.comp Ψ) ℤ 8).hom (p2 (4 + d + 1) m) = p2 4 m
      rw [Work.Thom.CohMap_comp Ψ φ ℤ 8]
      change (Work.Thom.CohMap Ψ ℤ 8).hom
        ((Work.Thom.CohMap φ ℤ 8).hom (p2 (4 + d + 1) m)) = p2 4 m
      rw [hφ2, h2]
  obtain ⟨e, rfl⟩ : ∃ e, m = 8 + e := ⟨m - 8, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = 4 + d := ⟨k - 4, by omega⟩
  obtain ⟨ΨM, hM⟩ := hstepM e
  obtain ⟨ΨK, hK⟩ := hstepK (8 + e) d
  refine ⟨ΨK.comp ΨM, ?_⟩
  rw [Work.Thom.CohMap_comp ΨM ΨK ℤ 8]
  change (Work.Thom.CohMap ΨM ℤ 8).hom
    ((Work.Thom.CohMap ΨK ℤ 8).hom (p2 (4 + d) (8 + e))) = p2 4 8
  rw [hK, hM]

/-- **The `p₂`-probe from the base case `(4,8)`**: if a map `ℂP⁴ → G̃r₄(ℝ¹²)` detects `p₂`, then so
does a map `ℂP⁴ → G̃r_k(ℝ^{k+m})` for every `k ≥ 4`, `m ≥ 8`. -/
theorem p2ProbeCP4_of_base
    (hbase : ∃ σ : C(CP 4, OG 4 8),
      TensorProduct.tmul ℤ (1 : ℚ) ((Work.Thom.CohMap σ ℤ 8).hom (p2 4 8)) ≠ 0)
    (k m : ℕ) (hk : 4 ≤ k) (hm : 8 ≤ m) :
    ∃ σ : C(CP 4, OG k m),
      TensorProduct.tmul ℤ (1 : ℚ) ((Work.Thom.CohMap σ ℤ 8).hom (p2 k m)) ≠ 0 := by
  obtain ⟨σ, hσ⟩ := hbase
  obtain ⟨Ψ, hΨ⟩ := chainP2 k m hk hm
  refine ⟨Ψ.comp σ, ?_⟩
  rw [Work.Thom.CohMap_comp σ Ψ ℤ 8]
  change TensorProduct.tmul ℤ (1 : ℚ)
    ((Work.Thom.CohMap σ ℤ 8).hom ((Work.Thom.CohMap Ψ ℤ 8).hom (p2 k m))) ≠ 0
  rw [hΨ]
  exact hσ

end

end Work.ThomBordism.Grassmann.LowDegree
