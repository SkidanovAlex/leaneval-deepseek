import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.B3.P_bilinear
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.D.psi.chartJetOf_jSym_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The time derivative of the energy `galE` along the span-form Galerkin scheme

`galE D k ε c = D.ENormB k (galState D ε c) + D.ENormB 0 (galState D ε c)` is the physical `Hᵏ`
energy (plus its `L²` part) of the metric `galState D ε c = g₀.inner + genMap D ε c`.

The point of this file is that `galE D k ε` is a **quadratic polynomial in the coefficients** `c`:
`genMap D ε c = Σ_z c z • jSym D ε z` is linear in `c`, and the pairing `D.ENormB_pair k` is a
symmetric bilinear form whose quadratic form is `D.ENormB k` (both proved in
`Submission/Work/Diff/STE/B3/P_bilinear.lean`).  Hence for *any* curve `c : ℝ → Coef` that is
differentiable (at a single point `t`) with derivative `c'`, the energy has derivative

  `(galE D k ε (c s))' = 2 (D.ENormB_pair k (genMap D ε c') (galState D ε (c t))
                          + D.ENormB_pair 0 (genMap D ε c') (galState D ε (c t)))`   at `t`.

The proof is the expansion of a quadratic polynomial:
* the **value identity** `galE D k ε (c + u) = galE D k ε c + L u + Q u`, where
  `L u = 2 (P k (genMap u) (galState c) + P 0 (genMap u) (galState c))` is linear and
  `Q u = P k (genMap u) (genMap u) + P 0 (genMap u) (genMap u)` is quadratic;
* the **finite-sum expansions** `L u = Σ_z u z • Lz` and `Q u = Σ_{z,z'} u z u z' Kz` obtained from
  the bilinearity of the pairing over the spanning family `jSym D ε`;
* the chain rule: `s ↦ L (c s - c t)` has derivative `L c'` (product rule on the coordinates), and
  `s ↦ Q (c s - c t)` has derivative `0` at `t` because every summand `u z · u z' · Kz` is a
  product of two factors that vanish at `t`.
-/

namespace Work.Diff.STE.Lead.Gal

open Classical LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Elementary structural facts -/

/-- `genMap` is additive in its coefficients. -/
lemma galE_genMap_add (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c u : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c + u)
      = Work.Diff.STE.D.genMap (I := I) (M := M) D ε c
        + Work.Diff.STE.D.genMap (I := I) (M := M) D ε u := by
  ext x a b
  simp only [Work.Diff.STE.D.genMap, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
    smul_apply, sum_apply, add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, add_smul, Finset.sum_add_distrib]

/-- `genMap` is homogeneous in its coefficients. -/
lemma galE_genMap_smul (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε r : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε (r • c)
      = r • Work.Diff.STE.D.genMap (I := I) (M := M) D ε c := by
  ext x a b
  simp only [Work.Diff.STE.D.genMap, Finset.sum_apply, Pi.smul_apply, smul_apply,
    sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z _ => by ring)

/-- **`galState` is additive**: adding coefficients on top of `c t` adds `genMap` of the
increment to the state, exactly as the expansion of the energy needs. -/
lemma galE_galState_add (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c u : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    Submission.Diff.STEGal.galState D ε (c + u)
      = Submission.Diff.STEGal.galState D ε c + Work.Diff.STE.D.genMap (I := I) (M := M) D ε u := by
  ext x a b
  simp only [Submission.Diff.STEGal.galState, Work.Diff.STE.D.addSec_apply, Pi.add_apply,
    ContinuousLinearMap.add_apply, galE_genMap_add, add_assoc]

/-! ## The component-smoothness predicate -/

/-- The component-smoothness predicate of Layer B3: every localised component of the section is
`C^∞`.  This is the regularity hypothesis of the bilinearity laws of the pairing
`D.ENormB_pair k`. -/
abbrev galE_sm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (u : Work.Diff.STE.Bil (I := I) (M := M)) : Prop :=
  ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)

/-- The localised component is additive in the section (from the definitions). -/
lemma galE_R_add (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h k : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (h + k) a b = D.R i h a b + D.R i k a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.add_apply,
    ContinuousLinearMap.add_apply]
  ring

/-- The localised component is homogeneous in the section (from the definitions). -/
lemma galE_R_smul (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (r : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (r • h) a b = r • D.R i h a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Component smoothness of `galState D ε c` from the chart data of the background metric. -/
lemma galE_sm_galState (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    galE_sm D (Submission.Diff.STEGal.galState D ε c) :=
  fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData D _
    (Work.Diff.STE.Lead.chartData_galState D ε hg c) i a b

/-- Component smoothness of `genMap D ε c`. -/
lemma galE_sm_genMap (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    galE_sm D (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) :=
  fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData D _
    (Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε c) i a b

/-- Component smoothness of a member of the spanning family `jSym D ε`. -/
lemma galE_sm_jSym (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    galE_sm D (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) :=
  fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData D _
    (Work.Diff.STE.D.psi.jSym_chartData (I := I) (M := M) D ε z) i a b

/-! ## The bilinearity laws of the pairing -/

/-- **The bilinearity laws of the pairing `D.ENormB_pair k`**, extracted from
`Work.Diff.STE.B3.P_bilinear` (`Submission/Work/Diff/STE/B3/P_bilinear.lean`) and *specialised to
the concrete coefficient index type* `JIdx ι₀ (finrank ℝ E) ε`: the two finite-sum laws are stated
for that concrete index type instead of a universe-polymorphic `{ι : Type*}`.  The reason is that a
single conjunct of a conjunction which contains a universe-polymorphic binder cannot be extracted
on its own (Lean leaves the universe level of that binder unsolved and rejects the declaration), so
the six laws are extracted in one place, where the two polymorphic conjuncts *are* instantiated
concretely. -/
lemma galE_laws (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ) :
    (∀ (u v w : Work.Diff.STE.Bil (I := I) (M := M)), galE_sm D u → galE_sm D v → galE_sm D w →
      D.ENormB_pair k (u + v) w = D.ENormB_pair k u w + D.ENormB_pair k v w)
    ∧ (∀ (r : ℝ) (u w : Work.Diff.STE.Bil (I := I) (M := M)), galE_sm D u → galE_sm D w →
      D.ENormB_pair k (r • u) w = r * D.ENormB_pair k u w)
    ∧ (∀ u : Work.Diff.STE.Bil (I := I) (M := M), D.ENormB_pair k u u = D.ENormB k u)
    ∧ (∀ u v : Work.Diff.STE.Bil (I := I) (M := M),
      D.ENormB_pair k u v = D.ENormB_pair k v u)
    ∧ (∀ (B : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε →
          Work.Diff.STE.Bil (I := I) (M := M))
        (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
        (W : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ z, galE_sm D (B z)) → galE_sm D W →
        D.ENormB_pair k (∑ z, w z • B z) W = ∑ z, w z * D.ENormB_pair k (B z) W)
    ∧ (∀ (B : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε →
          Work.Diff.STE.Bil (I := I) (M := M))
        (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        (∀ z, galE_sm D (B z)) →
        D.ENormB_pair k (∑ z, w z • B z) (∑ z, w z • B z)
          = ∑ z, ∑ z', w z * w z' * D.ENormB_pair k (B z) (B z')) := by
  have h := Work.Diff.STE.B3.P_bilinear (I := I) (M := M) D k
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun B w W hB hW => h.2.2.2.2.1 B w W hB hW,
    fun B w hB => h.2.2.2.2.2 B w hB⟩

/-! ## The energy of a sum of sections -/

/-- **The second-order expansion of the energy at a pair of sections.**  This is the polarisation
of the quadratic form `D.ENormB k` with respect to the pairing `D.ENormB_pair k`. -/
lemma galE_ENormB_add (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (H W : Work.Diff.STE.Bil (I := I) (M := M))
    (hH : galE_sm D H) (hW : galE_sm D W) (hHW : galE_sm D (H + W)) :
    D.ENormB k (H + W)
      = D.ENormB k H + 2 * D.ENormB_pair k W H + D.ENormB_pair k W W := by
  obtain ⟨Padd, Psmul, Pself, Pcomm, Psum, Psumself⟩ := galE_laws D k ε
  have e1 : D.ENormB_pair k (H + W) (H + W)
      = D.ENormB_pair k H (H + W) + D.ENormB_pair k W (H + W) :=
    Padd H W (H + W) hH hW hHW
  have e2 : D.ENormB_pair k H (H + W) = D.ENormB_pair k H H + D.ENormB_pair k H W := by
    rw [Pcomm H (H + W), Padd H W H hH hW hH, Pcomm W H]
  have e3 : D.ENormB_pair k W (H + W) = D.ENormB_pair k H W + D.ENormB_pair k W W := by
    rw [Pcomm W (H + W), Padd H W W hH hW hW]
  have e4 : D.ENormB_pair k H W = D.ENormB_pair k W H := Pcomm H W
  rw [← Pself (H + W), e1, e2, e3, e4, Pself H, Pself W]
  ring

/-! ## The expansions of the linear and the quadratic part over the spanning family -/

/-- **The linear part of the energy expansion is a linear combination of the spanning family.** -/
lemma galE_pair_genMap_sum (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (H : Work.Diff.STE.Bil (I := I) (M := M)) (hH : galE_sm D H)
    (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    D.ENormB_pair k (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w) H
      = ∑ z, w z * D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) H := by
  obtain ⟨Padd, Psmul, Pself, Pcomm, Psum, Psumself⟩ := galE_laws D k ε
  have h := Psum (fun z => Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) w H
    (fun z => galE_sm_jSym D ε z) hH
  simpa only [Work.Diff.STE.D.genMap] using h

/-- **The quadratic part of the energy expansion is a quadratic form in the coefficients.** -/
lemma galE_pair_genMap_self (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    D.ENormB_pair k (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)
      = ∑ z, ∑ z', w z * w z' *
          D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
            (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z') := by
  obtain ⟨Padd, Psmul, Pself, Pcomm, Psum, Psumself⟩ := galE_laws D k ε
  have h := Psumself (fun z => Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) w
    (fun z => galE_sm_jSym D ε z)
  simpa only [Work.Diff.STE.D.genMap] using h

/-! ## The linear and the quadratic part of the energy -/

/-- The **linear part** of the energy at the state `H`: `u ↦ 2 ((u : genMap) ∪ H)`. -/
noncomputable def galE_Lin (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (H : Work.Diff.STE.Bil (I := I) (M := M))
    (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) : ℝ :=
  2 * (D.ENormB_pair k (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w) H
        + D.ENormB_pair 0 (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w) H)

/-- The **quadratic part** of the energy: `u ↦ ((u : genMap) ∪ (u : genMap))`. -/
noncomputable def galE_Quad (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) : ℝ :=
  D.ENormB_pair k (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)
    + D.ENormB_pair 0 (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)

/-- The **value identity**: the energy of `galState D ε (c + u)` is the energy of `galState D ε c`
plus the linear and the quadratic part of the increment. -/
lemma galE_add_expansion (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (c u : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    galE D k ε (c + u)
      = galE D k ε c + galE_Lin D k ε (Submission.Diff.STEGal.galState D ε c) u
        + galE_Quad D k ε u := by
  have hstate : Submission.Diff.STEGal.galState D ε (c + u)
      = Submission.Diff.STEGal.galState D ε c + Work.Diff.STE.D.genMap (I := I) (M := M) D ε u :=
    galE_galState_add D ε c u
  have hH : galE_sm D (Submission.Diff.STEGal.galState D ε c) := galE_sm_galState D ε hg c
  have hW : galE_sm D (Work.Diff.STE.D.genMap (I := I) (M := M) D ε u) := galE_sm_genMap D ε u
  have hHW : galE_sm D (Submission.Diff.STEGal.galState D ε c
      + Work.Diff.STE.D.genMap (I := I) (M := M) D ε u) := by
    rw [← hstate]
    exact galE_sm_galState D ε hg (c + u)
  have hk := galE_ENormB_add D k ε (Submission.Diff.STEGal.galState D ε c)
    (Work.Diff.STE.D.genMap (I := I) (M := M) D ε u) hH hW hHW
  have h0 := galE_ENormB_add D 0 ε (Submission.Diff.STEGal.galState D ε c)
    (Work.Diff.STE.D.genMap (I := I) (M := M) D ε u) hH hW hHW
  simp only [galE, galE_Lin, galE_Quad]
  rw [hstate, hk, h0]
  ring

/-- The **``L``-expansion**: the linear part is a finite linear combination of the values on the
spanning family `jSym`. -/
lemma galE_Lin_eq_sum (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (H : Work.Diff.STE.Bil (I := I) (M := M)) (hH : galE_sm D H) :
    ∀ w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      galE_Lin D k ε H w
        = ∑ z, w z * (2 * (D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) H
            + D.ENormB_pair 0 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) H)) := by
  intro w
  rw [galE_Lin, galE_pair_genMap_sum D k ε H hH w, galE_pair_genMap_sum D 0 ε H hH w]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  ring

/-- The **``Q``-expansion**: the quadratic part is a quadratic form in the coefficients. -/
lemma galE_Quad_eq_sum (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ) :
    ∀ w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      galE_Quad D k ε w
        = ∑ z, ∑ z', w z * w z' *
            (D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z')
              + D.ENormB_pair 0 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z')) := by
  intro w
  rw [galE_Quad, galE_pair_genMap_self D k ε w, galE_pair_genMap_self D 0 ε w]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun z' _ => ?_)
  ring

end

theorem hasDerivAt_galE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    {c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)}
    {c' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ} {t : ℝ}
    (h : HasDerivAt c c' t) :
    HasDerivAt (fun s => Work.Diff.STE.Lead.galE D k ε (c s))
      (2 * (D.ENormB_pair k (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c')
              (Submission.Diff.STEGal.galState D ε (c t))
            + D.ENormB_pair 0 (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c')
              (Submission.Diff.STEGal.galState D ε (c t)))) t := by
  classical
  -- the increment of the coefficients, and its derivative
  set u : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :=
    fun s => c s - c t with hu_def
  have hu : HasDerivAt u c' t := by
    rw [hu_def]
    exact h.sub_const (c t)
  have hut : u t = 0 := by
    funext z
    simp only [hu_def, Pi.sub_apply, sub_self, Pi.zero_apply]
  -- the pointwise derivatives of the coordinates of `u`
  have huz : ∀ z, HasDerivAt (fun s => u s z) (c' z) t := by
    intro z
    have hl : HasFDerivAt (fun w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ => w z)
        (ContinuousLinearMap.proj z) (c t) :=
      hasFDerivAt_apply (𝕜 := ℝ) z (c t)
    have hc : HasDerivAt (fun s => (c s) z) (c' z) t := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using hl.comp_hasDerivAt t h
    have h1 : HasDerivAt (fun s => (c s) z - (c t) z) (c' z) t := hc.sub_const ((c t) z)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hu_def, Pi.sub_apply]
  -- the value identity
  have hval : ∀ s, Work.Diff.STE.Lead.galE D k ε (c s)
      = Work.Diff.STE.Lead.galE D k ε (c t)
        + galE_Lin D k ε (Submission.Diff.STEGal.galState D ε (c t)) (u s)
        + galE_Quad D k ε (u s) := by
    intro s
    have h1 : c t + u s = c s := by
      simp only [hu_def]
      abel
    have h := galE_add_expansion D k ε hg (c t) (u s)
    rwa [h1] at h
  -- the derivative of the linear part
  have hL : HasDerivAt (fun s => galE_Lin D k ε (Submission.Diff.STEGal.galState D ε (c t)) (u s))
      (galE_Lin D k ε (Submission.Diff.STEGal.galState D ε (c t)) c') t := by
    have hH : galE_sm D (Submission.Diff.STEGal.galState D ε (c t)) :=
      galE_sm_galState D ε hg (c t)
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun z (_ : z ∈ Finset.univ) => (huz z).mul_const
        (2 * (D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Submission.Diff.STEGal.galState D ε (c t))
              + D.ENormB_pair 0 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Submission.Diff.STEGal.galState D ε (c t)))))
    refine hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (galE_Lin_eq_sum D k ε _ hH (u s))) |>.congr_deriv ?_
    exact (galE_Lin_eq_sum D k ε _ hH c').symm
  -- the derivative of the quadratic part
  have hQ : HasDerivAt (fun s => galE_Quad D k ε (u s)) 0 t := by
    have hterm : ∀ z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        HasDerivAt (fun s => u s z * u s z' *
            (D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z')
              + D.ENormB_pair 0 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z'))) 0 t := by
      intro z z'
      have h1 := ((huz z).mul (huz z')).mul_const
        (D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
            (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z')
          + D.ENormB_pair 0 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
            (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z'))
      have h0 : (c' z * u t z' + u t z * c' z') *
            (D.ENormB_pair k (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z')
              + D.ENormB_pair 0 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z')) = 0 := by
        rw [hut]
        simp
      rwa [h0] at h1
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun z (_ : z ∈ Finset.univ) =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun z' (_ : z' ∈ Finset.univ) => hterm z z'))
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (galE_Quad_eq_sum D k ε (u s)))
  -- assembly
  have hmain : HasDerivAt (fun s => Work.Diff.STE.Lead.galE D k ε (c t)
      + galE_Lin D k ε (Submission.Diff.STEGal.galState D ε (c t)) (u s)
      + galE_Quad D k ε (u s))
      (galE_Lin D k ε (Submission.Diff.STEGal.galState D ε (c t)) c') t :=
    ((hL.const_add (Work.Diff.STE.Lead.galE D k ε (c t))).add hQ).congr_deriv (by ring)
  refine (hmain.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => (hval s)))).congr_deriv ?_
  simp only [galE_Lin]

end Work.Diff.STE.Lead.Gal
