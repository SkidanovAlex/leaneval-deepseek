import Mathlib
import Submission.Work.Diff.C.geoCrux.BadGeoDefs
import Submission.Work.Diff.C.geoCrux.BadGeoProps
import Submission.Work.Diff.C.dip_model_through
import Submission.Work.Diff.C.geoCrux.restart_compare_ray
import Submission.Work.Diff.C.geoCrux.good_value_arith4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bad-index model comparison of the classical endgame (area C)

This file proves `Work.Diff.C.GeoCrux.BadIndexModelProp` (the lemma `bad_index_model`), one of the
two geometric inputs of the bad branch of `Work.Diff.C.gram_bad_case`.

Setting: `γ τ = GExp p (τ • u)` is a minimising ray from `p` in the unit direction `u` on `[0,s]`
(`rdist p (γ τ) = τ`, `s ≤ π`), `q = qpt hmet p e (Fin.succ k)` is the point at distance `π/2` from
`p` in the direction `e k`, `f = fFam hmet p e (Fin.succ k) = cos ∘ d(q,·)`, `F = f ∘ γ`,
`m τ = β sin τ` with `β = ⟪e k, u⟫` (so `F` and `m` have the same value *and* the same derivative at
`τ = 0`, by `InitData`), and `λ = √c + ε₁π`.

The conclusion is, for every `τ ∈ [0,s]`:
`|F τ - m τ| ≤ 60λ`, `F τ ≤ -1+2c → |cos τ| ≤ 60λ` and `τ ≥ π - arccos (1-2c) → |F τ| ≤ 60λ`.

The proof splits on the "dip" `D = {σ : F σ ≤ -1+c}` (where `hHess` — which is only available where
`f > -1+c` — cannot be used):

* **dip**: `F τ ≤ -1+c`; then `|F τ + 1| ≤ c` and
  `|m τ + 1| = 1 - |β| cos(τ - π/2) ≤ 3c + (1-cos(τ-π/2))`, and `DipGeoProp` locates dip times
  near `π/2`;
* **good region, no dip time before `τ`**: the ray stays in `{f > -1+c}` on `[0,τ]`, so
  `value_off_cap` gives `|F τ - m τ| ≤ ε₁τ ≤ ε₁π`, which is `O(c)`;
* **good region, some dip time before `τ`**: with `b` the last dip time `≤ τ`,
  `restart_compare_ray` restarts the Sturm comparison at `b` (`F b = -1+c` exactly), the two anchor
  discrepancies `A = F b - m b`, `B = F'(b) - m'(b)` are bounded by `2c + (1-cos γ')` and
  `√(2c-c²) + sin γ'` (`γ' = b - π/2`), and the amplitude `|A cos z + B sin z|`
  (`z = τ - b ≤ π/2 - γ'`) is estimated both by the triangle inequality (with `|sin z| ≤ cos γ'`)
  and by Cauchy–Schwarz, whichever is better.

The analytic inputs isolated in `geoCrux/BadGeoProps.lean` are used here: `RestartCompareProp`
(proved in `geoCrux/restart_compare_ray.lean`), `DipGeoProp`, `AnnulusPhaseProp` and
`GoodValueArithProp`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric
open Submission.GlobalExp

namespace Work.Diff.C.geoCrux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- The pairing `⟪∇f (γ b), γ'(b)⟫` of the gradient of `f` with the velocity of the ray
`γ σ = GExp p (σ • u)` at time `b` — the initial velocity of the model ODE when the Sturm
comparison is restarted at the (interior) time `b`.  Factored out as a `def` because the unfolded
expression is enormous and repeating it in the statements below blows up elaboration. -/
noncomputable def gradRay (hmet : IsMetricCompatible cov) (f : M → ℝ) (p : M)
    (u : TangentSpace I p) (b : ℝ) : ℝ :=
  Inner.inner ℝ (rgrad (I := I) (M := M) f
      (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)))
    (Submission.Geodesic.curveVelocity (I := I)
      (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) b)

/-- The `β sin σ < -1+3c` hypothesis forces `β ≤ -(1-3c)`. -/
theorem bad_beta_le {β σ c s : ℝ} (hσ0 : 0 ≤ σ) (hsπ : s ≤ Real.pi) (hcs : σ ≤ s)
    (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hbad : β * Real.sin σ < -1 + 3 * c) : β ≤ -(1 - 3 * c) := by
  have hσπ : σ ≤ Real.pi := le_trans hcs hsπ
  have hsin_ge : 0 ≤ Real.sin σ := Real.sin_nonneg_of_nonneg_of_le_pi hσ0 hσπ
  have hneg : -1 + 3 * c < 0 := by linarith
  by_contra hcon
  push_neg at hcon
  rcases lt_or_ge β 0 with hβ | hβ
  · have h1 : β * Real.sin σ ≥ β := by
      have := mul_le_mul_of_nonpos_left (Real.sin_le_one σ) (le_of_lt hβ)
      simpa using this
    have h2 : -1 + 3 * c < β := by linarith
    linarith [h1, h2, hbad]
  · have h1 : 0 ≤ β * Real.sin σ := mul_nonneg hβ hsin_ge
    linarith [h1, hneg, hbad]

set_option maxHeartbeats 1600000 in
/-- **Far-ball membership at a level `e ≤ c`.**  If `cos (rdist q (γ σ)) ≤ -1 + e` with `e ≤ c`, then
`rdist q (γ σ) ≥ π - arccos (1-c)`: on the branch `L ≤ π` the cosine is decreasing and
`cos (π - arccos (1-e)) = -1 + e`, while on the branch `L ≥ π` the claim is trivial.  (The point of
the hypothesis `e ≤ c` is that `arccos (1-e) ≥ arccos (1-c)`.) -/
theorem dip_far_mem_aux {p q : M} {u : TangentSpace I p} {σ s e c : ℝ}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hray : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ)
    (hqp : rdist (I := I) (M := M) q p = Real.pi / 2)
    (hσ : σ ∈ Set.Icc (0 : ℝ) s) (hsπ : s ≤ Real.pi) (hc1 : c ≤ 1) (hec : e ≤ c)
    (hcos : Real.cos (rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + e) :
    Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
  set L : ℝ := rdist (I := I) (M := M) q
    (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact ENNReal.toReal_nonneg
  have hL3 : L ≤ 3 * Real.pi / 2 := by
    have htri := Work.Diff.C.dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
    rw [hqp, hray σ hσ] at htri
    rw [hLdef]
    linarith [htri, hσ.2, hsπ]
  have hδc0 : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg _
  rcases lt_or_ge L Real.pi with hcase | hcase
  · by_contra hcon
    push_neg at hcon
    have he0 : 0 ≤ e := by
      have h1 : -1 ≤ Real.cos (rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) := Real.neg_one_le_cos _
      linarith
    have hcos_arccos : Real.cos (Real.arccos (1 - e)) = 1 - e :=
      Real.cos_arccos (by linarith [hec, hc1]) (by linarith)
    have hcose : Real.cos (Real.pi - Real.arccos (1 - e)) = -1 + e := by
      rw [Real.cos_pi_sub, hcos_arccos]; ring
    have hA : Real.pi - Real.arccos (1 - e) ≤ Real.pi := by
      linarith [Real.arccos_nonneg (1 - e)]
    have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi (x := L)
      (y := Real.pi - Real.arccos (1 - e)) hL0 hA (by
        have : Real.arccos (1 - e) ≤ Real.arccos (1 - c) :=
          Real.arccos_le_arccos (by linarith)
        linarith)
    rw [hcose] at hmono
    have hLcos : Real.cos L
        = Real.cos (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) := rfl
    linarith [hmono, hcos, hLcos]
  · linarith [hcase, hδc0]

-- ---------------------------------------------------------------------------------------------
-- Elementary trigonometric facts used repeatedly below
-- ---------------------------------------------------------------------------------------------

/-- `1 - cos t ≤ t²/2` (via `1 - cos t = 2 sin²(t/2)` and `|sin x| ≤ |x|`). -/
theorem geoCrux_one_sub_cos_le_sq_div_two (t : ℝ) : 1 - Real.cos t ≤ t ^ 2 / 2 := by
  have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h
    have h2 := Real.sin_sq_add_cos_sq (t / 2)
    nlinarith [h, h2]
  rw [hcos]
  have h2 : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
    have h := Real.abs_sin_le_abs (x := t / 2)
    have h3 : Real.sin (t / 2) ^ 2 = |Real.sin (t / 2)| ^ 2 := (sq_abs _).symm
    have h4 : (t / 2) ^ 2 = |t / 2| ^ 2 := (sq_abs _).symm
    rw [h3, h4]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

/-- `(2/π)|a - π/2| ≤ |cos a|` for `a ∈ [0,π]`. -/
theorem geoCrux_phase_le_abs_cos {a : ℝ} (h1 : 0 ≤ a) (h2 : a ≤ Real.pi) :
    (2 / Real.pi) * |a - Real.pi / 2| ≤ |Real.cos a| := by
  have hx : |a - Real.pi / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith
  have h0 : 0 ≤ |a - Real.pi / 2| := abs_nonneg _
  have h := Real.mul_le_sin h0 hx
  have hsin : Real.sin |a - Real.pi / 2| = |Real.cos a| := by
    rcases le_total (0 : ℝ) (a - Real.pi / 2) with hh | hh
    · rw [abs_of_nonneg hh, Real.sin_sub_pi_div_two,
        abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith))]
    · have hca : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      rw [abs_of_nonpos hh, Real.sin_neg, Real.sin_sub_pi_div_two, abs_of_nonneg hca]
      ring
  rwa [hsin] at h

/-- **The phase of the first dip time.** -/
theorem first_dip_phase_aux : Work.Diff.C.GeoCrux.FirstDipPhaseProp := by
  intro β a c ε₁ hc hc96 hε₁ hnum2 ha0 haπ hβle hβ1 hcmp
  have hπε : ε₁ * Real.pi < c / 4 := by linarith
  have hsin0 : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha0 haπ
  have hmem : 1 - Real.sin a ≤ c + ε₁ * a := by
    have h1 : β * Real.sin a ≤ -1 + c + ε₁ * a := by
      have h0 := (abs_le.mp hcmp).1
      linarith
    have h3 : -Real.sin a ≤ β * Real.sin a := by nlinarith [hβ1, hsin0]
    linarith
  have hmain : 1 - Real.sin a ≤ c + ε₁ * Real.pi := by nlinarith [hmem, hπε, haπ, hε₁]
  have hsq : Real.cos a ^ 2 ≤ 2 * (c + ε₁ * Real.pi) := by
    have h1 : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
    nlinarith [h1, hmain]
  have hcos : |Real.cos a| ≤ Real.sqrt (2 * (c + ε₁ * Real.pi)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  have hph := geoCrux_phase_le_abs_cos ha0 haπ
  have hhalf : 0 < 2 / Real.pi := by positivity
  have hstep : (2 / Real.pi) * |a - Real.pi / 2| ≤ Real.sqrt (2 * (c + ε₁ * Real.pi)) :=
    le_trans hph hcos
  have hfin : |a - Real.pi / 2| ≤ (Real.pi / 2) * Real.sqrt (2 * (c + ε₁ * Real.pi)) := by
    have h1 : (Real.pi / 2) * ((2 / Real.pi) * |a - Real.pi / 2|)
        ≤ (Real.pi / 2) * Real.sqrt (2 * (c + ε₁ * Real.pi)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    have h2 : (Real.pi / 2) * ((2 / Real.pi) * |a - Real.pi / 2|) = |a - Real.pi / 2| := by
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    linarith [h1, h2]
  have harg : 2 * (c + ε₁ * Real.pi) ≤ 2.5 * c := by linarith
  have h2 : Real.sqrt (2 * (c + ε₁ * Real.pi)) ≤ Real.sqrt (2.5 * c) := Real.sqrt_le_sqrt harg
  have h3 : Real.sqrt (2.5 * c) = Real.sqrt 2.5 * Real.sqrt c := Real.sqrt_mul (by norm_num) c
  have h4 : Real.sqrt 2.5 ≤ 1.5812 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have h5 : Real.sqrt c ≤ Real.sqrt c := le_refl _
  have hπ2 : Real.pi / 2 ≤ 1.5708 := by nlinarith [Real.pi_lt_d4]
  have hs25 : 0 ≤ Real.sqrt 2.5 := Real.sqrt_nonneg 2.5
  have hbound : (Real.pi / 2) * Real.sqrt 2.5 ≤ 2.6 := by
    have h1 : (Real.pi / 2) * Real.sqrt 2.5 ≤ 1.5708 * 1.5812 :=
      mul_le_mul hπ2 h4 hs25 (by norm_num)
    have h2 : (1.5708 : ℝ) * 1.5812 ≤ 2.6 := by norm_num
    linarith
  have hup : (Real.pi / 2) * Real.sqrt (2.5 * c) ≤ 2.6 * Real.sqrt c := by
    rw [h3]
    calc (Real.pi / 2) * (Real.sqrt 2.5 * Real.sqrt c)
        = ((Real.pi / 2) * Real.sqrt 2.5) * Real.sqrt c := by ring
      _ ≤ 2.6 * Real.sqrt c :=
          mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg c)
  calc |a - Real.pi / 2| ≤ (Real.pi / 2) * Real.sqrt (2 * (c + ε₁ * Real.pi)) := hfin
    _ ≤ (Real.pi / 2) * Real.sqrt (2.5 * c) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2.6 * Real.sqrt c := hup

/-- **Upper bound of the distance to `q` at a dip time** (needed for the eikonal bound on `F'`):
`rdist q (γ σ) ≤ π + arccos (1-c)`, so `|sin (rdist q (γ σ))| ≤ √(2c-c²)`. -/
theorem dip_upper_aux {p q : M} {u : TangentSpace I p} {σ s c : ℝ}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hqp : rdist (I := I) (M := M) q p = Real.pi / 2)
    (hray : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ)
    (hσ : σ ∈ Set.Icc (0 : ℝ) s) (hsπ : s ≤ Real.pi)
    (hdip : rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) ≥ Real.pi - Real.arccos (1 - c))
    (hcos : Real.cos (rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c) :
    rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      ≤ Real.pi + Real.arccos (1 - c) := by
  set L : ℝ := rdist (I := I) (M := M) q
    (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) with hL
  have hL0 : 0 ≤ L := by rw [hL]; exact ENNReal.toReal_nonneg
  have hL3 : L ≤ 3 * Real.pi / 2 := by
    have htri := Work.Diff.C.dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q p
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
    rw [hqp, hray σ hσ] at htri
    rw [hL]; linarith [htri, hσ.2, hsπ]
  have hδ0 : 0 ≤ Real.arccos (1 - c) := Real.arccos_nonneg _
  rcases lt_or_ge L Real.pi with hlt | hge
  · linarith
  · by_contra hcon
    push_neg at hcon
    have hca : Real.cos (Real.arccos (1 - c)) = 1 - c :=
      Real.cos_arccos (by linarith) (by linarith)
    have hcosδ : Real.cos (Real.pi - Real.arccos (1 - c)) = -1 + c := by
      rw [Real.cos_pi_sub, hca]; ring
    have hy0 : 0 ≤ 2 * Real.pi - L := by linarith
    have hxπ : Real.pi - Real.arccos (1 - c) ≤ Real.pi := by
      linarith [Real.arccos_nonneg (1 - c)]
    have hxy : 2 * Real.pi - L < Real.pi - Real.arccos (1 - c) := by linarith
    have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 2 * Real.pi - L)
      (y := Real.pi - Real.arccos (1 - c)) hy0 hxπ hxy
    rw [hcosδ, Real.cos_two_pi_sub] at hmono
    have hLcos : Real.cos L = Real.cos (rdist (I := I) (M := M) q
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) := rfl
    linarith [hmono, hcos, hLcos]

/-- **The phase of an arbitrary dip time** given the first dip time `a` and the far-ball bound. -/
theorem dip_phase_aux {p q : M} {u : TangentSpace I p} {s c ε₁ lam : ℝ}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hlamdef : lam = Real.sqrt c + ε₁ * Real.pi)
    (hqp : rdist (I := I) (M := M) q p = Real.pi / 2)
    (hu : Inner.inner ℝ u u = 1) (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi)
    (hray : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      rdist (I := I) (M := M) p (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) = τ)
    (hfar : ∀ z z' : M,
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q z →
      Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q z' →
      rdist (I := I) (M := M) z z' ≤ 50 * lam)
    {a : ℝ} (haIcc : a ∈ Set.Icc (0 : ℝ) s)
    (ha_cos : Real.cos (rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))) = -1 + c)
    (ha_phase : |a - Real.pi / 2| ≤ 2.6 * Real.sqrt c)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) s)
    (hσ_dip : Real.cos (rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c) :
    |σ - Real.pi / 2| ≤ min (50 * lam + 2.6 * Real.sqrt c) (Real.pi / 2)
      ∧ rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
          ≤ Real.pi + Real.arccos (1 - c)
      ∧ Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
  have hc1' : c ≤ 1 := by linarith
  have hσ_ge : Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
    dip_far_mem_aux (I := I) (M := M) (cov := cov) hmet htor hray hqp hσ hsπ hc1' (le_refl c)
      hσ_dip
  have ha_le : Real.cos (rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))) ≤ -1 + c := le_of_eq ha_cos
  have ha_ge : Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) :=
    dip_far_mem_aux (I := I) (M := M) (cov := cov) hmet htor hray hqp haIcc hsπ hc1' (le_refl c)
      ha_le
  have hup := dip_upper_aux (I := I) (M := M) (cov := cov) hmet htor hc hc1' hqp hray hσ hsπ hσ_ge
    hσ_dip
  have hsub := (Work.Diff.C.dipAux_ray_eq (I := I) (M := M) (cov := cov) hmet htor hu hs0
    (hray s ⟨hs0, le_rfl⟩)).2
  have hdist : rdist (I := I) (M := M)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) = |σ - a| := by
    rcases le_total σ a with h | h
    · rw [hsub σ hσ a haIcc h, abs_of_nonpos (by linarith)]
      ring
    · rw [Work.Diff.C.dipAux_comm (I := I) (M := M)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
        (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))]
      rw [hsub a haIcc σ hσ h, abs_of_nonneg (by linarith)]
  have hfar_app : rdist (I := I) (M := M)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
      (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) ≤ 50 * lam :=
    hfar _ _ hσ_ge ha_ge
  have hσa : |σ - a| ≤ 50 * lam := by rw [← hdist]; exact hfar_app
  have hphase : |σ - Real.pi / 2| ≤ 50 * lam + 2.6 * Real.sqrt c := by
    calc |σ - Real.pi / 2| = |(σ - a) + (a - Real.pi / 2)| := by ring_nf
      _ ≤ |σ - a| + |a - Real.pi / 2| := abs_add_le _ _
      _ ≤ 50 * lam + 2.6 * Real.sqrt c := by linarith
  have hphase2 : |σ - Real.pi / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2, hsπ]
  exact ⟨le_min hphase hphase2, hup, hσ_ge⟩

-- ---------------------------------------------------------------------------------------------
-- The arithmetic inputs (see `geoCruX/GoodValueArith4.lean`)
-- ---------------------------------------------------------------------------------------------

/-- **The annulus phase bound, `K = 5` form.**  `Fb = -1+c` is the value of the ray function at a
clamp point, `Fp` the derivative there (bounded by `√(2c-c²)` in absolute value by the eikonal
identity), `z = τ - b ≥ 0`, and the restart comparison gives
`|Fτ - (Fb cos z + Fp sin z)| ≤ ε₁ z`.  If in addition `-1+c < Fτ ≤ -1+2c` then `z ≤ 5√c`
(the true threshold is `≈ 3.42 √c`; the slack in the constant `5` keeps the trigonometric estimates
elementary and robust).

Proof: with `φ = arccos (1-c)` and `ρ = √(2c-c²) = sin φ`, the two bounds on
`Fb cos z + Fp sin z` force
`2 sin²((z-φ)/2) ≤ 2c + ε₁z ≤ 2c + c/4 ≤ 2.25c`,
while `φ ≤ 2.4√c` gives `(5√c-φ)/2 ≥ 1.3√c` and hence (with `sin x ≥ x - x³/6`)
`sin((5√c-φ)/2) ≥ 1.2728 √c`, so that — since `z ≥ 5√c` and `sin` is increasing on `[0,π/2]` —
`2 sin²((z-φ)/2) ≥ 2.42c`.  Contradiction. -/
theorem annulus_phase5 {c ε₁ Fb Fp Fτ z : ℝ} (hc : 0 < c) (hc96 : c ≤ 1 / 96)
    (hε₁ : 0 ≤ ε₁) (hnum : 4 * ε₁ * Real.pi < c) (hz0 : 0 ≤ z) (hzπ : z ≤ Real.pi)
    (hFb : Fb = -1 + c) (hFp : |Fp| ≤ Real.sqrt (2 * c - c * c))
    (hcmp : |Fτ - (Fb * Real.cos z + Fp * Real.sin z)| ≤ ε₁ * z)
    (hlo : -1 + c < Fτ) (hhi : Fτ ≤ -1 + 2 * c) : z ≤ 5 * Real.sqrt c := by
  by_contra hcon
  push_neg at hcon
  set φ : ℝ := Real.arccos (1 - c) with hφdef
  set ρ : ℝ := Real.sqrt (2 * c - c * c) with hρdef
  have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
  have hcosφ : Real.cos φ = 1 - c := by
    rw [hφdef]; exact Real.cos_arccos (by linarith) (by linarith)
  have hsinφ : Real.sin φ = ρ := by
    rw [hφdef, hρdef, Real.sin_arccos]; congr 1; ring
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg _
  have hφle : φ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by linarith)
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  -- (1) the constraint coming from the restart comparison and the clamp bound
  have hkey : 2 * Real.sin ((z - φ) / 2) ^ 2 ≤ 2 * c + ε₁ * z := by
    have hX : Fb * Real.cos z + Fp * Real.sin z ≤ -1 + 2 * c + ε₁ * z := by
      have h2 := (abs_le.mp hcmp).1
      linarith
    have hlow : -Real.cos (z - φ) ≤ Fb * Real.cos z + Fp * Real.sin z := by
      have h4 : -ρ ≤ Fp := (abs_le.mp hFp).1
      have h5 : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz0 hzπ
      have h6 : -ρ * Real.sin z ≤ Fp * Real.sin z := by nlinarith
      have h7 : Real.cos (z - φ) = (1 - c) * Real.cos z + ρ * Real.sin z := by
        rw [Real.cos_sub, hcosφ, hsinφ]; ring
      rw [hFb, h7]
      nlinarith [h6]
    have h8 : 1 - 2 * c - ε₁ * z ≤ Real.cos (z - φ) := by linarith
    have h10 : Real.cos (z - φ) = 1 - 2 * Real.sin ((z - φ) / 2) ^ 2 := by
      have h := Real.cos_two_mul ((z - φ) / 2)
      rw [show 2 * ((z - φ) / 2) = z - φ by ring] at h
      have h2 := Real.sin_sq_add_cos_sq ((z - φ) / 2)
      nlinarith [h, h2]
    linarith [h8, h10]
  -- (2) `sin (φ/2) = √(c/2)` and `φ ≤ 2.4 √c`
  have hsinhalf : Real.sin (φ / 2) = Real.sqrt (c / 2) := by
    have hcos2 : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
      have h := Real.cos_two_mul (φ / 2)
      rw [show 2 * (φ / 2) = φ by ring] at h
      have h2 := Real.sin_sq_add_cos_sq (φ / 2)
      nlinarith [h, h2]
    have h2 : Real.sin (φ / 2) ^ 2 = c / 2 := by linarith [hcos2, hcosφ]
    have h0 : 0 ≤ Real.sin (φ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hφle])
    rw [← h2, Real.sqrt_sq_eq_abs, abs_of_nonneg h0]
  have hφle2 : φ ≤ 2.4 * Real.sqrt c := by
    have h1 : (2 / Real.pi) * (φ / 2) ≤ Real.sqrt (c / 2) := by
      rw [← hsinhalf]
      exact Real.mul_le_sin (by linarith) (by linarith [hφle])
    have h2 : (2 / Real.pi) * (φ / 2) = φ / Real.pi := by field_simp
    have h3 : Real.sqrt (c / 2) ≤ 0.71 * Real.sqrt c := by
      have hpos : (0 : ℝ) ≤ 0.71 * Real.sqrt c := by positivity
      rw [← Real.sqrt_sq hpos]
      refine Real.sqrt_le_sqrt ?_
      have h4 : (0.71 * Real.sqrt c) ^ 2 = 0.5041 * c := by rw [mul_pow, hsc]; norm_num
      rw [h4]; linarith
    have h4 : φ / Real.pi ≤ 0.71 * Real.sqrt c := by linarith [h1, h2, h3]
    have h5 : φ ≤ 0.71 * Real.sqrt c * Real.pi := by
      have h6 := mul_le_mul_of_nonneg_right h4 (le_of_lt Real.pi_pos)
      rwa [div_mul_cancel₀ _ Real.pi_ne_zero] at h6
    nlinarith [h5, Real.pi_lt_d4, hsc0]
  -- (3) the sine lower bound
  have hsinlow : 1.1 * Real.sqrt c ≤ Real.sin ((5 * Real.sqrt c - φ) / 2) := by
    set u₀ : ℝ := (5 * Real.sqrt c - φ) / 2 with hu0def
    have hu0 : 0 ≤ u₀ := by rw [hu0def]; nlinarith [hφle2, hsc0]
    have hu2 : u₀ ≤ 2.5 * Real.sqrt c := by rw [hu0def]; nlinarith [hφ0]
    have hu1 : 1.3 * Real.sqrt c ≤ u₀ := by rw [hu0def]; nlinarith [hφle2]
    have h1 : u₀ - u₀ ^ 3 / 6 ≤ Real.sin u₀ := Real.sin_ge_sub_cube hu0
    have h2 : u₀ ^ 3 ≤ (2.5 * Real.sqrt c) ^ 3 := pow_le_pow_left₀ hu0 hu2 3
    have h3 : (2.5 * Real.sqrt c) ^ 3 = 15.625 * (Real.sqrt c * c) := by nlinarith [hsc]
    have h4 : Real.sqrt c * c ≤ (1 / 96) * Real.sqrt c := by nlinarith [hc96, hsc0]
    have h5 : u₀ ^ 3 ≤ 15.625 * ((1 / 96) * Real.sqrt c) := by linarith [h2, h3, h4]
    nlinarith [h1, hu1, h5, hsc0]
  -- (4) assemble the contradiction
  have hu0' : 0 ≤ (z - φ) / 2 := by nlinarith [hz0, hφle2, hcon, hsc0]
  have hule : (z - φ) / 2 ≤ Real.pi / 2 := by nlinarith [hzπ, hφ0]
  have hx0le : (5 * Real.sqrt c - φ) / 2 ≤ (z - φ) / 2 := by nlinarith [hcon]
  have hmono : Real.sin ((5 * Real.sqrt c - φ) / 2) ≤ Real.sin ((z - φ) / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [hφle2, hsc0]) hule hx0le
  have hsin0 : 0 ≤ Real.sin ((5 * Real.sqrt c - φ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hφle2, hsc0])
      (by nlinarith [hφle2, hsc0, Real.pi_pos])
  have hsq : Real.sin ((5 * Real.sqrt c - φ) / 2) ^ 2 ≤ Real.sin ((z - φ) / 2) ^ 2 :=
    pow_le_pow_left₀ hsin0 hmono 2
  have hA : 2 * (1.1 * Real.sqrt c) ^ 2 ≤ 2 * Real.sin ((z - φ) / 2) ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith [hsc0] : (0 : ℝ) ≤ 1.1 * Real.sqrt c) hsinlow 2
    nlinarith [h, hsq]
  have hB : ε₁ * z ≤ c / 4 := by
    have h1 : ε₁ * z ≤ ε₁ * Real.pi := mul_le_mul_of_nonneg_left hzπ hε₁
    linarith
  have hfin : 2 * (1.1 * Real.sqrt c) ^ 2 ≤ 2 * c + c / 4 := by linarith [hA, hkey, hB]
  have hnum' : 2 * (1.1 * Real.sqrt c) ^ 2 = 2.42 * c := by nlinarith [hsc]
  linarith [hfin, hnum', hc]


set_option maxHeartbeats 20000000 in
theorem bad_index_model : Work.Diff.C.GeoCrux.BadIndexModelProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBL iNE iCS iPC cov iCD
    hmet htor α c ε₁ hα hα1 hc hc1 hε₁ hnum1 hnum2 p e hON hsmC hHess hcont hgrad hinit
    hdiam hfar u hu s hs0 hsπ hray k hbad
  classical
  -- ===================== setup =====================
  set q : M := qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) with hqdef
  set f : M → ℝ := fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) with hfdef
  set F : ℝ → ℝ := fun τ : ℝ => f (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) with hFdef
  set β : ℝ := Inner.inner ℝ (e k) u with hβdef
  set m : ℝ → ℝ := fun τ : ℝ => β * Real.sin τ with hmdef
  set lam : ℝ := Real.sqrt c + ε₁ * Real.pi with hlamdef
  have hfq : f = fcos (I := I) (M := M) q := by rw [hfdef, hqdef]; rfl
  have hFcos : ∀ σ : ℝ, F σ = Real.cos (rdist (I := I) (M := M) q
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) := by
    intro σ; rw [hFdef, hfq]; rfl
  have hmval : ∀ σ : ℝ, m σ = β * Real.sin σ := by intro σ; rw [hmdef]
  have hFfam : ∀ σ : ℝ, F σ = fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
      (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
    intro σ; rw [hFdef, hfdef]
  have hu_ne : u ≠ 0 := by intro h0; rw [h0] at hu; simp at hu
  have hu_norm : ‖u‖ = 1 := by
    have h : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq u]; exact hu
    nlinarith [norm_nonneg u]
  have hFp0 : f p = 0 := by rw [hfq]; exact (hinit.2.2 k).1
  have hGExp_zero : Submission.GlobalExp.GExp (cov := cov) hmet p (0 : TangentSpace I p) = p :=
    Submission.GlobalExp.GExp_zero hmet p
  have hF0 : F 0 = 0 := by
    rw [hFdef]
    show f (Submission.GlobalExp.GExp (cov := cov) hmet p ((0 : ℝ) • u)) = 0
    rw [zero_smul, hGExp_zero]
    exact hFp0
  have hqp : rdist (I := I) (M := M) q p = Real.pi / 2 := by
    rw [hqdef]
    exact Work.Diff.C.dipAux_qpt_p (I := I) (M := M) (cov := cov) hmet htor hinit hdiam
  have hcov_smul : Continuous (fun τ : ℝ =>
      Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) :=
    (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hu_ne).continuous
  have hF_cont : Continuous F := by
    rw [hFdef, hfq]
    exact (hcont q).comp hcov_smul
  have hβ_le : β ≤ -(1 - 3 * c) := by
    obtain ⟨σ, hσ, hlt⟩ := hbad
    exact bad_beta_le hσ.1 hsπ hσ.2 hc hc1 hlt
  have hβ_abs : |β| ≤ 1 := by
    have hnk : ‖e k‖ = 1 := by
      have h1 : Inner.inner ℝ (e k) (e k) = 1 := by simpa using hON k k
      have h : ‖e k‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h1
      nlinarith [norm_nonneg (e k)]
    have h := abs_real_inner_le_norm (e k) u
    rw [hnk, hu_norm, one_mul] at h
    exact h
  have hβ1 : -1 ≤ β := (abs_le.mp hβ_abs).1
  have hsincos : ∀ σ : ℝ, Real.sin σ = Real.cos (σ - Real.pi / 2) := by
    intro σ
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have hm_le_sin : ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s → |m τ| ≤ Real.sin τ := by
    intro τ hτ
    have h2 : 0 ≤ Real.sin τ := Real.sin_nonneg_of_nonneg_of_le_pi hτ.1 (le_trans hτ.2 hsπ)
    have h3 : 0 ≤ Real.sin τ := h2
    calc |m τ| = |β| * |Real.sin τ| := by rw [hmval, abs_mul]
      _ = |β| * Real.sin τ := by rw [abs_of_nonneg h2]
      _ ≤ 1 * Real.sin τ := mul_le_mul_of_nonneg_right hβ_abs h3
      _ = Real.sin τ := one_mul _
  have hsin_far : ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s → Real.pi - Real.arccos (1 - 2 * c) ≤ τ →
      Real.sin τ ≤ 2 * Real.sqrt c := by
    intro τ hτ hfarτ
    have h1 : Real.sin τ = Real.sin (Real.pi - τ) := (Real.sin_pi_sub τ).symm
    have h2 : Real.pi - τ ≤ Real.arccos (1 - 2 * c) := by linarith
    have h3 : -(Real.pi / 2) ≤ Real.pi - τ := by linarith [hτ.2, hsπ]
    have h4 : Real.sin (Real.pi - τ) ≤ Real.sin (Real.arccos (1 - 2 * c)) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two h3
        (Real.arccos_le_pi_div_two.mpr (by linarith [hc])) h2
    have h5 : Real.sin (Real.arccos (1 - 2 * c)) = Real.sqrt (1 - (1 - 2 * c) ^ 2) := by
      rw [Real.sin_arccos]
    have h6 : Real.sqrt (1 - (1 - 2 * c) ^ 2) ≤ Real.sqrt (4 * c) :=
      Real.sqrt_le_sqrt (by nlinarith [hc])
    have h7 : Real.sqrt (4 * c) = 2 * Real.sqrt c := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show Real.sqrt 4 = (2 : ℝ) by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    calc Real.sin τ = Real.sin (Real.pi - τ) := h1
      _ ≤ Real.sin (Real.arccos (1 - 2 * c)) := h4
      _ = Real.sqrt (1 - (1 - 2 * c) ^ 2) := h5
      _ ≤ Real.sqrt (4 * c) := h6
      _ = 2 * Real.sqrt c := h7
  by_cases hsmall : 60 * lam < 2
  · -- ===================== the main (non-trivial) case =====================
    have hlam_pos : 0 < lam := by rw [hlamdef]; positivity
    have hlam_lt : lam < 1 / 30 := by linarith
    have hsc_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hslc : Real.sqrt c ≤ lam := by rw [hlamdef]; nlinarith [hε₁, Real.pi_pos]
    have hsc_lt : Real.sqrt c < 1 / 30 := lt_of_le_of_lt hslc hlam_lt
    have hc96 : c ≤ 1 / 96 := by
      have h1 : 1 - Real.cos α ≤ α ^ 2 / 2 := by
        have h := Real.one_sub_sq_div_two_le_cos (x := α); linarith
      have h2 : α ^ 2 ≤ 1 / 16 := by nlinarith [hα1, hα]
      nlinarith [hnum1, h1, h2]
    have hπε : ε₁ * Real.pi < c / 4 := by linarith
    have hπε'' : ε₁ * Real.pi ≤ Real.sqrt c := by
      have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
      nlinarith [le_of_lt hπε, hsq, hsc_pos, hsc_lt]
    have hsc2lam : (2.6 : ℝ) * Real.sqrt c ≤ 2.6 * lam :=
      mul_le_mul_of_nonneg_left hslc (by norm_num)
    have h2sc : 2 * Real.sqrt c ≤ 2 * lam := mul_le_mul_of_nonneg_left hslc (by norm_num)
    have hc_lam : c ≤ lam ^ 2 := by
      have h1 : Real.sqrt c ^ 2 ≤ lam ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg c) hslc 2
      rwa [Real.sq_sqrt (le_of_lt hc)] at h1
    -- unit speed of the ray at positive time
    have hcv_norm : ∀ θ : ℝ, θ ≠ 0 → ‖Submission.Geodesic.curveVelocity (I := I)
        (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) θ‖ = 1 := by
      intro θ hθ
      have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hu_ne hθ
      rwa [hu_norm] at h
    -- ------------------------------------------------------------------
    by_cases hdipne : ∃ σ ∈ Set.Icc (0 : ℝ) s, F σ ≤ -1 + c
    · -- ============ the dip is non-empty ============
      obtain ⟨a, haIcc, haF, ha_goodPrev, ha_cmp⟩ :=
        Work.Diff.C.dip_first_compare (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hsmC
          hHess hcont hinit hu hs0 (k := k) hdipne
      have ha_cos : Real.cos (rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u))) = -1 + c := by
        rw [← hFcos a, hFdef, hfq]
        exact haF
      have ha_phase : |a - Real.pi / 2| ≤ 2.6 * Real.sqrt c := by
        have hcmp' : |(-1 + c) - β * Real.sin a| ≤ ε₁ * a := by
          have h := ha_cmp
          have h1 : fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (a • u)) = -1 + c := haF
          rw [h1] at h
          simpa [hβdef] using h
        exact Work.Diff.C.geoCrux.first_dip_phase_aux hc hc96 hε₁ hnum2 haIcc.1
          (le_trans haIcc.2 hsπ) hβ_le hβ1 hcmp'
      -- the phase locator for dip times
      have hloc_phase_sharp : ∀ σ ∈ Set.Icc (0 : ℝ) s, F σ ≤ -1 + c →
          |σ - Real.pi / 2| ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi) + 2.6 * Real.sqrt c)
            (Real.pi / 2) := by
        intro σ hσ hσdip
        have hσ' : Real.cos (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c := by
          rw [← hFcos σ]; exact hσdip
        have h := (dip_phase_aux (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁
          hlamdef hqp hu hs0 hsπ hray (fun z z' hz hz' => hfar k z z' hz hz') haIcc ha_cos ha_phase
          hσ hσ').1
        rw [hlamdef] at h
        exact h
      have hloc_phase : ∀ σ ∈ Set.Icc (0 : ℝ) s, F σ ≤ -1 + c →
          |σ - Real.pi / 2| ≤ 52.6 * lam := by
        intro σ hσ hσdip
        have h := hloc_phase_sharp σ hσ hσdip
        have hle : min (50 * (Real.sqrt c + ε₁ * Real.pi) + 2.6 * Real.sqrt c) (Real.pi / 2)
            ≤ 52.6 * lam := by
          refine le_trans (min_le_left _ _) ?_
          rw [hlamdef]; linarith [hsc2lam]
        linarith [h, hle]
      -- the far-ball locator
      have hloc_mem : ∀ σ ∈ Set.Icc (0 : ℝ) s, F σ ≤ -1 + c →
          Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
          ∧ rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
              ≤ Real.pi + Real.arccos (1 - c) := by
        intro σ hσ hσdip
        have hσ' : Real.cos (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ≤ -1 + c := by
          rw [← hFcos σ]; exact hσdip
        have h := dip_phase_aux (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hlamdef hqp
          hu hs0 hsπ hray (fun z z' hz hz' => hfar k z z' hz hz') haIcc ha_cos ha_phase hσ hσ'
        exact ⟨h.2.2, h.2.1⟩
      -- the last dip time below τ
      have hlast : ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s → -1 + c < F τ →
          (∃ σ ∈ Set.Icc (0 : ℝ) s, σ ≤ τ ∧ F σ ≤ -1 + c) →
          ∃ b : ℝ, b ∈ Set.Icc (0 : ℝ) s ∧ b < τ ∧ F b = -1 + c
            ∧ (∀ σ ∈ Set.Ioc b τ, -1 + c < F σ) := by
        intro τ hτ hgoodτ hbefore
        obtain ⟨σ₀, hσ₀, hσ₀τ, hσ₀d⟩ := hbefore
        have hKne : (Set.Icc (0 : ℝ) τ ∩ {σ : ℝ | F σ ≤ -1 + c}).Nonempty :=
          ⟨σ₀, by rw [Set.mem_inter_iff]; exact ⟨⟨hσ₀.1, hσ₀τ⟩, hσ₀d⟩⟩
        have hKcl : IsClosed (Set.Icc (0 : ℝ) τ ∩ {σ : ℝ | F σ ≤ -1 + c}) :=
          isClosed_Icc.inter (isClosed_Iic.preimage hF_cont)
        obtain ⟨b, hb, hbmax⟩ := (isCompact_Icc.of_isClosed_subset hKcl
          (Set.inter_subset_left)).exists_isGreatest hKne
        rw [Set.mem_inter_iff] at hb
        have hbτ : b ≤ τ := hb.1.2
        have hbdip : F b ≤ -1 + c := hb.2
        have hbIcc : b ∈ Set.Icc (0 : ℝ) s := ⟨hb.1.1, le_trans hbτ hτ.2⟩
        have hb_lt : b < τ := by
          rcases lt_or_eq_of_le hbτ with h | h
          · exact h
          · exfalso
            rw [h] at hbdip
            linarith [hbdip, hgoodτ]
        have hb_eq : F b = -1 + c := by
          refine le_antisymm hbdip ?_
          by_contra hcon
          push_neg at hcon
          have hev : ∀ᶠ σ in nhds b, F σ < -1 + c :=
            hF_cont.continuousAt.eventually_lt_const hcon
          obtain ⟨η, hη, hηlt⟩ := Metric.eventually_nhds_iff.mp hev
          have hτb : 0 < τ - b := by linarith
          have hminpos : 0 < min (η / 2) (τ - b) := lt_min (by linarith) hτb
          have hmem : b + min (η / 2) (τ - b) ∈ Set.Icc (0 : ℝ) τ ∩ {σ : ℝ | F σ ≤ -1 + c} := by
            rw [Set.mem_inter_iff]
            refine ⟨⟨by linarith [hb.1.1], by linarith [min_le_right (η / 2) (τ - b)]⟩, ?_⟩
            have hd : dist (b + min (η / 2) (τ - b)) b < η := by
              rw [Real.dist_eq, abs_of_pos (by linarith [hminpos])]
              linarith [min_le_left (η / 2) (τ - b)]
            exact le_of_lt (hηlt hd)
          have hle := hbmax hmem
          linarith [hminpos, hminpos]
        have hbgood : ∀ σ ∈ Set.Ioc b τ, -1 + c < F σ := by
          intro σ hσ
          by_contra hcon
          push_neg at hcon
          have hmem : σ ∈ Set.Icc (0 : ℝ) τ ∩ {σ : ℝ | F σ ≤ -1 + c} := by
            rw [Set.mem_inter_iff]
            exact ⟨⟨le_trans hb.1.1 (le_of_lt hσ.1), hσ.2⟩, hcon⟩
          have hle := hbmax hmem
          linarith [hσ.1]
        exact ⟨b, hbIcc, hb_lt, hb_eq, hbgood⟩
      -- the restart comparison at an interior dip exit
      have hrestart : ∀ b τ : ℝ, b ∈ Set.Icc (0 : ℝ) s → τ ∈ Set.Icc (0 : ℝ) s → b < τ →
          F b = -1 + c → (∀ σ ∈ Set.Ioc b τ, -1 + c < F σ) →
          |F τ - (F b * Real.cos (τ - b) + gradRay hmet f p u b * Real.sin (τ - b))|
            ≤ ε₁ * (τ - b) := by
        intro b τ hbIcc hτ hb_lt hb_eq hb_good
        have hb_le : b ≤ τ := le_of_lt hb_lt
        have hsm_on : ∀ θ ∈ Set.Icc b τ, CMDiffAt ∞ f
            (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)) := by
          intro θ hθ
          have hgt : -1 + c ≤ F θ := by
            rcases eq_or_lt_of_le hθ.1 with h | h
            · rw [← h]; exact le_of_eq hb_eq.symm
            · exact le_of_lt (hb_good θ ⟨h, hθ.2⟩)
          have hgt' : -1 + c ≤ fcos (I := I) (M := M) q
              (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)) := by
            show -1 + c ≤ F θ
            exact hgt
          rw [hfq]
          exact hsmC q _ hgt'
        have hHess_on : ∀ θ ∈ Set.Ioc b τ, ∀ V : TangentSpace I
            (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)),
            |rhess cov (fcos (I := I) (M := M) q)
                (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)) V V
              + (fcos (I := I) (M := M) q) (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u))
                * Inner.inner ℝ V V| ≤ ε₁ * Inner.inner ℝ V V := by
          intro θ hθ V
          have hgt : -1 + c < F θ := hb_good θ hθ
          have hgt' : -1 + c < (fcos (I := I) (M := M) q)
              (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)) := by
            show -1 + c < F θ
            exact hgt
          have h := hHess q (Submission.GlobalExp.GExp (cov := cov) hmet p (θ • u)) V V hgt'
          rw [real_inner_self_eq_norm_sq] at h ⊢
          simpa [pow_two, mul_assoc] using h
        have hcmp := Work.Diff.C.geoCrux.restart_compare_ray (I := I) (M := M) (cov := cov)
          hmet htor hu hε₁ hbIcc.1 hb_le hsm_on hHess_on
        simpa only [gradRay] using hcmp.1
      -- the derivative bound at a dip exit
      have hFpb_le : ∀ b : ℝ, b ∈ Set.Icc (0 : ℝ) s → F b = -1 + c →
          |gradRay hmet f p u b| ≤ Real.sqrt (2 * c - c * c) := by
        intro b hbIcc hb_eq
        have hb_ne : b ≠ 0 := by
          intro h0
          have h1 : F b = 0 := by rw [h0]; exact hF0
          rw [h1] at hb_eq; linarith [hc]
        have hcv := hcv_norm b hb_ne
        have hmvf : gradRay hmet f p u b
            = mvfderiv I f (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u))
                (Submission.Geodesic.curveVelocity (I := I)
                  (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) b) := by
          simp only [gradRay]
          exact Work.Diff.C.inner_rgrad_mvfderiv' (I := I) (M := M) f
            (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)) _
        rw [hmvf]
        have h := Work.Diff.C.dm_abs_mvfderiv_fcos_le (I := I) (M := M) (cov := cov) hmet htor
          (q := q) (x := Submission.GlobalExp.GExp (cov := cov) hmet p (b • u))
          (Submission.Geodesic.curveVelocity (I := I)
            (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) b)
        rw [hcv, mul_one] at h
        rw [← hfq] at h
        have hcosb : Real.cos (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u))) = -1 + c := by
          rw [← hFcos b]; exact hb_eq
        have hsq : Real.sin (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u))) ^ 2 ≤ 1 - (1 - c) ^ 2 := by
          have h1 : Real.cos (rdist (I := I) (M := M) q
              (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u))) ^ 2
              + Real.sin (rdist (I := I) (M := M) q
                (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u))) ^ 2 = 1 :=
            Real.cos_sq_add_sin_sq _
          rw [hcosb] at h1; linarith [h1]
        have hle : |Real.sin (rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)))|
            ≤ Real.sqrt (1 - (1 - c) ^ 2) := by
          rw [← Real.sqrt_sq_eq_abs]
          exact Real.sqrt_le_sqrt hsq
        have harg : 1 - (1 - c) ^ 2 = 2 * c - c * c := by ring
        rw [harg] at hle
        linarith [h, hle]
      -- the anchor value bound at a dip exit
      have hanchor : ∀ b : ℝ, b ∈ Set.Icc (0 : ℝ) s → F b = -1 + c →
          |F b - m b| ≤ 4 * c + (1 - Real.cos (b - Real.pi / 2)) := by
        intro b hbIcc hb_eq
        have hsb : 0 ≤ Real.sin b :=
          Real.sin_nonneg_of_nonneg_of_le_pi hbIcc.1 (le_trans hbIcc.2 hsπ)
        have h1 : |F b + 1| ≤ c := by
          rw [hb_eq, abs_le]; constructor <;> linarith [hc]
        have h3 : |m b + 1| ≤ 3 * c + (1 - Real.cos (b - Real.pi / 2)) := by
          have h4 : (0 : ℝ) ≤ β * Real.sin b + 1 := by
            have h5 : -Real.sin b ≤ β * Real.sin b := by nlinarith [hβ1, hsb]
            linarith [h5, Real.sin_le_one b]
          have h6 : β * Real.sin b + 1 ≤ (1 - Real.sin b) + 3 * c := by
            have h7 : (-β) * Real.sin b ≥ (1 - 3 * c) * Real.sin b := by
              nlinarith [hβ_le, hsb]
            have h8 : 3 * c * Real.sin b ≤ 3 * c := by
              nlinarith [hsb, Real.sin_le_one b, hc]
            have h9 : β * Real.sin b + 1 = 1 - (-β) * Real.sin b := by ring
            have h10 : 1 - (-β) * Real.sin b ≤ 1 - (1 - 3 * c) * Real.sin b := by linarith
            have h11 : 1 - (1 - 3 * c) * Real.sin b
                = (1 - Real.sin b) + 3 * c * Real.sin b := by ring
            linarith [h9, h10, h11, h8]
          have h12 : (1 - Real.sin b) + 3 * c ≤ 3 * c + (1 - Real.cos (b - Real.pi / 2)) := by
            rw [hsincos b]; linarith
          have h13 : 0 ≤ 3 * c + (1 - Real.cos (b - Real.pi / 2)) := by
            have h14 := Real.cos_le_one (b - Real.pi / 2); linarith [hc]
          rw [hmval, abs_le]
          exact ⟨by linarith [h4, h13], by linarith [h6, h12]⟩
        have h2 : |F b - m b| ≤ |F b + 1| + |m b + 1| := by
          have h : F b - m b = (F b + 1) - (m b + 1) := by ring
          rw [h]; exact abs_sub _ _
        linarith [h2, h1, h3]
      -- ==================================================================
      -- (A) τ in the dip
      have hdipcase : ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s → F τ ≤ -1 + c →
          |F τ - m τ| ≤ 60 * lam ∧ |Real.cos τ| ≤ 60 * lam
            ∧ (Real.pi - Real.arccos (1 - 2 * c) ≤ τ → |F τ| ≤ 60 * lam) := by
        intro τ hτ hdipτ
        have hγ : |τ - Real.pi / 2| ≤ 52.6 * lam := hloc_phase τ hτ hdipτ
        have hs0τ : 0 ≤ Real.sin τ := Real.sin_nonneg_of_nonneg_of_le_pi hτ.1 (le_trans hτ.2 hsπ)
        have h1mc : 1 - Real.cos (τ - Real.pi / 2) ≤ (52.6 * lam) ^ 2 / 2 := by
          have h1 := geoCrux_one_sub_cos_le_sq_div_two (τ - Real.pi / 2)
          have h2 : (τ - Real.pi / 2) ^ 2 ≤ (52.6 * lam) ^ 2 := by
            have h3 := abs_le.mp hγ
            nlinarith [h3.1, h3.2]
          linarith
        have hF1 : |F τ + 1| ≤ c := by
          have h1 : -1 ≤ F τ := by rw [hFcos τ]; exact Real.neg_one_le_cos _
          rw [abs_le]; constructor <;> linarith [hc]
        have hm1 : |m τ + 1| ≤ 3 * c + (1 - Real.cos (τ - Real.pi / 2)) := by
          have h13 : 0 ≤ 3 * c + (1 - Real.cos (τ - Real.pi / 2)) := by
            have h14 := Real.cos_le_one (τ - Real.pi / 2); linarith [hc]
          have h4 : -(3 * c + (1 - Real.cos (τ - Real.pi / 2))) ≤ β * Real.sin τ + 1 := by
            have h5 : -Real.sin τ ≤ β * Real.sin τ := by nlinarith [hβ1, hs0τ]
            linarith [h5, hs0τ, Real.sin_le_one τ, h13]
          have h6 : β * Real.sin τ + 1 ≤ (1 - Real.sin τ) + 3 * c := by
            have h7 : (-β) * Real.sin τ ≥ (1 - 3 * c) * Real.sin τ := by
              nlinarith [hβ_le, hs0τ]
            have h8 : 3 * c * Real.sin τ ≤ 3 * c := by
              nlinarith [hs0τ, Real.sin_le_one τ, hc]
            have h9 : β * Real.sin τ + 1 = 1 - (-β) * Real.sin τ := by ring
            have h10 : 1 - (-β) * Real.sin τ ≤ 1 - (1 - 3 * c) * Real.sin τ := by linarith
            have h11 : 1 - (1 - 3 * c) * Real.sin τ
                = (1 - Real.sin τ) + 3 * c * Real.sin τ := by ring
            linarith [h9, h10, h11, h8]
          rw [hmval, abs_le]
          refine ⟨by linarith [h4], ?_⟩
          have h12 : (1 - Real.sin τ) + 3 * c ≤ 3 * c + (1 - Real.cos (τ - Real.pi / 2)) := by
            rw [hsincos τ]; linarith
          linarith [h6, h12]
        have hI : |F τ - m τ| ≤ 60 * lam := by
          have h1 : |F τ - m τ| ≤ |F τ + 1| + |m τ + 1| := by
            have h : F τ - m τ = (F τ + 1) - (m τ + 1) := by ring
            rw [h]; exact abs_sub _ _
          have h2 : 4 * c + (52.6 * lam) ^ 2 / 2 ≤ 60 * lam := by
            nlinarith [hc_lam, hlam_lt, hlam_pos]
          linarith [h1, hF1, hm1, h1mc, h2]
        have hII : |Real.cos τ| ≤ 60 * lam := by
          have h1 : |Real.cos τ| = |Real.sin (τ - Real.pi / 2)| := by
            rw [Real.sin_sub_pi_div_two, abs_neg]
          have h2 : |Real.sin (τ - Real.pi / 2)| ≤ |τ - Real.pi / 2| := Real.abs_sin_le_abs
          linarith [h1, h2, hγ]
        have hIII : Real.pi - Real.arccos (1 - 2 * c) ≤ τ → |F τ| ≤ 60 * lam := by
          intro hfarτ
          have hsinτ : Real.sin τ ≤ 2 * Real.sqrt c := hsin_far τ hτ hfarτ
          have hγπ : |τ - Real.pi / 2| ≤ Real.pi / 2 := by
            rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2, hsπ]
          have hcase : Real.pi / 2 - Real.arccos (1 - 2 * c) ≤ |τ - Real.pi / 2| := by
            have h3 : Real.pi / 2 - Real.arccos (1 - 2 * c) ≤ τ - Real.pi / 2 := by linarith
            rcases abs_cases (τ - Real.pi / 2) with ⟨h, _⟩ | ⟨h, _⟩
            · linarith [h, h3]
            · rw [h]; linarith [h3]
          -- `arccos (1-2c) = 2 arcsin (√c) ≤ π √c`
          have hδ2 : Real.arccos (1 - 2 * c) ≤ Real.pi * lam := by
            have hca : Real.cos (Real.arccos (1 - 2 * c)) = 1 - 2 * c :=
              Real.cos_arccos (by linarith) (by linarith)
            have hθ0 : 0 ≤ Real.arccos (1 - 2 * c) := Real.arccos_nonneg _
            have hθπ : Real.arccos (1 - 2 * c) ≤ Real.pi := Real.arccos_le_pi _
            have hsin2 : Real.sin (Real.arccos (1 - 2 * c) / 2) ^ 2 = c := by
              have h1 := Real.cos_two_mul (Real.arccos (1 - 2 * c) / 2)
              rw [show 2 * (Real.arccos (1 - 2 * c) / 2) = Real.arccos (1 - 2 * c) by ring,
                hca] at h1
              have h2 := Real.sin_sq_add_cos_sq (Real.arccos (1 - 2 * c) / 2)
              nlinarith [h1, h2]
            have h0 : 0 ≤ Real.sin (Real.arccos (1 - 2 * c) / 2) :=
              Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
            have hsin : Real.sin (Real.arccos (1 - 2 * c) / 2) = Real.sqrt c := by
              conv_rhs => rw [← hsin2]
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h0]
            have hml := Real.mul_le_sin (x := Real.arccos (1 - 2 * c) / 2)
              (by linarith) (by linarith)
            rw [hsin] at hml
            have h1 : Real.arccos (1 - 2 * c) / 2 ≤ (Real.pi / 2) * Real.sqrt c := by
              have h2 : (Real.pi / 2) * ((2 / Real.pi) * (Real.arccos (1 - 2 * c) / 2))
                  ≤ (Real.pi / 2) * Real.sqrt c :=
                mul_le_mul_of_nonneg_left hml (by positivity)
              have h3 : (Real.pi / 2) * ((2 / Real.pi) * (Real.arccos (1 - 2 * c) / 2))
                  = Real.arccos (1 - 2 * c) / 2 := by
                field_simp
              linarith [h2, h3]
            have h4 : Real.arccos (1 - 2 * c) ≤ Real.pi * Real.sqrt c := by nlinarith [h1]
            exact le_trans h4 (mul_le_mul_of_nonneg_left hslc (le_of_lt Real.pi_pos))
          have hlam_low : 1.6 ≤ 60 * lam := by
            have h5 : Real.pi / 2 ≤ (52.6 + Real.pi) * lam := by
              linarith [hcase, hγ, hδ2]
            nlinarith [h5, Real.pi_gt_three, Real.pi_lt_d4]
          have hπ2 : (τ - Real.pi / 2) ^ 2 / 2 ≤ Real.pi ^ 2 / 8 := by
            have h := abs_le.mp hγπ
            nlinarith [h.1, h.2]
          have hbig : 4 * c + (τ - Real.pi / 2) ^ 2 / 2 + 2 * Real.sqrt c ≤ 60 * lam := by
            have h6 : 4 * c ≤ 4 * (1 / 96 : ℝ) := by linarith [hc96]
            have h7 : 2 * Real.sqrt c ≤ 2 * Real.sqrt (1 / 96 : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc96) (by norm_num)
            have h8 : Real.pi ^ 2 / 8 ≤ (3.1416 : ℝ) ^ 2 / 8 := by
              nlinarith [Real.pi_lt_d4, Real.pi_pos]
            nlinarith [h6, h7, h8, hlam_low, hπ2]
          have h3 : |F τ| ≤ |F τ + 1| + |m τ| + 3 * c + (1 - Real.cos (τ - Real.pi / 2)) := by
            have h6 : |F τ - m τ| ≤ |F τ + 1| + |m τ + 1| := by
              have h : F τ - m τ = (F τ + 1) - (m τ + 1) := by ring
              rw [h]; exact abs_sub _ _
            have h8 : |F τ| ≤ |F τ - m τ| + |m τ| := by
              have h2 := abs_add_le (F τ - m τ) (m τ)
              rwa [sub_add_cancel] at h2
            linarith [h6, hm1, h8]
          have hmτ_abs : |m τ| ≤ Real.sin τ := hm_le_sin τ hτ
          have h1mc' : 1 - Real.cos (τ - Real.pi / 2) ≤ (τ - Real.pi / 2) ^ 2 / 2 :=
            geoCrux_one_sub_cos_le_sq_div_two (τ - Real.pi / 2)
          linarith [h3, hF1, hmτ_abs, hsinτ, h1mc', hbig]
        exact ⟨hI, hII, hIII⟩
      -- ==================================================================
      -- (B) τ in the good region with a dip time before it (b ≥ π/2)
      have hgoodcase : ∀ b τ : ℝ, b ∈ Set.Icc (0 : ℝ) s → τ ∈ Set.Icc (0 : ℝ) s → b < τ →
          F b = -1 + c → (∀ σ ∈ Set.Ioc b τ, -1 + c < F σ) →
          Real.pi / 2 ≤ b →
          |b - Real.pi / 2| ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi) + 2.6 * Real.sqrt c)
            (Real.pi / 2) →
          |F τ - m τ| + 2 * Real.sqrt c ≤ 60 * lam := by
        intro b τ hbIcc hτ hb_lt hb_eq hb_good hγ0 hb_phase
        set P : ℝ := gradRay hmet f p u b with hP
        set Cc : ℝ := P - β * Real.cos b with hCc
        have hb_le : b ≤ τ := le_of_lt hb_lt
        have hz0 : 0 ≤ τ - b := by linarith
        have hγup : b - Real.pi / 2 ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi)
            + 2.6 * Real.sqrt c) (Real.pi / 2) :=
          le_trans (le_abs_self _) hb_phase
        have hzup : τ - b ≤ Real.pi / 2 - (b - Real.pi / 2) := by
          have h1 : τ ≤ Real.pi := le_trans hτ.2 hsπ
          linarith
        have hA : |F b - m b| ≤ 4 * c + (1 - Real.cos (b - Real.pi / 2)) :=
          hanchor b hbIcc hb_eq
        have hB : |Cc| ≤ Real.sqrt (2 * c - c * c) + Real.sin (b - Real.pi / 2) := by
          have hP' : |P| ≤ Real.sqrt (2 * c - c * c) := by
            rw [hP]; exact hFpb_le b hbIcc hb_eq
          have h1 : Real.sin (b - Real.pi / 2) = -Real.cos b := Real.sin_sub_pi_div_two b
          have h2 : 0 ≤ Real.sin (b - Real.pi / 2) :=
            Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hγ0])
              (by linarith [hbIcc.2, hsπ])
          have h3 : -β * Real.sin (b - Real.pi / 2) ≤ Real.sin (b - Real.pi / 2) := by
            have h4 : -β ≤ 1 := by linarith [hβ1]
            exact mul_le_of_le_one_left h2 h4
          have h5 : β * Real.cos b = -β * Real.sin (b - Real.pi / 2) := by rw [h1]; ring
          have h6 : |β * Real.cos b| = -β * Real.sin (b - Real.pi / 2) := by
            rw [h5]
            exact abs_of_nonneg (mul_nonneg (by linarith [hβ_le]) h2)
          have h7 : |P - β * Real.cos b| ≤ |P| + |β * Real.cos b| := abs_sub _ _
          rw [hCc]
          linarith [h7, h6, h3, hP']
        have harith := Work.Diff.C.geoCrux.good_value_arith4 (γ' := b - Real.pi / 2)
          hc hc96 hε₁ hnum2 hlamdef (by linarith [hγ0]) hγup hA hB
        have hcmp := hrestart b τ hbIcc hτ hb_lt hb_eq hb_good
        have hcmpP : |F τ - (F b * Real.cos (τ - b) + P * Real.sin (τ - b))|
            ≤ ε₁ * (τ - b) := by
          rw [← hP] at hcmp
          exact hcmp
        have hdec : F τ - m τ
            = (F τ - (F b * Real.cos (τ - b) + P * Real.sin (τ - b)))
              + ((F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)) := by
          have h4 : Real.sin τ = Real.sin b * Real.cos (τ - b) + Real.cos b * Real.sin (τ - b) := by
            rw [← Real.sin_add]; congr 1; ring
          rw [hmval τ, hmval b, h4, hCc]; ring
        have hampl : |(F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)|
            ≤ min (|F b - m b| + |Cc| * Real.cos (b - Real.pi / 2))
              (Real.sqrt ((F b - m b) ^ 2 + Cc ^ 2)) := by
          refine le_min ?_ ?_
          · have hsin_le : Real.sin (τ - b) ≤ Real.cos (b - Real.pi / 2) := by
              have h1 : τ - b ≤ Real.pi / 2 - (b - Real.pi / 2) := hzup
              have h2 : Real.sin (τ - b) ≤ Real.sin (Real.pi / 2 - (b - Real.pi / 2)) :=
                Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) h1
              rwa [Real.sin_pi_div_two_sub] at h2
            have h0 : 0 ≤ Real.sin (τ - b) := Real.sin_nonneg_of_nonneg_of_le_pi hz0 (by linarith)
            have hc0 : 0 ≤ Real.cos (b - Real.pi / 2) :=
              Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
            calc |(F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)|
                ≤ |(F b - m b) * Real.cos (τ - b)| + |Cc * Real.sin (τ - b)| := abs_add_le _ _
              _ = |F b - m b| * |Real.cos (τ - b)| + |Cc| * |Real.sin (τ - b)| := by
                  rw [abs_mul, abs_mul]
              _ ≤ |F b - m b| + |Cc| * Real.cos (b - Real.pi / 2) := by
                  have h1 : |Real.cos (τ - b)| ≤ 1 := Real.abs_cos_le_one _
                  have h2 : |Real.sin (τ - b)| ≤ Real.cos (b - Real.pi / 2) := by
                    rw [abs_of_nonneg h0]; exact hsin_le
                  have h3 : 0 ≤ |F b - m b| := abs_nonneg _
                  have h4 : 0 ≤ |Cc| := abs_nonneg _
                  have h5 := mul_le_mul_of_nonneg_left h1 h3
                  have h6 := mul_le_mul_of_nonneg_left h2 h4
                  rw [mul_one] at h5
                  linarith [h5, h6]
          · have h3 : ((F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)) ^ 2
                ≤ ((F b - m b) ^ 2 + Cc ^ 2) * (Real.cos (τ - b) ^ 2 + Real.sin (τ - b) ^ 2) := by
              nlinarith [sq_nonneg ((F b - m b) * Real.sin (τ - b) - Cc * Real.cos (τ - b))]
            have h4 : Real.cos (τ - b) ^ 2 + Real.sin (τ - b) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
            calc |(F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)|
                = Real.sqrt (((F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)) ^ 2) :=
                  (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt (((F b - m b) ^ 2 + Cc ^ 2)
                    * (Real.cos (τ - b) ^ 2 + Real.sin (τ - b) ^ 2)) := Real.sqrt_le_sqrt h3
              _ = Real.sqrt ((F b - m b) ^ 2 + Cc ^ 2) := by rw [h4, mul_one]
        have hfin : |F τ - m τ| + 2 * Real.sqrt c ≤ 60 * lam := by
          have h1 : |F τ - m τ| ≤ |F τ - (F b * Real.cos (τ - b) + P * Real.sin (τ - b))|
              + |(F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)| := by
            rw [hdec]; exact abs_add_le _ _
          have h2 : ε₁ * (τ - b) ≤ ε₁ * Real.pi := by
            have h3 : τ - b ≤ Real.pi := by linarith [le_trans hτ.2 hsπ]
            nlinarith [hε₁, h3, hz0]
          linarith [h1, hcmpP, h2, hampl, harith]
        exact hfin
      -- ==================================================================
      -- (B') τ in the good region with a dip time before it, b < π/2: crude bounds
      have hgoodcase_lo : ∀ b τ : ℝ, b ∈ Set.Icc (0 : ℝ) s → τ ∈ Set.Icc (0 : ℝ) s → b < τ →
          F b = -1 + c → (∀ σ ∈ Set.Ioc b τ, -1 + c < F σ) → b < Real.pi / 2 →
          |F τ - m τ| + 2 * Real.sqrt c ≤ 60 * lam := by
        intro b τ hbIcc hτ hb_lt hb_eq hb_good hblt
        set P : ℝ := gradRay hmet f p u b with hP
        set Cc : ℝ := P - β * Real.cos b with hCc
        have hb_le : b ≤ τ := le_of_lt hb_lt
        have hz0 : 0 ≤ τ - b := by linarith
        -- b ≥ π/2 - δ from the triangle inequality
        have hLb : Real.pi - Real.arccos (1 - c) ≤ rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)) :=
          (hloc_mem b hbIcc (le_of_eq hb_eq)).1
        have hLb' : rdist (I := I) (M := M) q
            (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u)) ≤ Real.pi / 2 + b := by
          have htri := Work.Diff.C.dipAux_triangle (I := I) (M := M) (cov := cov) hmet htor q p
            (Submission.GlobalExp.GExp (cov := cov) hmet p (b • u))
          rw [hqp, hray b hbIcc] at htri
          exact htri
        have hbδ : Real.pi / 2 - Real.arccos (1 - c) ≤ b := by linarith
        have hγ1 : 1 - Real.cos (b - Real.pi / 2) ≤ c := by
          have hu0 : 0 ≤ Real.pi / 2 - b := by linarith
          have hud : Real.pi / 2 - b ≤ Real.arccos (1 - c) := by linarith
          have hcos : Real.cos (Real.arccos (1 - c)) ≤ Real.cos (Real.pi / 2 - b) :=
            Real.cos_le_cos_of_nonneg_of_le_pi hu0 (Real.arccos_le_pi _) hud
          rw [Real.cos_arccos (by linarith) (by linarith)] at hcos
          have h2 : Real.cos (b - Real.pi / 2) = Real.cos (Real.pi / 2 - b) := by
            rw [← hsincos b, Real.cos_pi_div_two_sub]
          linarith
        have hA : |F b - m b| ≤ 4 * c + (1 - Real.cos (b - Real.pi / 2)) :=
          hanchor b hbIcc hb_eq
        have hA' : |F b - m b| ≤ 5 * c := by linarith [hA, hγ1]
        have hB : |P| ≤ Real.sqrt (2 * c - c * c) := by
          rw [hP]; exact hFpb_le b hbIcc hb_eq
        have hβcos : |β * Real.cos b| ≤ Real.sqrt (2 * c) := by
          have hcb0 : 0 ≤ Real.cos b :=
            Real.cos_nonneg_of_mem_Icc ⟨by linarith [hbIcc.1], by linarith⟩
          have hcb : Real.cos b ≤ Real.sqrt (2 * c) := by
            have h1 : Real.cos b = Real.sin (Real.pi / 2 - b) :=
              (Real.sin_pi_div_two_sub b).symm
            have h2 : Real.pi / 2 - b ≤ Real.arccos (1 - c) := by linarith
            have h3 : Real.sin (Real.pi / 2 - b) ≤ Real.sin (Real.arccos (1 - c)) :=
              Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith)
                (Real.arccos_le_pi_div_two.mpr (by linarith [hc])) h2
            have h4 : Real.sin (Real.arccos (1 - c)) = Real.sqrt (1 - (1 - c) ^ 2) := by
              rw [Real.sin_arccos]
            have h5 : Real.sqrt (1 - (1 - c) ^ 2) ≤ Real.sqrt (2 * c) :=
              Real.sqrt_le_sqrt (by nlinarith [hc])
            rw [h1]; linarith [h3, h4, h5]
          calc |β * Real.cos b| = |β| * Real.cos b := by rw [abs_mul, abs_of_nonneg hcb0]
            _ ≤ 1 * Real.sqrt (2 * c) := mul_le_mul hβ_abs hcb hcb0 zero_le_one
            _ = Real.sqrt (2 * c) := one_mul _
        have hB' : |Cc| ≤ Real.sqrt (2 * c - c * c) + Real.sqrt (2 * c) := by
          have h2 : |P - β * Real.cos b| ≤ |P| + |β * Real.cos b| := abs_sub _ _
          rw [hCc]
          linarith [h2, hβcos, hB]
        have hcmp := hrestart b τ hbIcc hτ hb_lt hb_eq hb_good
        have hcmpP : |F τ - (F b * Real.cos (τ - b) + P * Real.sin (τ - b))| ≤ ε₁ * (τ - b) := by
          rw [← hP] at hcmp
          exact hcmp
        have hfin : |F τ - m τ| + 2 * Real.sqrt c ≤ 60 * lam := by
          have hdec : F τ - m τ
              = (F τ - (F b * Real.cos (τ - b) + P * Real.sin (τ - b)))
                + ((F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)) := by
            have h4 : Real.sin τ = Real.sin b * Real.cos (τ - b) + Real.cos b * Real.sin (τ - b) := by
              rw [← Real.sin_add]; congr 1; ring
            rw [hmval τ, hmval b, h4, hCc]; ring
          have h1 : |F τ - m τ| ≤ ε₁ * (τ - b) + |F b - m b| + |Cc| := by
            have h2 : |(F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b)|
                ≤ |F b - m b| + |Cc| := by
              have h3 : |(F b - m b) * Real.cos (τ - b)| ≤ |F b - m b| := by
                rw [abs_mul]
                calc |F b - m b| * |Real.cos (τ - b)| ≤ |F b - m b| * 1 :=
                      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
                  _ = |F b - m b| := mul_one _
              have h4 : |Cc * Real.sin (τ - b)| ≤ |Cc| := by
                rw [abs_mul]
                calc |Cc| * |Real.sin (τ - b)| ≤ |Cc| * 1 :=
                      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
                  _ = |Cc| := mul_one _
              have h5 := abs_add_le ((F b - m b) * Real.cos (τ - b)) (Cc * Real.sin (τ - b))
              linarith [h5, h3, h4]
            rw [hdec]
            have h6 := abs_add_le (F τ - (F b * Real.cos (τ - b) + P * Real.sin (τ - b)))
              ((F b - m b) * Real.cos (τ - b) + Cc * Real.sin (τ - b))
            linarith [h6, h2, hcmpP]
          have h2 : ε₁ * (τ - b) ≤ ε₁ * Real.pi := by
            have h3 : τ - b ≤ Real.pi := by linarith [le_trans hτ.2 hsπ, hbIcc.1]
            nlinarith [hε₁, h3, hz0]
          have h3 : Real.sqrt (2 * c - c * c) ≤ Real.sqrt (2 * c) :=
            Real.sqrt_le_sqrt (by nlinarith [hc])
          have h4 : Real.sqrt (2 * c) ≤ 2 * Real.sqrt c := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
            have hs2 : Real.sqrt 2 ≤ 2 := by
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
            nlinarith [hs2, Real.sqrt_nonneg c]
          have h5 : Real.sqrt (2 * c) ≤ 2 * lam := le_trans h4 h2sc
          have h6 : 2 * Real.sqrt c ≤ 2 * lam := h2sc
          have h7 : 5 * c ≤ 5 * lam := by nlinarith [hc_lam, hlam_pos]
          linarith [h1, h2, hA', hB, hB', h3, h5, h6, h7, hπε'', hslc]
        exact hfin
      -- ==================================================================
      -- (C) τ in the good region with no dip time before it
      have hprefix : ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) s →
          (∀ σ ∈ Set.Icc (0 : ℝ) s, σ ≤ τ → -1 + c < F σ) →
          |F τ - m τ| ≤ 60 * lam ∧ (F τ ≤ -1 + 2 * c → |Real.cos τ| ≤ 60 * lam)
            ∧ (Real.pi - Real.arccos (1 - 2 * c) ≤ τ → |F τ| ≤ 60 * lam) := by
        intro τ hτ hgoodprev
        clear hloc_phase_sharp hloc_phase hloc_mem hlast hrestart hFpb_le hanchor hdipcase
          hgoodcase hgoodcase_lo
        have hgood : ∀ σ ∈ Set.Icc (0 : ℝ) τ, -1 + c < fFam (I := I) (M := M) (cov := cov)
            hmet p e (Fin.succ k) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
          intro σ hσ
          have h := hgoodprev σ ⟨hσ.1, le_trans hσ.2 hτ.2⟩ hσ.2
          show -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
          exact h
        have hv := Work.Diff.C.value_off_cap (I := I) (M := M) (cov := cov) hmet htor hε₁ hsmC
          hHess hinit hu hτ.1 hgood
        have hcmpτ : |F τ - m τ| ≤ ε₁ * Real.pi := by
          have h2 : m τ = Inner.inner ℝ (e k) u * Real.sin τ := by rw [hmval, hβdef]
          rw [hFfam τ, h2]
          refine le_trans hv ?_
          exact mul_le_mul_of_nonneg_left (le_trans hτ.2 hsπ) hε₁
        have hI : |F τ - m τ| ≤ 60 * lam := by linarith [hcmpτ, hπε'', hslc]
        clear hv hgood hgoodprev
        have hII : F τ ≤ -1 + 2 * c → |Real.cos τ| ≤ 60 * lam := by
          intro hclamp
          have h1 : β * Real.sin τ ≤ -1 + 2 * c + ε₁ * Real.pi := by
            have h := (abs_le.mp hcmpτ).1
            linarith
          have hsin : 1 - 2 * c - ε₁ * Real.pi ≤ Real.sin τ := by
            have hs0τ := Real.sin_nonneg_of_nonneg_of_le_pi hτ.1 (le_trans hτ.2 hsπ)
            nlinarith [hβ1, hs0τ, h1]
          have hcos2 : Real.cos τ ^ 2 ≤ 4.5 * c := by
            have h1 : Real.sin τ ^ 2 + Real.cos τ ^ 2 = 1 := Real.sin_sq_add_cos_sq τ
            have h2 : Real.sin τ ≤ 1 := Real.sin_le_one τ
            nlinarith [h1, hsin, h2, hπε]
          have hsq : Real.cos τ ^ 2 ≤ (60 * lam) ^ 2 := by
            have h1 : (4.5 : ℝ) * c ≤ (60 * lam) ^ 2 := by
              have h2 : (60 * lam) ^ 2 = 3600 * lam ^ 2 := by ring
              linarith [h2, hc_lam]
            linarith [hcos2, h1]
          calc |Real.cos τ| = Real.sqrt (Real.cos τ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ Real.sqrt ((60 * lam) ^ 2) := Real.sqrt_le_sqrt hsq
            _ = 60 * lam := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
        have hIII : Real.pi - Real.arccos (1 - 2 * c) ≤ τ → |F τ| ≤ 60 * lam := by
          intro hfarτ
          have h1 : |F τ| ≤ |F τ - m τ| + |m τ| := by
            have h2 := abs_add_le (F τ - m τ) (m τ)
            rwa [sub_add_cancel] at h2
          have h2 : |m τ| ≤ Real.sin τ := hm_le_sin τ hτ
          have h3 : Real.sin τ ≤ 2 * Real.sqrt c := hsin_far τ hτ hfarτ
          linarith [h1, hcmpτ, h2, h3, hπε'', hslc]
        exact ⟨hI, hII, hIII⟩
      -- ==================================================================
      -- assembly
      refine ⟨fun τ hτ hclamp => ?_, fun τ hτ hfarτ => ?_, fun τ hτ => ?_⟩
      · by_cases hdipτ : F τ ≤ -1 + c
        · exact (hdipcase τ hτ hdipτ).2.1
        · have hgoodτ : -1 + c < F τ := not_le.mp hdipτ
          by_cases hbefore : ∃ σ ∈ Set.Icc (0 : ℝ) s, σ ≤ τ ∧ F σ ≤ -1 + c
          · obtain ⟨b, hbIcc, hb_lt, hb_eq, hb_good⟩ := hlast τ hτ hgoodτ hbefore
            have hb_phase : |b - Real.pi / 2| ≤ 52.6 * lam := hloc_phase b hbIcc (le_of_eq hb_eq)
            have hcmp := hrestart b τ hbIcc hτ hb_lt hb_eq hb_good
            have hFpb := hFpb_le b hbIcc hb_eq
            have hann := annulus_phase5 hc hc96 hε₁ hnum2 (by linarith)
              (by linarith [le_trans hτ.2 hsπ, hbIcc.1]) hb_eq hFpb hcmp hgoodτ hclamp
            have hns : τ - b ≤ 5 * Real.sqrt c := hann
            have h3sc : 5 * Real.sqrt c ≤ 5 * lam :=
              mul_le_mul_of_nonneg_left hslc (by norm_num)
            have hphaseτ : |τ - Real.pi / 2| ≤ 57.6 * lam := by
              have h1 : |τ - Real.pi / 2| ≤ |b - Real.pi / 2| + |τ - b| := by
                calc |τ - Real.pi / 2| = |(b - Real.pi / 2) + (τ - b)| := by ring_nf
                  _ ≤ |b - Real.pi / 2| + |τ - b| := abs_add_le _ _
              have h2 : |τ - b| = τ - b := abs_of_nonneg (by linarith [hb_lt])
              linarith [h1, h2, hb_phase, hns, h3sc]
            have hcτ : |Real.cos τ| = |Real.sin (τ - Real.pi / 2)| := by
              rw [Real.sin_sub_pi_div_two, abs_neg]
            rw [hcτ]
            exact le_trans Real.abs_sin_le_abs (by linarith)
          · exact (hprefix τ hτ (fun σ hσ hστ => not_le.mp (fun hcon =>
              hbefore ⟨σ, hσ, hστ, hcon⟩))).2.1 hclamp
      · by_cases hdipτ : F τ ≤ -1 + c
        · exact (hdipcase τ hτ hdipτ).2.2 hfarτ
        · have hgoodτ : -1 + c < F τ := not_le.mp hdipτ
          by_cases hbefore : ∃ σ ∈ Set.Icc (0 : ℝ) s, σ ≤ τ ∧ F σ ≤ -1 + c
          · obtain ⟨b, hbIcc, hb_lt, hb_eq, hb_good⟩ := hlast τ hτ hgoodτ hbefore
            have hb_phase : |b - Real.pi / 2| ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi)
                + 2.6 * Real.sqrt c) (Real.pi / 2) :=
              hloc_phase_sharp b hbIcc (le_of_eq hb_eq)
            by_cases hb2 : Real.pi / 2 ≤ b
            · have h := hgoodcase b τ hbIcc hτ hb_lt hb_eq hb_good hb2 hb_phase
              have h1 : |F τ| ≤ |F τ - m τ| + |m τ| := by
                have h2 := abs_add_le (F τ - m τ) (m τ)
                rwa [sub_add_cancel] at h2
              have h2 : |m τ| ≤ Real.sin τ := hm_le_sin τ hτ
              have h3 : Real.sin τ ≤ 2 * Real.sqrt c := hsin_far τ hτ hfarτ
              linarith [h, h1, h2, h3]
            · have h := hgoodcase_lo b τ hbIcc hτ hb_lt hb_eq hb_good (not_le.mp hb2)
              have h1 : |F τ| ≤ |F τ - m τ| + |m τ| := by
                have h2 := abs_add_le (F τ - m τ) (m τ)
                rwa [sub_add_cancel] at h2
              have h2 : |m τ| ≤ Real.sin τ := hm_le_sin τ hτ
              have h3 : Real.sin τ ≤ 2 * Real.sqrt c := hsin_far τ hτ hfarτ
              linarith [h, h1, h2, h3]
          · exact (hprefix τ hτ (fun σ hσ hστ => not_le.mp (fun hcon =>
              hbefore ⟨σ, hσ, hστ, hcon⟩))).2.2 hfarτ
      · by_cases hdipτ : F τ ≤ -1 + c
        · exact (hdipcase τ hτ hdipτ).1
        · have hgoodτ : -1 + c < F τ := not_le.mp hdipτ
          by_cases hbefore : ∃ σ ∈ Set.Icc (0 : ℝ) s, σ ≤ τ ∧ F σ ≤ -1 + c
          · obtain ⟨b, hbIcc, hb_lt, hb_eq, hb_good⟩ := hlast τ hτ hgoodτ hbefore
            have hb_phase : |b - Real.pi / 2| ≤ min (50 * (Real.sqrt c + ε₁ * Real.pi)
                + 2.6 * Real.sqrt c) (Real.pi / 2) :=
              hloc_phase_sharp b hbIcc (le_of_eq hb_eq)
            by_cases hb2 : Real.pi / 2 ≤ b
            · have h := hgoodcase b τ hbIcc hτ hb_lt hb_eq hb_good hb2 hb_phase
              linarith [h, h2sc, hsc_pos]
            · have h := hgoodcase_lo b τ hbIcc hτ hb_lt hb_eq hb_good (not_le.mp hb2)
              linarith [h, h2sc, hsc_pos]
          · exact (hprefix τ hτ (fun σ hσ hστ => not_le.mp (fun hcon =>
              hbefore ⟨σ, hσ, hστ, hcon⟩))).1
    · -- ============ no dip at all ============
      have hgood_all : ∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + c < F σ := by
        intro σ hσ
        by_contra hcon
        exact hdipne ⟨σ, hσ, not_lt.mp hcon⟩
      have hnodip : ∀ τ ∈ Set.Icc (0 : ℝ) s,
          |F τ - m τ| ≤ 60 * lam ∧ (F τ ≤ -1 + 2 * c → |Real.cos τ| ≤ 60 * lam)
            ∧ (Real.pi - Real.arccos (1 - 2 * c) ≤ τ → |F τ| ≤ 60 * lam) := by
        intro τ hτ
        have hgood : ∀ σ ∈ Set.Icc (0 : ℝ) τ, -1 + c < fFam (I := I) (M := M) (cov := cov)
            hmet p e (Fin.succ k) (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) := by
          intro σ hσ
          have h := hgood_all σ ⟨hσ.1, le_trans hσ.2 hτ.2⟩
          show -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
          exact h
        have hv := Work.Diff.C.value_off_cap (I := I) (M := M) (cov := cov) hmet htor hε₁ hsmC
          hHess hinit hu hτ.1 hgood
        have hcmpτ : |F τ - m τ| ≤ ε₁ * Real.pi := by
          have h2 : m τ = Inner.inner ℝ (e k) u * Real.sin τ := by rw [hmval, hβdef]
          rw [hFfam τ, h2]
          refine le_trans hv ?_
          exact mul_le_mul_of_nonneg_left (le_trans hτ.2 hsπ) hε₁
        have hI : |F τ - m τ| ≤ 60 * lam := by linarith [hcmpτ, hπε'', hslc]
        have hII : F τ ≤ -1 + 2 * c → |Real.cos τ| ≤ 60 * lam := by
          intro hclamp
          have h1 : β * Real.sin τ ≤ -1 + 2 * c + ε₁ * Real.pi := by
            have h := (abs_le.mp hcmpτ).1
            linarith
          have hsin : 1 - 2 * c - ε₁ * Real.pi ≤ Real.sin τ := by
            have hs0τ := Real.sin_nonneg_of_nonneg_of_le_pi hτ.1 (le_trans hτ.2 hsπ)
            nlinarith [hβ1, hs0τ, h1]
          have hcos2 : Real.cos τ ^ 2 ≤ 4.5 * c := by
            have h1 : Real.sin τ ^ 2 + Real.cos τ ^ 2 = 1 := Real.sin_sq_add_cos_sq τ
            have h2 : Real.sin τ ≤ 1 := Real.sin_le_one τ
            nlinarith [h1, hsin, h2, hπε]
          have hsq : Real.cos τ ^ 2 ≤ (60 * lam) ^ 2 := by
            have h1 : (4.5 : ℝ) * c ≤ (60 * lam) ^ 2 := by
              have h2 : (60 * lam) ^ 2 = 3600 * lam ^ 2 := by ring
              linarith [h2, hc_lam]
            linarith [hcos2, h1]
          calc |Real.cos τ| = Real.sqrt (Real.cos τ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ Real.sqrt ((60 * lam) ^ 2) := Real.sqrt_le_sqrt hsq
            _ = 60 * lam := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
        have hIII : Real.pi - Real.arccos (1 - 2 * c) ≤ τ → |F τ| ≤ 60 * lam := by
          intro hfarτ
          have h1 : |F τ| ≤ |F τ - m τ| + |m τ| := by
            have h2 := abs_add_le (F τ - m τ) (m τ)
            rwa [sub_add_cancel] at h2
          have h2 : |m τ| ≤ Real.sin τ := hm_le_sin τ hτ
          have h3 : Real.sin τ ≤ 2 * Real.sqrt c := hsin_far τ hτ hfarτ
          linarith [h1, hcmpτ, h2, h3, hπε'', hslc]
        exact ⟨hI, hII, hIII⟩
      refine ⟨fun τ hτ hclamp => (hnodip τ hτ).2.1 hclamp, fun τ hτ hfarτ => (hnodip τ hτ).2.2 hfarτ,
        fun τ hτ => (hnodip τ hτ).1⟩
  · -- ===================== trivial case: 60 λ ≥ 2 =====================
    push_neg at hsmall
    have h2le : 2 ≤ 60 * lam := hsmall
    have hF1 : ∀ τ : ℝ, |F τ| ≤ 1 := by
      intro τ
      rw [hFcos τ, abs_le]
      exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hm1 : ∀ τ : ℝ, |m τ| ≤ 1 := by
      intro τ
      rw [hmval, abs_mul]
      have h4 : |Real.sin τ| ≤ 1 := Real.abs_sin_le_one τ
      calc |β| * |Real.sin τ| ≤ 1 * 1 := mul_le_mul hβ_abs h4 (abs_nonneg _) zero_le_one
        _ = 1 := mul_one 1
    refine ⟨fun τ hτ _ => ?_, fun τ hτ _ => ?_, fun τ hτ => ?_⟩
    · have h1 : |Real.cos τ| ≤ 1 := Real.abs_cos_le_one τ
      linarith
    · linarith [hF1 τ, h2le]
    · have h1 : |F τ - m τ| ≤ |F τ| + |m τ| := abs_sub _ _
      linarith [h1, hF1 τ, hm1 τ, h2le]

end Work.Diff.C.geoCrux