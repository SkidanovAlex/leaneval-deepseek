import Submission.Work.RiemLib.HingeGlobal
import Submission.Work.RiemLib.HopfRinow2
import Submission.Work.RiemLib.Commons.Geometry.Sphere.modelDist_hinge_step

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Key Lemma for the globalisation of the hinge comparison

This file starts the implementation of the *Key Lemma* (`Submission/Roadmap.lean` §31): the
statement that the hinge comparison for hinges of size `< (2/3) l` at all points of `B_l(p)`
implies the hinge comparison at `p` for hinges of size `< l`.  Iterating it (with the
Archimedean property and the uniformity of the local comparison radius over the compact
manifold) gives Toponogov's hinge comparison for hinges of size `< π`, which is what
Grove–Shiohama's Step 2 uses.

## Contents

* `HingeCompG` — the hinge comparison at a point, in the language of the *global* exponential
  map `GExp` (so that the sides can have any length, not only the local radius of `expMap`);
* `GCompHolds` — the comparison holds at `z` for all hinges of size `< r` with minimising sides;
* `gcompHolds_of_local` — the local comparison in that language.

The construction of the *smaller* violating hinge (Step 1 of the Key Lemma's proof) follows in
the next part of the file.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.HingeKey

noncomputable section

open Submission.HingeGlobal

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The hinge comparison at the apex `z`**, in the language of the global exponential map
`GExp`: the distance between the endpoints of the hinge is at most the model distance. -/
def HingeCompG (hmet : IsMetricCompatible cov) (z : M)
    (a b : ℝ) (v w : TangentSpace I z) : Prop :=
  Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
      (GExp (cov := cov) hmet z (b • w))
    ≤ ENNReal.ofReal (modelDist1 (hingeAngle v w) a b)

/-- **The hinge comparison holds at `z` for all hinges of size `< r`** (the sides being
minimising), in the language of the global exponential map. -/
def GCompHolds (hmet : IsMetricCompatible cov) (z : M) (r : ℝ) : Prop :=
  ∀ (a b : ℝ) (v w : TangentSpace I z), 0 < a → 0 < b → a + b < r → ‖v‖ = 1 → ‖w‖ = 1 →
    Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (a • v)) = ENNReal.ofReal a →
    Manifold.riemannianEDist I z (GExp (cov := cov) hmet z (b • w)) = ENNReal.ofReal b →
    HingeCompG (cov := cov) hmet z a b v w

/-- **The local hinge comparison in the global-exp language.**  Every point has a positive radius
on which the hinge comparison holds. -/
theorem gcompHolds_of_local
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (z : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ GCompHolds (cov := cov) hmet z ρ := by
  obtain ⟨ρ₁, hρ₁, h₁⟩ := Submission.HingeLocal.edist_expMap_le_model
    (cov := cov) hmet htor hpinch z
  obtain ⟨ρ₂, hρ₂, h₂⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet z
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro a b v w ha hb hab hv hw hmina hminb
  have har : ‖a • v‖ = a := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hv, mul_one]
  have hbr : ‖b • w‖ = b := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb, hw, mul_one]
  have haρ : a < min ρ₁ ρ₂ := lt_of_lt_of_le (lt_add_of_pos_right a hb) hab.le
  have hbρ : b < min ρ₁ ρ₂ := lt_of_lt_of_le (lt_add_of_pos_left b ha) hab.le
  have hGa : GExp (cov := cov) hmet z (a • v) = expMap cov z (a • v) :=
    h₂ _ (by rw [har]; exact lt_of_lt_of_le haρ (min_le_right _ _))
  have hGb : GExp (cov := cov) hmet z (b • w) = expMap cov z (b • w) :=
    h₂ _ (by rw [hbr]; exact lt_of_lt_of_le hbρ (min_le_right _ _))
  have hmain := h₁ a b v w ha (lt_of_lt_of_le haρ (min_le_left _ _)) hb
    (lt_of_lt_of_le hbρ (min_le_left _ _)) hv hw
  show Manifold.riemannianEDist I (GExp (cov := cov) hmet z (a • v))
      (GExp (cov := cov) hmet z (b • w)) ≤ _
  rw [hGa, hGb]
  refine hmain.trans_eq ?_
  rw [modelDist1, cos_hingeAngle hv hw]

/-! ## The ray of a minimising geodesic: continuation identities -/

/-- The velocity of a `geodCurve` is a unit vector. -/
lemma norm_curveVelocity_geodCurve (hmet : IsMetricCompatible cov) {T : ℝ} (hT : 0 ≤ T)
    (x : M) (ξ : TangentSpace I x) (hξ : ‖ξ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t‖ = 1 := by
  have hδ := geodDelta_pos (cov := cov) hmet
  have hmem : t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  exact (geodCurve_spec (cov := cov) hmet T hT x ξ hξ).2.2.2.2 t hmem

/-- **Backward continuation of a `geodCurve`**, in unit-vector form. -/
lemma GExp_neg_curveVelocity_geodCurve (hmet : IsMetricCompatible cov)
    {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1) {T : ℝ} (hT : 0 ≤ T)
    {t s : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hs0 : 0 ≤ s) (hst : s ≤ t) :
    GExp (cov := cov) hmet ((geodCurve (cov := cov) hmet T hT x ξ hξ) t)
        (s • (-(curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t)))
      = (geodCurve (cov := cov) hmet T hT x ξ hξ) (t - s) := by
  rw [smul_neg, ← neg_smul]
  exact GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet x hξ hT ht0 htT hs0 hst

/-- **Forward continuation of a `geodCurve`. -/
lemma GExp_add_curveVelocity_geodCurve (hmet : IsMetricCompatible cov)
    {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1) {T : ℝ} (hT : 0 ≤ T)
    {t s : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hs0 : 0 ≤ s) (hts : t + s ≤ T) :
    GExp (cov := cov) hmet ((geodCurve (cov := cov) hmet T hT x ξ hξ) t)
        (s • (curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t))
      = (geodCurve (cov := cov) hmet T hT x ξ hξ) (t + s) :=
  GExp_geodCurve_add (cov := cov) hmet x hξ hT ht0 htT hs0 hts

/-- **Sub-arcs of a minimising ray are minimising.**  If the `geodCurve` segment `[0,s]` is
minimising (`d(x, G s) = s`), then so is every sub-arc `[a,b] ⊆ [0,s]`. -/
lemma geodCurve_sub_arc_minimising' (hmet : IsMetricCompatible cov)
    {T : ℝ} (hT : 0 ≤ T) {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T)
    (hmin : Manifold.riemannianEDist I x ((geodCurve (cov := cov) hmet T hT x ξ hξ) s)
      = ENNReal.ofReal s) :
    ∀ a ∈ Set.Icc (0 : ℝ) s, ∀ b ∈ Set.Icc (0 : ℝ) s, a ≤ b →
      Manifold.riemannianEDist I ((geodCurve (cov := cov) hmet T hT x ξ hξ) a)
        ((geodCurve (cov := cov) hmet T hT x ξ hξ) b) = ENNReal.ofReal (b - a) := by
  have hδ := geodDelta_pos (cov := cov) hmet
  obtain ⟨hG0, -, hsm, -, hsp⟩ := geodCurve_spec (cov := cov) hmet T hT x ξ hξ
  have hsub : Set.Icc (0 : ℝ) s ⊆
      Set.Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2, hsT, hδ]⟩
  have hC : CMDiff[Set.Icc (0 : ℝ) s] 1 (geodCurve (cov := cov) hmet T hT x ξ hξ) :=
    (hsm.mono hsub).of_le (WithTop.coe_le_coe.mpr le_top)
  have hsp' : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ‖curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t‖ = 1 :=
    fun t ht => hsp t (hsub ht)
  have hmin' : Manifold.riemannianEDist I ((geodCurve (cov := cov) hmet T hT x ξ hξ) 0)
      ((geodCurve (cov := cov) hmet T hT x ξ hξ) s) = ENNReal.ofReal s := by
    rw [hG0]; exact hmin
  exact Submission.Minimising.riemannianEDist_eq_ofReal_of_unit_speed_of_minimising
    (I := I) hs0 hC hsp' hmin'

/-! ## Small auxiliary facts about the model distance -/

lemma hingeAngle_comm {z : M} (v w : TangentSpace I z) :
    hingeAngle v w = hingeAngle w v := by
  simp only [hingeAngle, real_inner_comm]

lemma modelDist1_comm (θ a b : ℝ) : modelDist1 θ a b = modelDist1 θ b a := by
  simp only [modelDist1]
  ring_nf

lemma modelDist1_nonneg (θ a b : ℝ) : 0 ≤ modelDist1 θ a b := Real.arccos_nonneg _

lemma modelDist1_le_pi (θ a b : ℝ) : modelDist1 θ a b ≤ Real.pi := Real.arccos_le_pi _

/-- The model distance at angle `0` is the difference of the side lengths (for ordered sides). -/
lemma modelDist1_zero_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi) :
    modelDist1 0 a b = b - a := by
  rw [modelDist1]
  have harg : Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos 0
      = Real.cos (b - a) := by
    rw [Real.cos_zero, mul_one, Real.cos_sub b a]
    ring
  rw [harg, Real.arccos_cos (by linarith) (by linarith)]

/-- **Step 1 of the Key Lemma.**  From a *violating* hinge at `x` (sides to `p` and `q` of lengths
`t ≤ s`, both minimising, of total size in `(l/2, l)`) and the hinge comparison at all points of the
ball `B_l(p)` for hinges of size `< 2l/3`, one constructs a *new* violating hinge at a point `x'` on
the side `[x,q]`, of no larger size. -/
theorem key_step1
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {l : ℝ} (hlπ : l ≤ Real.pi)
    {c A B x : M} {t s : ℝ} {ξ η : TangentSpace I x} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (ht : 0 < t) (hs : 0 < s) (hts' : t ≤ s) (hts : t + s < l) (hl2 : l / 2 ≤ t + s)
    (hGA : GExp (cov := cov) hmet x (t • ξ) = A)
    (hGB : GExp (cov := cov) hmet x (s • η) = B)
    (hminA : Manifold.riemannianEDist I x A = ENNReal.ofReal t)
    (hminB : Manifold.riemannianEDist I x B = ENNReal.ofReal s)
    (hcx : Manifold.riemannianEDist I c x < ENNReal.ofReal l)
    (hcen : c = A ∨ c = B)
    (hcomp : ∀ z : M, Manifold.riemannianEDist I c z < ENNReal.ofReal l →
      GCompHolds (cov := cov) hmet z ((2/3) * l))
    (hviol : ENNReal.ofReal (modelDist1 (hingeAngle ξ η) t s) < Manifold.riemannianEDist I A B) :
    ∃ (x' : M) (s₁ : ℝ) (ξ' u' : TangentSpace I x') (w' s₂ : ℝ),
      s₁ = (l / 2 - t) / 3 ∧ s₂ = s - s₁ ∧ GExp (cov := cov) hmet x (s₁ • η) = x' ∧
      ‖ξ'‖ = 1 ∧ ‖u'‖ = 1 ∧ 0 < w' ∧ 0 < s₂ ∧ w' + s₂ ≤ t + s ∧
      Manifold.riemannianEDist I c x' < ENNReal.ofReal l ∧
      GExp (cov := cov) hmet x' (w' • ξ') = A ∧ GExp (cov := cov) hmet x' (s₂ • u') = B ∧
      Manifold.riemannianEDist I x' A = ENNReal.ofReal w' ∧
      Manifold.riemannianEDist I x' B = ENNReal.ofReal s₂ ∧
      w' ≤ modelDist1 (hingeAngle ξ η) t s₁ ∧
      |t - s₁| ≤ w' ∧
      Manifold.riemannianEDist I x x' = ENNReal.ofReal s₁ ∧
      modelDist1 (hingeAngle ξ' u') w' s₂ ≤ modelDist1 (hingeAngle ξ η) t s ∧
      ENNReal.ofReal (modelDist1 (hingeAngle ξ' u') w' s₂) < Manifold.riemannianEDist I A B := by
  classical
  have hl0 : 0 ≤ l := by linarith
  have hlpos : 0 < l := by linarith
  have hth : t < l / 2 := by linarith
  set s₁ : ℝ := (l / 2 - t) / 3 with hs₁def
  have hs₁pos : 0 < s₁ := by rw [hs₁def]; linarith
  have hs₁s : s₁ < s := by rw [hs₁def]; linarith
  have hs₁l : s₁ < l := by linarith
  have hcrit : t + 3 * s₁ = l / 2 := by rw [hs₁def]; ring
  have hsl : s ≤ l := by linarith
  have htl : t ≤ l := by linarith
  have hsposπ : s < Real.pi := by linarith
  have htposπ : t < Real.pi := by linarith
  -- the minimising geodesic through `x` in the direction `η`
  set G : ℝ → M := geodCurve (cov := cov) hmet l hl0 x η hη with hGdef
  have hG0 : G 0 = x := by
    rw [hGdef]; exact (geodCurve_spec (cov := cov) hmet l hl0 x η hη).1
  have hGs : G s = B := by
    rw [hGdef, ← GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := η) hη (T := l) hl0
      (r := s) hs.le hsl]
    exact hGB
  have hGs₁ : G s₁ = GExp (cov := cov) hmet x (s₁ • η) := by
    rw [hGdef]
    exact (GExp_eq_geodCurve (cov := cov) hmet (x := x) (u := η) hη (T := l) hl0
      (r := s₁) hs₁pos.le hs₁l.le).symm
  have hmin' : Manifold.riemannianEDist I x (G s) = ENNReal.ofReal s := by rw [hGs]; exact hminB
  have hsub : ∀ a ∈ Set.Icc (0:ℝ) s, ∀ b ∈ Set.Icc (0:ℝ) s, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) := by
    have h := geodCurve_sub_arc_minimising' (cov := cov) hmet hl0 hη hs.le hsl hmin'
    intro a ha b hb hab
    simp only [hGdef]
    exact h a ha b hb hab
  have hmet_xx' : Manifold.riemannianEDist I x (G s₁) = ENNReal.ofReal s₁ := by
    have h := hsub 0 ⟨le_refl 0, hs.le⟩ s₁ ⟨hs₁pos.le, hs₁s.le⟩ hs₁pos.le
    rw [hG0] at h
    simpa using h
  have hx'x : Manifold.riemannianEDist I (G s₁) x = ENNReal.ofReal s₁ := by
    rw [Manifold.riemannianEDist_comm]; exact hmet_xx'
  -- membership of `x'` in the ball of radius `l` around `c`
  have hx'mem : Manifold.riemannianEDist I c (G s₁) < ENNReal.ofReal l := by
    rcases hcen with hcA | hcB
    · subst hcA
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := c) (y := x) (z := G s₁)
      rw [Manifold.riemannianEDist_comm (I := I) (x := c) (y := x), hminA, hmet_xx'] at htri
      rw [← ENNReal.ofReal_add ht.le hs₁pos.le] at htri
      refine lt_of_le_of_lt htri ?_
      exact (ENNReal.ofReal_lt_ofReal_iff hlpos).mpr (by linarith [hcrit])
    · subst hcB
      have h := hsub s₁ ⟨hs₁pos.le, hs₁s.le⟩ s ⟨hs.le, le_refl s⟩ hs₁s.le
      rw [hGs] at h
      rw [Manifold.riemannianEDist_comm, h]
      exact (ENNReal.ofReal_lt_ofReal_iff hlpos).mpr (by linarith)
  -- the first hinge comparison, at `x`
  have hst1 : s₁ + t < (2/3) * l := by nlinarith [hcrit, hs₁pos]
  have hmin1 : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s₁ • η))
      = ENNReal.ofReal s₁ := by rw [← hGs₁]; exact hmet_xx'
  have hmin2 : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (t • ξ))
      = ENNReal.ofReal t := by rw [hGA]; exact hminA
  have h1raw := hcomp x hcx s₁ t η ξ hs₁pos ht hst1 hη hξ hmin1 hmin2
  have h1 : Manifold.riemannianEDist I (G s₁) A
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle ξ η) t s₁) := by
    rw [hGs₁, ← hGA]
    refine h1raw.trans_eq ?_
    rw [hingeAngle_comm η ξ, modelDist1_comm (hingeAngle ξ η) t s₁]
  -- Hopf–Rinow from `x'` to `p`
  obtain ⟨v₀, hv₀G, hv₀d⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
    (cov := cov) hmet htor (G s₁) A
  set w' : ℝ := ‖v₀‖ with hw'def
  have hw'mem : Manifold.riemannianEDist I (G s₁) A = ENNReal.ofReal w' := hv₀d
  have hw'le : w' ≤ modelDist1 (hingeAngle ξ η) t s₁ := by
    rw [← ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _), ← hw'mem]
    exact h1
  -- `w' > 0`
  have hw'pos : 0 < w' := by
    rw [hw'def]
    by_contra h
    push Not at h
    have hzero : ‖v₀‖ = 0 := le_antisymm h (norm_nonneg v₀)
    have hv₀zero : v₀ = 0 := norm_eq_zero.mp hzero
    have hx'A : G s₁ = A := by
      rw [← hv₀G, hv₀zero, GExp_zero]
    have hs₁t : s₁ = t := by
      have h2 : ENNReal.ofReal s₁ = ENNReal.ofReal t := by
        rw [← hmet_xx', hx'A, hminA]
      exact (ENNReal.ofReal_eq_ofReal_iff hs₁pos.le ht.le).mp h2
    have hABmin : Manifold.riemannianEDist I A B = ENNReal.ofReal (s - s₁) := by
      have h := hsub s₁ ⟨hs₁pos.le, hs₁s.le⟩ s ⟨hs.le, le_refl s⟩ hs₁s.le
      rw [hx'A, hGs] at h
      exact h
    have hv := hviol
    rw [hABmin, hs₁t] at hv
    have hlt : modelDist1 (hingeAngle ξ η) t s < s - t :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hv
    have hge : s - t ≤ modelDist1 (hingeAngle ξ η) t s := by
      have hθ0 : (0:ℝ) ≤ hingeAngle ξ η := Real.arccos_nonneg _
      have hθπ : hingeAngle ξ η ≤ Real.pi := Real.arccos_le_pi _
      have hbase : modelDist1 0 t s ≤ modelDist1 (hingeAngle ξ η) t s :=
        (modelDist1_le_iff ht htposπ hs hsposπ ⟨le_refl 0, Real.pi_pos.le⟩
          ⟨hθ0, hθπ⟩).mpr hθ0
      rw [modelDist1_zero_of_le ht.le hts' (le_of_lt hsposπ)] at hbase
      linarith
    linarith
  have hv₀ne : v₀ ≠ 0 := by
    intro h0
    have hzw : w' = 0 := by rw [hw'def, h0, norm_zero]
    rw [hzw] at hw'pos
    exact lt_irrefl 0 hw'pos
  set ξ' : TangentSpace I (G s₁) := unitOf v₀ hv₀ne with hξ'def
  have hξ'1 : ‖ξ'‖ = 1 := unitOf_norm v₀ hv₀ne
  have hw'smul : w' • ξ' = v₀ := by
    rw [hξ'def, hw'def, unitOf, smul_smul, mul_inv_cancel₀ (by simpa using hv₀ne), one_smul]
  have hGξ' : GExp (cov := cov) hmet (G s₁) (w' • ξ') = A := by
    rw [hw'smul]; exact hv₀G
  -- the velocity of the ray at `s₁`
  set velt : TangentSpace I (G s₁) :=
    curveVelocity (I := I) (geodCurve (cov := cov) hmet l hl0 x η hη) s₁ with hveltdef
  have hvelt1 : ‖velt‖ = 1 := by
    rw [hveltdef]
    exact norm_curveVelocity_geodCurve (cov := cov) hmet hl0 x η hη hs₁pos.le hs₁l.le
  have hnegvelt1 : ‖-velt‖ = 1 := by rw [norm_neg, hvelt1]
  -- the backward and forward rays
  have hback : GExp (cov := cov) hmet (G s₁) (s₁ • (-velt)) = x := by
    rw [hGdef, hveltdef]
    exact (GExp_neg_curveVelocity_geodCurve (cov := cov) hmet hη hl0 hs₁pos.le hs₁l.le
      hs₁pos.le (le_refl s₁)).trans (by rw [sub_self]; exact hG0)
  have hfwd : GExp (cov := cov) hmet (G s₁) ((s - s₁) • velt) = B := by
    rw [hGdef, hveltdef]
    exact (GExp_add_curveVelocity_geodCurve (cov := cov) hmet hη hl0 hs₁pos.le hs₁l.le
      (by linarith : 0 ≤ s - s₁) (by linarith : s₁ + (s - s₁) ≤ l)).trans
      (by rw [show s₁ + (s - s₁) = s from by ring]; exact hGs)
  -- the second hinge comparison, at `x'`
  have hw'le' : w' ≤ t + s₁ := by
    have htri := Manifold.riemannianEDist_triangle (I := I) (x := G s₁) (y := x) (z := A)
    rw [hx'x, hminA, hw'mem] at htri
    rw [← ENNReal.ofReal_add hs₁pos.le ht.le] at htri
    rw [show s₁ + t = t + s₁ from by ring] at htri
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith : (0:ℝ) ≤ t + s₁)).mp htri
  have hst2 : s₁ + w' < (2/3) * l := by nlinarith [hcrit, hs₁pos, hw'le']
  have hmin3 : Manifold.riemannianEDist I (G s₁)
      (GExp (cov := cov) hmet (G s₁) (s₁ • (-velt))) = ENNReal.ofReal s₁ := by
    rw [hback]; exact hx'x
  have hmin4 : Manifold.riemannianEDist I (G s₁) (GExp (cov := cov) hmet (G s₁) (w' • ξ'))
      = ENNReal.ofReal w' := by rw [hGξ']; exact hw'mem
  have h2raw := hcomp (G s₁) hx'mem s₁ w' (-velt) ξ' hs₁pos hw'pos hst2 hnegvelt1 hξ'1
    hmin3 hmin4
  have h2 : t ≤ modelDist1 (hingeAngle (-velt) ξ') s₁ w' := by
    have h := h2raw
    simp only [HingeCompG] at h
    rw [hback, hGξ', hminA] at h
    exact (ENNReal.ofReal_le_ofReal_iff (modelDist1_nonneg _ _ _)).mp h
  -- the trigonometric step
  have hθmem : hingeAngle ξ η ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hα'mem : hingeAngle (-velt) ξ' ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hwlo : |t - s₁| ≤ w' := by
    have h1 : t ≤ s₁ + w' := by
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := x) (y := G s₁) (z := A)
      rw [hmet_xx', hw'mem, hminA] at htri
      rw [← ENNReal.ofReal_add hs₁pos.le hw'pos.le] at htri
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp htri
    have h2 : s₁ ≤ t + w' := by
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := G s₁) (y := A) (z := x)
      rw [hx'x, hw'mem, Manifold.riemannianEDist_comm (I := I) (x := A) (y := x), hminA] at htri
      rw [← ENNReal.ofReal_add hw'pos.le ht.le] at htri
      have h' := (ENNReal.ofReal_le_ofReal_iff (by linarith : (0:ℝ) ≤ w' + t)).mp htri
      linarith
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hmain := Commons.Geometry.Sphere.modelDist_hinge_step (t := t) (s₁ := s₁)
    (s₂ := s - s₁) (w := w') (θ := hingeAngle ξ η) (α' := hingeAngle (-velt) ξ')
    ht htposπ hs₁pos (by linarith) (by linarith) (by linarith)
    hw'pos (by linarith) hwlo hw'le' (by linarith) hθmem hα'mem
    (by simpa only [modelDist1] using hw'le)
    (by simpa only [modelDist1] using h2)
  -- the angle of the new hinge
  have hangle : hingeAngle ξ' velt = Real.pi - hingeAngle (-velt) ξ' := by
    rw [hingeAngle_apply, hingeAngle_apply, inner_neg_left, real_inner_comm ξ' velt,
      Real.arccos_neg]
    ring
  have hmodel : modelDist1 (hingeAngle ξ' velt) w' (s - s₁)
      ≤ modelDist1 (hingeAngle ξ η) t s := by
    have h := hmain
    rw [show s₁ + (s - s₁) = s from by ring] at h
    rwa [← hangle] at h
  have hs₁def' : s₁ = (l / 2 - t) / 3 := hs₁def
  have hGx' : GExp (cov := cov) hmet x (s₁ • η) = G s₁ := hGs₁.symm
  have hlo : |t - s₁| ≤ w' := by
    have h1 : t ≤ s₁ + w' := by
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := x) (y := G s₁) (z := A)
      rw [hminA, hmet_xx', hw'mem] at htri
      rw [← ENNReal.ofReal_add hs₁pos.le hw'pos.le] at htri
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp htri
    have h3 : s₁ ≤ t + w' := by
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := x) (y := A) (z := G s₁)
      rw [hmet_xx', hminA, Manifold.riemannianEDist_comm (I := I) (x := A) (y := G s₁),
        hw'mem] at htri
      rw [← ENNReal.ofReal_add ht.le hw'pos.le] at htri
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp htri
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  refine ⟨G s₁, s₁, ξ', velt, w', s - s₁, hs₁def', rfl, hGx', hξ'1, hvelt1, hw'pos, by linarith,
    by linarith, hx'mem, hGξ', hfwd, hw'mem, ?_, hw'le, hlo, hmet_xx', hmodel, ?_⟩
  · have h := hsub s₁ ⟨hs₁pos.le, hs₁s.le⟩ s ⟨hs.le, le_refl s⟩ hs₁s.le
    rw [hGs] at h
    exact h
  · refine lt_of_le_of_lt ?_ hviol
    exact ENNReal.ofReal_le_ofReal hmodel
/-! ## The recursion step: a smaller violating hinge -/

/-- A **violating hinge** at the point `x` with endpoints `p` and `q`: two unit-speed minimising
geodesics from `x` to `p` and to `q`, whose hinge comparison fails. -/
structure VHinge (hmet : IsMetricCompatible cov) (p q : M) where
  x : M
  tp : ℝ
  tq : ℝ
  vp : TangentSpace I x
  vq : TangentSpace I x
  hvp : ‖vp‖ = 1
  hvq : ‖vq‖ = 1
  htp : 0 < tp
  htq : 0 < tq
  hGp : GExp (cov := cov) hmet x (tp • vp) = p
  hGq : GExp (cov := cov) hmet x (tq • vq) = q
  hminp : Manifold.riemannianEDist I x p = ENNReal.ofReal tp
  hminq : Manifold.riemannianEDist I x q = ENNReal.ofReal tq
  hviol : ENNReal.ofReal (modelDist1 (hingeAngle vp vq) tp tq)
    < Manifold.riemannianEDist I p q

/-- The model distance is invariant under swapping the two sides. -/
lemma modelDist1_swap {z : M} (v w : TangentSpace I z) (a b : ℝ) :
    modelDist1 (hingeAngle w v) b a = modelDist1 (hingeAngle v w) a b := by
  rw [hingeAngle_comm w v, modelDist1_comm]

/-- The output of one step of the Key-Lemma recursion: the new violating hinge `K'`, the step size
`s₁`, the distance `w'` from the new apex to the *near* endpoint of the old hinge, and all the
identities needed for the limiting argument. -/
structure StepOut (hmet : IsMetricCompatible cov) (p q : M) (l : ℝ)
    (K : VHinge (cov := cov) hmet p q) where
  /-- the new violating hinge -/
  K' : VHinge (cov := cov) hmet p q
  /-- the step size -/
  s₁ : ℝ
  /-- the distance from the new apex to the near endpoint -/
  w' : ℝ
  hs₁ : 0 < s₁
  hcrit : min K.tp K.tq + 3 * s₁ = l / 2
  hw' : 0 < w'
  hbr : ((K.tp ≤ K.tq ∧ GExp (cov := cov) hmet K.x (s₁ • K.vq) = K'.x ∧
      K'.tq = K.tq - s₁ ∧ K'.tp = w') ∨
    (K.tq ≤ K.tp ∧ GExp (cov := cov) hmet K.x (s₁ • K.vp) = K'.x ∧
      K'.tp = K.tp - s₁ ∧ K'.tq = w'))
  hsize : K'.tp + K'.tq ≤ K.tp + K.tq
  hrel : w' = min K.tp K.tq + s₁ - ((K.tp + K.tq) - (K'.tp + K'.tq))
  hcmp : w' ≤ modelDist1 (hingeAngle K.vp K.vq) (min K.tp K.tq) s₁
  hlo : |min K.tp K.tq - s₁| ≤ w'
  hxx : Manifold.riemannianEDist I K.x K'.x = ENNReal.ofReal s₁
  hmono : modelDist1 (hingeAngle K'.vp K'.vq) K'.tp K'.tq
    ≤ modelDist1 (hingeAngle K.vp K.vq) K.tp K.tq

/-- **The recursion step of the Key Lemma.**  Given a violating hinge of size in `(l/2, l)` whose
apex lies in the ball of radius `l` around `p`, and the hinge comparison at all points of that ball
for hinges of size `< 2l/3`, one produces a new violating hinge: its apex lies on the side towards
the *farther* endpoint, at distance `s₁ = (l/2 - min tp tq)/3` from the old apex, and its size is no
larger.  The disjunction records which side has been shortened. -/
theorem VHinge.step
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {l : ℝ} (hlπ : l ≤ Real.pi)
    {p q : M} (hcomp : ∀ z : M, Manifold.riemannianEDist I p z < ENNReal.ofReal l →
      GCompHolds (cov := cov) hmet z ((2/3) * l))
    (K : VHinge (cov := cov) hmet p q)
    (hxmem : Manifold.riemannianEDist I p K.x < ENNReal.ofReal l)
    (hsizel : K.tp + K.tq < l) (hl2 : l / 2 ≤ K.tp + K.tq) :
    Nonempty (StepOut (cov := cov) hmet p q l K) := by
  rcases le_total K.tp K.tq with hle | hle
  · obtain ⟨x', s₁, ξ', u', w', s₂, hs₁eq, hs₂eq, hray, hξ'1, hu'1, hw'0, hs₂0, hsize, hmem,
      hGp', hGq', hminp', hminq', hwle, hlo, hxx, hmono, hviol'⟩ :=
      key_step1 (cov := cov) (c := p) (A := p) (B := q) (x := K.x) (t := K.tp) (s := K.tq)
        hmet htor hpinch hlπ K.hvp K.hvq K.htp K.htq hle hsizel hl2 K.hGp K.hGq K.hminp K.hminq
        hxmem (Or.inl rfl) hcomp K.hviol
    have hs₁0 : 0 < s₁ := by rw [hs₁eq]; linarith
    have hmin : min K.tp K.tq = K.tp := min_eq_left hle
    refine ⟨⟨⟨x', w', s₂, ξ', u', hξ'1, hu'1, hw'0, hs₂0, hGp', hGq', hminp', hminq', hviol'⟩,
      s₁, w', hs₁0, by rw [hmin, hs₁eq]; ring, hw'0, Or.inl ⟨hle, hray, hs₂eq, rfl⟩, hsize,
      ?_, ?_, ?_, ?_, ?_⟩⟩
    · show w' = min K.tp K.tq + s₁ - ((K.tp + K.tq) - (w' + s₂))
      rw [hmin, hs₂eq]; ring
    · rw [hmin]; exact hwle
    · rw [hmin]; exact hlo
    · show Manifold.riemannianEDist I K.x x' = ENNReal.ofReal s₁
      exact hxx
    · show modelDist1 (hingeAngle ξ' u') w' s₂ ≤ modelDist1 (hingeAngle K.vp K.vq) K.tp K.tq
      exact hmono
  · obtain ⟨x', s₁, ξ', u', w', s₂, hs₁eq, hs₂eq, hray, hξ'1, hu'1, hw'0, hs₂0, hsize, hmem,
      hGq', hGp', hminq', hminp', hwle, hlo, hxx, hmono, hviol'⟩ :=
      key_step1 (cov := cov) (c := p) (A := q) (B := p) (x := K.x) (t := K.tq) (s := K.tp)
        hmet htor hpinch hlπ K.hvq K.hvp K.htq K.htp hle (by linarith) (by linarith) K.hGq K.hGp
        K.hminq K.hminp hxmem (Or.inr rfl) hcomp
        (by rw [Manifold.riemannianEDist_comm, hingeAngle_comm K.vq K.vp,
            modelDist1_comm (hingeAngle K.vp K.vq) K.tq K.tp]; exact K.hviol)
    have hs₁0 : 0 < s₁ := by rw [hs₁eq]; linarith
    have hmin : min K.tp K.tq = K.tq := min_eq_right hle
    refine ⟨⟨⟨x', s₂, w', u', ξ', hu'1, hξ'1, hs₂0, hw'0, hGp', hGq', hminp', hminq',
      by rw [Manifold.riemannianEDist_comm, hingeAngle_comm u' ξ',
          ← modelDist1_comm (hingeAngle ξ' u') w' s₂]; exact hviol'⟩,
      s₁, w', hs₁0, by rw [hmin, hs₁eq]; ring, hw'0, Or.inr ⟨hle, hray, hs₂eq, rfl⟩,
      by linarith, ?_, ?_, ?_, ?_, ?_⟩⟩
    · show w' = min K.tp K.tq + s₁ - ((K.tp + K.tq) - (s₂ + w'))
      rw [hmin, hs₂eq]; ring
    · rw [hmin]; rw [hingeAngle_comm K.vq K.vp] at hwle; exact hwle
    · rw [hmin]; exact hlo
    · show Manifold.riemannianEDist I K.x x' = ENNReal.ofReal s₁
      exact hxx
    · show modelDist1 (hingeAngle u' ξ') s₂ w' ≤ modelDist1 (hingeAngle K.vp K.vq) K.tp K.tq
      rw [← modelDist1_swap u' ξ' s₂ w', ← modelDist1_swap K.vp K.vq K.tp K.tq]
      exact hmono

/-- **From a hinge comparison to an angle comparison.**  If the model distance for the sides
`t, s` and the angle `θ` is at least `w`, then the model angle determined by the three side lengths
`w, t, s` is at most `θ`.  This is the form in which the hinge comparison enters the recursive
analysis of the Key Lemma. -/
lemma modelAngle_le_of_le_modelDist1 {w t s θ : ℝ} (hw0 : 0 ≤ w) (hwπ : w ≤ Real.pi)
    (ht : 0 < t) (htπ : t < Real.pi) (hs : 0 < s) (hsπ : s < Real.pi)
    (hlo : |t - s| ≤ w) (hhi : w ≤ t + s) (hts : t + s ≤ Real.pi)
    (hθ : θ ∈ Set.Icc (0:ℝ) Real.pi) (h : w ≤ modelDist1 θ t s) :
    modelAngle w t s ≤ θ := by
  have hmem : modelAngle w t s ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hbase : modelDist1 (modelAngle w t s) t s ≤ modelDist1 θ t s := by
    rw [modelDist1_modelAngle hw0 hwπ ht htπ hs hsπ hlo hts hhi]
    exact h
  exact (modelDist1_le_iff ht htπ hs hsπ hmem hθ).mp hbase

/-- **Case 1 of the Key Lemma's proof.**  A violating hinge whose size is `< 2l/3` and whose apex
lies in the ball of radius `l` around `p` cannot exist, since the comparison applies to it. -/
theorem VHinge.false_of_size_lt
    (hmet : IsMetricCompatible cov)
    {l : ℝ} {p q : M}
    (hcomp : ∀ z : M, Manifold.riemannianEDist I p z < ENNReal.ofReal l →
      GCompHolds (cov := cov) hmet z ((2/3) * l))
    (K : VHinge (cov := cov) hmet p q)
    (hx : Manifold.riemannianEDist I p K.x < ENNReal.ofReal l)
    (h : K.tp + K.tq < (2/3) * l) : False := by
  have hmain := hcomp K.x hx K.tp K.tq K.vp K.vq K.htp K.htq h K.hvp K.hvq (by rw [K.hGp]; exact K.hminp) (by rw [K.hGq]; exact K.hminq)
  simp only [HingeCompG] at hmain
  rw [K.hGp, K.hGq] at hmain
  exact absurd hmain (not_le.mpr K.hviol)

end

end Submission.HingeKey
