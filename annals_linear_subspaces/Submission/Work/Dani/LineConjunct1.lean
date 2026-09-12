import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.Commons.Lattice.Minkowski.convex_body
import Submission.Commons.Measure.EuclideanSpace.volume_orthogonal_box
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.GeometryOfNumbers.ExteriorCoordinates
import Submission.GeometryOfNumbers.FlowLatticeCovolume
import Submission.Bridge.Challenge
import Submission.Work.ModelStar.ModelStarHeight
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.GeometryOfNumbers.RationalSpan
import Submission.DirichletTarget
import Submission.Work.Interface.Theorem9ToConjunct1
import Submission.Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real
import Submission.Work.Dani.StarPairAssembly

/-!
# Dirichlet's principle for `k = 1`: `β₁(x) ≥ d/(d − ℓ)` for every `ℓ`-plane `x`

The `k = 1` case of de Saxcé's Theorem 1 — the classical "Dirichlet principle" for the
approximation of an `ℓ`-plane by rational lines.

**Method** (see `Submission/Work/ROADMAP.md`, session 142).  One cannot reach the *cone
condition* `‖π_{xᗮ}v‖ ≤ η‖π_x v‖` by Minkowski's theorem: the cone body is not convex for
`η < 1`.  Instead one produces the **critical relation**

    ‖π_{xᗮ}b‖^{d−ℓ} · ‖b‖^{ℓ} ≤ C₀^{d−ℓ}      (b ∈ ℤᵈ \ {0}),

which *is* Minkowski-accessible: apply the convex-body theorem to the **symmetric convex** body
`K_B = {v : ‖π_{xᗮ}v‖ ≤ C₀B^{−ℓ}} ∩ B(0, B^{d−ℓ})` (a cylinder ∩ ball).  Its volume is bounded
below by the orthogonal box `{‖π_x v‖ ≤ B^{d−ℓ}/2} ∩ {‖π_{xᗮ}v‖ ≤ C₀B^{−ℓ}}`, whose volume is
`2^{−ℓ}C₀^{d−ℓ}ω_ℓω_{d−ℓ}` — *independent of `B`*.  With `C₀^{d−ℓ} ω_ℓ ω_{d−ℓ} 2^{−ℓ} = 2^{d+1}`
the theorem yields `b ≠ 0` in `K_B`, and `‖π_{xᗮ}b‖·‖b‖^{ℓ/(d−ℓ)} ≤ C₀` follows.

The critical relation gives `sin(b)·H(b)^{d/(d−ℓ)} ≤ C₀`, and the heights are **unbounded**
(otherwise the finitely many admissible `b` would have `‖π_{xᗮ}b‖ ≥ c > 0`, contradicting
`‖π_{xᗮ}b_B‖ ≤ C₀B^{−ℓ} → 0`).  Evaluating at a tall `b` gives, for every `β < d/(d−ℓ)` and
every `c > 0`, a rational line `v` with `dist(v,x) < c·H(v)^{−β}`, i.e. `β₁(x) ≥ d/(d−ℓ)`.

Module `Submission.Work.Dani.LineConjunct1`, namespace `Submission.LineConjunct1`.
-/

noncomputable section

open LinearSubspaces ENNReal Real Module exteriorPower InnerProductGeometry MeasureTheory Metric
open scoped LinearAlgebra.Projectivization ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.LineConjunct1

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- The volume of the unit ball of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def uBall (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

lemma uBall_pos {n : ℕ} (hn : 0 < n) : 0 < uBall n := by
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI := hne
  rw [uBall]
  exact ENNReal.toReal_pos
    (ne_of_gt (Metric.measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin n)) (by norm_num)))
    (MeasureTheory.measure_closedBall_lt_top (μ := volume)).ne

/-- The Minkowski constant of the `k = 1` argument. -/
noncomputable def lineConst (l d : ℕ) : ℝ :=
  (((2 : ℝ) ^ (d + l + 1)) / (uBall l * uBall (d - l))) ^ (1 / (((d - l : ℕ)) : ℝ))

lemma lineConst_pos {l : ℕ} (hl0 : 0 < l) (hld : l < d) : 0 < lineConst l d := by
  have h1 : 0 < uBall l := uBall_pos hl0
  have h2 : 0 < uBall (d - l) := uBall_pos (Nat.sub_pos_of_lt hld)
  rw [lineConst]
  have hnum : (0 : ℝ) < (2 : ℝ) ^ (d + l + 1) := pow_pos (by norm_num) _
  have hden : (0 : ℝ) < uBall l * uBall (d - l) :=
    mul_pos (uBall_pos hl0) (uBall_pos (by omega))
  exact Real.rpow_pos_of_pos (div_pos hnum hden) _

/-- The defining property of `lineConst`: its `(d−ℓ)`-th power is the chosen constant. -/
lemma lineConst_pow {l : ℕ} (hl0 : 0 < l) (hld : l < d) :
    lineConst l d ^ (d - l) = ((2 : ℝ) ^ (d + l + 1)) / (uBall l * uBall (d - l)) := by
  have hpos : 0 < d - l := Nat.sub_pos_of_lt hld
  have hne : (((d - l : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  set x : ℝ := ((2 : ℝ) ^ (d + l + 1)) / (uBall l * uBall (d - l)) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (by positivity)
      (mul_nonneg (uBall_pos hl0).le (uBall_pos (by omega)).le)
  rw [lineConst, ← hx, ← Real.rpow_natCast,
    ← Real.rpow_mul hx0 (1 / (((d - l : ℕ)) : ℝ)) (((d - l : ℕ)) : ℝ),
    one_div_mul_cancel hne, Real.rpow_one, hx]

/-- The volume identity used in the Minkowski step. -/
private lemma volume_algebra {l : ℕ} (hl0 : 0 < l) (hld : l < d) {B : ℝ} (hB : 0 < B) :
    (B ^ (d - l) / 2) ^ l * (lineConst l d * (B ^ l)⁻¹) ^ (d - l) * uBall l * uBall (d - l)
      = (2 : ℝ) ^ (d + 1) := by
  have hkey : ((B ^ l)⁻¹) ^ (d - l) = ((B ^ (d - l)) ^ l)⁻¹ := by
    rw [inv_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hC : lineConst l d ^ (d - l) = (2 : ℝ) ^ (d + l + 1) / (uBall l * uBall (d - l)) :=
    lineConst_pow hl0 hld
  have h2exp : (2 : ℝ) ^ (d + l + 1) = (2 : ℝ) ^ (d + 1) * (2 : ℝ) ^ l := by
    rw [← pow_add]; congr 1; omega
  set z : ℝ := (B ^ (d - l)) ^ l with hzdef
  set U : ℝ := uBall l * uBall (d - l) with hUdef
  have hz : z ≠ 0 := by rw [hzdef]; positivity
  have hU : U ≠ 0 := by
    rw [hUdef]
    exact mul_ne_zero (ne_of_gt (uBall_pos hl0)) (ne_of_gt (uBall_pos (by omega)))
  rw [div_pow, mul_pow, hkey, hC, h2exp]
  rw [← hzdef]
  field_simp
  ring

/-- **The Minkowski step.**  For every scale `B ≥ 1` with `2·lineConst ≤ B^d`, the body
`{v : ‖π_{xᗮ}v‖ ≤ lineConst·B^{−ℓ}} ∩ B(0, B^{d−ℓ})` contains a nonzero lattice point. -/
theorem exists_cone_point {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    (W : Submodule ℝ ℝᵈ) (hW : Module.finrank ℝ W = l)
    {B : ℝ} (hB1 : 1 ≤ B) (hB2 : 2 * lineConst l d ≤ B ^ d) :
    ∃ b : ℝᵈ, b ≠ 0 ∧ b ∈ ℤᵈ ∧
      ‖((Wᗮ).starProjection b : ℝᵈ)‖ ≤ lineConst l d * (B ^ l)⁻¹ ∧
      ‖b‖ ≤ B ^ (d - l) := by
  classical
  have hC0 : 0 < lineConst l d := lineConst_pos hl0 hld
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  set δ : ℝ := lineConst l d * (B ^ l)⁻¹ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set A : ℝ := B ^ (d - l) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hδA : δ ≤ A / 2 := by
    have hBd : B ^ (d - l) * B ^ l = B ^ d := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hld)]
    rw [hδdef, hAdef, ← div_eq_mul_inv, div_le_iff₀ (by positivity : (0 : ℝ) < B ^ l),
      div_mul_eq_mul_div, hBd, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [hB2]
  let E : Set ℝᵈ := {v : ℝᵈ | ‖(Wᗮ).starProjection v‖ ≤ δ} ∩ Metric.closedBall 0 A
  -- convexity of the cylinder
  have hconv1 : Convex ℝ {v : ℝᵈ | ‖(Wᗮ).starProjection v‖ ≤ δ} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    have hcoe : ((Wᗮ).starProjection (a • x + b • y) : ℝᵈ)
        = a • ((Wᗮ).starProjection x : ℝᵈ) + b • ((Wᗮ).starProjection y : ℝᵈ) := by
      simp [map_add, map_smul]
    rw [hcoe]
    calc ‖a • ((Wᗮ).starProjection x : ℝᵈ) + b • ((Wᗮ).starProjection y : ℝᵈ)‖
        ≤ ‖a • ((Wᗮ).starProjection x : ℝᵈ)‖ + ‖b • ((Wᗮ).starProjection y : ℝᵈ)‖ :=
          norm_add_le _ _
      _ = a * ‖(Wᗮ).starProjection x‖ + b * ‖(Wᗮ).starProjection y‖ := by
          simp only [norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * δ + b * δ := by gcongr
      _ = δ := by rw [← add_mul, hab, one_mul]
  have hconvE : Convex ℝ E := hconv1.inter (convex_closedBall (0 : ℝᵈ) A)
  have hsymE : ∀ x ∈ E, -x ∈ E := by
    intro v hv
    obtain ⟨h1, h2⟩ := (show v ∈ {u : ℝᵈ | ‖(Wᗮ).starProjection u‖ ≤ δ} ∧
      v ∈ Metric.closedBall 0 A from hv)
    refine ⟨?_, ?_⟩
    · show ‖(Wᗮ).starProjection (-v)‖ ≤ δ
      have hneg : ((Wᗮ).starProjection (-v) : ℝᵈ) = -((Wᗮ).starProjection v : ℝᵈ) := by
        rw [map_neg]
      rw [hneg, norm_neg]
      exact h1
    · rw [Metric.mem_closedBall, dist_zero_right, norm_neg]
      simpa [dist_zero_right] using (Metric.mem_closedBall.mp h2)
  have hclosedE : IsClosed E :=
    (isClosed_le (Continuous.norm (Wᗮ).starProjection.continuous) continuous_const).inter
      Metric.isClosed_closedBall
  have hbddE : Bornology.IsBounded E :=
    (Metric.isBounded_closedBall (x := (0 : ℝᵈ)) (r := A)).subset Set.inter_subset_right
  have hintE : (interior E).Nonempty := by
    set r : ℝ := min A δ / 2 with hrdef
    have hrpos : 0 < r := by rw [hrdef]; exact div_pos (lt_min hApos hδpos) (by norm_num)
    have hrA : r ≤ A := by rw [hrdef]; linarith [min_le_left A δ]
    have hrδ : r ≤ δ := by rw [hrdef]; linarith [min_le_right A δ]
    have hball : Metric.ball (0 : ℝᵈ) r ⊆ E := by
      intro v hv
      rw [Metric.mem_ball, dist_zero_right] at hv
      refine ⟨?_, Metric.mem_closedBall.mpr ?_⟩
      · calc ‖(Wᗮ).starProjection v‖ ≤ ‖v‖ := (Wᗮ).norm_starProjection_apply_le v
          _ ≤ r := le_of_lt hv
          _ ≤ δ := hrδ
      · rw [dist_zero_right]
        exact le_of_lt (lt_of_lt_of_le hv hrA)
    exact ⟨0, interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hrpos)⟩
  -- volume: the orthogonal box inside `E`
  have hvolQ : (volume {v : ℝᵈ | ‖W.starProjection v‖ ≤ A / 2 ∧
      ‖(Wᗮ).starProjection v‖ ≤ δ}).toReal = (A / 2) ^ l * δ ^ (d - l) * uBall l * uBall (d - l) := by
    simpa [uBall] using Commons.Measure.EuclideanSpace.volume_orthogonal_box (le_of_lt hld) W hW
      (A := A / 2) (δ := δ) (by positivity) hδpos
  have hvolQeq : (volume {v : ℝᵈ | ‖W.starProjection v‖ ≤ A / 2 ∧
      ‖(Wᗮ).starProjection v‖ ≤ δ}).toReal = (2 : ℝ) ^ (d + 1) := by
    rw [hvolQ, hδdef, hAdef]
    exact volume_algebra hl0 hld hB0
  have hQsub : {v : ℝᵈ | ‖W.starProjection v‖ ≤ A / 2 ∧ ‖(Wᗮ).starProjection v‖ ≤ δ} ⊆ E := by
    intro v hv
    obtain ⟨h1, h2⟩ := hv
    refine ⟨h2, Metric.mem_closedBall.mpr ?_⟩
    rw [dist_zero_right]
    have hpy : ‖v‖ ^ 2 = ‖W.starProjection v‖ ^ 2 + ‖(Wᗮ).starProjection v‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection v W
    have h3 : ‖W.starProjection v‖ ^ 2 ≤ (A / 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h4 : ‖(Wᗮ).starProjection v‖ ^ 2 ≤ (A / 2) ^ 2 := by
      have h5 : δ ^ 2 ≤ (A / 2) ^ 2 := pow_le_pow_left₀ (le_of_lt hδpos) hδA 2
      have h6 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      linarith
    have h7 : ‖v‖ ^ 2 ≤ (A / 2) ^ 2 + (A / 2) ^ 2 := by rw [hpy]; linarith
    have h8 : ‖v‖ ^ 2 ≤ A ^ 2 := by nlinarith [h7, hApos]
    exact (sq_le_sq₀ (norm_nonneg v) hApos.le).mp h8
  have hvolK : (volume {v : ℝᵈ | ‖W.starProjection v‖ ≤ A / 2 ∧
      ‖(Wᗮ).starProjection v‖ ≤ δ}).toReal ≤ (volume E).toReal := by
    apply ENNReal.toReal_mono
    · exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (isCompact_closedBall 0 A).measure_lt_top)
    · exact measure_mono hQsub
  have hlt : (2 : ℝ) ^ d * ZLattice.covolume (intPoints (d := d))
      (volume : MeasureTheory.Measure ℝᵈ) < (volume E).toReal := by
    rw [Submission.FlowLattice.covol_intPoints d, mul_one]
    have h2 : (2 : ℝ) ^ d < (2 : ℝ) ^ (d + 1) := by
      rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) d]
    linarith [hvolK, hvolQeq]
  obtain ⟨v, hvne, hvK⟩ := Commons.Lattice.Minkowski.convex_body
    (n := d) (L := intPoints (d := d)) hconvE hsymE hclosedE hbddE hintE hlt
  obtain ⟨hk1, hk2⟩ := (show (v : ℝᵈ) ∈ {u : ℝᵈ | ‖(Wᗮ).starProjection u‖ ≤ δ} ∧
    (v : ℝᵈ) ∈ Metric.closedBall 0 A from hvK)
  refine ⟨(v : ℝᵈ), fun h => hvne (Subtype.ext h), v.2, hk1, ?_⟩
  have hk2' : ‖(v : ℝᵈ)‖ ≤ A := by
    have h := Metric.mem_closedBall.mp hk2
    rwa [dist_zero_right] at h
  simpa [hAdef] using hk2'



/-- **The critical relation.** There is a nonzero integer vector `b` with

    ‖π_{xᗮ} b‖^{d−ℓ} · ‖b‖^ℓ ≤ lineConst^{d−ℓ} ,

i.e. `b` lies on the critical curve `dist · H^{d/(d−ℓ)} = O(1)` of the Dirichlet problem
(here `x` is the `ℓ`-plane `W`).  Obtained from `exists_cone_point` by multiplying the two
bounds `‖π_{xᗮ}b‖ ≤ lineConst·B^{−ℓ}` and `‖b‖ ≤ B^{d−ℓ}` (whose powers cancel exactly). -/
theorem line_critical_relation {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    (W : Submodule ℝ ℝᵈ) (hW : Module.finrank ℝ W = l) :
    ∃ b : ℝᵈ, b ≠ 0 ∧ b ∈ ℤᵈ ∧
      ‖((Wᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l ≤ (lineConst l d) ^ (d - l) := by
  have hC0 : 0 < lineConst l d := lineConst_pos hl0 hld
  set B : ℝ := max 1 (2 * lineConst l d + 1) with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBge : 2 * lineConst l d + 1 ≤ B := le_max_right _ _
  have hBd : 1 ≤ d := by omega
  have hB2 : 2 * lineConst l d ≤ B ^ d := by
    calc 2 * lineConst l d ≤ 2 * lineConst l d + 1 := by linarith
      _ ≤ B := hBge
      _ = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ d := pow_le_pow_right₀ hB1 hBd
  obtain ⟨b, hbne, hbmem, hb1, hb2⟩ := exists_cone_point hl0 hld W hW hB1 hB2
  refine ⟨b, hbne, hbmem, ?_⟩
  have hkey : ((B ^ l)⁻¹) ^ (d - l) = ((B ^ (d - l)) ^ l)⁻¹ := by
    rw [inv_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring
  calc ‖((Wᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l
      ≤ (lineConst l d * (B ^ l)⁻¹) ^ (d - l) * (B ^ (d - l)) ^ l := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact pow_le_pow_left₀ (norm_nonneg _) hb1 (d - l)
        · exact pow_le_pow_left₀ (norm_nonneg _) hb2 l
    _ = (lineConst l d) ^ (d - l) := by
        rw [mul_pow, hkey, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]


/-- **Unbounded heights.**  If `W` contains no nonzero integer vector, then for every `M` there is
`b ∈ ℤᵈ \ {0}` satisfying the critical relation with `‖b‖ ≥ M`.  (If `W ∩ ℤᵈ ≠ {0}` the statement
fails for large `M` — that is exactly the "`x` contains a rational line" case of the challenge,
handled separately by taking that line, for which the distance is `0`.)

Proof: if every `b` with the critical relation had `‖b‖ < M`, then the finitely many such `b`
(of norm `≤ max M 1`) would all have `‖π_{xᗮ}b‖ ≥ c₀ > 0` (each is nonzero, and `π_{xᗮ}b = 0`
would put `b ∈ W`), contradicting the Minkowski point of scale `B` for `B` so large that
`lineConst·B^{−ℓ} < c₀`. -/
theorem exists_line_vector_ge_of_disjoint {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    (W : Submodule ℝ ℝᵈ) (hW : Module.finrank ℝ W = l)
    (hW0 : ∀ b : ℝᵈ, b ∈ ℤᵈ → b ∈ W → b = 0) (M : ℝ) :
    ∃ b : ℝᵈ, b ≠ 0 ∧ b ∈ ℤᵈ ∧
      ‖((Wᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l ≤ (lineConst l d) ^ (d - l) ∧
      M ≤ ‖b‖ := by
  classical
  have hC0 : 0 < lineConst l d := lineConst_pos hl0 hld
  by_contra hcon
  have hcon' : ∀ b : ℝᵈ, b ≠ 0 → b ∈ ℤᵈ →
      ‖((Wᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l ≤ (lineConst l d) ^ (d - l) →
      ‖b‖ < M := by
    intro b h1 h2 h3
    by_contra h4
    exact hcon ⟨b, h1, h2, h3, not_lt.mp h4⟩
  -- the finite set of admissible vectors of norm `≤ max M 1`
  set S : Set ℝᵈ := {b : ℝᵈ | b ∈ ℤᵈ ∧ b ≠ 0 ∧ ‖b‖ ≤ max M 1} with hSdef
  have hSfin : S.Finite := by
    have hfin : (Metric.closedBall (0 : ℝᵈ) (max M 1) ∩ (intPoints (d := d))).Finite :=
      ZSpan.setFinite_inter (b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
        (Metric.isBounded_closedBall (x := (0 : ℝᵈ)) (r := max M 1))
    refine hfin.subset ?_
    rintro b ⟨hbint, hbne, hbn⟩
    refine ⟨?_, hbint⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbn
  have hSpos : ∀ b ∈ S, 0 < ‖((Wᗮ).starProjection b : ℝᵈ)‖ := by
    rintro b ⟨hbint, hbne, _⟩
    refine norm_pos_iff.mpr ?_
    intro h0
    have h1 : b - W.starProjection b = 0 := by simpa using h0
    have hbW : b ∈ W := (Submodule.starProjection_eq_self_iff).mp (sub_eq_zero.mp h1).symm
    exact hbne (hW0 b hbint hbW)
  -- the positive gap
  obtain ⟨c₀, hc₀pos, hc₀le⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ b ∈ S, c₀ ≤ ‖((Wᗮ).starProjection b : ℝᵈ)‖ := by
    by_cases hSne : S.Nonempty
    · refine ⟨hSfin.toFinset.inf' (hSfin.toFinset_nonempty.mpr hSne)
        (fun b => ‖((Wᗮ).starProjection b : ℝᵈ)‖), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro b hb
        exact hSpos b (hSfin.mem_toFinset.mp hb)
      · intro b hb
        exact Finset.inf'_le _ (hSfin.mem_toFinset.mpr hb)
    · refine ⟨1, one_pos, fun b hb => absurd ⟨b, hb⟩ hSne⟩
  -- choose the scale
  obtain ⟨B, hB1, hB2, hB3⟩ : ∃ B : ℝ, 1 ≤ B ∧ 2 * lineConst l d ≤ B ^ d ∧
      lineConst l d * (B ^ l)⁻¹ < c₀ := by
    obtain ⟨n, hn⟩ := exists_nat_gt (lineConst l d / c₀)
    have hn' : lineConst l d / c₀ < (n : ℝ) := hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (div_pos hC0 hc₀pos) hn'
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have hnne : n ≠ 0 := by
        rintro rfl
        simp at hnpos
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hnne)
    set B : ℝ := max (max 1 (2 * lineConst l d + 1)) (n : ℝ) with hBdef
    have hB1' : 1 ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
    have hBge : 2 * lineConst l d + 1 ≤ B :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hnB : (n : ℝ) ≤ B := le_max_right _ _
    refine ⟨B, hB1', ?_, ?_⟩
    · have hd1 : 1 ≤ d := Nat.succ_le_of_lt (lt_trans hl0 hld)
      calc 2 * lineConst l d ≤ 2 * lineConst l d + 1 := by linarith
        _ ≤ B := hBge
        _ = B ^ 1 := (pow_one B).symm
        _ ≤ B ^ d := pow_le_pow_right₀ hB1' hd1
    · have hlt : lineConst l d < c₀ * (n : ℝ) := by
        rw [div_lt_iff₀ hc₀pos] at hn'
        linarith
      have hpow1 : (n : ℝ) ≤ (n : ℝ) ^ l := by
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ l := pow_le_pow_right₀ hn1 hl0
      have hpow2 : (n : ℝ) ^ l ≤ B ^ l := pow_le_pow_left₀ (le_of_lt hnpos) hnB l
      have hfin : lineConst l d < c₀ * B ^ l := by
        calc lineConst l d < c₀ * (n : ℝ) := hlt
          _ ≤ c₀ * (n : ℝ) ^ l := by
              exact mul_le_mul_of_nonneg_left hpow1 (le_of_lt hc₀pos)
          _ ≤ c₀ * B ^ l := mul_le_mul_of_nonneg_left hpow2 (le_of_lt hc₀pos)
      rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity : (0 : ℝ) < B ^ l)]
      exact hfin
  obtain ⟨b, hbne, hbint, hbpi, hbnorm⟩ := exists_cone_point hl0 hld W hW hB1 hB2
  have hrel : ‖((Wᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l ≤ (lineConst l d) ^ (d - l) := by
    have hkey : ((B ^ l)⁻¹) ^ (d - l) = ((B ^ (d - l)) ^ l)⁻¹ := by
      rw [inv_pow, ← pow_mul, ← pow_mul]
      congr 1
      ring
    calc ‖((Wᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l
        ≤ (lineConst l d * (B ^ l)⁻¹) ^ (d - l) * (B ^ (d - l)) ^ l := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · exact pow_le_pow_left₀ (norm_nonneg _) hbpi (d - l)
          · exact pow_le_pow_left₀ (norm_nonneg _) hbnorm l
      _ = (lineConst l d) ^ (d - l) := by
          rw [mul_pow, hkey, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hMlt : ‖b‖ < M := hcon' b hbne hbint hrel
  have hbS : b ∈ S := ⟨hbint, hbne, le_trans (le_of_lt hMlt) (le_max_left M 1)⟩
  have hle := hc₀le b hbS
  linarith [hbpi, hB3, hle]


/-- **Unbounded heights, unconditionally.**  For every `M` there is `b ∈ ℤᵈ \ {0}` satisfying the
critical relation with `‖b‖ ≥ M`.

If `W` contains a nonzero integer vector `b₀` we take a large integer multiple of it: it stays in
`W` (hence `π_{xᗮ}· = 0`, so the critical relation holds trivially) and stays in `ℤᵈ` because
`ℤᵈ` is a `ℤ`-submodule, while its norm is `k‖b₀‖` and can be made as large as we like.
Otherwise we apply `exists_line_vector_ge_of_disjoint`. -/
theorem exists_line_vector_ge {l : ℕ} (hl0 : 0 < l) (hld : l < d)
    (W : Submodule ℝ ℝᵈ) (hW : Module.finrank ℝ W = l) (M : ℝ) :
    ∃ b : ℝᵈ, b ≠ 0 ∧ b ∈ ℤᵈ ∧
      ‖((Wᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l ≤ (lineConst l d) ^ (d - l) ∧
      M ≤ ‖b‖ := by
  by_cases hA : ∃ b₀ : ℝᵈ, b₀ ∈ ℤᵈ ∧ b₀ ∈ W ∧ b₀ ≠ 0
  · obtain ⟨b₀, hmem, hWmem, hne⟩ := hA
    have hb₀pos : 0 < ‖b₀‖ := norm_pos_iff.mpr hne
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, 1 ≤ k ∧ M ≤ (k : ℝ) * ‖b₀‖ := by
      obtain ⟨k, hk⟩ := exists_nat_ge (max 1 (M / ‖b₀‖))
      refine ⟨k, ?_, ?_⟩
      · exact_mod_cast (le_trans (le_max_left _ _) hk)
      · have h3 : M / ‖b₀‖ ≤ (k : ℝ) := le_trans (le_max_right _ _) hk
        rw [div_le_iff₀ hb₀pos] at h3
        linarith
    have hk0 : k ≠ 0 := by omega
    have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
    have hcast : (k : ℝ) • b₀ = (k : ℤ) • b₀ := by
      rw [← Int.cast_smul_eq_zsmul ℝ (k : ℤ) b₀]
      norm_num
    have hbint : (k : ℝ) • b₀ ∈ ℤᵈ := by
      rw [hcast]
      exact Submodule.smul_mem (intPoints (d := d)) (k : ℤ) hmem
    have hbW : ((k : ℝ) • b₀ : ℝᵈ) ∈ W := Submodule.smul_mem W (k : ℝ) hWmem
    refine ⟨(k : ℝ) • b₀, smul_ne_zero (by positivity : (k : ℝ) ≠ 0) hne, hbint, ?_, ?_⟩
    · have hproj0 : (Wᗮ).starProjection ((k : ℝ) • b₀) = 0 := by
        refine (Submodule.starProjection_apply_eq_zero_iff (Wᗮ)).mpr ?_
        rw [Submodule.orthogonal_orthogonal]
        exact hbW
      have hnorm0 : ‖((Wᗮ).starProjection ((k : ℝ) • b₀) : ℝᵈ)‖ = 0 := by
        rw [hproj0]
        simp
      rw [hnorm0]
      simp only [zero_pow (Nat.sub_pos_of_lt hld).ne', zero_mul]
      exact pow_nonneg (lineConst_pos hl0 hld).le _
    · have hnorm : ‖(k : ℝ) • b₀‖ = (k : ℝ) * ‖b₀‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
      rw [hnorm]
      exact hk2
  · have hW0 : ∀ b : ℝᵈ, b ∈ ℤᵈ → b ∈ W → b = 0 := by
      intro b h1 h2
      by_contra h3
      exact hA ⟨b, h1, h2, h3⟩
    exact exists_line_vector_ge_of_disjoint hl0 hld W hW hW0 M


/-- **The residual of a line.**  For `b ≠ 0` the residual `δ(ℝb, x)` — the supremum of the
residuals of the unit vectors of the line — is at most `‖π_{xᗮ}b‖ / ‖b‖` (in fact it equals it,
but only the upper bound is needed for the distance half of the challenge). -/
lemma planeResidual_line_le {b : ℝᵈ} (hb : b ≠ 0) (x : Submodule ℝ ℝᵈ) :
    Submission.ProjectionDistance.planeResidual (ℝ ∙ b) x ≤
      ‖((xᗮ).starProjection b : ℝᵈ)‖ / ‖b‖ := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hne : ‖b‖ ≠ 0 := ne_of_gt hbpos
  rw [Submission.ProjectionDistance.planeResidual]
  refine csSup_le ?hne' ?hle
  · refine ⟨‖((xᗮ).starProjection b : ℝᵈ)‖ / ‖b‖,
      (‖b‖)⁻¹ • b, Submodule.mem_span_singleton.mpr ⟨(‖b‖)⁻¹, rfl⟩, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hne]
    · have h1 : ((‖b‖)⁻¹ • b - (x.orthogonalProjectionOnto ((‖b‖)⁻¹ • b) : ℝᵈ))
          = (((xᗮ).starProjection ((‖b‖)⁻¹ • b)) : ℝᵈ) := by
        rw [← Submodule.starProjection_apply x ((‖b‖)⁻¹ • b)]
        simp only [map_smul]
        rw [← smul_sub]
        simp
      rw [h1, map_smul, norm_smul, Real.norm_of_nonneg (by positivity), div_eq_mul_inv]
      ring
  · rintro r ⟨u, hu, hu1, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hcu : ‖c‖ * ‖b‖ = 1 := by simpa [norm_smul] using hu1
    have hc : ‖c‖ = (‖b‖)⁻¹ := by
      have h := congrArg (fun t : ℝ => t * (‖b‖)⁻¹) hcu
      rw [mul_assoc, mul_inv_cancel₀ hne, mul_one, one_mul] at h
      exact h
    have h1 : (c • b - (x.orthogonalProjectionOnto (c • b) : ℝᵈ))
        = (((xᗮ).starProjection (c • b)) : ℝᵈ) := by
      rw [← Submodule.starProjection_apply x (c • b)]
      simp only [map_smul]
      rw [← smul_sub]
      simp
    rw [h1, map_smul, norm_smul, hc, div_eq_mul_inv]
    exact le_of_eq (mul_comm _ _)


lemma norm_iMulti_one (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (v : Fin 1 → E) :
    ‖exteriorPower.ιMulti ℝ 1 v‖ = ‖v 0‖ := by
  have hsq : ‖exteriorPower.ιMulti ℝ 1 v‖ ^ 2 = ‖v 0‖ ^ 2 := by
    calc ‖exteriorPower.ιMulti ℝ 1 v‖ ^ 2
        = inner ℝ (exteriorPower.ιMulti ℝ 1 v) (exteriorPower.ιMulti ℝ 1 v) := by
          rw [inner_self_eq_norm_sq_to_K (𝕜 := ℝ)]
          simp
      _ = (Matrix.gram ℝ v).det := by rw [exteriorPower.inner_ιMulti_self]
      _ = ‖v 0‖ ^ 2 := by
          rw [Matrix.det_fin_one, Matrix.gram_apply, inner_self_eq_norm_sq_to_K]
          norm_num
  have h1 : 0 ≤ ‖exteriorPower.ιMulti ℝ 1 v‖ := norm_nonneg _
  have h2 : 0 ≤ ‖v 0‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

lemma span_range_one_eq (b : ℝᵈ) :
    Submodule.span ℝ (Set.range (fun _ : Fin 1 => b)) = ℝ ∙ b := by
  ext x
  simp [Submodule.mem_span_singleton]

theorem conjunct1_one (hd : 2 ≤ d) (l : ℕ) (hl0 : 0 < l) (hld : l < d) :
    ∀ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l →
      diophantineExponent 1 x ≥ (d : ℝ≥0∞) / (1 * (d - l)) := by
  have hdl0 : 0 < d - l := Nat.sub_pos_of_lt hld
  have hdlR : (0 : ℝ) < (((d - l : ℕ)) : ℝ) := by exact_mod_cast hdl0
  have hdlcast : (((d - l : ℕ)) : ℝ) = (d : ℝ) - (l : ℝ) := Nat.cast_sub (le_of_lt hld)
  have hdir : ∀ (x : Submodule ℝ ℝᵈ) (hx : finrank ℝ x = l) (β : ℝ) (hβ : 0 < β),
      β < (d : ℝ) / ((((1 : ℕ) : ℝ)) * ((d : ℝ) - (l : ℝ))) → ∀ c : ℝ, 0 < c →
        ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v, finrank ℝ v = 1 ∧
          distSubspaces v x < c * height v hv ^ (-β) := by
    intro x hx β hβ hβD c hc
    set C : ℝ := lineConst l d with hCdef
    have hCpos : 0 < C := by rw [hCdef]; exact lineConst_pos hl0 hld
    have hCnn : 0 ≤ C := le_of_lt hCpos
    set dlt : ℝ := (d : ℝ) / (((d - l : ℕ)) : ℝ) with hdltdef
    have hβD' : β < dlt := by
      rw [hdltdef, hdlcast]
      simp only [Nat.cast_one, one_mul] at hβD
      exact hβD
    set e : ℝ := dlt - β with hedef
    have hepos : 0 < e := by rw [hedef]; linarith
    set M : ℝ := (C / c + 1) ^ (1 / e) with hMdef
    have hMpos : 0 < M := by rw [hMdef]; exact Real.rpow_pos_of_pos (by positivity) _
    have hMpow : M ^ e = C / c + 1 := by
      rw [hMdef, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ C / c + 1),
        one_div_mul_cancel (ne_of_gt hepos), Real.rpow_one]
    obtain ⟨b, hbne, hbint, hbrel, hbM⟩ :=
        Submission.LineConjunct1.exists_line_vector_ge hl0 hld x hx M
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hbne
    have hLI : LinearIndependent ℝ (fun _ : Fin 1 => b) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h1 : g 0 • b = 0 := by simpa using hg
      rcases smul_eq_zero.mp h1 with h2 | h2
      · fin_cases i; exact h2
      · exact absurd h2 hbne
    set v : Submodule ℝ ℝᵈ := Submodule.span ℝ (Set.range (fun _ : Fin 1 => b)) with hvdef
    have hfinv : Module.finrank ℝ v = 1 := by
      rw [hvdef]; exact PlaneFinrank.finrank_span_range (fun _ : Fin 1 => b) hLI
    have hvrat : IsRational v := by
      rw [hvdef]
      exact RationalSpan.isRational_span_of_mem_intPoints (fun _ : Fin 1 => b) (fun i => hbint)
    have hvne : v ≠ ⊥ := by
      intro h; rw [h] at hfinv; simp at hfinv
    have hxne : x ≠ ⊥ := by
      intro h; rw [h] at hx; simp at hx; omega
    refine ⟨v, hvrat, hfinv, ?_⟩
    have hHle : height v hvrat ≤ ‖b‖ := by
      have hH := ModelStarHeight.height_le_span_intPoints (d := d) (V := v) hvrat
        (m := fun _ : Fin 1 => b) hvdef.symm (fun i => hbint) hLI
      rw [hfinv] at hH
      simpa [norm_iMulti_one] using hH
    have hdist : distSubspaces v x ≤ ‖((xᗮ).starProjection b : ℝᵈ)‖ / ‖b‖ := by
      have h1 : Module.finrank ℝ v ≤ Module.finrank ℝ x := by
        rw [hfinv, hx]; exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt hl0)
      refine le_trans (Bridge.distSubspaces_le_planeResidual_of_le v x h1 hvne hxne) ?_
      rw [hvdef, span_range_one_eq b]
      exact planeResidual_line_le hbne x
    -- the critical relation, in the form `δ^(d-l) * H'^l ≤ C^(d-l)`
    have hbrel' : ‖((xᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l ≤ C ^ (d - l) := by
      rw [hCdef]; exact hbrel
    -- step A: raise `δ · H'^(l/(d-l))` to the `(d-l)`-th power
    have hroot : (‖((xᗮ).starProjection b : ℝᵈ)‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ))) ^ (d - l)
        ≤ C ^ (d - l) := by
      have h1 : (‖((xᗮ).starProjection b : ℝᵈ)‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ))) ^ (d - l)
          = ‖((xᗮ).starProjection b : ℝᵈ)‖ ^ (d - l) * ‖b‖ ^ l := by
        rw [mul_pow, ← Real.rpow_natCast (‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ))) (d - l),
          ← Real.rpow_mul (le_of_lt hbpos) ((l : ℝ) / (((d - l : ℕ)) : ℝ)) (((d - l : ℕ)) : ℝ),
          div_mul_cancel₀ _ (ne_of_gt hdlR), Real.rpow_natCast]
      rw [h1]
      exact hbrel'
    -- step B: take the `(d-l)`-th root
    have hstep1 : ‖((xᗮ).starProjection b : ℝᵈ)‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ)) ≤ C :=
      le_of_pow_le_pow_left₀ (by omega : d - l ≠ 0) hCnn hroot
    -- step C: `a * ‖b‖^dlt ≤ δ * ‖b‖^(l/(d-l)) ≤ C`
    have hX : (d : ℝ) - (l : ℝ) ≠ 0 := by rw [← hdlcast]; exact ne_of_gt hdlR
    have hdlt1 : dlt = 1 + (l : ℝ) / (((d - l : ℕ)) : ℝ) := by
      rw [hdltdef, hdlcast, div_eq_iff hX]
      field_simp
      ring
    have hC2 : distSubspaces v x * ‖b‖ ^ dlt ≤ C := by
      have h1 : ‖b‖ ^ dlt = ‖b‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ)) := by
        rw [hdlt1, Real.rpow_add hbpos 1 _, Real.rpow_one]
      rw [h1]
      have h2 : distSubspaces v x * (‖b‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ)))
          ≤ (‖((xᗮ).starProjection b : ℝᵈ)‖ / ‖b‖) * (‖b‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ))) :=
        mul_le_mul_of_nonneg_right hdist (by positivity)
      have h3 : (‖((xᗮ).starProjection b : ℝᵈ)‖ / ‖b‖) * (‖b‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ)))
          = ‖((xᗮ).starProjection b : ℝᵈ)‖ * ‖b‖ ^ ((l : ℝ) / (((d - l : ℕ)) : ℝ)) := by
        field_simp
      linarith [h2, h3, hstep1]
    -- step D: `a * ‖b‖^β ≤ C * ‖b‖^(-e)`
    have hC3 : distSubspaces v x * ‖b‖ ^ β ≤ C * ‖b‖ ^ (-e) := by
      have h1 : distSubspaces v x * ‖b‖ ^ β
          = (distSubspaces v x * ‖b‖ ^ dlt) * ‖b‖ ^ (-e) := by
        rw [mul_assoc, ← Real.rpow_add hbpos dlt (-e)]
        congr 1
        rw [hedef]
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg (le_of_lt hbpos) _)
    -- step E: `C * ‖b‖^(-e) < c`
    have hCe : C * ‖b‖ ^ (-e) < c := by
      rw [Real.rpow_neg (le_of_lt hbpos), ← div_eq_mul_inv, div_lt_iff₀ (Real.rpow_pos_of_pos hbpos e)]
      have h3 : M ^ e ≤ ‖b‖ ^ e := Real.rpow_le_rpow (le_of_lt hMpos) hbM (le_of_lt hepos)
      have h4 : c * M ^ e ≤ c * ‖b‖ ^ e := mul_le_mul_of_nonneg_left h3 (le_of_lt hc)
      have h5 : c * M ^ e = C + c := by
        rw [hMpow]
        field_simp
      linarith [h4, h5]
    -- conclude
    have hlt1 : distSubspaces v x * ‖b‖ ^ β < c := lt_of_le_of_lt hC3 hCe
    have hlt2 : distSubspaces v x < c * ‖b‖ ^ (-β) := by
      rw [Real.rpow_neg (le_of_lt hbpos) β, ← div_eq_mul_inv,
        lt_div_iff₀ (Real.rpow_pos_of_pos hbpos β)]
      exact hlt1
    have hHpos : 0 < height v hvrat := Submission.height_pos v hvrat
    have hmono : ‖b‖ ^ (-β) ≤ (height v hvrat) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hHpos hHle (by linarith : -β ≤ 0)
    exact lt_of_lt_of_le hlt2 (mul_le_mul_of_nonneg_left hmono (le_of_lt hc))
  simpa using (Submission.lower_bound_of_dirichlet (d := d) hd (k := 1) hl0 hld (le_refl 1) hl0 hdir)


/-- **The §3 production interface (Prop 5 output), pinned.**  This is the *only* remaining
conjunct-1 input for `1 ≤ k ≤ ℓ`: the cone-family production.  Concretely, for every `ℓ`-plane `W`
there is a uniform constant `C` such that for every `0 < ε ≤ 1` there are `k` independent integer
vectors whose **whole span** lies in the cone of aperture `ε` around `W` and whose wedge norm is at
most `C·ε^{−k(d−ℓ)/d}`.

This wrapper shows that *everything downstream of it is already assembled*: it is consumed by
`Submission.DaniStarPair.conjunct1_of_cone_family` (which routes through
`Submission.DaniStarPair.star_pair_of_cone_family` and `conjunct1_of_dirichlet_bound_perX`), so
proving the hypothesis proves the first conjunct of the challenge.  The `k = 1` instance of the
hypothesis is proved in this file (`conjunct1_one`, via `exists_cone_point` +
`line_critical_relation` + `exists_line_vector_ge`); the general case is the Grayson–HN/Prop-5
production. -/
theorem conjunct1_of_production {l k : ℕ} (hd : 2 ≤ d) (hl0 : 0 < l) (hld : l < d)
    (hk1 : 1 ≤ k) (hkl : k ≤ l)
    (hcf : ∀ (W : Submodule ℝ ℝᵈ), Module.finrank ℝ W = l →
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ b : Fin k → ℝᵈ,
        (∀ i, b i ∈ ℤᵈ) ∧ LinearIndependent ℝ b ∧
        (∀ v ∈ Submodule.span ℝ (Set.range b),
          ‖v - (W.starProjection v : ℝᵈ)‖ ≤ ε * ‖(W.starProjection v : ℝᵈ)‖) ∧
        ‖exteriorPower.ιMulti ℝ k b‖ ≤
          C * ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ))) :
    ∀ (x : Submodule ℝ ℝᵈ), Module.finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) :=
  Submission.DaniStarPair.conjunct1_of_cone_family hd hl0 hld hk1 hkl hcf


/-- **The pinned production is satisfiable**: at the model plane `W = modelX ℓ` the cone family is
supplied by the first `k` standard basis vectors — their span *is* contained in `W`, so the cone
condition holds with zero residual, and their wedge is orthonormal so has norm `1`.  This is a
genuine instance of the hypothesis of `conjunct1_of_production` (in particular the `k = 2` base
case), and it shows the pinned statement is not vacuous. -/
theorem cone_family_modelX {l k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) (hld : l < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ b : Fin k → ℝᵈ,
      (∀ i, b i ∈ ℤᵈ) ∧ LinearIndependent ℝ b ∧
      (∀ v ∈ Submodule.span ℝ (Set.range b),
        ‖v - ((Submission.WedgeBlocks.modelX (d := d) l).starProjection v : ℝᵈ)‖ ≤
          ε * ‖((Submission.WedgeBlocks.modelX (d := d) l).starProjection v : ℝᵈ)‖) ∧
      ‖exteriorPower.ιMulti ℝ k b‖ ≤
        C * ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ)) := by
  refine ⟨1, one_pos, fun ε hε hε1 => ?_⟩
  let e : Fin k → Fin d := fun i =>
    ⟨i.val, lt_of_lt_of_le (lt_of_lt_of_le i.isLt hkl) (le_of_lt hld)⟩
  have heinj : Function.Injective e := by
    intro i j hij
    have h1 : (e i).val = (e j).val := congrArg Fin.val hij
    have h2 : i.val = j.val := by simpa [e] using h1
    exact Fin.ext h2
  have hON : Orthonormal ℝ (fun i : Fin k => (Submission.ExteriorCoordinates.B d) (e i)) :=
    (Submission.ExteriorCoordinates.B d).orthonormal.comp e heinj
  refine ⟨fun i => (Submission.ExteriorCoordinates.B d) (e i), ?_, hON.linearIndependent, ?_, ?_⟩
  · intro i
    exact Submodule.subset_span (Set.mem_range_self (e i))
  · intro v hv
    have hvX : v ∈ Submission.WedgeBlocks.modelX (d := d) l := by
      refine Submodule.span_le.mpr ?_ hv
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨e i, lt_of_lt_of_le i.isLt hkl, rfl⟩
    have hproj : (Submission.WedgeBlocks.modelX (d := d) l).starProjection v = v :=
      (Submodule.starProjection_eq_self_iff).mpr hvX
    rw [hproj, sub_self, norm_zero]
    exact mul_nonneg (le_of_lt hε) (norm_nonneg _)
  · rw [Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal _ hON hk1, one_mul]
    have hexp : (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ)) ≤ 0 := by
      have h1 : 0 ≤ (k : ℝ) * (((d - l : ℕ)) : ℝ) := by positivity
      have h2 : 0 < (d : ℝ) := by
        have h3 : 0 < d := by omega
        exact_mod_cast h3
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
    have := Real.rpow_le_rpow_of_nonpos hε hε1 hexp
    rwa [Real.one_rpow] at this


/-- **The §3 analytic obligation at a plane `W`** (the "irrational case" of the cone-family
production): for every `ε ∈ (0,1]` there are `k` integer vectors, `ℤ`-independent, whose *whole*
span lies in the cone of aperture `ε` around `W`, with wedge norm at most `C·ε^{−k(d−ℓ)/d}`.

This is the exact structure that the Grayson–HN/Prop-5 construction must produce.  Note the
`ℤ`-independence (not `ℝ`): that is what the lattice-side construction naturally yields, and
`cone_family_of_obligation` converts it to the pinned production statement. -/
def ConeObligation (l k : ℕ) (W : Submodule ℝ ℝᵈ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ b : Fin k → ℝᵈ,
    (∀ i, b i ∈ ℤᵈ) ∧ LinearIndependent ℤ b ∧
    (∀ v ∈ Submodule.span ℝ (Set.range b),
      ‖v - (W.starProjection v : ℝᵈ)‖ ≤ ε * ‖(W.starProjection v : ℝᵈ)‖) ∧
    ‖exteriorPower.ιMulti ℝ k b‖ ≤
      C * ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ))

/-- **The structural half of the production.**  `ConeObligation` (which only asks for
`ℤ`-independence of the integer family) implies the pinned production statement, whose witness
must be `ℝ`-independent.  The conversion is the standard "integer coordinates ⟹ real
independence" transfer (`Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real`);
everything else is unchanged. -/
theorem cone_family_of_obligation {l k : ℕ} {W : Submodule ℝ ℝᵈ} (h : ConeObligation l k W) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ b : Fin k → ℝᵈ,
      (∀ i, b i ∈ ℤᵈ) ∧ LinearIndependent ℝ b ∧
      (∀ v ∈ Submodule.span ℝ (Set.range b),
        ‖v - (W.starProjection v : ℝᵈ)‖ ≤ ε * ‖(W.starProjection v : ℝᵈ)‖) ∧
      ‖exteriorPower.ιMulti ℝ k b‖ ≤
        C * ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ)) := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨b, hmem, hliZ, hcone, hbond⟩ := h ε hε hε1
  exact ⟨b, hmem,
    Commons.Analysis.InnerProductSpace.intCoords_linearIndependent_real hmem hliZ, hcone, hbond⟩




/-- **The general-`W` production, stated as the target.**  If the §3 analytic obligation
(`ConeObligation`) holds at every `ℓ`-plane, then the first conjunct of the challenge holds.  This
is the precise statement of what the Grayson–HN/Prop-5 layer must deliver: nothing else is
missing. -/
theorem conjunct1_of_obligations {l k : ℕ} (hd : 2 ≤ d) (hl0 : 0 < l) (hld : l < d)
    (hk1 : 1 ≤ k) (hkl : k ≤ l)
    (h : ∀ W : Submodule ℝ ℝᵈ, Module.finrank ℝ W = l → ConeObligation (d := d) l k W) :
    ∀ x : Submodule ℝ ℝᵈ, Module.finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) :=
  conjunct1_of_production hd hl0 hld hk1 hkl
    (fun W hW => cone_family_of_obligation (h W hW))


/-- **First instance of the §3 obligation for a general plane**: if `W` contains the span of a
`ℤ`-independent integer family `c`, then `ConeObligation l k W` holds.  The cone condition is then
exact — every vector of `span ℝ (range c)` already lies in `W`, so the residual is `0` — and the
constant is `‖ιMulti ℝ k c‖ + 1`, valid for every `ε ≤ 1` because `ε^{negative} ≥ 1`.  This drops
the model-plane restriction of `cone_family_modelX`; the genuinely open case is an *irrational*
`W`, for which no such integer family exists. -/
theorem coneObligation_of_rational_subplane {l k : ℕ} {W : Submodule ℝ ℝᵈ}
    (hW : ∃ c : Fin k → ℝᵈ, (∀ i, c i ∈ ℤᵈ) ∧ LinearIndependent ℤ c ∧
      Submodule.span ℝ (Set.range c) ≤ W) :
    ConeObligation (d := d) l k W := by
  obtain ⟨c, hmem, hliZ, hle⟩ := hW
  refine ⟨‖exteriorPower.ιMulti ℝ k c‖ + 1, by positivity, fun ε hε hε1 => ?_⟩
  refine ⟨c, hmem, hliZ, ?_, ?_⟩
  · intro v hv
    have hproj : W.starProjection v = v :=
      (Submodule.starProjection_eq_self_iff).mpr (hle hv)
    rw [hproj, sub_self, norm_zero]
    exact mul_nonneg (le_of_lt hε) (norm_nonneg _)
  · have hexp : (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ)) ≤ 0 := by
      have hk : 0 ≤ (k : ℝ) * (((d - l : ℕ)) : ℝ) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h1 : (1 : ℝ) ≤ ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ)) := by
      have := Real.rpow_le_rpow_of_nonpos hε hε1 hexp
      rwa [Real.one_rpow] at this
    calc ‖exteriorPower.ιMulti ℝ k c‖ ≤ ‖exteriorPower.ιMulti ℝ k c‖ + 1 := by linarith
      _ = (‖exteriorPower.ιMulti ℝ k c‖ + 1) * 1 := by ring
      _ ≤ (‖exteriorPower.ιMulti ℝ k c‖ + 1) *
          ε ^ (-((k : ℝ) * (((d - l : ℕ)) : ℝ)) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)


/-- **The `k = 2` extraction obligation** (the first rung of the `k ≥ 2` case, addendum 11).

For an `ℓ`-plane `W` with **no** rational `2`-plane inside it, find independent integer vectors
`b₁, b₂` whose *wedge* is controlled in the block decomposition of `⋀²ℝᵈ` relative to `L = modelX ℓ`
— i.e. the `k = 2` analogue of the critical relation `‖π_{Wᗮ}b‖^{d−ℓ}·‖b‖^ℓ ≤ C^{d−ℓ}` of
`line_critical_relation`, with `blockElem (b₁ ∧ b₂) 0` playing the role of `π_W b` and
`blockElem (b₁ ∧ b₂) 1` the role of `π_{Wᗮ}b`.

This is *not* obtainable by applying Minkowski to a product cylinder: that body can contain a single
lattice point, so ℝ-independence of the two vectors is not free, and the wedge of the found point
need not be decomposable.  The correct tool is the successive-minima refinement already in the
commons (`Commons.Lattice.Minkowski.wedge_norm_ge_prod_successiveMinimum`,
`Commons.Lattice.Minkowski.minkowski_second_upper`): the pair `(b₁, b₂)` should be read off the two
shortest successive-minima vectors of the flow lattice, whose wedge is controlled by
Minkowski-2-upper on their span.  Stated here as a named `Prop` so that the extraction can be
targeted directly; the downstream consumers are already on disk (see addendum 11). -/
def WedgeExtraction (l : ℕ) (_W : Submodule ℝ ℝᵈ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, ∃ b : Fin 2 → ℝᵈ,
    (∀ i, b i ∈ ℤᵈ) ∧ LinearIndependent ℝ b ∧
    M ≤ ‖exteriorPower.ιMulti ℝ 2 b‖ ∧
    ‖Submission.ExteriorCoordinates.blockElem (d := d) (k := 2) (ℓ := l)
        (exteriorPower.ιMulti ℝ 2 b) 1‖ ^ (d - l) *
        ‖exteriorPower.ιMulti ℝ 2 b‖ ^ l ≤ C ^ (d - l)

end Submission.LineConjunct1

end
