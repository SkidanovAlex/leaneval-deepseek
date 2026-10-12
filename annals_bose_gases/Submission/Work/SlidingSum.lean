import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.Measure.FinFunction.cube_shell_volume_le
import Submission.PairInt
import Submission.Work.DLInfra
import Submission.Work.DLRepoint.Assembly
import Submission.Work.DLRepoint.d4Regime_family_of_max
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# Chain links 2–3 — the sliding-sum identity (eq:appsliding) and the χ_B/λ₁ geometry

STATUS: **typeset targets** (corpus `def`-Prop convention, sorry-free
compiling — the corpus's established format for not-yet-formalizable
statements, cf. `APrioriBounds`).  The bodies need the `dℓ`-infra layer
(the `u`-indexed boxes `B(u)`, cutoffs `χ_{B(u)}`, localised kernels), which
the corpus does not yet name inside its object vocabulary — that infra IS
part of the body work.

## FS content (final_v2.tex eq:BSsliding2 → eq:appsliding)
The BS localisation `H_Λ(μ) ≥ Σᵢ(b/2)Q_{Λ,i}ℓ⁻² + ∫ H_{B(u)}(μ) du` (valid
when `ε_T, s, ds⁻¹, (s⁻²+d⁻³)(sd)⁻²s^M` are below universal constants)
plus the chemical-potential lemma (`χ⋆χ((x−y)/(ℓd))`-estimate shifting
`μ ↦ 4μ` in the boundary band) give, on the restricted set
`G := {u : ‖ℓdu‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}}`,

    H_Λ(μ) ≥ (b/2)ℓ⁻²·ΣᵢQ_{Λ,i} + ∫_G H_{B(u)}(m(u)μ) du ,

`m(u) = 1` in the interior (`‖ℓdu‖_∞ ≤ ½ℓ(1+d) − 2μ^{-1/3}`), `m(u) = 4`
near the boundary; restricting to `G` keeps every box's shortest side
`λ₁(u) ≥ μ^{-1/3}` (thm:smallbox's hypothesis), and the discarded boundary
band contributes only `−Cμ²a(μa³)^{M/3}ℓ³ − Cμad^{-3}` (take `M = 8`).

## Chain role (thm:aprioriHLambda, step 2 of the on-paper chain)
Summing link 1 (`smallbox_dl_energy_bound`, the `eB`-bound at `m(u)μ`) over
`u ∈ G` with the sliding identity: the `c·(n(u)/|B(u)|−μ)²/(1+n(u)/(|B(u)|μ))`
density terms assemble into the a-priori remainder `R_Ψ := ∫_G
F(n(u)/|B(u)|)·8π(av)|B(u)| du` (`F(t) = c(t−μ)²/(1+tμ⁻¹)`), the
`−½μ²·8π(av)|B(u)|` terms telescope to `−4πμ²(av)ℓ³` (via the
`u`-normalisation `∬χ_{B(u)}² dx du = ℓ³` + `∬w_{1,B(u)} ≈ 8π(av)|B(u)|`),
the kinetic `ΣᵢQ`-parts give `(b/2ℓ²)⟨n₊⟩`, and the error terms give
`−4πμ²(av)ℓ³·CK_B³(μ(av)³)^{1/2}` — i.e. step 2's
`⟨H_Λ(μ)⟩ ≥ R_Ψ + (b/2ℓ²)⟨n₊⟩ − 4πμ²aℓ³(1 + CK_B³(μa³)^{1/2})`.

`sliding_sum_statement` below typesets the per-state corpus form of this
conclusion with the summed small-box contribution carried as an explicit
function-of-`u` parameter (`eBf : ℝ³ → ℝ`, over the good set `G`); the body
must instantiate `eBf` from link 1 and the `u`-data.  `chiB_geometric_
estimates` typesets the three geometric facts the sliding argument uses.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Sliding-sum bound, corpus per-state form (typeset target)**: the
analysis-box per-state energy satisfies

    kinWord + qLHSword ≥ (b/2ℓ²)·cnPlus + ∫_{G} eBf u du
        − 4πμ²(av)ℓ³·(1 + C·K_B³(μ(av)³)^{1/2})

where `G := {u : ‖ℓdu‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}}` (the good set) and
`eBf : ℝ³ → ℝ` is the summed small-box contribution (the body instantiates
it as link 1's `eB`-bound at `m(u)μ`; the `c·(t−μ)²/(1+tμ⁻¹)`-part is the
a-priori remainder `R_Ψ`, the kinetic part is `(b/2ℓ²)⟨n₊⟩`, the
`−½μ²`-parts telescope to the `−4πμ²(av)ℓ³` background). -/
def sliding_sum_statement {N : ℕ} {ℓ d μ b : ℝ} {v : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hd : 0 < d) (hb : 0 ≤ b)
    {K_B C : ℝ} (hKB : 0 < K_B) (hC : 0 ≤ C)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    -- the summed small-box contribution over the good set G (u ↦ bound at
    -- m(u)·μ; body obligation: instantiate from link 1 + the u-data)
    (eBf : ℝ³ → ℝ) : Prop :=
  (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ
      + (∫ u in {u : ℝ³ | ‖(ℓ * d) • u‖ ≤ (1 / 2) * ℓ * (1 + d) - μ ^ (-1 / 3 : ℝ)}, eBf u)
      - 4 * π * μ ^ 2 * (a v) * ℓ ^ 3 * (1 + C * K_B ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2))
    ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ

/-- **`χ_B` bad-band volume bound (the remaining dℓ-target)** — with (g1)
`∫_u χ_{B(u)}(x)² du = (χ(x/ℓ))²` and (g3) `∬χ_{B(u)}² dx du = ℓ³` now
PROVEN (`DLInfra.chiB_partition_u`, `DLInfra.chiB_double_integral_u_sq`),
the one open geometry fact is the bad-band (`μ ↦ 4μ`) volume bound

    ∫_{u ∈ I} ∫_x χ_{B(u)}(x)² dx du ≤ C·(μa³)^{M/3}·ℓ³,

`I := {u : ½ℓ(1+d) − 2μ^{-1/3} ≤ ‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}}`,
from the `χ`-approach (FS: `|χ_{B(u)}(x)| ≤ C(μ^{-1/3}/ℓ)^M`-type on the
band, via `λ₁(u)`-decay and `‖χ_B‖_∞ ≤ C(λ₁/(dℓ))^M`). -/
def chiB_badband_volume_bound {ℓ d μ a : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hμ : 0 < μ) {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) : Prop :=
  (∫ u in {u : ℝ³ | (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ ‖(ℓ * d) • u‖
        ∧ ‖(ℓ * d) • u‖ ≤ (1 / 2) * ℓ * (1 + d) - μ ^ (-1 / 3 : ℝ)},
        ∫ x : ℝ³, (chiB ℓ d u x) ^ 2)
      ≤ C * (μ * a ^ 3) ^ (M / 3) * ℓ ^ 3
lemma coordCube_volume {c : ℝ} (hc : 0 ≤ c) :
    (volume : Measure (Fin 3 → ℝ)) {f : Fin 3 → ℝ | ∀ i : Fin 3, |f i| ≤ c}
      = ENNReal.ofReal ((2 * c) ^ 3) := by
  have hset : {f : Fin 3 → ℝ | ∀ i : Fin 3, |f i| ≤ c}
      = Set.univ.pi (fun _ : Fin 3 => Set.Icc (-c) c) := by
    ext f
    constructor
    · intro h i hi
      exact abs_le.mp (h i)
    · intro h i
      rw [abs_le]
      exact h i (by simp)
  rw [hset]
  have hI : ∀ i : Fin 3, volume (Set.Icc (-c) c) = ENNReal.ofReal (2 * c) := by
    intro i
    rw [Real.volume_Icc]
    congr 1
    ring
  have h2c : 0 ≤ 2 * c := by positivity
  calc
    (volume (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-c) c)))
        = (∏ i : Fin 3, volume (Set.Icc (-c) c)) := by
            rw [MeasureTheory.volume_pi_pi]
    _ = (∏ _i : Fin 3, ENNReal.ofReal (2 * c)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            exact hI i
    _ = (ENNReal.ofReal (2 * c)) ^ 3 := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ENNReal.ofReal ((2 * c) ^ 3) := by
            rw [← ENNReal.ofReal_pow h2c]

/-- **`chiB_band_support_slab`**: on the `μ ↦ 4μ` bad band (some coordinate
of `(ℓd)•u` reaches `≥ ½ℓ(1+d) − 2μ^{-1/3}`), the support of
`χ_{B(u)}` lies in the face-slab of the big box: some coordinate of `x`
satisfies `ℓ/2 − 2μ^{-1/3} ≤ |x_j| ≤ ℓ/2`. -/
lemma chiB_band_support_slab {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u x : ℝ³)
    (hx : chiB ℓ d u x ≠ 0)
    (hband : ∃ j : Fin 3, (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|) :
    ∃ j : Fin 3, ℓ / 2 - 2 * μ ^ (-1 / 3 : ℝ) ≤ |x.ofLp j| ∧ |x.ofLp j| ≤ ℓ / 2 := by
  have h1 : chiScale ℓ x ≠ 0 := by
    intro h
    apply hx
    simp [chiB, h]
  have h2 : chiScale (ℓ * d) (x - (ℓ * d) • u) ≠ 0 := by
    intro h
    apply hx
    simp [chiB, h]
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hxℓ : ‖x‖ ≤ ℓ / 2 := chiScale_support_le hℓ h1
  have hxw : ‖x - (ℓ * d) • u‖ ≤ (ℓ * d) / 2 := chiScale_support_le hℓd h2
  let w : ℝ³ := (ℓ * d) • u
  have htri : ∀ j : Fin 3, |(w.ofLp j)| ≤ |x.ofLp j| + |((x - w).ofLp j)| := by
    intro j
    calc
      |(w.ofLp j)| = |x.ofLp j + ((w - x).ofLp j)| := by
          congr 1
          -- w = x + (w − x) coordinatewise
          change (w.ofLp j) = (x.ofLp j) + (w.ofLp j - x.ofLp j)
          ring
      _ ≤ |x.ofLp j| + |((w - x).ofLp j)| := abs_add_le _ _
      _ = |x.ofLp j| + |((x - w).ofLp j)| := by
          have hco : ((w - x).ofLp j) = - ((x - w).ofLp j) := by
            change (w.ofLp j - x.ofLp j) = - (x.ofLp j - w.ofLp j)
            ring
          rw [hco, abs_neg]
  rcases hband with ⟨j, hj⟩
  refine ⟨j, ?_, ?_⟩
  · have hwj : |((x - w).ofLp j)| ≤ (ℓ * d) / 2 := by
      have hb := coord_abs_le_norm (x - w) j
      exact le_trans hb hxw
    have hj' : (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |(w.ofLp j)| := by
      simpa [w] using hj
    have htri' := htri j
    nlinarith
  · have hb := coord_abs_le_norm x j
    exact le_trans hb hxℓ


-- shell set in coordinate space
def band_shellF (A δ : ℝ) : Set (Fin 3 → ℝ) :=
  {f : Fin 3 → ℝ | (∃ i : Fin 3, A - δ ≤ |f i|) ∧ (∀ i : Fin 3, |f i| ≤ A)}

-- shell set in Euclidean space
def band_shellE (A δ : ℝ) : Set ℝ³ :=
  {w : ℝ³ | (∃ i : Fin 3, A - δ ≤ |w.ofLp i|) ∧ (∀ i : Fin 3, |w.ofLp i| ≤ A)}

lemma band_shellE_eq_preimage (A δ : ℝ) :
    band_shellE A δ = (fun w : ℝ³ => w.ofLp) ⁻¹' band_shellF A δ := by
  ext w
  change ((∃ i : Fin 3, A - δ ≤ |w.ofLp i|) ∧ (∀ i : Fin 3, |w.ofLp i| ≤ A)) ↔
         ((∃ i : Fin 3, A - δ ≤ |(w.ofLp) i|) ∧ (∀ i : Fin 3, |(w.ofLp) i| ≤ A))
  exact Iff.rfl

lemma band_shellF_meas (A δ : ℝ) : MeasurableSet (band_shellF A δ) := by
  let C : Set (Fin 3 → ℝ) := {f | ∀ i : Fin 3, |f i| ≤ A}
  let B : Set (Fin 3 → ℝ) := {f | ∀ i : Fin 3, |f i| < A - δ}
  have hCpi : C = Set.univ.pi (fun _ : Fin 3 => Set.Icc (-A) A) := by
    ext f
    simp [C, Set.mem_Icc, abs_le, Pi.le_def, forall_and]
  have hBpi : B = Set.univ.pi (fun _ : Fin 3 => Set.Ioo (-(A - δ)) (A - δ)) := by
    ext f
    simp [B, Set.mem_Ioo, abs_lt, forall_and]
  have hCmeas : MeasurableSet C := by
    rw [hCpi]
    exact MeasurableSet.pi (s := (Set.univ : Set (Fin 3))) (t := fun _ : Fin 3 => Set.Icc (-A) A)
      Set.countable_univ (by intro i hi; exact measurableSet_Icc)
  have hBmeas : MeasurableSet B := by
    rw [hBpi]
    exact MeasurableSet.pi (s := (Set.univ : Set (Fin 3))) (t := fun _ : Fin 3 => Set.Ioo (-(A - δ)) (A - δ))
      Set.countable_univ (by intro i hi; exact measurableSet_Ioo)
  have hdiff : band_shellF A δ = C \ B := by
    ext f
    constructor
    · intro hf
      refine ⟨?_, ?_⟩
      · intro i
        exact hf.2 i
      · change ¬ (∀ i : Fin 3, |f i| < A - δ)
        rw [not_forall]
        rcases hf.1 with ⟨i, hi⟩
        exact ⟨i, not_lt.mpr hi⟩
    · intro hf
      have hfC : ∀ i : Fin 3, |f i| ≤ A := by
        intro i
        exact (by simpa [C] using hf.1 i)
      have hnotB : ¬ (∀ i : Fin 3, |f i| < A - δ) := by
        have h : f ∉ B := hf.2
        change ¬ (∀ i : Fin 3, |f i| < A - δ) at h
        exact h
      constructor
      · rw [not_forall] at hnotB
        rcases hnotB with ⟨i, hi⟩
        exact ⟨i, not_lt.mp hi⟩
      · exact hfC
  rw [hdiff]
  exact hCmeas.diff hBmeas

lemma band_shellE_vol_le {A δ : ℝ} (hA : 0 ≤ A) (hAδ : 0 ≤ A - δ) :
    (volume : Measure ℝ³) (band_shellE A δ) ≤ ENNReal.ofReal ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3) := by
  rw [band_shellE_eq_preimage]
  have hpre := MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    (band_shellF_meas A δ).nullMeasurableSet
  rw [hpre]
  exact Commons.Measure.FinFunction.cube_shell_volume_le (A := A) (δ := δ) hA hAδ

lemma band_smul_meas {c : ℝ} : Measurable (fun u : ℝ³ => c • u) := by
  by_cases hc : c ≠ 0
  · let φ : ℝ³ ≃ₜ ℝ³ := Homeomorph.smulOfNeZero c hc
    have hfun : (fun u : ℝ³ => c • u) = ⇑φ := by
      funext u
      simp [φ, Homeomorph.smulOfNeZero]
    simpa [hfun] using φ.measurable
  · have hc0 : c = 0 := not_not.mp hc
    subst c
    simp

lemma band_shellE_meas (A δ : ℝ) : MeasurableSet (band_shellE A δ) := by
  rw [band_shellE_eq_preimage]
  exact (PiLp.volume_preserving_ofLp (Fin 3)).measurable (band_shellF_meas A δ)

/-- **`EuclideanSpace` cube-shell measure under a `c`-dilation (PROVEN — the
generic measure layer of `(g2)`)**: with `A` a half-side and `δ` a shell
width (`0 ≤ δ ≤ A`), the set of points whose `c`-dilated coordinates lie in
the boundary shell of the `∞`-cube `[-A,A]³` has volume

    volume {u | (∃ j, A − δ ≤ |(c•u).ofLp j|) ∧ (∀ j, |(c•u).ofLp j| ≤ A)}
        ≤ c⁻³ · ( (2A)³ − (2(A−δ))³ ) .

Proof route: the `w := c•u`-side shell `band_shellE A δ` is transferred to
the function cube via the volume-preserving `ofLp`
(`PiLp.volume_preserving_ofLp` + `band_shellE_vol_le` + the commons
`cube_shell_volume_le`), then the `u ↦ c•u` dilation (`map_smul_volume3`,
the `c⁻³` Jacobian) and `ENNReal.ofReal`-arithmetic (`ofReal_mul`,
`mul_le_mul'`) close. -/
lemma band_shell_measure {c A δ : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hAδ : 0 ≤ A - δ) :
    (volume : Measure ℝ³) {u : ℝ³ | (∃ j : Fin 3, A - δ ≤ |(c • u).ofLp j|)
        ∧ (∀ j : Fin 3, |(c • u).ofLp j| ≤ A)}
      ≤ ENNReal.ofReal ((c ^ 3)⁻¹ * ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3)) := by
  let S : Set ℝ³ := {u : ℝ³ | (∃ j : Fin 3, A - δ ≤ |(c • u).ofLp j|)
        ∧ (∀ j : Fin 3, |(c • u).ofLp j| ≤ A)}
  have hS : S = (fun u : ℝ³ => c • u) ⁻¹' band_shellE A δ := by
    rfl
  -- map (smul c) volume = ofReal (c^3)⁻¹ • volume
  have hmap := map_smul_volume3 c hc
  have hSvol : (volume : Measure ℝ³) S = ENNReal.ofReal ((c ^ 3)⁻¹) * (volume : Measure ℝ³) (band_shellE A δ) := by
    rw [hS]
    rw [← Measure.map_apply (f := fun u : ℝ³ => c • u) (band_smul_meas (c := c)) (band_shellE_meas A δ)]
    rw [hmap]
    simp
  let X : ℝ := (2 * A) ^ 3 - (2 * (A - δ)) ^ 3
  have hcn : 0 ≤ (c ^ 3)⁻¹ := by positivity
  have hX : 0 ≤ X := by
    dsimp [X]
    have hle : 2 * (A - δ) ≤ 2 * A := by nlinarith
    have hpos : 0 ≤ 2 * (A - δ) := by nlinarith
    have hA2 : 0 ≤ 2 * A := by nlinarith
    have hp := pow_le_pow_left₀ hpos hle 3
    nlinarith
  have hsh := band_shellE_vol_le (A := A) (δ := δ) hA hAδ
  have hmul_le : ENNReal.ofReal ((c ^ 3)⁻¹) * (volume : Measure ℝ³) (band_shellE A δ)
      ≤ ENNReal.ofReal ((c ^ 3)⁻¹) * ENNReal.ofReal X := by
    exact mul_le_mul' le_rfl hsh
  change (volume : Measure ℝ³) S ≤ ENNReal.ofReal ((c ^ 3)⁻¹ * ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3))
  calc
    (volume : Measure ℝ³) S = ENNReal.ofReal ((c ^ 3)⁻¹) * (volume : Measure ℝ³) (band_shellE A δ) := hSvol
    _ ≤ ENNReal.ofReal ((c ^ 3)⁻¹) * ENNReal.ofReal X := hmul_le
    _ = ENNReal.ofReal ((c ^ 3)⁻¹ * X) := by rw [← ENNReal.ofReal_mul hcn]
    _ = ENNReal.ofReal ((c ^ 3)⁻¹ * ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3)) := by rfl

/-- **Band `du`-measure bound (PROVEN — the integration/measure layer of
`(g2)`)**: with `A := ½ℓ(1+d)` (outer half-side in the `w := (ℓd)•u`
coordinates) and `δ := 2μ^{-1/3}` (band width), the `u`-set whose relevant
face-coordinate of `w` lies in the boundary slab satisfies

    volume {u | (∃ j, A − δ ≤ |((ℓd)•u).ofLp j|) ∧ (∀ j, |((ℓd)•u).ofLp j| ≤ A)}
        ≤ (ℓd)⁻³ · ( (2A)³ − (2(A−δ))³ ) .

This is `band_shell_measure` specialised to the dilation `c := ℓd`. -/
lemma band_u_measure_le {ℓ d A δ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hAδ : 0 ≤ A - δ) :
    (volume : Measure ℝ³) {u : ℝ³ | (∃ j : Fin 3, A - δ ≤ |((ℓ * d) • u).ofLp j|)
        ∧ (∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ A)}
      ≤ ENNReal.ofReal (((ℓ * d) ^ 3)⁻¹ * ((2 * A) ^ 3 - (2 * (A - δ)) ^ 3)) := by
  simpa using (band_shell_measure (c := ℓ * d) (mul_pos hℓ hd) hA hδ hAδ)

/-- **Volume of the union of the face-slabs of `acube ℓ` of width `δ`**
(over `EuclideanSpace` coordinates; the `x`-side counterpart of
`band_shell_measure` with `c := 1`, `A := ℓ/2`): the slab set of the big box
`{x : |x_j| ≤ ℓ/2}` where some coordinate reaches `≥ ℓ/2 − δ` has volume
`≤ (2·(ℓ/2))³ − (2·(ℓ/2−δ))³`. -/
lemma band_x_slab_measure_le {ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ) (hℓδ : 0 ≤ ℓ / 2 - δ) :
    (volume : Measure ℝ³) {x : ℝ³ | (∃ j : Fin 3, ℓ / 2 - δ ≤ |x.ofLp j|)
        ∧ (∀ j : Fin 3, |x.ofLp j| ≤ ℓ / 2)}
      ≤ ENNReal.ofReal ((2 * (ℓ / 2)) ^ 3 - (2 * (ℓ / 2 - δ)) ^ 3) := by
  simpa using (band_shell_measure (c := (1 : ℝ)) (by norm_num) (A := ℓ / 2) (δ := δ)
    (by positivity) hδ hℓδ)

-- ============ band-shape matching: Euclidean-norm band vs coordinatewise shell ============

lemma norm_sq_eq_sum_sq (w : ℝ³) : ‖w‖ ^ 2 = ∑ j : Fin 3, |w.ofLp j| ^ 2 := by
  simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) w)

/-- some coordinate has `|w_j|² ≥ ‖w‖²/3` (finite-dimensional norm fact). -/
lemma exists_coord_sq_ge_norm_sq_div_three (w : ℝ³) :
    ∃ j : Fin 3, ‖w‖ ^ 2 / 3 ≤ |w.ofLp j| ^ 2 := by
  by_cases hw0 : ‖w‖ = 0
  · refine ⟨0, ?_⟩
    rw [hw0]
    simpa using (sq_nonneg (w.ofLp 0) : 0 ≤ (w.ofLp 0) ^ 2)
  · by_contra h
    push_neg at h
    have hsq : ‖w‖ ^ 2 = ∑ j : Fin 3, |w.ofLp j| ^ 2 := norm_sq_eq_sum_sq w
    have hlt : (∑ j : Fin 3, |w.ofLp j| ^ 2) < 3 * (‖w‖ ^ 2 / 3) := by
      calc
        (∑ j : Fin 3, |w.ofLp j| ^ 2) < ∑ _j : Fin 3, (‖w‖ ^ 2 / 3) := by
            refine Finset.sum_lt_sum ?_ ?_
            · intro j hj
              exact le_of_lt (h j)
            · refine ⟨0, by simp, h 0⟩
        _ = 3 * (‖w‖ ^ 2 / 3) := by simp
    have h3 : 3 * (‖w‖ ^ 2 / 3) = ‖w‖ ^ 2 := by ring
    nlinarith [hsq, hlt, h3]

/-- some coordinate has `|w_j| ≥ ‖w‖/√3`. -/
lemma exists_coord_abs_ge_norm_div_sqrt3 (w : ℝ³) :
    ∃ j : Fin 3, ‖w‖ / Real.sqrt 3 ≤ |w.ofLp j| := by
  rcases exists_coord_sq_ge_norm_sq_div_three w with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ha0 : 0 ≤ ‖w‖ / Real.sqrt 3 := div_nonneg (norm_nonneg w) (le_of_lt hsqrt)
  have hb0 : 0 ≤ |w.ofLp j| := abs_nonneg _
  have hconv : (‖w‖ / Real.sqrt 3) ^ 2 ≤ |w.ofLp j| ^ 2 := by
    simpa [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using hj
  have habs := sq_le_sq.mp hconv
  simpa [abs_of_nonneg ha0, abs_of_nonneg hb0] using habs

/-- **band-shape matching (Euclidean band ⊆ coordinate shell)**: if
`A − δ ≤ ‖w‖ ≤ A` then some coordinate reaches `|w_j| ≥ (A−δ)/√3` and all
coordinates are `≤ A`.  This is the finite-dimensional fact that lets any
Euclidean-norm band be measured by the coordinatewise shell
`band_u_measure_le` (at the `√3`-scaled width). -/
lemma eucl_band_subset_coord_shell {ℓ d A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hAδ : 0 ≤ A - δ) :
    {u : ℝ³ | A - δ ≤ ‖(ℓ * d) • u‖ ∧ ‖(ℓ * d) • u‖ ≤ A}
      ⊆ {u : ℝ³ | (∃ j : Fin 3, (A - δ) / Real.sqrt 3 ≤ |((ℓ * d) • u).ofLp j|)
          ∧ (∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ A)} := by
  intro u hu
  rcases hu with ⟨hlow, hup⟩
  constructor
  · rcases exists_coord_abs_ge_norm_div_sqrt3 ((ℓ * d) • u) with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    calc
      (A - δ) / Real.sqrt 3 ≤ ‖(ℓ * d) • u‖ / Real.sqrt 3 :=
          div_le_div_of_nonneg_right hlow (le_of_lt hsqrt)
      _ ≤ |((ℓ * d) • u).ofLp j| := hj
  · intro j
    exact le_trans (coord_abs_le_norm ((ℓ * d) • u) j) hup

/-- **band-shape matching (coordinate box ⊆ Euclidean ball)**: the
coordinatewise `‖·‖_∞`-box `{|w_j| ≤ A for all j}` lies in the Euclidean
ball of radius `√3·A`. -/
lemma coord_box_subset_eucl_ball {A : ℝ} (hA : 0 ≤ A) :
    {w : ℝ³ | ∀ j : Fin 3, |w.ofLp j| ≤ A} ⊆ {w : ℝ³ | ‖w‖ ≤ Real.sqrt 3 * A} := by
  intro w hw
  have hsq : ‖w‖ ^ 2 = ∑ j : Fin 3, |w.ofLp j| ^ 2 := norm_sq_eq_sum_sq w
  have hsum : (∑ j : Fin 3, |w.ofLp j| ^ 2) ≤ 3 * A ^ 2 := by
    calc
      (∑ j : Fin 3, |w.ofLp j| ^ 2) ≤ ∑ _j : Fin 3, A ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact pow_le_pow_left₀ (abs_nonneg _) (hw j) 2
      _ = 3 * A ^ 2 := by simp
  have hsqle : ‖w‖ ^ 2 ≤ 3 * A ^ 2 := by
    rw [hsq]
    exact hsum
  have hb0 : 0 ≤ Real.sqrt 3 * A := mul_nonneg (le_of_lt (Real.sqrt_pos.mpr (by norm_num))) hA
  have hconv : ‖w‖ ^ 2 ≤ (Real.sqrt 3 * A) ^ 2 := by
    simpa [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using hsqle
  have habs := sq_le_sq.mp hconv
  simpa [abs_of_nonneg (norm_nonneg w), abs_of_nonneg hb0] using habs

end BoseGases

end Submission
