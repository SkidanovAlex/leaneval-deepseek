import Submission.Work.OddBound.PolygonModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary energy / side-length bookkeeping for the polygon model

Small, purely algebraic consequences of the definitions in `Submission/Work/OddBound/PolygonModel.lean`,
used by the value bound `Work.OddBound.polygonValueBound`:

* `gonSideLen_sq_le_two_mul_gonEnergy` — each side bounds the total energy: `d_i² ≤ 2E/N`;
* `gonLength_nonneg`, `gonEnergy_nonneg`;
* `gonSideLen_lt_of_energy_lt` — an energy bound `< 2π²/K` together with `N > 4π²/(Kρ²)` forces
  every side to be shorter than `ρ`;
* `gonLength_lt_of_energy_lt` — the same energy bound forces the total length below `2π/√K`;
* `div_lt_of_lt_two_pi_div_sqrt` — `L/N < ρ` for `L < 2π/√K` and `N > 4π²/(Kρ²)` (the τ = 0
  identification: the sub-arcs of the geodesic have length `L/N < ρ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Length Submission.InjRadius

namespace Work.OddBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

/-- Every side length of the polygon is bounded by the energy: `d_i² ≤ 2E/N`. -/
theorem gonSideLen_sq_le_two_mul_gonEnergy (p : M) {N : ℕ} (hN : 0 < N)
    (w : Fin (N - 1) → M) (i : Fin N) :
    (gonSideLen (I := I) p w i) ^ 2 ≤ 2 * gonEnergy (I := I) p w / N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdnn : ∀ j : Fin N, (0 : ℝ) ≤ (gonSideLen (I := I) p w j) ^ 2 := fun j => sq_nonneg _
  have hle : (gonSideLen (I := I) p w i) ^ 2
      ≤ ∑ j : Fin N, (gonSideLen (I := I) p w j) ^ 2 :=
    Finset.single_le_sum (fun j _ => hdnn j) (Finset.mem_univ i)
  have hkey : 2 * gonEnergy (I := I) p w / N
      = ∑ j : Fin N, (gonSideLen (I := I) p w j) ^ 2 := by
    rw [gonEnergy, ← mul_assoc]
    field_simp
  rw [hkey]
  exact hle

/-- Every side length is nonnegative. -/
theorem gonSideLen_nonneg (p : M) {N : ℕ} (w : Fin (N - 1) → M) (i : ℕ) :
    0 ≤ gonSideLen (I := I) p w i :=
  Submission.Distance.riemannianDist_nonneg _ _

/-- The polygon length is nonnegative. -/
theorem gonLength_nonneg (p : M) {N : ℕ} (w : Fin (N - 1) → M) :
    0 ≤ gonLength (I := I) p w :=
  Finset.sum_nonneg (fun i _ => Submission.Distance.riemannianDist_nonneg _ _)

/-- The polygon energy is nonnegative. -/
theorem gonEnergy_nonneg (p : M) {N : ℕ} (w : Fin (N - 1) → M) :
    0 ≤ gonEnergy (I := I) p w := by
  rw [gonEnergy]
  have h1 : (0 : ℝ) ≤ ∑ i : Fin N, (gonSideLen (I := I) p w i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  exact mul_nonneg h2 h1

/-- `2π/√(K N) < ρ` whenever `N > 4π²/(K ρ²)`. -/
theorem two_pi_div_sqrt_mul_lt_of_big {K ρ : ℝ} (hK : 0 < K) (hρ : 0 < ρ) {N : ℕ}
    (hbig : 4 * Real.pi ^ 2 / (K * ρ ^ 2) < (N : ℝ)) :
    2 * Real.pi / Real.sqrt (K * N) < ρ := by
  have hKρ : 0 < K * ρ ^ 2 := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h4 : 0 < 4 * Real.pi ^ 2 / (K * ρ ^ 2) := by positivity
    linarith
  have hcross : 4 * Real.pi ^ 2 < (N : ℝ) * (K * ρ ^ 2) := by
    have h := (div_lt_iff₀ hKρ).mp hbig
    linarith [h]
  have hfac : (N : ℝ) * (K * ρ ^ 2) = (ρ * Real.sqrt (N * K)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ N * K)]
    ring
  rw [hfac] at hcross
  have hpos : 0 ≤ ρ * Real.sqrt (N * K) := by positivity
  have h2π : 2 * Real.pi < ρ * Real.sqrt (N * K) := by
    nlinarith [Real.pi_pos, hpos]
  have hNK : Real.sqrt (N * K) = Real.sqrt (K * N) := by rw [mul_comm]
  rw [hNK] at h2π
  have hKn : (0 : ℝ) < K * N := by positivity
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr hKn)]
  linarith [h2π]

/-- **The sides of a polygon of energy `< 2π²/K` are shorter than `ρ`**, provided
`N > 4π²/(Kρ²)`.  Indeed `d_i ≤ √(2E/N) < 2π/√(K N) < ρ`. -/
theorem gonSideLen_lt_of_energy_lt {p : M} {N : ℕ} {K ρ : ℝ} (hN : 3 ≤ N)
    (hbig : 4 * Real.pi ^ 2 / (K * ρ ^ 2) < (N : ℝ)) (hK : 0 < K) (hρ : 0 < ρ)
    (w : Fin (N - 1) → M) (hE : gonEnergy (I := I) p w < 2 * Real.pi ^ 2 / K)
    (i : Fin N) :
    gonSideLen (I := I) p w i < ρ := by
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hsq : (gonSideLen (I := I) p w i) ^ 2 < 2 * (2 * Real.pi ^ 2 / K) / N := by
    have h := gonSideLen_sq_le_two_mul_gonEnergy (I := I) p hN0 w i
    have h2E : 2 * gonEnergy (I := I) p w / N < 2 * (2 * Real.pi ^ 2 / K) / N := by
      apply div_lt_div_of_pos_right _ hNpos
      linarith
    linarith
  have htarget : 2 * (2 * Real.pi ^ 2 / K) / N = 4 * Real.pi ^ 2 / (K * N) := by
    field_simp
    ring
  rw [htarget] at hsq
  have hsq2 : 4 * Real.pi ^ 2 / (K * N) = (2 * Real.pi / Real.sqrt (K * N)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ K * N)]
    ring
  rw [hsq2] at hsq
  have hKn : (0 : ℝ) < K * N := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
    positivity
  have hsqrtpos : 0 < Real.sqrt (K * N) := Real.sqrt_pos.mpr hKn
  have hpos : 0 < 2 * Real.pi / Real.sqrt (K * N) := by positivity
  have hlt : gonSideLen (I := I) p w i < 2 * Real.pi / Real.sqrt (K * N) := by
    nlinarith [gonSideLen_nonneg (I := I) p w i, hpos,
      sq_nonneg (gonSideLen (I := I) p w i - 2 * Real.pi / Real.sqrt (K * N))]
  exact lt_trans hlt (two_pi_div_sqrt_mul_lt_of_big hK hρ hbig)

/-- **The length of a polygon of energy `< 2π²/K` is shorter than `2π/√K`** (Cauchy–Schwarz). -/
theorem gonLength_lt_of_energy_lt {p : M} {K : ℝ} (hK : 0 < K)
    {N : ℕ} (w : Fin (N - 1) → M) (hE : gonEnergy (I := I) p w < 2 * Real.pi ^ 2 / K) :
    gonLength (I := I) p w < 2 * Real.pi / Real.sqrt K := by
  have hcs := gonLength_sq_le_two_mul_gonEnergy (I := I) p w
  have hsq : (gonLength (I := I) p w) ^ 2 < (2 * Real.pi / Real.sqrt K) ^ 2 := by
    have h1 : 2 * gonEnergy (I := I) p w < 2 * (2 * Real.pi ^ 2 / K) := by linarith
    have h2 : (2 * Real.pi / Real.sqrt K) ^ 2 = 4 * Real.pi ^ 2 / K := by
      rw [div_pow, Real.sq_sqrt hK.le]
      ring
    rw [h2]
    have h3 : 2 * (2 * Real.pi ^ 2 / K) = 4 * Real.pi ^ 2 / K := by ring
    linarith
  have hsqrtpos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hpos : 0 < 2 * Real.pi / Real.sqrt K := by positivity
  nlinarith [gonLength_nonneg (I := I) p w, hpos,
    sq_nonneg (gonLength (I := I) p w - 2 * Real.pi / Real.sqrt K)]

/-- `L/N < ρ` whenever `L < 2π/√K`, `N ≥ 3` and `N > 4π²/(K ρ²)`. -/
theorem div_lt_of_lt_two_pi_div_sqrt {K ρ L : ℝ} (hK : 0 < K) (hρ : 0 < ρ) {N : ℕ}
    (hN : 3 ≤ N) (hbig : 4 * Real.pi ^ 2 / (K * ρ ^ 2) < (N : ℝ))
    (hL : L < 2 * Real.pi / Real.sqrt K) :
    L / N < ρ := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hsqrtN : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hN1
  have hsqN : (Real.sqrt (N:ℝ))^2 = (N:ℝ) := Real.sq_sqrt hN0.le
  have h1 : L / N < (2 * Real.pi / Real.sqrt K) / N := by
    apply div_lt_div_of_pos_right hL (by positivity)
  have h2 : (2 * Real.pi / Real.sqrt K) / N ≤ 2 * Real.pi / Real.sqrt (K * N) := by
    rw [Real.sqrt_mul hK.le, div_div]
    gcongr
    nlinarith [hsqrtN, hsqN, Real.sqrt_nonneg (N:ℝ)]
  have h3 : 2 * Real.pi / Real.sqrt (K * N) < ρ :=
    two_pi_div_sqrt_mul_lt_of_big hK hρ hbig
  linarith

end Work.OddBound
