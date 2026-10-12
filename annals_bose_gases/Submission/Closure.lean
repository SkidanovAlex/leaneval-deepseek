import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Excess
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — the closure scaffold: per-box facts about the grand-canonical
affine values at the canonical density.

For a box of side `L` at nominal density `ρ` write

    ρ_L := ⌊ρL³⌋/L³        (the actual particle density),
    h_L(μ) := gcDensity(μ,ρmax,L) + μ·ρ_L      (μ ≥ 0),

the grand-canonical affine values evaluated at the canonical density.  This
module proves the elementary facts needed to pass from the vanishing canonical
excess (Ingredient 1, `gcExcess_witness_aux` in `Submission.Excess`) to the
upper side `gcSup_upper`: the density `ρ_L` converges to `ρ`; `h_L` is
concave in `μ ≥ 0`, converges pointwise to `g(μ) := p(μ) + μρ`, is
Lipschitz-controlled at `μ = 0` (uniformly in `L`), and decays linearly in
`μ` once `μ` is large (uniformly in `L`), so that the supremum of `h_L` over
`μ ≥ 0` is eventually attained on a compact range `[0,M]`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The actual particle density `⌊ρL³⌋/L³` in a box of side `L` at nominal
density `ρ`. -/
noncomputable def rhoL (ρ L : ℝ) : ℝ := (Nat.floor (ρ * L ^ (3:ℕ)) : ℝ) / L ^ (3:ℕ)

/-- The grand-canonical affine value at density `ρ_L` and chemical potential
`μ`: `gcDensity(μ,ρmax,L) + μ·ρ_L`. -/
noncomputable def hL (v : ℝ³ → ℝ) (ρmax ρ μ L : ℝ) : ℝ :=
  gcDensity v μ ρmax L + μ * rhoL ρ L

/-- The pointwise limit of `h_L` in the thermodynamic limit: `g(μ) := p(μ)+μρ`. -/
noncomputable def gVal (v : ℝ³ → ℝ) (ρmax ρ μ : ℝ) : ℝ :=
  gcPressure v ρmax μ + μ * ρ

/-- The canonical density dominates every grand-canonical affine value, so the
supremum over `μ ≥ 0` is finite. -/
noncomputable def canonSup (v : ℝ³ → ℝ) (ρmax ρ L : ℝ) : ℝ :=
  sSup (gcCanonSet v ρmax ρ L)

/-! ## The density `ρ_L` -/

/-- `0 ≤ ρ_L ≤ ρ` for `0 ≤ ρ`, `0 < L`. -/
lemma rhoL_nonneg_le {ρ L : ℝ} (hρ : 0 ≤ ρ) (hLpos : 0 < L) :
    0 ≤ rhoL ρ L ∧ rhoL ρ L ≤ ρ := by
  have hL3pos : 0 < L ^ (3:ℕ) := pow_pos hLpos 3
  have hL3nonneg : 0 ≤ L ^ (3:ℕ) := le_of_lt hL3pos
  have hmul : 0 ≤ ρ * L ^ (3:ℕ) := mul_nonneg hρ hL3nonneg
  unfold rhoL
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hL3nonneg
  · rw [div_le_iff₀ hL3pos]
    exact Nat.floor_le hmul

/-- `ρ − 1/L³ ≤ ρ_L` (the floor loses less than one particle). -/
lemma rhoL_lower {ρ L : ℝ} (hρ : 0 ≤ ρ) (hLpos : 0 < L) :
    ρ - 1 / L ^ (3:ℕ) ≤ rhoL ρ L := by
  have hL3pos : 0 < L ^ (3:ℕ) := pow_pos hLpos 3
  have hL3ne : L ^ (3:ℕ) ≠ 0 := ne_of_gt hL3pos
  unfold rhoL
  rw [le_div_iff₀ hL3pos]
  have hrew : (ρ - 1 / L ^ (3:ℕ)) * L ^ (3:ℕ) = ρ * L ^ (3:ℕ) - 1 := by
    field_simp [hL3ne]
  rw [hrew]
  have hlt := Nat.lt_floor_add_one (ρ * L ^ (3:ℕ))
  nlinarith

/-- `ρ_L → ρ` as `L → ∞` (squeeze between `ρ − 1/L³` and `ρ`; use
`Filter.Tendsto.squeeze'` and `tendsto_const_div_cube_nhds_zero`). -/
lemma tendsto_rhoL {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (fun L : ℝ => rhoL ρ L) atTop (𝓝 ρ) := by
  have hdiv : Tendsto (fun L : ℝ => 1 / L ^ (3:ℕ)) atTop (𝓝 0) :=
    tendsto_const_div_cube_nhds_zero (μ := 1) (by norm_num)
  have hf : Tendsto (fun L : ℝ => ρ - 1 / L ^ (3:ℕ)) atTop (𝓝 ρ) := by
    simpa using (tendsto_const_nhds (x := ρ)).sub hdiv
  have hlo : ∀ᶠ L : ℝ in atTop, ρ - 1 / L ^ (3:ℕ) ≤ rhoL ρ L := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    exact rhoL_lower hρ (by linarith)
  have hhi : ∀ᶠ L : ℝ in atTop, rhoL ρ L ≤ ρ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    exact (rhoL_nonneg_le hρ (by linarith)).2
  exact Filter.Tendsto.squeeze' hf (tendsto_const_nhds (x := ρ)) hlo hhi

/-! ## Pointwise facts about `h_L` -/

/-- `gcDensity(0,ρmax,L) ≥ 0`: the grand-canonical optimum at `μ = 0` is
nonnegative (`N = 0` gives value `0` and all energies are nonnegative). -/
lemma gcDensity_zero_nonneg {v : ℝ³ → ℝ} {ρmax L : ℝ} (hρmax : 0 ≤ ρmax)
    (hLpos : 0 < L) (hv : 0 ≤ v) : 0 ≤ gcDensity v 0 ρmax L := by
  simpa [gcDensity] using (gcBox_density_ge (v := v) (μ := 0) (ρmax := ρmax) (L := L)
    (by norm_num) hρmax hLpos hv)

/-- `h_L(0) ≥ 0`. -/
lemma hL_zero_nonneg {v : ℝ³ → ℝ} {ρmax ρ L : ℝ} (hρmax : 0 ≤ ρmax)
    (hLpos : 0 < L) (hv : 0 ≤ v) : 0 ≤ hL v ρmax ρ 0 L := by
  have h := gcDensity_zero_nonneg (v := v) (ρmax := ρmax) (L := L) hρmax hLpos hv
  simpa [hL] using h

/-- Every grand-canonical affine value is at most the canonical density:
`h_L(μ) ≤ diag(ρ,L)` for `μ ≥ 0`, `0 ≤ ρ ≤ ρmax`. -/
lemma hL_le_diag {v : ℝ³ → ℝ} {ρ ρmax μ L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hLpos : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) (hμ : 0 ≤ μ) :
    hL v ρmax ρ μ L ≤ diag v ρ L := by
  have h := gcDensity_add_mu_rho_L_le_diag (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
    hv hρmax hLpos hρ0 hρm hμ
  simpa [hL, rhoL] using h

/-- `gcDensity(·,ρmax,L)` is concave on `[0,∞)` in the chemical potential. -/
lemma gcDensity_concaveOn {v : ℝ³ → ℝ} {ρmax L : ℝ} (hv : 0 ≤ v) (hρmax : 0 ≤ ρmax)
    (hLpos : 0 < L) : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun μ : ℝ => gcDensity v μ ρmax L) := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have ha1 : a ≤ 1 := by linarith
  have hb' : b = 1 - a := by linarith
  rw [hb']
  simpa [smul_eq_mul] using
    gcDensity_concave_ineq (v := v) (ρmax := ρmax) (L := L) (μ₁ := x) (μ₂ := y) (t := a)
      hv hρmax hLpos hx0 hy0 ha ha1

/-- `h_L` is concave on `[0,∞)` in the chemical potential (concave density +
affine `μ·ρ_L`). -/
lemma hL_concaveOn {v : ℝ³ → ℝ} {ρmax ρ L : ℝ} (hv : 0 ≤ v) (hρmax : 0 ≤ ρmax)
    (hLpos : 0 < L) : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun μ : ℝ => hL v ρmax ρ μ L) := by
  refine ⟨convex_Ici (0 : ℝ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have ha1 : a ≤ 1 := by linarith
  have hb' : b = 1 - a := by linarith
  rw [hb']
  simp only [smul_eq_mul]
  have hineq := gcDensity_concave_ineq (v := v) (ρmax := ρmax) (L := L) (μ₁ := x) (μ₂ := y)
    (t := a) hv hρmax hLpos hx0 hy0 ha ha1
  have hlin : (a * x + (1 - a) * y) * rhoL ρ L =
      a * (x * rhoL ρ L) + (1 - a) * (y * rhoL ρ L) := by ring
  calc
    a * hL v ρmax ρ x L + (1 - a) * hL v ρmax ρ y L
        = a * (gcDensity v x ρmax L + x * rhoL ρ L) +
          (1 - a) * (gcDensity v y ρmax L + y * rhoL ρ L) := by
            simp only [hL]
    _ = (a * gcDensity v x ρmax L + (1 - a) * gcDensity v y ρmax L) +
          (a * (x * rhoL ρ L) + (1 - a) * (y * rhoL ρ L)) := by ring
    _ ≤ gcDensity v (a * x + (1 - a) * y) ρmax L +
          (a * (x * rhoL ρ L) + (1 - a) * (y * rhoL ρ L)) := by
            exact add_le_add_left hineq (a * (x * rhoL ρ L) + (1 - a) * (y * rhoL ρ L))
    _ = gcDensity v (a * x + (1 - a) * y) ρmax L + (a * x + (1 - a) * y) * rhoL ρ L := by
            rw [hlin]
    _ = hL v ρmax ρ (a * x + (1 - a) * y) L := by
            simp only [hL]

/-- `h_L` converges pointwise to `g` at every `μ ≥ 0` (for `0 ≤ ρ`). -/
lemma hL_tendsto {v : ℝ³ → ℝ} {ρ ρmax μ : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hρ : 0 ≤ ρ) {R : ℝ} (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    Tendsto (fun L : ℝ => hL v ρmax ρ μ L) atTop (𝓝 (gVal v ρmax ρ μ)) := by
  have h1 := gcDensity_tendsto_pressure (v := v) (μ := μ) (ρmax := ρmax) (R := R)
    hμ hρmax hR hv hv1 hsupp
  have h2 := tendsto_rhoL hρ
  have h3 : Tendsto (fun L : ℝ => μ * rhoL ρ L) atTop (𝓝 (μ * ρ)) := h2.const_mul μ
  simpa [hL, gVal] using h1.add h3

/-- Boundary control of `h_L` at `μ = 0`, uniform in `L`:
`|h_L(μ) − h_L(0)| ≤ 2μρmax` for `0 ≤ μ`, `0 ≤ ρ ≤ ρmax`. -/
lemma hL_lipschitz_zero {v : ℝ³ → ℝ} {ρ ρmax μ L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hLpos : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) (hμ : 0 ≤ μ) :
    |hL v ρmax ρ μ L - hL v ρmax ρ 0 L| ≤ μ * (2 * ρmax) := by
  have h1 := gcDensity_lipschitz_at_zero (v := v) (μ := μ) (ρmax := ρmax) (L := L)
    hμ hρmax hLpos hv
  have hρL0 : 0 ≤ rhoL ρ L := (rhoL_nonneg_le hρ0 hLpos).1
  have hρLρ : rhoL ρ L ≤ ρ := (rhoL_nonneg_le hρ0 hLpos).2
  have hμρL : 0 ≤ μ * rhoL ρ L := mul_nonneg hμ hρL0
  have hμρLρ : μ * rhoL ρ L ≤ μ * ρ := mul_le_mul_of_nonneg_left hρLρ hμ
  have hμρρmax : μ * ρ ≤ μ * ρmax := mul_le_mul_of_nonneg_left hρm hμ
  have h2 : |μ * rhoL ρ L| ≤ μ * ρmax := by
    rw [abs_of_nonneg hμρL]
    exact le_trans hμρLρ hμρρmax
  have hrew : hL v ρmax ρ μ L - hL v ρmax ρ 0 L =
      (gcDensity v μ ρmax L - gcDensity v 0 ρmax L) + μ * rhoL ρ L := by
    dsimp [hL]
    ring
  calc
    |hL v ρmax ρ μ L - hL v ρmax ρ 0 L|
        = |(gcDensity v μ ρmax L - gcDensity v 0 ρmax L) + μ * rhoL ρ L| := by rw [hrew]
    _ ≤ |gcDensity v μ ρmax L - gcDensity v 0 ρmax L| + |μ * rhoL ρ L| := abs_add_le _ _
    _ ≤ μ * ρmax + μ * ρmax := add_le_add h1 h2
    _ = μ * (2 * ρmax) := by ring

/-- The pressure is Lipschitz at `μ = 0`: `|p(μ) − p(0)| ≤ μρmax` (the
per-box bound passes to the limit). -/
lemma gcPressure_lipschitz_zero {v : ℝ³ → ℝ} {ρmax μ : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) {R : ℝ} (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) : |gcPressure v ρmax μ - gcPressure v ρmax 0| ≤ μ * ρmax := by
  let C : ℝ := μ * ρmax
  let xL : ℝ → ℝ := fun L => gcDensity v μ ρmax L - gcDensity v 0 ρmax L
  have htμ := gcDensity_tendsto_pressure (v := v) (μ := μ) (ρmax := ρmax) (R := R)
    hμ hρmax hR hv hv1 hsupp
  have ht0 := gcDensity_tendsto_pressure (v := v) (μ := 0) (ρmax := ρmax) (R := R)
    (by norm_num) hρmax hR hv hv1 hsupp
  have hsub : Tendsto xL atTop (𝓝 (gcPressure v ρmax μ - gcPressure v ρmax 0)) := by
    simpa [xL] using htμ.sub ht0
  have hbd : ∀ᶠ L : ℝ in atTop, |xL L| ≤ C := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    have hLpos : 0 < L := by linarith
    simpa [xL, C] using gcDensity_lipschitz_at_zero (v := v) (μ := μ) (ρmax := ρmax) (L := L)
      hμ hρmax hLpos hv
  have hle : ∀ᶠ L : ℝ in atTop, xL L ≤ C := (hbd.mono (fun L h => (abs_le.mp h).2))
  have hge : ∀ᶠ L : ℝ in atTop, -C ≤ xL L := (hbd.mono (fun L h => (abs_le.mp h).1))
  have hc1 : gcPressure v ρmax μ - gcPressure v ρmax 0 ≤ C := by
    have hf : Tendsto (fun L : ℝ => C - xL L) atTop (𝓝 (C - (gcPressure v ρmax μ - gcPressure v ρmax 0))) :=
      (tendsto_const_nhds (x := C)).sub hsub
    have hnon : ∀ᶠ L : ℝ in atTop, 0 ≤ C - xL L := hle.mono (fun L h => sub_nonneg.mpr h)
    have h0 : 0 ≤ C - (gcPressure v ρmax μ - gcPressure v ρmax 0) := ge_of_tendsto hf hnon
    linarith
  have hc2 : -(gcPressure v ρmax μ - gcPressure v ρmax 0) ≤ C := by
    have hf : Tendsto (fun L : ℝ => xL L + C) atTop (𝓝 (gcPressure v ρmax μ - gcPressure v ρmax 0 + C)) :=
      hsub.add (tendsto_const_nhds (x := C))
    have hnon : ∀ᶠ L : ℝ in atTop, 0 ≤ xL L + C := hge.mono (fun L h => by linarith)
    have h0 : 0 ≤ gcPressure v ρmax μ - gcPressure v ρmax 0 + C := ge_of_tendsto hf hnon
    linarith
  rw [abs_le]
  constructor
  · linarith
  · exact hc1

/-- Boundary control of `g` at `μ = 0`: `|g(μ) − g(0)| ≤ 2μρmax`. -/
lemma gVal_lipschitz_zero {v : ℝ³ → ℝ} {ρ ρmax μ : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) {R : ℝ} (hR : 0 ≤ R)
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) :
    |gVal v ρmax ρ μ - gVal v ρmax ρ 0| ≤ μ * (2 * ρmax) := by
  have h1 := gcPressure_lipschitz_zero (v := v) (ρmax := ρmax) (μ := μ) hμ hρmax hR hv hv1 hsupp
  have hμρ0 : 0 ≤ μ * ρ := mul_nonneg hμ hρ0
  have hμρρmax : μ * ρ ≤ μ * ρmax := mul_le_mul_of_nonneg_left hρm hμ
  have h2 : |μ * ρ| ≤ μ * ρmax := by
    rw [abs_of_nonneg hμρ0]
    exact hμρρmax
  have hrew : gVal v ρmax ρ μ - gVal v ρmax ρ 0 =
      (gcPressure v ρmax μ - gcPressure v ρmax 0) + μ * ρ := by
    dsimp [gVal]
    ring
  calc
    |gVal v ρmax ρ μ - gVal v ρmax ρ 0|
        = |(gcPressure v ρmax μ - gcPressure v ρmax 0) + μ * ρ| := by rw [hrew]
    _ ≤ |gcPressure v ρmax μ - gcPressure v ρmax 0| + |μ * ρ| := abs_add_le _ _
    _ ≤ μ * ρmax + μ * ρmax := add_le_add h1 h2
    _ = μ * (2 * ρmax) := by ring

/-! ## The linear decay in `μ` and the compact truncation of the supremum -/

/-- `gcDensity(μ,ρmax,L) ≤ E(N₀,L)/L³ − μ·(N₀/L³)` for the admissible
`N₀ := ⌊ρmaxL³⌋` (the grand-canonical optimum is achieved by no better than
the largest admissible state, whose energy is bounded by the product state). -/
lemma gcDensity_le_max_state {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ)
    (hρmax : 0 ≤ ρmax) (hLpos : 0 < L) (hv : 0 ≤ v) :
    gcDensity v μ ρmax L ≤ boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ)
      - μ * ((Nat.floor (ρmax * L ^ (3:ℕ)) : ℝ) / L ^ (3:ℕ)) := by
  have hL3pos : 0 < L ^ (3:ℕ) := pow_pos hLpos 3
  have hL3ne : L ^ (3:ℕ) ≠ 0 := ne_of_gt hL3pos
  have hx0 : 0 ≤ ρmax * L ^ (3:ℕ) := mul_nonneg hρmax (pow_nonneg hLpos.le 3)
  have hNad : gcAdmissible ρmax L (Nat.floor (ρmax * L ^ (3:ℕ))) := by
    dsimp [gcAdmissible]
    exact Nat.floor_le hx0
  have hgcle := gcBox_le_value (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hLpos hv hNad
  have hd := div_le_div_of_nonneg_right hgcle (pow_nonneg hLpos.le 3)
  unfold gcDensity
  have hEq : (boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v - μ * (Nat.floor (ρmax * L ^ (3:ℕ)) : ℝ))
        / L ^ (3:ℕ) =
      boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) -
        μ * ((Nat.floor (ρmax * L ^ (3:ℕ)) : ℝ) / L ^ (3:ℕ)) := by
    rw [sub_div]
    congr 1
    rw [← mul_div_assoc]
  rw [← hEq]
  exact hd

/-- Linear decay of `h_L` in `μ`, uniform in `L ≥ 1`: for `0 ≤ ρ < ρmax`
there is `M > 0` such that eventually `h_L(μ) ≤ h_L(0)` for all `μ ≥ M`.
(Combine `gcDensity_le_max_state` with the product-state upper bound
`boxDensity_upper_bound` at `ρ₀ := ρmax` and `hL_zero_nonneg`; use
`(⌊ρmaxL³⌋/L³ − ρ_L) ≥ (ρmax−ρ)/2` eventually.) -/
lemma hL_tail_decay {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {ρmax ρ : ℝ}
    (hρmax : 0 < ρmax) (hρ0 : 0 ≤ ρ) (hρm : ρ < ρmax) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ L : ℝ in atTop, ∀ μ : ℝ, M ≤ μ →
      hL v ρmax ρ μ L ≤ hL v ρmax ρ 0 L := by
  rcases boxDensity_upper_bound hv1 with ⟨C, hCpos, hbd⟩
  let B : ℝ := C * (ρmax ^ 2 * vL1 v + ρmax)
  have hvL1 : 0 ≤ vL1 v := by
    unfold vL1
    exact integral_nonneg (fun x => abs_nonneg (v x))
  have hBpos : 0 < B := by
    dsimp [B]
    have h1 : 0 ≤ ρmax ^ 2 * vL1 v := mul_nonneg (sq_nonneg ρmax) hvL1
    exact mul_pos hCpos (by linarith)
  let gap0 : ℝ := (ρmax - ρ) / 2
  have hgap0pos : 0 < gap0 := by
    dsimp [gap0]
    linarith
  let M : ℝ := 2 * B / (ρmax - ρ)
  have hMpos : 0 < M := by
    dsimp [M]
    exact div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hBpos) (by linarith : 0 < ρmax - ρ)
  refine ⟨M, hMpos, ?_⟩
  have hdiv : Tendsto (fun L : ℝ => 1 / L ^ (3:ℕ)) atTop (𝓝 0) :=
    tendsto_const_div_cube_nhds_zero (μ := 1) (by norm_num)
  have hsmall : ∀ᶠ L : ℝ in atTop, 1 / L ^ (3:ℕ) ≤ gap0 := by
    have hmem : {y : ℝ | y < gap0} ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hgap0pos
    exact (hdiv.eventually hmem).mono (fun L h => le_of_lt h)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with L hL1 hsmallL
  intro μ hμM
  have hLpos : 0 < L := by linarith
  have hμ0 : 0 ≤ μ := le_trans hMpos.le hμM
  -- product-state upper bound on E(⌊ρmaxL³⌋,L)/L³
  have hNdens : (Nat.floor (ρmax * L ^ (3:ℕ)) : ℝ) / L ^ (3:ℕ) ≤ ρmax := by
    simpa [rhoL] using (rhoL_nonneg_le hρmax.le hLpos).2
  have hEbd : boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) ≤ B := by
    simpa [B] using hbd ρmax (Nat.floor (ρmax * L ^ (3:ℕ))) hL1 hρmax.le hNdens
  -- the floor gap (⌊ρmaxL³⌋/L³ − ρ_L) is eventually at least gap0
  have hNlow : ρmax - 1 / L ^ (3:ℕ) ≤ (Nat.floor (ρmax * L ^ (3:ℕ)) : ℝ) / L ^ (3:ℕ) := by
    simpa [rhoL] using rhoL_lower hρmax.le hLpos
  have hρLρ : rhoL ρ L ≤ ρ := (rhoL_nonneg_le hρ0 hLpos).2
  have hg2 : gap0 ≤ ρmax - 1 / L ^ (3:ℕ) - ρ := by
    dsimp [gap0] at hsmallL ⊢
    nlinarith
  have hg1 : ρmax - 1 / L ^ (3:ℕ) - ρ ≤
      (Nat.floor (ρmax * L ^ (3:ℕ)) : ℝ) / L ^ (3:ℕ) - rhoL ρ L := by
    exact add_le_add hNlow (neg_le_neg hρLρ)
  have hgapL : gap0 ≤
      (Nat.floor (ρmax * L ^ (3:ℕ)) : ℝ) / L ^ (3:ℕ) - rhoL ρ L := le_trans hg2 hg1
  have hgapL' : gap0 ≤ rhoL ρmax L - rhoL ρ L := by
    simpa [rhoL] using hgapL
  -- grand-canonical density upper bound at the maximal admissible state
  have hge0 := gcDensity_le_max_state (v := v) (μ := μ) (ρmax := ρmax) (L := L)
    hμ0 hρmax.le hLpos hv
  have hge : gcDensity v μ ρmax L ≤ boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ)
      - μ * rhoL ρmax L := by
    simpa [rhoL] using hge0
  -- algebra: h_L(μ) ≤ E − μ·gap0 ≤ B − μ·gap0 ≤ 0 ≤ h_L(0)
  have hμg : μ * gap0 ≤ μ * (rhoL ρmax L - rhoL ρ L) := mul_le_mul_of_nonneg_left hgapL' hμ0
  have hmid : (boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) - μ * rhoL ρmax L)
        + μ * rhoL ρ L ≤ B - μ * gap0 := by
    have hrew : (boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) - μ * rhoL ρmax L)
          + μ * rhoL ρ L =
        boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) - μ * (rhoL ρmax L - rhoL ρ L) := by ring
    rw [hrew]
    have hstep : boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) -
          μ * (rhoL ρmax L - rhoL ρ L) ≤
        boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) - μ * gap0 := by
      exact sub_le_sub_left hμg _
    have hstep2 : boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) - μ * gap0 ≤ B - μ * gap0 :=
      sub_le_sub_right hEbd _
    exact le_trans hstep hstep2
  have hleB : hL v ρmax ρ μ L ≤ B - μ * gap0 := by
    calc
      hL v ρmax ρ μ L = gcDensity v μ ρmax L + μ * rhoL ρ L := by simp [hL]
      _ ≤ (boxEnergy (Nat.floor (ρmax * L ^ (3:ℕ))) L v / L ^ (3:ℕ) - μ * rhoL ρmax L)
            + μ * rhoL ρ L := by
              exact add_le_add_left hge (μ * rhoL ρ L)
      _ ≤ B - μ * gap0 := hmid
  have hMge : M * gap0 ≤ μ * gap0 := mul_le_mul_of_nonneg_right hμM hgap0pos.le
  have hle0 : B - μ * gap0 ≤ 0 := by
    have hz : B - μ * gap0 ≤ B - M * gap0 := sub_le_sub_left hMge B
    have hMB : B - M * gap0 = 0 := by
      dsimp [M, gap0]
      have hne : ρmax - ρ ≠ 0 := by linarith
      field_simp [hne]
      ring
    rwa [hMB] at hz
  have hL0 : 0 ≤ hL v ρmax ρ 0 L :=
    hL_zero_nonneg (v := v) (ρmax := ρmax) (ρ := ρ) (L := L) hρmax.le hLpos hv
  exact le_trans (le_trans hleB hle0) hL0

/-- The canonical set is the image of `h_L` on `μ ≥ 0`, bounded above by the
diagonal. -/
lemma canonSup_eq_sSup_hL {v : ℝ³ → ℝ} {ρ ρmax L : ℝ} (hv : 0 ≤ v)
    (hρmax : 0 ≤ ρmax) (hLpos : 0 < L) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ ρmax) :
    canonSup v ρmax ρ L = sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Ici (0 : ℝ)) := by
  have hSet : (fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Ici (0 : ℝ) = gcCanonSet v ρmax ρ L := by
    ext y
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      dsimp [gcCanonSet]
      refine ⟨μ, hμ, ?_⟩
      simp [hL, rhoL]
    · rintro ⟨μ, hμ, rfl⟩
      refine ⟨μ, hμ, ?_⟩
      simp [hL, rhoL]
  unfold canonSup
  rw [hSet]

/-- Eventually the supremum over `μ ≥ 0` is attained on the compact range
`[0,M]` (for the `M` of `hL_tail_decay`). -/
lemma canonSup_eq_sSup_Icc {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {ρmax ρ M : ℝ}
    (hρmax : 0 < ρmax) (hρ0 : 0 ≤ ρ) (hρm : ρ < ρmax) (hM : 0 < M)
    (hdecay : ∀ᶠ L : ℝ in atTop, ∀ μ : ℝ, M ≤ μ → hL v ρmax ρ μ L ≤ hL v ρmax ρ 0 L) :
    ∀ᶠ L : ℝ in atTop,
      canonSup v ρmax ρ L = sSup ((fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M) := by
  filter_upwards [hdecay, eventually_ge_atTop (1 : ℝ)] with L hdecayL hL1
  have hLpos : 0 < L := by linarith
  let A : Set ℝ := (fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Icc (0 : ℝ) M
  let B : Set ℝ := (fun μ : ℝ => hL v ρmax ρ μ L) '' Set.Ici (0 : ℝ)
  have hsubAB : A ⊆ B := by
    intro y hy
    rcases hy with ⟨μ, hμI, rfl⟩
    exact ⟨μ, hμI.1, rfl⟩
  have hBddB : BddAbove B := by
    refine ⟨diag v ρ L, ?_⟩
    intro y hy
    rcases hy with ⟨μ, hμ, rfl⟩
    exact hL_le_diag (v := v) (ρ := ρ) (ρmax := ρmax) (μ := μ) (L := L)
      hv hρmax.le hLpos hρ0 (le_of_lt hρm) hμ
  have hBddA : BddAbove A := hBddB.mono hsubAB
  have hAnon : A.Nonempty := by
    refine ⟨hL v ρmax ρ 0 L, 0, ⟨le_rfl, hM.le⟩, rfl⟩
  have hBnon : B.Nonempty := by
    refine ⟨hL v ρmax ρ 0 L, ?_⟩
    refine ⟨0, ?_, rfl⟩
    exact Set.mem_Ici.mpr (le_rfl : (0 : ℝ) ≤ 0)
  have hleAB : sSup A ≤ sSup B := csSup_le_csSup hBddB hAnon hsubAB
  have hleBA : sSup B ≤ sSup A := by
    apply csSup_le hBnon
    intro y hy
    rcases hy with ⟨μ, hμ, rfl⟩
    by_cases hμM : μ ≤ M
    · exact le_csSup hBddA ⟨μ, ⟨hμ, hμM⟩, rfl⟩
    · have hMμ : M ≤ μ := le_of_not_ge hμM
      have hdec : hL v ρmax ρ μ L ≤ hL v ρmax ρ 0 L := hdecayL μ hMμ
      have h0mem : hL v ρmax ρ 0 L ∈ A := ⟨0, ⟨le_rfl, hM.le⟩, rfl⟩
      exact le_trans hdec (le_csSup hBddA h0mem)
  have hEqB : canonSup v ρmax ρ L = sSup B := by
    unfold canonSup B
    exact canonSup_eq_sSup_hL (v := v) (ρ := ρ) (ρmax := ρmax) (L := L)
      hv hρmax.le hLpos hρ0 (le_of_lt hρm)
  have hEqAB : sSup B = sSup A := le_antisymm hleBA hleAB
  simpa [A] using hEqB.trans hEqAB

end BoseGases

end Submission
