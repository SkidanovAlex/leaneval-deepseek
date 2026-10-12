import ChallengeDeps
import Submission.DiagUpperLim
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — from diagonal limits to the convergence of the box densities along
the joint filter.

If, for every positive density `ρ'`, the diagonal `diag v ρ' L` converges to
`x ρ'` as `L → ∞`, and `x` is continuous at `ρ > 0`, then the box-energy
densities converge along the joint filter at density `ρ`:

    Tendsto (boxDensity v) (jointFilter ρ) (𝓝 (x ρ))

The argument is a window sandwich: because the box energy is nondecreasing in
the particle number, for `|N/L³ − ρ| < δ` the density `E(N,L)/L³` lies between
the diagonal values at the densities `ρ−δ` and `ρ+δ`:

    diag v (ρ−δ) L ≤ boxDensity v (L,N) ≤ diag v (ρ+δ) L

and these converge to `x (ρ±δ)`, which are arbitrarily close to `x ρ` by
continuity.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `L^{-3} = (L³)⁻¹`. -/
lemma zpow_neg_three (L : ℝ) : L ^ (-3 : ℤ) = (L ^ 3)⁻¹ := by
  rw [zpow_neg]
  norm_num

/-! ## Window-sandwich facts -/

/-- Counts from the density window: `(ρ−δ)L³ < N ⟹ ⌊(ρ−δ)L³⌋ ≤ N`. -/
lemma floor_le_of_lt_density {ρ δ : ℝ} {L : ℝ} {N : ℕ}
    (h : (ρ - δ) * L ^ 3 < (N : ℝ)) : Nat.floor ((ρ - δ) * L ^ 3) ≤ N := by
  let x : ℝ := (ρ - δ) * L ^ 3
  have hxN : x < (N : ℝ) := h
  by_cases hx0 : 0 ≤ x
  · have hfl : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx0
    have : (Nat.floor x : ℝ) < (N : ℝ) := lt_of_le_of_lt hfl hxN
    exact_mod_cast (le_of_lt this)
  · have hneg : x < 0 := lt_of_not_ge hx0
    have hf0 : Nat.floor x = 0 := by
      apply le_antisymm
      · have hm := Nat.floor_mono (a := x) (b := 0) (le_of_lt hneg)
        simpa using hm
      · exact Nat.zero_le _
    rw [hf0]
    exact Nat.zero_le N

/-- Counts from the density window: `N < (ρ+δ)L³ ⟹ N ≤ ⌊(ρ+δ)L³⌋`. -/
lemma le_floor_of_lt_density {ρ δ : ℝ} {L : ℝ} {N : ℕ}
    (h : (N : ℝ) < (ρ + δ) * L ^ 3) : N ≤ Nat.floor ((ρ + δ) * L ^ 3) := by
  let x : ℝ := (ρ + δ) * L ^ 3
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  have hx0 : 0 ≤ x := by nlinarith
  have hNx : (N : ℝ) ≤ x := le_of_lt h
  apply (Nat.le_floor_iff hx0).2
  simpa using hNx

/-- `boxDensity v (L,N) = E(N,L)/L³` for `0 < L`. -/
lemma boxDensity_eq_div {v : ℝ³ → ℝ} {L : ℝ} {N : ℕ} :
    boxDensity v (L, N) = boxEnergy N L v / L ^ 3 := by
  dsimp [boxDensity]
  rw [zpow_neg_three]
  rw [div_eq_mul_inv]
  rw [mul_comm]

/-- The sandwich: inside the density window, the box density lies between the
diagonal values at the two window densities. -/
lemma boxDensity_window_le {v : ℝ³ → ℝ} {ρ δ : ℝ} {L : ℝ} {N : ℕ}
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hL : 0 < L) (hρδ0 : 0 < ρ - δ)
    (hwin : |(N : ℝ) / L ^ 3 - ρ| < δ) :
    diag v (ρ - δ) L ≤ boxDensity v (L, N) ∧ boxDensity v (L, N) ≤ diag v (ρ + δ) L := by
  have hlo : (ρ - δ) * L ^ 3 < (N : ℝ) := by
    have h1 : ρ - δ < (N : ℝ) / L ^ 3 := by
      rw [abs_lt] at hwin
      nlinarith
    rwa [lt_div_iff₀ (pow_pos hL 3)] at h1
  have hhi : (N : ℝ) < (ρ + δ) * L ^ 3 := by
    have h1 : (N : ℝ) / L ^ 3 < ρ + δ := by
      rw [abs_lt] at hwin
      nlinarith
    rwa [div_lt_iff₀ (pow_pos hL 3)] at h1
  have hNlo : Nat.floor ((ρ - δ) * L ^ 3) ≤ N := floor_le_of_lt_density hlo
  have hNhi : N ≤ Nat.floor ((ρ + δ) * L ^ 3) := le_floor_of_lt_density hhi
  have hE1 : boxEnergy (Nat.floor ((ρ - δ) * L ^ 3)) L v ≤ boxEnergy N L v :=
    boxEnergy_mono_N hL hv hv1 hNlo
  have hE2 : boxEnergy N L v ≤ boxEnergy (Nat.floor ((ρ + δ) * L ^ 3)) L v :=
    boxEnergy_mono_N hL hv hv1 hNhi
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL.le 3
  constructor
  · dsimp [diag]
    rw [boxDensity_eq_div]
    exact div_le_div_of_nonneg_right hE1 hL3
  · dsimp [diag]
    rw [boxDensity_eq_div]
    exact div_le_div_of_nonneg_right hE2 hL3

/-! ## Convergence along the joint filter from diagonal limits -/

/-- If the diagonal has a limit `x` at every density in `(0,ρ₀)` and `x` is
continuous at `ρ ∈ (0,ρ₀)`, then the box densities converge along the joint
filter at `ρ` to `x ρ`. -/
lemma tendsto_boxDensity_of_diag_limits_on {v : ℝ³ → ℝ} {ρ ρ₀ : ℝ} {x : ℝ → ℝ}
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hρ : 0 < ρ) (hρ₀ : ρ < ρ₀)
    (hx : ContinuousAt x ρ)
    (hdiag : ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρ₀ → Tendsto (fun L : ℝ => diag v ρ' L) atTop (𝓝 (x ρ'))) :
    Tendsto (boxDensity v) (jointFilter ρ) (𝓝 (x ρ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ε3 : ℝ := ε / 3
  have hε3 : 0 < ε3 := by dsimp [ε3]; linarith
  rcases Metric.continuousAt_iff.mp hx ε3 hε3 with ⟨η₀, hη₀, hxη⟩
  let δ : ℝ := min (min (η₀ / 2) (ρ / 2)) ((ρ₀ - ρ) / 2)
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hδη : δ < η₀ := by
    dsimp [δ]
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hδρ : δ < ρ := by
    dsimp [δ]
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hδρ₀ : δ < ρ₀ - ρ := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hρδ0 : 0 < ρ - δ := by linarith
  have hρδn : 0 < ρ + δ := by linarith
  have hρδlt : ρ + δ < ρ₀ := by linarith
  have hxlo : |x (ρ - δ) - x ρ| < ε3 := by
    have harg : dist (ρ - δ) ρ < η₀ := by
      change |(ρ - δ) - ρ| < η₀
      rw [show (ρ - δ) - ρ = -δ by ring, abs_neg, abs_of_pos hδ0]
      exact hδη
    have hd := hxη harg
    change |x (ρ - δ) - x ρ| < ε3
    exact hd
  have hxhi : |x (ρ + δ) - x ρ| < ε3 := by
    have harg : dist (ρ + δ) ρ < η₀ := by
      change |(ρ + δ) - ρ| < η₀
      rw [show (ρ + δ) - ρ = δ by ring, abs_of_pos hδ0]
      exact hδη
    have hd := hxη harg
    change |x (ρ + δ) - x ρ| < ε3
    exact hd
  have hloT := hdiag (ρ - δ) hρδ0 (by linarith)
  have hhiT := hdiag (ρ + δ) hρδn hρδlt
  have hloEv : ∀ᶠ L : ℝ in atTop, |diag v (ρ - δ) L - x (ρ - δ)| < ε3 :=
    hloT.eventually (Metric.ball_mem_nhds (x (ρ - δ)) hε3)
  have hhiEv : ∀ᶠ L : ℝ in atTop, |diag v (ρ + δ) L - x (ρ + δ)| < ε3 :=
    hhiT.eventually (Metric.ball_mem_nhds (x (ρ + δ)) hε3)
  have hL1 : ∀ᶠ L : ℝ in atTop, (1 : ℝ) ≤ L := eventually_ge_atTop 1
  rcases eventually_atTop.mp ((hloEv.and hhiEv).and hL1) with ⟨L₀, hL₀⟩
  have hEv : ∀ᶠ p : ℝ × ℕ in jointFilter ρ,
      L₀ ≤ p.1 ∧ |(p.2 : ℝ) / p.1 ^ 3 - ρ| < δ := by
    have hbig : ∀ᶠ p : ℝ × ℕ in atTop.comap (Prod.fst : ℝ × ℕ → ℝ), L₀ ≤ p.1 :=
      (eventually_ge_atTop L₀).comap Prod.fst
    have hb : ∀ᶠ y : ℝ in 𝓝 ρ, |y - ρ| < δ := Metric.ball_mem_nhds ρ hδ0
    have hdens : ∀ᶠ p : ℝ × ℕ in (𝓝 ρ).comap (fun p : ℝ × ℕ => (p.2 : ℝ) / p.1 ^ 3),
        |(p.2 : ℝ) / p.1 ^ 3 - ρ| < δ := hb.comap (fun p : ℝ × ℕ => (p.2 : ℝ) / p.1 ^ 3)
    filter_upwards [hbig.filter_mono inf_le_left, hdens.filter_mono inf_le_right]
      with p hLp hdens'
    exact ⟨hLp, hdens'⟩
  filter_upwards [hEv] with p hp
  rcases hp with ⟨hLp, hdensp⟩
  have hL0ge1 : (1 : ℝ) ≤ L₀ := (hL₀ L₀ (le_rfl)).2
  have hLge1 : (1 : ℝ) ≤ p.1 := le_trans hL0ge1 hLp
  have hLpos : 0 < p.1 := lt_of_lt_of_le zero_lt_one hLge1
  have hsand := boxDensity_window_le (v := v) (ρ := ρ) (δ := δ) (L := p.1) (N := p.2)
    hv hv1 hLpos hρδ0 hdensp
  have hL₀₀ := hL₀ p.1 hLp
  have hloE : |diag v (ρ - δ) p.1 - x (ρ - δ)| < ε3 := hL₀₀.1.1
  have hhiE : |diag v (ρ + δ) p.1 - x (ρ + δ)| < ε3 := hL₀₀.1.2
  -- lower bound: xρ − ε < boxDensity
  have hxlo' : -ε3 < x (ρ - δ) - x ρ := by rw [abs_lt] at hxlo; linarith
  have hdlo' : -ε3 < diag v (ρ - δ) p.1 - x (ρ - δ) := by rw [abs_lt] at hloE; linarith
  have hbdlo : x ρ - ε < boxDensity v p := by
    have hz : x ρ - 2 * ε3 < diag v (ρ - δ) p.1 := by nlinarith
    have hzw : x ρ - ε < diag v (ρ - δ) p.1 := by nlinarith [show ε3 = ε / 3 from rfl]
    exact lt_of_lt_of_le hzw hsand.1
  -- upper bound: boxDensity < xρ + ε
  have hxhi' : -ε3 < x ρ - x (ρ + δ) := by rw [abs_lt] at hxhi; linarith
  have dhio' : -ε3 < x (ρ + δ) - diag v (ρ + δ) p.1 := by rw [abs_lt] at hhiE; linarith
  have hbdup : boxDensity v p < x ρ + ε := by
    have hz : diag v (ρ + δ) p.1 < x ρ + 2 * ε3 := by nlinarith
    have hzw : diag v (ρ + δ) p.1 < x ρ + ε := by nlinarith [show ε3 = ε / 3 from rfl]
    exact lt_of_le_of_lt hsand.2 hzw
  rw [Real.dist_eq]
  rw [abs_lt]
  constructor
  · nlinarith
  · nlinarith

end BoseGases

end Submission
