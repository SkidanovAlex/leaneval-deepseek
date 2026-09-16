import Mathlib
import Submission.Theorem35Disc
import Submission.Theorem35Main
import Submission.LevelOfDistribution
import Submission.Theorem36i

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 4000000

/-!
# Polymath8a Theorem 3.5(i): the θ-weighted window asymptotics

This module assembles the two halves proved earlier:

* `thetaMainSum_asymptotic_unconditional` (`Submission.Theorem35Main`) — the main
  term of the θ-weighted window sum, `(1/φ(W))·x·prefactor^k·∏ᵢ∫Fᵢ′Gᵢ′`;
* `thetaDiscSum_le` (`Submission.Theorem35Disc`) — the discrepancy part is
  `O(x log^{-B}x)` for every fixed `B`, using the shifted-window level of
  distribution.

The output `theorem35_i` is Polymath8a (26): the θ-weighted window product

    Σ_{x≤n≤2x, n≡b(W)} θ(n+h)·∏_{i<k} λ_{Fᵢ}(n+hᵢ)λ_{Gᵢ}(n+hᵢ)

is `(c + o(1))·(1/φ(W))·x·B^{-k}` with `c = ∏ᵢ ∫₀^∞ Fᵢ′Gᵢ′` and
`B = (φ(W)/W)·log x`.
-/

namespace Commons.NumberTheory.MaynardSieve

attribute [local instance] Classical.propDecidable

/-- The θ-weighted window product of Polymath8a (26):
`Σ_{N≤n≤2N, n≡b (W)} θ(n+h)·∏ᵢ (Σ_{d|n+Hᵢ}αᵢ(d))·(Σ_{e|n+Hᵢ}βᵢ(e))`. -/
noncomputable def thetaWindowSum {k : ℕ} (N W b h D : ℕ) (H : Fin k → ℕ)
    (α β : Fin k → ℕ → ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
    thetaNat (n + h) * ∏ i : Fin k,
      (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
      (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))

/-- The `(1/φ(W))·x·B^{-k}` scale of the main term of Theorem 3.5. -/
noncomputable def thetaMainScale {k : ℕ} (Wf : ℕ → ℕ) (x : ℕ) : ℝ :=
  (1 / ((Wf x).totient : ℝ)) * (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k

/-- The main term of Polymath8a (26). -/
noncomputable def thetaMainTerm {k : ℕ} (F G : Fin k → ℝ → ℝ) (Wf : ℕ → ℕ) (x : ℕ) : ℝ :=
  thetaMainScale (k := k) Wf x *
    ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)

/-- `x/(log x)^{A₀+k} ≤ (1/φ(W))·x·B^{-k}` when `W ≤ (log x)^{A₀}`, `log x ≥ 1`.
This is the lower bound on the main scale that converts an absolute
`O(x log^{-B}x)` error into a relative one. -/
theorem thetaMainScale_ge_log {W : ℕ → ℕ} {x : ℕ} (hW : W x ≠ 0) (hx : 2 ≤ x)
    {A₀ k : ℕ} (hlog1 : 1 ≤ Real.log (x : ℝ))
    (hA : (W x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀) :
    (x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k) ≤ thetaMainScale (k := k) W x := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hLnn : 0 ≤ Real.log (x : ℝ) := le_of_lt hLpos
  have hWpos : 0 < (W x : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hW)
  have hφpos : 0 < ((W x).totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW))
  have hφle : ((W x).totient : ℝ) ≤ (W x : ℝ) := by exact_mod_cast Nat.totient_le (W x)
  have hpre1 : (Real.log (x : ℝ))⁻¹ ≤ prefactor W (fun _ => 1) x :=
    inv_log_le_prefactor_one (W := W) hW hx
  have hlinn : 0 ≤ (Real.log (x : ℝ))⁻¹ := by positivity
  have hpown : ((Real.log (x : ℝ)) ^ k)⁻¹ ≤ (prefactor W (fun _ => 1) x) ^ k := by
    have h := pow_le_pow_left₀ hlinn hpre1 k
    rwa [inv_pow] at h
  have h1 : ((Real.log (x : ℝ)) ^ A₀)⁻¹ ≤ ((W x : ℝ))⁻¹ :=
    (inv_le_inv₀ (pow_pos hLpos A₀) hWpos).mpr hA
  have h2 : ((W x : ℝ))⁻¹ ≤ (((W x).totient : ℝ))⁻¹ :=
    (inv_le_inv₀ hWpos hφpos).mpr hφle
  have hA1 : (x : ℝ) * ((Real.log (x : ℝ)) ^ A₀)⁻¹ ≤
      (x : ℝ) * (((W x).totient : ℝ))⁻¹ :=
    mul_le_mul_of_nonneg_left (le_trans h1 h2) hxnn
  have hA2 : (x : ℝ) * ((Real.log (x : ℝ)) ^ A₀)⁻¹ * ((Real.log (x : ℝ)) ^ k)⁻¹ ≤
      (x : ℝ) * (((W x).totient : ℝ))⁻¹ * ((Real.log (x : ℝ)) ^ k)⁻¹ :=
    mul_le_mul_of_nonneg_right hA1 (by positivity)
  have hstep : (x : ℝ) * ((Real.log (x : ℝ)) ^ A₀)⁻¹ * ((Real.log (x : ℝ)) ^ k)⁻¹ ≤
      (x : ℝ) * (((W x).totient : ℝ))⁻¹ * (prefactor W (fun _ => 1) x) ^ k :=
    le_trans hA2 (mul_le_mul_of_nonneg_left hpown (by positivity))
  calc (x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k)
      = (x : ℝ) * ((Real.log (x : ℝ)) ^ A₀)⁻¹ * ((Real.log (x : ℝ)) ^ k)⁻¹ := by
        rw [div_eq_mul_inv, pow_add, mul_inv]; ring
    _ ≤ (x : ℝ) * (((W x).totient : ℝ))⁻¹ * (prefactor W (fun _ => 1) x) ^ k := hstep
    _ = thetaMainScale (k := k) W x := by
        rw [thetaMainScale, one_div]; ring

/-- **Polymath8a Theorem 3.5(i) (26), assembled.**  Under the level of
distribution `EH[ϑ]`, for an admissible tuple `H`, a residue class `b (W)` with
`b + H i` coprime to `W` for all `i`, a shift `h` distinct from all `H i` and
separated from them by `wd`, smooth compactly supported cutoffs `F, G` whose
support radii sum to `< ϑ`, the θ-weighted window product is

    `(c + o(1))·(1/φ(W))·x·B^{-k}`   with `c = ∏ᵢ ∫₀^∞ Fᵢ′Gᵢ′`. -/
theorem theorem35_i {k : ℕ} (hk : 1 ≤ k) (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ i, HasCompactSupport (F i)) (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i))
    (hcsG : ∀ i, HasCompactSupport (G i)) (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (Wf : ℕ → ℕ) (hW : ∀ x, Wf x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ Wf x)
    (hlq : Tendsto (fun x : ℕ =>
      Real.log ((Wf x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0))
    {BF BG : ℝ} (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hFbd : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF)
    (hGbd : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ2 : ϑ < 1 / 2) {Mf Mg : Fin k → ℝ}
    (hMfnn : ∀ i, 0 ≤ Mf i) (hMgnn : ∀ i, 0 ≤ Mg i)
    (hMf : ∀ (i : Fin k) (t : ℝ), Mf i < |t| → F i t = 0)
    (hMg : ∀ (i : Fin k) (t : ℝ), Mg i < |t| → G i t = 0)
    (hsum : ∑ i : Fin k, (Mf i + Mg i) < ϑ)
    (b : ℕ → ℕ) (h : ℕ) (H : Fin k → ℕ) (hHinj : Function.Injective H)
    (hbW : ∀ᶠ x : ℕ in atTop, ∀ i : Fin k, (b x + H i).Coprime (Wf x))
    (hbWh : ∀ᶠ x : ℕ in atTop, (b x + h).Coprime (Wf x))
    (hhne : ∀ i, h ≠ H i)
    (wd : ℕ → ℕ) (hwdw : ∀ᶠ x : ℕ in atTop, wd x ≤ w x)
    (hsep : ∀ᶠ x : ℕ in atTop, ∀ i j : Fin k, i ≠ j → H j - H i < wd x)
    (hseph : ∀ᶠ x : ℕ in atTop, ∀ i : Fin k, h - H i < wd x ∧ H i - h < wd x)
    (hlev : levelOfDistribution ϑ)
    (hWlog : ∃ A₀ : ℕ, ∀ᶠ x : ℕ in atTop, (Wf x : ℝ) ≤ (Real.log (x : ℝ)) ^ A₀)
    (D : ℕ → ℕ) (hDM : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ M ≤ (D x : ℝ))
    (hDϑ : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      |thetaWindowSum x (Wf x) (b x) h (D x) H
          (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) -
        thetaMainTerm F G Wf x| ≤ ε x * thetaMainScale (k := k) Wf x := by
  classical
  obtain ⟨A₀, hA₀⟩ := hWlog
  obtain ⟨x₁, ε₁, hε₁, hb₁⟩ :=
    thetaMainSum_asymptotic_unconditional (k := k) hk F G hcsF hsmF hcsG hsmG
      Wf hW w hw hsmall hlq hBF hBG hFbd hGbd hM hϑ0 hϑ2 hMf hMg hsum h D hDM hDϑ
  obtain ⟨C, hCpos, hCb⟩ := thetaDiscSum_le (k := k) hk F G hBF hBG hFbd hGbd hMfnn hMgnn
    hMf hMg hϑ0 hϑ2 hsum Wf hW w hw hsmall hlq b h H hbWh hhne wd hwdw hseph
    hlev ⟨A₀, hA₀⟩ D (A₀ + k + 3)
  have hinv : Tendsto (fun x : ℕ => (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop
  have hCinv : Tendsto (fun x : ℕ => C * (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hinv
    simpa using h
  have hlog1ev : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)
  have hxbig : ∀ᶠ x : ℕ in atTop, max x₁ 3 ≤ x := eventually_ge_atTop _
  have hw2ev : ∀ᶠ x : ℕ in atTop, 2 ≤ w x := hw.eventually (eventually_ge_atTop 2)
  have hgoal : ∀ᶠ x : ℕ in atTop,
      |thetaWindowSum x (Wf x) (b x) h (D x) H
          (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) -
        thetaMainTerm F G Wf x| ≤
      (ε₁ x + C * (Real.log (x : ℝ))⁻¹) * thetaMainScale (k := k) Wf x := by
    filter_upwards [hCb, hA₀, hlog1ev, hxbig, hwdw, hbW, hsep, hseph, hbWh, hw2ev]
      with x hCx hA₀x hlog1x hxbigx hwdwx hbWx hsepx hsephx hbWhx hw2x
    have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hxbigx
    have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hxbigx
    have hx2 : 2 ≤ x := by omega
    have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlog1x
    have hW2x : 2 ≤ Wf x :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (hW x)) (hsmall x 2 Nat.prime_two hw2x)
    -- the decomposition into main term and discrepancy
    have hdec : thetaWindowSum x (Wf x) (b x) h (D x) H
          (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) =
        thetaMainSum (N := x) (W := Wf x) (h := h) (D := D x)
            (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) +
          thetaDiscSum (N := x) (W := Wf x) (b := b x) (h := h) (D := D x) H
            (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) :=
      thetaWindowProduct_eq_main_add_disc (k := k) (D := D x) (N := x) (W := Wf x)
        (b := b x) (wd := wd x) (H := H) h
        (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
        hW2x (fun p hp hpw => hsmall x p hp (le_trans hpw hwdwx)) hHinj
        (fun i => hbWx i) (fun i j hij => hsepx i j hij)
    have hmain : |thetaMainSum (N := x) (W := Wf x) (h := h) (D := D x)
          (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) -
        thetaMainTerm F G Wf x| ≤ ε₁ x * thetaMainScale (k := k) Wf x := hb₁ x hx1
    -- the main scale dominates `x/(log x)^{A₀+k}`
    have hXge : (x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k) ≤
        thetaMainScale (k := k) Wf x :=
      thetaMainScale_ge_log (W := Wf) (hW x) hx2 hlog1x hA₀x
    have hX0 : 0 ≤ thetaMainScale (k := k) Wf x :=
      le_trans (by positivity) hXge
    have hdratio : C / (Real.log (x : ℝ)) ^ 3 ≤ C * (Real.log (x : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCpos)
      have hLL : (1 : ℝ) ≤ Real.log (x : ℝ) * Real.log (x : ℝ) := by
        have h := mul_le_mul hlog1x hlog1x (show (0 : ℝ) ≤ 1 by norm_num) (le_of_lt hLpos)
        simpa using h
      have hLL3 : Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ 3 := by
        calc Real.log (x : ℝ) = Real.log (x : ℝ) * 1 := (mul_one _).symm
          _ ≤ Real.log (x : ℝ) * (Real.log (x : ℝ) * Real.log (x : ℝ)) :=
              mul_le_mul_of_nonneg_left hLL (le_of_lt hLpos)
          _ = (Real.log (x : ℝ)) ^ 3 := by ring
      exact (inv_le_inv₀ (pow_pos hLpos 3) hLpos).mpr hLL3
    have hCd : C * (x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k + 3) ≤
        (C * (Real.log (x : ℝ))⁻¹) * thetaMainScale (k := k) Wf x := by
      have hsplit : C * (x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k + 3) =
          (C / (Real.log (x : ℝ)) ^ 3) * ((x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k)) := by
        rw [show A₀ + k + 3 = 3 + (A₀ + k) by ring, pow_add]
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
        ring
      rw [hsplit]
      exact mul_le_mul hdratio hXge (by positivity) (by positivity)
    have h2 : ε₁ x * thetaMainScale (k := k) Wf x +
          C * (x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k + 3) ≤
        (ε₁ x + C * (Real.log (x : ℝ))⁻¹) * thetaMainScale (k := k) Wf x := by
      calc ε₁ x * thetaMainScale (k := k) Wf x +
              C * (x : ℝ) / (Real.log (x : ℝ)) ^ (A₀ + k + 3)
          ≤ ε₁ x * thetaMainScale (k := k) Wf x +
              (C * (Real.log (x : ℝ))⁻¹) * thetaMainScale (k := k) Wf x :=
            add_le_add le_rfl hCd
        _ = (ε₁ x + C * (Real.log (x : ℝ))⁻¹) * thetaMainScale (k := k) Wf x := by ring
    have hT : thetaWindowSum x (Wf x) (b x) h (D x) H
          (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) -
        thetaMainTerm F G Wf x =
        (thetaMainSum (N := x) (W := Wf x) (h := h) (D := D x)
            (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) -
          thetaMainTerm F G Wf x) +
        thetaDiscSum (N := x) (W := Wf x) (b := b x) (h := h) (D := D x) H
          (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x) := by
      rw [hdec]; ring
    rw [hT]
    exact le_trans (abs_add_le _ _)
      (le_trans (add_le_add hmain hCx) h2)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hgoal
  have hε : Tendsto (fun x : ℕ => ε₁ x + C * (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) := by
    have h := hε₁.add hCinv
    simpa using h
  exact ⟨x₀, fun x => ε₁ x + C * (Real.log (x : ℝ))⁻¹, hε, hx₀⟩

end Commons.NumberTheory.MaynardSieve
