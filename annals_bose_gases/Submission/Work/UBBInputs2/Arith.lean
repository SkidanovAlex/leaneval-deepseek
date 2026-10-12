import ChallengeDeps
import Submission.Work.UBBInputs2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs2.Arith` — the proved arithmetic of the Hamiltonian route

Every statement in this module is PROVED (`sorry`-free, axiom-clean).  They are
the FS arithmetic that carries the Hamiltonian-carrier inputs of
`Defs.lean` into the delivered assembly `Work.UBB.UBB_of_spectralH` /
`Work.UBB.Consumer.hpres_of_spectralH`:

* `lowStateH_iff_density` — FS `eq:aprioriPsi` in the density form
  (`Rayl/L³ − 8π(a v)ρ² ≤ Theta (a v) J ρ`) is the same hypothesis as the
  `H_Λ`-form `LowStateH`;
* `lambda_le_div_iff` — the (unnormalised) `Λ·L³ ≤ ⟨H_ΛΨ⟩` form and the
  (density) `Λ ≤ Rayl/L³ − 8π(a v)ρ²` form of the conclusion are the same
  inequality;
* `cnPlus_le_fsWindow_of_H` — FS's step
  `eq:BSsliding2 ⟹ eq:apriorinn+` at the Hamiltonian: the sliding input and the
  low-state condition give the FS window `fsWindow v b J K_B`;
* `spectralInputH_of_apriori_bog` — `AprioriNPlusH + BogoliubovLowH ⟹
  SpectralInputH` (FS's a-priori route, no word dictionary);
* `spectralInputH_of_locMatrices` — `LocMatricesResidual + BogoliubovWindowedH
  ⟹ SpectralInputH`, i.e. FS's `eq:LargeMatricesNew` absorption step: the
  located state's energy loss `4πρ²(a v)K(ρ(a v)³)^{1/2+η₀}L³` is *exactly* the
  shift `C ↦ C + K` of the `Λ`-coefficient, so the `lem:LocMatrices` error is
  paid for by the BOUND on `Λ` (larger `C` means smaller `Λ`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs2

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The two dictionary identities -/

/-- `Rayl/L³ − 8πAρ² = (Rayl − 8πAρ²L³)/L³`. -/
theorem div_sub_dens (A : ℝ) (N : ℕ) {L : ℝ} (hL : 0 < L) (R : ℝ) :
    R / L ^ 3 - 8 * π * A * (dens N L) ^ 2
      = (R - 8 * π * A * (dens N L) ^ 2 * L ^ 3) / L ^ 3 := by
  have h3 : L ^ 3 ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- **FS `eq:aprioriPsi` in its two equivalent forms**: the `H_Λ`-form
`LowStateH` (unnormalised) and the density form of FS is an inequality of the
shifted energy density. -/
theorem lowStateH_iff_density {v : ℝ³ → ℝ} {N : ℕ} {L J : ℝ} (hL : 0 < L)
    (Ψ : CInfty0Box N L) :
    LowStateH v N L J Ψ ↔
      Rayl N L v Ψ / L ^ 3 - 8 * π * (a v) * (dens N L) ^ 2
        ≤ Theta (a v) J (dens N L) := by
  unfold LowStateH
  have h3 : (0 : ℝ) < L ^ 3 := by positivity
  rw [div_sub_dens (a v) N hL (Rayl N L v Ψ), div_le_iff₀ h3]

/-- **The (unnormalised) `Λ`-form and the (density) `Λ`-form of the box
conclusion are the same inequality.**  This is the passage between
`BogoliubovLowH`'s `Λ·L³ ≤ ⟨H_ΛΨ⟩` and `SpectralInputH`'s
`Λ ≤ Rayl/L³ − 8π(a v)ρ²`. -/
theorem lambda_le_div_iff {A C η₀ ρ R L : ℝ} (hL : 0 < L) :
    Lambda A C η₀ ρ ≤ R / L ^ 3 - 8 * π * A * ρ ^ 2 ↔
      Lambda A C η₀ ρ * L ^ 3 ≤ R - 8 * π * A * ρ ^ 2 * L ^ 3 := by
  have h3 : (0 : ℝ) < L ^ 3 := by positivity
  have hkey : R / L ^ 3 - 8 * π * A * ρ ^ 2
      = (R - 8 * π * A * ρ ^ 2 * L ^ 3) / L ^ 3 := by
    field_simp
  rw [hkey, le_div_iff₀ h3]

/-! ## 2. FS `eq:BSsliding2 ⟹ eq:apriorinn+` at the Hamiltonian -/

/-- **FS's a-priori window from the sliding inequality** (the Hamiltonian
version of `Work.UBB.Apriori.cnPlus_le_window_of_low`, with the same pure
arithmetic): a low box state `Ψ` whose excited count is controlled by
`eq:BSsliding2` has at most `fsWindow v b J K_B N L` excited particles per unit
box norm,

`cnPlus L Ψ ≤ (2L²/b)·4πρ²(a v)L³(J+K_B³)(ρ(a v)³)^{1/2}·⟪Ψ,Ψ⟫_{N,L}`.

In the Hamiltonian normalisation this is a two-line linear computation: the
low condition bounds `⟨Ψ,H_Λ(ρ)Ψ⟩` above by `−4πρ²(a v)L³(1−J√(ρ(a v)³))`,
and the sliding inequality bounds `(b/2L²)(cnPlus/⟪Ψ,Ψ⟫)` above by
`⟨Ψ,H_Λ(ρ)Ψ⟩ − R' + 4πρ²(a v)L³(1+K_B³√(ρ(a v)³))`. -/
theorem cnPlus_le_fsWindow_of_H {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} (ha : 0 ≤ a v) (hb : 0 < b) (hR' : 0 ≤ R')
    (hslide : DLSlideCovH v h b K_B R' J ε₀) :
    AprioriNPlusH v h J (fsWindow v b J K_B) ε₀ := by
  intro L hL N hN Ψ hlow
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hspos : 0 < boxSq N L Ψ := boxSq_pos hLpos Ψ
  have hmain : (b / (2 * L ^ 2)) * (cnPlus L (Ψ : X N → ℝ) / boxSq N L Ψ)
      ≤ 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3 * ((J + K_B ^ 3)
          * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    have hsl' := hslide L hL N hN Ψ hlow
    have hth := hlow
    unfold LowStateH at hth
    simp only [Theta] at hth
    have hrw : Real.sqrt (dens N L * (a v) ^ 3)
        = (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    rw [hrw] at hth
    nlinarith [hsl', hth, hR']
  have hne : 0 < 2 * L ^ 2 / b := by positivity
  have hdiv : cnPlus L (Ψ : X N → ℝ) / boxSq N L Ψ ≤ fsWindow v b J K_B N L := by
    have h2 := mul_le_mul_of_nonneg_left hmain hne.le
    have heq : (2 * L ^ 2 / b)
        * ((b / (2 * L ^ 2)) * (cnPlus L (Ψ : X N → ℝ) / boxSq N L Ψ))
        = cnPlus L (Ψ : X N → ℝ) / boxSq N L Ψ := by
      field_simp
    rw [heq] at h2
    rw [fsWindow]
    refine le_trans h2 (le_of_eq ?_)
    ring
  rw [fsWindow]
  have h3 := mul_le_mul_of_nonneg_right hdiv hspos.le
  rw [fsWindow] at h3
  have heq2 : cnPlus L (Ψ : X N → ℝ) / boxSq N L Ψ * boxSq N L Ψ
      = cnPlus L (Ψ : X N → ℝ) := by
    field_simp
  rwa [heq2] at h3

/-! ## 3. The a-priori route and the `lem:LocMatrices` route -/

/-- **FS's a-priori route at the Hamiltonian**: the shared-window a-priori
bound and the Bogoliubov bound under that window give FS `eq:ToProve` on the
Hamiltonian carrier (`Work.UBB.SpectralInputH`), hence `UBB` and `hpres` by the
delivered `Work.UBB.Consumer.hpres_of_spectralH`.  **No word/Hamiltonian
dictionary is used** — residual (1) is not consumed. -/
theorem spectralInputH_of_apriori_bog {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (ha1 : AprioriNPlusH v h J W ε₀) (ha2 : BogoliubovLowH v h J W ε₀ η₀) :
    SpectralInputH v J ε₀ η₀ := by
  rcases ha2 with ⟨C, hC, ha2⟩
  refine ⟨C, hC, ?_⟩
  intro L hL N hN Ψ hlow
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hlowH : LowStateH v N L J Ψ := (lowStateH_iff_density hLpos Ψ).mpr hlow
  exact (lambda_le_div_iff (A := a v) (C := C) (η₀ := η₀) (ρ := dens N L)
    (R := Rayl N L v Ψ) hLpos).mpr
    (ha2 L hL N hN Ψ (ha1 L hL N hN Ψ hlowH) hlowH)

/-- **FS's `eq:LargeMatricesNew` step**: `lem:LocMatrices` + the windowed
Bogoliubov bound give FS `eq:ToProve` at the Hamiltonian.

The arithmetic is the *exact* absorption of the localisation loss: if `Ψ̃` has
`⟨H_ΛΨ̃⟩ ≤ ⟨H_ΛΨ⟩ + 4πρ²(a v)K(ρ(a v)³)^{1/2+η₀}L³` and
`Λ(a v) C₁ η₀ ρ·L³ ≤ ⟨H_ΛΨ̃⟩`, then
`Λ(a v) (C₁+K) η₀ ρ·L³ ≤ ⟨H_ΛΨ⟩`, because
`Λ(C₁+K) = Λ(C₁) − 4πρ²(a v)K(ρ(a v)³)^{1/2+η₀}` (the `Λ`-coefficient is
*negative* in the shift). -/
theorem spectralInputH_of_locMatrices {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (hLM : LocMatricesResidual v h J W ε₀ η₀)
    (hB : BogoliubovWindowedH v h J W ε₀ η₀) :
    SpectralInputH v J ε₀ η₀ := by
  rcases hLM with ⟨K, hK, hLM⟩
  rcases hB with ⟨C₁, hC₁, hB⟩
  refine ⟨C₁ + K, add_nonneg hC₁ hK, ?_⟩
  intro L hL N hN Ψ hlow
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hlowH : LowStateH v N L J Ψ := (lowStateH_iff_density hLpos Ψ).mpr hlow
  obtain ⟨Psit, hE, hwin⟩ := hLM L hL N hN Ψ hlowH
  have h1 := hB L hL N hN Psit hwin
  have hshift : Lambda (a v) (C₁ + K) η₀ (dens N L) * L ^ 3
      = Lambda (a v) C₁ η₀ (dens N L) * L ^ 3
        - 4 * π * (dens N L) ^ 2 * (a v) * K
            * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3 := by
    unfold Lambda
    ring
  refine (lambda_le_div_iff (A := a v) (C := C₁ + K) (η₀ := η₀) (ρ := dens N L)
    (R := Rayl N L v Ψ) hLpos).mpr ?_
  rw [hshift]
  linarith [h1, hE]

/-- **The a-priori window is a special case of `lem:LocMatrices`**: if every low
state already satisfies the window (`AprioriNPlusH`), then the located state
can be taken to be the state itself, at *zero* energy cost (`K = 0`).  Hence
`LocMatricesResidual` is a *weakening* of FS `eq:apriorinn+` and the
`lem:LocMatrices` route (`hpres_of_locMatrices`) is a strict generalisation of
the a-priori route (`hpres_of_HInputs`). -/
theorem locMatricesResidual_of_aprioriNPlusH {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ} (hA : AprioriNPlusH v h J W ε₀) :
    LocMatricesResidual v h J W ε₀ η₀ := by
  refine ⟨0, le_rfl, fun L hL N hN Ψ hlow => ⟨Ψ, ?_, hA L hL N hN Ψ hlow⟩⟩
  have h0 : 4 * π * (dens N L) ^ 2 * (a v) * 0
      * (dens N L * (a v) ^ 3) ^ (1 / 2 + η₀) * L ^ 3 = 0 := by ring
  rw [h0]
  linarith

/-- The windowed Bogoliubov bound is stronger than the low-state one (it does
not use the low-state hypothesis), so it gives FS §9–11 under the window:
`BogoliubovWindowedH ⟹ BogoliubovLowH`. -/
theorem bogoliubovLowH_of_windowed {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (hW : BogoliubovWindowedH v h J W ε₀ η₀) :
    BogoliubovLowH v h J W ε₀ η₀ := by
  rcases hW with ⟨C, hC, hW⟩
  exact ⟨C, hC, fun L hL N hN Ψ hwin _ => hW L hL N hN Ψ hwin⟩

/-- Window monotonicity: a larger window makes the a-priori input weaker. -/
theorem aprioriNPlusH_mono_window {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ : ℝ}
    {W W' : ℕ → ℝ → ℝ} (hW : ∀ N L, W N L ≤ W' N L)
    (hA : AprioriNPlusH v h J W ε₀) : AprioriNPlusH v h J W' ε₀ :=
  fun L hL N hN Ψ hlow => le_trans (hA L hL N hN Ψ hlow)
    (mul_le_mul_of_nonneg_right (hW N L)
      (le_of_lt (boxSq_pos (lt_of_lt_of_le one_pos hL) Ψ)))

/-- Window monotonicity for the windowed Bogoliubov input. -/
theorem bogoliubovWindowedH_mono_window {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W W' : ℕ → ℝ → ℝ} (hW : ∀ N L, W' N L ≤ W N L)
    (hB : BogoliubovWindowedH v h J W ε₀ η₀) :
    BogoliubovWindowedH v h J W' ε₀ η₀ := by
  rcases hB with ⟨C, hC, hB⟩
  exact ⟨C, hC, fun L hL N hN Ψ hwin =>
    hB L hL N hN Ψ (le_trans hwin (mul_le_mul_of_nonneg_right (hW N L)
      (le_of_lt (boxSq_pos (lt_of_lt_of_le one_pos hL) Ψ))))⟩

/-- The same monotonicity for the low-state Bogoliubov input (again the window
is a *hypothesis*, so a smaller window is a stronger input). -/
theorem bogoliubovLowH_mono_window {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W W' : ℕ → ℝ → ℝ} (hW : ∀ N L, W' N L ≤ W N L)
    (hB : BogoliubovLowH v h J W ε₀ η₀) :
    BogoliubovLowH v h J W' ε₀ η₀ := by
  rcases hB with ⟨C, hC, hB⟩
  exact ⟨C, hC, fun L hL N hN Ψ hwin hlow =>
    hB L hL N hN Ψ (le_trans hwin (mul_le_mul_of_nonneg_right (hW N L)
      (le_of_lt (boxSq_pos (lt_of_lt_of_le one_pos hL) Ψ)))) hlow⟩

/-- Window monotonicity for `LocMatricesResidual`. -/
theorem locMatricesResidual_mono_window {v : ℝ³ → ℝ} {h : ScatSol v}
    {J ε₀ η₀ : ℝ} {W W' : ℕ → ℝ → ℝ} (hW : ∀ N L, W N L ≤ W' N L)
    (hL : LocMatricesResidual v h J W ε₀ η₀) :
    LocMatricesResidual v h J W' ε₀ η₀ := by
  rcases hL with ⟨K, hK, hL⟩
  exact ⟨K, hK, fun L hL' N hN Ψ hlow => by
    obtain ⟨Psit, hE, hwin⟩ := hL L hL' N hN Ψ hlow
    exact ⟨Psit, hE, le_trans hwin (mul_le_mul_of_nonneg_right (hW N L)
      (le_of_lt (boxSq_pos (lt_of_lt_of_le one_pos hL') Psit)))⟩⟩

end Work.UBBInputs2
