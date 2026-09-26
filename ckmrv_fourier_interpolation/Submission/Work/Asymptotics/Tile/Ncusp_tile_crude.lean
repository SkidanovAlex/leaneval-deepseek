import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.KMinusFunnelSlash
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.Tile.z_atoms
import Submission.Work.Asymptotics.Tile.tile_tau_atoms

/-!
# The crude tile bound for the cleared numerator `Ncusp`

On the cusp-`±1` tiles `τ = n +ᵥ w` (`n = ±1`, `w` in the cusp-`0` neighbourhood
`E = KEpsilon`) the cleared cusp numerator `Ncusp ℓ d τ z` is bounded by

`C (scale w)^N e^{c Im (S • w)} e^{π Im z}`,   `c < 2π`,

uniformly for `1 ≤ Im z`.  This is the hypothesis of the Schwarz upgrade
`Work.Asymptotics.Tile.Ncusp_tile_sharp`.

The proof reads the exact cancelled forms of the `z`-factor of `Ncusp`
(`T8_cancelled`, `T24_cancelled`) and estimates every factor:

* `τ`-atoms (`E₄, E₆, E₈, E₁₀, Δ, ψ₂, ψ₄` bounded by `(scale w)^N`, `Δ⁻¹` and `j` by
  `(scale w)^N e^{2π Im (S • w)}`, `j·Δ` by `(scale w)^N`) come from
  `Work.Asymptotics.Tile.tile_tau_atoms` and `EtailE.E_bdd_j_Delta`;
* the combination `ψ₄E₈ - ψ₂E₁₀` at the tile is `≲ (scale w)^N e^{-δ Im (S • w)}` with
  `δ > 0` by the hypothesis `hF`;
* `z`-atoms come from `Work.Asymptotics.Tile.z_atoms`.

All factors are handled by the bookkeeping predicate `Sh` below: `Sh a b F` records
`‖F (n +ᵥ w) z‖ ≤ C (scale w)^N e^{a Im (S • w) + b Im z}`, which is closed under sums,
products, scalar multiples and monotone weakening of `(a, b)`.
-/

set_option maxHeartbeats 1600000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold

noncomputable section

/-- The bound shape on the cusp-`±1` tiles: `‖F (n +ᵥ w) z‖ ≤ C (scale w)^N e^{a Im (S w) + b Im z}`
for `n = ±1`, `w ∈ E` and `Im z ≥ 1`. -/
def Sh (a b : ℝ) (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ) (z : ℍ), (n = 1 ∨ n = -1) →
    w ∈ Work.Asymptotics.KEpsilon → 1 ≤ z.im →
    ‖F ((n : ℝ) +ᵥ w) z‖
      ≤ C * (Work.Kernels.scale w) ^ N
          * Real.exp (a * (ModularGroup.S • w).im + b * z.im)

lemma Sh.mono {a b a' b' : ℝ} {F : ℍ → ℍ → ℂ} (h : Sh a b F) (ha : a ≤ a') (hb : b ≤ b') :
    Sh a' b' F := by
  obtain ⟨C, N, hC, hN, hle⟩ := h
  refine ⟨C, N, hC, hN, fun w n z hn hw hz => ?_⟩
  have hS : 0 ≤ (ModularGroup.S • w).im := le_trans (by norm_num) hw.2
  have hz0 : 0 ≤ z.im := le_trans (by norm_num) hz
  have hexp : a * (ModularGroup.S • w).im + b * z.im
      ≤ a' * (ModularGroup.S • w).im + b' * z.im :=
    add_le_add (mul_le_mul_of_nonneg_right ha hS) (mul_le_mul_of_nonneg_right hb hz0)
  refine le_trans (hle w n z hn hw hz) ?_
  have hC0 : 0 ≤ C * (Work.Kernels.scale w) ^ N :=
    mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC0

lemma Sh.congr {a b : ℝ} {F G : ℍ → ℍ → ℂ} (h : ∀ τ z, F τ z = G τ z) (hG : Sh a b G) :
    Sh a b F := by
  obtain ⟨C, N, hC, hN, hle⟩ := hG
  exact ⟨C, N, hC, hN, fun w n z hn hw hz => by rw [h]; exact hle w n z hn hw hz⟩

lemma Sh.add {a b : ℝ} {F G : ℍ → ℍ → ℂ} (hF : Sh a b F) (hG : Sh a b G) :
    Sh a b (fun τ z => F τ z + G τ z) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, by linarith, le_max_of_le_left hN1, fun w n z hn hw hz => ?_⟩
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hN1' : (Work.Kernels.scale w) ^ N1 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hN2' : (Work.Kernels.scale w) ^ N2 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hE : 0 ≤ Real.exp (a * (ModularGroup.S • w).im + b * z.im) := Real.exp_nonneg _
  have hm1 : C1 * (Work.Kernels.scale w) ^ N1 * Real.exp (a * (ModularGroup.S • w).im + b * z.im)
      ≤ C1 * (Work.Kernels.scale w) ^ (max N1 N2)
          * Real.exp (a * (ModularGroup.S • w).im + b * z.im) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN1' hC1.le) hE
  have hm2 : C2 * (Work.Kernels.scale w) ^ N2 * Real.exp (a * (ModularGroup.S • w).im + b * z.im)
      ≤ C2 * (Work.Kernels.scale w) ^ (max N1 N2)
          * Real.exp (a * (ModularGroup.S • w).im + b * z.im) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2' hC2.le) hE
  have hsplit : (C1 + C2) * (Work.Kernels.scale w) ^ (max N1 N2)
        * Real.exp (a * (ModularGroup.S • w).im + b * z.im)
      = C1 * (Work.Kernels.scale w) ^ (max N1 N2)
          * Real.exp (a * (ModularGroup.S • w).im + b * z.im)
        + C2 * (Work.Kernels.scale w) ^ (max N1 N2)
          * Real.exp (a * (ModularGroup.S • w).im + b * z.im) := by ring
  calc ‖F ((n : ℝ) +ᵥ w) z + G ((n : ℝ) +ᵥ w) z‖
      ≤ ‖F ((n : ℝ) +ᵥ w) z‖ + ‖G ((n : ℝ) +ᵥ w) z‖ := norm_add_le _ _
    _ ≤ C1 * (Work.Kernels.scale w) ^ N1 * Real.exp (a * (ModularGroup.S • w).im + b * z.im)
        + C2 * (Work.Kernels.scale w) ^ N2 * Real.exp (a * (ModularGroup.S • w).im + b * z.im) :=
        add_le_add (h1 w n z hn hw hz) (h2 w n z hn hw hz)
    _ ≤ (C1 + C2) * (Work.Kernels.scale w) ^ (max N1 N2)
          * Real.exp (a * (ModularGroup.S • w).im + b * z.im) := by
        rw [hsplit]; exact add_le_add hm1 hm2

lemma Sh.mul {a b a' b' : ℝ} {F G : ℍ → ℍ → ℂ} (hF : Sh a b F) (hG : Sh a' b' G) :
    Sh (a + a') (b + b') (fun τ z => F τ z * G τ z) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := hF
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, by positivity, by positivity, fun w n z hn hw hz => ?_⟩
  have hs0 : 0 < Work.Kernels.scale w := Work.Kernels.scale_pos w
  rw [norm_mul]
  have e1 := h1 w n z hn hw hz
  have e2 := h2 w n z hn hw hz
  have h1nonneg : (0 : ℝ) ≤ C1 * (Work.Kernels.scale w) ^ N1
      * Real.exp (a * (ModularGroup.S • w).im + b * z.im) :=
    mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg hs0.le N1)) (Real.exp_nonneg _)
  have h2nonneg : (0 : ℝ) ≤ C2 * (Work.Kernels.scale w) ^ N2
      * Real.exp (a' * (ModularGroup.S • w).im + b' * z.im) :=
    mul_nonneg (mul_nonneg hC2.le (Real.rpow_nonneg hs0.le N2)) (Real.exp_nonneg _)
  have hexp : Real.exp (a * (ModularGroup.S • w).im + b * z.im)
        * Real.exp (a' * (ModularGroup.S • w).im + b' * z.im)
      = Real.exp ((a + a') * (ModularGroup.S • w).im + (b + b') * z.im) := by
    rw [← Real.exp_add]; ring_nf
  have hrpow : (Work.Kernels.scale w) ^ N1 * (Work.Kernels.scale w) ^ N2
      = (Work.Kernels.scale w) ^ (N1 + N2) := (Real.rpow_add hs0 N1 N2).symm
  calc ‖F ((n : ℝ) +ᵥ w) z‖ * ‖G ((n : ℝ) +ᵥ w) z‖
      ≤ (C1 * (Work.Kernels.scale w) ^ N1
            * Real.exp (a * (ModularGroup.S • w).im + b * z.im))
          * (C2 * (Work.Kernels.scale w) ^ N2
            * Real.exp (a' * (ModularGroup.S • w).im + b' * z.im)) :=
        mul_le_mul e1 e2 (norm_nonneg _) h1nonneg
    _ = C1 * C2 * (Work.Kernels.scale w) ^ (N1 + N2)
          * Real.exp ((a + a') * (ModularGroup.S • w).im + (b + b') * z.im) := by
        rw [show C1 * (Work.Kernels.scale w) ^ N1
              * Real.exp (a * (ModularGroup.S • w).im + b * z.im)
              * (C2 * (Work.Kernels.scale w) ^ N2
                * Real.exp (a' * (ModularGroup.S • w).im + b' * z.im))
            = C1 * C2 * ((Work.Kernels.scale w) ^ N1 * (Work.Kernels.scale w) ^ N2)
              * (Real.exp (a * (ModularGroup.S • w).im + b * z.im)
                * Real.exp (a' * (ModularGroup.S • w).im + b' * z.im)) from by ring,
          hrpow, hexp]

lemma Sh.const_mul (k : ℂ) {a b : ℝ} {F : ℍ → ℍ → ℂ} (hF : Sh a b F) :
    Sh a b (fun τ z => k * F τ z) := by
  obtain ⟨C, N, hC, hN, hle⟩ := hF
  have hCpos : (0 : ℝ) < (‖k‖ + 1) * C := by
    have hk := norm_nonneg k
    nlinarith [hC, hk]
  refine ⟨(‖k‖ + 1) * C, N, hCpos, hN, fun w n z hn hw hz => ?_⟩
  rw [norm_mul]
  have h0 : 0 ≤ C * (Work.Kernels.scale w) ^ N
      * Real.exp (a * (ModularGroup.S • w).im + b * z.im) :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N))
      (Real.exp_nonneg _)
  have h1 : ‖k‖ * ‖F ((n : ℝ) +ᵥ w) z‖
      ≤ ‖k‖ * (C * (Work.Kernels.scale w) ^ N
          * Real.exp (a * (ModularGroup.S • w).im + b * z.im)) :=
    mul_le_mul_of_nonneg_left (hle w n z hn hw hz) (norm_nonneg k)
  refine le_trans h1 ?_
  have h2 : (0 : ℝ) ≤ Real.exp (a * (ModularGroup.S • w).im + b * z.im) := Real.exp_nonneg _
  have h3 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos w).le N
  nlinarith [h0, h2, h3, hC.le, norm_nonneg k]

lemma Sh.div {a b a' b' : ℝ} {F G : ℍ → ℍ → ℂ}
    (hF : Sh a b F) (hGi : Sh a' b' (fun τ z => (G τ z)⁻¹)) :
    Sh (a + a') (b + b') (fun τ z => F τ z / G τ z) :=
  Sh.congr (fun τ z => by rw [div_eq_mul_inv]) (hF.mul hGi)

lemma Sh.one : Sh 0 0 (fun (_ : ℍ) (_ : ℍ) => (1 : ℂ)) := by
  refine ⟨1, 0, one_pos, le_refl 0, fun w n z hn hw hz => ?_⟩
  simp

/-- A `z`-atom bounded by a constant. -/
lemma Sh.of_zatom {A : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖A z‖ ≤ C) : Sh 0 0 (fun (_ : ℍ) z => A z) := by
  refine ⟨C, 0, hC, le_refl 0, fun w n z hn hw hz => ?_⟩
  simpa only [zero_mul, add_zero, Real.exp_zero, mul_one, Real.rpow_zero] using h z hz

/-- A `z`-atom decaying like `e^{a Im z}`. -/
lemma Sh.of_zatom_exp {A : ℍ → ℂ} {C a : ℝ} (hC : 0 < C)
    (h : ∀ z : ℍ, 1 ≤ z.im → ‖A z‖ ≤ C * Real.exp (a * z.im)) :
    Sh 0 a (fun (_ : ℍ) z => A z) := by
  refine ⟨C, 0, hC, le_refl 0, fun w n z hn hw hz => ?_⟩
  simpa only [zero_mul, zero_add, add_zero, Real.exp_zero, mul_one, Real.rpow_zero,
    neg_mul] using h z hz

/-- A `τ`-atom bounded by `(scale w)^N` at the tiles `n +ᵥ w`. -/
lemma Sh.of_tau_atom {A : ℍ → ℂ} {C N : ℝ} (hC : 0 < C) (hN : 0 ≤ N)
    (h : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖A ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N) :
    Sh 0 0 (fun τ (_ : ℍ) => A τ) := by
  refine ⟨C, N, hC, hN, fun w n z hn hw hz => ?_⟩
  simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using h w n hn hw

/-- A `τ`-atom bounded by `(scale w)^N e^{a Im (S w)}` at the tiles `n +ᵥ w`. -/
lemma Sh.of_tau_atom_exp {A : ℍ → ℂ} {C N a : ℝ} (hC : 0 < C) (hN : 0 ≤ N)
    (h : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖A ((n : ℝ) +ᵥ w)‖ ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (a * (ModularGroup.S • w).im)) :
    Sh a 0 (fun τ (_ : ℍ) => A τ) := by
  refine ⟨C, N, hC, hN, fun w n z hn hw hz => ?_⟩
  simpa only [zero_mul, add_zero] using h w n hn hw

/-- A `T`-invariant function is unchanged by the translation `n +ᵥ ·` for `n = ±1`. -/
lemma vadd_int_eq_self (F : ℍ → ℂ) (hF : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ)
    (n : ℤ) (hn : n = 1 ∨ n = -1) (w : ℍ) : F ((n : ℝ) +ᵥ w) = F w := by
  rcases hn with h | h
  · rw [h, Int.cast_one]; exact hF w
  · rw [h, Int.cast_neg, Int.cast_one]
    have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w := by rw [← add_vadd]; norm_num
    have h4 := hF ((-1 : ℝ) +ᵥ w)
    rw [h3] at h4
    exact h4.symm


/-- The crude tile bound for the cleared cusp numerator `Ncusp` on the cusp-`±1` tiles. -/
theorem Ncusp_tile_crude (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hF : ∃ CF NF δ : ℝ, 0 < CF ∧ 0 ≤ NF ∧ 0 < δ ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)
          - Work.Kernels.psi2 ℓ ((n : ℝ) +ᵥ w) * Work.Kernels.E10Fun ((n : ℝ) +ᵥ w)‖
        ≤ CF * (Work.Kernels.scale w) ^ NF * Real.exp (-(δ * (ModularGroup.S • w).im))) :
    ∃ c C N : ℝ, 0 ≤ c ∧ c < 2 * Real.pi ∧ 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ z : UpperHalfPlane, 1 ≤ z.im →
          ‖Work.Asymptotics.Ncusp ℓ d ((n : ℝ) +ᵥ w) z‖
            ≤ C * (Work.Kernels.scale w) ^ N * Real.exp (c * (ModularGroup.S • w).im)
                * Real.exp (Real.pi * z.im) := by
  obtain ⟨CF, NF, δ, hCF, hNF, hδ, hFb⟩ := hF
  obtain ⟨CT, NT, hCT, hNT, hT⟩ := tile_tau_atoms ℓ
  obtain ⟨CZ, hCZ, hE4z, hE6z, hE8z, hE10z, hE14z, hUz, hWz, hVz, hUWz, hLSz,
    hDinvz, hjz, hE14dz, hE10dz⟩ := z_atoms ℓ
  -- the `τ`-atoms at the tiles
  have hE4T : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E4Fun ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).1
  have hE8T : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.E8Fun ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).2.2.1
  have hDelT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.1
  have hpsi4T : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.psi4 ℓ ((n : ℝ) +ᵥ w)‖ ≤ CT * (Work.Kernels.scale w) ^ NT :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.2.2.1
  have hDinvT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖(Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w))⁻¹‖
        ≤ CT * (Work.Kernels.scale w) ^ NT * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.2.2.2.1
  have hjT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)‖
        ≤ CT * (Work.Kernels.scale w) ^ NT * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) :=
    fun w n hn hw => (hT w n hn hw).2.2.2.2.2.2.2.2
  -- `j · Δ` is moderate
  have hjD : Work.Asymptotics.EtailE.Bdd 0
      (fun w : ℍ => Work.Kernels.jInvariantFun w * Work.Kernels.DeltaFun w) :=
    Work.Asymptotics.EtailE.Bdd.mono (c := 2 * Real.pi + -(2 * Real.pi)) (c' := 0)
      (by linarith [Real.pi_pos])
      ((Work.Asymptotics.EtailE.E_bdd_j).mul Work.Asymptotics.EtailE.E_bdd_Delta)
  obtain ⟨CjD, NjD, hCjD, hNjD, hjDb⟩ := hjD
  have hjDT : ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) * Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w)‖
        ≤ CjD * (Work.Kernels.scale w) ^ NjD := by
    intro w n hn hw
    have h := hjDb w hw
    have h1 : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
        = Work.Kernels.jInvariantFun w :=
      vadd_int_eq_self _ (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ) n hn w
    have h2 : Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w) = Work.Kernels.DeltaFun w :=
      vadd_int_eq_self _ (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ) n hn w
    rw [h1, h2]
    simpa only [zero_mul, Real.exp_zero, mul_one] using h
  -- `Sh` instances for the `τ`-atoms
  have sE4 : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.E4Fun τ) :=
    Sh.of_tau_atom hCT hNT hE4T
  have sE8 : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.E8Fun τ) :=
    Sh.of_tau_atom hCT hNT hE8T
  have sDel : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.DeltaFun τ) :=
    Sh.of_tau_atom hCT hNT hDelT
  have spsi4 : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.psi4 ℓ τ) :=
    Sh.of_tau_atom hCT hNT hpsi4T
  have sDeli : Sh (2 * Real.pi) 0 (fun τ (_ : ℍ) => (Work.Kernels.DeltaFun τ)⁻¹) :=
    Sh.of_tau_atom_exp hCT hNT hDinvT
  have sj : Sh (2 * Real.pi) 0 (fun τ (_ : ℍ) => Work.Kernels.jInvariantFun τ) :=
    Sh.of_tau_atom_exp hCT hNT hjT
  have sjDel : Sh 0 0 (fun τ (_ : ℍ) => Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ) :=
    Sh.of_tau_atom hCjD hNjD hjDT
  have sF : Sh (-δ) 0 (fun τ (_ : ℍ) =>
      Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) := by
    refine ⟨CF, NF, hCF, hNF, fun w n z hn hw hz => ?_⟩
    simpa only [zero_mul, add_zero, neg_mul] using hFb w n hn hw
  -- `Sh` instances for the `z`-atoms
  have zE6 : Sh 0 0 (fun (_ : ℍ) z => Work.Kernels.E6Fun z) := Sh.of_zatom hCZ hE6z
  have zE8 : Sh 0 0 (fun (_ : ℍ) z => Work.Kernels.E8Fun z) := Sh.of_zatom hCZ hE8z
  have zE10 : Sh 0 0 (fun (_ : ℍ) z => Work.Kernels.E10Fun z) := Sh.of_zatom hCZ hE10z
  have zV : Sh 0 (-Real.pi) (fun (_ : ℍ) z => Work.Kernels.VFun z) :=
    Sh.of_zatom_exp hCZ (fun z hz => by simpa only [neg_mul] using hVz z hz)
  have zUW : Sh 0 (-Real.pi) (fun (_ : ℍ) z => Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2) :=
    Sh.of_zatom_exp hCZ (fun z hz => by simpa only [neg_mul] using hUWz z hz)
  have zLS : Sh 0 (-Real.pi) (fun (_ : ℍ) z => ℓ.L_S z) :=
    Sh.of_zatom_exp hCZ (fun z hz => by simpa only [neg_mul] using hLSz z hz)
  have zDinv : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => (Work.Kernels.DeltaFun z)⁻¹) :=
    Sh.of_zatom_exp hCZ hDinvz
  have zj : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => Work.Kernels.jInvariantFun z) :=
    Sh.of_zatom_exp hCZ hjz
  have zE14d : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) :=
    Sh.of_zatom_exp hCZ hE14dz
  have zE10d : Sh 0 (2 * Real.pi) (fun (_ : ℍ) z => Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z) :=
    Sh.of_zatom_exp hCZ hE10dz
  -- the common exponents
  have hc0 : 0 ≤ max 0 (2 * Real.pi - δ) := le_max_left _ _
  have hclt : max 0 (2 * Real.pi - δ) < 2 * Real.pi :=
    max_lt (by linarith [Real.pi_pos]) (by linarith [hδ])
  have hpi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hmax2 : 2 * Real.pi - δ ≤ max 0 (2 * Real.pi - δ) := le_max_right _ _
  rcases hd with rfl | rfl
  · -- ## `d = 8`
    have hT8 : Sh (max 0 (2 * Real.pi - δ)) Real.pi (fun τ z => T8 ℓ τ z) := by
      have t1 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-3456) (sE4.mul (zE10.mul zLS))).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      have t2 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (Work.Kernels.E8Fun z * Work.Kernels.VFun z
                + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
              * (Work.Kernels.E4Fun τ
                * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                / Work.Kernels.DeltaFun τ)) := by
        refine Sh.congr (fun τ z => by ring) (((zE8.mul zV).add (zE6.mul zUW)).mul
          ((sE4.mul sF).div sDeli) |>.mono ?_ (by linarith [Real.pi_pos]))
        linarith [hmax2]
      have t3 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z
              * Work.Kernels.VFun z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-1728) ((spsi4.mul zE8).mul zV)).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      exact Sh.congr (fun τ z => by rw [T8_cancelled ℓ τ z]; ring) (t1.add (t2.add t3))
    have hN : Sh (max 0 (2 * Real.pi - δ)) Real.pi (fun τ z => Ncusp ℓ 8 τ z) :=
      Sh.congr (fun τ z => Ncusp_eight_expansion ℓ τ z)
        (Sh.const_mul ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) hT8)
    obtain ⟨C, N, hC, hNn, hle⟩ := hN
    refine ⟨max 0 (2 * Real.pi - δ), C, N, hc0, hclt, hC, hNn, fun w n hn hw z hz => ?_⟩
    refine le_trans (hle w n z hn hw hz) (le_of_eq ?_)
    rw [Real.exp_add]; ring
  · -- ## `d = 24`
    have hT24 : Sh (max 0 (2 * Real.pi - δ)) Real.pi (fun τ z => T24 ℓ τ z) := by
      have u1 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-3456) ((sDel.mul zE14d).mul zLS)).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      have u2 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (3456 : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ
              * Work.Kernels.VFun z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul 3456 (sjDel.mul zV)).mono (by linarith [hc0]) (by linarith [Real.pi_pos]))
      have u3 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (-3456 : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun z
              * Work.Kernels.VFun z) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-3456) (sDel.mul (zj.mul zV))).mono (by linarith [hc0]) (by linarith [Real.pi_pos]))
      have u4 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (2 : ℂ)
              * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                  * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z) := by
        refine Sh.congr (fun τ z => by ring)
          ((Sh.const_mul 2 ((sF.mul sj).mul zV)).mono ?_ (by linarith [Real.pi_pos]))
        linarith [hmax2]
      have u5 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (-2 : ℂ)
              * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                  * Work.Kernels.jInvariantFun z) * Work.Kernels.VFun z) := by
        refine Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-2) ((sF.mul zj).mul zV)).mono ?_ (by linarith [Real.pi_pos]))
        have h2 : (-δ : ℝ) ≤ max 0 (2 * Real.pi - δ) := by linarith [hc0, hδ]
        linarith
      have u6 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * Work.Kernels.jInvariantFun τ * Work.Kernels.VFun z) := by
        refine Sh.congr (fun τ z => by ring)
          (((sF.mul sj).mul zV).mono ?_ (by linarith [Real.pi_pos]))
        linarith [hmax2]
      have u7 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ
              * (Work.Kernels.E8Fun τ * Work.Kernels.VFun z)) :=
        Sh.congr (fun τ z => by ring)
          ((Sh.const_mul (-1728) (spsi4.mul (sE8.mul zV))).mono (by linarith [hc0])
            (by linarith [Real.pi_pos]))
      have u8 : Sh (max 0 (2 * Real.pi - δ)) Real.pi
          (fun τ z => (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
              * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)) := by
        refine Sh.congr (fun τ z => by ring)
          ((sF.mul (zE10d.mul zUW)).mono ?_ (by linarith [Real.pi_pos]))
        have h2 : (-δ : ℝ) ≤ max 0 (2 * Real.pi - δ) := by linarith [hc0, hδ]
        linarith
      exact Sh.congr (fun τ z => by rw [T24_cancelled ℓ τ z]; ring)
        (Sh.add (Sh.add (Sh.add (Sh.add (Sh.add (Sh.add (Sh.add u1 u2) u3) u4) u5) u6)
          u7) u8)
    have hN : Sh (max 0 (2 * Real.pi - δ)) Real.pi (fun τ z => Ncusp ℓ 24 τ z) :=
      Sh.congr (fun τ z => Ncusp_twentyfour_expansion ℓ τ z)
        (Sh.const_mul ((2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹) hT24)
    obtain ⟨C, N, hC, hNn, hle⟩ := hN
    refine ⟨max 0 (2 * Real.pi - δ), C, N, hc0, hclt, hC, hNn, fun w n hn hw z hz => ?_⟩
    refine le_trans (hle w n z hn hw hz) (le_of_eq ?_)
    rw [Real.exp_add]; ring

end

end Work.Asymptotics.Tile
