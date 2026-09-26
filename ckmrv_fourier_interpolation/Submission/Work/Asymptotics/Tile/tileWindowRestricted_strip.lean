/-
# The resonant strip of the tile deviation (cusp-`±1` tiles)

Target: `Work.Asymptotics.Tile.tileWindowRestricted_strip` (the statement below):
for `w ∈ E = KEpsilon` with `Re w ≠ 0`, `n = ±1` and `t` in the resonant strip
`|t − Im (S • w)| ≤ 1` the CKMRV kernel differs from its cusp model by a polynomial.

## What is proved here

* `Work.Asymptotics.Tile.phi_Tpow_S_eq_zero` (proved): `φ (T^k · S) = 0` for every `k : ℤ`
  (computation of the `(0,1)`-entry of the six-dimensional representation `σ_R`).
* `Work.Asymptotics.Tile.tile_KfunClear_self_S_vanish` (proved): the missing `m = 0` case of
  `Work.Asymptotics.Tile.tile_KfunClear_shift_vanish`, namely
  `KfunClear ℓ d (n +ᵥ σ) (S • σ) = 0` for `n = ±1`.  Together with the proved `m = ±1` cases
  this gives the three zeros `KfunClear ℓ d τ (σ + k) = 0` (`k ∈ {-1,0,1}`) of the second
  variable slice at the resonant points `σ + k` of the orbit `Γ (n +ᵥ w)`.

## The remaining gap (route, for the next stretch)

The strip bound is the "below-pole window" of the tile and the crux of the CKMRV tile
analysis.  The workspace's proved sharp tails
(`KPlusTileTailSharp`/`KMinusTileTailSharp`) bound the half-kernel deviations only for
`t ≥ Im (S • w) + 1` (they divide by `Sh = -Δ(z)(j τ - j z)`, which is bounded below by `1/16`
only above the poles).  In the strip the individual half-kernel deviations blow up (the two
half-kernels have opposite residues at the crossed points, `AfunFun_crossed_vanish`), so only
the **cleared** combination

  `N := Sh(τ,ζ)·(K_+ - 𝒢_+)(τ,ζ) + Sh(τ,ζ)·(K_- - 𝒢_-)(τ,ζ) = 2·Sh(τ,ζ)·(K - Gfun)(τ,ζ)`

is polynomially bounded on the ball `‖ζ - S • w‖ ≤ 29/20`; `N` is holomorphic in `ζ` and
vanishes at `ζ = S•w + k` (`k ∈ {-1,0,1}`) — the three zeros established above.  Given the
ball bound for `N` (the two cleared-deviation bounds), the statement follows by
`Work.Analysis.ThreeZeros.three_zeros_bound_ball` (the three-zeros maximum-modulus estimate),
the divisor lower bounds `SpikeCircle.divisorLowerDisc` / `SpikeCircle.DeltaFunBoundsHalf`
(for `‖Δ(ζ)(j τ - j ζ)‖ ≥ c e^{-2π Im ζ} e^{2π Im(S•w)} ‖ζ - S•w‖`), the clearing identity
`KfunClear_eq_growthPrefactor_mul` and the identification `Aexp_Gcusp_eq_Gfun`.

The cleared deviation bounds themselves are the *reference-expansion* content
(`Compact.tail_identity`, `kmfd_bracket_decomp`, `kmfd_BR_expansion`, `TBM.ktl_G8/G24`):
the bracket is a finite combination of `(Ept ζ)^k ·(τ-atoms)`, whose weights satisfy
`a ≤ bπ`, so that on the *whole* strip `t ≥ Im(S•w) - 1` (not only above the poles) the
factors `e^{a Im(S•w) - b π t} ≤ e^{bπ}` are bounded.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.Tile.tileWinDefs
import Submission.Work.Asymptotics.Tile.tile_KfunClear_shift_vanish
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Analysis.ThreeZeros.three_zeros_bound_ball
import Submission.Work.Asymptotics.Tile.tile_Kfun_near
import Submission.Work.Asymptotics.Tile.tile_Kfun_far
import Submission.Work.Asymptotics.Tile.tile_dev_aux
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc
import Submission.Work.Asymptotics.Tile.tileNumBallBoundA

set_option maxHeartbeats 3200000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

/-- **`φ (T^k · S) = 0`.**  The functional `φ` of CKMRV (3.12) annihilates the monomial
`T^k S` for every `k : ℤ`.  (The proof is the computation
`(σ_R (T^k S)) 0 1 = Σ_j (σ_R (T^k))_{0j} (σ_R S)_{j1} = 0`, since the row `0` of `σ_R (T^k)` is
`(1-k, k, 0, 0, 0, 0)` and the column `1` of `σ_R S` has its only nonzero entry in row `2`.) -/
theorem phi_Tpow_S_eq_zero (k : ℤ) :
    Work.Residues.phi
      (MonoidAlgebra.single (ModularGroup.T ^ k * ModularGroup.S) (1 : ℂ)) = 0 := by
  have hsplit : MonoidAlgebra.single (ModularGroup.T ^ k * ModularGroup.S) (1 : ℂ)
      = MonoidAlgebra.single (ModularGroup.T ^ k) (1 : ℂ)
        * MonoidAlgebra.single ModularGroup.S (1 : ℂ) := by
    rw [MonoidAlgebra.single_mul_single, mul_one]
  rw [hsplit, Work.Residues.phi_eq_sigmaR, map_mul]
  have hS : Work.Residues.sigmaR (MonoidAlgebra.single ModularGroup.S (1 : ℂ)) =
      Work.Modular.sigmaS :=
    Work.Residues.sigmaR_R_S
  have hrow := Work.Residues.sigmaR_single_T_zpow_row0 k
  rw [hS, Matrix.mul_apply, Fin.sum_univ_six, hrow]
  simp [Work.Modular.sigmaS]

/-- **The `m = 0` branch of the vanishing of the cleared kernel.**  For `n = ±1` and any
`σ ∈ ℍ` the cleared CKMRV kernel vanishes at the pair `(n +ᵥ σ, S • σ)`.

This is the missing case `m = 0` of `Work.Asymptotics.Tile.tile_KfunClear_shift_vanish`; the
group element is `δ = T^n * S` (one lone `S`), whose `φ`-value vanishes by
`Work.Asymptotics.Tile.phi_Tpow_S_eq_zero`. -/
theorem tile_KfunClear_self_S_vanish (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (n : ℤ) (hn : n = 1 ∨ n = -1) (σ : UpperHalfPlane) :
    Work.Kernels.KfunClear ℓ d ((n : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
  set δ : SL(2, ℤ) := ModularGroup.T ^ n * ModularGroup.S with hδdef
  have hphi : Work.Residues.phi (MonoidAlgebra.single δ (1 : ℂ)) = 0 := by
    rw [hδdef]; exact phi_Tpow_S_eq_zero n
  have hδpair : Work.Residues.phiPlus (MonoidAlgebra.single δ (1 : ℂ))
      + Work.Residues.phiMinus (MonoidAlgebra.single δ (1 : ℂ)) = 0 := by
    have h := Work.Residues.phi_eq_half_phiPlus_add_phiMinus (MonoidAlgebra.single δ (1 : ℂ))
    rw [hphi] at h
    rcases div_eq_zero_iff.mp h.symm with h0 | h2
    · exact h0
    · exact absurd h2 (by norm_num)
  have hz : δ • (ModularGroup.S • σ) = (n : ℝ) +ᵥ σ := by
    rw [hδdef, mul_smul, S_smul_S_smul, UpperHalfPlane.modular_T_zpow_smul]
  have hv := Work.Asymptotics.Graze.KfunClear_vanish_of_phiPair_uncond ℓ d hd δ hδpair
    (ModularGroup.S • σ)
  rw [hz] at hv
  exact hv

/-- **The three resonant zeros of the cleared kernel at the tile.**  For `w ∈ E`, `n = ±1` and
`k ∈ {-1,0,1}` the second-variable slice `ζ ↦ KfunClear ℓ d (n +ᵥ w) ζ` vanishes at
`ζ = k +ᵥ (S • w)`. -/
theorem tile_KfunClear_strip_zeros (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (k : ℤ) (hk : k = -1 ∨ k = 0 ∨ k = 1) :
    Work.Kernels.KfunClear ℓ d ((n : ℝ) +ᵥ w) ((k : ℝ) +ᵥ (ModularGroup.S • w)) = 0 := by
  rcases hk with h | h | h
  · subst h; exact tile_KfunClear_shift_vanish ℓ d hd n (-1) hn (Or.inr rfl) w
  · subst h; simpa using tile_KfunClear_self_S_vanish ℓ d hd n hn w
  · subst h; exact tile_KfunClear_shift_vanish ℓ d hd n 1 hn (Or.inl rfl) w

/-- The divisor `Sh (n +ᵥ w) ·` vanishes at the three resonant orbit points of the tile: it
vanishes at `S • w + k` for `k ∈ {-1, 0, 1}`, because `j (S • w + k) = j (S • w) = j w = j (n +ᵥ w)`. -/
theorem Sh_strip_zeros (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1) (k : ℤ)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) :
    Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ((k : ℝ) +ᵥ (ModularGroup.S • w)) = 0 := by
  have hjS : Work.Kernels.jInvariantFun (ModularGroup.S • w) = Work.Kernels.jInvariantFun w :=
    Work.Kernels.KernelFacts.jInvariantFun_S_smul w
  have hjw : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w :=
    ktl_jInvariantFun_vadd_int n hn w
  have hjk : Work.Kernels.jInvariantFun ((k : ℝ) +ᵥ (ModularGroup.S • w))
      = Work.Kernels.jInvariantFun w := by
    rcases hk with h | h | h
    · subst h
      have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one
        (((-1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w))
      rw [show (1 : ℝ) +ᵥ (((-1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w)) = ModularGroup.S • w by
        rw [← add_vadd]; push_cast; norm_num] at h1
      exact h1.symm.trans hjS
    · subst h
      simpa using hjS
    · subst h
      rw [show ((1 : ℤ) : ℝ) = (1 : ℝ) by norm_num,
        Work.Kernels.KernelFacts.jInvariantFun_vadd_one, hjS]
  rw [Work.Asymptotics.Compact.Sh_eq, hjk, hjw, sub_self, mul_zero, neg_zero]

/-- **The three resonant zeros of the tile numerator.**  For `w ∈ E`, `n = ±1` and `k ∈ {-1,0,1}`
the auxiliary numerator `N(ζ) = 2·Sh(τ,ζ)·(Kfun(τ,ζ) − Gfun(τ,ζ))` (with `τ = n +ᵥ w`) vanishes at
`ζ = k +ᵥ (S • w)`.  These are the three zeros fed to `three_zeros_bound_ball` in the reduction of
the strip bound to the ball bound on `N` (see the module notes). -/
theorem tileNum_strip_zeros (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1) (k : ℤ)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) :
    2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ((k : ℝ) +ᵥ (ModularGroup.S • w))
        * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ((k : ℝ) +ᵥ (ModularGroup.S • w))
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ((k : ℝ) +ᵥ (ModularGroup.S • w))))
      = 0 := by
  rw [Sh_strip_zeros w n hn k hk, zero_mul, mul_zero]

/-- **The sharp lower bound for the divisor `Sh` on the strip.**  For `w ∈ E`, `n = ±1` and
`t ∈ [Im(S•w) − 1, Im(S•w) + 1]` with `t > 0`, with `σ = S • w`,

  `c · e^{2π(Im σ − t)} · |i t − σ|·|i t − σ − 1|·|i t − σ + 1| ≤ |Sh (n +ᵥ w) (i t)|`.

It combines `SpikeCircle.divisorLowerDisc` at the *funnel* point `σ` (using `j σ = j w = j (n+ᵥw)`)
with the sharp lower bound `SpikeCircle.DeltaFunBoundsHalf` for `‖Δ‖` on `im ≥ 1/2`; it supplies
the divisor input of the three-zeros endgame (the product of the three distances is the same
product that `three_zeros_bound_ball` produces). -/
theorem Sh_axis_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ,
        (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t),
          (ModularGroup.S • w).im - 1 ≤ t → t ≤ (ModularGroup.S • w).im + 1 →
          c * (Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t))
                * ‖(((t : ℂ) * Complex.I) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ))
                    * (((t : ℂ) * Complex.I)
                        - ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - 1))
                    * (((t : ℂ) * Complex.I)
                        - ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) + 1))‖)
            ≤ ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨c₀, hc₀, hdiv⟩ := Work.Asymptotics.SpikeCircle.divisorLowerDisc
  obtain ⟨cΔ, CΔ, hcΔ, hCΔ, hΔ⟩ := Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
  refine ⟨c₀ * cΔ, mul_pos hc₀ hcΔ, ?_⟩
  intro w hw n hn t ht ht1 ht2
  have h2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have hζcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  have hζim : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  have hζhalf : (1 / 2 : ℝ) ≤ (Work.Kernels.imagAxis t ht).im := by
    rw [hζim]; linarith
  have hσF : Work.Asymptotics.Funnel (ModularGroup.S • w) := Work.Asymptotics.S_smul_mem_funnel hw
  have hσD : ModularGroup.S • w ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.S_smul_mem_DomainD hw.1
  obtain ⟨hσre1, hσre2⟩ := Work.Asymptotics.re_bounds_of_mem_DomainD hσD
  have hσre : |(ModularGroup.S • w).re| < 1 := abs_lt.mpr ⟨hσre1, hσre2⟩
  have hdist : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ ≤ 29 / 20 := by
    have hns : Complex.normSq (((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
        - ((ModularGroup.S • w : UpperHalfPlane) : ℂ))
        = (ModularGroup.S • w).re ^ 2 + (t - (ModularGroup.S • w).im) ^ 2 := by
      rw [Complex.normSq_apply, hζcoe]
      simp
      ring
    have hb : (ModularGroup.S • w).re ^ 2 + (t - (ModularGroup.S • w).im) ^ 2 ≤ 2 := by
      have h3 : -1 ≤ t - (ModularGroup.S • w).im := by linarith
      have h4 : t - (ModularGroup.S • w).im ≤ 1 := by linarith
      nlinarith [hσre, h3, h4]
    have hsq : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
        - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ ^ 2 ≤ (29 / 20 : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hns]
      nlinarith [hb]
    nlinarith [hsq, norm_nonneg (((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
      - ((ModularGroup.S • w : UpperHalfPlane) : ℂ))]
  have hjτ : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      = Work.Kernels.jInvariantFun (ModularGroup.S • w) := by
    rw [ktl_jInvariantFun_vadd_int n hn w]
    exact (Work.Kernels.KernelFacts.jInvariantFun_S_smul w).symm
  have hdiv' := hdiv (ModularGroup.S • w) (Work.Kernels.imagAxis t ht) hσF hdist
  have hΔ' : cΔ * Real.exp (-(2 * Real.pi * (Work.Kernels.imagAxis t ht).im))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    (hΔ (Work.Kernels.imagAxis t ht) hζhalf).1
  have hexp : Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t))
      = Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        * Real.exp (-(2 * Real.pi * (Work.Kernels.imagAxis t ht).im)) := by
    rw [hζim, ← Real.exp_add]
    congr 1
    ring
  rw [← hζcoe]
  calc c₀ * cΔ * (Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t))
        * ‖(((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
              - ((ModularGroup.S • w : UpperHalfPlane) : ℂ))
            * (((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
              - (((ModularGroup.S • w : UpperHalfPlane) : ℂ) - 1))
            * (((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
              - (((ModularGroup.S • w : UpperHalfPlane) : ℂ) + 1))‖)
      = (cΔ * Real.exp (-(2 * Real.pi * (Work.Kernels.imagAxis t ht).im)))
          * (c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
              * ‖(((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
                    - ((ModularGroup.S • w : UpperHalfPlane) : ℂ))
                  * (((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
                    - (((ModularGroup.S • w : UpperHalfPlane) : ℂ) - 1))
                  * (((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
                    - (((ModularGroup.S • w : UpperHalfPlane) : ℂ) + 1))‖) := by
        rw [hexp]; ring
    _ ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
          * ‖Work.Kernels.jInvariantFun (ModularGroup.S • w)
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ :=
        mul_le_mul hΔ' hdiv' (by positivity) (norm_nonneg _)
    _ = ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
          * (Work.Kernels.jInvariantFun (ModularGroup.S • w)
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ :=
        (norm_mul _ _).symm
    _ = ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ := by
        rw [Work.Asymptotics.Compact.Sh_eq, norm_neg, hjτ]
/-- **The clearing identity for the tile kernel.**  Off the coincidence locus `j τ ≠ j ζ` one has
`Sh τ ζ · Kfun ℓ d τ ζ = - KfunClear ℓ d τ ζ / (Δ(τ) · Δ(ζ)^(e-1))`, where `e = dpow d` (`1` for
`d = 8`, `2` for `d = 24`).

This is the identity that makes the auxiliary function
`N ζ = 2 · Sh τ ζ · (Kfun τ ζ - Gfun τ ζ)` holomorphic in `ζ` (its first half is
`- KfunClear/(Δ(τ)Δ(ζ)^(e-1))`), and that underlies the maximum modulus step in the reduction of
the tile strip bound to the "ball bound" on `N` (see the module notes). -/
theorem Sh_mul_Kfun_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ ζ : UpperHalfPlane) (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ) :
    Work.Asymptotics.Compact.Sh τ ζ * Work.Kernels.Kfun ℓ d τ ζ
      = - Work.Kernels.KfunClear ℓ d τ ζ
          / (Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun ζ ^ (Work.Residues.dpow d - 1)) := by
  have hA := Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ ζ h
  have hC := Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d τ ζ
  have hSh := Work.Asymptotics.Compact.Sh_eq τ ζ
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero τ
  have hDz : Work.Kernels.DeltaFun ζ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero ζ
  have hdp : 1 ≤ Work.Residues.dpow d := by rcases hd with rfl | rfl <;> decide
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Work.Residues.dpow d = m + 1 := ⟨Work.Residues.dpow d - 1, by omega⟩
  have hpe : Work.Kernels.DeltaFun ζ ^ (Work.Residues.dpow d - 1) * Work.Kernels.DeltaFun ζ
      = Work.Kernels.DeltaFun ζ ^ Work.Residues.dpow d := by
    rw [hm, Nat.add_sub_cancel, pow_succ]
  rw [hSh, hC, ← hA, ← hpe]
  field_simp

/-- **The holomorphic representative of the tile numerator** (off the coincidence locus).  For
`j τ ≠ j ζ` one has

  `2·Sh(τ,ζ)·(Kfun(τ,ζ) − Gfun(τ,ζ)) = −2·Δ(ζ)·AfunFun(τ,ζ) − 2·Sh(τ,ζ)·Gfun(τ,ζ)`,

so the numerator `N(ζ) = 2·Sh(τ,ζ)(Kfun(τ,ζ) − Gfun(τ,ζ))` agrees with the manifestly holomorphic
expression on the right wherever `N` is the honest (non-`0⁻¹`) value; this is the identity that
lets one bound `N` on the disc by the maximum modulus principle in the three-zeros endgame. -/
theorem tileNum_eq_hol (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w : UpperHalfPlane) (n : ℤ) (ζ : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) ≠ Work.Kernels.jInvariantFun ζ) :
    2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
        * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))
      = -2 * (Work.Kernels.DeltaFun ζ * Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ w) ζ)
          - 2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ) := by
  have hSK := Sh_mul_Kfun_eq ℓ d hd ((n : ℝ) +ᵥ w) ζ h
  have hC := Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d ((n : ℝ) +ᵥ w) ζ
  have hDτ : Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w) ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero ((n : ℝ) +ᵥ w)
  have hDζ : Work.Kernels.DeltaFun ζ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero ζ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Work.Residues.dpow d = m + 1 :=
    ⟨Work.Residues.dpow d - 1, by
      rcases hd with rfl | rfl <;> norm_num [Work.Residues.dpow]⟩
  have hpe : Work.Kernels.DeltaFun ζ ^ (Work.Residues.dpow d - 1) * Work.Kernels.DeltaFun ζ
      = Work.Kernels.DeltaFun ζ ^ Work.Residues.dpow d := by
    rw [hm, Nat.add_sub_cancel, pow_succ]
  rw [mul_sub, hSK, hC, ← hpe]
  field_simp
/-- **The three resonant zeros of `AfunFun`.**  At the three orbit points `S•w + k`,
`k ∈ {-1,0,1}`, the "cleared" kernel `AfunFun = KfunClear/(Δ(τ)Δ(ζ)^e)` vanishes.  It is the
second ingredient (besides `Sh = 0`) making the holomorphic representative
`−2Δ(ζ)AfunFun − 2 Sh·Gfun` of the numerator `N` vanish there. -/
theorem AfunFun_strip_zeros (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1) (k : ℤ)
    (hk : k = -1 ∨ k = 0 ∨ k = 1) :
    Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ w) ((k : ℝ) +ᵥ (ModularGroup.S • w)) = 0 := by
  have h0 := tile_KfunClear_strip_zeros ℓ d hd w n hn k hk
  have hC := Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d ((n : ℝ) +ᵥ w)
    ((k : ℝ) +ᵥ (ModularGroup.S • w))
  have hDτ : Work.Kernels.DeltaFun ((n : ℝ) +ᵥ w) ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero ((n : ℝ) +ᵥ w)
  have hDζ : Work.Kernels.DeltaFun ((k : ℝ) +ᵥ (ModularGroup.S • w)) ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using
      ModularForm.discriminant_ne_zero ((k : ℝ) +ᵥ (ModularGroup.S • w))
  rw [h0] at hC
  exact (mul_eq_zero.mp hC.symm).resolve_left
    (mul_ne_zero hDτ (pow_ne_zero _ hDζ))

/-! ## Two elementary facts used by the three-zeros endgame -/

/-- `‖Ept z‖ ≤ 1` on the upper half-plane. -/
lemma norm_Ept_le_one (z : ℍ) (hz : 0 ≤ z.im) : ‖Work.Residues.Ept z‖ ≤ 1 := by
  rw [Work.Residues.Ept_apply, Complex.norm_exp, ← Real.exp_zero]
  refine Real.exp_le_exp.mpr ?_
  have hre : ((Real.pi : ℂ) * Complex.I * (z : ℂ)).re = -(Real.pi * z.im) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
  rw [hre]; nlinarith [Real.pi_pos, hz]

/-- `↑(ofComplex w) = w` for `w` in the upper half-plane. -/
lemma ofComplex_coe_of_im_pos (w : ℂ) (hw : 0 < w.im) :
    ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) = w :=
  (congrArg (fun z : UpperHalfPlane => (z : ℂ))
    (UpperHalfPlane.ofComplex_apply_of_im_pos (z := w) hw)).trans (UpperHalfPlane.coe_mk w hw)

/-- `Gfun` is holomorphic in its second variable, over the upper half-plane. -/
theorem differentiableOn_Gfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) :
    DifferentiableOn ℂ
      (fun w : ℂ => Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} := by
  have hEpt : DifferentiableOn ℂ
      (fun w : ℂ => Work.Residues.Ept (UpperHalfPlane.ofComplex w)) {w : ℂ | 0 < w.im} :=
    (((differentiableOn_const ((Real.pi : ℂ) * Complex.I)).mul
      differentiableOn_id).cexp).congr (fun w hw => by
        rw [Work.Residues.Ept_apply]
        exact congrArg (fun t : ℂ => Complex.exp ((Real.pi : ℂ) * Complex.I * t))
          (ofComplex_coe_of_im_pos w hw))
  have hEptz : DifferentiableOn ℂ
      (fun w : ℂ => (Work.Residues.Ept (UpperHalfPlane.ofComplex w)) ^ (-2 : ℤ))
      {w : ℂ | 0 < w.im} :=
    hEpt.zpow (Or.inl (fun w _ => Work.Residues.Ept_ne_zero (UpperHalfPlane.ofComplex w)))
  have hid : DifferentiableOn ℂ
      (fun w : ℂ => ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)) {w : ℂ | 0 < w.im} :=
    differentiableOn_id.congr (fun w hw => (ofComplex_coe_of_im_pos w hw))
  have hmain : DifferentiableOn ℂ
      (fun w : ℂ => Work.Asymptotics.Compact.Gcoef d ℓ 0 0 τ
        + ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)
            * Work.Asymptotics.Compact.Gcoef d ℓ 0 1 τ
        + (Work.Residues.Ept (UpperHalfPlane.ofComplex w)) ^ (-2 : ℤ)
            * (Work.Asymptotics.Compact.Gcoef d ℓ 1 0 τ
                + ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)
                    * Work.Asymptotics.Compact.Gcoef d ℓ 1 1 τ)) {w : ℂ | 0 < w.im} :=
    ((differentiableOn_const _).add (hid.mul (differentiableOn_const _))).add
      (hEptz.mul ((differentiableOn_const _).add (hid.mul (differentiableOn_const _))))
  refine hmain.congr (fun w _ => ?_)
  rw [Work.Asymptotics.Compact.Gfun]

/-- **The `t ≤ 3` part of the strip bound.**  For `t ≤ 3` the kernel and the cusp model are
*separately* polynomially bounded (the `tile_Kfun_near`/`tile_Kfun_far` kernel bounds and the
`tile_Gfun_bound` model bound), so no cancellation is needed. -/
theorem dev_low_three (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t → t ≤ 3 →
          ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨Cn, hCn, hnear⟩ := tile_Kfun_near ℓ d hd
    (fun n m hn hm σ => tile_KfunClear_strip_zeros ℓ d hd σ n hn m hm)
  obtain ⟨Cf, Nf, hCf, hNf, hfar⟩ := tile_Kfun_far ℓ d hd
  obtain ⟨Cg, Ng, hCg, hNg, hgb⟩ := tile_Gfun_bound ℓ d hd
  refine ⟨max Cn Cf + Cg, max Nf Ng, by positivity,
    le_trans hNf (le_max_left _ _), ?_⟩
  intro w hw n hn t ht ht1 ht3
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
  have hM0 : Nf ≤ max Nf Ng := le_max_left _ _
  have hsf : (Work.Kernels.scale w) ^ Nf ≤ (Work.Kernels.scale w) ^ (max Nf Ng) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hM0
  have hsg : (Work.Kernels.scale w) ^ Ng ≤ (Work.Kernels.scale w) ^ (max Nf Ng) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hk : ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
      ≤ max Cn Cf * (Work.Kernels.scale w) ^ (max Nf Ng) := by
    by_cases h6 : (ModularGroup.S • w).im ≤ 6
    · refine le_trans (hnear w hw h6 n hn t ht ht1 ht3) ?_
      calc Cn = Cn * 1 := (mul_one Cn).symm
        _ ≤ Cn * (Work.Kernels.scale w) ^ (max Nf Ng) :=
            mul_le_mul_of_nonneg_left (Real.one_le_rpow hs1 (le_trans hNf hM0)) hCn.le
        _ ≤ max Cn Cf * (Work.Kernels.scale w) ^ (max Nf Ng) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs0 _)
    · push_neg at h6
      refine le_trans (hfar w hw (le_of_lt h6) n hn t ht ht1 ht3) ?_
      calc Cf * (Work.Kernels.scale w) ^ Nf
          ≤ Cf * (Work.Kernels.scale w) ^ (max Nf Ng) :=
            mul_le_mul_of_nonneg_left hsf hCf.le
        _ ≤ max Cn Cf * (Work.Kernels.scale w) ^ (max Nf Ng) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hs0 _)
  have hg : ‖Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
      ≤ Cg * (Work.Kernels.scale w) ^ (max Nf Ng) :=
    le_trans (hgb w hw n hn t ht ht1 ht3) (mul_le_mul_of_nonneg_left hsg hCg.le)
  calc ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
        + ‖Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ :=
        norm_sub_le _ _
    _ ≤ max Cn Cf * (Work.Kernels.scale w) ^ (max Nf Ng)
        + Cg * (Work.Kernels.scale w) ^ (max Nf Ng) := add_le_add hk hg
    _ = (max Cn Cf + Cg) * (Work.Kernels.scale w) ^ (max Nf Ng) := by ring


theorem tileWindowRestricted_strip_of_numBall (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hball : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
            ≤ C * (Work.Kernels.scale w) ^ N) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ (n : ℤ),
        (n = 1 ∨ n = -1) → ∀ t : ℝ, (ModularGroup.S • w).im - 1 ≤ t →
          t ≤ (ModularGroup.S • w).im + 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨Cb, Nb, hCb, hNb, hballb⟩ := hball
  obtain ⟨Cl, Nl, hCl, hNl, hlow⟩ := dev_low_three ℓ d hd
  obtain ⟨c, hc, hdiv⟩ := Sh_axis_lower_bound
  set δ0 : ℝ := (9 / 20) * (9 / 20) * (29 / 20) with hδ0
  have hδ0pos : (0 : ℝ) < δ0 := by rw [hδ0]; norm_num
  set Kf : ℝ := Cb * Real.exp (2 * Real.pi) / (2 * c * δ0) with hKf
  have hKfnn : (0 : ℝ) ≤ Kf := by rw [hKf]; positivity
  refine ⟨max Cl Kf + 1, max Nl Nb, 0, by positivity,
    le_trans hNl (le_max_left _ _), le_refl 0, ?_⟩
  intro w hwE hre n hn t ht1 ht2
  have ht0 : (0 : ℝ) < t := by have h := hwE.2; linarith
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
  have hL1 : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
    rw [Work.Kernels.Kaxis, dif_pos ht0]
  have hL2 : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t
      = Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) := by
    rw [Work.Asymptotics.Gcusp_eq_Gcoef ℓ d hd,
      Work.Asymptotics.Aexp_Gcoef' ℓ d ((n : ℝ) +ᵥ w) t ht0]
  rw [hL1, hL2, Real.rpow_zero, mul_one]
  by_cases ht3 : t ≤ 3
  · refine le_trans (hlow w hwE n hn t ht0 (by linarith [hwE.2]) ht3) ?_
    calc Cl * (Work.Kernels.scale w) ^ Nl
        ≤ max Cl Kf * (Work.Kernels.scale w) ^ (max Nl Nb) :=
          mul_le_mul (le_max_left _ _)
            (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _))
            (Real.rpow_nonneg hs0 _) (by positivity)
      _ ≤ (max Cl Kf + 1) * (Work.Kernels.scale w) ^ (max Nl Nb) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hs0 _)
  · push_neg at ht3
    set σ : ℍ := ModularGroup.S • w with hσdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    have hσF : Work.Asymptotics.Funnel σ := by
      rw [hσdef]; exact Work.Asymptotics.S_smul_mem_funnel hwE
    have hσD : σ ∈ Work.Asymptotics.DomainD := hσF.1
    have hσim : (2 : ℝ) ≤ σ.im := hσF.2
    obtain ⟨hσre1, hσre2⟩ := Work.Asymptotics.re_bounds_of_mem_DomainD hσD
    have hσre : |σ.re| < 1 := abs_lt.mpr ⟨hσre1, hσre2⟩
    have hjτσ : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun σ := by
      rw [hτdef, hσdef, ktl_jInvariantFun_vadd_int n hn w,
        Work.Kernels.KernelFacts.jInvariantFun_S_smul]
    have hσre_ne : σ.re ≠ 0 := by
      intro h0
      have hcoe : ((ModularGroup.S • w : ℍ) : ℂ) = -((w : ℂ))⁻¹ := by
        rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
      have h2 : (ModularGroup.S • w).re = -w.re / Complex.normSq (w : ℂ) := by
        rw [← UpperHalfPlane.coe_re, hcoe, Complex.neg_re, Complex.inv_re,
          UpperHalfPlane.coe_re, neg_div]
      rw [hσdef] at h0
      rw [h2] at h0
      have hnw : Complex.normSq (w : ℂ) ≠ 0 :=
        ne_of_gt (Complex.normSq_pos.mpr w.ne_zero)
      have : w.re = 0 := by
        rw [div_eq_zero_iff] at h0
        rcases h0 with h | h
        · linarith
        · exact absurd h hnw
      exact hre this
    -- the holomorphic representative
    set F : ℂ → ℂ := fun u => -2 * (Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex u) /
        (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u))
          ^ (Work.Residues.dpow d - 1)))
      - 2 * (Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
          * Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u)) with hFdef
    have him_of_ball : ∀ u : ℂ, u ∈ Metric.ball (σ : ℂ) (3 / 2) → 0 < u.im := by
      intro u hu
      have h1 : ‖u - (σ : ℂ)‖ < 3 / 2 := by
        have h := Metric.mem_ball.mp hu
        rwa [dist_eq_norm] at h
      have h2 : |u.im - σ.im| ≤ ‖u - (σ : ℂ)‖ := by
        have h3 := Complex.abs_im_le_norm (u - (σ : ℂ))
        rwa [Complex.sub_im, UpperHalfPlane.coe_im] at h3
      have h4 := (abs_le.mp h2).1
      linarith
    have hofc : ∀ z : ℍ, ((UpperHalfPlane.ofComplex ((z : ℍ) : ℂ) : ℍ) : ℂ) = (z : ℂ) :=
      fun z => ofComplex_coe_of_im_pos _ z.im_pos
    have hΔd : DifferentiableOn ℂ
        (fun u : ℂ => Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u)) {u : ℂ | 0 < u.im} :=
      (UpperHalfPlane.mdifferentiable_iff (f := Work.Kernels.DeltaFun)).mp
        Work.Asymptotics.mdiff_DeltaFun
    have hE4d : DifferentiableOn ℂ
        (fun u : ℂ => Work.Kernels.E4Fun (UpperHalfPlane.ofComplex u)) {u : ℂ | 0 < u.im} :=
      (UpperHalfPlane.mdifferentiable_iff (f := Work.Kernels.E4Fun)).mp
        Work.Asymptotics.mdiff_E4Fun
    have hAd : DifferentiableOn ℂ
        (fun u : ℂ => Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
        {u : ℂ | 0 < u.im} :=
      (UpperHalfPlane.mdifferentiable_iff
        (f := fun z : ℍ => Work.Asymptotics.AfunFun ℓ d τ z)).mp
        (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ)
    have hGd : DifferentiableOn ℂ
        (fun u : ℂ => Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u))
        {u : ℂ | 0 < u.im} := differentiableOn_Gfun ℓ d τ
    have hnumd : DifferentiableOn ℂ
        (fun u : ℂ => Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex u))
        {u : ℂ | 0 < u.im} := by
      have heq : (fun u : ℂ => Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex u))
          = fun u : ℂ => Work.Kernels.DeltaFun τ
              * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u)) ^ (Work.Residues.dpow d)
              * Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) := by
        funext u
        rw [Work.Asymptotics.KfunClear_eq_mul_AfunFun]
      rw [heq]
      exact ((differentiableOn_const _).mul (hΔd.pow _)).mul hAd
    have hterm1 : DifferentiableOn ℂ
        (fun u : ℂ => Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex u) /
          (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u))
            ^ (Work.Residues.dpow d - 1))) {u : ℂ | 0 < u.im} :=
      hnumd.div ((differentiableOn_const _).mul (hΔd.pow _))
        (fun u _ => mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
          (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)))
    have hterm2 : DifferentiableOn ℂ
        (fun u : ℂ => Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
          * Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u))
        {u : ℂ | 0 < u.im} := by
      have heq : (fun u : ℂ => Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
            * Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u))
          = fun u : ℂ => (Work.Kernels.E4Fun (UpperHalfPlane.ofComplex u) ^ 3
              - Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u) * Work.Kernels.jInvariantFun τ)
              * Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u) := by
        funext u; rw [Work.Asymptotics.Compact.Sh]
      rw [heq]
      exact ((hE4d.pow 3).sub (hΔd.mul (differentiableOn_const _))).mul hGd
    have hFd3 : DifferentiableOn ℂ F (Metric.ball (σ : ℂ) (3 / 2)) := by
      have hmain : DifferentiableOn ℂ
          (fun u : ℂ => -2 * (Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex u) /
              (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u))
                ^ (Work.Residues.dpow d - 1)))
            - 2 * (Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
                * Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u)))
          {u : ℂ | 0 < u.im} :=
        (hterm1.const_mul (-2)).sub (hterm2.const_mul 2)
      rw [hFdef]
      exact hmain.mono (fun u hu => him_of_ball u hu)
    have hρ23 : (29 : ℝ) / 20 ≤ 3 / 2 := by norm_num
    have hFd : DifferentiableOn ℂ F (Metric.ball (σ : ℂ) (29 / 20)) :=
      hFd3.mono (Metric.ball_subset_ball hρ23)
    have hclsub : closure (Metric.ball (σ : ℂ) (29 / 20)) ⊆ Metric.ball (σ : ℂ) (3 / 2) :=
      (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num)))
    have hFcont : ContinuousOn F (closure (Metric.ball (σ : ℂ) (29 / 20))) :=
      hFd3.continuousOn.mono hclsub
    have hFdc : DiffContOnCl ℂ F (Metric.ball (σ : ℂ) (29 / 20)) := ⟨hFd, hFcont⟩
    have hzv₁ : (((1 : ℝ) +ᵥ σ : ℍ) : ℂ) = (σ : ℂ) + 1 := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    have hzv₂ : (((-1 : ℝ) +ᵥ σ : ℍ) : ℂ) = (σ : ℂ) - 1 := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    have hofcσ : UpperHalfPlane.ofComplex ((σ : ℍ) : ℂ) = σ :=
      UpperHalfPlane.ofComplex_apply σ
    have hofc₁ : UpperHalfPlane.ofComplex ((σ : ℂ) + 1) = ((1 : ℝ) +ᵥ σ : ℍ) := by
      rw [← hzv₁]; exact UpperHalfPlane.ofComplex_apply _
    have hofc₂ : UpperHalfPlane.ofComplex ((σ : ℂ) - 1) = ((-1 : ℝ) +ᵥ σ : ℍ) := by
      rw [← hzv₂]; exact UpperHalfPlane.ofComplex_apply _
    have hvan : ∀ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) →
        Work.Kernels.KfunClear ℓ d τ ((k : ℝ) +ᵥ σ) = 0 := by
      intro k hk
      rw [hτdef, hσdef]
      exact tile_KfunClear_strip_zeros ℓ d hd w n hn k hk
    have hvanS : ∀ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) →
        Work.Asymptotics.Compact.Sh τ ((k : ℝ) +ᵥ σ) = 0 := by
      intro k hk
      rw [hτdef, hσdef]
      exact Sh_strip_zeros w n hn k hk
    have hFz₁ : F (σ : ℂ) = 0 := by
      have h1 : Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex (σ : ℂ)) = 0 := by
        rw [hofcσ]
        simpa using hvan 0 (Or.inr (Or.inl rfl))
      have h2 : Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex (σ : ℂ)) = 0 := by
        rw [hofcσ]
        simpa using hvanS 0 (Or.inr (Or.inl rfl))
      simp only [hFdef, h1, h2, zero_div, zero_mul, mul_zero, sub_zero]
    have hFz₂ : F ((σ : ℂ) + 1) = 0 := by
      have h1 : Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex ((σ : ℂ) + 1)) = 0 := by
        rw [hofc₁]
        simpa using hvan 1 (Or.inr (Or.inr rfl))
      have h2 : Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex ((σ : ℂ) + 1)) = 0 := by
        rw [hofc₁]
        simpa using hvanS 1 (Or.inr (Or.inr rfl))
      simp only [hFdef, h1, h2, zero_div, zero_mul, mul_zero, sub_zero]
    have hFz₃ : F ((σ : ℂ) - 1) = 0 := by
      have h1 : Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex ((σ : ℂ) - 1)) = 0 := by
        rw [hofc₂]
        simpa using hvan (-1) (Or.inl rfl)
      have h2 : Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex ((σ : ℂ) - 1)) = 0 := by
        rw [hofc₂]
        simpa using hvanS (-1) (Or.inl rfl)
      simp only [hFdef, h1, h2, zero_div, zero_mul, mul_zero, sub_zero]
    have hFval : ∀ u ∈ Metric.ball (σ : ℂ) (29 / 20),
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u) →
        F u = 2 * (Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
          * (Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex u)
              - Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u))) := by
      intro u _ hne
      have h := Sh_mul_Kfun_eq ℓ d hd τ (UpperHalfPlane.ofComplex u) hne
      simp only [hFdef]
      have h' : Work.Kernels.KfunClear ℓ d τ (UpperHalfPlane.ofComplex u) /
          (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u))
            ^ (Work.Residues.dpow d - 1))
          = -(Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
              * Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex u)) := by
        rw [h]; ring
      rw [h']
      ring
    have hbd : ∀ u ∈ Metric.ball (σ : ℂ) (29 / 20),
        ‖F u‖ ≤ Cb * (Work.Kernels.scale w) ^ Nb := by
      intro u hu
      have himu : 0 < u.im := him_of_ball u (Metric.ball_subset_ball hρ23 hu)
      have hofcu : ((UpperHalfPlane.ofComplex u : ℍ) : ℂ) = u :=
        ofComplex_coe_of_im_pos u himu
      have hdist : ‖((UpperHalfPlane.ofComplex u : ℍ) : ℂ) - (σ : ℂ)‖ ≤ 29 / 20 := by
        have h := Metric.mem_ball.mp hu
        rw [dist_eq_norm] at h
        rw [hofcu]
        exact le_of_lt h
      by_cases hne : Work.Kernels.jInvariantFun τ
          = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u)
      · have hj' : Work.Kernels.jInvariantFun σ
            = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u) := by
          rw [← hjτσ]; exact hne
        have hcls := (Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc hσF hdist).mp hj'
        have hzero : F u = 0 := by
          rcases hcls with h | h | h
          · rw [show u = (σ : ℂ) from by rw [← hofcu, h]]
            exact hFz₁
          · rw [show u = (σ : ℂ) + 1 from by rw [← hofcu, h, hzv₁]]
            exact hFz₂
          · rw [show u = (σ : ℂ) - 1 from by rw [← hofcu, h, hzv₂]]
            exact hFz₃
        rw [hzero, norm_zero]
        exact mul_nonneg hCb.le (Real.rpow_nonneg hs0 _)
      · have h3 := hballb w hwE n hn (UpperHalfPlane.ofComplex u) hdist
        rw [← hτdef] at h3
        rw [hFval u hu hne]
        exact h3
    have hbnd : ∀ u ∈ Metric.sphere (σ : ℂ) (29 / 20),
        δ0 ≤ ‖u - (σ : ℂ)‖ * ‖u - ((σ : ℂ) + 1)‖ * ‖u - ((σ : ℂ) - 1)‖ := by
      intro u hu
      have h1 : ‖u - (σ : ℂ)‖ = 29 / 20 := by
        have h := Metric.mem_sphere.mp hu
        rwa [dist_eq_norm] at h
      have h2 : (9 / 20 : ℝ) ≤ ‖u - ((σ : ℂ) + 1)‖ := by
        have h3 : ‖u - (σ : ℂ)‖ ≤ ‖(u - ((σ : ℂ) + 1)) + 1‖ := by
          rw [show (u - ((σ : ℂ) + 1)) + 1 = u - (σ : ℂ) by ring]
        have h4 : ‖(u - ((σ : ℂ) + 1)) + 1‖ ≤ ‖u - ((σ : ℂ) + 1)‖ + 1 := by
          simpa using norm_add_le (u - ((σ : ℂ) + 1)) (1 : ℂ)
        rw [h1] at h3
        linarith
      have h5 : (9 / 20 : ℝ) ≤ ‖u - ((σ : ℂ) - 1)‖ := by
        have h3 : ‖u - (σ : ℂ)‖ ≤ ‖(u - ((σ : ℂ) - 1)) - 1‖ := by
          rw [show (u - ((σ : ℂ) - 1)) - 1 = u - (σ : ℂ) by ring]
        have h4 : ‖(u - ((σ : ℂ) - 1)) - 1‖ ≤ ‖u - ((σ : ℂ) - 1)‖ + 1 := by
          simpa using norm_sub_le (u - ((σ : ℂ) - 1)) (1 : ℂ)
        rw [h1] at h3
        linarith
      rw [hδ0]
      have h1' : (29 / 20 : ℝ) ≤ ‖u - (σ : ℂ)‖ := le_of_eq h1.symm
      have hp1 : (9 / 20) * (9 / 20) ≤ ‖u - ((σ : ℂ) + 1)‖ * ‖u - ((σ : ℂ) - 1)‖ :=
        mul_le_mul h2 h5 (by norm_num) (norm_nonneg _)
      have hp2 : (9 / 20) * (9 / 20) * (29 / 20)
          ≤ ‖u - ((σ : ℂ) + 1)‖ * ‖u - ((σ : ℂ) - 1)‖ * ‖u - (σ : ℂ)‖ :=
        mul_le_mul hp1 h1' (by norm_num)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      calc (9 / 20) * (9 / 20) * (29 / 20)
          ≤ ‖u - ((σ : ℂ) + 1)‖ * ‖u - ((σ : ℂ) - 1)‖ * ‖u - (σ : ℂ)‖ := hp2
        _ = ‖u - (σ : ℂ)‖ * ‖u - ((σ : ℂ) + 1)‖ * ‖u - ((σ : ℂ) - 1)‖ := by ring
    have hmem : ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) ∈ Metric.ball (σ : ℂ) (29 / 20) := by
      have hcoe : ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
      have hsq : ‖((t : ℂ) * Complex.I) - (σ : ℂ)‖ ^ 2 = σ.re ^ 2 + (t - σ.im) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        ring
      rw [Metric.mem_ball, dist_eq_norm, hcoe]
      have hb : σ.re ^ 2 + (t - σ.im) ^ 2 < (29 / 20 : ℝ) ^ 2 := by
        have h1 : σ.re ^ 2 ≤ 1 := by nlinarith [hσre]
        have h2 : (t - σ.im) ^ 2 ≤ 1 := by
          have hh : |t - σ.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
          nlinarith [hh, sq_abs (t - σ.im)]
        nlinarith
      rw [← hsq] at hb
      have hnorm0 : (0 : ℝ) ≤ ‖((t : ℂ) * Complex.I) - (σ : ℂ)‖ := norm_nonneg _
      nlinarith [hnorm0, hb]
    have hz₁ : (σ : ℂ) ≠ (σ : ℂ) + 1 := by
      intro h0
      have h' := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re] at h'
      linarith
    have hz₂ : (σ : ℂ) ≠ (σ : ℂ) - 1 := by
      intro h0
      have h' := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.one_re, UpperHalfPlane.coe_re] at h'
      linarith
    have hz₃ : (σ : ℂ) + 1 ≠ (σ : ℂ) - 1 := by
      intro h0
      have h' := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, UpperHalfPlane.coe_re] at h'
      linarith
    have hkey := Work.Analysis.ThreeZeros.three_zeros_bound_ball (f := F) (c := (σ : ℂ))
      (ρ := 29 / 20) (M := Cb * (Work.Kernels.scale w) ^ Nb) (δ := δ0)
      (by norm_num) (mul_nonneg hCb.le (Real.rpow_nonneg hs0 _)) hδ0pos hFdc hbd
      hz₁ hz₂ hz₃ hFz₁ hFz₂ hFz₃ hbnd
      ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) hmem
    have hshlow := hdiv w hwE n hn t ht0 ht1 ht2
    -- the real-valued quantities entering the final arithmetic
    set M0 : ℝ := Cb * (Work.Kernels.scale w) ^ Nb / δ0 with hM0
    set A : ℝ := ‖((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) - (σ : ℂ)‖ with hAdef
    set B : ℝ := ‖((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) - ((σ : ℂ) + 1)‖ with hBdef
    set C : ℝ := ‖((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) - ((σ : ℂ) - 1)‖ with hCdef
    set S : ℝ := ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖ with hSdef
    set D : ℝ := ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)
        - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0)‖ with hDdef
    set P : ℝ := ‖(((t : ℂ) * Complex.I) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ))
          * (((t : ℂ) * Complex.I) - ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - 1))
          * (((t : ℂ) * Complex.I) - ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) + 1))‖ with hPdef
    set E : ℝ := Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) with hEdef
    have hM0nn : (0 : ℝ) ≤ M0 := by rw [hM0]; positivity
    have hPposraw : 0 < P := by
      have h1 : ((t : ℂ) * Complex.I - (σ : ℂ)) ≠ 0 := by
        intro h0
        have hre : (((t : ℂ) * Complex.I - (σ : ℂ)).re) = 0 := by simp [h0]
        have hre' : (((t : ℂ) * Complex.I - (σ : ℂ)).re) = -σ.re := by simp
        rw [hre'] at hre
        exact hσre_ne (by linarith)
      have h2 : ((t : ℂ) * Complex.I - ((σ : ℂ) - 1)) ≠ 0 := by
        intro h0
        have hre : (((t : ℂ) * Complex.I - ((σ : ℂ) - 1)).re) = 0 := by simp [h0]
        have hre' : (((t : ℂ) * Complex.I - ((σ : ℂ) - 1)).re) = 1 - σ.re := by simp
        rw [hre'] at hre
        linarith [hσre2]
      have h3 : ((t : ℂ) * Complex.I - ((σ : ℂ) + 1)) ≠ 0 := by
        intro h0
        have hre : (((t : ℂ) * Complex.I - ((σ : ℂ) + 1)).re) = 0 := by simp [h0]
        have hre' : (((t : ℂ) * Complex.I - ((σ : ℂ) + 1)).re) = -1 - σ.re := by
          simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, UpperHalfPlane.coe_re]
          ring
        rw [hre'] at hre
        linarith [hσre1]
      rw [hPdef, norm_pos_iff]
      exact mul_ne_zero (mul_ne_zero h1 h2) h3
    have hEpos : 0 < E := by rw [hEdef]; exact Real.exp_pos _
    have hEge : Real.exp (-(2 * Real.pi)) ≤ E := by
      rw [hEdef]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht2, hσim])
    have hdivP : c * (E * P) ≤ S := by
      linarith [hshlow, hEdef, hPdef, hSdef]
    have hSpos : 0 < S := by
      have hp : 0 < c * (E * P) := mul_pos hc (mul_pos hEpos hPposraw)
      linarith [hdivP, hp]
    have hShne : Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht0) ≠ 0 := by
      intro h0
      rw [hSdef] at hSpos
      rw [h0, norm_zero] at hSpos
      linarith
    have hjne : Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht0) := by
      intro hcon
      refine hShne ?_
      rw [Work.Asymptotics.Compact.Sh_eq, hcon, sub_self, mul_zero, neg_zero]
    have hjneO : Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun
            (UpperHalfPlane.ofComplex ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ)) := by
      simpa only [UpperHalfPlane.ofComplex_apply] using hjne
    have hval : F ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ)
        = 2 * (Work.Asymptotics.Compact.Sh τ (Work.Kernels.imagAxis t ht0)
            * (Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht0)
                - Work.Asymptotics.Compact.Gfun d ℓ τ (Work.Kernels.imagAxis t ht0))) := by
      have h := hFval _ hmem hjneO
      simpa only [UpperHalfPlane.ofComplex_apply] using h
    have hnorm : ‖(2 : ℂ) * (Work.Asymptotics.Compact.Sh τ (Work.Kernels.imagAxis t ht0)
          * (Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht0)
              - Work.Asymptotics.Compact.Gfun d ℓ τ (Work.Kernels.imagAxis t ht0)))‖
        = 2 * (S * D) := by
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hSdef, hDdef, norm_mul, norm_mul, h2]
    have hPABC : P = A * B * C := by
      rw [hPdef, hAdef, hBdef, hCdef]
      rw [show ((Work.Kernels.imagAxis t ht0 : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
      simp only [norm_mul]
      ring
    have h₁ : 2 * (S * D) ≤ M0 * P := by
      have h := hkey
      rw [hval] at h
      rw [hnorm] at h
      rw [hPABC]
      linarith [h]
    have h₂ : 2 * (S * D) * (c * E) ≤ M0 * S := by
      have h := h₁
      have hcE : 0 ≤ c * E := le_of_lt (mul_pos hc hEpos)
      have step := mul_le_mul_of_nonneg_right h hcE
      refine le_trans step ?_
      have h3 : (M0 * P) * (c * E) = M0 * (c * (E * P)) := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hdivP hM0nn
    have h₃ : D * (2 * c * E) ≤ M0 := by
      have h := h₂
      have h4 : 2 * (S * D) * (c * E) = S * (D * (2 * c * E)) := by ring
      rw [h4] at h
      rw [mul_comm M0 S] at h
      exact le_of_mul_le_mul_left h hSpos
    have h₄ : D ≤ M0 / (2 * c * E) := by
      rw [le_div_iff₀ (by positivity)]
      exact h₃
    have h₅ : D ≤ Kf * (Work.Kernels.scale w) ^ Nb := by
      have hEinv : 1 / E ≤ Real.exp (2 * Real.pi) := by
        rw [div_le_iff₀ hEpos]
        have h1 : (1 : ℝ) = Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi)) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        rw [h1]
        exact mul_le_mul_of_nonneg_left hEge (Real.exp_pos _).le
      have hA1 : M0 / (2 * c * E) ≤ M0 * Real.exp (2 * Real.pi) / (2 * c) := by
        have hf1 : M0 / (2 * c * E) = (M0 / (2 * c)) * (1 / E) := by ring_nf
        have hf2 : M0 * Real.exp (2 * Real.pi) / (2 * c)
            = (M0 / (2 * c)) * Real.exp (2 * Real.pi) := by ring_nf
        rw [hf1, hf2]
        exact mul_le_mul_of_nonneg_left hEinv (by positivity)
      have hA2 : M0 * Real.exp (2 * Real.pi) / (2 * c)
          = Kf * (Work.Kernels.scale w) ^ Nb := by
        rw [hM0, hKf]
        ring_nf
      have h := hA1
      rw [hA2] at h
      exact le_trans h₄ h
    have hfin : D ≤ (max Cl Kf + 1) * (Work.Kernels.scale w) ^ (max Nl Nb) := by
      calc D ≤ Kf * (Work.Kernels.scale w) ^ Nb := h₅
        _ ≤ (max Cl Kf) * (Work.Kernels.scale w) ^ (max Nl Nb) :=
            mul_le_mul (le_max_right _ _)
              (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _))
              (Real.rpow_nonneg hs0 _) (le_trans hKfnn (le_max_right _ _))
        _ ≤ (max Cl Kf + 1) * (Work.Kernels.scale w) ^ (max Nl Nb) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hs0 _)
    exact hfin

/-- **The resonant strip of the tile deviation** (the target). -/
theorem tileWindowRestricted_strip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → w.re ≠ 0 → ∀ (n : ℤ),
        (n = 1 ∨ n = -1) → ∀ t : ℝ, (ModularGroup.S • w).im - 1 ≤ t →
          t ≤ (ModularGroup.S • w).im + 1 →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M :=
  tileWindowRestricted_strip_of_numBall ℓ d hd (Work.Asymptotics.Tile.tileNumBallBoundA ℓ d hd)

end Work.Asymptotics.Tile
