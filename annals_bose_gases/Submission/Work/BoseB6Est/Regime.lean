import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — FS's parameter regime

The estimates of this chapter (`fsI1_le`, `fsZeroPoint_le`, `kappaSum_le`) hold
*at FS's parameters*: `μ` fixed, box side `ℓ = K_ℓ (μa)^{-1/2}`, particle number
free.  What remains are FS's §4/§11 ingredient conditions — `eq:Close`
(`9/10 μ ≤ ρ_z ≤ 11/10 μ`), the smallness of `ε_T, d, s`, the two kinetic
cutoffs

  `c₁ = ½(K_ℓs)^{-1}(μ/ρ_z)^{1/2}`,  `c₂ = ½(K_ℓds)^{-1}(μ/ρ_z)^{1/2}`,

the kernel regime `β ≈ 8π` on the mode range, and the *size* relations between
the kernel's momentum cutoff `T`, the mode range and FS's error `ε(μ,ρ_z)` that
FS's concrete parameter choices (`K_ℓ = X^{-3/2}`, `d = X⁶`, `s = X`,
`ε_T = X^{23/4}`, `K_M = X^{-1}`, `X = (μa³)^{1/323}`) satisfy.  They are
collected in the two structures below:

* `FsI1Regime` — everything the `I₁` estimate of `lem:BogIntegral` needs
  (the scalar conditions and the dominance of the cutoffs by `lhyEps`, which is
  FS's own "the error term is bigger than each cutoff" statement);
* `FsZeroRegime` — additionally the mode-lattice data of `hzero`:
  `(n:ℝ)+1 = ℓ√(ρ_z a)` (`zeroPoint_fs_sharp`'s mesh relation) and the kernel's
  support inside the mode range.

No conclusion of the chapter appears as a field: every field is a statement
about FS's *ingredients* (the kernel, the parameters, the mesh), of the kind FS
assume in §4/§11 (`con:...`).  Concretely, each dominance field below is the
consequence of FS's `K_ℓ, K_M, d, s ≫ 1` choices; e.g. FS's `con:KMKellKH`
(`K_M K_ℓ⁴ ≪ K_H³`) and `d ≪ 1` give `T(μa³)^{1/2} ≤ K_ℓds/(μa³)^{1/2}`, and
`ε(μ,ρ_z) ≥ (K_ℓs)^{-1}` gives `(K_ℓds)^{-1} ≤ e·ε(μ,ρ_z)`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB6Est

/-! ## The `I₁` regime -/

/-- **FS's parameter regime for `lem:BogIntegral`** (`I₁` estimate).

Primitive ingredient conditions: `a, ρ_z, μ, K_ℓ, s, d > 0`, `R ≥ 0`,
`eq:Close` (`9/10 μ ≤ ρ_z ≤ 11/10 μ`), `0 ≤ ε_T ≤ 1/2`, the two cutoffs
`c₁, c₂` at FS's values, the cutoff smallness `K_ℓs ≥ 1`, `K_ℓds ≥ 1`, `d ≤ 1`
and `K_ℓds ≥ (μa³)^{1/2}` (so that FS's logarithms are nonnegative), and the
kernel regime `B ≤ 100`, `ηT ≤ 1`, `T ≥ 1`, `T√(ρ_za)R ≤ K_ℓds/√(μa)`,
`T(μa³)^{1/2} ≤ K_ℓds/(μa³)^{1/2}` (the kernel's support against FS's scales).

Dominance conditions (FS's "the error dominates every cutoff"): each of
`ε_T`, `(μa)^{1/4}√R`, `(K_ℓs)^{-1}`, `(K_ℓds)^{-1}` and the logarithmic
products `(K_ℓs)^{-1}(1 + log(T/c₂))`, `(K_ℓds)^{-1}(1 + log(T/c₂))`,
`(B+8π)²log T/T` is bounded by `lhyEps`, and `η ≤ lhyEps`. -/
structure FsI1Regime (K : FsKernel) (a R ρz μ εT c1 c2 Kl s d : ℝ) : Prop where
  ha : 0 < a
  hR : 0 ≤ R
  hρz : 0 < ρz
  hμ : 0 < μ
  hKl : 0 < Kl
  hs : 0 < s
  hd : 0 < d
  hε0 : 0 ≤ εT
  hε1 : εT ≤ 1 / 2
  hc1 : 0 ≤ c1
  hc12 : c1 ≤ c2
  /-- the two cutoffs together are `≤ 1` (at FS's parameters
  `c₁ + ε_Tc₂ = ½X^{1/2} + ½X^{1/4} ≤ 1` for `X ≤ 1/10`). -/
  hcc1 : c1 + εT * c2 ≤ 1
  hc1val : c1 = (1 / 2) * (Kl * s)⁻¹ * Real.sqrt (μ / ρz)
  hc2val : c2 = (1 / 2) * (Kl * d * s)⁻¹ * Real.sqrt (μ / ρz)
  hclose1 : 9 / 10 * μ ≤ ρz
  hclose2 : ρz ≤ 11 / 10 * μ
  hKl1 : 1 ≤ Kl * s
  hd1 : d ≤ 1
  hlog1 : 1 ≤ Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)
  hB : K.B ≤ 100
  hηT : K.η * K.T ≤ 1
  hT1 : 1 ≤ K.T
  hc1T : c1 < K.T
  hTsupp : K.T * Real.sqrt (ρz * a) * R ≤ Kl * d * s / Real.sqrt (μ * a)
  hTm : K.T * (μ * a ^ 3) ^ (1 / 2 : ℝ) ≤ Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)
  hsmall : (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R ≤ 1
  hI2 : fsGω0 ρz a K ≤ 1
  -- dominance of the cutoffs and of the kernel scale by FS's error
  hEpsEta : K.η ≤ Work.BoseB6.lhyEps a R εT Kl s d μ
  hEpsT : εT ≤ Work.BoseB6.lhyEps a R εT Kl s d μ
  hEpsR : (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R ≤ Work.BoseB6.lhyEps a R εT Kl s d μ
  hEpsKl : (Kl * s)⁻¹ ≤ Work.BoseB6.lhyEps a R εT Kl s d μ
  hEpsLog : (Kl * s)⁻¹ * (1 + Real.log (K.T / c2)) ≤ Work.BoseB6.lhyEps a R εT Kl s d μ
  /-- **FS's logarithmic absorption, in FS's own weighted form.**  The
  log-divergent model deviation `(c₁ + ε_Tc₂)log T` of `lem:BogIntegral` (with the
  `ε_T`-weight *retained*, exactly as in FS's `eq:Logarithm`) is dominated by FS's
  error `ε(μ,ρ_z)`.  At FS's parameters
  (`K_ℓ = X^{-3/2}, s = X, d = X⁶, ε_T = X^{23/4}, X = (μa³)^{1/323}`) this holds
  with ratio `≈ 0.5` for every `X`, whereas the *unweighted* form
  `(K_ℓds)^{-1}log T ≤ ε` fails as `X → 0`; see `fsRegime_fs` for the verified
  instance. -/
  hEpsLogT : (c1 + εT * c2) * Real.log K.T ≤ Work.BoseB6.lhyEps a R εT Kl s d μ
  hEpsTlog : (K.B + 8 * Real.pi) ^ 2 * Real.log K.T / K.T
      ≤ Work.BoseB6.lhyEps a R εT Kl s d μ
  /-- the model bracket's tail beyond the kernel's cutoff is negligible: with
  `∫_{ℝ³} lhyR3 (8π) = −lhyValue(8π)` concentrated on the whole momentum range,
  `T` must be large enough that the part of it outside `[0,T]` is bounded by FS's
  error (in FS's parameters `T` is `K_M(ρ_z a³)^{-1/2}`, so the tail is
  `O(1/T)`). -/
  hTtail : 4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * K.T)
      ≤ Work.BoseB6.lhyEps a R εT Kl s d μ

/-! ## The lattice (zero-point) regime -/

/-- **FS's parameter regime for the zero-point comparison `hzero`**: the `I₁`
regime together with the mode-lattice data — the mesh relation
`(n:ℝ)+1 = ℓ√(ρ_z a)` of `zeroPoint_fs_sharp`, `0 < ℓ`, the kernel's support
inside the mode range (`T ≤ √3π(n+1)`, so that the mesh-`δ` lattice covers the
support of `β`) and the bound 
(FS: `K_ℓ = X^{-3/2} ≤ 10³` for every `X = (μa³)^{1/323} ∈ (0,1)`). -/
structure FsZeroRegime (n : ℕ) (K : FsKernel) (a R ρz ℓ μ z chiM δ : ℝ)
    (εT c1 c2 Kl s d : ℝ) : Prop where
  hi1 : FsI1Regime K a R ρz μ εT c1 c2 Kl s d
  hn : 1 ≤ n
  hℓ : 0 < ℓ
  /-- `ℓ³ ≥ 3` (FS: `ℓ = K_ℓ(μa)^{-1/2} ≫ 1`); the `𝒞`-sum bound loses this
  factor. -/
  hℓ3 : 3 ≤ ℓ ^ 3
  hrel : (n : ℝ) + 1 = ℓ * Real.sqrt (ρz * a)
  /-- the kernel's support lies inside the mode range: the mesh-`δ` lattice
  covers the support of `β` (FS: the box modes resolve the kernel). -/
  hTlat : K.T ≤ Real.sqrt 3 * Real.pi * (ℓ * Real.sqrt (ρz * a))
  /-- the lattice mesh error is dominated by FS's error (at FS's parameters
  `latticeMeshErr (8π) n = O(δ log(1/δ))` with `δ = 2π/(n+1) = 2π/K_ℓ → 0`, while
  `ε` decays only like `(K_ℓs)^{-1}log(K_ℓds/(μa³)^{1/2})`). -/
  hEpsLatt : Work.BoseB6.latticeMeshErr (8 * Real.pi) n
      ≤ 2 * 10 ^ 11 * Work.BoseB6.lhyEps a R εT Kl s d μ

/-! ## Immediate consequences -/

lemma FsI1Regime.lhyEps_nonneg {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    0 ≤ Work.BoseB6.lhyEps a R εT Kl s d μ :=
  le_trans (inv_nonneg.mpr (mul_pos h.hKl h.hs).le) h.hEpsKl

lemma FsI1Regime.T_pos {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : 0 < K.T :=
  lt_of_lt_of_le one_pos h.hT1

lemma FsI1Regime.eta_le_one {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : K.η ≤ 1 := by
  have h1 : K.η * 1 ≤ K.η * K.T := mul_le_mul_of_nonneg_left h.hT1 K.ηnn
  linarith [h.hηT]

lemma FsI1Regime.etaT_sq_le {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : K.η * K.T ^ 2 ≤ K.T := by
  have h1 : K.T * (K.η * K.T) ≤ K.T * 1 := mul_le_mul_of_nonneg_left h.hηT h.T_pos.le
  nlinarith [h1]

lemma FsI1Regime.c1_le_KT {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : c1 < K.T := h.hc1T

/-- `c₁ ≤ 1`: from `K_ℓs ≥ 1` and FS's `eq:Close` (`√(μ/ρ_z) ≤ 2`). -/
lemma FsI1Regime.c1_le_one {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : c1 ≤ 1 := by
  have hKs : 0 < Kl * s := mul_pos h.hKl h.hs
  have h2 : μ / ρz ≤ 4 := by
    rw [div_le_iff₀ h.hρz]
    linarith [h.hclose1, h.hμ]
  have hs4 : Real.sqrt (μ / ρz) ≤ 2 := by
    refine le_trans (Real.sqrt_le_sqrt h2) ?_
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h3 : (Kl * s)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hKs]
    exact h.hKl1
  rw [h.hc1val]
  nlinarith [hs4, h3, Real.sqrt_nonneg (μ / ρz)]

lemma FsI1Regime.c2_pos {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : 0 < c2 := by
  have h1 : 0 < (Kl * d * s)⁻¹ := inv_pos.mpr (mul_pos (mul_pos h.hKl h.hd) h.hs)
  have h2 : 0 < Real.sqrt (μ / ρz) := Real.sqrt_pos.mpr (div_pos h.hμ h.hρz)
  rw [h.hc2val]
  exact mul_pos (mul_pos (by norm_num) h1) h2

lemma FsI1Regime.fsTau_le {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ} (hr : 0 ≤ r) :
    Work.BoseB6.fsTau εT c1 c2 r ≤ r ^ 2 :=
  fsTau_le_sq h.hε0 h.hε1 h.hc1 h.hc12 hr

lemma FsI1Regime.fsTau_nonneg' {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ Work.BoseB6.fsTau εT c1 c2 r :=
  fsTau_nonneg h.hε0 (by linarith [h.hε1]) hr

lemma FsZeroRegime.n_pos {n : ℕ} {K : FsKernel} {a R ρz ℓ μ z chiM δ εT c1 c2 Kl s d : ℝ}
    (h : FsZeroRegime n K a R ρz ℓ μ z chiM δ εT c1 c2 Kl s d) : 0 < (n : ℝ) + 1 := by
  have := h.hn
  positivity

/-! ## The cutoffs against FS's error

FS's error `ε(μ,ρ_z)` (`eq:LebesgueError-Total`) dominates each of the cutoffs:
the `(K_ℓs)^{-1}` summand is bigger than `c₁` and the `ε_T(K_ℓds)^{-1}` summand is
bigger than `ε_T c₂` (as `c₂ = ½(K_ℓds)^{-1}√(μ/ρ_z)` with `√(μ/ρ_z) ≤ 2`).  The
region estimates of the `I₁` bound (`reg_small`, `reg_mid`, `reg_far`) use these
comparisons to convert every term of the pointwise bound into a multiple of `ε`.
-/

lemma FsI1Regime.sqrt_mu_div_rhoz_le_two {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : Real.sqrt (μ / ρz) ≤ 2 := by
  have h1 : μ / ρz ≤ 4 := by
    rw [div_le_iff₀ h.hρz]
    linarith [h.hclose1, h.hμ]
  calc Real.sqrt (μ / ρz) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h1
    _ = 2 := by norm_num

/-- `1 ≤ d⁻¹` (from `d ≤ 1`), so `log d⁻¹ ≥ 0`. -/
lemma FsI1Regime.one_le_inv_d {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) : 1 ≤ d⁻¹ :=
  (one_le_inv₀ h.hd).mpr h.hd1

/-- The third summand of FS's error dominates `(K_ℓs)^{-1}`. -/
lemma FsI1Regime.lhyEps_ge_inv {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    (Kl * s)⁻¹ ≤ Work.BoseB6.lhyEps a R εT Kl s d μ := by
  have h1 : 0 ≤ Real.log d⁻¹ := Real.log_nonneg h.one_le_inv_d
  have h2 : 0 ≤ Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)) := Real.log_nonneg h.hlog1
  have h3 : 0 ≤ (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R :=
    mul_nonneg (Real.rpow_nonneg (mul_pos h.hμ h.ha).le _) (Real.sqrt_nonneg R)
  have h4 : 0 ≤ (Kl * s)⁻¹ := inv_nonneg.mpr (mul_pos h.hKl h.hs).le
  have h5 : 0 ≤ (Kl * d * s)⁻¹ := inv_nonneg.mpr (mul_pos (mul_pos h.hKl h.hd) h.hs).le
  have h6 : 0 ≤ εT * (Kl * d * s)⁻¹
      * (1 + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) :=
    mul_nonneg (mul_nonneg h.hε0 h5) (by linarith)
  have h8 : (Kl * s)⁻¹ * 1
      ≤ (Kl * s)⁻¹ * (1 + Real.log d⁻¹
        + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) h4
  calc (Kl * s)⁻¹ = (Kl * s)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (Kl * s)⁻¹ * (1 + Real.log d⁻¹
          + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) := h8
    _ ≤ (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R + εT
          + (Kl * s)⁻¹ * (1 + Real.log d⁻¹
            + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)))
          + εT * (Kl * d * s)⁻¹
            * (1 + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) := by
        have hA : (0 : ℝ) ≤ (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R + εT := by
          linarith [h3, h.hε0]
        have hB : (0 : ℝ) ≤ εT * (Kl * d * s)⁻¹
            * (1 + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) := h6
        calc (Kl * s)⁻¹ * (1 + Real.log d⁻¹
              + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)))
            ≤ ((μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R + εT)
              + (Kl * s)⁻¹ * (1 + Real.log d⁻¹
                + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) :=
              le_add_of_nonneg_left hA
          _ ≤ (((μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R + εT)
                + (Kl * s)⁻¹ * (1 + Real.log d⁻¹
                  + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))))
              + εT * (Kl * d * s)⁻¹
                * (1 + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) :=
              le_add_of_nonneg_right hB
          _ = (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R + εT
                + (Kl * s)⁻¹ * (1 + Real.log d⁻¹
                  + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)))
                + εT * (Kl * d * s)⁻¹
                  * (1 + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) := by ring
    _ = Work.BoseB6.lhyEps a R εT Kl s d μ := by rw [Work.BoseB6.lhyEps]

/-- The fourth summand of FS's error dominates `ε_T (K_ℓds)^{-1}`. -/
lemma FsI1Regime.lhyEps_ge_eT_inv {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    εT * (Kl * d * s)⁻¹ ≤ Work.BoseB6.lhyEps a R εT Kl s d μ := by
  rw [Work.BoseB6.lhyEps]
  have h1 : 0 ≤ Real.log d⁻¹ := Real.log_nonneg h.one_le_inv_d
  have h2 : 0 ≤ Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)) := Real.log_nonneg h.hlog1
  have h3 : 0 ≤ (μ * a) ^ (1 / 4 : ℝ) * Real.sqrt R :=
    mul_nonneg (Real.rpow_nonneg (mul_pos h.hμ h.ha).le _) (Real.sqrt_nonneg R)
  have h4 : 0 ≤ (Kl * s)⁻¹ := inv_nonneg.mpr (mul_pos h.hKl h.hs).le
  have h5 : 0 ≤ (Kl * d * s)⁻¹ := inv_nonneg.mpr (mul_pos (mul_pos h.hKl h.hd) h.hs).le
  have h6 : 0 ≤ (Kl * s)⁻¹
      * (1 + Real.log d⁻¹ + Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ))) :=
    mul_nonneg h4 (by linarith)
  have h7 : 0 ≤ εT * (Kl * d * s)⁻¹
      * Real.log (Kl * d * s / (μ * a ^ 3) ^ (1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg h.hε0 h5) h2
  nlinarith [h3, h6, h7, h.hε0]

/-- `c₁ ≤ 2ε`: FS's first cutoff `c₁ = ½(K_ℓs)^{-1}√(μ/ρ_z)` against the
`(K_ℓs)^{-1}` summand of FS's error. -/
lemma FsI1Regime.c1_le_eps {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    c1 ≤ 2 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  have h1 : 0 < (Kl * s)⁻¹ := inv_pos.mpr (mul_pos h.hKl h.hs)
  have h2 : c1 ≤ (Kl * s)⁻¹ := by
    rw [h.hc1val]
    nlinarith [h.sqrt_mu_div_rhoz_le_two, h1]
  linarith [h2, h.lhyEps_ge_inv]

/-- `ε_T c₂ ≤ ε`: FS's second cutoff against the `ε_T(K_ℓds)^{-1}` summand of
FS's error, using `c₂ = ½(K_ℓds)^{-1}√(μ/ρ_z) ≤ (K_ℓds)^{-1}`. -/
lemma FsI1Regime.eTc2_le_eps {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    εT * c2 ≤ Work.BoseB6.lhyEps a R εT Kl s d μ := by
  have h1 : 0 < (Kl * d * s)⁻¹ := inv_pos.mpr (mul_pos (mul_pos h.hKl h.hd) h.hs)
  have h2 : c2 ≤ (Kl * d * s)⁻¹ := by
    rw [h.hc2val]
    nlinarith [h.sqrt_mu_div_rhoz_le_two, h1]
  calc εT * c2 ≤ εT * (Kl * d * s)⁻¹ := mul_le_mul_of_nonneg_left h2 h.hε0
    _ ≤ Work.BoseB6.lhyEps a R εT Kl s d μ := h.lhyEps_ge_eT_inv

/-- `c₁ + ε_T c₂ ≤ 3ε`. -/
lemma FsI1Regime.c1_add_eTc2_le {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    c1 + εT * c2 ≤ 3 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  linarith [h.c1_le_eps, h.eTc2_le_eps]

/-- `η ≤ ε` (the regime field `hEpsEta`, named for the region estimates). -/
lemma FsI1Regime.eta_le_eps {K : FsKernel} {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    K.η ≤ Work.BoseB6.lhyEps a R εT Kl s d μ := h.hEpsEta

end Work.BoseB6Est
