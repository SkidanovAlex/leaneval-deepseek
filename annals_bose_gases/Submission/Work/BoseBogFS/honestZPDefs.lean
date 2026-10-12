import ChallengeDeps
import Submission.Work.BoseBogFS.exists_fsKernel_affine
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestZPDefs` — the honest `FsBogData` data for the zero-point slot

`FINDING_honestZP_design.md` §1 fixes the design of the honest `FsBogData n` at

`D μ = Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ`, `E := (D μ).E`, `ℓ := sideAt μ (a v)`.
This module implements the **data**:

* `honestN` — the mesh size `n`, with `(n + 1) = 2⌈ℓ√(ρ a v)/2⌉` (even, so `gridD n = (n+1)²`
  is divisible by `4`, which `meshInj` needs) and `hmis` with `η = 2/(ℓ√(ρ a v))`;
* `honestZPη`, `honestZPT` — the affine kernel's parameters
  `K.η = 16πR√(ρ_z a v)`, `K.T = √3·(2π·N/ℓ)/√(ρ_z a v) + 1`;
* `honestK` — the kernel `K : FsKernel` (`Work.BoseBogFS.exists_fsKernel_affine`) with its
  profile `honestK_beta`;
* `honestXh` — the localisation `χh t = if ‖t‖ ≤ K.T then √(ℓ³)·χ̂((n+1) • t) else 0`, with
  `honestXh_supp`.

The choice `chiM = 1` (with the `√(ℓ³)` scaling of `χh`) is forced: `hG0` demands
`fsG0 = 8π a·chiM ≤ 8π a`, while `hχnorm` needs `Σ_k χh(t_k)² ≤ ℓ³ chiM`; the `ℓ³`-scaled choice
`χh = ℓ³χ̂(·)` satisfies the latter with `chiM = ℓ³` and fails the former.

The two remaining χ-bricks live in separate modules (delegated, so that this one stays
`sorry`-free):

* `Work.BoseBogFS.honestN_smul_modePos` — `(n+1) • modePos n k = (1/2) • vec (2k − gridD n)`;
* `Work.BoseBogFS.honestχnorm` — `chiSqSum (honestN v μ ρ) (honestXh v μ ρ N K) ≤ ℓ³·1·(1+0)`,
  from the shifted-cube Parseval row `Work.BoseBogFS.sum_hatChi_shifted_cube_le`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## 1. The mesh size -/

/-- The mesh size of the honest `FsBogData`: `n + 1 = 2⌈ℓ√(ρ·a v)/2⌉`, so that `n + 1` is even
(hence `gridD n = (n+1)²` is divisible by `4`, as `Work.BoseBogFS.meshInj` needs) and
`|(n:ℝ)+1 − ℓ√(ρ a v)| < 2`. -/
def honestN (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) : ℕ :=
  2 * Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2) - 1

/-- The mesh size is odd (so `(n:ℝ)+1` is even). -/
theorem honestN_odd (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (hc : 1 ≤ Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)) :
    honestN v μ ρ + 1
      = 2 * Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2) := by
  rw [honestN]
  omega

/-- `(honestN v μ ρ : ℝ) + 1 = 2⌈ℓ√(ρ a v)/2⌉`. -/
theorem honestN_succ (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (hc : 1 ≤ Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)) :
    ((honestN v μ ρ : ℕ) : ℝ) + 1
      = 2 * (Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2) : ℝ) := by
  have hidx := honestN_odd v μ ρ hc
  rw [show ((honestN v μ ρ : ℕ) : ℝ) + 1 = ((honestN v μ ρ + 1 : ℕ) : ℝ) by push_cast; ring,
    hidx]
  push_cast
  ring

/-- `gridD (honestN v μ ρ) = 2·(2c²)` with `c = ⌈ℓ√(ρ a v)/2⌉`, hence divisible by `4`. -/
theorem honestN_grid (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (hc : 1 ≤ Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)) :
    Work.BoseB6.gridD (honestN v μ ρ)
      = 2 * (2 * Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)
          * Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)) := by
  have hidx := honestN_odd v μ ρ hc
  rw [Work.BoseB6.gridD, hidx]
  ring

/-! ## 2. The affine kernel -/

/-- The affine kernel's closeness parameter `K.η = 16πR√(ρ_z a v)`. -/
def honestZPη (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R ρ : ℝ) : ℝ := 16 * π * R * Real.sqrt (ρ * a v)

/-- The affine kernel's momentum cutoff `K.T`: the box's maximal mode norm in `t`-units,
`√3·(2π·N/ℓ)/√(ρ_z a v) + 1`, so that `E.W1 = ζ·Ŵ₁` never sees the kernel's support on the box's
mode range (`FINDING_honest_rows_session7.md` (d)). -/
def honestZPT (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt 3 * (2 * π * (N : ℝ) / Work.BoseFixR.ell v μ) / Real.sqrt (ρ * a v) + 1

/-- The honest affine kernel (`Work.BoseBogFS.exists_fsKernel_affine`). -/
def honestK (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ ρ : ℝ) (N : ℕ)
    (hη : 0 ≤ honestZPη v R ρ) (hT : 0 ≤ honestZPT v μ ρ N) :
    Work.BoseB6Est.FsKernel :=
  (exists_fsKernel_affine (η := honestZPη v R ρ) (T := honestZPT v μ ρ N) hη hT).choose

/-- The kernel's closeness parameter. -/
theorem honestK_eta (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ ρ : ℝ) (N : ℕ)
    (hη : 0 ≤ honestZPη v R ρ) (hT : 0 ≤ honestZPT v μ ρ N) :
    (honestK v R μ ρ N hη hT).η = honestZPη v R ρ :=
  (exists_fsKernel_affine (η := honestZPη v R ρ) (T := honestZPT v μ ρ N) hη hT).choose_spec.1

/-- The kernel's momentum cutoff. -/
theorem honestK_T (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ ρ : ℝ) (N : ℕ)
    (hη : 0 ≤ honestZPη v R ρ) (hT : 0 ≤ honestZPT v μ ρ N) :
    (honestK v R μ ρ N hη hT).T = honestZPT v μ ρ N :=
  (exists_fsKernel_affine (η := honestZPη v R ρ) (T := honestZPT v μ ρ N) hη hT).choose_spec.2.1

/-- The kernel's profile on the mode range. -/
theorem honestK_beta (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ ρ : ℝ) (N : ℕ)
    (hη : 0 ≤ honestZPη v R ρ) (hT : 0 ≤ honestZPT v μ ρ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ honestZPT v μ ρ N) :
    (honestK v R μ ρ N hη hT).β r = 8 * π + honestZPη v R ρ * r :=
  (exists_fsKernel_affine (η := honestZPη v R ρ) (T := honestZPT v μ ρ N) hη hT).choose_spec.2.2.1
    r hr0 hr

/-- The kernel vanishes beyond its cutoff. -/
theorem honestK_beta_zero (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ ρ : ℝ) (N : ℕ)
    (hη : 0 ≤ honestZPη v R ρ) (hT : 0 ≤ honestZPT v μ ρ N) {r : ℝ}
    (hr : honestZPT v μ ρ N < r) : (honestK v R μ ρ N hη hT).β r = 0 :=
  (exists_fsKernel_affine (η := honestZPη v R ρ) (T := honestZPT v μ ρ N) hη hT).choose_spec.2.2.2
    r hr

/-! ## 3. The localisation -/

/-- The honest localisation: `χh t = √(ℓ³)·χ̂((n+1) • t)` on the kernel's support, `0` beyond.
The scaling `√(ℓ³)` (not `ℓ³`) is what makes `hχnorm` and `hG0` both hold.  The domain is
`Fin 3 → ℝ` (the convention of `Work.BoseB6Est.χh`) with the Euclidean norm
`Work.BoseB6Est.nrm`; `WithLp.toLp 2` converts to the `EuclideanSpace` expected by
`corpusBox.hatChi`. -/
def honestXh (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (N : ℕ)
    (K : Work.BoseB6Est.FsKernel) : (Fin 3 → ℝ) → ℝ :=
  fun t => if Work.BoseB6Est.nrm t ≤ K.T
    then Real.sqrt (Work.BoseFixR.ell v μ ^ 3)
      * Work.BoseK15.corpusBox.hatChi (WithLp.toLp 2 ((((honestN v μ ρ : ℕ) : ℝ) + 1) • t))
    else 0

/-- `χh` vanishes beyond the kernel's cutoff. -/
theorem honestXh_supp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (N : ℕ)
    (K : Work.BoseB6Est.FsKernel) {t : Fin 3 → ℝ} (ht : K.T < Work.BoseB6Est.nrm t) :
    honestXh v μ ρ N K t = 0 := by
  rw [honestXh]
  exact if_neg (not_le.mpr ht)

end Work.BoseBogFS
