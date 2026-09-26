import Mathlib
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresExpansion
import Submission.Work.Asymptotics.KhatE1.ZAtomsSecondOrder

/-!
# The `z`-atom substitutions for the residual of the sharp tail bound

`KhatE1.KdevWresClearedPolyFullJF_eq` writes the cleared residual of the sharp tail bound as an
explicit `j(τ)`-free polynomial in the `z`-atoms.  To read that expression as a polynomial in
`u = Ept z` one substitutes the cusp expansions of the `z`-atoms.  Two of them do **not** yet
appear in truncated form in that expression (the `*ref` atoms `E₆ref,E₈ref,E₁₀ref,Wref,D2ref,
Lref` and the deviations `dW,dD2,dL,dE₈,dE₆,dE₁₀` are already truncated):

* `E₂(z)`, occurring in `PhiMain` and (through `phitVec = (z², z²E₂ˢ, z²(E₂ˢ)²)`) in
  `kdevDir`/`kdevNum0`;
* `Δ(z)`, occurring in `kdevSig2JF` as `φ₂(τ)E₁₄(τ)z²Δ(z)`.

Here we name their deviations from the second-order truncations
(`dE2z`, `dDz`), record the bounds `‖dE2z z‖ ≤ C‖q(z)‖³`, `‖dDz z‖ ≤ C‖q(z)‖⁴` in the plain
`qParamFun`-norm form (extracted from the proved `ZAtomsSecondOrder`), and split `PhiMain` — a
polynomial of degree two in `E₂(z)` — into its truncated part plus the linear and quadratic
deviation terms.  This is the pass that turns the residual into (a polynomial in `u`) +
(explicit deviation terms).
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- The second-order truncation of `E₂(z)`: `1 - 24q(z) - 72q(z)²`. -/
def E2Ztr (z : ℍ) : ℂ :=
  1 - 24 * Work.Kernels.qParamFun z - 72 * (Work.Kernels.qParamFun z) ^ 2

/-- The third-order truncation of `Δ(z)`: `q(z) - 24q(z)² + 252q(z)³`. -/
def DeltaZtr (z : ℍ) : ℂ :=
  Work.Kernels.qParamFun z - 24 * (Work.Kernels.qParamFun z) ^ 2
    + 252 * (Work.Kernels.qParamFun z) ^ 3

/-- The deviation of `E₂(z)` from its second-order truncation. -/
def dE2z (z : ℍ) : ℂ := Work.Kernels.E2Fun z - E2Ztr z

/-- The deviation of `Δ(z)` from its third-order truncation. -/
def dDz (z : ℍ) : ℂ := Work.Kernels.DeltaFun z - DeltaZtr z

/-- `E₂(z) = E2Ztr z + dE2z z`. -/
theorem E2Fun_eq_trunc_add (z : ℍ) :
    Work.Kernels.E2Fun z = E2Ztr z + dE2z z := by
  rw [dE2z]; ring

/-- `Δ(z) = DeltaZtr z + dDz z`. -/
theorem DeltaFun_eq_trunc_add (z : ℍ) :
    Work.Kernels.DeltaFun z = DeltaZtr z + dDz z := by
  rw [dDz]; ring

/-- **`dE2z z = O(‖q(z)‖³)`** (plain `qParamFun`-norm form of `ZAtomsSecondOrder`). -/
theorem exists_dE2z_bound :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : ℍ, T ≤ z.im → ‖dE2z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨T, hT, _, _, h2, _, _, _, _, _⟩ := ZAtomsSecondOrder
  obtain ⟨C, hC, h⟩ := h2
  refine ⟨T, C, hT, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [dE2z, E2Ztr]
  convert h' using 2 <;> ring

/-- **`dDz z = O(‖q(z)‖⁴)`** (plain `qParamFun`-norm form of `ZAtomsSecondOrder`). -/
theorem exists_dDz_bound :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : ℍ, T ≤ z.im → ‖dDz z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
  obtain ⟨T, hT, _, _, _, h4, _, _, _, _⟩ := ZAtomsSecondOrder
  obtain ⟨C, hC, h⟩ := h4
  refine ⟨T, C, hT, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [dDz, DeltaZtr]
  convert h' using 2 <;> ring

/-- **The `E₂`-split of `PhiMain`.**  `PhiMain` is a polynomial of degree two in `E₂(z)`; here it
is written as its truncated part `PhiMainTrunc` plus the linear and quadratic deviation terms.
`PhiMainTrunc τ z` is `PhiMain` with `E₂(z)` replaced by `E2Ztr z`. -/
def PhiMainTrunc (τ z : ℍ) : ℂ :=
  (E2Ztr z - 1) * ((τ : ℂ) * Work.Kernels.E6Fun τ *
      (-((z : ℂ) ^ 2 * (1 + E2Ztr z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
    + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)

/-- The linear coefficient of `dE2z` in `PhiMain`. -/
def PhiMainLin (τ z : ℍ) : ℂ :=
  ((τ : ℂ) * Work.Kernels.E6Fun τ *
      (-((z : ℂ) ^ 2 * (1 + E2Ztr z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
    + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)
    + (E2Ztr z - 1) * (-((τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2))

/-- **`PhiMain = PhiMainTrunc + dE2z·PhiMainLin + dE2z²·(-τE₆(τ)z²)`.** -/
theorem PhiMain_split (τ z : ℍ) :
    Work.Asymptotics.Compact.PhiMain τ z
      = PhiMainTrunc τ z + dE2z z * PhiMainLin τ z
        + (dE2z z) ^ 2 * (-((τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2)) := by
  rw [Work.Asymptotics.Compact.PhiMain, PhiMainTrunc, PhiMainLin, E2Fun_eq_trunc_add z]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- The second-order truncation of `E₄(z)`: `1 + 240q(z) + 2160q(z)²`. -/
def E4Ztr (z : ℍ) : ℂ :=
  1 + 240 * Work.Kernels.qParamFun z + 2160 * (Work.Kernels.qParamFun z) ^ 2

/-- The second-order truncation of `E₆(z)`: `1 - 504q(z) - 16632q(z)²`. -/
def E6Ztr (z : ℍ) : ℂ :=
  1 - 504 * Work.Kernels.qParamFun z - 16632 * (Work.Kernels.qParamFun z) ^ 2

/-- The deviation of `E₄(z)` from its second-order truncation. -/
def dE4z (z : ℍ) : ℂ := Work.Kernels.E4Fun z - E4Ztr z

/-- The deviation of `E₆(z)` from its second-order truncation. -/
def dE6z (z : ℍ) : ℂ := Work.Kernels.E6Fun z - E6Ztr z

theorem E4Fun_eq_trunc_add (z : ℍ) : Work.Kernels.E4Fun z = E4Ztr z + dE4z z := by
  rw [dE4z]; ring

theorem E6Fun_eq_trunc_add (z : ℍ) : Work.Kernels.E6Fun z = E6Ztr z + dE6z z := by
  rw [dE6z]; ring

/-- **`dE4z z = O(‖q(z)‖³)`**. -/
theorem exists_dE4z_bound :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : ℍ, T ≤ z.im → ‖dE4z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨T, hT, hE4, _, _, _, _, _, _, _⟩ := ZAtomsSecondOrder
  obtain ⟨C, hC, h⟩ := hE4
  refine ⟨T, C, hT, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [dE4z, E4Ztr]
  convert h' using 2 <;> ring

/-- **`dE6z z = O(‖q(z)‖³)`**. -/
theorem exists_dE6z_bound :
    ∃ T C : ℝ, 1 ≤ T ∧ 0 < C ∧ ∀ z : ℍ, T ≤ z.im → ‖dE6z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨T, hT, _, hE6, _, _, _, _, _, _⟩ := ZAtomsSecondOrder
  obtain ⟨C, hC, h⟩ := hE6
  refine ⟨T, C, hT, hC, fun z hz => ?_⟩
  have h' := h z hz
  rw [dE6z, E6Ztr]
  convert h' using 2 <;> ring

/-- The second-order truncation of `Gt z = z·E₂(z) - 6i/π` (the `phitVec` generator). -/
def GtTr (z : ℍ) : ℂ := (z : ℂ) * E2Ztr z - 6 * Complex.I / (Real.pi : ℂ)

/-- **`Gt z = GtTr z + z·dE2z z`.** -/
theorem Gt_eq_trunc_add (z : ℍ) :
    Work.Kernels.TildeFacts.Gt z = GtTr z + (z : ℂ) * dE2z z := by
  rw [Work.Kernels.TildeFacts.Gt, GtTr, E2Fun_eq_trunc_add z]
  ring

/-- Truncation of `phitVec z 1 = z·Gt z`. -/
def phit1Ztr (z : ℍ) : ℂ := (z : ℂ) * GtTr z

/-- Truncation of `phitVec z 2 = (Gt z)²`. -/
def phit2Ztr (z : ℍ) : ℂ := (GtTr z) ^ 2

/-- **`phitVec z 1 = phit1Ztr z + z·(z·dE2z z)`.** -/
theorem phitVec_one_split (z : ℍ) :
    Work.Kernels.phitVec z 1 = phit1Ztr z + (z : ℂ) * ((z : ℂ) * dE2z z) := by
  rw [Work.Kernels.TildeFacts.phitVec_one z, phit1Ztr, Gt_eq_trunc_add z]
  ring

/-- **`phitVec z 2 = phit2Ztr z + 2·GtTr z·(z·dE2z z) + (z·dE2z z)²`.** -/
theorem phitVec_two_split (z : ℍ) :
    Work.Kernels.phitVec z 2
      = phit2Ztr z + 2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2 := by
  rw [Work.Kernels.TildeFacts.phitVec_two z, phit2Ztr, Gt_eq_trunc_add z]
  ring

/-- The truncated `kdevDir`: `phitVec` replaced by `phit1Ztr`, `phit2Ztr`. -/
def kdevDirTrunc (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ * phit2Ztr z
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * phit1Ztr z

/-- **The `phitVec`-split of `kdevDir`.**  `kdevDir` is linear in `phitVec`, so its split is the
combination of `phitVec_one_split` and `phitVec_two_split`. -/
theorem kdevDir_split (τ z : ℍ) :
    kdevDir τ z
      = kdevDirTrunc τ z
        + (τ : ℂ) * Work.Kernels.E6Fun τ
            * (2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2)
        - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * ((z : ℂ) * ((z : ℂ) * dE2z z)) := by
  rw [kdevDir, kdevDirTrunc, phitVec_one_split z, phitVec_two_split z]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The `kdevSig2JF` with the single `Δ(z)`-occurrence truncated: `DeltaFun z ↦ DeltaZtr z`.
`kdevSig2JF` is *linear* in `Δ(z)` (it occurs only inside the `φ₂(τ)E₁₄(τ)z²Δ(z)` term), so the
split needs no quadratic piece. -/
def kdevSig2JFZtr (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
      (Work.Kernels.DeltaFun τ * br8refJF ℓ τ z
        + Work.Kernels.DeltaFun τ * Dev8RawJF ℓ τ z)
    - Work.Asymptotics.Compact.tailC⁻¹ *
        (Work.Kernels.DeltaFun τ *
          (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              * DeltaZtr z
            + Work.Kernels.DeltaFun τ * kdevNum0 τ z))

/-- **The `Δ(z)`-split of `kdevSig2JF`.**  Since `Δ(z)` occurs only linearly (in the
`φ₂(τ)E₁₄(τ)z²Δ(z)` term), the split is truncation plus the single `dDz` term. -/
theorem kdevSig2JF_split (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevSig2JF ℓ τ z
      = kdevSig2JFZtr ℓ τ z
        - Work.Asymptotics.Compact.tailC⁻¹ *
            (Work.Kernels.DeltaFun τ *
              (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 * dDz z)) := by
  rw [kdevSig2JF, kdevSig2JFZtr, DeltaFun_eq_trunc_add z]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The truncated `kdevNum0`: `phitVec z 1 ↦ phit1Ztr z`, `phitVec z 2 ↦ phit2Ztr z`,
`E₄(z) ↦ E4Ztr z`, `E₆(z) ↦ E6Ztr z`. -/
def kdevNum0Ztr (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ * phit2Ztr z * (E4Ztr z) ^ 2
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * phit1Ztr z * E4Ztr z * E6Ztr z

/-- **The bilinear split of `kdevNum0`.**  `kdevNum0` is linear in
`phitVec z 1`, `phitVec z 2`, quadratic in `E₄(z)` and bilinear in `E₄(z),E₆(z)`; isolating the
two difference factors (`phitVec·E₄² - phit2Ztr·E4Ztr²` and
`phitVec z 1·E₄(z)E₆(z) - phit1Ztr·E4Ztr·E6Ztr`) keeps the deviations exact and the truncation
polynomial.  The first difference is `O(‖z‖²‖q(z)‖³)` and the second `O(‖z‖‖q(z)‖³)` on
`Im z ≥ T`, by `exists_dE2z_bound`, `exists_dE4z_bound`, `exists_dE6z_bound`. -/
theorem kdevNum0_split (τ z : ℍ) :
    kdevNum0 τ z
      = kdevNum0Ztr τ z
        + ((τ : ℂ) * Work.Kernels.E6Fun τ
              * (Work.Kernels.phitVec z 2 * (Work.Kernels.E4Fun z) ^ 2
                  - phit2Ztr z * (E4Ztr z) ^ 2)
            - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
              * (Work.Kernels.phitVec z 1 * Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
                  - phit1Ztr z * E4Ztr z * E6Ztr z)) := by
  rw [kdevNum0, kdevNum0Ztr]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `E2Ztr` as a polynomial in `u = Ept z` (`qParamFun z = (Ept z)²`). -/
theorem E2Ztr_eq_Ept (z : ℍ) :
    E2Ztr z = 1 - 24 * (Work.Residues.Ept z) ^ 2 - 72 * (Work.Residues.Ept z) ^ 4 := by
  rw [E2Ztr, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

/-- `E4Ztr` as a polynomial in `u = Ept z`. -/
theorem E4Ztr_eq_Ept (z : ℍ) :
    E4Ztr z = 1 + 240 * (Work.Residues.Ept z) ^ 2 + 2160 * (Work.Residues.Ept z) ^ 4 := by
  rw [E4Ztr, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

/-- `E6Ztr` as a polynomial in `u = Ept z`. -/
theorem E6Ztr_eq_Ept (z : ℍ) :
    E6Ztr z = 1 - 504 * (Work.Residues.Ept z) ^ 2 - 16632 * (Work.Residues.Ept z) ^ 4 := by
  rw [E6Ztr, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

/-- `DeltaZtr` as a polynomial in `u = Ept z`. -/
theorem DeltaZtr_eq_Ept (z : ℍ) :
    DeltaZtr z = (Work.Residues.Ept z) ^ 2 - 24 * (Work.Residues.Ept z) ^ 4
      + 252 * (Work.Residues.Ept z) ^ 6 := by
  rw [DeltaZtr, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

/-- `GtTr` as a polynomial in `u = Ept z` (with the explicit `z`-factor kept). -/
theorem GtTr_eq_Ept (z : ℍ) :
    GtTr z = (z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2 - 72 * (Work.Residues.Ept z) ^ 4)
      - 6 * Complex.I / (Real.pi : ℂ) := by
  rw [GtTr, E2Ztr_eq_Ept z]

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The truncated `Δ(τ)Sh(τ,z) = Δ(τ)E₄(z)³ − Δ(z)E₄(τ)³`: both `z`-atoms replaced by their
truncations. -/
def ShDeltaZtr (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (E4Ztr z) ^ 3 - DeltaZtr z * (Work.Kernels.E4Fun τ) ^ 3

/-- **The split of the factor `Δ(τ)E₄(z)³ − Δ(z)E₄(τ)³`.**  Binomial on the cube of `E₄(z)`,
linear on `Δ(z)`: the three `dE4z`-terms and the single `dDz`-term are isolated exactly. -/
theorem ShDelta_split (τ z : ℍ) :
    Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun z) ^ 3
        - Work.Kernels.DeltaFun z * (Work.Kernels.E4Fun τ) ^ 3
      = ShDeltaZtr τ z
        + Work.Kernels.DeltaFun τ
            * (3 * (E4Ztr z) ^ 2 * dE4z z + 3 * E4Ztr z * (dE4z z) ^ 2 + (dE4z z) ^ 3)
        - dDz z * (Work.Kernels.E4Fun τ) ^ 3 := by
  rw [ShDeltaZtr, E4Fun_eq_trunc_add z, DeltaFun_eq_trunc_add z]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The truncated `kdevA2JF`: `PhiMain ↦ PhiMainTrunc`, `kdevDir ↦ kdevDirTrunc`. -/
def kdevA2JFZtr (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹ * PhiMainTrunc τ z)
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
        * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.br0 8 ℓ τ z
            - Work.Residues.Ept z * R8p0JF ℓ τ)
    + Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹ * kdevDirTrunc τ z)

/-- **The `kdevA2JF` split.**  `kdevA2JF` contains the `z`-atoms `E₂(z)` only through `PhiMain`
(degree two in `E₂`) and `kdevDir` (linear in `phitVec`); both are replaced by their truncations,
with the `dE2z`-terms isolated exactly. -/
theorem kdevA2JF_split (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevA2JF ℓ τ z
      = kdevA2JFZtr ℓ τ z
        + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹
            * (dE2z z * PhiMainLin τ z
                + (dE2z z) ^ 2 * (-((τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2)))
        + Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹
            * ((τ : ℂ) * Work.Kernels.E6Fun τ
                * (2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2)
              - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                  * ((z : ℂ) * ((z : ℂ) * dE2z z))) := by
  rw [kdevA2JF, kdevA2JFZtr, PhiMain_split τ z, kdevDir_split τ z]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The raw `Sh`-factor `Δ(τ)E₄(z)³ − Δ(z)E₄(τ)³`. -/
def Shr (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun z) ^ 3
    - Work.Kernels.DeltaFun z * (Work.Kernels.E4Fun τ) ^ 3

/-- The deviation part of `Shr` (from `ShDelta_split`). -/
def ShDev (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ
      * (3 * (E4Ztr z) ^ 2 * dE4z z + 3 * E4Ztr z * (dE4z z) ^ 2 + (dE4z z) ^ 3)
    - dDz z * (Work.Kernels.E4Fun τ) ^ 3

/-- The `dE2z`-deviation part of `kdevA2JF` (from `kdevA2JF_split`). -/
def KdevA2Dev (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.tailC⁻¹
    * (dE2z z * PhiMainLin τ z
        + (dE2z z) ^ 2 * (-((τ : ℂ) * Work.Kernels.E6Fun τ * (z : ℂ) ^ 2))
        + ((τ : ℂ) * Work.Kernels.E6Fun τ
              * (2 * GtTr z * ((z : ℂ) * dE2z z) + ((z : ℂ) * dE2z z) ^ 2)
            - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
                * ((z : ℂ) * ((z : ℂ) * dE2z z))))

/-- The `dDz`-deviation part of `kdevSig2JF` (from `kdevSig2JF_split`). -/
def KdevSig2Dev (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  - Work.Asymptotics.Compact.tailC⁻¹
      * (Work.Kernels.DeltaFun τ
          * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 * dDz z))

/-- **The polynomial part of the cleared residual**: all `z`-atoms replaced by their truncations,
hence (after `*_eq_Ept`) a literal polynomial in `u = Ept z` with `τ`-atom and `Xc`, `z`
coefficients. -/
def WresPoly (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (kdevA2JFZtr ℓ τ z
      - 2 * (Work.Residues.Ept z) ^ 2 * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
    * ShDeltaZtr τ z
  + kdevSig2JFZtr ℓ τ z

/-- **The cleared residual of the sharp tail bound equals its polynomial part plus three
explicit deviation terms.**  Assembly of `kdevA2JF_split`, `kdevSig2JF_split` and
`ShDelta_split` inside `KdevWresClearedPolyFullJF_eq`: the deviation of the first factor acts on
the *truncated* second factor and vice versa, which is exactly the three correction terms listed.
After `E2Ztr_eq_Ept`…`GtTr_eq_Ept`, `WresPoly` is a polynomial in `u = Ept z`. -/
theorem KdevWresClearedPoly_decomp (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0)
    (hΔ : Work.Kernels.DeltaFun τ ≠ 0) :
    Work.Kernels.DeltaFun τ *
        (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.Sh τ z *
          (Work.Asymptotics.KhatE1Core.Kdev8Bracket ℓ τ z
            - 2 * KdevE2 ℓ τ z * (Work.Residues.Ept z) ^ 2))
      = WresPoly ℓ τ z
        + (kdevA2JF ℓ τ z
            - 2 * (Work.Residues.Ept z) ^ 2 * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * ShDev τ z
        + KdevA2Dev ℓ τ z * ShDeltaZtr τ z
        + KdevSig2Dev ℓ τ z := by
  rw [KdevWresClearedPolyFullJF_eq ℓ τ z hSh hΔ, kdevA2JF_split ℓ τ z,
    kdevSig2JF_split ℓ τ z, ShDelta_split τ z,
    WresPoly, KdevA2Dev, KdevSig2Dev, ShDev]
  simp only [ShDeltaZtr, kdevA2JFZtr, kdevSig2JFZtr, E2Ztr, E4Ztr, E6Ztr, DeltaZtr,
    GtTr, dE2z, dDz, dE4z, PhiMainTrunc, PhiMainLin, kdevDirTrunc]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- **The `u⁰`-rung input.**  Every truncated `z`-atom differs from its value at `u = 0`
(`E2Ztr 0 = 1`, `E4Ztr 0 = 1`, `E6Ztr 0 = 1`, `DeltaZtr 0 = 0`, `GtTr 0 = -6i/π`) by an explicit
multiple of `u²` (resp. `u`).  Consequently the constant term of any polynomial in these atoms is
obtained by the substitution `E2Ztr,E4Ztr,E6Ztr ↦ 1`, `DeltaZtr ↦ 0`, `GtTr ↦ -6i/π`, `Ept ↦ 0`,
and the `u⁰`-cancellation becomes a finite `ring` identity. -/
theorem E2Ztr_sub_one (z : ℍ) :
    E2Ztr z - 1 = (Work.Residues.Ept z) ^ 2 * (-24 - 72 * (Work.Residues.Ept z) ^ 2) := by
  rw [E2Ztr_eq_Ept z]; ring

/-- `E4Ztr z - 1 = u²·(240 + 2160u²)`. -/
theorem E4Ztr_sub_one (z : ℍ) :
    E4Ztr z - 1 = (Work.Residues.Ept z) ^ 2 * (240 + 2160 * (Work.Residues.Ept z) ^ 2) := by
  rw [E4Ztr_eq_Ept z]; ring

/-- `E6Ztr z - 1 = u²·(-504 - 16632u²)`. -/
theorem E6Ztr_sub_one (z : ℍ) :
    E6Ztr z - 1 = (Work.Residues.Ept z) ^ 2 * (-504 - 16632 * (Work.Residues.Ept z) ^ 2) := by
  rw [E6Ztr_eq_Ept z]; ring

/-- `DeltaZtr z = u²·(1 - 24u² + 252u⁴)` (so `DeltaZtr` has no constant term). -/
theorem DeltaZtr_factor (z : ℍ) :
    DeltaZtr z = (Work.Residues.Ept z) ^ 2
      * (1 - 24 * (Work.Residues.Ept z) ^ 2 + 252 * (Work.Residues.Ept z) ^ 4) := by
  rw [DeltaZtr_eq_Ept z]; ring

/-- `GtTr z = z + u²·(z·(-24 - 72u²)) - 6i/π`, i.e. the deviation of `GtTr` from its value at
`u = 0`, which is `z - 6i/π` (note the explicit `z`: `z` is not a `u`-atom). -/
theorem GtTr_sub_const (z : ℍ) :
    GtTr z - ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
      = (Work.Residues.Ept z) ^ 2 * ((z : ℂ) * (-24 - 72 * (Work.Residues.Ept z) ^ 2)) := by
  rw [GtTr_eq_Ept z]; ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `kdevDir` evaluated at `u = 0` (using `GtTr|₀ = z - 6i/π`, so
`phitVec z 1 ↦ z(z - 6i/π)`, `phitVec z 2 ↦ (z - 6i/π)²`). -/
def kdevDirAt0 (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
        * ((z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)))

/-- The `u = 0` value of `kdevA2JFZtr`: `PhiMainTrunc|₀ = 0` (its `E2Ztr - 1` factor) and the
`Ept z·R8p0JF` term drops out. -/
def kdevA2At0 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      * (Work.Kernels.DeltaFun τ * Work.Asymptotics.Compact.br0 8 ℓ τ z)
    + Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹ * kdevDirAt0 τ z)

/-- The `u = 0` value of `kdevSig2JFZtr`: `Dev8RawJF|₀ = 0`, `DeltaZtr|₀ = 0`,
`br8refJF|₀ = -Δ(τ)·br0 8|₀` and `kdevNum0|₀ = kdevDirAt0`. -/
def kdevSig2At0 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
      * (Work.Kernels.DeltaFun τ *
          ((-3456 : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
              * Work.Asymptotics.Compact.Xc ℓ z
            + 1728 * Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ))
    - Work.Asymptotics.Compact.tailC⁻¹
        * (Work.Kernels.DeltaFun τ * (Work.Kernels.DeltaFun τ * kdevDirAt0 τ z))

/-- **The `u⁰`-coefficient identity.**  With the corrected substitution (`GtTr|₀ = z - 6i/π`,
`ShDeltaZtr|₀ = Δ(τ)`), the constant term of `WresPoly` is
`kdevA2At0·Δ(τ) + kdevSig2At0`, and it vanishes: the two `(3456π)⁻¹`-terms cancel through
`br8refJF|₀ = -Δ(τ)·br0 8|₀` and the two `tailC⁻¹`-terms through `kdevNum0|₀ = kdevDir|₀`. -/
theorem WresPolyAt0_eq_zero (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevA2At0 ℓ τ z * Work.Kernels.DeltaFun τ + kdevSig2At0 ℓ τ z = 0 := by
  have hbr : Work.Asymptotics.Compact.br0 8 ℓ τ z
      = 3456 * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z
        - 1728 * Work.Kernels.psi4 ℓ τ := by
    rw [Work.Asymptotics.Compact.br0, Work.Asymptotics.Compact.Gminus, if_pos rfl,
      Work.Asymptotics.Compact.Gminus8, Work.Asymptotics.Compact.Xc]
    field_simp
    ring
  rw [kdevA2At0, kdevSig2At0, kdevDirAt0, hbr]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- **The `u¹`-rung: the first-order term of `br8refJF` is `R8p0JF·u`.**

Subtracting the claimed first-order part `R8p0JF ℓ τ · u` leaves an expression whose four
`u`-dependent bracket factors are *even* in `u` (their `u¹`-coefficients vanish):
`E₁₀ref·Lref + 8u`, `E₈ref·Wref - E₆ref·D2ref + 24u`, `E₈ref·Wref + 8u`, `E₆ref·D2ref - 16u`
(using `Lref|₁ = -8`, `Wref|₁ = -8`, `D2ref|₁ = +16`, and `E₁₀ref|₀ = E₈ref|₀ = E₆ref|₀ = 1`).
This is the `u¹`-counterpart of `WresPolyAt0_eq_zero`: together with `-(3456π)⁻¹·u·R8p0JF` from
`kdevA2JFZtr`, the `D(τ)·R8p0JF`-terms cancel in the `u¹`-coefficient of `WresPoly`. -/
theorem br8refJF_u1 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJF ℓ τ z - R8p0JF ℓ τ * Work.Residues.Ept z
      = Work.Kernels.DeltaFun τ
          * (-3456 * Work.Kernels.E4Fun τ
              * (Work.Asymptotics.Compact.E10ref z * Work.Asymptotics.Compact.Lref ℓ z
                  + 8 * Work.Residues.Ept z))
        + Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ
            * (Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
                - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z
                + 24 * Work.Residues.Ept z)
        + Work.Kernels.psi4 ℓ τ
            * ((1728 * Work.Kernels.DeltaFun τ - (Work.Kernels.E4Fun τ) ^ 3)
                * (Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
                    + 8 * Work.Residues.Ept z)
              + (Work.Kernels.E4Fun τ) ^ 3
                * (Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z
                    - 16 * Work.Residues.Ept z)) := by
  rw [br8refJF, R8p0JF]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- **First bracket evenness lemma (`u¹`-coefficient vanishes).**

`E₁₀ref z·Lref ℓ z + 8·u` has *vanishing* `u¹`-coefficient: it differs from its value at `u = 0`
(namely `Xc ℓ z`) by an explicit multiple of `u²`:

  `(1 - 264u²)(Xc - 8u + 12u²) + 8u - Xc = u²·(12 - 264Xc + 2112u - 3168u²)`.

(CAREFUL: the factor is *not* even — the product creates a `u³`-term `2112u³`; what vanishes is
only the `u¹`-coefficient, which is all the `u¹`-rung needs.) -/
theorem E10ref_mul_Lref_sub_Xc (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    Work.Asymptotics.Compact.E10ref z * Work.Asymptotics.Compact.Lref ℓ z
        + 8 * Work.Residues.Ept z - Work.Asymptotics.Compact.Xc ℓ z
      = (Work.Residues.Ept z) ^ 2
          * (12 - 264 * Work.Asymptotics.Compact.Xc ℓ z
              + 2112 * Work.Residues.Ept z - 3168 * (Work.Residues.Ept z) ^ 2) := by
  rw [Work.Asymptotics.Compact.E10ref, Work.Asymptotics.Compact.Lref]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- **Second bracket lemma.**  `E₈ref·Wref - E₆ref·D2ref + 24u` has vanishing `u¹`-coefficient
(value `0` at `u = 0`). -/
theorem E8ref_Wref_sub_E6ref_D2ref (z : ℍ) :
    Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
        - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z
        + 24 * Work.Residues.Ept z
      = (Work.Residues.Ept z) ^ 2
          * (1152 + 4224 * Work.Residues.Ept z
              - 61056 * (Work.Residues.Ept z) ^ 2) := by
  rw [Work.Asymptotics.Compact.E8ref, Work.Asymptotics.Compact.Wref,
    Work.Asymptotics.Compact.E6ref, Work.Asymptotics.Compact.D2ref]
  ring

/-- **Third bracket lemma.**  `E₈ref·Wref + 8u` has the value `1` at `u = 0` and vanishing
`u¹`-coefficient. -/
theorem E8ref_Wref_add_Ept (z : ℍ) :
    Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
        + 8 * Work.Residues.Ept z - 1
      = (Work.Residues.Ept z) ^ 2
          * (504 - 3840 * Work.Residues.Ept z
              + 11520 * (Work.Residues.Ept z) ^ 2) := by
  rw [Work.Asymptotics.Compact.E8ref, Work.Asymptotics.Compact.Wref]
  ring

/-- **Fourth bracket lemma.**  `E₆ref·D2ref - 16u` has the value `1` at `u = 0` and vanishing
`u¹`-coefficient. -/
theorem E6ref_D2ref_sub_Ept (z : ℍ) :
    Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z
        - 16 * Work.Residues.Ept z - 1
      = (Work.Residues.Ept z) ^ 2
          * (-648 - 8064 * Work.Residues.Ept z
              + 72576 * (Work.Residues.Ept z) ^ 2) := by
  rw [Work.Asymptotics.Compact.E6ref, Work.Asymptotics.Compact.D2ref]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- **The `u²`-input for the `u²`-rung: `[br8refJF]_{u²}`.**

Assembled from the four first-order lemmas (`E10ref_mul_Lref_sub_Xc`,
`E8ref_Wref_sub_E6ref_D2ref`, `E8ref_Wref_add_Ept`, `E6ref_D2ref_sub_Ept`): the `u²`-coefficient
of `br8refJF` is

  `Δ(τ)(-3456E₄(τ))(12 - 264·Xc ℓ z) + 1152·ψ₂E₁₄ + 504(1728Δ(τ) - E₄(τ)³)ψ₄ - 648E₄(τ)³ψ₄`.

This is the quantity that has to meet its `R8_p2` counterpart (via the proved
`KhatE1.Kdev8BracketE2_eq_two_KdevE2`, which supplies the bracket's `E²`-coefficient `2·KdevE2`)
in the `u²` bookkeeping; see `.Kdev8TailSharpFleet_findings.md` §28. -/
def br8refJFAt2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (-3456 * Work.Kernels.E4Fun τ)
      * (12 - 264 * Work.Asymptotics.Compact.Xc ℓ z)
    + 1152 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ)
    + 504 * ((1728 * Work.Kernels.DeltaFun τ - (Work.Kernels.E4Fun τ) ^ 3)
        * Work.Kernels.psi4 ℓ τ)
    + (-648) * ((Work.Kernels.E4Fun τ) ^ 3 * Work.Kernels.psi4 ℓ τ)

/-- The collected form of `br8refJFAt2` (the §28 second line). -/
theorem br8refJFAt2_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJFAt2 ℓ τ z
      = -41472 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
        + 912384 * Work.Kernels.DeltaFun τ * Work.Kernels.E4Fun τ
            * Work.Asymptotics.Compact.Xc ℓ z
        + 1152 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ)
        + 870912 * Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ
        - 1152 * (Work.Kernels.E4Fun τ) ^ 3 * Work.Kernels.psi4 ℓ τ := by
  rw [br8refJFAt2]; ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `PhiMainTrunc|₂ = -24·(the `u = 0` bracket)`. -/
def PhiMainTruncAt2 (τ z : ℍ) : ℂ :=
  (-24) * ((τ : ℂ) * Work.Kernels.E6Fun τ
      * (-2 * (z : ℂ) ^ 2 + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
    + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)

/-- `kdevDirTrunc|₂`. -/
def kdevDirTruncAt2 (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ
      * (-48 * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)))
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (-24 * (z : ℂ) ^ 2)

/-- `kdevA2JFZtr|₂`: only the `PhiMainTrunc` and `kdevDirTrunc` slots carry a `u²`-part. -/
def kdevA2At2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹ * PhiMainTruncAt2 τ z)
    + Work.Kernels.DeltaFun τ * (Work.Asymptotics.Compact.tailC⁻¹ * kdevDirTruncAt2 τ z)

/-- `ShDeltaZtr|₂ = 720·Δ(τ) - E₄(τ)³` (since `(E4Ztr)³|₂ = 3·240` and `DeltaZtr|₂ = 1`). -/
def ShDeltaZtrAt2 (τ z : ℍ) : ℂ :=
  720 * Work.Kernels.DeltaFun τ - (Work.Kernels.E4Fun τ) ^ 3

/-- `kdevNum0|₂` (product rule on both terms; `phitVec z 1|₂ = -24z²`,
`phitVec z 2|₂ = -48z(z-6i/π)`, `E₄(z)²|₂ = 480`, `E₄(z)E₆(z)|₂ = -264`). -/
def kdevNum0At2 (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ
      * (-48 * (z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
          + 480 * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2)
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
        * (-24 * (z : ℂ) ^ 2
            + 240 * ((z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)))
            - 504 * ((z : ℂ) * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))))

/-- `kdevSig2JFZtr|₂`: `Dev8RawJF|₂ = 0`, `DeltaZtr|₂ = 1`. -/
def kdevSig2At2 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * (Work.Kernels.DeltaFun τ * br8refJFAt2 ℓ τ z)
    - Work.Asymptotics.Compact.tailC⁻¹
        * (Work.Kernels.DeltaFun τ
            * (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2 * 1
              + Work.Kernels.DeltaFun τ * kdevNum0At2 τ z))

/-- **The `u²`-coefficient identity.**  The `u²`-coefficient of `WresPoly` vanishes:
`[WresPoly]_{u²} = kdevA2At0·ShDeltaZtr|₂ + (kdevA2At2 - 2·Δ(τ)KdevE2)·Δ(τ) + kdevSig2At2 = 0`
(product rule, `ShDeltaZtr|₀ = Δ(τ)`).  Together with the `O(u³)`-vanishing of the three
deviation aggregates this pins the residual to `O(u³)`.  The `τ`-atom identity behind it is the
proved `KhatE1.Kdev8BracketE2_eq_two_KdevE2` (the bracket's `E²`-coefficient is `2·KdevE2`),
which enters through the `Δ(τ)·KdevE2` slot. -/
theorem WresPolyAt2_eq_zero (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevA2At0 ℓ τ z * ShDeltaZtrAt2 τ z
      + (kdevA2At2 ℓ τ z
          - 2 * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
          * Work.Kernels.DeltaFun τ
      + kdevSig2At2 ℓ τ z = 0 := by
  have hbr : Work.Asymptotics.Compact.br0 8 ℓ τ z
      = 3456 * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z
        - 1728 * Work.Kernels.psi4 ℓ τ := by
    rw [Work.Asymptotics.Compact.br0, Work.Asymptotics.Compact.Gminus, if_pos rfl,
      Work.Asymptotics.Compact.Gminus8, Work.Asymptotics.Compact.Xc]
    field_simp
    ring
  rw [kdevA2At0, kdevA2At2, kdevSig2At2, kdevDirAt0, PhiMainTruncAt2, kdevDirTruncAt2,
    ShDeltaZtrAt2, kdevNum0At2, br8refJFAt2]
  rw [Delta_mul_KdevE2 ℓ τ z, hbr]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- High truncation of `E₈(z) = E₄(z)²` (`Kdev8WresHighTrunc`, conj. 1). -/
def E8refHi (z : ℍ) : ℂ :=
  1 + 480 * Work.Kernels.qParamFun z + 61920 * (Work.Kernels.qParamFun z) ^ 2

/-- High truncation of `E₁₀(z) = E₄(z)E₆(z)` (`Kdev8WresHighTrunc`, conj. 2). -/
def E10refHi (z : ℍ) : ℂ :=
  1 - 264 * Work.Kernels.qParamFun z - 135432 * (Work.Kernels.qParamFun z) ^ 2

/-- High truncation of `E₆(z)` (= `E6Ztr`). -/
def E6refHi (z : ℍ) : ℂ :=
  1 - 504 * Work.Kernels.qParamFun z - 16632 * (Work.Kernels.qParamFun z) ^ 2

/-- High truncation of `W(z) = θ₀₁⁴` (`Kdev8WresHighTrunc`, conj. 3). -/
def WrefHi (z : ℍ) : ℂ :=
  1 - 8 * Work.Residues.Ept z + 24 * Work.Kernels.qParamFun z
    - 32 * (Work.Residues.Ept z) ^ 3 + 24 * (Work.Kernels.qParamFun z) ^ 2
    - 48 * (Work.Residues.Ept z) ^ 5

/-- High truncation of `U(z)² - V(z)²` (`Kdev8WresHighTrunc`, conj. 4). -/
def D2refHi (z : ℍ) : ℂ :=
  1 + 16 * Work.Residues.Ept z - 144 * Work.Kernels.qParamFun z
    + 448 * (Work.Residues.Ept z) ^ 3 - 912 * (Work.Kernels.qParamFun z) ^ 2
    + 2016 * (Work.Residues.Ept z) ^ 5

/-- High truncation of `𝓛(z)` at its proved order `O(u⁵)` (from `cusp_L_fourth`). -/
def LrefHi (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  Work.Asymptotics.Compact.Xc ℓ z - 8 * Work.Residues.Ept z
    + 12 * Work.Kernels.qParamFun z
    - (32 / 3) * (Work.Residues.Ept z) ^ 3 + 6 * (Work.Kernels.qParamFun z) ^ 2

/-- The `Hi - ref` differences: what the high-truncation substitution introduces. -/
theorem E8refHi_sub_E8ref (z : ℍ) :
    E8refHi z - Work.Asymptotics.Compact.E8ref z
      = 61920 * (Work.Kernels.qParamFun z) ^ 2 := by
  rw [E8refHi, Work.Asymptotics.Compact.E8ref, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring

/-- `E10refHi - E10ref = -135432q²`. -/
theorem E10refHi_sub_E10ref (z : ℍ) :
    E10refHi z - Work.Asymptotics.Compact.E10ref z
      = -135432 * (Work.Kernels.qParamFun z) ^ 2 := by
  rw [E10refHi, Work.Asymptotics.Compact.E10ref, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring

/-- `E6refHi - E6ref = -16632q²`. -/
theorem E6refHi_sub_E6ref (z : ℍ) :
    E6refHi z - Work.Asymptotics.Compact.E6ref z
      = -16632 * (Work.Kernels.qParamFun z) ^ 2 := by
  rw [E6refHi, Work.Asymptotics.Compact.E6ref, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring

/-- `WrefHi - Wref = -32u³ + 24u⁴ - 48u⁵` (the `dW`-tail started at `u³`). -/
theorem WrefHi_sub_Wref (z : ℍ) :
    WrefHi z - Work.Asymptotics.Compact.Wref z
      = -32 * (Work.Residues.Ept z) ^ 3 + 24 * (Work.Kernels.qParamFun z) ^ 2
        - 48 * (Work.Residues.Ept z) ^ 5 := by
  rw [WrefHi, Work.Asymptotics.Compact.Wref, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring

/-- `D2refHi - D2ref = 448u³ - 912u⁴ + 2016u⁵`. -/
theorem D2refHi_sub_D2ref (z : ℍ) :
    D2refHi z - Work.Asymptotics.Compact.D2ref z
      = 448 * (Work.Residues.Ept z) ^ 3 - 912 * (Work.Kernels.qParamFun z) ^ 2
        + 2016 * (Work.Residues.Ept z) ^ 5 := by
  rw [D2refHi, Work.Asymptotics.Compact.D2ref, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring

/-- `LrefHi - Lref = -(32/3)u³ + 6u⁴`. -/
theorem LrefHi_sub_Lref (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) :
    LrefHi ℓ z - Work.Asymptotics.Compact.Lref ℓ z
      = -(32 / 3) * (Work.Residues.Ept z) ^ 3 + 6 * (Work.Kernels.qParamFun z) ^ 2 := by
  rw [LrefHi, Work.Asymptotics.Compact.Lref, Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]; ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `br8refJF` with `E10ref ↦ E10refHi` (first summand of the `WresPoly6` substitution). -/
def br8refJFE10Hi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * E10refHi z
            * Work.Asymptotics.Compact.Lref ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
              - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.E8ref z * Work.Asymptotics.Compact.Wref z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
              * Work.Asymptotics.Compact.D2ref z)

/-- **The `E10refHi` summand.**  `br8refJF` meets `E10ref` only through the single product
`E10ref z·Lref ℓ z`, so the substitution shifts it by
`Δ(τ)(-3456E₄(τ))·(E10ref - E10refHi)·Lref = Δ(τ)(-3456E₄(τ))·135432·q(z)²·Lref ℓ z`
(`E10refHi - E10ref = -135432q²`). -/
theorem br8refJF_E10refHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJF ℓ τ z
      = br8refJFE10Hi ℓ τ z
        + Work.Kernels.DeltaFun τ * (-3456 * Work.Kernels.E4Fun τ)
            * (135432 * (Work.Kernels.qParamFun z) ^ 2)
            * Work.Asymptotics.Compact.Lref ℓ z := by
  rw [br8refJF, br8refJFE10Hi, E10refHi, Work.Asymptotics.Compact.E10ref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `br8refJFE10Hi` with `E8ref ↦ E8refHi` (second summand; two occurrences). -/
def br8refJFE10HiE8Hi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * E10refHi z
            * Work.Asymptotics.Compact.Lref ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (E8refHi z * Work.Asymptotics.Compact.Wref z
              - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * Work.Asymptotics.Compact.Wref z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
              * Work.Asymptotics.Compact.D2ref z)

/-- **The `E8refHi` summand.**  `E8ref` occurs twice, both times multiplied by `Wref` (in the
`ψ₂E₁₄`-block and in the `(1728Δ - E₄³)`-part of the `ψ₄`-block), so the substitution shifts
`br8refJFE10Hi` by `-61920q(z)²·Wref·(ψ₂E₁₄ + ψ₄(1728Δ(τ) - E₄(τ)³))`
(`E8refHi - E8ref = 61920q²`). -/
theorem br8refJFE10Hi_E8refHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJFE10Hi ℓ τ z
      = br8refJFE10HiE8Hi ℓ τ z
        + (-61920 * (Work.Kernels.qParamFun z) ^ 2) * Work.Asymptotics.Compact.Wref z
            * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ
                + Work.Kernels.psi4 ℓ τ
                    * (1728 * Work.Kernels.DeltaFun τ - (Work.Kernels.E4Fun τ) ^ 3)) := by
  rw [br8refJFE10Hi, br8refJFE10HiE8Hi, E8refHi, Work.Asymptotics.Compact.E8ref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `br8refJFE10HiE8Hi` with `E6ref ↦ E6refHi` (third summand; two occurrences). -/
def br8refJFE10HiE8HiE6Hi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * E10refHi z
            * Work.Asymptotics.Compact.Lref ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (E8refHi z * Work.Asymptotics.Compact.Wref z
              - E6refHi z * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * Work.Asymptotics.Compact.Wref z
            + E4Fun τ ^ 3 * E6refHi z
              * Work.Asymptotics.Compact.D2ref z)

/-- **The `E6refHi` summand.**  Both `E6ref`-occurrences sit in `D2ref`-products (the
`ψ₂E₁₄`-block with a minus, the `ψ₄E₄(τ)³`-block with a plus), so the coefficient is
`D2ref z·(-ψ₂ ℓ τ·E₁₄(τ) + ψ₄ ℓ τ·E₄(τ)³)` and, with `E6refHi - E6ref = -16632q²`,
```
E6ref = E6refHi + 16632q²
```
so the substitution shifts the body by `+16632q(z)²·D2ref z·(-ψ₂E₁₄ + ψ₄E₄(τ)³)`. -/
theorem br8refJFE10HiE8Hi_E6refHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJFE10HiE8Hi ℓ τ z
      = br8refJFE10HiE8HiE6Hi ℓ τ z
        + (16632 * (Work.Kernels.qParamFun z) ^ 2) * Work.Asymptotics.Compact.D2ref z
            * (-(Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ)
                + Work.Kernels.psi4 ℓ τ * (Work.Kernels.E4Fun τ) ^ 3) := by
  rw [br8refJFE10HiE8Hi, br8refJFE10HiE8HiE6Hi, E6refHi, Work.Asymptotics.Compact.E6ref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `br8refJFE10HiE8HiE6Hi` with `Wref ↦ WrefHi` (fourth summand; two occurrences). -/
def br8refJFE10HiE8HiE6HiWHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * E10refHi z
            * Work.Asymptotics.Compact.Lref ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (E8refHi z * WrefHi z
              - E6refHi z * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * WrefHi z
            + E4Fun τ ^ 3 * E6refHi z
              * Work.Asymptotics.Compact.D2ref z)

/-- **The `WrefHi` summand.**  Both `Wref`-occurrences sit in `E8refHi`-products (the
`ψ₂E₁₄`-block and the `(1728Δ - E₄³)`-part of the `ψ₄`-block), so the coefficient is
`E8refHi z·(ψ₂ ℓ τ·E₁₄(τ) + ψ₄ ℓ τ·(1728Δ(τ) - E₄(τ)³))`.  With
`WrefHi - Wref = -32u³ + 24q² - 48u⁵` (i.e. `Wref = WrefHi + 32u³ - 24q² + 48u⁵`), the shift is
`(32u³ - 24q(z)² + 48u⁵)·E8refHi z·(ψ₂E₁₄ + ψ₄(1728Δ - E₄(τ)³))`. -/
theorem br8refJFE10HiE8HiE6Hi_WrefHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJFE10HiE8HiE6Hi ℓ τ z
      = br8refJFE10HiE8HiE6HiWHi ℓ τ z
        + (32 * (Work.Residues.Ept z) ^ 3
            - 24 * (Work.Kernels.qParamFun z) ^ 2
            + 48 * (Work.Residues.Ept z) ^ 5) * E8refHi z
            * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ
                + Work.Kernels.psi4 ℓ τ
                    * (1728 * Work.Kernels.DeltaFun τ - (Work.Kernels.E4Fun τ) ^ 3)) := by
  rw [br8refJFE10HiE8HiE6Hi, br8refJFE10HiE8HiE6HiWHi, WrefHi, Work.Asymptotics.Compact.Wref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `br8refJFE10HiE8HiE6HiWHi` with `D2ref ↦ D2refHi` (fifth summand; two occurrences). -/
def br8refJFAllHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * E10refHi z
            * Work.Asymptotics.Compact.Lref ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (E8refHi z * WrefHi z
              - E6refHi z * D2refHi z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * WrefHi z
            + E4Fun τ ^ 3 * E6refHi z
              * D2refHi z)

/-- **The `D2refHi` summand.**  Both `D2ref`-occurrences sit in `E6refHi`-products (the
`ψ₂E₁₄`-block with a minus, the `ψ₄E₄(τ)³`-block with a plus), so the coefficient is
`E6refHi z·(ψ₄ ℓ τ·E₄(τ)³ - ψ₂ ℓ τ·E₁₄(τ))`.  With
`D2refHi - D2ref = 448u³ - 912q² + 2016u⁵` (i.e. `D2ref = D2refHi - 448u³ + 912q² - 2016u⁵`),
the shift is `(-448u³ + 912q(z)² - 2016u⁵)·E6refHi z·(ψ₄E₄(τ)³ - ψ₂E₁₄(τ))`. -/
theorem br8refJFE10HiE8HiE6HiWHi_D2refHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJFE10HiE8HiE6HiWHi ℓ τ z
      = br8refJFAllHi ℓ τ z
        + (-448 * (Work.Residues.Ept z) ^ 3
            + 912 * (Work.Kernels.qParamFun z) ^ 2
            - 2016 * (Work.Residues.Ept z) ^ 5) * E6refHi z
            * (Work.Kernels.psi4 ℓ τ * (Work.Kernels.E4Fun τ) ^ 3
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ) := by
  rw [br8refJFE10HiE8HiE6HiWHi, br8refJFAllHi, D2refHi, Work.Asymptotics.Compact.D2ref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `br8refJFAllHi` with `Lref ↦ LrefHi` (sixth and last summand: `br8refJF` with *all six*
`*ref ↦ *Hi` replacements applied). -/
def br8refJFHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (-3456 * E4Fun τ * E10refHi z
            * LrefHi ℓ z)
        + psi2 ℓ τ * E14Fun τ
            * (E8refHi z * WrefHi z
              - E6refHi z * D2refHi z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * WrefHi z
            + E4Fun τ ^ 3 * E6refHi z
              * D2refHi z)

/-- **The `LrefHi` summand.**  `Lref` occurs once, in the `Δ(τ)(-3456E₄(τ))·E10refHi·Lref` term,
so the coefficient is `Δ(τ)(-3456E₄(τ))·E10refHi z`.  With
`LrefHi - Lref = -(32/3)u³ + 6q²` (i.e. `Lref = LrefHi + (32/3)u³ - 6q²`), the shift is
`((32/3)u³ - 6q(z)²)·Δ(τ)(-3456E₄(τ))·E10refHi z`. -/
theorem br8refJFAllHi_LrefHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    br8refJFAllHi ℓ τ z
      = br8refJFHi ℓ τ z
        + ((32 / 3) * (Work.Residues.Ept z) ^ 3
            - 6 * (Work.Kernels.qParamFun z) ^ 2)
            * (Work.Kernels.DeltaFun τ * (-3456 * Work.Kernels.E4Fun τ) * E10refHi z) := by
  rw [br8refJFAllHi, br8refJFHi, LrefHi, Work.Asymptotics.Compact.Lref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `Dev8RawJF` with `E8ref ↦ E8refHi` (first summand of the `Dev8RawJF` leg). -/
def Dev8RawJFE8Hi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (Work.Asymptotics.Compact.DevA1 ℓ τ z
            + Work.Asymptotics.Compact.DevA2 ℓ τ z
            + Work.Asymptotics.Compact.DevA3 ℓ τ z)
        + psi2 ℓ τ * E14Fun τ
            * ((E8refHi z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.dD2 z)
              + (Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.Wref z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.D2ref z)
              + (Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.dD2 z))
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
              * Work.Asymptotics.Compact.dD2 z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.Wref z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.dD2 z)

/-- **The `Dev8RawJF` `E8refHi` summand.**  Both `E8ref`-occurrences are multiplied by `dW`, so
the coefficient is `dW z·(ψ₂ ℓ τ·E₁₄(τ) + ψ₄ ℓ τ·(1728Δ(τ) - E₄(τ)³))` and, with
`E8ref = E8refHi - 61920q²`, the shift is `-61920q(z)²·dW z·(ψ₂E₁₄ + ψ₄(1728Δ - E₄³))`. -/
theorem Dev8RawJF_E8refHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Dev8RawJF ℓ τ z
      = Dev8RawJFE8Hi ℓ τ z
        + (-61920 * (Work.Kernels.qParamFun z) ^ 2) * Work.Asymptotics.Compact.dW z
            * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ
                + Work.Kernels.psi4 ℓ τ
                    * (1728 * Work.Kernels.DeltaFun τ - (Work.Kernels.E4Fun τ) ^ 3)) := by
  rw [Dev8RawJF, Dev8RawJFE8Hi, E8refHi, Work.Asymptotics.Compact.E8ref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `Dev8RawJFE8Hi` with `Wref ↦ WrefHi` (second summand of the `Dev8RawJF` leg). -/
def Dev8RawJFE8HiWHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (Work.Asymptotics.Compact.DevA1 ℓ τ z
            + Work.Asymptotics.Compact.DevA2 ℓ τ z
            + Work.Asymptotics.Compact.DevA3 ℓ τ z)
        + psi2 ℓ τ * E14Fun τ
            * ((E8refHi z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.E6ref z * Work.Asymptotics.Compact.dD2 z)
              + (Work.Asymptotics.Compact.dE8 z * WrefHi z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.D2ref z)
              + (Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.dD2 z))
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.E6ref z
              * Work.Asymptotics.Compact.dD2 z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * WrefHi z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.dD2 z)

/-- **The `Dev8RawJF` `WrefHi` summand.**  Both `Wref`-occurrences are multiplied by `dE₈`, so
the coefficient is `dE₈ z·(ψ₂ ℓ τ·E₁₄(τ) + ψ₄ ℓ τ·(1728Δ(τ) - E₄(τ)³))` and, with
`Wref = WrefHi + 32u³ - 24q² + 48u⁵`, the shift is
`(32u³ - 24q(z)² + 48u⁵)·dE₈ z·(ψ₂E₁₄ + ψ₄(1728Δ - E₄(τ)³))`. -/
theorem Dev8RawJFE8Hi_WrefHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Dev8RawJFE8Hi ℓ τ z
      = Dev8RawJFE8HiWHi ℓ τ z
        + (32 * (Work.Residues.Ept z) ^ 3
            - 24 * (Work.Kernels.qParamFun z) ^ 2
            + 48 * (Work.Residues.Ept z) ^ 5) * Work.Asymptotics.Compact.dE8 z
            * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ
                + Work.Kernels.psi4 ℓ τ
                    * (1728 * Work.Kernels.DeltaFun τ - (Work.Kernels.E4Fun τ) ^ 3)) := by
  rw [Dev8RawJFE8Hi, Dev8RawJFE8HiWHi, WrefHi, Work.Asymptotics.Compact.Wref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `Dev8RawJFE8HiWHi` with `E6ref ↦ E6refHi` (third summand of the `Dev8RawJF` leg). -/
def Dev8RawJFE8HiWHiE6Hi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (Work.Asymptotics.Compact.DevA1 ℓ τ z
            + Work.Asymptotics.Compact.DevA2 ℓ τ z
            + Work.Asymptotics.Compact.DevA3 ℓ τ z)
        + psi2 ℓ τ * E14Fun τ
            * ((E8refHi z * Work.Asymptotics.Compact.dW z
                  - E6refHi z * Work.Asymptotics.Compact.dD2 z)
              + (Work.Asymptotics.Compact.dE8 z * WrefHi z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.D2ref z)
              + (Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.dD2 z))
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * E6refHi z
              * Work.Asymptotics.Compact.dD2 z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * WrefHi z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.D2ref z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.dD2 z)

/-- **The `Dev8RawJF` `E6refHi` summand.**  Both `E6ref`-occurrences are multiplied by `dD2` (the
`ψ₂E₁₄`-block with a minus, the `ψ₄E₄(τ)³`-block with a plus), so the coefficient is
`dD2 z·(-ψ₂ ℓ τ·E₁₄(τ) + ψ₄ ℓ τ·E₄(τ)³)` and, with `E6ref = E6refHi + 16632q²`, the shift is
`+16632q(z)²·dD2 z·(-ψ₂E₁₄ + ψ₄E₄(τ)³)` — the same shape as the `br8refJF`-leg `E6refHi` step
with `D2ref ↦ dD2`. -/
theorem Dev8RawJFE8HiWHi_E6refHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Dev8RawJFE8HiWHi ℓ τ z
      = Dev8RawJFE8HiWHiE6Hi ℓ τ z
        + (16632 * (Work.Kernels.qParamFun z) ^ 2) * Work.Asymptotics.Compact.dD2 z
            * (-(Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ)
                + Work.Kernels.psi4 ℓ τ * (Work.Kernels.E4Fun τ) ^ 3) := by
  rw [Dev8RawJFE8HiWHi, Dev8RawJFE8HiWHiE6Hi, E6refHi, Work.Asymptotics.Compact.E6ref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `Dev8RawJF` with **all four** literal atoms replaced by their high truncations
(`E8refHi`, `WrefHi`, `E6refHi`, `D2refHi`). -/
def Dev8RawJFHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  DeltaFun τ * (Work.Asymptotics.Compact.DevA1 ℓ τ z
            + Work.Asymptotics.Compact.DevA2 ℓ τ z
            + Work.Asymptotics.Compact.DevA3 ℓ τ z)
        + psi2 ℓ τ * E14Fun τ
            * ((E8refHi z * Work.Asymptotics.Compact.dW z
                  - E6refHi z * Work.Asymptotics.Compact.dD2 z)
              + (Work.Asymptotics.Compact.dE8 z * WrefHi z
                  - Work.Asymptotics.Compact.dE6 z * D2refHi z)
              + (Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
                  - Work.Asymptotics.Compact.dE6 z * Work.Asymptotics.Compact.dD2 z))
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * E8refHi z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * E6refHi z
              * Work.Asymptotics.Compact.dD2 z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * WrefHi z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * D2refHi z)
        + psi4 ℓ τ * ((1728 * DeltaFun τ - E4Fun τ ^ 3)
              * Work.Asymptotics.Compact.dE8 z * Work.Asymptotics.Compact.dW z
            + E4Fun τ ^ 3 * Work.Asymptotics.Compact.dE6 z
              * Work.Asymptotics.Compact.dD2 z)

/-- **The `Dev8RawJF` `D2refHi` summand** (last literal atom of that leg).  Both
`D2ref`-occurrences are multiplied by `dE₆` (the `ψ₂E₁₄`-block with a minus, the `ψ₄E₄(τ)³`-block
with a plus), so the coefficient is `dE₆ z·(-ψ₂ ℓ τ·E₁₄(τ) + ψ₄ ℓ τ·E₄(τ)³)` and, with
`D2ref = D2refHi - 448u³ + 912q² - 2016u⁵`, the shift is
`(-448u³ + 912q(z)² - 2016u⁵)·dE₆ z·(ψ₄E₄(τ)³ - ψ₂E₁₄(τ))` — the direct analogue of the
`br8refJF`-leg `D2refHi` step with `E6ref ↦ dE6`. -/
theorem Dev8RawJFE8HiWHiE6Hi_D2refHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Dev8RawJFE8HiWHiE6Hi ℓ τ z
      = Dev8RawJFHi ℓ τ z
        + (-448 * (Work.Residues.Ept z) ^ 3
            + 912 * (Work.Kernels.qParamFun z) ^ 2
            - 2016 * (Work.Residues.Ept z) ^ 5) * Work.Asymptotics.Compact.dE6 z
            * (Work.Kernels.psi4 ℓ τ * (Work.Kernels.E4Fun τ) ^ 3
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ) := by
  rw [Dev8RawJFE8HiWHiE6Hi, Dev8RawJFHi, D2refHi, Work.Asymptotics.Compact.D2ref,
    Work.Asymptotics.Small.qParamFun_eq_Ept_sq z]
  ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `kdevSig2JFZtr` with `br8refJF ↦ br8refJFHi` and `Dev8RawJF ↦ Dev8RawJFHi`. -/
def kdevSig2JFZtrHi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
      (Work.Kernels.DeltaFun τ * br8refJFHi ℓ τ z
        + Work.Kernels.DeltaFun τ * Dev8RawJFHi ℓ τ z)
    - Work.Asymptotics.Compact.tailC⁻¹ *
        (Work.Kernels.DeltaFun τ *
          (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              * DeltaZtr z
            + Work.Kernels.DeltaFun τ * kdevNum0 τ z))

/-- **The polynomial part with the high truncations**: `WresPoly` with both substitution chains
applied (hence a *finite* polynomial in `u = Ept z` after `qParamFun z = (Ept z)²`, together with
`kdevNum0_split`). -/
def WresPoly6 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  (kdevA2JFZtr ℓ τ z
      - 2 * (Work.Residues.Ept z) ^ 2 * (Work.Kernels.DeltaFun τ * KdevE2 ℓ τ z))
    * ShDeltaZtr τ z
  + kdevSig2JFZtrHi ℓ τ z

/-- **The `kdevSig2JFZtr` substitution identity** (only the two chain heads change). -/
theorem kdevSig2JFZtr_eq_Hi (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevSig2JFZtr ℓ τ z
      = kdevSig2JFZtrHi ℓ τ z
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Kernels.DeltaFun τ
            * ((br8refJF ℓ τ z - br8refJFHi ℓ τ z)
                + (Dev8RawJF ℓ τ z - Dev8RawJFHi ℓ τ z)) := by
  rw [kdevSig2JFZtr, kdevSig2JFZtrHi]
  ring

/-- **The assembly.**  `WresPoly = WresPoly6 + (3456π)⁻¹Δ(τ)·(chain differences)`; the ten
`*ref ↦ *Hi` difference lemmas substitute into the two bracketed differences, which is the form
in which the tail's `P` is read off. -/
theorem WresPoly_eq_WresPoly6 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    WresPoly ℓ τ z
      = WresPoly6 ℓ τ z
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Kernels.DeltaFun τ
            * ((br8refJF ℓ τ z - br8refJFHi ℓ τ z)
                + (Dev8RawJF ℓ τ z - Dev8RawJFHi ℓ τ z)) := by
  rw [WresPoly, WresPoly6, kdevSig2JFZtr_eq_Hi]
  ring

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `ShDeltaZtr` in `u = Ept z` form: `Δ(τ)(1+240u²+2160u⁴)³ - (u²-24u⁴+252u⁶)E₄(τ)³`. -/
theorem ShDeltaZtr_eq_Ept (τ z : ℍ) :
    ShDeltaZtr τ z
      = Work.Kernels.DeltaFun τ
          * (1 + 240 * (Work.Residues.Ept z) ^ 2 + 2160 * (Work.Residues.Ept z) ^ 4) ^ 3
        - ((Work.Residues.Ept z) ^ 2 - 24 * (Work.Residues.Ept z) ^ 4
            + 252 * (Work.Residues.Ept z) ^ 6) * (Work.Kernels.E4Fun τ) ^ 3 := by
  rw [ShDeltaZtr, E4Ztr_eq_Ept z, DeltaZtr_eq_Ept z]

/-- `phit1Ztr z = z·GtTr z` in `u`-form. -/
theorem phit1Ztr_eq_Ept (z : ℍ) :
    phit1Ztr z
      = (z : ℂ) * ((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
            - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ)) := by
  rw [phit1Ztr, GtTr_eq_Ept z]

/-- `phit2Ztr z = (GtTr z)²` in `u`-form. -/
theorem phit2Ztr_eq_Ept (z : ℍ) :
    phit2Ztr z
      = ((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
            - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2 := by
  rw [phit2Ztr, GtTr_eq_Ept z]

/-- `kdevDirTrunc` in `u`-form (`phitVec z 1 = z·GtTr`, `phitVec z 2 = GtTr²`). -/
theorem kdevDirTrunc_eq_Ept (τ z : ℍ) :
    kdevDirTrunc τ z
      = (τ : ℂ) * Work.Kernels.E6Fun τ
          * ((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
                - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
        - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            * ((z : ℂ) * ((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
                - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ))) := by
  rw [kdevDirTrunc, phit1Ztr_eq_Ept z, phit2Ztr_eq_Ept z]

end

end Work.Asymptotics.KhatE1

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `PhiMainTrunc` in `u = Ept z` form (the `E₂(z) - 1` factor becomes `-24u² - 72u⁴`). -/
theorem PhiMainTrunc_eq_Ept (τ z : ℍ) :
    PhiMainTrunc τ z
      = (-24 * (Work.Residues.Ept z) ^ 2 - 72 * (Work.Residues.Ept z) ^ 4)
          * ((τ : ℂ) * Work.Kernels.E6Fun τ
              * (-((z : ℂ) ^ 2
                    * (1 + (1 - 24 * (Work.Residues.Ept z) ^ 2
                        - 72 * (Work.Residues.Ept z) ^ 4)))
                  + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
            + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2) := by
  rw [PhiMainTrunc, E2Ztr_eq_Ept z]
  try ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `PhiMainTrunc` in `u`-form, as a named object. -/
def PhiMainTruncUEpt (τ z : ℍ) : ℂ :=
  (-24 * (Work.Residues.Ept z) ^ 2 - 72 * (Work.Residues.Ept z) ^ 4)
          * ((τ : ℂ) * Work.Kernels.E6Fun τ
              * (-((z : ℂ) ^ 2
                    * (1 + (1 - 24 * (Work.Residues.Ept z) ^ 2
                        - 72 * (Work.Residues.Ept z) ^ 4)))
                  + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
            + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ) ^ 2)

/-- `kdevDirTrunc` in `u`-form, as a named object. -/
def kdevDirTruncUEpt (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ
          * ((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
                - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2
        - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
            * ((z : ℂ) * ((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
                - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ)))

/-- Repackaging of `PhiMainTrunc_eq_Ept`. -/
theorem PhiMainTrunc_eq_UEpt (τ z : ℍ) : PhiMainTrunc τ z = PhiMainTruncUEpt τ z :=
  PhiMainTrunc_eq_Ept τ z

/-- Repackaging of `kdevDirTrunc_eq_Ept`. -/
theorem kdevDirTrunc_eq_UEpt (τ z : ℍ) : kdevDirTrunc τ z = kdevDirTruncUEpt τ z :=
  kdevDirTrunc_eq_Ept τ z

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `kdevSig2JFZtrHi` with the `DeltaZtr z` slot in `u`-form (slot 1 of §39). -/
def kdevSig2JFZtrHiDeltaU (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
      (Work.Kernels.DeltaFun τ * br8refJFHi ℓ τ z
        + Work.Kernels.DeltaFun τ * Dev8RawJFHi ℓ τ z)
    - Work.Asymptotics.Compact.tailC⁻¹ *
        (Work.Kernels.DeltaFun τ *
          (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              * ((Work.Residues.Ept z)^2 - 24*(Work.Residues.Ept z)^4 + 252*(Work.Residues.Ept z)^6)
            + Work.Kernels.DeltaFun τ * kdevNum0 τ z))

/-- **Slot 1 of §39**: the `DeltaZtr` slot of `kdevSig2JFZtrHi` in `u`-form. -/
theorem kdevSig2JFZtrHi_deltaU (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevSig2JFZtrHi ℓ τ z = kdevSig2JFZtrHiDeltaU ℓ τ z := by
  rw [kdevSig2JFZtrHi, kdevSig2JFZtrHiDeltaU, DeltaZtr_eq_Ept z]
  try ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `kdevNum0Ztr` in `u`-form (slot 2 of §39): the four truncated atoms substituted. -/
def kdevNum0ZtrUEpt (τ z : ℍ) : ℂ :=
  (τ : ℂ) * Work.Kernels.E6Fun τ * (((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
            - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2) * ((1 + 240 * (Work.Residues.Ept z) ^ 2 + 2160 * (Work.Residues.Ept z) ^ 4)) ^ 2
    - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * ((z : ℂ) * ((z : ℂ) * (1 - 24 * (Work.Residues.Ept z) ^ 2
            - 72 * (Work.Residues.Ept z) ^ 4) - 6 * Complex.I / (Real.pi : ℂ))) * (1 + 240 * (Work.Residues.Ept z) ^ 2 + 2160 * (Work.Residues.Ept z) ^ 4) * (1 - 504 * (Work.Residues.Ept z) ^ 2 - 16632 * (Work.Residues.Ept z) ^ 4)

/-- **Slot 2 of §39, first half**: the `u`-form of `kdevNum0Ztr`. -/
theorem kdevNum0Ztr_eq_UEpt (τ z : ℍ) : kdevNum0Ztr τ z = kdevNum0ZtrUEpt τ z := by
  rw [kdevNum0Ztr, kdevNum0ZtrUEpt, phit1Ztr_eq_Ept z, phit2Ztr_eq_Ept z,
    E4Ztr_eq_Ept z, E6Ztr_eq_Ept z]
  try ring

end

end Work.Asymptotics.KhatE1


namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- `kdevSig2JFZtrHiDeltaU` with the `kdevNum0` slot split (`kdevNum0_split`) and its truncated
part in `u`-form (`kdevNum0Ztr_eq_UEpt`) — the last `u`-hazard of step (1). -/
def kdevSig2JFZtrHiUEpt (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) : ℂ :=
  ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
      (Work.Kernels.DeltaFun τ * br8refJFHi ℓ τ z
        + Work.Kernels.DeltaFun τ * Dev8RawJFHi ℓ τ z)
    - Work.Asymptotics.Compact.tailC⁻¹ *
        (Work.Kernels.DeltaFun τ *
          (Work.Kernels.phi2 τ * Work.Kernels.E14Fun τ * (z : ℂ) ^ 2
              * ((Work.Residues.Ept z)^2 - 24*(Work.Residues.Ept z)^4 + 252*(Work.Residues.Ept z)^6)
            + Work.Kernels.DeltaFun τ * (kdevNum0ZtrUEpt τ z
        + ((τ : ℂ) * Work.Kernels.E6Fun τ
              * (Work.Kernels.phitVec z 2 * (Work.Kernels.E4Fun z) ^ 2
                  - phit2Ztr z * (E4Ztr z) ^ 2)
            - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ
              * (Work.Kernels.phitVec z 1 * Work.Kernels.E4Fun z * Work.Kernels.E6Fun z
                  - phit1Ztr z * E4Ztr z * E6Ztr z)))))

/-- **Step (2) of §41**: the `kdevNum0` slot split and `u`-formed. -/
theorem kdevSig2JFZtrHiDeltaU_eq_UEpt (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    kdevSig2JFZtrHiDeltaU ℓ τ z = kdevSig2JFZtrHiUEpt ℓ τ z := by
  rw [kdevSig2JFZtrHiDeltaU, kdevSig2JFZtrHiUEpt, kdevNum0_split τ z,
    kdevNum0Ztr_eq_UEpt τ z]
  try ring

end

end Work.Asymptotics.KhatE1
