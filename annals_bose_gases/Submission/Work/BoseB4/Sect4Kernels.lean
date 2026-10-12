import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB4.BoxChi
import Submission.Work.BoseB4.Q3Defs
import Submission.Work.BoseB7.Q3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Sect4Kernels` — FS §4's Fourier transforms on the mode lattice

This module **pins once** the passage from FS §4's *continuous* kernels to the
*mode-indexed* kernels of the bundles `Work.BoseB4.H2ndData`,
`Work.BoseB4.Q3Data` and `Work.BoseB7.Q3Env`, in the measure convention recorded
in the header of `Work.BoseB4.H2nd`:

    `(2π)⁻³ℓ³ ∫ dk  =  Σ_{k}`   (one Brillouin zone = one cell of `(2π/ℓ)ℤ³`),

so that a continuous kernel `F` is evaluated at the mode's momentum,

    `F_mode k := F(kmom k)`,

and FS's `χ̂_Λ`-rows — which carry no `k`-integral — are the *normalised*
transform `χ̂(ℓk)` (because `χ̂_Λ(k) = ℓ³χ̂(ℓk)` and the row's
`(2π)⁻³∫χ̂_Λ(k)a_k†a_0 dk = ℓ⁻³Σ_k χ̂_Λ(k)a_k†a_0 = Σ_k χ̂(ℓk)a_k†a_0`).

The definitions of the continuous kernels are FS's:

* `tauFun` — `def:tau`,
  `τ(k) = (1−ε_T)[|k| − 1/(2sℓ)]₊² + ε_T[|k| − 1/(2dsℓ)]₊²`;
* `fLFun` — FS l. 1464, `f_L(s) = f(s/(K_L√(μa)))`, the low-momentum localisation
  (`f` a fixed cutoff profile);
* `chiHatMode`, `chiHatSqMode` — `χ̂_Λ` and `χ̂_Λ²` on the modes, from
  `Work.BoseB4.BoxData.hatChi`/`hatChiSq`;
* the potentials `Ŵ₁`, `Ŵ₁ω` and `ĝ`, `ĝω` are supplied by the scattering side of
  the corpus as functions `ℝ³ → ℝ`; only their mode values are used.

The two `ofSect4` constructors turn an instance of that data plus a mode family
`kmom : Mode → ℝ³` into the bundles the dictionary consumes.  The structural
lemma `ccrKernel_hatChiMode` records that the resulting mode-indexed `χ̂`, `χ̂²`
reproduce FS `eq:Commutator_general`'s kernel `Work.BoseB7.ccrKernel`, i.e. that
the convention is consistent with `Work.BoseB4.BoxKernel.realIP_qVec_qVec`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The continuous §4 kernels -/

/-- FS `def:tau`: the kinetic symbol
`τ(k) = (1−ε_T)[|k| − (2sℓ)⁻¹]₊² + ε_T[|k| − (2dsℓ)⁻¹]₊²`. -/
noncomputable def tauFun (eT s d ell : ℝ) (k : ℝ³) : ℝ :=
  (1 - eT) * (max (‖k‖ - (2 * s * ell)⁻¹) 0) ^ 2
    + eT * (max (‖k‖ - (2 * d * s * ell)⁻¹) 0) ^ 2

/-- FS's low-momentum localisation `f_L(s) = f(s/(K_L√(μa)))` (l. 1464): the
profile `f : ℝ → ℝ` rescaled to the momentum scale `K_L√(μa)`, evaluated
radially. -/
noncomputable def fLFun (f : ℝ → ℝ) (KL mu a : ℝ) (s : ℝ³) : ℝ :=
  f (‖s‖ / (KL * Real.sqrt (mu * a)))

/-! ## The mode-indexed kernels -/

/-- The mode-indexed kernel of a continuous §4 kernel: `F_mode k = F(kmom k)`
(the whole lattice weight `(2π)⁻³ℓ³` is already inside `F`, cf. the header of
`Work.BoseB4.H2nd`). -/
noncomputable def modeKernel {Mode : Type*} (F : ℝ³ → ℝ) (kmom : Mode → ℝ³) : Mode → ℝ :=
  fun k => F (kmom k)

/-- The mode-indexed `χ̂_Λ`: FS's `(2π)⁻³∫χ̂_Λ(k)a_k†a_0 dk = Σ_k χ̂(ℓk)a_k†a_0`
uses the **normalised** transform `χ̂(ℓk)` (`χ̂_Λ(k) = ℓ³χ̂(ℓk)`). -/
noncomputable def chiHatMode (B : BoxData) {Mode : Type*}
    (ell : ℝ) (kmom : Mode → ℝ³) : Mode → ℝ :=
  fun k => B.hatChi (ell • kmom k)

/-- The mode-indexed `χ̂²_Λ` (`= ℓ³χ̂²(ℓk)`), i.e. FS's `χ̂²(ℓk)`. -/
noncomputable def chiHatSqMode (B : BoxData) {Mode : Type*}
    (ell : ℝ) (kmom : Mode → ℝ³) : Mode → ℝ :=
  fun k => B.hatChiSq (ell • kmom k)

/-! ## The bundles -/

/-- **`H2ndData` from FS §4.**  All continuous kernels are evaluated at the mode
momenta, `χ̂_Λ` through the normalised `χ̂(ℓk)`; `Ŵ₁(0)`, `Ŵ₁ω(0)`, `ĝ(0)`,
`ĝω(0)` are the values at the origin of the corresponding transforms (the
rows `Hchi`, `HchiOm`, `Hnn`, `Hcontact`, `Hmu` carry them as scalars). -/
noncomputable def H2ndData.ofSect4 {m : ℕ} [NeZero m] (kmom : Fin m → ℝ³)
    (ell mu b eT d : ℝ) (g0 gomega0 W10 W1omega0 : ℝ)
    (W1fun W1omegafun tauF : ℝ³ → ℝ) (B : BoxData) (PHset : Finset (Fin m)) :
    H2ndData m where
  ell := ell
  mu := mu
  b := b
  eT := eT
  d := d
  g0 := g0
  gomega0 := gomega0
  W10 := W10
  W1omega0 := W1omega0
  tau := modeKernel tauF kmom
  W1 := modeKernel W1fun kmom
  W1omega := modeKernel W1omegafun kmom
  chiHat := chiHatMode B ell kmom
  PHset := PHset

/-- **`Q3Data` from FS §4** (`eq:3Qtilde`'s row): the `Ŵ₁` and `f_L` kernels
evaluated on the modes, and the coordinates of the localised modes `ã_s`
(orthogonal to the condensate, hence combinations of excited modes only). -/
noncomputable def Q3Data.ofSect4 {m : ℕ} [NeZero m] (kmom : Fin m → ℝ³)
    (ell : ℝ) (W1fun : ℝ³ → ℝ) (fLfun' : ℝ³ → ℝ) (phi : Fin m → Excited m → ℝ)
    (PHset : Finset (Fin m)) : Q3Data m where
  ell := ell
  W1 := modeKernel W1fun kmom
  fL := modeKernel fLfun' kmom
  phi := phi
  PHset := PHset

/-- **`Q3Env` from FS §4** (§10's scalar data): every kernel evaluated on the
modes, `𝒜 = τ + ρ_zŴ₁`, `ℬ = ρ_zŴ₁` as FS's `eq:DefA`, `eq:DefB` require of the
`Q3Env` fields `A`, `B`. -/
noncomputable def Q3Env.ofSect4 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (kmom : Mode → ℝ³) (z ell mu aScat KH Kl KL d s eT b : ℝ) (intM : ℕ)
    (bigM delta : ℝ) (fLf W1f W1omegaf tauF : ℝ³ → ℝ) (W1omega0 : ℝ) (B : BoxData) :
    Work.BoseB7.Q3Env Mode where
  z := z
  ell := ell
  mu := mu
  aScat := aScat
  KH := KH
  Kl := Kl
  KL := KL
  d := d
  s := s
  eT := eT
  b := b
  intM := intM
  bigM := bigM
  delta := delta
  fL := modeKernel fLf kmom
  W1 := modeKernel W1f kmom
  W1omega := modeKernel W1omegaf kmom
  W1omega0 := W1omega0
  hatChi := chiHatMode B ell kmom
  hatChiSq := chiHatSqMode B ell kmom
  tau := modeKernel tauF kmom
  A := fun k => tauF (kmom k) + (z ^ 2 / ell ^ 3) * W1f (kmom k)
  B := fun k => (z ^ 2 / ell ^ 3) * W1f (kmom k)

/-! ## Consistency with FS `eq:Commutator_general` -/

theorem ccrKernel_eq_boxKernel (B : BoxData) (ell : ℝ) (k k' : ℝ³) :
    Work.BoseB7.ccrKernel ell B.hatChiSq B.hatChi k k' = B.boxKernel ell k k' := rfl

/-- **The measure convention is consistent**: the *mode-indexed* data
`chiHatMode`, `chiHatSqMode` (which is what the bundles `H2ndData`, `Q3Data`,
`Q3Env` carry, and what `Work.BoseB7.ccrKernel` reads off a mode family) satisfies
FS `eq:Commutator_general` as soon as the momentum assignment is additive on
differences — and the value is the box kernel of the concrete `L²(Λ)` computation
proved in `Work.BoseB4.BoxKernel.realIP_qVec_qVec` (divided by `ℓ³`). -/
theorem ccrKernel_hatChiMode {Mode : Type*} [AddCommGroup Mode] (B : BoxData)
    (ell : ℝ) (kmom : Mode → ℝ³) (had : ∀ i j : Mode, kmom (i - j) = kmom i - kmom j)
    (i j : Mode) :
    chiHatSqMode (Mode := Mode) B ell kmom (i - j)
        - chiHatMode (Mode := Mode) B ell kmom i * chiHatMode (Mode := Mode) B ell kmom j
      = B.boxKernel ell (kmom i) (kmom j) := by
  have h1 : chiHatSqMode (Mode := Mode) B ell kmom (i - j)
      = B.hatChiSq (ell • (kmom i - kmom j)) := by
    simp only [chiHatSqMode, had i j]
  have h2 : chiHatMode (Mode := Mode) B ell kmom i = B.hatChi (ell • kmom i) := rfl
  have h3 : chiHatMode (Mode := Mode) B ell kmom j = B.hatChi (ell • kmom j) := rfl
  rw [h1, h2, h3, BoxData.boxKernel]


end Work.BoseB4
