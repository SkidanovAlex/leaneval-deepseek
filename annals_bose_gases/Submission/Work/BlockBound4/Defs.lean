import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.KinPSuperadd.Superadd
import Submission.Work.KinPSuperadd.fubini_abox_two
import Submission.Work.KinPSuperadd.integral_abox_one_slot
import Submission.Work.KinPSuperadd.kinPWord_le_diagWord
import Submission.Work.KinPSuperadd.modePGen_block_deficiency
import Submission.Work.KinPSuperadd.slotSplit_pModeDiagonal
import Submission.Work.SmallBoxBlockBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BlockBound4` — DOOR 4: the FS-faithful block bound at the faithful word

## Why this chapter exists

`Submission.Work.KinPSuperadd` settles the *superadditivity* half of FS's
`thm:smallbox` for the **faithful** transcription of FS's kinetic operator
`𝒯_B = Q_Bχ_B[√−Δ−c]₊²χ_BQ_B` (`eq:appTB`): the sum-of-one-particle-forms word

    diagSlotWord s c₀ cgap = cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)

is block-splittable (`slotSplit_diagSlotWord`), its ground energy is
superadditive (`diagKinPeB_superadd`, `diagKinPeBAt_group_superadd`), and its
Rayleigh inequality is available (`rayleigh_diagSlotWord`).

What is still missing for Door 4 is FS's **analytic gate** at that word: the
Bogoliubov pairing payment `lm:appbogolubov` (`eq:refinedaprioribog`,
`final_v2.tex` l.3762–3865), stated for the one-particle sum
`Σ_i Q_iχ_i[√−Δ_i − c]₊²χ_iQ_i` — which in the corpus's variables is
`pDiagForm s (fsKinCoeff c₀)` (`SmallBoxBridge`'s `T0Form = pDiagForm`), NOT
the corpus's `kinPWord`, whose mode content `modeP` is a *square of a sum*
over the particles.  The corpus's proved D1
(`Submission.Work.SmallBoxD1Final.lm_appbogolubov_pWord_holds`, restated with
its constant exposed as `Work.SmallBoxA0.lm_appbogolubov_pWord_explicitC`)
controls `kinPWord`; the one-way comparison `kinPWord_le_diagWord` does not
transfer it.  This chapter supplies the faithful statement and its consumers.

This file (`Defs.lean`) is the **interface**: nothing here is a rung, every
declaration is `sorry`-free.  The rungs are the four modules

* `diagW_lm_appbogolubov_explicitC` — (R1) the analytic gate;
* `state_block_bound_of_inputs_diagW` — (R2) the per-state fixed-`n` assembly;
* `diagW_block_bound_of_D1` — (R3) the `eB`-level faithful block bound
  (conditional on the named R1 input, and unconditional once R1 lands);
* `Repoint.lean` — (R4) the per-box comparison `pDiagForm ≼ kinWordB` and the
  downstream re-point.

## Conventions (fixed here, once and for all)

* `X N = Fin N → ℝ³`, `ℝ³ = EuclideanSpace ℝ (Fin 3)`, `acube s = abox 1 s`,
  `abox N s` the centred box of side `s` in `N` slots.
* The **faithful word**: `diagWWord s c₀ cgap := diagSlotWord s c₀ cgap`
  (`cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`), with `cgap` FS's `ε_T`-gap
  constant and `c₀` FS's `(dsℓ)^{-1}` spectral threshold.
* The **faithful energy** at particle count `n+1`:
  `diagWEnergy n s μ w w1 c₀ cgap Φ := diagWWord s c₀ cgap (n+1) Φ + qLHSword …`;
  its `eB`-infimum: `diagWeB n s μ v h c₀ cgap`, and the count-indexed
  `diagWeBAt N s μ v h c₀ cgap` (`Work.KinPSuperadd.diagKinPeBAt`).
* The **D1 error shapes** are the *same* as the corpus D1's
  (`d1TargetC Ct chiR0 chiSup d1Ks` and its derived `η`, `n₊`-coefficient and
  log/quartic/interior bracket): they are functions of the *data*
  `(Ct, R0, s, c₀, v)`, not of the kinetic word, so nothing is re-derived.
* The **mass coefficient** of R1 is FS's own count `(N̂+1)N̂` with `N̂` the
  particle number (`final_v2.tex` l.3766: `½(1+…)(1+…)\hat{gω}(0)(n+1)n|B|^{-2}∫χ_B²`
  with `|B| = ∫χ_B² = s³`, i.e. `(n+1)n/s³`).  For a state on `X (N+1)` this
  is `((N+1)(N+2))/s³`.  (The corpus's proved D1 is stated with `(N+1)²`;
  the difference is the factor `(n+1)/n`, and `(n+1)n` is the *weaker* — and
  FS's — coefficient.  See `README.md` §2.)
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BlockBound4

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  The faithful word, energy and ground energy -/

/-- **The faithful word** (FS's one-particle `𝒯_B`, summed over the particles):
`diagWWord s c₀ cgap = cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`.  This is
`Work.KinPSuperadd.diagSlotWord`, re-exported so that the whole Door-4 chapter
speaks one vocabulary. -/
noncomputable def diagWWord (s c₀ cgap : ℝ) : ∀ N : ℕ, (X N → ℝ) → ℝ :=
  Work.KinPSuperadd.diagSlotWord s c₀ cgap

/-- `diagWWord` is the `KinPSuperadd` word (definitional). -/
lemma diagWWord_eq (s c₀ cgap : ℝ) :
    diagWWord s c₀ cgap = Work.KinPSuperadd.diagSlotWord s c₀ cgap := rfl

/-- `diagWWord` unfolded: `cgap·cnPlus + pDiagForm s (fsKinCoeff c₀)`. -/
lemma diagWWord_apply (s c₀ cgap : ℝ) (N : ℕ) (Φ : X N → ℝ) :
    diagWWord s c₀ cgap N Φ
      = cgap * cnPlus s Φ + pDiagForm s (fsKinCoeff c₀) Φ := rfl

/-- **The faithful small-box energy** at particle count `n+1`:
`diagWEnergy n s μ w w1 c₀ cgap Φ = diagWWord s c₀ cgap (n+1) Φ + qLHSword …`.
This is FS's `ℋ_B(μ)` of `eq:HBU` with `T_B` of `eq:appTB` and the trial-space
potential word `qLHSword`. -/
noncomputable def diagWEnergy (n : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (c₀ cgap : ℝ)
    (Φ : X (n + 1) → ℝ) : ℝ :=
  Work.KinPSuperadd.diagKinPEnergy n s μ w w1 c₀ cgap Φ

/-- `diagWEnergy` at the chosen kernels is the block energy of `diagWWord`. -/
lemma diagWEnergy_eq (n : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (c₀ cgap : ℝ)
    (Φ : X (n + 1) → ℝ) :
    diagWEnergy n s μ w w1 c₀ cgap Φ
      = diagWWord s c₀ cgap (n + 1) Φ + qLHSword (N := n + 1) s μ w w1 Φ := rfl

/-- **The faithful `eB`-level small-box ground energy** (count `n+1`). -/
noncomputable def diagWeB (n : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : ℝ :=
  Work.KinPSuperadd.diagKinPeB n s μ v h c₀ cgap

/-- **The faithful ground energy at a general particle count `N`**. -/
noncomputable def diagWeBAt (N : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : ℝ :=
  Work.KinPSuperadd.diagKinPeBAt N s μ v h c₀ cgap

lemma diagWeB_eq_at (n : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) :
    diagWeB n s μ v h c₀ cgap = diagWeBAt (n + 1) s μ v h c₀ cgap := rfl


/-- **FS's own mass coefficient** `(N̂+1)N̂/s³` at particle count `N̂` (`final_v2.tex`
l.3766: the pairing payment `½(1+…)(1+…)\hat{gω}(0)(n+1)n|B|^{-2}\int\chi_B²` with
`|B| = \int\chi_B² = s³`).  Stated as `(N̂+1)N̂·s⁻³` so that it composes
syntactically with `Work.SmallBoxA0.eta_mass_le_mul` (whose conclusion carries
exactly `((N+1)*N)*(s³)⁻¹` at its `N`) and with the `m²·s⁻³` slot of the
`cS1 > 0` chain. -/
noncomputable def d4MassCoeff (N : ℕ) (s : ℝ) : ℝ := (((N : ℝ) + 1) * (N : ℝ)) * (s ^ 3)⁻¹

/-! ## 2  The D1 error shapes (data functions; the same at either word) -/

/-- D1's constant: `d1TargetC Ct chiR0 chiSup d1Ks`. -/
noncomputable def d4C (Ct : ℝ) : ℝ := Work.SmallBoxA0.d1C Ct

/-- D1's loss factor `η = (1+C·R0/s)(1+C·c₀·a v) − 1`. -/
noncomputable def d4Eta (Ct R0 s c₀ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  Work.SmallBoxA0.kinPeta Ct R0 s c₀ v

/-- D1's `n₊`-coefficient `C·(a v)·(N̂+1)/s³`. -/
noncomputable def d4BogErr (Ct : ℝ) (N : ℕ) (s : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  Work.SmallBoxA0.kinPBogErr Ct N s v

/-- D1's log/quartic/interior bracket. -/
noncomputable def d4Bracket (Ct : ℝ) (N : ℕ) (s c₀ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  Work.SmallBoxA0.kinPBracket Ct N s c₀ v

/-- FS's error shape `Γ = (R0/s)² + K_B³(μ(av)³)^{1/2}`. -/
noncomputable def d4Gamma (R0 s K_B μ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  Work.SmallBoxA0.kinPGamma R0 s K_B μ v

lemma d4C_nonneg (Ct : ℝ) : 0 ≤ d4C Ct := by
  unfold d4C Work.SmallBoxA0.d1C
  unfold Submission.BoseGases.d1TargetC
  exact le_trans (by positivity : (0 : ℝ) ≤ 6 * (2 * Real.pi) ^ 3) (le_max_left _ _)

/-! ## 3  The data bundle

The regime fields of FS's `eq:appdellsassumption`-type that D1's constants
need (`hbox`, `hη`, `hbracket`, `hcorrreg`, `hcgap`, `hchi`) are **independent
of the kinetic word**, as are D1's own inputs (`hc0`, `hCt`, `hav`, `hdil`,
`hWfin`, `hNewton`).  Hence the Door-4 bundle is the corpus's `KinPBoxData`
*verbatim*: we re-export it under the Door-4 name rather than duplicating the
structure (a duplicate would drift).  What differs between the two doors is
only which theorem is stated *over* the bundle. -/

/-- The Door-4 data bundle: the standing small-box hypotheses, FS's
`eq:appdellsassumption`-type regimes, and D1's own inputs.  Identical to
`Work.SmallBoxA0.KinPBoxData`; there is NO Bogoliubov rung field. -/
abbrev DiagWBoxData := Work.SmallBoxA0.KinPBoxData

/-- The Door-4 bundle at a fixed state. -/
abbrev DiagWStateData := Work.SmallBoxA0.KinPStateData

/-- **The `p`-integrability input** of the faithful word's
`pDiagForm s (fsKinCoeff c₀)` per-slot form (the `hint` hypothesis of
`Work.KinPSuperadd.slotSplit_diagSlotWord` /
`Work.KinPSuperadd.rayleigh_diagSlotWord`), NAMED once so that consumers can
pass it around.  It is the `p`-integrability of the per-slot content
`F(‖p‖)·(s³)⁻¹∫_x ‖pSlotAmp s p Ψ i x‖²` at every smooth `Ψ`. -/
def DiagWKinIntegrable (s c₀ : ℝ) : Prop :=
  ∀ (M : ℕ) (Ψ : X M → ℝ), ContDiff ℝ ∞ Ψ →
    Integrable (fun p : ℝ³ => fsKinCoeff c₀ ‖p‖ *
      ∑ i : Fin M, (s ^ 3)⁻¹ * ∫ x in abox M s, ‖pSlotAmp s p Ψ i x‖ ^ 2)

/-- The faithful word is nonnegative at `0 ≤ cgap`, `0 < s`. -/
lemma diagWWord_nonneg (s c₀ cgap : ℝ) (hcgap : 0 ≤ cgap) (hs : 0 < s) (N : ℕ)
    (Φ : X N → ℝ) : 0 ≤ diagWWord s c₀ cgap N Φ :=
  Work.KinPSuperadd.diagSlotWord_nonneg s c₀ cgap hcgap hs N Φ

/-! ## 4  What is already PROVED for this word (import list for consumers)

* `Work.KinPSuperadd.slotSplit_diagSlotWord` — block-splittability;
* `Work.KinPSuperadd.blockSuperadd_diagSlotWord` — the sharp one-sided form;
* `Work.KinPSuperadd.rayleigh_diagSlotWord` — the Rayleigh inequality;
* `Work.KinPSuperadd.slotEB_superadd_diagSlotWord`,
  `Work.KinPSuperadd.diagKinPeB_superadd`,
  `Work.KinPSuperadd.diagKinPeBAt_group_superadd` — the grouping trick
  (`n = m·n′ + n″`), i.e. the count-split that `thm:smallbox` needs.

`Door4Summary` collects them in one place so that a consumer has a single
name for the "superadditivity" half of the door. -/
structure Door4Superadd (s R μ c₀ cgap : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : Prop where
  /-- FS's grouping trick at the faithful word, `n = m·n′ + n″`. -/
  group : ∀ (m N' N'' : ℕ), (m : ℝ) * diagWeBAt N' s μ v h c₀ cgap
      + diagWeBAt N'' s μ v h c₀ cgap ≤ diagWeBAt (m * N' + N'') s μ v h c₀ cgap

/-- The superadditivity half of Door 4, assembled from the two PROVED grouping
theorems of `Work.KinPSuperadd`. -/
theorem door4Superadd {s R μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (hcgap : 0 ≤ cgap)
    (hint : DiagWKinIntegrable s c₀) :
    Door4Superadd s R μ c₀ cgap v h :=
  ⟨fun m N' N'' => Work.KinPSuperadd.diagKinPeBAt_group_superadd hR hv_nonneg hvrad hv_memL1
    hv_supp h hs hRs hμ hcgap hint⟩

/-! ## 5  The per-mode DIAGONAL content (the faithful word's integrand)

`pDiagForm s F Ψ` is the `p`-integral of the diagonal content
`Σ_i (per-slot amplitude)²`; naming that content once lets the D1 argument be
stated per momentum `p`.  The identification
`pDiagForm s F Ψ = (2π)⁻³∫_p F‖p‖(s³)⁻¹(diagContent (qModeRe p) + diagContent (qModeIm p))`
is the lemma `pDiagForm_eq_diagContent` (its own module). -/

/-- **The per-mode DIAGONAL content** of a real mode `g`:
`Σ_i ∫_{abox N s} (∫_{acube s} g z · Ψ(x_{i←z}) dz)²`.  This is the sum over the
slots of the squared slot amplitude — the quadratic form of the one-particle
operator `|g⟩⟨g|` summed over the particles, i.e. `⟨a†(g)a(g)⟩` in the corpus's
slot calculus (up to the `(s³)⁻¹` normalisation of `pDiagForm`). -/
noncomputable def diagContent (s : ℝ) (g : ℝ³ → ℝ) (N : ℕ) (Ψ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N s, (∫ z in acube s, g z * Ψ (Function.update x i z)) ^ 2

/-- The diagonal content is nonnegative. -/
lemma diagContent_nonneg (s : ℝ) (g : ℝ³ → ℝ) (N : ℕ) (Ψ : X N → ℝ) :
    0 ≤ diagContent s g N Ψ :=
  Finset.sum_nonneg (fun i _ => integral_nonneg (fun _ => sq_nonneg _))


/-! ## 6  The χ-weighted Dirichlet form (the honest localised kinetic at the box's
own window)

`pDiagForm s F` is the quadratic form of the ONE-PARTICLE operator
`QχF(√−Δ)χQ` summed over the particles, and the honest localised kinetic of the
same window is `winDirWord`.  Since `F = fsKinCoeff c₀ = (max(r−c₀)0)² ≤ r²`, the
symbol inequality `(|p|−c₀)₊² ≤ p²` reduces the comparison to the IMS/commutator
computation `χ(−Δ)χ ≼ χ²(−Δ) + ‖∇χ‖²_∞`, whose commutator loss is `≲ 1/s²`
(paying, as FS do, with the `ε_T`-gap term `cgap·cnPlus ≥ 1/(36s²)·n₊`). -/

/-- **The χ-weighted Dirichlet form** `Σ_iΣ_k ∫_{abox N s} χ(x_i)²(∂_{ik}Φ)²`
with `χ = chiScale s` — the honest localised kinetic of the box window
(the box-level sibling of `Work.SmallBoxSliding.kinWordB`, which uses the
sliding window `chiSmallB M ℓ d u`). -/
noncomputable def winDirWord (N : ℕ) (s : ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N s, (chiScale s (x i)) ^ 2 * (fderiv ℝ Φ x (kcDir N i k)) ^ 2


end Work.BlockBound4
