import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7AK.K15R.Defs
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.Defs` — the honest §10 gate (node GATE)

Design: `BOSE_BOXFOCK_LEAD.md` §5.3/§5.6 (Claude, curric-46, 2026-10-04).

The §10 kernel interface of `Work.BoseK15.Q3Kernel'` / `Work.BoseB7AK.Q3KernelG`
is *not* satisfiable at the honest box model: its row `kmom_sub` is guarded only
by `f_L ≠ 0` and `k ∈ P_H`, while the honest lattice cube `Lab N` wraps around
near the cutoff, so the label identity needs the *momentum* guard `Ŵ₁(k) ≠ 0`
(finding **F1**, machine-checked in `BOSE_BOXFOCK_KmomSubFalse.lean.txt`).  The
corrected gate `Q3KernelFS` of the design (Appendix A §5) repairs four rows:

* `kmom_subW` / `hasKernelW` guarded by `E.W1 k ≠ 0`;
* `fL_supp2`: FS's own support `‖s‖ ≤ 2K_L√(μa)` (the design's `fL_supp` with
  `K_L√(μa)` is refuted by the cutoff profile, which is `1` on `[0,1]` and
  vanishes on `[2,∞)` only);
* `q2exLowerR`: the `Q₂^ex` cancellation with the reserve `½·dNumOpR` off
  `P_H^q` (the model's `n₊^H` starts at `2K_L√(μa)`, while the physical one starts
  at `K_L√(μa)`; the window `[K_L√(μa), 4K_L√(μa)]` is paid by the kinetic
  energy there — this is the node GATE's own content).

## Contents

* `kinkEnv` — the environment `E` with its kinetic symbol replaced by FS's
  *kinked* `Work.BoseB4.tauFun` (and `𝒜` recomputed accordingly).  It is the
  device that lets the whole of `Work.BoseK15`'s row machinery be reused at the
  honest (smoothed) environment: `Work.BoseK15.K15Input` is a statement about an
  environment differing from `E` only in `tau`/`A`, and every field of
  `K15Input` except `halpha_lip`/`hintOne` is *τ-free*, hence transports.
* `rHi` — the design's `RHi`: `|k| ≥ ½K_L√(μa)`, the region on which the
  Bogoliubov diagonal `𝒟` is available (and off `P_H^q`).
* `GateKernelFS` — the corrected gate, field for field the design's `Q3KernelFS`.
* `GateInput` — the honest bundle: the τ̃-pin (`tauF`, even, nonnegative), the
  two Σ-rows `A_ge`/`ABq` and the three density-uniform FS §11 rows
  (`alpha_lip`, `intOne`, `q2exLowerR`), plus a `K15Input` at the kinked
  environment (`kink`), which carries all the primitive potential/χ/lattice data.

## Conventions

* `ℝ³ = EuclideanSpace ℝ (Fin 3)`; the mode vocabulary is that of `Work.BoseB7`
  (`FockData`, `Q3Env`) and `Work.BoseB7A` (`TildeData`), the bundle vocabulary
  that of `Work.BoseK15` (`K15Input`, `corpusBox`).
* Every constant is absolute; the single chapter constant is `K₀` of the bundle.
* The result is *not* self-contained: the `kink` field is the honest row bundle
  of §10, whose inhabitation at the honest box is `GateHonest.lean`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A

open Work.BoseFixR

/-- **The kinked environment**: `E` with FS's *kinked* kinetic symbol
`Work.BoseB4.tauFun eT s d ℓ (·)` in place of `tau`, and `𝒜 = τ + ρ_zŴ₁`
recomputed.  Everything else — `z`, `ℓ`, `μ`, `a`, `K_H`, `Kl`, `KL`, `d`, `s`,
`ε_T`, `b`, `M`, `𝓜`, `δ`, `f_L`, `Ŵ₁`, `Ŵ₁ω`, `χ̂`, `χ̂²`, `ℬ`, hence `ρ_z`,
`𝓁`, `𝒟`, `α`, `η` — is `E`'s.

The point of the definition: `Work.BoseK15.K15Input`'s *only* τ-dependent rows
are `tau_eq`, `A_eq`, `halpha_lip` and `hintOne`; at `kinkEnv F E` they are the
rows of FS's own τ, so the whole K15 chapter (potential, χ-decay, lattice sums,
`sum_W1sq`, `count_PL`, the χ̂²-form, …) applies, and its τ-free conclusions
transport to `E` by `rfl`. -/
abbrev kinkEnv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : Q3Env Mode :=
  { E with
    tau := fun k => Work.BoseB4.tauFun E.eT E.s E.d E.ell (F.kmom k)
    A := fun k => Work.BoseB4.tauFun E.eT E.s E.d E.ell (F.kmom k) + E.rho * E.W1 k }

@[simp] lemma kinkEnv_tau {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) :
    (kinkEnv F E).tau k = Work.BoseB4.tauFun E.eT E.s E.d E.ell (F.kmom k) := rfl

@[simp] lemma kinkEnv_A {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) :
    (kinkEnv F E).A k = Work.BoseB4.tauFun E.eT E.s E.d E.ell (F.kmom k) + E.rho * E.W1 k :=
  rfl

@[simp] lemma kinkEnv_W1 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) : (kinkEnv F E).W1 k = E.W1 k := rfl

@[simp] lemma kinkEnv_W1omega {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) :
    (kinkEnv F E).W1omega k = E.W1omega k := rfl

@[simp] lemma kinkEnv_hatChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) :
    (kinkEnv F E).hatChi k = E.hatChi k := rfl

@[simp] lemma kinkEnv_hatChiSq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) :
    (kinkEnv F E).hatChiSq k = E.hatChiSq k := rfl

@[simp] lemma kinkEnv_fL {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) : (kinkEnv F E).fL k = E.fL k := rfl

@[simp] lemma kinkEnv_B {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) : (kinkEnv F E).B k = E.B k := rfl

@[simp] lemma kinkEnv_mu {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).mu = E.mu := rfl

@[simp] lemma kinkEnv_aScat {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).aScat = E.aScat := rfl

@[simp] lemma kinkEnv_KH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).KH = E.KH := rfl

@[simp] lemma kinkEnv_Kl {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).Kl = E.Kl := rfl

@[simp] lemma kinkEnv_KL {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).KL = E.KL := rfl

@[simp] lemma kinkEnv_ell {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).ell = E.ell := rfl

@[simp] lemma kinkEnv_eT {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).eT = E.eT := rfl

@[simp] lemma kinkEnv_b {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).b = E.b := rfl

@[simp] lemma kinkEnv_intM {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).intM = E.intM := rfl

@[simp] lemma kinkEnv_W1omega0 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) : (kinkEnv F E).W1omega0 = E.W1omega0 := rfl

/-- **The region kept for §10 and for the `q2exLower` reserve**: `|k| ≥ ½K_L√(μa)`.
This is the design's `RHi` (`BOSE_BOXFOCK_LEAD.md` §5.3), written here so that
the gate is stateable before the vocabulary module lands; the two are the same
predicate. -/
def rHi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : FockData Mode)
    (E : Q3Env Mode) (k : Mode) : Prop :=
  E.KL * Real.sqrt (E.mu * E.aScat) / 2 ≤ ‖F.kmom k‖

instance {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : FockData Mode)
    (E : Q3Env Mode) : DecidablePred (rHi F E) := fun k => Classical.dec _

@[simp] lemma rHi_iff {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (E : Q3Env Mode) (k : Mode) :
    rHi F E k ↔ E.KL * Real.sqrt (E.mu * E.aScat) / 2 ≤ ‖F.kmom k‖ := Iff.rfl

/-- The K15R fork's `corpusBox` is the K15 chapter's (both are the corpus χ). -/
theorem K15R_corpusBox_eq : Work.BoseB7AK.K15R.corpusBox = Work.BoseK15.corpusBox := rfl

/-- **The admissible density window of the gate**: `ρ ∈ [μ/2, 3μ/2]` (which
`CloseCond` implies at FS's parameters, `eq:Close`).  All the `ρ`-dependent rows
of the honest bundle are stated on this window. -/
def AdmRho {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Q3Env Mode) (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ E.mu / 2 ≤ ρ ∧ ρ ≤ 3 * E.mu / 2

/-! ## 3bis. The corrected τ-free input bundle `KinkFS`

The design's `Q3Kernel'_of_box` consumes `Work.BoseK15.K15Input`, and the
`Work.BoseB7AK.K15R` fork was built from it by deleting the three pointwise
`Ŵ₁ω` rows (which have no honest instance).  Two of the remaining rows of that
bundle, however, are *also* unsatisfiable at the honest box, and for the same
reason as finding **F1**:

* `K15Input.kmom_add : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E → kmom (i-j) = kmom i - kmom j`
  — the guard is only *lower*-bounded in momentum (`PH` has no upper bound), and
  the F1 chain `k_n = k₀ - n•s` stays in `P_H` whenever `⟨kmom k₀, kmom s⟩ ≤ 0`, so
  on any finite lattice with a low nonzero mode and `P_H ≠ ∅` the row is false;
* `K15Input.hasKernel`, guarded the same way (its unguarded form is
  `Work.BoseK15.Obstruction`),
* `K15Input.fL_supp`/`fL_eq_one` with radius `K_L√(μa)` (finding **F7**: FS's
  `f_L` vanishes only on `[2,∞)`, so its honest support has radius
  `2K_L√(μa)`; the two rows together force `f_L = 1_{ball}`, which contradicts
  `E.fL = f_L(·/(K_L√(μa)))∘kmom` at the lattice points with ratio in `(1,2)`).

`KinkFS` is the same bundle with those rows repaired exactly as the design
repairs the *gate*: the two label rows are guarded by `E.W1 k ≠ 0` (`Ŵ₁` is what
every §10 word carries, and the UV cut confines `supp W1` to `|k| ≤ 2Λ` with
`4K_L√(μa) ≤ Λ`, so the guard confines the labels strictly inside the lattice
range — the honest fix of F1), and the `f_L` support is FS's own
`‖kmom s‖ ≤ 2K_L√(μa)` (F7).  Every `ρ`-dependent and every §11/§12 row stays
out of the bundle: they are the explicit rows of `GateInput`.

The bundle is a `Prop`; its fields are exactly the τ-free rows that
`GateInput.toGateKernelFS` consumes. -/
structure KinkFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : Prop where
  /-- `|Ŵ₁| ≤ K₀a` (FS `eq:1Q-integral`). -/
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  W1_even : ∀ k, E.W1 (-k) = E.W1 k
  /-- the scattering length is nonnegative (FS's `a > 0`). -/
  aScat_nonneg : 0 ≤ E.aScat
  /-- the momentum assignment is odd (so that `E.hatChi` is even). -/
  kmom_neg : ∀ k, F.kmom (-k) = -F.kmom k
  fL_nonneg : ∀ s, 0 ≤ E.fL s
  fL_le_one : ∀ s, E.fL s ≤ 1
  fL_even : ∀ s, E.fL (-s) = E.fL s
  /-- **FS's own support** `supp f_L ⊆ {|s| ≤ 2K_L√(μa)}` (finding F7). -/
  fL_supp2 : ∀ s, E.fL s ≠ 0 → ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat))
  /-- **The guarded label arithmetic** (finding F1): the guard `E.W1 k ≠ 0` is the
  UV cut-off of `E.W1`, which confines `k` strictly inside the lattice range. -/
  kmom_subW : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.kmom (s - k) = F.kmom s - F.kmom k
  /-- the *inner* additivity: both labels are localised (`f_L ≠ 0`). -/
  kmom_subL : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 → F.kmom (s - s') = F.kmom s - F.kmom s'
  /-- FS `eq:Commutator_general` on the summed pairs, with the F1 guard. -/
  hasKernelW : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E → E.W1 j ≠ 0 →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  /-- the mode-indexed `χ̂` is the corpus box kernel at `ℓ • kmom`. -/
  hatChi_eq : ∀ k, E.hatChi k = Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom k)
  /-- the mode-indexed `χ̂²` is the corpus box kernel at `ℓ • kmom`. -/
  hatChiSq_eq : ∀ k, E.hatChiSq k = Work.BoseK15.corpusBox.hatChiSq (E.ell • F.kmom k)
  W1omega0_nonneg : 0 ≤ E.W1omega0
  W1omega0_le : E.W1omega0 ≤ K₀ * E.aScat
  /-- the PSD half of the `χ̂²`-form (Bochner + Schur), for weights vanishing off
  `supp f_L`. -/
  hatChiSq_form_psd : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
    (∀ s ∈ S, c s ≠ 0 → E.fL s ≠ 0) →
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s)

namespace KinkFS

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ K₁ : ℝ}

/-- `|χ̂| ≤ 1` at the modes. -/
theorem hatChi_le (h : KinkFS K₀ F T E) (s : Mode) : |E.hatChi s| ≤ 1 := by
  rw [h.hatChi_eq s]; exact Work.BoseK15.hatChi_le_one.1 _

/-- `|χ̂²| ≤ 1` at the modes. -/
theorem hatChiSq_le (h : KinkFS K₀ F T E) (s : Mode) : |E.hatChiSq s| ≤ 1 := by
  rw [h.hatChiSq_eq s]; exact Work.BoseK15.hatChi_le_one.2 _

/-- `χ̂` is even at the modes. -/
theorem hatChi_even (h : KinkFS K₀ F T E) (s : Mode) : E.hatChi (-s) = E.hatChi s := by
  rw [h.hatChi_eq (-s), h.hatChi_eq s, h.kmom_neg s, smul_neg, Work.BoseB4.BoxData.hatChi_neg]

/-- `χ̂²` is even at the modes. -/
theorem hatChiSq_even (h : KinkFS K₀ F T E) (s : Mode) : E.hatChiSq (-s) = E.hatChiSq s := by
  rw [h.hatChiSq_eq (-s), h.hatChiSq_eq s, h.kmom_neg s, smul_neg,
    Work.BoseB4.BoxData.hatChiSq_neg]

/-- The bundle is **monotone in `K₀`**: only `W1_le` and `W1omega0_le` mention it. -/
theorem mono {h : KinkFS K₀ F T E} (hle : K₀ ≤ K₁) : KinkFS K₁ F T E where
  W1_le := fun k => le_trans (h.W1_le k) (mul_le_mul_of_nonneg_right hle h.aScat_nonneg)
  W1_even := h.W1_even
  aScat_nonneg := h.aScat_nonneg
  kmom_neg := h.kmom_neg
  fL_nonneg := h.fL_nonneg
  fL_le_one := h.fL_le_one
  fL_even := h.fL_even
  fL_supp2 := h.fL_supp2
  kmom_subW := h.kmom_subW
  kmom_subL := h.kmom_subL
  hasKernelW := h.hasKernelW
  hatChi_eq := h.hatChi_eq
  hatChiSq_eq := h.hatChiSq_eq
  W1omega0_nonneg := h.W1omega0_nonneg
  W1omega0_le := le_trans h.W1omega0_le (mul_le_mul_of_nonneg_right hle h.aScat_nonneg)
  hatChiSq_form_psd := h.hatChiSq_form_psd

end KinkFS

/-- **The corrected §10 gate** (`BOSE_BOXFOCK_LEAD.md` §5.3, the design's
`Q3KernelFS`; `RHi` unfolded).  Compared with `Work.BoseK15.Q3Kernel'`:

* `kmom_subW`, `hasKernelW` are guarded by `E.W1 k ≠ 0` — the unguarded rows have
  no instance on any finite lattice with a low nonzero mode and `P_H ≠ ∅`
  (finding F1);
* `fL_supp2` has FS's own radius `2K_L√(μa)`;
* `q2exLowerR` carries the reserve `½·dNumOpR` on `rHi ∖ P_H^q`. -/
structure GateKernelFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  W1_even : ∀ k, E.W1 (-k) = E.W1 k
  A_even : ∀ k, E.A (-k) = E.A k
  B_even : ∀ k, E.B (-k) = E.B k
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  AB : ∀ k, |E.B k| ≤ E.A k
  A_ge : ∀ q, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q
  fL_nonneg : ∀ s, 0 ≤ E.fL s
  fL_le_one : ∀ s, E.fL s ≤ 1
  fL_even : ∀ s, E.fL (-s) = E.fL s
  fL_supp2 : ∀ s, E.fL s ≠ 0 → ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat))
  kmom_subW : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
    F.kmom (s - k) = F.kmom s - F.kmom k
  kmom_subL : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 → F.kmom (s - s') = F.kmom s - F.kmom s'
  hasKernelW : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E → E.W1 j ≠ 0 →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hasKernel_noWrap : ∀ i j, Work.BoseK15.NoWrap F.kmom i j →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1
  hatChi_le : ∀ s, |E.hatChi s| ≤ 1
  hatChi_even : ∀ s, E.hatChi (-s) = E.hatChi s
  hatChiSq_even : ∀ s, E.hatChiSq (-s) = E.hatChiSq s
  hatChi_small : ∀ q, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E
  ccrX_small : ∀ s q, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E
  hatChiSq_form : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
    (∀ s ∈ S, c s ≠ 0 → E.fL s ≠ 0) →
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s) ∧
      ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s)
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s)
  count_PL : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
    ≤ K₀ * (E.Kl * E.KL) ^ 3
  sum_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀
  tail_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
    ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))
  sum_W1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
    ≤ K₀ * E.aScat
  alpha_lip : ∀ p q, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |E.alpha p - E.alpha q| ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  W1omega0_nonneg : 0 ≤ E.W1omega0
  W1omega0_le : E.W1omega0 ≤ K₀ * E.aScat
  intOne : |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
    ≤ K₀ * E.rho * E.aScat * E.KH⁻¹
  q2exLowerR : ∀ Ψ : F.H, 2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
    ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)
      + (1 / 2) * F.qw Ψ (F.dNumOpR E (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k))

/-- **The honest bundle of the gate.**  It consists of

* the τ̃-pin: a symbol `tauF` with `E.tau = tauF ∘ kmom`, even and nonnegative
  (at the honest model `tauF = tauSm`); the *quantitative* facts about τ̃ are
  consumed through `A_ge`/`ABq` below, not through `tauF`;
* the honest §10 rows at the *smoothed* environment `E`: the two quadratic rows
  `A_ge`, `ABq` on `P_H^q` (density-uniform in `ρ`), the low-momentum positivity
  `W1low` of `Ŵ₁` (which turns them into the global `AB`), and the three
  density-uniform FS §11 rows `alpha_lip` (K3), `intOne` (K5) and `q2exLowerR`
  (the `Q₂^ex` cancellation with the `½·dNumOpR` reserve);
* a full `KinkFS K₀ F T E` — the corrected τ-free bundle (`Defs.lean` §3bis:
  the K15 row bundle with the F1/F7 repairs) — which carries the potential, the
  χ-pins and the guarded label/kernel rows. -/
structure GateInput {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) where
  /-- the smoothed kinetic symbol, as a function of the momentum. -/
  tauF : EuclideanSpace ℝ (Fin 3) → ℝ
  tau_eq : ∀ k : Mode, E.tau k = tauF (F.kmom k)
  tau_nonneg : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ tauF p
  tau_even : ∀ p : EuclideanSpace ℝ (Fin 3), tauF (-p) = tauF p
  /-- `Ŵ₁ ≥ 0` below the `P_H^q` threshold (FS §11). -/
  W1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k
  heT0 : 0 ≤ E.eT
  heT1 : E.eT ≤ 1
  /-- `‖k‖²/2 ≤ 𝒜_k` on `P_H^q`, density-uniform in `ρ`. -/
  A_ge : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
    ‖F.kmom q‖ ^ 2 / 2 ≤ (KzEnvAt E ρ).A q
  /-- FS `eq:BoverA` on `P_H^q`, density-uniform in `ρ`. -/
  ABq : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
    2 * |(KzEnvAt E ρ).B q| ≤ (KzEnvAt E ρ).A q
  /-- **K3** at the honest (smoothed) data, density-uniform in `ρ`. -/
  alpha_lip : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode,
    F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |(KzEnvAt E ρ).alpha p - (KzEnvAt E ρ).alpha q|
      ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  /-- **K5** at the honest data, density-uniform in `ρ`. -/
  intOne : ∀ ρ : ℝ, AdmRho E ρ →
    |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k|
      ≤ K₀ * ρ * E.aScat * E.KH⁻¹
  /-- FS `eq:Q3Cancels` with the reserve `½·dNumOpR` on `rHi ∖ P_H^q`. -/
  q2exLowerR : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H,
    2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2ex (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
        + (1 / 2) * F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
            (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k))
  /-- **the box-model equation**: the commutator kernel of `F` is the χ-kernel of
  the momentum *difference* (this is the definition of the honest
  `boxFockData`, and the hypothesis `hFbox` of `Work.BoseK15.Q3Kernel'_of_box`). -/
  boxKernel : ∀ i j : Mode, F.ccrK i j
    = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
      - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
        * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j)
  /-- the corrected τ-free bundle (the potential/χ/label rows). -/
  kink : KinkFS K₀ F T E

end Work.BoseGateFS
