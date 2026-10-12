import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.CubicChi
import Submission.Work.BoseB4.TildeDataInst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.Defs` — the B4-side kernel obligations K1–K5 of FS §10

Design: `BOSE_3Q_LEAD.md` §3–§5 (the K1–K5 list).  The chapter
`Submission/Work/BoseB7A/` states FS §10's `thm:Control3Q` with **absolute**
constants against a *kernel interface* (`Work.BoseB7A.Q3Kernel`,
`Work.BoseB7A.IntKernel`): twenty-seven facts about FS's honest data that §10
consumes.  This area (`BoseK15`) supplies them.

## The obligations

| obligation | content | where |
|---|---|---|
| **K1** | the `TildeData` instance (θ-modes, `N`, `NH`, grading) | already delivered: `Work.BoseB4.exists_tildeData_lattice` |
| **K2** | `χ̂`-decay (`lem:DecaychiHat`) and the lattice sums, `hasKernel`, `ccrX`, `hatChi_even`, `hatChiSq_even`, `hatChiSq_form`, `hatChi_small`, `ccrX_small`, `count_PL`, `sum_hatChiSq`, `tail_hatChiSq` | `ChiReg.lean`, `ChiSums.lean`, `ChiSmall.lean`, `ChiForm.lean` |
| **K3** | `alpha_lip` — the Lipschitz bound on `α` (FS's `T₁` repair, design D7) | `AlphaLip.lean` |
| **K4** | `W1_le`, `W1_even`, `sum_W1sq` and the remaining `Q3Kernel` fields | `Pot.lean`, `SumW1sq.lean` |
| **K5** | `q2exLower` and the `IntKernel` fields (`A_pos`, `AB_kernel`, the `ω`-lattice identity, the lattice sums) | `Green.lean`, `Q2ex.lean` |

## The honest instance

The corpus's *actual* localization function is `Submission.BoseGases.chi`
(`Submission/CubicChi.lean`): the smooth cubic bump — `C^∞`, even, `0 ≤ χ`,
`∫χ² = 1`, supported in the ball of radius `1/2`.  `corpusBox` presents it as
FS's `Work.BoseB4.BoxData`.  Its Fourier transform is what
`Work.BoseB4.BoxData.hatChi` computes, so all the K2 fields are statements about
the corpus's own χ.

`BoseB4/README.md` §9 records that the `BoxData` axioms (continuity,
compactness, normalisation) *alone* do not imply the K2 decay fields: they need
the smoothness of χ.  This chapter therefore isolates that regularity in the
predicate `ChiReg` (`χ̂`, `χ̂²` decay at order `s`) and proves it for the concrete
corpus χ from Mathlib's `SchwartzMap.decay` (`ChiReg_corpus`); everything else in
K2 is derived from it.

## The bundle

`K15Input K₀ F T E` collects, in *primitive* form, everything about FS's data
that the twenty-seven fields need: the lattice geometry (`OnDualLattice`), the
χ-regularity, FS's potential kernels `Ŵ₁`, `Ŵ₁ω`, `ĝ` with their honest bounds,
the kinetic symbol `τ`, FS's cutoff profile `f_L`, and the three genuinely
analytic rows of `lem:EstimateIntegral` (`omega_lattice`, `sum_diff`) and of the
`Q₂^ex` cancellation (`q2exLower`).  `K15Input.toQ3Kernel` (`Main.lean`) derives
the whole of `Work.BoseB7A.Q3Kernel` from it, field by field, and
`K15Input.toIntKernel` the whole of `Work.BoseB7A.IntKernel`.

## Conventions

* `ℝ³ = EuclideanSpace ℝ (Fin 3)`; `realIP f g = ∫ Re(conj f · g)` (corpus).
* Momentum sums are the normalised `(2π)⁻³ℓ³∫dk = Σ_k` of
  `Work.BoseB4.H2nd`.
* `OnDualLattice ℓ kmom` says the labels are the box's dual-lattice points
  `(2π/ℓ)ℤ³` (`Work.BoseB4.vec n = 2πn`).  The finite `Mode` set *truncates*
  FS's integrals, so this is a sublattice embedding, not a group isomorphism; it
  is what every lattice count uses.
* Every constant is absolute and declared once, in `K15Input.K₀`; no `K₀` is
  ever read off an instance.
-/

noncomputable section

open scoped BigOperators Pointwise ContDiff
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The corpus localization function as FS's `BoxData` -/

/-- The corpus χ vanishes off the ball of radius `1/2`, which sits inside the
unit cube. -/
theorem chi_support_subset_unitCell :
    Function.support Submission.BoseGases.chi ⊆ Work.BoseB4.unitCell := by
  intro x hx
  have hle : ‖x‖ ≤ 1 / 2 := by
    by_contra h
    exact hx (Submission.BoseGases.chi_eq_zero_of_norm_gt x (lt_of_not_ge h))
  rw [Work.BoseB4.unitCell]
  intro i
  have h2 : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  exact abs_le.mpr (abs_le.mp (le_trans h2 hle))

/-- **The corpus χ as FS's `BoxData`**: `Submission.BoseGases.chi` on the unit
cell `[-1/2,1/2]³`. -/
noncomputable def corpusBox : Work.BoseB4.BoxData where
  chi := Submission.BoseGases.chi
  chi_cont := Submission.BoseGases.chi_continuous
  chi_nonneg := Submission.BoseGases.chi_nonneg
  chi_even := Submission.BoseGases.chi_even
  cell := Work.BoseB4.unitCell
  cell_meas := Work.BoseB4.isClosed_unitCell.measurableSet
  cell_compact := Work.BoseB4.isCompact_unitCell
  cell_vol := Work.BoseB4.volume_unitCell
  chi_supp := chi_support_subset_unitCell
  chi_int := Submission.BoseGases.chi_L2

@[simp] lemma corpusBox_chi (x : ℝ³) : corpusBox.chi x = Submission.BoseGases.chi x := rfl

/-- The corpus χ is smooth: this is the regularity that supplies K2's decay
(FS `lem:DecaychiHat`). -/
theorem corpusBox_chi_contDiff : ContDiff ℝ (⊤ : ℕ∞) corpusBox.chi :=
  Submission.BoseGases.chi_contDiff

lemma corpusBox_chi_nonneg (x : ℝ³) : 0 ≤ corpusBox.chi x :=
  Submission.BoseGases.chi_nonneg x

lemma corpusBox_chi_even (x : ℝ³) : corpusBox.chi (-x) = corpusBox.chi x :=
  Submission.BoseGases.chi_even x

/-- **The honest box mode system** on the corpus χ: FS's `a_k = a(Q(e^{ikx}χ_Λ))`
over a mode lattice (`Work.BoseB4.boxFockData`).  Abbreviation for readability in
the statements of the chapter. -/
noncomputable abbrev boxFockDataBox (ℓ : ℝ) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (m : ℕ) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j) =
      Work.BoseB7.ccrKernel ℓ corpusBox.hatChiSq corpusBox.hatChi (kmom i) (kmom j)) :
    FockData Mode :=
  Work.BoseB4.boxFockData corpusBox kmom hkmom m f hf

/-- **The θ-mode data on that mode system** (`Work.BoseB4.tildeData`). -/
noncomputable abbrev tildeDataBox (ℓ : ℝ) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (m : ℕ) (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j) =
      Work.BoseB7.ccrKernel ℓ corpusBox.hatChiSq corpusBox.hatChi (kmom i) (kmom j))
    (hg : ∀ s t : Mode, s ≠ 0 → t ≠ 0 → Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0) :
    Work.BoseB7A.TildeData (boxFockDataBox ℓ kmom hkmom m f hf) :=
  Work.BoseB4.tildeData corpusBox kmom hkmom m f g hf hg

/-! ## 2. The lattice geometry -/

/-- **The dual-lattice condition.**  The mode labels of the box are *distinct*
dual-lattice points `(2π/ℓ)ℤ³`: `kmom` is injective and
`kmom i = ℓ⁻¹ • vec n` with `vec n = 2πn` (`Work.BoseB4.vec`).

Injectivity is part of the geometry (the honest mode labels are the box's
momentum lattice points, and a momentum occurs once); it is exactly what turns
`Σ_i` into a sum over a subset of `ℤ³` in the lattice counts of K2/K4/K5. -/
def OnDualLattice {Mode : Type*} (ℓ : ℝ) (kmom : Mode → ℝ³) : Prop :=
  Function.Injective kmom ∧ ∀ i : Mode, ∃ n : Fin 3 → ℤ, kmom i = ℓ⁻¹ • Work.BoseB4.vec n

lemma OnDualLattice.injective {Mode : Type*} {ℓ : ℝ} {kmom : Mode → ℝ³}
    (h : OnDualLattice ℓ kmom) : Function.Injective kmom := h.1

lemma OnDualLattice.exists_vec {Mode : Type*} {ℓ : ℝ} {kmom : Mode → ℝ³}
    (h : OnDualLattice ℓ kmom) (i : Mode) :
    ∃ n : Fin 3 → ℤ, kmom i = ℓ⁻¹ • Work.BoseB4.vec n := h.2 i

/-- A chosen lattice index of a mode. -/
noncomputable def OnDualLattice.lift {Mode : Type*} {ℓ : ℝ} {kmom : Mode → ℝ³}
    (h : OnDualLattice ℓ kmom) (i : Mode) : Fin 3 → ℤ := Classical.choose (h.2 i)

lemma OnDualLattice.lift_spec {Mode : Type*} {ℓ : ℝ} {kmom : Mode → ℝ³}
    (h : OnDualLattice ℓ kmom) (i : Mode) :
    kmom i = ℓ⁻¹ • Work.BoseB4.vec (h.lift i) := Classical.choose_spec (h.2 i)

/-- The lattice index map is injective (its composite with the injection
`n ↦ ℓ⁻¹ • vec n` is `kmom`). -/
lemma OnDualLattice.lift_injective {Mode : Type*} {ℓ : ℝ} {kmom : Mode → ℝ³}
    (h : OnDualLattice ℓ kmom) : Function.Injective h.lift := by
  intro i j hij
  refine h.injective ?_
  rw [h.lift_spec i, h.lift_spec j, hij]

/-! ## 3. The regularity of `χ̂` (FS `lem:DecaychiHat`) -/

/-- **FS `lem:DecaychiHat` as an interface.**  `χ̂` and `χ̂²` decay at order `s`
with constant `C`:

    `|χ̂(p)|·(1+‖p‖²)^s ≤ C`,   `|χ̂²(p)|·(1+‖p‖²)^s ≤ C`.

For FS's product-form χ this holds with `C = ∫|(1-Δ)^sχ|` and `s = M̃ = ⌊M/2⌋`;
for the *corpus* χ (which is `C^∞`) it holds for **every** `s`
(`ChiReg_corpus`).  This is precisely the regularity that the `BoxData` axioms of
`Work.BoseB4.BoxChi` leave out. -/
def ChiReg (B : Work.BoseB4.BoxData) (s : ℕ) (C : ℝ) : Prop :=
  (∀ p : ℝ³, |B.hatChi p| * (1 + ‖p‖ ^ 2) ^ s ≤ C) ∧
  (∀ p : ℝ³, |B.hatChiSq p| * (1 + ‖p‖ ^ 2) ^ s ≤ C)

/-- The decay order of the chapter: `s = 26`.  Two thresholds enter:

* `hatChi_small` on `P_H^q` needs `2s·log(ℓ/(4K_Ha)) ≥ log(η^{-1})`, i.e.
  `51.5·s ≥ 1236` (FS's own `M̃ = 24` is exactly borderline; `26` gives margin);
* `tail_hatChiSq` needs `Σ_{‖p‖≥K_ℓK_L}|χ̂²(p)| ≤ (K_ℓK_L)^{-48}`, i.e.
  `24s - 36 ≥ 576`, i.e. `s ≥ 25.5`.

The corpus χ being `C^∞`, both are available. -/
def decayOrder : ℕ := 26

lemma one_le_decayOrder : (1 : ℕ) ≤ decayOrder := by decide

/-- **FS's cutoff profile** `f` of `f_L(s) = f(s/(K_L√(μa)))` (l. 1464): a fixed
profile with `0 ≤ f ≤ 1` vanishing beyond `|x| = 2`. -/
structure Profile (f : ℝ → ℝ) : Prop where
  nonneg : ∀ x : ℝ, 0 ≤ f x
  le_one : ∀ x : ℝ, f x ≤ 1
  /-- FS's cutoff is `1` on the inner ball. -/
  eq_one : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = 1
  /-- FS's cutoff vanishes beyond `|x| = 2`. -/
  supp : ∀ x : ℝ, f x ≠ 0 → x ≤ 2

/-! ## 4. The primitive data of the honest instance

`K15Input` gathers FS's honest data in *primitive* form.  Everything about it
is a true statement about FS's χ (`corpusBox`, `C^∞`), FS's cutoff profile
`f_L`, FS's kinetic symbol `τ` (`def:tau`), FS's potential kernels `Ŵ₁`, `Ŵ₁ω`,
`ĝ`, and the three analytic rows of `lem:EstimateIntegral` / of the first
quantised `Q₂^ex` estimate that the chapter does not re-derive. -/

/-- **The primitive data of the honest `BoseB4` instance at FS's parameters.** -/
structure K15Input (K₀ : ℝ) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) where
  /-- FS `eq:def_ell`: the box side, which is the environment's. -/
  ell : ℝ
  ell_eq_E : ell = E.ell
  ell_pos : 0 < ell
  /-- FS's scattering length is positive at the honest instance. -/
  aScat_pos : 0 < E.aScat
  Cw : ℝ
  Cw_nonneg : 0 ≤ Cw
  /-- FS's chemical potential is positive. -/
  mu_pos : 0 < E.mu
  /-- FS's `K_H > 0`. -/
  KH_pos : 0 < E.KH
  /-- FS's `K_ℓ > 0`. -/
  Kl_pos : 0 < E.Kl
  /-- `K_H ≥ 1` (FS's `K`'s are large). -/
  one_le_KH : 1 ≤ E.KH
  /-- The box side is positive; this is FS `eq:def_ell` with `μa > 0`. -/
  ell_pos_E : 0 < E.ell
  /-- The momentum assignment. -/
  kmom : Mode → ℝ³
  kmom_eq : ∀ i : Mode, F.kmom i = kmom i
  kmom_neg : ∀ i : Mode, kmom (-i) = -kmom i
  /-- **The label arithmetic `kmom (s - k) = kmom s - kmom k` on the pairs §10
  uses** — *guarded*, as in `Work.BoseB7A.Q3Kernel.kmom_sub`.  The guard is not
  cosmetic: the mode set is a *truncated* lattice and its group law wraps around
  near the cutoff, while `kmom` reads the unwrapped representative, so additivity
  holds only on the pairs `(s,k)` actually summed over (`s ∈ supp f_L ⊆ P_L`,
  `k ∈ P_H`); an *unguarded* additivity would force `kmom ≡ 0` on the finite
  group `Mode` (design §5, "label wrap-around near the cutoff"). -/
  kmom_add : ∀ i j : Mode, E.fL i ≠ 0 → j ∈ F.PHset E →
    kmom (i - j) = kmom i - kmom j
  /-- **The label arithmetic on pairs of *localised* modes** — the second guard
  needed by §10.  The PSD/Schur form `hatChiSq_form` is used with `S ⊆ excited`
  and weights `c = f_L` (so only `s ∈ supp f_L` contribute), and it needs
  `E.hatChiSq (s'-s) = χ̂²(ℓ(kmom s' - kmom s))`, i.e. additivity on pairs of
  modes *both in `supp f_L`*.  Both labels are then in `P_L` (small), so their
  difference is far from the truncation boundary and the identity holds in the
  honest box model (design §5); the unguarded form is impossible
  (`Work.BoseK15.kmom_eq_zero_of_add`). -/
  kmom_add_inner : ∀ i j : Mode, E.fL i ≠ 0 → E.fL j ≠ 0 →
    kmom (i - j) = kmom i - kmom j
  /-- the labels are dual-lattice points. -/
  hlat : OnDualLattice ell kmom
  /-- FS `eq:def_ell`/`eq:KL_d` read together: `ℓ·K_L·√(μa) = K_ℓK_L` — the
  identity that turns the `f_L`-support (`‖kmom s‖ ≤ K_L√(μa)`) and the `1-f_L`
  threshold into the lattice radius `K_ℓK_L`. -/
  ellKL : ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL
  /-- **K2's regularity.**  The constant of the corpus χ-decay at order `decayOrder`. -/
  Cchi : ℝ
  Cchi_nonneg : 0 ≤ Cchi
  chi : ChiReg corpusBox decayOrder Cchi
  /-- a constant bounding every finite `Σ_n (1+‖vec n‖²)^{-decayOrder}`. -/
  Csum : ℝ
  Csum_nonneg : 0 ≤ Csum
  /-- every finite lattice sum of the decay weight is `≤ Csum`. -/
  sum_geom : ∀ S : Finset (Fin 3 → ℤ),
    (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ decayOrder)⁻¹) ≤ Csum
  /-- a constant for the *tail* lattice sum above a radius `R ≥ 1`. -/
  Ctail : ℝ
  Ctail_nonneg : 0 ≤ Ctail
  /-- the tail lattice sum is `≤ Ctail·R^{-intM}`. -/
  sum_geom_tail : ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
    (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
    (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ decayOrder)⁻¹) ≤ Ctail / R ^ E.intM
  /-- a constant for the `(1+‖·‖)^{-4}` sum over the modes, weighted by `ℓ³`. -/
  Csem : ℝ
  Csem_nonneg : 0 ≤ Csem
  sum_sem : (∑ q ∈ excited Mode, (1 + ‖kmom q‖) ^ (-(4 : ℝ))) ≤ Csem * ell ^ 3
  /-- the constant of the ball count `#S ≤ Ccard·(ρ+1)³`. -/
  Ccard : ℝ
  one_le_Ccard : 1 ≤ Ccard
  card_le : ∀ (S : Finset (Fin 3 → ℤ)) (ρ : ℝ), 0 ≤ ρ →
    (∀ n ∈ S, ‖Work.BoseB4.vec n‖ ≤ ρ) → (S.card : ℝ) ≤ Ccard * (ρ + 1) ^ 3
  /-- **The chapter constant dominates every auxiliary constant** (it is free: the
  estimates of §10 only need *some* absolute `K₀`). -/
  K₀_one : 1 ≤ K₀
  K₀_w : Cw ≤ K₀
  K₀_chi : Cchi * 8 ^ (2 * decayOrder) ≤ K₀
  K₀_sum : Cchi * (Csum + Ctail) ≤ K₀
  K₀_card : Ccard * 8 ≤ K₀
  /-- The **scaled** weighted lattice sum of `sum_W1sq`: the `1/‖q‖²` must be
  integrated against the decay, not bounded crudely by `(2K_Ha)²` (which would
  insert `K_H²` and force an upper bound on `K₀`).  The sum is `0 ≤ · ≤ Cwt`
  with an **absolute** `Cwt`: pointwise `(1+‖q‖)^{-4}‖q‖^{-2} ≤ ‖q‖^{-4}` above
  `‖q‖ = 1` and `≤ ‖q‖^{-2}` below, and the two lattice sums are
  `(2π)^{-3}∫_{|q|≥1}|q|^{-4}dq` and `(2π)^{-3}∫_{c ≤ |q| ≤ 1}|q|^{-2}dq ≤ 1`
  (`Work.BoseK15.sum_wt_abs`). -/
  Cwt : ℝ
  Cwt_nonneg : 0 ≤ Cwt
  sum_wt : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
        (1 + ‖kmom q‖) ^ (-(4 : ℝ)) * ‖kmom q‖ ^ (-(2 : ℝ)) ≤ Cwt
  /-- `sum_W1sq`'s constant bookkeeping — a **lower** bound on the chapter
  constant, unlike the crude route's upper bound: `8·Cw²·Cwt ≤ K₀`.  With it
  the derivation gives `≤ (Cwa)²·Cwt = Cw²Cwt a² ≤ K₀a`. -/
  K₀_wt : 8 * Cw * Cw * Cwt ≤ K₀
  /-- FS's `Ŵ₁`. -/
  W1f : ℝ³ → ℝ
  W1_eq : ∀ k : Mode, E.W1 k = W1f (kmom k)
  W1_even : ∀ p : ℝ³, W1f (-p) = W1f p
  W1_contDiff : ContDiff ℝ 1 W1f
  /-- **The *absolute* constant of FS's `Ŵ₁`.**  It must be absolute and not `K₀`:
  `sum_W1sq` bounds `ℓ⁻³Σ_{P_H^q}Ŵ₁²/k²` by `K₀a`, and a derivation that replaces
  `Ŵ₁` by `K₀a` produces `K₀²a²` on the left, forcing an *upper* bound on `K₀` that
  is incompatible with the χ-side domination fields (`K₀_chi` etc.).  With `Cw`
  absolute the derivation gives `≤ K₀a` exactly when `K₀ ≥ Cw²·Cwt·a`, a *lower*
  bound.  It is declared near the top of the structure because the domination
  fields below refer to it.

  FS `eq:W1-g`: `|Ŵ₁| ≤ Cw·a`. -/
  W1_le : ∀ p : ℝ³, |W1f p| ≤ Cw * E.aScat
  /-- the decay of `Ŵ₁` (it is the Fourier transform of a compactly supported
  smooth `W₁`), which is what makes `sum_W1sq` a *finite* lattice sum even when the
  mode set is truncated at a momentum cutoff far above `1/a`. -/
  W1_decay : ∀ p : ℝ³, |W1f p| * (1 + ‖p‖) ^ 2 ≤ Cw * E.aScat
  /-- the linear growth of `∇Ŵ₁` (K3). -/
  W1_grad_le : ∀ p : ℝ³, ‖fderiv ℝ W1f p‖ ≤ Cw * E.aScat * (1 + ‖p‖)
  /-- The diluteness normalisation `a ≤ 1` (FS rescale the interaction so that the
  scattering length is at most `1`; at the corpus instance `a = 1`). -/
  aScat_le_one : E.aScat ≤ 1
  /-- FS's `Ŵ₁ω`. -/
  W1omegaf : ℝ³ → ℝ
  W1omega_eq : ∀ k : Mode, E.W1omega k = W1omegaf (kmom k)
  W1omega_nonneg : ∀ p : ℝ³, 0 ≤ W1omegaf p
  W1omega0_nonneg : 0 ≤ E.W1omega0
  W1omega0_le : E.W1omega0 ≤ K₀ * E.aScat
  /-- FS's `f_L`, i.e. the rescaled cutoff profile. -/
  fLf : ℝ³ → ℝ
  fL_eq : ∀ s : Mode, E.fL s = fLf (kmom s)
  fL_nonneg : ∀ p : ℝ³, 0 ≤ fLf p
  fL_le_one : ∀ p : ℝ³, fLf p ≤ 1
  /-- `f_L` is even (it is a function of `‖p‖`). -/
  fL_even : ∀ p : ℝ³, fLf (-p) = fLf p
  /-- `f_L` vanishes outside `P_L`: `‖p‖ ≤ K_L√(μa)`. -/
  fL_supp : ∀ p : ℝ³, fLf p ≠ 0 → ‖p‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat)
  /-- `f_L = 1` on the inner ball `P_L` (FS's cutoff profile is `1` on `[0,1]`), so
  `1 - f_L` is supported on the momenta above `K_ℓK_L` — which is what makes
  `tail_hatChiSq` a *small* lattice sum. -/
  fL_eq_one : ∀ p : ℝ³, ‖p‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat) → fLf p = 1
  /-- FS's `def:tau`. -/
  tau_eq : ∀ k : Mode, E.tau k = Work.BoseB4.tauFun E.eT E.s E.d E.ell (kmom k)
  /-- FS `eq:BogHamPositive-1`: `𝒜 = τ + ρ_zŴ₁`. -/
  A_eq : ∀ k : Mode, E.A k = E.tau k + E.rho * E.W1 k
  /-- FS `eq:BogHamPositive-1`: `ℬ = ρ_zŴ₁`. -/
  B_eq : ∀ k : Mode, E.B k = E.rho * E.W1 k
  /-- the mode-indexed `χ̂ = χ̂(ℓ·)`. -/
  hatChi_eq : ∀ k : Mode, E.hatChi k = corpusBox.hatChi (E.ell • kmom k)
  /-- the mode-indexed `χ̂²`. -/
  hatChiSq_eq : ∀ k : Mode, E.hatChiSq k = corpusBox.hatChiSq (E.ell • kmom k)
  /-- the θ/χ cross commutator `ccrX s k = χ̂(ℓ(kmom k - kmom s))`. -/
  ccrX_eq : ∀ s k : Mode, T.ccrX s k = corpusBox.hatChi (E.ell • (kmom k - kmom s))
  /-- FS `eq:Commutator_general` in mode indices, **on the pairs §10 sums over**
  (`i ∈ supp f_L ⊆ P_L`, `j ∈ P_H`).  The guard is not cosmetic: the *global*
  identity forces the unguarded label additivity, hence `kmom ≡ 0` on the finite
  group `Mode` (`Work.BoseK15.kmom_eq_zero_of_add`) and empties `P_H^q`
  (`Work.BoseK15.PHq_eq_false_of_add`), so no honest instance exists — the design's
  §5 wrap-around risk.  This is the form the box model satisfies
  (`Work.BoseK15.hasKernel_guarded`), and `toQ3Kernel` takes the global field as an
  explicit hypothesis. -/
  hasKernel : ∀ i j : Mode, E.fL i ≠ 0 → j ∈ F.PHset E →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  /-- FS's `ĝ`, mode-indexed. -/
  gHat : Mode → ℝ
  gHat_le : ∀ k : Mode, |gHat k| ≤ K₀ * E.aScat
  /-- FS's low-momentum tail `(2π)⁻³∫_{|k|<K_H^{-1}a^{-1}}k^{-2}dk ≤ K₀/(K_Ha)`
  (`eq:I2-integral`, the `k ∉ P_H` part of `lem:EstimateIntegral`). -/
  low_sum : E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ (excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k), 1 / ‖kmom k‖ ^ 2
    ≤ K₀ / (E.KH * E.aScat)
  /-- `(2π)⁻³∫_{P_H}k^{-4}dk ≤ K₀K_Ha`. -/
  sum_inv4 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖kmom k‖ ^ 4
    ≤ K₀ * E.KH * E.aScat
  /-- `(2π)⁻³∫_{P_H}k^{-6}dk ≤ K₀(K_Ha)³`. -/
  sum_inv6 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖kmom k‖ ^ 6
    ≤ K₀ * (E.KH * E.aScat) ^ 3
  /-- `(2π)⁻³∫_{P_H, |k|≤a^{-1}}k^{-3}dk ≤ K₀(1+log K_H)`. -/
  sum_inv3 : E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ (F.PHset E).filter (fun k => ‖kmom k‖ ≤ 1 / E.aScat), 1 / ‖kmom k‖ ^ 3
    ≤ K₀ * (1 + Real.log E.KH)
  /-- the periodic Green's-function identity of `lem:EstimateIntegral`. -/
  omega_lattice : |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ excited Mode, E.W1 k * gHat k / (2 * ‖kmom k‖ ^ 2)| ≤ K₀ * E.aScat ^ 2 / E.ell
  /-- the `R`-difference row of `lem:EstimateIntegral`. -/
  sum_diff : ∀ R : ℝ, E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖kmom k‖ ^ 2
    ≤ K₀ * E.aScat * (R / E.ell) ^ 4
  /-- FS's first-quantised `Q₂^ex` cancellation (`eq:Q3Cancels`, l. 3260 ff.). -/
  q2exLower : ∀ Ψ : F.H, 2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
    ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)
  /-- **K3's constant**: the Lipschitz constant of `α` on `P_H^q`
  (`AlphaLip.leaf` derives it from `W1_grad_le`, `tau_eq` and the smallness of
  `aK_H/(sℓ)`). -/
  Calpha : ℝ
  Calpha_nonneg : 0 ≤ Calpha
  /-- **K3** (FS design D7): `α` is Lipschitz on `P_H^q` with the geometric
  constant `𝓁·K_Ha` — the bound that repairs FS's `T₁` step. -/
  halpha_lip : ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |E.alpha p - E.alpha q| ≤ Calpha * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  /-- **K5's constant**: that of `lem:EstimateIntegral` (`eq:CompIntegrals-Final`). -/
  Cint : ℝ
  Cint_nonneg : 0 ≤ Cint
  /-- **K5**: `ρ_zŴ₁ω(0)` is `ℓ⁻³Σ_{P_H}Ŵ₁α` up to `ρa K_H⁻¹` (FS
  `eq:CompIntegrals-Final`, corrected: the full `K_H`). -/
  hintOne : |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
    ≤ Cint * E.rho * E.aScat * E.KH⁻¹
  /-- the chapter constant dominates the two analytic constants. -/
  K₀_alpha : Calpha ≤ K₀
  K₀_int : Cint ≤ K₀

end Work.BoseK15
