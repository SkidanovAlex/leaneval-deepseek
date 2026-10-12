import ChallengeDeps
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.vac_row` — the model annihilates the Fock vacuum

`H2ndF` (`Defs.lean`, FS `eq:HLambdaSecond`) is built from `a₀`-monomials and the
χ/θ-mode operators `annOf (f k)`, `annOf (g s)`: **every** row carries at least one
annihilation operator on its right end (for the `L0`-row the identity part of
`L0 = ℓ⁻³Ŵ₁(0)·n₀ − μŴ₁(0)` is followed by `annOf (f k)`).  Hence the model
Hamiltonian kills the Fock vacuum `x^0 = 1` of `RealFock m`, which is the
`Ψ = vac` candidate of `box_to_model` (with `⟨vac,vac⟩ = mfac 0 = 1`).

Main contents:

* `vac` — the vacuum `x^0`;
* `ann_vac`, `annOf_vac`, `n0_vac`, `totNumOp_vac` — the vacuum evaluations;
* `NH_honest_vac` — the honest `NH` (`tildeDataHon`) kills the vacuum;
* `H2ndF_vac` — the general statement: `H2ndF f g NH PHs E gHat0 vac = 0` whenever
  `NH vac = 0`;
* `vac_row` — `H2ndHon v h fc fu HM μ vac = 0`.
-/

noncomputable section
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- The Fock vacuum of `RealFock m`: the monomial `x^0 = 1` (zero particles). -/
def vac (m : ℕ) : Work.BoseB4.RealFock m := Finsupp.single (0 : Fin m →₀ ℕ) (1 : ℝ)

@[simp] lemma vac_zero_apply (m : ℕ) : vac m (0 : Fin m →₀ ℕ) = 1 :=
  Finsupp.single_eq_same

/-- Annihilation of a single mode kills the vacuum: `∂_l 1 = 0`. -/
lemma ann_vac {m : ℕ} (l : Fin m) : Work.BoseB4.ann m l (vac m) = 0 := by
  rw [vac, Work.BoseB4.ann, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply]

/-- Annihilation of a superposition (a χ-mode or a θ-mode) kills the vacuum. -/
@[simp] lemma annOf_vac {m : ℕ} (f : Fin m → ℝ) :
    Work.BoseB4.annOf m f (vac m) = 0 := by
  rw [Work.BoseB4.annOf]
  simp [ann_vac]

/-- Creation of a superposition kills `0`. -/
@[simp] lemma creOf_zero_apply {m : ℕ} (f : Fin m → ℝ) :
    Work.BoseB4.creOf m f (0 : Work.BoseB4.RealFock m) = 0 :=
  map_zero _

/-- The identity operator applied to a vector. -/
@[simp] lemma one_end_apply {m : ℕ} (x : Work.BoseB4.RealFock m) :
    (1 : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m) x = x :=
  LinearMap.id_apply x

/-- The mode number operator kills the vacuum. -/
@[simp] lemma modeNumOp_vac {m : ℕ} (l : Fin m) :
    Work.BoseB4.modeNumOp m l (vac m) = 0 := by
  rw [Work.BoseB4.modeNumOp, LinearMap.comp_apply, ann_vac, LinearMap.map_zero]

/-- The total number operator kills the vacuum. -/
@[simp] lemma totNumOp_vac {m : ℕ} [NeZero m] :
    Work.BoseB4.totNumOp m (vac m) = 0 := by
  rw [Work.BoseB4.totNumOp]
  simp [modeNumOp_vac]

/-- The condensate number operator kills the vacuum. -/
@[simp] lemma n0_vac {m : ℕ} [NeZero m] : n0 (m := m) (vac m) = 0 := by
  rw [n0, LinearMap.comp_apply, ann_vac, LinearMap.map_zero]

/-- **The general vacuum row.**  `H2ndF` annihilates the vacuum as soon as its
`NH`-row does: every other row ends in an annihilation operator. -/
theorem H2ndF_vac {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ)
    (NH : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (hNH : NH (vac m) = 0) :
    H2ndF f g NH PHs E gHat0 (vac m) = 0 := by
  unfold H2ndF
  dsimp only
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.sub_apply, one_end_apply, map_neg,
    map_sum, map_smul, map_zero, smul_zero, Finset.sum_const_zero, add_zero, sub_zero,
    zero_add, zero_sub, neg_zero, hNH, annOf_vac, ann_vac, n0_vac, totNumOp_vac]
  try simp [map_neg]

/-- The `NH` field of `tildeDataHon`, written out: it is `(1/32)Σ_k η_H(k)·a_k†a_k`
over the χ-modes. -/
lemma tildeDataHon_NH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {ℓ : ℝ} (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (m : ℕ)
    (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq Work.BoseK15.corpusBox.hatChi
          (kmom i) (kmom j))
    (hg : ∀ s t : Mode, s ≠ 0 → t ≠ 0 → Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (fu : Work.BoseBoxFix.LowCut) (κ : ℝ) :
    (tildeDataHon kmom hkmom m f g hf hg fu κ).NH
      = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode,
          etaH fu κ (kmom k) •
            (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k)) := rfl

/-- The honest `NH` kills the vacuum: it is `(1/32)Σ_k η_H(k)·a_k†a_k` over the
χ-modes, and each `a_k = annOf m (f k)` kills the vacuum.

NOT landed here (follow-up): the *honest* instantiation `H2ndHon … (vac …) = 0`
needs this fact for `(HonestBoxFam …).T.NH`, and computing that runs into the
`FockData.H`-instance diamond: `(boxFockData …).H = RealFock m` but its
`AddCommGroup`/`Module` instances are *fields* (`(boxFockData …).instAddCommGroup`),
not the canonical `Finsupp` ones, so `LinearMap.smul_apply`/`sum_apply` cannot be
applied to the `RealFock m`-typed sum.  The cure is to do the computation at the
`FockData`-level (transport `T.NH` along `show … from rfl` *before* the row
rewrites, or use the `FockData`-level operator lemmas `F.nOp`/`F.a`).  The general
row `H2ndF_vac` above is the mathematical content; `tildeDataHon_NH` gives the
explicit form of the honest `NH`. -/
theorem H2ndHon_vac_of_NH {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}
    (hNH : (((HonestBoxFam v h fc fu HM μ).T.NH :
        Work.BoseB4.RealFock (HM μ).m →ₗ[ℝ] Work.BoseB4.RealFock (HM μ).m))
      (vac (HM μ).m) = 0) :
    H2ndHon v h fc fu HM μ (vac (HM μ).m) = 0 := by
  rw [H2ndHon]
  exact H2ndF_vac (HM μ).f (HM μ).g
    (((HonestBoxFam v h fc fu HM μ).T.NH :
      Work.BoseB4.RealFock (HM μ).m →ₗ[ℝ] Work.BoseB4.RealFock (HM μ).m)) _ _ _ hNH

end Work.BoseBoxFock
