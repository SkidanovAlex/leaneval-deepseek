import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.DvApriori.sum_Icc_cast_eq_sum_range
import Submission.Work.BoseFixB2.Energy.gradeA_support_herm
import Submission.Work.BoseFixB2.Polar.boxFormB_smul
import Submission.Work.BoseFixB2.Polar.par_polarisation_hpol
import Submission.Work.BoseFixB2.Pot.potWordU_integrable
import Submission.Work.BoseFixB2.Recomb.boxFormB_polar_homog
import Submission.Work.BoseFixB2.Recomb.nPlusPow_secProj_sum
import Submission.Work.BoseFixB2.Sector.normB_secProj_sum
import Submission.Work.BoseFixB2.Sector.secProj_contDiff_symm
import Submission.Work.BoseFixB2.Sector.secProj_orthogonal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Recomb.recomb_clause` — FS §6, the recombination clause

FS `lem:LocMatrices` (`final_v2.tex` ll. 1365–1445), step (5): given the grading data
`(nn, A, ψv, Mw)` of a low box state `Φ`, and a unit vector `φ` supported in a window
`[n₀, n₀+Mw) ⊆ [0,nn]` of `Mw` consecutive indices with `⟨φ,Aφ⟩ < 0`, the *recombined*
state
`Φ' = Σ_i c_i·1_{n₊=i}Φ`,  `c_i = φ_i/‖1_{n₊=i}Φ‖`
has the same centred-box norm as `Φ`, word at most `⟨φ,Aφ⟩‖Φ‖²`, is spectrally confined
to `1_{[0,𝓜₂]}(n₊)` for every `𝓜₂ ≥ n₀ + Mw`, and has `⟨n₊⟩ ≥ n₀‖Φ'‖²`.

This file proves the clause as stated.  The mathematical content is the *grading
identity*: the box word is a quadratic form whose polar form is the matrix `𝒜`, so that
`wordB(Σ_i c_i 1_iΦ) = Σ_{i,j} c_i c_j 𝒜_{ij}`.  The polar form is genuinely bilinear
(the general "parallelogram + 2-homogeneity" statement is **false** — see
`Work.BoseFixB2.Polar.par_polarisation`; the missing homogeneity is supplied by the
decomposition of the box word into nonnegative pieces,
`Work.BoseFixB2.Recomb.jvn_polar_expansion`, applied to the four nonnegative summands of
FS `eq:DefT`).

## Structure of this file

* `normB_weighted_secProj`, `normB_pairing_weighted_secProj` — Pythagoras for a weighted
  combination of the `n₊`-sectors and the cross pairing of two such combinations;
* `wordB_polar_homog`, `kinFormB_polar_homog`, `boxFormB_polar_homog` — the polar
  homogeneity of the box word (from `fsT_polar_homog` by slot integration);
* `boxFormB_expansion` — the grading identity (via `par_polarisation_hpol`);
* the complex-to-real vector reduction, the `𝒜`-identification, the spectral
  confinement and the `n₊`-expectation of a windowed combination;
* `recomb_clause` — the assembly.
-/

noncomputable section
set_option maxHeartbeats 1000000
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB2.Recomb

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Pythagoras for weighted sector combinations -/

lemma continuous_secProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n k : ℕ} {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    Continuous (Work.BoseFixB2.secProj ℓ k Φ) := by
  rw [Work.BoseFixB2.secProj, Finset.sum_fn]
  exact continuous_finsetSum _ (fun S _ => Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦ)

lemma secProj_eq_zero_of_lt {ℓ : ℝ} {n k : ℕ} (hk : n < k) (Φ : X n → ℝ) :
    Work.BoseFixB2.secProj ℓ k Φ = 0 := by
  rw [Work.BoseFixB2.secProj]
  refine Finset.sum_eq_zero (fun S hS => ?_)
  obtain ⟨hSr, hSc⟩ := Finset.mem_powersetCard.mp hS
  have : S.card ≤ n := by
    simpa [Finset.card_range] using Finset.card_le_card hSr
  omega

/-- **Pythagoras for a weighted combination of the `n₊`-sectors.**  The weighted sectors
`c_k·1_{n₊=k}Φ` are pairwise orthogonal in `L²(abox n ℓ)`, so the box integral of the
square of their sum is the sum of the box integrals of the squares. -/
theorem integral_sq_weighted_secProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : X n → ℝ}
    (hΦc : Continuous Φ) (c : ℕ → ℝ) :
    (∫ x in abox n ℓ, (∑ k ∈ Finset.range (n + 1), c k * Work.BoseFixB2.secProj ℓ k Φ x) ^ 2)
      = ∑ k ∈ Finset.range (n + 1),
          (c k) ^ 2 * ∫ x in abox n ℓ, (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2 := by
  have hcont : ∀ k ∈ Finset.range (n + 1),
      Continuous (fun x : X n => c k * Work.BoseFixB2.secProj ℓ k Φ x) :=
    fun k _ => continuous_const.mul (continuous_secProj hℓ hΦc)
  have horth : ∀ k ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (n + 1), k ≠ l →
      ∫ x in abox n ℓ, (c k * Work.BoseFixB2.secProj ℓ k Φ x)
        * (c l * Work.BoseFixB2.secProj ℓ l Φ x) = 0 := by
    intro k _ l _ hkl
    rw [show (fun x : X n => (c k * Work.BoseFixB2.secProj ℓ k Φ x)
          * (c l * Work.BoseFixB2.secProj ℓ l Φ x))
        = fun x : X n => c k * c l * (Work.BoseFixB2.secProj ℓ k Φ x
            * Work.BoseFixB2.secProj ℓ l Φ x) from by funext x; ring]
    rw [MeasureTheory.integral_const_mul,
      Work.BoseFixB2.Sector.secProj_orthogonal hℓ hkl hΦc, mul_zero]
  have h := Work.BoseFixB2.Sector.integral_sq_finset_sum_of_orthogonal hℓ (Finset.range (n + 1))
    (fun k x => c k * Work.BoseFixB2.secProj ℓ k Φ x) hcont horth
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (fun x : X n => (c k * Work.BoseFixB2.secProj ℓ k Φ x) ^ 2)
      = fun x : X n => (c k) ^ 2 * (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2 from by
        funext x; ring,
    MeasureTheory.integral_const_mul]

/-- **The cross pairing of two weighted sector combinations.**  Since the sectors are
pairwise orthogonal, the box pairing of `Σ_k d_k1_kΦ` and `Σ_l e_l1_lΦ` reduces to the
diagonal `Σ_k d_k e_k ‖1_kΦ‖²`. -/
theorem integral_mul_weighted_secProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : X n → ℝ}
    (hΦc : Continuous Φ) (d e : ℕ → ℝ) :
    (∫ x in abox n ℓ,
        (∑ k ∈ Finset.range (n + 1), d k * Work.BoseFixB2.secProj ℓ k Φ x)
          * (∑ l ∈ Finset.range (n + 1), e l * Work.BoseFixB2.secProj ℓ l Φ x))
      = ∑ k ∈ Finset.range (n + 1),
          d k * e k * ∫ x in abox n ℓ, (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2 := by
  have hcont : ∀ k ∈ Finset.range (n + 1),
      Continuous (fun x : X n => d k * Work.BoseFixB2.secProj ℓ k Φ x)
        ∧ Continuous (fun x : X n => e k * Work.BoseFixB2.secProj ℓ k Φ x) :=
    fun k _ => ⟨continuous_const.mul (continuous_secProj hℓ hΦc),
      continuous_const.mul (continuous_secProj hℓ hΦc)⟩
  have hexp : (∫ x in abox n ℓ,
        (∑ k ∈ Finset.range (n + 1), d k * Work.BoseFixB2.secProj ℓ k Φ x)
          * (∑ l ∈ Finset.range (n + 1), e l * Work.BoseFixB2.secProj ℓ l Φ x))
      = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          ∫ x in abox n ℓ, (d k * Work.BoseFixB2.secProj ℓ k Φ x)
            * (e l * Work.BoseFixB2.secProj ℓ l Φ x) := by
    have hfun : (fun x : X n =>
          (∑ k ∈ Finset.range (n + 1), d k * Work.BoseFixB2.secProj ℓ k Φ x)
            * (∑ l ∈ Finset.range (n + 1), e l * Work.BoseFixB2.secProj ℓ l Φ x))
        = fun x : X n => ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
            (d k * Work.BoseFixB2.secProj ℓ k Φ x)
              * (e l * Work.BoseFixB2.secProj ℓ l Φ x) := by
      funext x
      rw [Finset.sum_mul_sum]
    rw [hfun]
    have hint : ∀ k ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (n + 1),
        IntegrableOn (fun x : X n => (d k * Work.BoseFixB2.secProj ℓ k Φ x)
          * (e l * Work.BoseFixB2.secProj ℓ l Φ x)) (abox n ℓ) volume :=
      fun k hk l hl => ContinuousOn.integrableOn_compact (abox_compact n hℓ)
        (((hcont k hk).1).mul (hcont l hl).2).continuousOn
    rw [MeasureTheory.integral_finsetSum _
      (fun k hk => MeasureTheory.integrable_finsetSum _ (fun l hl => hint k hk l hl))]
    exact Finset.sum_congr rfl (fun k hk =>
      MeasureTheory.integral_finsetSum _ (fun l hl => hint k hk l hl))
  rw [hexp]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.sum_eq_single k]
  · rw [show (fun x : X n => (d k * Work.BoseFixB2.secProj ℓ k Φ x)
        * (e k * Work.BoseFixB2.secProj ℓ k Φ x))
      = fun x : X n => d k * e k * (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2 from by
        funext x; ring,
      MeasureTheory.integral_const_mul]
  · intro l hl hlk
    rw [show (fun x : X n => (d k * Work.BoseFixB2.secProj ℓ k Φ x)
        * (e l * Work.BoseFixB2.secProj ℓ l Φ x))
      = fun x : X n => d k * e l * (Work.BoseFixB2.secProj ℓ k Φ x
          * Work.BoseFixB2.secProj ℓ l Φ x) from by funext x; ring,
      MeasureTheory.integral_const_mul,
      Work.BoseFixB2.Sector.secProj_orthogonal hℓ (Ne.symm hlk) hΦc, mul_zero]
  · intro hcon
    exact absurd hk hcon

/-- The `normB` form of Pythagoras for a weighted sector combination. -/
theorem normB_weighted_secProj {v : ℝ³ → ℝ} {μ : ℝ} {n : ℕ}
    (hℓ : 0 < Work.BoseFixB2.fsSide v μ) {Φ : X n → ℝ} (hΦc : Continuous Φ) (c : ℕ → ℝ) :
    Work.BoseBoxFix.normB v μ n
        (fun x => ∑ k ∈ Finset.range (n + 1),
          c k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x)
      = ∑ k ∈ Finset.range (n + 1),
          (c k) ^ 2 * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by
  simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, Work.BoseFixB2.fsSide] using
    integral_sq_weighted_secProj hℓ hΦc c

/-- The cross pairing in the `normB` vocabulary. -/
theorem normB_pairing_weighted_secProj {v : ℝ³ → ℝ} {μ : ℝ} {n : ℕ}
    (hℓ : 0 < Work.BoseFixB2.fsSide v μ) {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (d e : ℕ → ℝ) :
    (∫ x in abox n (Work.BoseFixB2.fsSide v μ),
        (∑ k ∈ Finset.range (n + 1),
            d k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x)
          * (∑ l ∈ Finset.range (n + 1),
            e l * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ x))
      = ∑ k ∈ Finset.range (n + 1),
          d k * e k * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by
  simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, Work.BoseFixB2.fsSide] using
    integral_mul_weighted_secProj hℓ hΦc d e

/-! ## 2. The grading identity: the box word expanded over a sector family -/

/-- The smooth `n`-body states, as a real vector space (the space on which the box word is
known to be a quadratic form: `boxFormB_parallelogram` and `boxFormB_smul` carry smoothness
hypotheses, and the *polar* homogeneity `boxFormB_polar_homog` is the missing ingredient of
the general polarisation theorem `Work.BoseFixB2.Polar.par_polarisation`). -/
def SmoothBox (n : ℕ) : Submodule ℝ (Submission.BoseGases.X n → ℝ) where
  carrier := {Φ | ContDiff ℝ (⊤ : ℕ∞) Φ}
  zero_mem' := by
    show ContDiff ℝ (⊤ : ℕ∞) (0 : Submission.BoseGases.X n → ℝ)
    exact contDiff_const
  add_mem' := by
    intro a b ha hb
    show ContDiff ℝ (⊤ : ℕ∞) (a + b)
    have ha' : ContDiff ℝ (⊤ : ℕ∞) a := by simpa using ha
    have hb' : ContDiff ℝ (⊤ : ℕ∞) b := by simpa using hb
    exact ha'.add hb'
  smul_mem' := by
    intro c x hx
    show ContDiff ℝ (⊤ : ℕ∞) (c • x)
    have hx' : ContDiff ℝ (⊤ : ℕ∞) x := by simpa using hx
    exact ContDiff.const_smul c hx'

lemma SmoothBox.mem_mk {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (h : ContDiff ℝ (⊤ : ℕ∞) Φ) : Φ ∈ SmoothBox n := by
  change ContDiff ℝ (⊤ : ℕ∞) Φ
  exact h

lemma SmoothBox.contDiff {n : ℕ} (x : SmoothBox n) :
    ContDiff ℝ (⊤ : ℕ∞) (x : Submission.BoseGases.X n → ℝ) := by
  change (x : Submission.BoseGases.X n → ℝ) ∈ SmoothBox n
  exact x.2

lemma SmoothBox.coe_add' {n : ℕ} (x y : SmoothBox n) :
    ((x + y : SmoothBox n) : Submission.BoseGases.X n → ℝ)
      = fun z => (x : Submission.BoseGases.X n → ℝ) z
        + (y : Submission.BoseGases.X n → ℝ) z := by
  funext z
  simp only [Submodule.coe_add, Pi.add_apply]

lemma SmoothBox.coe_sub' {n : ℕ} (x y : SmoothBox n) :
    ((x - y : SmoothBox n) : Submission.BoseGases.X n → ℝ)
      = fun z => (x : Submission.BoseGases.X n → ℝ) z
        - (y : Submission.BoseGases.X n → ℝ) z := by
  funext z
  simp only [Submodule.coe_sub, Pi.sub_apply]

lemma SmoothBox.coe_smul' {n : ℕ} (c : ℝ) (x : SmoothBox n) :
    ((c • x : SmoothBox n) : Submission.BoseGases.X n → ℝ)
      = fun z => c * (x : Submission.BoseGases.X n → ℝ) z := by
  funext z
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]

lemma SmoothBox.coe_sum' {n : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (F : ι → SmoothBox n) :
    ((∑ i ∈ s, c i • F i : SmoothBox n) : Submission.BoseGases.X n → ℝ)
      = fun z => ∑ i ∈ s, c i * (F i : Submission.BoseGases.X n → ℝ) z := by
  funext z
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- **The box word expanded over a smooth family**: the polarisation identity for the
box-restricted word, in the form in which the grading of FS §6 uses it. -/
theorem boxFormB_expansion {n : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ d s εT b : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 < εT) (hb : 0 < b)
    (hw : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      (Submission.BoseGases.abox n ℓ))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (Ψ : ι → Submission.BoseGases.X n → ℝ)
    (hΨ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Ψ i)) :
    Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => ∑ i, c i * Ψ i x)
      = ∑ i, ∑ j, c i * c j * ((Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b
            (fun x => Ψ i x + Ψ j x)
          - Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => Ψ i x - Ψ j x)) / 4) := by
  set Q : SmoothBox n → ℝ :=
    fun F => Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (F : Submission.BoseGases.X n → ℝ)
    with hQ
  have hpar : ∀ x y : SmoothBox n, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y := by
    intro x y
    have h := Work.BoseFixB2.Polar.boxFormB_parallelogram (n := n)
      (Φ := (x : Submission.BoseGases.X n → ℝ)) (Ψ := (y : Submission.BoseGases.X n → ℝ))
      hℓ hd hs hεT hb (SmoothBox.contDiff x) (SmoothBox.contDiff y) hw
    simp only [hQ, SmoothBox.coe_add', SmoothBox.coe_sub', Subtype.coe_mk]
    exact h
  have hhom : ∀ (t : ℝ) (x : SmoothBox n), Q (t • x) = t ^ 2 * Q x := by
    intro t x
    have h := Work.BoseFixB2.Polar.boxFormB_smul (v := v) (g := g) (ℓ := ℓ) (μ := μ)
      (d := d) (s := s) (εT := εT) (b := b) (t := t) hℓ (SmoothBox.contDiff x)
    simp only [hQ, SmoothBox.coe_smul', Subtype.coe_mk]
    exact h
  have hpol : ∀ (t : ℝ) (x y : SmoothBox n), Q (t • x + y) - Q (t • x - y)
      = t * (Q (x + y) - Q (x - y)) := by
    intro t x y
    have h := boxFormB_polar_homog (v := v) (g := g) (ℓ := ℓ) (μ := μ)
      (d := d) (s := s) (εT := εT) (b := b) (t := t) hℓ hd hs hεT hb
      (SmoothBox.contDiff x) (SmoothBox.contDiff y) hw
    simp only [hQ, SmoothBox.coe_add', SmoothBox.coe_sub', SmoothBox.coe_smul', Subtype.coe_mk]
    exact h
  have key := Work.BoseFixB2.Polar.par_polarisation_hpol (V := SmoothBox n) Q hpar hhom hpol c
    (fun i => (⟨Ψ i, SmoothBox.mem_mk (hΨ i)⟩ : SmoothBox n))
  simp only [hQ] at key
  have hcoe : ((∑ i, c i • (⟨Ψ i, SmoothBox.mem_mk (hΨ i)⟩ : SmoothBox n) : SmoothBox n)
        : Submission.BoseGases.X n → ℝ) = fun x => ∑ i, c i * Ψ i x :=
    SmoothBox.coe_sum' Finset.univ c (fun i => (⟨Ψ i, SmoothBox.mem_mk (hΨ i)⟩ : SmoothBox n))
  rw [hcoe] at key
  exact key.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
    simp only [SmoothBox.coe_add', SmoothBox.coe_sub', Subtype.coe_mk])))

/-- **The grading identity for FS's box word**: `wordB(Σ_i c_iΦ_i) = Σ_{i,j} c_i c_j
polB(Φ_i,Φ_j)`, i.e. `polB` is the bilinear form of the box word. -/
theorem wordB_expansion {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hw : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
          (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (Ψ : ι → Submission.BoseGases.X n → ℝ)
    (hΨ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Ψ i)) :
    Work.BoseBoxFix.wordB v h μ n (fun x => ∑ i, c i * Ψ i x)
      = ∑ i, ∑ j, c i * c j * Work.BoseFixB2.polB v h μ n (Ψ i) (Ψ j) := by
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
    have h := Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 6) ht
    simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using h
  have hs : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := by
    have h := Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 1) ht
    simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using h
  have heT : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
    have h := Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 23 / 4) ht
    simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams] using h
  have hb : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b := by
    simpa only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.bValue] using
      (by norm_num : (0 : ℝ) < 1 / 16)
  have hℓ : 0 < Work.BoseFixB2.fsSide v μ := by
    simpa only [Work.BoseFixB2.fsSide] using Work.BoseBox.sideAt_pos hμ hav
  have h := boxFormB_expansion (v := v) (g := Submission.BoseGases.g0 v h)
    (ℓ := Work.BoseFixB2.fsSide v μ) (μ := μ)
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
    (εT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b) hℓ hd hs heT hb hw c Ψ hΨ
  simpa only [Work.BoseBoxFix.wordB, Work.BoseFixB2.polB, Work.BoseFixB2.fsSide] using h

/-- **The grading identity for FS's box word**, in the `range`-sum form used below. -/
theorem wordB_expansion_range {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hw : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
          (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ)))
    {j : ℕ} (c : ℕ → ℝ) (Ψ : ℕ → Submission.BoseGases.X n → ℝ)
    (hΨ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k)) :
    Work.BoseBoxFix.wordB v h μ n (fun x => ∑ k ∈ Finset.range (j + 1), c k * Ψ k x)
      = ∑ k ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1),
          c k * c l * Work.BoseFixB2.polB v h μ n (Ψ k) (Ψ l) := by
  have hwexp := wordB_expansion (v := v) (h := h) (μ := μ) (n := n) hμ hav hw (ι := Fin (j + 1))
    (fun k : Fin (j + 1) => c k) (fun k : Fin (j + 1) => Ψ k) (fun k => hΨ k)
  rw [show (fun x => ∑ k ∈ Finset.range (j + 1), c k * Ψ k x)
      = (fun x => ∑ i : Fin (j + 1), c i * Ψ i x) from by
    funext x
    exact (Fin.sum_univ_eq_sum_range (fun k => c k * Ψ k x) (j + 1)).symm]
  rw [hwexp]
  rw [show (∑ i : Fin (j + 1), ∑ l : Fin (j + 1),
        c i * c l * Work.BoseFixB2.polB v h μ n (Ψ i) (Ψ l))
      = (∑ i ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1),
          c i * c l * Work.BoseFixB2.polB v h μ n (Ψ i) (Ψ l)) from by
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ∑ l : Fin (j + 1), c i * c l * Work.BoseFixB2.polB v h μ n (Ψ i) (Ψ l))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Fin.sum_univ_eq_sum_range
      (fun l => c k * c l * Work.BoseFixB2.polB v h μ n (Ψ k) (Ψ l)) (j + 1)]

/-! ## 3. The complex-to-real reduction of the window vector

FS's window vector `φ` is complex, but the recombined state is real.  The reduction uses that
the matrix `𝒜` is real-valued: the quadratic form then splits into its real and imaginary
parts, and one of the two carries a value at least as negative as the whole. -/

/-- The real part of a finite sum of complex numbers. -/
lemma re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum Complex.reAddGroupHom f s

lemma re_double_sum {ι : Type*} (s : Finset ι) (f : ι → ι → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, f i j).re = ∑ i ∈ s, ∑ j ∈ s, (f i j).re := by
  rw [re_sum]
  exact Finset.sum_congr rfl (fun i _ => re_sum s (f i))

/-- **The `(i,j)` summand of a quadratic form with a real-valued matrix.** -/
lemma re_star_mul_ofReal_mul (r : ℝ) (u v : ℂ) :
    (star u * ((r : ℝ) : ℂ) * v).re = r * (u.re * v.re + u.im * v.im) := by
  rw [show star u * ((r : ℝ) : ℂ) * v = ((r : ℝ) : ℂ) * (star u * v) by ring,
    Complex.mul_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The quadratic form of a real-valued matrix splits into its real and imaginary parts. -/
lemma qform_split_re_im {A : ℤ → ℤ → ℂ} {B : Finset ℤ} (hAim : ∀ i j, (A i j).im = 0)
    (z : ℤ → ℂ) :
    qform A B z z
      = qform A B (fun j => ((z j).re : ℂ)) (fun j => ((z j).re : ℂ))
        + qform A B (fun j => ((z j).im : ℂ)) (fun j => ((z j).im : ℂ)) := by
  have hA : ∀ i j, A i j = (((A i j).re : ℝ) : ℂ) := by
    intro i j
    refine Complex.ext ?_ ?_
    · simp
    · simpa using hAim i j
  have hterm : ∀ i j, (star (z i) * A i j * z j).re
      = (A i j).re * (z i).re * (z j).re + (A i j).re * (z i).im * (z j).im := by
    intro i j
    rw [hA i j, re_star_mul_ofReal_mul]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hterma : ∀ i j, (star (((z i).re : ℝ) : ℂ) * A i j * (((z j).re : ℝ) : ℂ)).re
      = (A i j).re * (z i).re * (z j).re := by
    intro i j
    rw [hA i j, re_star_mul_ofReal_mul]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have htermb : ∀ i j, (star (((z i).im : ℝ) : ℂ) * A i j * (((z j).im : ℝ) : ℂ)).re
      = (A i j).re * (z i).im * (z j).im := by
    intro i j
    rw [hA i j, re_star_mul_ofReal_mul]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h1 : qform A B z z
      = (∑ i ∈ B, ∑ j ∈ B, (A i j).re * (z i).re * (z j).re)
        + (∑ i ∈ B, ∑ j ∈ B, (A i j).re * (z i).im * (z j).im) := by
    unfold Work.UBBInputs3.qform
    rw [re_double_sum]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)]
    rw [Finset.sum_add_distrib]
  have h2 : qform A B (fun j => ((z j).re : ℂ)) (fun j => ((z j).re : ℂ))
      = ∑ i ∈ B, ∑ j ∈ B, (A i j).re * (z i).re * (z j).re := by
    unfold Work.UBBInputs3.qform
    rw [re_double_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterma i j))
  have h3 : qform A B (fun j => ((z j).im : ℂ)) (fun j => ((z j).im : ℂ))
      = ∑ i ∈ B, ∑ j ∈ B, (A i j).re * (z i).im * (z j).im := by
    unfold Work.UBBInputs3.qform
    rw [re_double_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => htermb i j))
  rw [h1, h2, h3]

/-- The squared norm of a complex vector splits into its real and imaginary parts. -/
lemma normSq_split_re_im {B : Finset ℤ} (z : ℤ → ℂ) :
    normSq B z
      = normSq B (fun j => ((z j).re : ℂ)) + normSq B (fun j => ((z j).im : ℂ)) := by
  unfold Work.UBBInputs3.normSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 : ‖(((z j).re : ℝ) : ℂ)‖ ^ 2 = (z j).re ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  have h2 : ‖(((z j).im : ℝ) : ℂ)‖ ^ 2 = (z j).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    ring
  rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]
  ring

lemma normSq_nonneg' {B : Finset ℤ} (z : ℤ → ℂ) : 0 ≤ normSq B z :=
  Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- Scaling by a real number scales the squared norm. -/
lemma normSq_smul_real {B : Finset ℤ} (c : ℝ) (φ : ℤ → ℂ) :
    normSq B (fun j => ((c : ℝ) : ℂ) * φ j) = c ^ 2 * normSq B φ := by
  unfold Work.UBBInputs3.normSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal,
    ← Complex.sq_norm (φ j)]
  ring

/-- Scaling by a real number scales the quadratic form. -/
lemma qform_smul_real {A : ℤ → ℤ → ℂ} {B : Finset ℤ} (c : ℝ) (φ : ℤ → ℂ) :
    qform A B (fun j => ((c : ℝ) : ℂ) * φ j) (fun j => ((c : ℝ) : ℂ) * φ j)
      = c ^ 2 * qform A B φ φ := by
  have hL : qform A B (fun j => ((c : ℝ) : ℂ) * φ j) (fun j => ((c : ℝ) : ℂ) * φ j)
      = ∑ i ∈ B, ∑ j ∈ B,
          (star (((c : ℝ) : ℂ) * φ i) * A i j * (((c : ℝ) : ℂ) * φ j)).re := by
    unfold Work.UBBInputs3.qform
    exact re_double_sum B
      (fun i j => star (((c : ℝ) : ℂ) * φ i) * A i j * (((c : ℝ) : ℂ) * φ j))
  have hR : qform A B φ φ = ∑ i ∈ B, ∑ j ∈ B, (star (φ i) * A i j * φ j).re := by
    unfold Work.UBBInputs3.qform
    exact re_double_sum B (fun i j => star (φ i) * A i j * φ j)
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcs : star (((c : ℝ) : ℂ)) = (((c : ℝ) : ℂ)) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [show star (((c : ℝ) : ℂ) * φ i) * A i j * (((c : ℝ) : ℂ) * φ j)
      = ((c * c : ℝ) : ℂ) * (star (φ i) * A i j * φ j) from by
    rw [star_mul, hcs]
    push_cast
    ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A vector of vanishing squared norm vanishes on its index set. -/
lemma eq_zero_of_normSq_eq_zero {B : Finset ℤ} {f : ℤ → ℂ} (h : normSq B f = 0) {j : ℤ}
    (hj : j ∈ B) : f j = 0 := by
  have h2 : ‖f j‖ ^ 2 ≤ normSq B f :=
    Finset.single_le_sum (f := fun k => ‖f k‖ ^ 2) (fun k _ => sq_nonneg _) hj
  have h3 : ‖f j‖ ^ 2 = 0 := le_antisymm (by rw [h] at h2; exact h2) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h3)

/-- A vector of vanishing squared norm has vanishing quadratic form. -/
lemma qform_eq_zero_of_normSq_eq_zero {A : ℤ → ℤ → ℂ} {B : Finset ℤ} {f : ℤ → ℂ}
    (h : normSq B f = 0) : qform A B f f = 0 := by
  have h0 : ∀ j ∈ B, f j = 0 := fun j hj => eq_zero_of_normSq_eq_zero h hj
  unfold Work.UBBInputs3.qform
  rw [re_double_sum]
  refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => ?_))
  rw [h0 i hi, h0 j hj]
  simp

lemma one_div_sqrt_sq {t : ℝ} (ht : 0 < t) : (1 / Real.sqrt t) ^ 2 = 1 / t := by
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt ht)]

/-- The quadratic form is unchanged by zeroing a vector on the indices where the matrix
vanishes. -/
lemma qform_eq_of_eqOff {A : ℤ → ℤ → ℂ} {B : Finset ℤ} {P : ℤ → Prop}
    (hAz₁ : ∀ i j, P i → A i j = 0) (hAz₂ : ∀ i j, P j → A i j = 0)
    {y z : ℤ → ℂ} (h : ∀ j, ¬ P j → y j = z j) :
    qform A B y y = qform A B z z := by
  unfold Work.UBBInputs3.qform
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hi : P i
  · rw [hAz₁ i j hi]
    simp
  · by_cases hj : P j
    · rw [hAz₂ i j hj]
      simp
    · rw [h i hi, h j hj]

/-- The box norm of the zero state vanishes. -/
lemma normB_zero (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ) :
    Work.BoseBoxFix.normB v μ n (0 : Submission.BoseGases.X n → ℝ) = 0 := by
  rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  simp only [Pi.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), MeasureTheory.integral_zero]

/-- **The complex-to-real reduction.**  For a real-valued matrix `A` and a vector `z` of
squared norm at most `1` whose quadratic form is negative, there is a *real* unit vector `x`
whose quadratic form is no larger, and which is supported where `z` is. -/
theorem exists_real_unit_of_neg {A : ℤ → ℤ → ℂ} {B : Finset ℤ} (hAim : ∀ i j, (A i j).im = 0)
    {z : ℤ → ℂ} (hz : normSq B z ≤ 1) (hneg : qform A B z z < 0) :
    ∃ x : ℤ → ℂ, (∀ j, (x j).im = 0) ∧ (∀ j, x j ≠ 0 → z j ≠ 0) ∧
      normSq B x = 1 ∧ qform A B x x ≤ qform A B z z := by
  have hz0 : normSq B z ≠ 0 := by
    intro h0
    rw [qform_eq_zero_of_normSq_eq_zero h0] at hneg
    exact lt_irrefl 0 hneg
  set a : ℤ → ℂ := fun j => (((z j).re : ℝ) : ℂ) with ha
  set b : ℤ → ℂ := fun j => (((z j).im : ℝ) : ℂ) with hb
  have hsplit : qform A B z z = qform A B a a + qform A B b b := qform_split_re_im hAim z
  have hnsplit : normSq B z = normSq B a + normSq B b := normSq_split_re_im z
  set α := normSq B a with hα
  set β := normSq B b with hβ
  have hαβ : α + β = normSq B z := hnsplit.symm
  have hα0 : 0 ≤ α := normSq_nonneg' a
  have hβ0 : 0 ≤ β := normSq_nonneg' b
  have htpos : 0 < α + β := lt_of_le_of_ne (add_nonneg hα0 hβ0) (by rw [hαβ]; exact Ne.symm hz0)
  have ht1 : α + β ≤ 1 := by rw [hαβ]; exact hz
  have hmem_a : ∀ j, a j ≠ 0 → z j ≠ 0 := by
    intro j hj hzj
    exact hj (by simp [ha, hzj])
  have hmem_b : ∀ j, b j ≠ 0 → z j ≠ 0 := by
    intro j hj hzj
    exact hj (by simp [hb, hzj])
  rcases eq_or_ne α 0 with hαz | hαz
  · -- the imaginary part carries the negativity
    have hQa0 : qform A B a a = 0 :=
      qform_eq_zero_of_normSq_eq_zero (A := A) (by rw [← hα]; exact hαz)
    have hL : qform A B z z = qform A B b b := by rw [hsplit, hQa0, zero_add]
    have hL' : qform A B b b = qform A B z z := hL.symm
    have hβt : β = normSq B z := by rw [← hαβ, hαz, zero_add]
    have hβpos : 0 < β := by
      rw [hβt]
      exact lt_of_le_of_ne (normSq_nonneg' z) (Ne.symm hz0)
    have hβle1 : β ≤ 1 := by rw [hβt]; exact hz
    refine ⟨fun j => ((1 / Real.sqrt β : ℝ) : ℂ) * b j, ?_, ?_, ?_, ?_⟩
    · intro j; simp [hb]
    · intro j hj
      exact hmem_b j (fun h0 => hj (by simp [h0]))
    · rw [normSq_smul_real, ← hβ, one_div_sqrt_sq hβpos, one_div,
        inv_mul_cancel₀ (ne_of_gt hβpos)]
    · rw [qform_smul_real, one_div_sqrt_sq hβpos, hL',
        show (1 / β) * qform A B z z = qform A B z z / β by ring]
      rw [div_le_iff₀ hβpos]
      nlinarith [hneg, hβle1]
  · rcases eq_or_ne β 0 with hβz | hβz
    · -- the real part carries the negativity
      have hQb0 : qform A B b b = 0 :=
        qform_eq_zero_of_normSq_eq_zero (A := A) (by rw [← hβ]; exact hβz)
      have hL : qform A B z z = qform A B a a := by rw [hsplit, hQb0, add_zero]
      have hL' : qform A B a a = qform A B z z := hL.symm
      have hαt : α = normSq B z := by rw [← hαβ, hβz, add_zero]
      have hαpos : 0 < α := by
        rw [hαt]
        exact lt_of_le_of_ne (normSq_nonneg' z) (Ne.symm hz0)
      have hαle1 : α ≤ 1 := by rw [hαt]; exact hz
      refine ⟨fun j => ((1 / Real.sqrt α : ℝ) : ℂ) * a j, ?_, ?_, ?_, ?_⟩
      · intro j; simp [ha]
      · intro j hj
        exact hmem_a j (fun h0 => hj (by simp [h0]))
      · rw [normSq_smul_real, ← hα, one_div_sqrt_sq hαpos, one_div,
          inv_mul_cancel₀ (ne_of_gt hαpos)]
      · rw [qform_smul_real, one_div_sqrt_sq hαpos, hL',
          show (1 / α) * qform A B z z = qform A B z z / α by ring]
        rw [div_le_iff₀ hαpos]
        nlinarith [hneg, hαle1]
    · -- both parts are nondegenerate: take the more negative one
      have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαz)
      have hβpos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβz)
      have hmin : min (qform A B a a / α) (qform A B b b / β) ≤ qform A B z z / (α + β) := by
        have havg : (α / (α + β)) * (qform A B a a / α)
            + (β / (α + β)) * (qform A B b b / β) = qform A B z z / (α + β) := by
          rw [hsplit]
          field_simp
        rw [← havg]
        have hw1 : 0 ≤ α / (α + β) := div_nonneg (le_of_lt hαpos) (le_of_lt htpos)
        have hw2 : 0 ≤ β / (α + β) := div_nonneg (le_of_lt hβpos) (le_of_lt htpos)
        have hw3 : α / (α + β) + β / (α + β) = 1 := by field_simp
        have h5 : α / (α + β) * min (qform A B a a / α) (qform A B b b / β)
            ≤ α / (α + β) * (qform A B a a / α) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hw1
        have h6 : β / (α + β) * min (qform A B a a / α) (qform A B b b / β)
            ≤ β / (α + β) * (qform A B b b / β) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hw2
        have h7 : α / (α + β) * min (qform A B a a / α) (qform A B b b / β)
            + β / (α + β) * min (qform A B a a / α) (qform A B b b / β)
            = min (qform A B a a / α) (qform A B b b / β) := by
          rw [← add_mul, hw3, one_mul]
        linarith [h5, h6, h7]
      have hle0 : qform A B z z / (α + β) ≤ qform A B z z := by
        rw [div_le_iff₀ htpos]
        nlinarith [hneg, ht1]
      rcases le_total (qform A B a a / α) (qform A B b b / β) with hle | hle
      · have hbound : qform A B a a / α ≤ qform A B z z := by
          refine le_trans ?_ hle0
          rw [← min_eq_left hle]
          exact hmin
        refine ⟨fun j => ((1 / Real.sqrt α : ℝ) : ℂ) * a j, ?_, ?_, ?_, ?_⟩
        · intro j; simp [ha]
        · intro j hj
          exact hmem_a j (fun h0 => hj (by simp [h0]))
        · rw [normSq_smul_real, ← hα, one_div_sqrt_sq hαpos, one_div,
            inv_mul_cancel₀ (ne_of_gt hαpos)]
        · rw [qform_smul_real, one_div_sqrt_sq hαpos,
            show (1 / α) * qform A B a a = qform A B a a / α by ring]
          exact hbound
      · have hbound : qform A B b b / β ≤ qform A B z z := by
          refine le_trans ?_ hle0
          rw [← min_eq_right hle]
          exact hmin
        refine ⟨fun j => ((1 / Real.sqrt β : ℝ) : ℂ) * b j, ?_, ?_, ?_, ?_⟩
        · intro j; simp [hb]
        · intro j hj
          exact hmem_b j (fun h0 => hj (by simp [h0]))
        · rw [normSq_smul_real, ← hβ, one_div_sqrt_sq hβpos, one_div,
            inv_mul_cancel₀ (ne_of_gt hβpos)]
        · rw [qform_smul_real, one_div_sqrt_sq hβpos,
            show (1 / β) * qform A B b b = qform A B b b / β by ring]
          exact hbound

/-! ## 4. The spectral confinement and the `n₊`-expectation of a windowed combination -/

section Window

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}

/-- A sum over `iRange N` with vanishing terms outside the sector range is a sum over
`range (n+1)`. -/
lemma sum_iRange_eq_sum_range {N : ℕ} (hN : n + 1 ≤ N) (f : ℤ → ℝ)
    (hf : ∀ i ∈ Work.UBBInputs3.iRange N, i ∉ Finset.Icc (0 : ℤ) (n : ℤ) → f i = 0) :
    (∑ i ∈ Work.UBBInputs3.iRange N, f i)
      = ∑ k ∈ Finset.range (n + 1), f (k : ℤ) := by
  have h1 : (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), f i)
      = ∑ k ∈ Finset.range (n + 1), f (k : ℤ) := by
    simpa using Work.BoseFixB2.DvApriori.sum_Icc_cast_eq_sum_range (f := f) 0 n
  have h2 : (∑ i ∈ Finset.Icc (0 : ℤ) (n : ℤ), f i) = ∑ i ∈ Work.UBBInputs3.iRange N, f i := by
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Work.UBBInputs3.iRange, Finset.mem_Icc]
      refine ⟨hi.1, ?_⟩
      have hN' : (n : ℤ) + 1 ≤ (N : ℤ) := by exact_mod_cast hN
      linarith [hi.2]
    · intro i hi hin
      exact hf i hi hin
  rw [← h2, h1]

/-- **The spectral confinement of a windowed sector combination.**  If the coefficients
are supported on indices at most `𝓜`, the combination is in the `n₊ ≤ 𝓜` spectral
subspace (all-moments form). -/
theorem spectralNPlusLe_weighted (hℓ : 0 < Work.BoseFixB2.fsSide v μ) {Φ : X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (cc : ℕ → ℝ) {𝓜 : ℝ} (h𝓜 : 0 ≤ 𝓜)
    (hwin : ∀ k ∈ Finset.range (n + 1), cc k ≠ 0 → (k : ℝ) ≤ 𝓜) :
    Work.BoseBox.SpectralNPlusLe (Work.BoseFixB2.fsSide v μ) 𝓜
      (fun x => ∑ k ∈ Finset.range (n + 1),
        cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x) := by
  intro m
  have hΦc : Continuous Φ := hΦ.continuous
  have hpow := nPlusPow_secProj_sum (ℓ := Work.BoseFixB2.fsSide v μ) hℓ hΦ cc m
  rw [show Work.BoseBox.nPlusPow (Work.BoseFixB2.fsSide v μ) n m
        (fun x => ∑ k ∈ Finset.range (n + 1),
          cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x)
      = fun x => ∑ k ∈ Finset.range (n + 1),
          (cc k * (k : ℝ) ^ m) * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x
      from hpow]
  rw [normB_pairing_weighted_secProj (v := v) (μ := μ) (n := n) hℓ hΦc
    (fun k => cc k * (k : ℝ) ^ m) cc]
  rw [show (∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
        (fun x => ∑ k ∈ Finset.range (n + 1),
          cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x) x ^ 2)
      = ∑ k ∈ Finset.range (n + 1),
          (cc k) ^ 2 * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
      from normB_weighted_secProj hℓ hΦc cc]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  by_cases hk0 : cc k = 0
  · rw [hk0]; simp
  · have hk𝓜 : (k : ℝ) ≤ 𝓜 := hwin k hk hk0
    have hk0' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpowk : (k : ℝ) ^ m ≤ 𝓜 ^ m := pow_le_pow_left₀ hk0' hk𝓜 m
    have hS : 0 ≤ Work.BoseBoxFix.normB v μ n
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg (fun z => sq_nonneg _)
    have hcc2 : 0 ≤ (cc k) ^ 2 := sq_nonneg _
    calc (cc k * (k : ℝ) ^ m) * cc k
          * Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
        = ((cc k) ^ 2 * (k : ℝ) ^ m) * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by ring
      _ ≤ ((cc k) ^ 2 * 𝓜 ^ m) * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by
          refine mul_le_mul_of_nonneg_right ?_ hS
          exact mul_le_mul_of_nonneg_left hpowk hcc2
      _ = 𝓜 ^ m * ((cc k) ^ 2 * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)) := by ring

/-- **The `n₊`-expectation of a windowed sector combination** is at least `n₀‖Φ'‖²` when
the coefficients are supported on indices at least `n₀`. -/
theorem cnPlus_weighted (hℓ : 0 < Work.BoseFixB2.fsSide v μ) {Φ : X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (cc : ℕ → ℝ) {n₀ : ℝ}
    (hwin : ∀ k ∈ Finset.range (n + 1), cc k ≠ 0 → n₀ ≤ (k : ℝ)) :
    n₀ * Work.BoseBoxFix.normB v μ n
        (fun x => ∑ k ∈ Finset.range (n + 1),
          cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x)
      ≤ Submission.BoseGases.cnPlus (Work.BoseFixB2.fsSide v μ)
          (fun x => ∑ k ∈ Finset.range (n + 1),
            cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hΦ'c : Continuous (fun x => ∑ k ∈ Finset.range (n + 1),
      cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x) :=
    continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_secProj hℓ hΦc))
  rw [Work.UBBInputs4.cnPlus_eq_qform_nPlus hℓ hΦ'c]
  have h1 : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
        (∑ i, Submission.BoseGases.aQ (Work.BoseFixB2.fsSide v μ) i
          (fun y => ∑ k ∈ Finset.range (n + 1),
            cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ y) x)
          * (fun y => ∑ k ∈ Finset.range (n + 1),
            cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ y) x)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
        Work.BoseBox.nPlusPow (Work.BoseFixB2.fsSide v μ) n 1
          (fun y => ∑ k ∈ Finset.range (n + 1),
            cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ y) x
          * (fun y => ∑ k ∈ Finset.range (n + 1),
            cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ y) x := rfl
  rw [h1, nPlusPow_secProj_sum (ℓ := Work.BoseFixB2.fsSide v μ) hℓ hΦ cc 1]
  rw [normB_pairing_weighted_secProj (v := v) (μ := μ) (n := n) hℓ hΦc
    (fun k => cc k * (k : ℝ) ^ 1) cc]
  rw [normB_weighted_secProj (v := v) (μ := μ) (n := n) hℓ hΦc cc]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  by_cases hk0 : cc k = 0
  · rw [hk0]; simp
  · have hS : 0 ≤ Work.BoseBoxFix.normB v μ n
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg (fun z => sq_nonneg _)
    have hcc2 : 0 ≤ (cc k) ^ 2 := sq_nonneg _
    calc n₀ * ((cc k) ^ 2 * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ))
        = ((cc k) ^ 2 * n₀) * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by ring
      _ ≤ ((cc k) ^ 2 * (k : ℝ)) * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by
          refine mul_le_mul_of_nonneg_right ?_ hS
          exact mul_le_mul_of_nonneg_left (hwin k hk hk0) hcc2
      _ = (cc k * (k : ℝ) ^ 1) * cc k * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by ring

end Window

/-! ## 5. The identification of the grading identity with `⟨φ,𝓐φ⟩` -/

section Identification

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}

/-- `vecZ` at a natural index in range is the sector. -/
lemma vecZ_natCast {ℓ : ℝ} {Φ : X n → ℝ} {k : ℕ} (hk : k ≤ n) :
    Work.BoseFixB2.vecZ ℓ Φ (k : ℤ) = Work.BoseFixB2.secProj ℓ k Φ := by
  have h : (0 : ℤ) ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ) :=
    ⟨Int.natCast_nonneg k, by exact_mod_cast hk⟩
  rw [Work.BoseFixB2.vecZ, if_pos h]
  exact congrArg (fun m => Work.BoseFixB2.secProj ℓ m Φ) (Int.toNat_natCast k)

lemma normB_zero_vecZ {ℓ : ℝ} {Φ : X n → ℝ} {j : ℤ}
    (hj : j ∉ Finset.Icc (0 : ℤ) (n : ℤ)) :
    Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ j) = 0 := by
  have hvec0 : Work.BoseFixB2.vecZ ℓ Φ j = 0 := by
    rw [Work.BoseFixB2.vecZ, if_neg]
    rwa [Finset.mem_Icc] at hj
  rw [hvec0, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  simp only [Pi.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), MeasureTheory.integral_zero]

/-- **The grading identity against the matrix `𝓐`.**  For the sector coefficients
`c_k = √‖Φ‖²·x_k/‖1_{n₊=k}Φ‖` (FS's recombination), the polarised word evaluates to the
quadratic form of the grading matrix `𝓐 = gradeA` on the window vector `x`. -/
theorem gradeA_weighted_sum (hℓ : 0 < Work.BoseFixB2.fsSide v μ) {Φ : X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hSpos : 0 < Work.BoseBoxFix.normB v μ n Φ)
    (x : ℤ → ℂ) (hxim : ∀ j, (x j).im = 0)
    (hxsupp : ∀ j, x j ≠ 0 →
      Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j) ≠ 0)
    (cc : ℕ → ℝ)
    (hcc : ∀ k, k ≤ n → cc k = Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) * (x (k : ℤ)).re
      / Real.sqrt (Work.BoseBoxFix.normB v μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ))) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        cc k * cc l * Work.BoseFixB2.polB v h μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ))
      = Work.BoseBoxFix.normB v μ n Φ
        * Work.UBBInputs3.qform (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
            (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) x x := by
  have hN : n + 1 ≤ Work.BoseFixB2.fsNn v μ n := by
    rw [Work.BoseFixB2.fsNn]
    exact succ_le_gradeNn n
  -- terms outside the sector range are killed by the vanishing of `x`
  have hxzero : ∀ j : ℤ, j ∉ Finset.Icc (0 : ℤ) (n : ℤ) → x j = 0 := by
    intro j hj
    by_contra hne
    exact hxsupp j hne
      (normB_zero_vecZ (v := v) (μ := μ) (n := n) (ℓ := Work.BoseFixB2.fsSide v μ) hj)
  -- the quadratic form of `𝓐` on `x`, as a double sum over the sector range
  have hq : Work.UBBInputs3.qform (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
      (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) x x
      = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          ((x (k : ℤ)).re
            * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ) (l : ℤ)
            * (x (l : ℤ)).re) := by
    have hstep1 : Work.UBBInputs3.qform
        (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
        (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) x x
        = ∑ i ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
            ∑ j ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
              ((x i).re * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j
                * (x j).re) := by
      unfold Work.UBBInputs3.qform
      rw [re_double_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Work.BoseFixB2.Energy.gradeA_eq_ofReal, re_star_mul_ofReal_mul,
        hxim i, hxim j]
      ring
    rw [hstep1]
    have hinner : ∀ i : ℤ,
        (∑ j ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
            ((x i).re * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j
              * (x j).re))
          = ∑ l ∈ Finset.range (n + 1),
              ((x i).re
                * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ i (l : ℤ)
                * (x (l : ℤ)).re) := by
      intro i
      apply sum_iRange_eq_sum_range hN
      intro j _ hjn
      rw [hxzero j hjn]
      simp
    calc (∑ i ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
            ∑ j ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
              ((x i).re * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ i j
                * (x j).re))
        = ∑ i ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
            ∑ l ∈ Finset.range (n + 1),
              ((x i).re
                * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ i (l : ℤ)
                * (x (l : ℤ)).re) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hinner i
      _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
            ((x (k : ℤ)).re
              * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ) (l : ℤ)
              * (x (l : ℤ)).re) := by
          apply sum_iRange_eq_sum_range hN
          intro i _ hin
          rw [hxzero i hin]
          simp
  -- the termwise identity for the sector coefficients
  have hterm : ∀ k ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (n + 1),
      cc k * cc l * Work.BoseFixB2.polB v h μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)
        = Work.BoseBoxFix.normB v μ n Φ
          * ((x (k : ℤ)).re
            * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ) (l : ℤ)
            * (x (l : ℤ)).re) := by
    intro k hk l hl
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    by_cases hkpos : 0 < Work.BoseBoxFix.normB v μ n
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
    · by_cases hlpos : 0 < Work.BoseBoxFix.normB v μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)
      · have hAk : Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ
            (k : ℤ) (l : ℤ)
            = Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
                (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)
              / (Real.sqrt (Work.BoseBoxFix.normB v μ n
                    (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ))
                * Real.sqrt (Work.BoseBoxFix.normB v μ n
                    (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ))) := by
          have hguard : (0 ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ) ∧ 0 ≤ (l : ℤ) ∧ (l : ℤ) ≤ (n : ℤ)
              ∧ 0 < Work.BoseBoxFix.normB v μ n
                  (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ))
              ∧ 0 < Work.BoseBoxFix.normB v μ n
                  (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (l : ℤ))) := by
            refine ⟨Int.natCast_nonneg k, by exact_mod_cast hkn, Int.natCast_nonneg l,
              by exact_mod_cast hln, ?_, ?_⟩
            · rwa [vecZ_natCast hkn]
            · rwa [vecZ_natCast hln]
          rw [Work.BoseFixB2.Energy.gradeARe, if_pos hguard, vecZ_natCast hkn, vecZ_natCast hln]
        rw [hcc k hkn, hcc l hln, hAk]
        have hsk : Real.sqrt (Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.mpr hkpos)
        have hsl : Real.sqrt (Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.mpr hlpos)
        have hSsq : (Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)) ^ 2
            = Work.BoseBoxFix.normB v μ n Φ := Real.sq_sqrt (le_of_lt hSpos)
        field_simp
        ring_nf
        rw [hSsq]
        ring
      · have hl0 : Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ) ≤ 0 := not_lt.mp hlpos
        have hcl : cc l = 0 := by
          rw [hcc l hln, Real.sqrt_eq_zero_of_nonpos hl0, div_zero]
        have hneg : ¬ (0 ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ) ∧ 0 ≤ (l : ℤ) ∧ (l : ℤ) ≤ (n : ℤ)
            ∧ 0 < Work.BoseBoxFix.normB v μ n
                (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ))
            ∧ 0 < Work.BoseBoxFix.normB v μ n
                (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (l : ℤ))) := by
          intro hcon
          have h6 := hcon.2.2.2.2.2
          rw [vecZ_natCast hln] at h6
          exact hlpos h6
        have hAl : Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ
            (k : ℤ) (l : ℤ) = 0 := by
          rw [Work.BoseFixB2.Energy.gradeARe, if_neg hneg]
        rw [hcl, hAl]
        ring
    · have hk0 : Work.BoseBoxFix.normB v μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) ≤ 0 := not_lt.mp hkpos
      have hck : cc k = 0 := by
        rw [hcc k hkn, Real.sqrt_eq_zero_of_nonpos hk0, div_zero]
      have hneg : ¬ (0 ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ) ∧ 0 ≤ (l : ℤ) ∧ (l : ℤ) ≤ (n : ℤ)
          ∧ 0 < Work.BoseBoxFix.normB v μ n
              (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ))
          ∧ 0 < Work.BoseBoxFix.normB v μ n
              (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ (l : ℤ))) := by
        intro hcon
        have h5 := hcon.2.2.2.2.1
        rw [vecZ_natCast hkn] at h5
        exact hkpos h5
      have hAk : Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ
          (k : ℤ) (l : ℤ) = 0 := by
        rw [Work.BoseFixB2.Energy.gradeARe, if_neg hneg]
      rw [hck, hAk]
      ring
  rw [hq]
  calc (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        cc k * cc l * Work.BoseFixB2.polB v h μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ))
      = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          Work.BoseBoxFix.normB v μ n Φ
            * ((x (k : ℤ)).re
              * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ) (l : ℤ)
              * (x (l : ℤ)).re) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        exact hterm k hk l hl
    _ = Work.BoseBoxFix.normB v μ n Φ
        * (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
            ((x (k : ℤ)).re
              * Work.BoseFixB2.Energy.gradeARe v h μ n (Work.BoseFixB2.fsSide v μ) Φ (k : ℤ) (l : ℤ)
              * (x (l : ℤ)).re)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]

end Identification

theorem recomb_clause {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hσ : Submission.BoseGases.PermInvariant n Φ) (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ) (n₀ : ℤ) (φ : ℤ → ℂ) (hn₀ : 0 ≤ n₀) (hnn : n₀ + (Work.BoseFixB2.fsRmw v μ : ℤ) ≤ (Work.BoseFixB2.fsNn v μ n : ℤ)) (hsupp : ∀ j : ℤ, φ j ≠ 0 → n₀ ≤ j ∧ j < n₀ + (Work.BoseFixB2.fsRmw v μ : ℤ)) (hunit : Work.UBBInputs3.normSq (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) φ = 1) (hneg : Work.UBBInputs3.qform (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) φ φ < 0) : ∃ Φ' : Work.BoseKinLoc.BoxState n (Work.BoseFixB2.fsSide v μ), Work.BoseBoxFix.normB v μ n Φ' = Work.BoseBoxFix.normB v μ n Φ ∧ Work.BoseBoxFix.wordB v h μ n Φ' ≤ Work.UBBInputs3.qform (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) φ φ * Work.BoseBoxFix.normB v μ n Φ ∧ (∀ 𝓜₂ : ℝ, (n₀ : ℝ) + (Work.BoseFixB2.fsRmw v μ : ℝ) ≤ 𝓜₂ → Work.BoseBox.SpectralNPlusLe (Work.BoseFixB2.fsSide v μ) 𝓜₂ (Φ' : Submission.BoseGases.X n → ℝ)) ∧ (n₀ : ℝ) * Work.BoseBoxFix.normB v μ n Φ' ≤ Submission.BoseGases.cnPlus (Work.BoseFixB2.fsSide v μ) (Φ' : Submission.BoseGases.X n → ℝ) := by
  classical
  -- ## 0. Basic data
  have hℓpos : 0 < Work.BoseFixB2.fsSide v μ := by
    simpa only [Work.BoseFixB2.fsSide] using Work.BoseBox.sideAt_pos hμ hav
  have hΦc : Continuous Φ := hΦ.continuous
  have hN : n + 1 ≤ Work.BoseFixB2.fsNn v μ n := by
    rw [Work.BoseFixB2.fsNn]
    exact succ_le_gradeNn n
  have hw : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
          (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ)) :=
    Work.BoseFixB2.Pot.potWordU_integrable (n := n) h hR hv_supp hv1
      (Work.BoseFixB2.fsSide v μ)
  -- ## 1. The real window vector
  set P : ℤ → Prop := fun j => Work.BoseBoxFix.normB v μ n
      (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j) = 0 with hP
  set A : ℤ → ℤ → ℂ := Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ with hA
  set B : Finset ℤ := Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n) with hB
  have hAz₁ : ∀ i j, P i → A i j = 0 := by
    intro i j hi
    rw [hP] at hi
    rw [hA, Work.BoseFixB2.gradeA, if_neg]
    intro hcon
    rw [hi] at hcon
    exact lt_irrefl 0 hcon.2.2.2.2.1
  have hAz₂ : ∀ i j, P j → A i j = 0 := by
    intro i j hj
    rw [hP] at hj
    rw [hA, Work.BoseFixB2.gradeA, if_neg]
    intro hcon
    rw [hj] at hcon
    exact lt_irrefl 0 hcon.2.2.2.2.2
  have hAim : ∀ i j, (A i j).im = 0 := by
    intro i j
    rw [hA, Work.BoseFixB2.gradeA]
    split
    · rw [Complex.ofReal_im]
    · simp
  set y : ℤ → ℂ := fun j => if P j then 0 else φ j with hy
  have hyapp : ∀ j, y j = if P j then 0 else φ j := by
    intro j
    rw [hy]
  have hqy : Work.UBBInputs3.qform A B y y = Work.UBBInputs3.qform A B φ φ :=
    qform_eq_of_eqOff (A := A) (B := B) hAz₁ hAz₂ (fun j hj => by rw [hyapp j, if_neg hj])
  have hnormy : Work.UBBInputs3.normSq B y ≤ Work.UBBInputs3.normSq B φ := by
    unfold Work.UBBInputs3.normSq
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : P j
    · rw [hyapp j, if_pos hj, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact sq_nonneg _
    · rw [hyapp j, if_neg hj]
  have hnormφ : Work.UBBInputs3.normSq B φ = 1 := by
    rw [hB]
    exact hunit
  have hnegy : Work.UBBInputs3.qform A B y y < 0 := by
    rw [hqy, hA, hB]
    exact hneg
  obtain ⟨x, hxim, hxy, hnormx, hnegx⟩ :=
    exists_real_unit_of_neg (A := A) (B := B) hAim (z := y)
      (le_trans hnormy (le_of_eq hnormφ)) hnegy
  have hxsupp : ∀ j, x j ≠ 0 → Work.BoseBoxFix.normB v μ n
      (Work.BoseFixB2.vecZ (Work.BoseFixB2.fsSide v μ) Φ j) ≠ 0 := by
    intro j hxj h0
    have hPj : P j := by rw [hP]; exact h0
    exact hxy j hxj (by rw [hyapp j, if_pos hPj])
  have hxφ : ∀ j, x j ≠ 0 → φ j ≠ 0 := by
    intro j hxj hφj
    have hyj := hxy j hxj
    by_cases hPj : P j
    · rw [hyapp j, if_pos hPj] at hyj
      exact hyj rfl
    · rw [hyapp j, if_neg hPj, hφj] at hyj
      exact hyj rfl
  have hxzero : ∀ j : ℤ, j ∉ Finset.Icc (0 : ℤ) (n : ℤ) → x j = 0 := by
    intro j hj
    by_contra hne
    exact hxsupp j hne
      (normB_zero_vecZ (v := v) (μ := μ) (n := n) (ℓ := Work.BoseFixB2.fsSide v μ) hj)
  -- ## 2. The recombined state
  set cc : ℕ → ℝ := fun k => Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) * (x (k : ℤ)).re
      / Real.sqrt (Work.BoseBoxFix.normB v μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)) with hcc
  set Φ' : Submission.BoseGases.X n → ℝ := fun z => ∑ k ∈ Finset.range (n + 1),
      cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ z with hΦ'
  have hcc' : ∀ k, k ≤ n → cc k = Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) * (x (k : ℤ)).re
      / Real.sqrt (Work.BoseBoxFix.normB v μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)) := by
    intro k _
    rw [hcc]
  have hccx : ∀ k : ℕ, cc k ≠ 0 → x (k : ℤ) ≠ 0 := by
    intro k hk h0
    exact hk (by rw [hcc]; simp [h0])
  have hsm : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) :=
    fun k => (Work.BoseFixB2.Sector.secProj_contDiff_symm hℓpos hΦ hσ).1
  have hcls : ∀ z, Φ' z = ∑ k ∈ Finset.range (n + 1),
      cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ z := by
    intro z
    rw [hΦ']
  have hfun : Φ' = fun z => ∑ k ∈ Finset.range (n + 1),
      cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ z := funext hcls
  -- the squared norm of `Φ'`
  have hnormΦ' : Work.BoseBoxFix.normB v μ n Φ' = Work.BoseBoxFix.normB v μ n Φ := by
    have hSsq : (Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)) ^ 2
        = Work.BoseBoxFix.normB v μ n Φ := Real.sq_sqrt (le_of_lt hpos)
    have hnn : ∀ Ψ : Submission.BoseGases.X n → ℝ,
        0 ≤ Work.BoseBoxFix.normB v μ n Ψ := by
      intro Ψ
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg (fun z => sq_nonneg _)
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (cc k) ^ 2 * Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
          = Work.BoseBoxFix.normB v μ n Φ * ((x (k : ℤ)).re) ^ 2 := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hk0 : Work.BoseBoxFix.normB v μ n
          (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) = 0
      · have hxk : x (k : ℤ) = 0 := by
          by_contra hne
          refine hxsupp (k : ℤ) hne ?_
          rw [vecZ_natCast hkn]
          exact hk0
        rw [hxk, hk0]
        simp [hcc]
      · have hpos' : 0 < Work.BoseBoxFix.normB v μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) :=
          lt_of_le_of_ne (hnn _) (Ne.symm hk0)
        rw [hcc' k hkn]
        field_simp
        ring_nf
        rw [hSsq, Real.sq_sqrt (le_of_lt hpos')]
        ring
    have hxsum : (∑ k ∈ Finset.range (n + 1), ((x (k : ℤ)).re) ^ 2) = 1 := by
      have hre : Work.UBBInputs3.normSq B x
          = ∑ k ∈ Finset.range (n + 1), ((x (k : ℤ)).re) ^ 2 := by
        have h1 : Work.UBBInputs3.normSq B x = ∑ j ∈ B, ((x j).re) ^ 2 := by
          unfold Work.UBBInputs3.normSq
          exact Finset.sum_congr rfl (fun j _ => by
            rw [Complex.sq_norm, Complex.normSq_apply, hxim j]
            ring)
        rw [h1, hB]
        exact sum_iRange_eq_sum_range (N := Work.BoseFixB2.fsNn v μ n) hN
          (fun j => ((x j).re) ^ 2) (by
            intro j _ hjn
            rw [hxzero j hjn]
            simp)
      rw [← hre, hnormx]
    calc Work.BoseBoxFix.normB v μ n Φ'
        = Work.BoseBoxFix.normB v μ n (fun z => ∑ k ∈ Finset.range (n + 1),
            cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ z) := by
          rw [hfun]
      _ = ∑ k ∈ Finset.range (n + 1),
            (cc k) ^ 2 * Work.BoseBoxFix.normB v μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) :=
          normB_weighted_secProj (v := v) (μ := μ) (n := n) hℓpos hΦc cc
      _ = ∑ k ∈ Finset.range (n + 1),
            Work.BoseBoxFix.normB v μ n Φ * ((x (k : ℤ)).re) ^ 2 :=
          Finset.sum_congr rfl hterm
      _ = Work.BoseBoxFix.normB v μ n Φ
            * ∑ k ∈ Finset.range (n + 1), ((x (k : ℤ)).re) ^ 2 := by
          rw [Finset.mul_sum]
      _ = Work.BoseBoxFix.normB v μ n Φ * 1 := by rw [hxsum]
      _ = Work.BoseBoxFix.normB v μ n Φ := by ring
  -- ## 3. The word bound
  have hword : Work.BoseBoxFix.wordB v h μ n Φ'
      ≤ Work.UBBInputs3.qform (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
          (Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n)) φ φ * Work.BoseBoxFix.normB v μ n Φ := by
    have hle : Work.UBBInputs3.qform A B x x ≤ Work.UBBInputs3.qform A B φ φ :=
      le_trans hnegx (le_of_eq hqy)
    rw [hA, hB] at hle
    have hexp := wordB_expansion_range (v := v) (h := h) (μ := μ) (n := n) hμ hav hw
      (j := n) cc (fun k => Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) hsm
    have hid := gradeA_weighted_sum (v := v) (h := h) (μ := μ) (n := n) hℓpos hΦ hpos x hxim
      hxsupp cc hcc'
    simp only [hΦ']
    rw [hexp, hid]
    nlinarith [hpos, hle]
  -- ## 4. The spectral confinement and the `n₊`-expectation
  have hcls : ∀ z, Φ' z = ∑ k ∈ Finset.range (n + 1),
      cc k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ z := by
    intro z
    rw [hΦ']
  refine ⟨⟨Φ', ?_, ?_, ?_⟩, hnormΦ', hword, ?_, ?_⟩
  · simp only [hΦ']
    exact ContDiff.sum (fun k _ => by
      simpa only [smul_eq_mul] using ContDiff.const_smul (cc k) (hsm k))
  · intro σ z
    simp only [hcls]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [(Work.BoseFixB2.Sector.secProj_contDiff_symm hℓpos hΦ hσ).2 σ z]
  · intro hzero
    have hS := hnormΦ'
    rw [hzero, normB_zero] at hS
    exact absurd hS.symm (ne_of_gt hpos)
  · intro 𝓜₂ h𝓜₂
    have hwin : ∀ k ∈ Finset.range (n + 1), cc k ≠ 0 → (k : ℝ) ≤ 𝓜₂ := by
      intro k _ hk0
      have hxk : x (k : ℤ) ≠ 0 := hccx k hk0
      obtain ⟨_, h2⟩ := hsupp (k : ℤ) (hxφ (k : ℤ) hxk)
      have h2' : ((k : ℤ) : ℝ) < (n₀ : ℝ) + (Work.BoseFixB2.fsRmw v μ : ℝ) := by
        exact_mod_cast h2
      have : ((k : ℤ) : ℝ) ≤ 𝓜₂ := by linarith
      simpa using this
    have hMnn : 0 ≤ 𝓜₂ :=
      le_trans (add_nonneg (by exact_mod_cast hn₀) (Nat.cast_nonneg _)) h𝓜₂
    simp only [hΦ']
    exact spectralNPlusLe_weighted (v := v) (μ := μ) (n := n) hℓpos hΦ cc hMnn hwin
  · have hwin : ∀ k ∈ Finset.range (n + 1), cc k ≠ 0 → (n₀ : ℝ) ≤ (k : ℝ) := by
      intro k _ hk0
      have hxk : x (k : ℤ) ≠ 0 := hccx k hk0
      obtain ⟨h1, _⟩ := hsupp (k : ℤ) (hxφ (k : ℤ) hxk)
      have h1' : (n₀ : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast h1
      simpa using h1'
    simp only [hΦ']
    exact cnPlus_weighted (v := v) (μ := μ) (n := n) (n₀ := (n₀ : ℝ)) hℓpos hΦ cc hwin

end Work.BoseFixB2.Recomb
