import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.smallness_ratios
import Submission.Work.BoseK15.A_ge_and_AB_of_taurad
import Submission.Work.BoseK15.ChiSmall
import Submission.Work.BoseK15.Main
import Submission.Work.BoseK15.arith_KH_a_div_ell_pow_le_eta
import Submission.Work.BoseK15.arith_aKH_div_sell_le
import Submission.Work.BoseK15.arith_tau_ge
import Submission.Work.BoseK15.chi_sums_of_decay
import Submission.Work.BoseK15.count_PL_le
import Submission.Work.BoseK15.hatChiSq_double_sum_nonneg
import Submission.Work.BoseK15.hatChiSq_form_upper
import Submission.Work.BoseK15.sum_W1sq_le_new
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.Corpus` — the derived fields at FS's parameters

`Main.lean`'s `toQ3Kernel` assembles `Work.BoseB7A.Q3Kernel` from a
`Work.BoseK15.K15Input` plus the chapter's derived-field facts.  This module
supplies those facts at FS's own parameter point: a single diluteness threshold
`t₀` (absolute, depending only on the chapter constant `K₀` and the gap lower
bound `b₀`) at which `hatChi_small`, `ccrX_small`, `sum_hatChiSq`,
`tail_hatChiSq`, `hatChiSq_form`, `count_PL`, `sum_W1sq`, `A_ge` and `AB|_{P_H^q}`
all hold simultaneously.

The four ingredient thresholds are

* `Work.BoseB7A.smallness_ratios` (the §10 smallness list S1–S11),
* `Work.BoseK15.arith_aKH_div_sell_le` (`aK_H/(sℓ) → 0`, which makes `‖kmom q‖`
  dominate `1/(2sℓ)` on `P_H^q`),
* `Work.BoseK15.arith_tau_ge` (the radial `τ` bound), and
* the χ-decay arithmetic `Work.BoseK15.arith_KH_a_div_ell_pow_le_eta`
  (`(K_Ha/ℓ)^{52} ≤ η`, no threshold).

They are combined by taking the minimum; the result is stated as the single
existential `Work.BoseK15.K15Fields_of_fsParams`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

universe u v

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `E.intM + 3 ≤ 2·decayOrder`: FS's `M = 48` against the chapter's
`decayOrder = 26` (`48 + 3 = 51 ≤ 52`). -/
theorem intM_add_three_le {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) (hv : FSParamsView E) :
    E.intM + 3 ≤ 2 * decayOrder := by
  rw [hv.intM_eq]
  decide

/-- **The derived fields of the chapter at FS's parameters.**  A single
diluteness threshold `t₀` (absolute, depending only on `K₀` and `b₀`) at which all
the χ-side and potential-side facts that `toQ3Kernel`/`toIntKernel` consume hold
simultaneously, for every honest `K15Input` at FS's parameter point. -/
theorem K15Fields_of_fsParams {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : Work.BoseB7.FockData.{u, v} Mode}
    {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (h : K15Input K₀ F T E) (hv : Work.BoseB7.FSParamsView E) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ (hv.t ≤ t₀ → b₀ ≤ E.b →
        (∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E) ∧
        (∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q →
          |T.ccrX s q| ≤ K₀ * eta E) ∧
        (∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀) ∧
        (∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
          ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) ∧
        (∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H),
          (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
            ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s)) ∧
        (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3 ∧
        (E.ell ^ (-(3 : ℝ)) *
            ∑ q ∈ (excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
              E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 ≤ K₀ * E.aScat) ∧
        (∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q) ∧
        (∀ q : Mode, F.PHq E.KH E.aScat q → 2 * |E.B q| ≤ E.A q) ∧
        (∀ q : Mode, F.PHq E.KH E.aScat q → 0 < E.A q)) := by
  obtain ⟨t₁, ht₁, hsmall⟩ := smallness_ratios K₀ b₀ hb₀ (1 / 16) (by norm_num)
  obtain ⟨t₂, ht₂, hsell⟩ := arith_aKH_div_sell_le (1 / 16) (by norm_num)
  obtain ⟨t₃, ht₃, htau⟩ := arith_tau_ge K₀
  refine ⟨min (min t₁ t₂) t₃, lt_min_iff.mpr ⟨lt_min_iff.mpr ⟨ht₁, ht₂⟩, ht₃⟩, ?_⟩
  intro ht hb
  have ht1 : hv.t ≤ t₁ := le_trans ht (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht2 : hv.t ≤ t₂ := le_trans ht (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht3 : hv.t ≤ t₃ := le_trans ht (min_le_right _ _)
  obtain ⟨hS1, _hS2, _hS3, _hS4, _hS5, _hS6, _hS7, _hS8, hS9⟩ := hsmall E hv ht1 hb
  -- `aK_H/(sℓ) ≤ 1/16`
  have hsell' : E.aScat * E.KH / (E.s * E.ell) ≤ 1 / 16 := hsell E hv ht2
  -- the χ-decay arithmetic of the chapter
  have heta : (E.aScat * E.KH / E.ell) ^ (2 * decayOrder) ≤ eta E :=
    arith_KH_a_div_ell_pow_le_eta E hv
  -- `hatChi_small` and `ccrX_small` (K2's decay on `P_H^q`)
  have hsmall1 : E.KL * Real.sqrt (E.mu * E.aScat) * (E.KH * E.aScat) ≤ 1 / 16 := hS1
  have hchi : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E :=
    fun q hq => h.hatChi_small_holds heta q hq
  have hccrX : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q →
      |T.ccrX s q| ≤ K₀ * eta E := h.ccrX_small_holds heta hsmall1
  -- `sum_hatChiSq` and `tail_hatChiSq` (K2's lattice sums; `hKL` is FS's S10)
  obtain ⟨hsum, htail⟩ :=
    chi_sums_of_decay_fixed_statement h h.ellKL hS9 (intM_add_three_le E hv)
  -- the χ-form upper bound
  have hform := hatChiSq_form_upper h
  -- `count_PL`
  have hcount := count_PL_le h h.ellKL hS9
  -- `sum_W1sq`
  have hsumW1 := sum_W1sq_le_new h
  -- `A_ge` and `AB` on `P_H^q`
  have hrho : 0 ≤ E.rho := h.rho_nonneg
  have htaurad := htau E hv ht3 hsell'
  obtain ⟨hAge, hABq⟩ := A_ge_and_AB_of_taurad h hrho htaurad
  refine ⟨hchi, hccrX, hsum, htail, hform, hcount, hsumW1, hAge, hABq, ?_⟩
  intro q hq
  have h1 := hAge q hq
  have hK : 0 < E.KH * E.aScat := mul_pos h.KH_pos h.aScat_pos
  have h2 : 0 < 1 / (4 * E.KH * E.aScat) := by
    have hh : 0 < E.KH := h.KH_pos
    have haa : 0 < E.aScat := h.aScat_pos
    positivity
  have h3 : 0 < ‖F.kmom q‖ := lt_of_lt_of_le h2 hq
  nlinarith [h1, h3, norm_nonneg (F.kmom q)]

/-- **`Q3Kernel` for the corpus instance at FS's parameters.**  The complete
chapter deliverable: a single absolute `K₀`, a single diluteness threshold `t₀`
and the honest-instance bundle `K15Input K₀` give the whole of FS §10's kernel
interface.

Three hypotheses are not derivable from the bundle's *primitive* fields, and all
three are recorded in the README (§5):

* the **global** `hasKernel`.  The bundle's field is guarded on the summed pairs
  (that is the only form the box model satisfies, `Obstruction.lean`); the global
  identity would force `kmom ≡ 0` and empty `P_H^q`.

* the **global** `AB` (`|E.B k| ≤ E.A k` for every mode).  FS's `eq:BoverA` is
  stated for `|k| ≥ ½K_H^{-1}a^{-1}` only, and that is the form the chapter
  proves *unconditionally* (`Work.BoseK15.A_ge_and_AB_of_taurad`).  The global
  form is also true and is proved separately by `Work.BoseK15.AB_global` from
  FS's low-momentum positivity of `Ŵ₁`; it is taken here as an explicit
  hypothesis so that this theorem does not depend on that row.
* the **positive-semidefiniteness** half of `hatChiSq_form` (the *guarded* form —
  weights vanishing off `supp f_L` — is proved in
  `Work.BoseK15.hatChiSq_form_psd_guarded`, and used by
  `Work.BoseK15.Q3Kernel'`; the unguarded form is not formally refuted here, see
  `README.md` §5.3).  The kernel
  `χ̂²(ℓ·kmom(s'−s))` is Bochner-positive *as a function of the momentum
  difference*, i.e. for the kernel `χ̂²(M s' − M s)` with `M = ℓ·kmom`
  (`Work.BoseK15.hatChiSq_double_sum_nonneg`, proved).  Identifying
  `ℓ·kmom(s'−s)` with `ℓ·kmom s' − ℓ·kmom s` is the label additivity, which on a
  *truncated* lattice holds only away from the wrap-around near the cutoff
  (design §5): for `S ⊆ supp f_L ⊆ P_L` (the only place §10 uses it) it does
  hold. -/
theorem Q3Kernel_corpus {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : Work.BoseB7.FockData.{u, v} Mode}
    {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (h : K15Input K₀ F T E) (hv : Work.BoseB7.FSParamsView E) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ((∀ k : Mode, |E.B k| ≤ E.A k) →
        (∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H),
          0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s)) →
        (∀ i j : Mode, F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j) →
        hv.t ≤ t₀ → b₀ ≤ E.b →
        Q3Kernel K₀ F T E) := by
  obtain ⟨t₀, ht₀, hfields⟩ := K15Fields_of_fsParams K₀ b₀ hb₀ h hv
  refine ⟨t₀, ht₀, ?_⟩
  intro hAB hPSD hhasK ht hb
  obtain ⟨hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, _hc₉, _⟩ := hfields ht hb
  exact h.toQ3Kernel hc₁ hc₂ hc₃ hc₄ hPSD hc₅ hc₆ hc₇ hc₈ hAB hhasK h.intOne_holds

/-- **`IntKernel` for the corpus instance at FS's parameters** (the inputs of
`lem:EstimateIntegral`).  The `P_H`-form of the region facts and the `P_H`-form of
`sum_W1sq` are taken as hypotheses; `Work.BoseB7A.PH_subset_PHq_sub` converts
them from the chapter's `P_H^q` bounds once the smallness of `K_L√(μa)·K_Ha` is
available. -/
theorem IntKernel_corpus {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : Work.BoseB7.FockData.{u, v} Mode}
    {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    (K₀ b₀ R : ℝ) (hb₀ : 0 < b₀) (h : K15Input K₀ F T E) (hv : Work.BoseB7.FSParamsView E) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ((∀ k : Mode, F.PH E.KH E.aScat k → ‖F.kmom k‖ ^ 2 / 2 ≤ E.A k) →
        (∀ k : Mode, F.PH E.KH E.aScat k → 2 * |E.B k| ≤ E.A k) →
        (∀ k : Mode, F.PH E.KH E.aScat k →
          0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k ∧ ‖F.kmom k‖ ^ 2 - E.tau k
            ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell)) →
        (E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
          ≤ K₀ * E.aScat) →
        hv.t ≤ t₀ → b₀ ≤ E.b →
        IntKernel K₀ R F E h.gHat) := by
  obtain ⟨t₀, ht₀, _⟩ := K15Fields_of_fsParams K₀ b₀ hb₀ h hv
  refine ⟨t₀, ht₀, ?_⟩
  intro hAge hAB htau hW ht hb
  exact h.toIntKernel R hAge hAB (fun k hk => h.kmom_ne_holds hk) htau hW

end Work.BoseK15
