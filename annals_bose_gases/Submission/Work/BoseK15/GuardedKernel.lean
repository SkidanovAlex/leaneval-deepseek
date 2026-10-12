import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.ABglobal
import Submission.Work.BoseK15.Additive
import Submission.Work.BoseK15.Corpus
import Submission.Work.BoseK15.hatChiSq_form_psd_guarded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.GuardedKernel` — the `Q3Kernel` interface at the honest box

Three fields of `Work.BoseB7A.Q3Kernel` cannot hold at the honest box model:

* the **global `hasKernel`** identity (it forces the unguarded label additivity,
  hence `kmom ≡ 0`: `Work.BoseK15.Obstruction`);
* the **PSD half of `hatChiSq_form`** — genuine only for weights supported on
  `supp f_L` (the way §10 uses it: `c = f_L`);
* (and, as recorded in README §5.2, the global `AB` *as the design stated it* —
  but this one is **global after all**: `Work.BoseK15.AB_global` recovers it
  from the `P_H^q` row plus FS's low-momentum positivity of `Ŵ₁`).

This module defines `Work.BoseK15.Q3Kernel'`, a parallel interface that keeps
*every* field of `Work.BoseB7A.Q3Kernel` — including the global `AB`, so
`Work.BoseB7A.Assembly`'s `𝒟 ≥ 0` and `dNumOpR_mono` enlargement still work —
and replaces only the two genuinely refutable ones by their honest form:

* `hasKernel : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E → …` (the bundle's guard), plus
  the pair-level `hasKernel_noWrap : ∀ i j, NoWrap F.kmom i j → …`;
* `hatChiSq_form` with the weight guard `c s ≠ 0 → E.fL s ≠ 0`.

`Q3Kernel'_of_box` proves it from `K15Input K₀ F T E` + `FSParamsView` at one
absolute `t₀` (in the shape of `Work.BoseK15.IntKernel_box_of_inhabited`),
modulo the box-model equations (`hkmomeq`, `hFbox`, `hχεq`, `hχ2eq` — all `rfl`
at `Work.BoseK15.boxFockDataBox`) and FS's low-momentum positivity row `hW1low`
(the one extra honest row that restores the global `AB`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

universe u v

/-- **The honest kernel interface.**  Same fields as `Work.BoseB7A.Q3Kernel`,
except that (i) the label identity is guarded (bundle guard + `NoWrap`) and
(ii) the `χ̂²`-form is asked only for weights vanishing off `supp f_L`.  The
global `AB` row is kept: it is *derivable* (`Work.BoseK15.AB_global`). -/
structure Q3Kernel' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : Prop where
  W1_le : ∀ k, |E.W1 k| ≤ K₀ * E.aScat
  W1_even : ∀ k, E.W1 (-k) = E.W1 k
  A_even : ∀ k, E.A (-k) = E.A k
  B_even : ∀ k, E.B (-k) = E.B k
  B_eq : ∀ k, E.B k = E.rho * E.W1 k
  /-- FS `eq:BoverA`, **globally** (`Work.BoseK15.AB_global`). -/
  AB : ∀ k, |E.B k| ≤ E.A k
  A_ge : ∀ q, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q
  fL_nonneg : ∀ s, 0 ≤ E.fL s
  fL_le_one : ∀ s, E.fL s ≤ 1
  fL_even : ∀ s, E.fL (-s) = E.fL s
  fL_supp : ∀ s, E.fL s ≠ 0 → F.PL E.KL E.mu E.aScat s
  kmom_sub : ∀ s k, E.fL s ≠ 0 → k ∈ F.PHset E → F.kmom (s - k) = F.kmom s - F.kmom k
  /-- FS `eq:Commutator_general`, on the pairs §10 sums over. -/
  hasKernel : ∀ i j, E.fL i ≠ 0 → j ∈ F.PHset E →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  /-- the same identity at every pair whose labels do not wrap
  (`Work.BoseK15.NoWrap`). -/
  hasKernel_noWrap : ∀ i j, NoWrap F.kmom i j →
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
  hatChiSq_le : ∀ s, |E.hatChiSq s| ≤ 1
  hatChi_le : ∀ s, |E.hatChi s| ≤ 1
  hatChi_even : ∀ s, E.hatChi (-s) = E.hatChi s
  hatChiSq_even : ∀ s, E.hatChiSq (-s) = E.hatChiSq s
  hatChi_small : ∀ q, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E
  ccrX_small : ∀ s q, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E
  /-- Bochner + Schur, for the weights §10 uses (`c = f_L`). -/
  hatChiSq_form : ∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H),
    (∀ s ∈ S, c s ≠ 0 → E.fL s ≠ 0) →
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s) ∧
      ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s)
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s)
  count_PL : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3
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
  q2exLower : ∀ Ψ : F.H, 2 * E.rho * E.W1omega0 * F.qw Ψ (T.Gop E)
    ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E)

/-- **`Q3Kernel'` at the honest box**, from the bundle alone.  The extra
hypotheses are the box-model equations (`rfl` at `Work.BoseK15.boxFockDataBox`)
and FS's low-momentum positivity row `hW1low` (`Ŵ₁ ≥ 0` for
`‖k‖ ≤ ¼K_H⁻¹a⁻¹`), which is what turns the `P_H^q` row `2|ℬ| ≤ 𝒜` into the
global row `|ℬ| ≤ 𝒜` (`Work.BoseK15.AB_global`). -/
theorem Q3Kernel'_of_box {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : Work.BoseB7.FockData.{u, v} Mode}
    {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (h : K15Input K₀ F T E)
    (hv : Work.BoseB7.FSParamsView E)
    (kmom : Mode → ℝ³) (hkmomeq : ∀ i : Mode, F.kmom i = kmom i)
    (hFbox : ∀ i j : Mode, F.ccrK i j
      = corpusBox.hatChiSq (E.ell • (kmom i - kmom j))
        - corpusBox.hatChi (E.ell • kmom i) * corpusBox.hatChi (E.ell • kmom j))
    (hχεq : ∀ k : Mode, E.hatChi k = corpusBox.hatChi (E.ell • kmom k))
    (hχ2eq : ∀ k : Mode, E.hatChiSq k = corpusBox.hatChiSq (E.ell • kmom k))
    (hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ (hv.t ≤ t₀ → b₀ ≤ E.b → Q3Kernel' K₀ F T E) := by
  obtain ⟨t₀, ht₀, hf⟩ := K15Fields_of_fsParams K₀ b₀ hb₀ h hv
  have heT0 : 0 ≤ E.eT := by
    rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have heT1 : E.eT ≤ 1 := by
    rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  refine ⟨t₀, ht₀, fun ht hb => ?_⟩
  obtain ⟨hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hc₈, hc₉, _⟩ := hf ht hb
  exact
    { W1_le := h.W1_le_holds
      W1_even := h.W1_even_holds
      A_even := h.A_even_holds
      B_even := h.B_even_holds
      B_eq := h.B_eq_holds
      AB := AB_global h hc₉ hW1low heT0 heT1
      A_ge := hc₈
      fL_nonneg := h.fL_nonneg_holds
      fL_le_one := h.fL_le_one_holds
      fL_even := h.fL_even_holds
      fL_supp := h.fL_supp_holds
      kmom_sub := h.kmom_sub_holds
      hasKernel := h.hasKernel
      hasKernel_noWrap := fun i j hij =>
        hasKernel_of_noWrap kmom hFbox hχ2eq hχεq (by
          show kmom (i - j) = kmom i - kmom j
          rw [← hkmomeq (i - j), ← hkmomeq i, ← hkmomeq j]
          show F.kmom (i - j) = F.kmom i - F.kmom j
          exact hij)
      hatChiSq_le := h.hatChiSq_le_holds
      hatChi_le := h.hatChi_le_holds
      hatChi_even := h.hatChi_even_holds
      hatChiSq_even := h.hatChiSq_even_holds
      hatChi_small := hc₁
      ccrX_small := hc₂
      hatChiSq_form := fun S c v hg =>
        ⟨hatChiSq_form_psd_guarded h S c v hg, hc₅ S c v⟩
      count_PL := hc₆
      sum_hatChiSq := hc₃
      tail_hatChiSq := hc₄
      sum_W1sq := hc₇
      alpha_lip := h.alpha_lip_holds
      W1omega0_nonneg := h.W1omega0_nonneg_holds
      W1omega0_le := h.W1omega0_le_holds
      intOne := h.intOne_holds
      q2exLower := h.q2exLower_holds }

end Work.BoseK15
