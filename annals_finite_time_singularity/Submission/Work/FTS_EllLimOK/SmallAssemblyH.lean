/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.SmallAssemblyH` — the order-`3` reduction and the small-`α` assembly over `HasPkgH`

Three ingredients, all over the installed honest hypothesis `HasPkgH` (`FatouH`):

* `ClosedE3H_of_compact3_uniq3` — obligation 1 at order `3` (`ClosedCompact3H`) plus the jet
  uniqueness (`ClosedUniq3G`, unchanged — its `IsJetLimit3G` consumes only the minimal package
  `FatouPkgG`) give the order-`3` closure `ClosedE3G`;
* `SmallCompact3H_of` — the three sequence-level pieces (`SmallLocalBoundH`, `SmallFatouDataH`,
  `SmallBoxDataH`) give the small-`α` compactness obligation;
* `smallBoxDataH_of_pointwise` / `smallBoxDataH` — the box data is produced `α`-local
  (`BoxDataH.boxDataH_of_hasPkgH`, a separate module);
* `smallCompact3H` — **obligation 1 over `HasPkgH`, unconditionally** (all three pieces are proved).
-/
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Metrizable.Uniformity
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS_EllLimOK.ClosedCompact3H_of_bounds_fatou
import Submission.Work.FTS_EllLimOK.Closed3
import Submission.Work.FTS_EllLimOK.Closed
import Submission.Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The order-`3` reduction over `HasPkgH`**: obligations 1 and 2 give the order-`3` closure of
every operator carrying `HasPkgH` (same subsequence argument as `Closed3.ClosedE3_of_compact3_uniq3`;
the uniqueness statement `ClosedUniq3G` is package-free). -/
theorem ClosedE3H_of_compact3_uniq3 {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn}
    (hE : HasPkgH α Ce E) (hcomp : ClosedCompact3H α Ce) (huniq : ClosedUniq3G α) :
    ClosedE3G α E := by
  intro fn f hL
  obtain ⟨Ψ, hΨlim⟩ := hcomp E hE fn f hL
  refine ⟨Ψ, hΨlim.1, ?_⟩
  intro j i hji z θ hz
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hL' : LimSeq4 α (fun n => fn (ns (ψ n))) f := limSeq4_comp hL hnsψ.tendsto_atTop
  obtain ⟨Ψ₂, hfat₂, σ, hσ, hJ₂⟩ := hcomp E hE _ f hL'
  have h₂ : IsJetLimit3G α E fn f Ψ₂ :=
    ⟨hfat₂, ⟨fun n => ns (ψ (σ n)), hnsψ.tendsto_atTop.comp hσ, by
      simpa only [Function.comp_apply] using hJ₂⟩⟩
  have hjet := huniq E fn f hL Ψ Ψ₂ hΨlim h₂ j i hji z θ hz
  refine ⟨fun n => ψ (σ n), ?_⟩
  rw [hjet]
  simpa only [Function.comp_apply] using hJ₂ j i hji z θ hz

/-- **The small-`α` compactness assembly over `HasPkgH`.** -/
theorem SmallCompact3H_of (hbd : SmallLocalBoundH) (hfat : SmallFatouDataH)
    (hbox : SmallBoxDataH) : SmallCompact3H := by
  obtain ⟨αb, hαb, hb⟩ := hbd
  obtain ⟨αf, hαf, hf⟩ := hfat
  obtain ⟨αx, hαx, hx⟩ := hbox
  refine ⟨min (min αb αf) αx, lt_min (lt_min hαb hαf) hαx, fun α hα hle Ce => ?_⟩
  have h1 : α ≤ αb := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have h2 : α ≤ αf := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have h3 : α ≤ αx := le_trans hle (min_le_right _ _)
  exact ClosedCompact3H_of_bounds_fatou (hb α hα h1 Ce) (hf α hα h2 Ce) (hx α hα h3 Ce)

/-- The box data at the `α`-local threshold gives the small-`α` shape. -/
theorem smallBoxDataH_of_pointwise
    (h : ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ Ce : ℝ, BoxDataH α Ce) : SmallBoxDataH :=
  ⟨1, one_pos, fun α hα hα1 Ce => h α hα hα1 Ce⟩

/-- **The box data over `HasPkgH`, unconditionally** (the Hölder closed-box producer). -/
theorem smallBoxDataH : SmallBoxDataH :=
  smallBoxDataH_of_pointwise fun α hα hα1 Ce =>
    Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH hα hα1

/-- **Obligation 1 over `HasPkgH`, unconditionally**: the three sequence-level pieces
(`SmallLocalBoundH`, `SmallFatouDataH`, `SmallBoxDataH`) are all proved. -/
theorem smallCompact3H : SmallCompact3H :=
  SmallCompact3H_of smallLocalBoundH smallFatouDataH smallBoxDataH

end Work.FTS_EllLimOK
