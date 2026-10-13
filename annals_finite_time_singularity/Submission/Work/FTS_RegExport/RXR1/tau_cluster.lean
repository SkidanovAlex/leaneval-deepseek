import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.RegPkgGal.Der.rhs_jet_of_parts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.tau_cluster` — the `τ`-regularity cluster of the `R1` block

The target is the pair of `τ`-derivative fields of `RegExportIface.R1Block`
(`hjdt` and `ht0`, at `θ ∈ Iθ` and `τ₀ ∈ Ico 0 (S+1)`) for the sanitised family
`G := gS α (tauExt g)`, from the primitive `R5Parts` data at the horizon `S+1`.

The proof goes through the right-hand side of the fake-time equation
`R τ z θ := dynLin (pExp α) G τ z θ + dynRHS (pExp α) Φ G τ z θ`:

* `R5Parts.hsol`/`h0` identify `∂_τ G` with `R` at every `τ ≥ 0` on the open quadrant, and the
  right-Taylor branch of `tauExt` identifies it with the *right* derivative of `G` at `τ = 0` for
  `τ < 0`; hence `deriv (fun s => G z θ s) s' = R (max s' 0) z θ`;
* `R5Parts.hJ` (the four `Jet`s) + `hmb`/`hmbh` upgrade to a `Jet` of `R` itself
  (`Der.rhs_jet_of_parts`), which by `tauJetMax`/`tauJetTau` is continuous at `z = 0⁺` and from
  the right at `τ = 0`;
* `R5Parts.hRz0` says `R τ 0 θ = 0`;
* on the two angular ends `θ = 0, π/2` the family and its `τ`-derivative vanish identically
  (`DynOK'.1.1.vanish`), so both limits are trivial there.
-/

namespace Work.FTS_RegExport.RXR1

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## `Jet`-continuity at `z = 0⁺` and from the right at `τ = 0` -/

/-- **A `Jet` is right-continuous at `τ = 0`.**  From the `τ`-modulus of `Jet.tmod` and the
continuity of `t ↦ N·t^α` at `0` (`α > 0`). -/
theorem tauJetTau {α T N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α T N h) (hα : 0 < α) (hT : 0 < T)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Filter.Tendsto (fun τ => h z θ τ) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (h z θ 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hN0 : 0 ≤ N := H.1
  have hcont : ContinuousAt (fun t : ℝ => N * t ^ α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
  have htend : Filter.Tendsto (fun t : ℝ => N * t ^ α) (𝓝 (0:ℝ)) (𝓝 0) := by
    have h := hcont.tendsto
    have h0 : N * (0:ℝ) ^ α = 0 := by rw [Real.zero_rpow hα.ne', mul_zero]
    rwa [h0] at h
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (Metric.tendsto_nhds.mp htend ε hε)
  have hbound : ∀ s : ℝ, 0 ≤ s → s < δ₁ → N * s ^ α < ε := by
    intro s hs0 hs1
    have hsball : s ∈ Metric.ball (0:ℝ) δ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]; exact hs1
    have h := hδ₁ hsball
    simp only [Set.mem_ofPred_eq] at h
    rw [Real.dist_eq, sub_zero] at h
    rwa [abs_of_nonneg (mul_nonneg hN0 (Real.rpow_nonneg hs0 α))] at h
  refine ⟨min δ₁ T, lt_min hδ₁pos hT, ?_⟩
  intro τ hτ hdist
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hdist_eq : dist τ (0:ℝ) = |τ - 0| := Real.dist_eq τ 0
  have hslt : |τ - 0| < δ₁ := by
    rw [← hdist_eq]
    exact lt_of_lt_of_le hdist (min_le_left δ₁ T)
  have hτT : τ ≤ T := by
    have h2 := lt_of_lt_of_le hdist (min_le_right δ₁ T)
    rw [hdist_eq, sub_zero, abs_of_nonneg hτ0] at h2
    exact h2.le
  have hb := H.tmod (z := z) (θ := θ) (τ := τ) (τ' := 0) hz hθ ⟨hτ0, hτT⟩ ⟨le_rfl, hT.le⟩
  rw [Real.dist_eq]
  calc |h z θ τ - h z θ 0| ≤ N * |τ - 0| ^ α := hb
    _ < ε := hbound _ (abs_nonneg _) hslt

/-- **A `Jet` is continuous at `z = 0⁺`** (jointly in `τ`): the right-hand side of the fake-time
equation tends to its value at `z = 0` as `(z, τ) → (0⁺, τ₀)`, `τ ∈ (-∞,T]`. -/
theorem tauJetMax {α T N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α T N h) (hα : 0 < α) (hT : 0 < T)
    {θ τ₀ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hτ₀ : τ₀ ∈ Set.Ico 0 T) :
    Filter.Tendsto (fun p : ℝ × ℝ => h p.1 θ (max p.2 0))
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0 : ℝ)) (Set.univ)))
      (nhds (h 0 θ τ₀)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hN0 : 0 ≤ N := H.1
  have hcont : ContinuousAt (fun t : ℝ => N * t ^ α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
  have htend : Filter.Tendsto (fun t : ℝ => N * t ^ α) (𝓝 (0:ℝ)) (𝓝 0) := by
    have h := hcont.tendsto
    have h0 : N * (0:ℝ) ^ α = 0 := by rw [Real.zero_rpow hα.ne', mul_zero]
    rwa [h0] at h
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (Metric.tendsto_nhds.mp htend ε hε)
  have hbound : ∀ s : ℝ, 0 ≤ s → s < δ₁ → N * s ^ α < ε := by
    intro s hs0 hs1
    have hsball : s ∈ Metric.ball (0:ℝ) δ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]; exact hs1
    have h := hδ₁ hsball
    simp only [Set.mem_ofPred_eq] at h
    rw [Real.dist_eq, sub_zero] at h
    rwa [abs_of_nonneg (mul_nonneg hN0 (Real.rpow_nonneg hs0 α))] at h
  have hτ₀0 : 0 ≤ τ₀ := hτ₀.1
  have hT0 : 0 < T - τ₀ := by linarith [hτ₀.2]
  refine ⟨min (δ₁ / 2) ((T - τ₀) / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro p hp hdist
  have hp1 : 0 < p.1 := hp.1
  have hd1 : dist p ((0:ℝ), τ₀) < δ₁ / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : dist p ((0:ℝ), τ₀) < (T - τ₀) / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hdist_eq : dist p ((0:ℝ), τ₀) = max |p.1| |p.2 - τ₀| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
  have h1 : |p.1| ≤ dist p ((0:ℝ), τ₀) := by rw [hdist_eq]; exact le_max_left _ _
  have h2 : |p.2 - τ₀| ≤ dist p ((0:ℝ), τ₀) := by rw [hdist_eq]; exact le_max_right _ _
  have h3 : |max p.2 0 - τ₀| ≤ dist p ((0:ℝ), τ₀) := by
    rcases le_or_gt 0 p.2 with h2' | h2'
    · calc |max p.2 0 - τ₀| = |p.2 - τ₀| := by rw [max_eq_left h2']
        _ ≤ dist p ((0:ℝ), τ₀) := h2
    · have hmax0 : max p.2 0 = 0 := max_eq_right h2'.le
      have h4 : τ₀ ≤ dist p ((0:ℝ), τ₀) := by
        rw [hdist_eq]
        have h8 : τ₀ ≤ |p.2 - τ₀| := by
          rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < τ₀ - p.2)]
          linarith
        exact le_trans h8 (le_max_right |p.1| |p.2 - τ₀|)
      rw [hmax0, zero_sub, abs_neg, abs_of_nonneg hτ₀.1]
      exact h4
  have hmaxT : max p.2 0 ≤ T := by
    have h6 : |p.2 - τ₀| < (T - τ₀) / 2 := lt_of_le_of_lt h2 hd2
    have h7 : p.2 - τ₀ ≤ |p.2 - τ₀| := le_abs_self _
    have h5 : p.2 < T := by linarith
    exact max_le h5.le hT.le
  have hsum : |p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀| ≤ 2 * dist p ((0:ℝ), τ₀) := by
    simp only [sub_zero, sub_self, abs_zero, add_zero]
    linarith [h1, h3]
  have hsum0 : 0 ≤ |p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀| := by positivity
  have hsumlt : |p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀| < δ₁ := by
    linarith [hsum, hd1]
  have hholder := H.2.2 p.1 0 θ θ (max p.2 0) τ₀ (le_of_lt hp1) le_rfl hθ hθ
    ⟨le_max_right _ _, hmaxT⟩ ⟨hτ₀.1, le_of_lt hτ₀.2⟩
  rw [Real.dist_eq]
  calc |h p.1 θ (max p.2 0) - h 0 θ τ₀|
      ≤ N * (|p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀|) ^ α := hholder
    _ < ε := hbound _ hsum0 hsumlt

/-! ## The general reduction -/

/-- **The general reduction.**  For a family `G` carrying the primitive `R5` data on `[0,T]`,
which vanishes identically on the two angular ends, and whose negative-`τ` branch is its own
right-Taylor jet, the `τ`-derivative of `G` has the `R1` limits: it tends to `0` as
`(z,τ) → (0⁺,τ₀)` and it is right-continuous at `τ = 0`. -/
theorem tau_of_r5 {α T : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hT : 0 < T)
    {G Φ : Work.FTS.Galerkin.Fam} (hR5 : Work.FTS.RegPkgGal.R5Parts α T G Φ)
    (hend : ∀ z θ, 0 < z → θ ∈ Work.Spaces.Iθ → (θ = 0 ∨ θ = π / 2) → ∀ s, G z θ s = 0)
    (haff : ∀ z θ s, 0 < z → θ ∈ Work.Spaces.Iθ → s < 0 →
      G z θ s = G z θ 0 + s * derivWithin (fun u => G z θ u) (Set.Ici 0) 0) :
    (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 T,
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => G p.1 θ s) p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun τ => deriv (fun s => G z θ s) τ)
        (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => G z θ s) 0))) := by
  obtain ⟨NJ, hL, hN₀, hN, hNs⟩ := hR5.hJ
  obtain ⟨Nc, hJet⟩ :=
    Work.FTS.RegPkgGal.Der.rhs_jet_of_parts hα hα13 hT hL hN₀ hN hNs hR5.hmb hR5.hmbh
  set R : ℝ → ℝ → ℝ → ℝ := fun τ z θ =>
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) G τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ G τ z θ with hRdef
  have hJetR : Work.FTS.Regularity.Jet α T Nc (fun z θ τ => R τ z θ) := hJet
  have hRz0 : ∀ τ ∈ Set.Icc 0 T, ∀ θ ∈ Work.Spaces.Iθ, R τ 0 θ = 0 := hR5.hRz0
  -- ### The derivative of `G` is the right-hand side, at `max s' 0`
  have hderiv_int : ∀ θ ∈ Work.Spaces.Iθ, 0 < θ → θ < π / 2 → ∀ z : ℝ, 0 < z → ∀ s' : ℝ,
      deriv (fun s => G z θ s) s' = R (max s' 0) z θ := by
    intro θ hθ hθ0 hθ1 z hz s'
    have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
    rcases lt_trichotomy s' 0 with hs | hs | hs
    · -- `s' < 0`: the affine branch of the right-Taylor extension
      have hev : (fun u : ℝ => G z θ u) =ᶠ[𝓝 s']
          (fun u => G z θ 0 + u * derivWithin (fun u => G z θ u) (Set.Ici 0) 0) := by
        filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
        exact haff z θ u hz hθ hu
      rw [hev.deriv_eq, max_eq_right hs.le]
      have hd : HasDerivAt (fun u : ℝ =>
            G z θ 0 + u * derivWithin (fun u => G z θ u) (Set.Ici 0) 0)
          (derivWithin (fun u => G z θ u) (Set.Ici 0) 0) s' := by
        simpa using (((hasDerivAt_id s').mul_const
          (derivWithin (fun u => G z θ u) (Set.Ici 0) 0)).const_add (G z θ 0))
      rw [hd.deriv]
      exact ((hR5.h0 z θ hz hzθ).hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ici 0)
    · -- `s' = 0`: the two-sided equation at `τ = 0`
      subst hs; rw [max_self]; exact (hR5.h0 z θ hz hzθ).deriv
    · -- `s' > 0`: the dynamic equation
      rw [max_eq_left hs.le]
      exact ((hR5.hsol z θ s' hs.le hzθ).hasDerivAt (Ici_mem_nhds hs)).deriv
  constructor
  · -- ### `hjdt`: the joint limit at `z = 0⁺`
    intro θ hθ τ₀ hτ₀
    by_cases hθe : θ = 0 ∨ θ = π / 2
    · -- the angular ends: everything vanishes identically
      refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0:ℝ)))
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [show (fun s => G p.1 θ s) = fun _ => (0:ℝ) from funext (hend p.1 θ hp.1 hθ hθe),
        deriv_const]
    · push Not at hθe
      have hh0 : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθe.1)
      have hh1 : θ < π / 2 := lt_of_le_of_ne hθ.2 hθe.2
      have hlim := tauJetMax hJetR hα hT hθ hτ₀
      rw [hRz0 τ₀ ⟨hτ₀.1, le_of_lt hτ₀.2⟩ θ hθ] at hlim
      refine Filter.Tendsto.congr' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (hderiv_int θ hθ hh0 hh1 p.1 hp.1 p.2).symm
  · -- ### `ht0`: right-continuity of `∂_τ G` at `τ = 0`
    intro θ hθ z hz
    by_cases hθe : θ = 0 ∨ θ = π / 2
    · have hzero : ∀ τ, deriv (fun s => G z θ s) τ = 0 := by
        intro τ
        rw [show (fun s => G z θ s) = fun _ => (0:ℝ) from funext (hend z θ hz hθ hθe),
          deriv_const]
      rw [hzero 0]
      refine Filter.Tendsto.congr'
        (Filter.Eventually.of_forall (fun τ => (hzero τ).symm)) tendsto_const_nhds
    · push Not at hθe
      have hh0 : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθe.1)
      have hh1 : θ < π / 2 := lt_of_le_of_ne hθ.2 hθe.2
      have hval : deriv (fun s => G z θ s) 0 = R 0 z θ := by
        rw [hderiv_int θ hθ hh0 hh1 z hz 0, max_self]
      have hlim := tauJetTau hJetR hα hT hz.le hθ
      rw [hval]
      refine Filter.Tendsto.congr' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      rw [hderiv_int θ hθ hh0 hh1 z hz τ, max_eq_left hτ.le]

theorem tau_cluster {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hSt1 : ∀ S > 0,
      Work.FTS.RegPkgGal.St1Class α S (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∀ S > 0,
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ =>
            deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) p.2)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun τ =>
            deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) τ)
          (nhdsWithin 0 (Set.Ioi (0:ℝ)))
          (nhds (deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0))) := by
  intro S hS
  set G : Work.FTS.Galerkin.Fam := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) with hGdef
  set ΦΦ : Work.FTS.Galerkin.Fam :=
    Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) with hΦdef
  have hR5 : Work.FTS.RegPkgGal.R5Parts α (S + 1) G ΦΦ := by
    rw [hGdef, hΦdef]; exact H5 (S + 1) (by linarith)
  refine tau_of_r5 hα hα13 (by linarith : (0:ℝ) < S + 1) hR5 ?_ ?_
  · -- the angular ends: `G` vanishes identically (from `DynOK'.1.1.vanish`)
    intro z θ hz hθ hθe s
    have hv := hOK.1.1.vanish
    have hg0 : ∀ u, 0 ≤ u → g z θ u = 0 := by
      intro u hu
      rcases hθe with h | h
      · rw [h]; exact (hv u hu z hz.le).1
      · rw [h]; exact (hv u hu z hz.le).2
    have hG_eq : G z θ s = Work.FTS.FinalV2.tauExt g z θ s := by
      rw [hGdef]
      simp only [Work.FTS.FinalV2.gS]
      rw [if_pos hz, if_pos ⟨hθ.1, hθ.2⟩]
    rw [hG_eq]
    by_cases hs : s < 0
    · rw [Work.FTS.FinalV2.tauExt_of_neg g hs]
      have hdw : derivWithin (fun u => g z θ u) (Set.Ici 0) 0 = 0 := by
        have h1 : derivWithin (fun u => g z θ u) (Set.Ici (0:ℝ)) 0
            = derivWithin (Function.const ℝ (0:ℝ)) (Set.Ici 0) 0 :=
          derivWithin_congr (fun u hu => hg0 u hu) (hg0 0 le_rfl)
        rw [h1, derivWithin_const]
        simp
      rw [hg0 0 le_rfl, hdw]; ring
    · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hs)]
      exact hg0 s (not_lt.mp hs)
  · -- the affine branch of `G` for `s < 0` is the right-Taylor jet of `g`
    intro z θ s hz hθ hs
    have hθ0 : 0 ≤ θ := hθ.1
    have hθ1 : θ ≤ π / 2 := hθ.2
    have hG_eq : ∀ u : ℝ, G z θ u = Work.FTS.FinalV2.tauExt g z θ u := by
      intro u
      rw [hGdef]
      simp only [Work.FTS.FinalV2.gS]
      rw [if_pos hz, if_pos ⟨hθ0, hθ1⟩]
    have hG0 : G z θ 0 = g z θ 0 := by
      rw [hG_eq 0, Work.FTS.FinalV2.tauExt_of_nonneg g le_rfl]
    have hdc : derivWithin (fun u => g z θ u) (Set.Ici 0) 0
        = derivWithin (fun u => G z θ u) (Set.Ici 0) 0 := by
      refine derivWithin_congr (f₁ := fun u => g z θ u) (f := fun u => G z θ u) ?_ ?_
      · intro u hu
        exact ((hG_eq u).trans (Work.FTS.FinalV2.tauExt_of_nonneg g hu)).symm
      · exact hG0.symm
    rw [hG_eq s, Work.FTS.FinalV2.tauExt_of_neg g hs, hG0, hdc]

end Work.FTS_RegExport.RXR1
