import Mathlib
import Submission.Work.Drive.PushDisc.chartObligation
import Submission.Work.Drive.PushDisc.signOfCoreDerivative_of_immersion
import Submission.Work.Drive.PushDisc.fingerGraph
import Submission.Work.Drive.PushDisc.smoothChartOfInjOnImmersion
import Submission.Work.Drive.PushDisc.asymAnchor
import Submission.Work.Drive.PushDisc.sheetModel
import Submission.Work.Drive.PushDisc.sheetOneFlatteningData
import Submission.Work.Drive.PushDisc.signWindowOfCore
import Submission.Work.Drive.PushDisc.firstSheet_xyJet_signCoherence

/-!
# The assembly of `ReducedChartObligation` from the *position* of the plain chart

The target `Work.Drive.PushDisc.chartObligationOfConfiguration` asks for
`Nonempty (ReducedChartObligation n f W p₁ p₂ q₁ q₂)` for every configuration of the compact `n ≥ 3`
branch.  This file separates the *geometric inputs* of that construction from the *derivations*.

## The geometric inputs (the hypotheses of `nonempty_reducedChartObligation_of_chartPosition`)

* a plain chart `Φ, Θ` (a global `C^∞` diffeomorphism) with the two double points pinned to the model
  double points `(-1,0,0,0)`, `(1,0,0,0)`;
* the **flat first tube** `U₁`: an open tube around `γ₁` on which `Φ (f x) ∈ sheetA`, containing the
  *straightened* model arc (`hU₁seg`: the closed segment `|x| ≤ 1 + δ₀` is covered by the tube's
  image), avoiding `p₂, q₂`;
* the **finger's position**: an open tube `O` around `γ₂`, disjoint from `U₁`, on which the `(x, v)`
  projection `g` is injective with invertible derivative and whose image covers the window
  `{|x| < X₀, ‖v‖ < R₀}` with `R₀ > 1`;
* the **core's height** `c`: the `v = 0` locus (the finger's spine) has coordinates `(x, c x, 0, 0)`
  (`hspine`), with the sign pattern `hcpos₀` / `hslope` at the two double points — the output of
  `Work.Drive.PushDisc.signOfCoreDerivative_of_immersion` (where `OppositeType` is spent) together
  with the choice of the sign of the model `u`-coordinate;
* the **avoidance** `havoid` of the model disc `asymDisc k c` by the image of the complement of the
  two tubes — the *cleanliness of the Whitney disc* seen in the chart.

## What is derived here

The finger block (`h`, `σ₂`, the graph row, the openness `hW₀o` and the smallness `hW₀W`), the core
rows `hcore`, `hcm`, `hc1`, `hlip`, the negative sign row `hcneg` (from `hslope` and
`exists_window_neg_of_slopes`), the frontier row from `frontier_row_of_graph`, the pin rows `hp₁c`,
`hq₁c`, and the isolation rows `V`, `hVo`, `hVD`, `hVW`, `hVthin` (from `havoid`, with `V` the
complement of the image of the complement of the two tubes — `exists_isolationRows_of_discAvoid`).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The `(x,v)` projection of `Φ ∘ f`** (the finger's base coordinates). -/
noncomputable def fingerProj {k : ℕ}
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) : M → EuclideanSpace ℝ (Fin (k + 1)) :=
  fun z => splitE k ((Φ (f z)).1, (Φ (f z)).2.2.2)

/-- **The isolation rows from the avoidance of the model disc.** -/
theorem exists_isolationRows_of_discAvoid {k : ℕ} [T2Space M] [CompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : Continuous f)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (hΦc : Continuous Φ)
    (U₁ O W : Set M) (c : ℝ → ℝ)
    (hU₁o : IsOpen U₁) (hOo : IsOpen O)
    (hU₁W : U₁ ⊆ W) (hOW : O ⊆ W)
    (havoid : ∀ z : M, z ∉ U₁ → z ∉ O → Φ (f z) ∉ asymDisc k c) :
    ∃ V : Set (Work.Drive.Whitney.Mdl k), IsOpen V ∧ asymDisc k c ⊆ V ∧
      (∀ z : M, Φ (f z) ∈ V → z ∈ W) ∧ (∀ z : M, Φ (f z) ∈ V → z ∈ U₁ ∨ z ∈ O) := by
  have hcompc : IsCompact (Set.univ \ (U₁ ∪ O) : Set M) :=
    isCompact_univ.diff (hU₁o.union hOo)
  refine ⟨(Φ '' (f '' (Set.univ \ (U₁ ∪ O))))ᶜ, ?_, ?_, ?_, ?_⟩
  · exact ((hcompc.image hf).image hΦc).isClosed.isOpen_compl
  · intro ξ hξ hcon
    obtain ⟨y, hy, rfl⟩ := hcon
    obtain ⟨z, hz, rfl⟩ := hy
    exact havoid z (fun h => hz.2 (Or.inl h)) (fun h => hz.2 (Or.inr h)) hξ
  · intro z hz
    have h : z ∈ U₁ ∪ O := by
      by_contra h
      exact hz ⟨f z, ⟨z, ⟨Set.mem_univ z, h⟩, rfl⟩, rfl⟩
    rcases h with h | h
    · exact hU₁W h
    · exact hOW h
  · intro z hz
    by_contra h
    exact hz ⟨f z, ⟨z, ⟨Set.mem_univ z, h⟩, rfl⟩, rfl⟩

/-- **The assembly.** -/
theorem nonempty_reducedChartObligation_of_chartPosition {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂)
    (k : ℕ) (hk : n = k + 1)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y)
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (hpinP : Φ (f p₁) = ((-1 : ℝ), 0, 0, 0)) (hpinQ : Φ (f q₁) = ((1 : ℝ), 0, 0, 0))
    (U₁ : Set M) (hU₁o : IsOpen U₁) (hU₁W : U₁ ⊆ W) (hU₁arc : γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ U₁)
    (hU₁flat : ∀ x : M, x ∈ U₁ → Φ (f x) ∈ Work.Drive.Whitney.sheetA)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hU₁seg : ∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ (f z) = (x, 0, 0, 0))
    (hp₂U₁ : p₂ ∉ U₁) (hq₂U₁ : q₂ ∉ U₁)
    (O : Set M) (hOo : IsOpen O) (hOW : O ⊆ W) (hOarc : γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ O)
    (hOdisj : Disjoint O U₁)
    (hOinj : Set.InjOn (fingerProj (n := n) Φ f) O)
    (hOimm : ∀ z : M, z ∈ O → Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (fingerProj (n := n) Φ f) z))
    (X₀ : ℝ) (hX₀ : 1 < X₀) (R₀ : ℝ) (hR₀ : 1 < R₀)
    (hwin : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| < X₀ → ‖p.2‖ < R₀ →
      ∃ z : M, z ∈ O ∧ fingerProj (n := n) Φ f z = splitE k p)
    (c : ℝ → ℝ) (hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hspine : ∀ x : ℝ, |x| < X₀ → ∀ z : M, z ∈ O →
      fingerProj (n := n) Φ f z = splitE k (x, 0) →
      (Φ (f z)).2.1 = c x ∧ (Φ (f z)).2.2.1 = 0)
    (hcpos₀ : ∀ x : ℝ, |x| < 1 → 0 < c x)
    (hslope : ∃ a b : ℝ, HasDerivAt c a (-1) ∧ HasDerivAt c b 1 ∧ 0 < a ∧ b < 0)
    (havoid : ∀ z : M, z ∉ U₁ → z ∉ O → ∀ x : ℝ, |x| < 1 → ∀ u : ℝ, 0 < u → u < c x →
      (Φ (f z)) ≠ ((x, u, 0, 0) : Work.Drive.Whitney.Mdl k)) :
    Nonempty (Work.Drive.PushDisc.ReducedChartObligation n f W p₁ p₂ q₁ q₂) := by
  subst hk
  classical
  -- ## 0-2. the finger's base projection, its chart, and the finger block
  have hgsm : ContMDiff (𝓡 (k + 1)) (𝓡 (k + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : M => splitE k ((Φ (f z)).1, (Φ (f z)).2.2.2)) := by
    have h1 : ContMDiff (𝓡 (k + 1)) (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : M => Φ (f z)) := hΦsm.contMDiff.comp hf
    have h2 : ContMDiff (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (𝓡 (k + 1))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k => splitE k ((ξ.1, ξ.2.2.2))) := by
      have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : Work.Drive.Whitney.Mdl k =>
          ((ξ.1, ξ.2.2.2) : ℝ × EuclideanSpace ℝ (Fin k))) := by fun_prop
      have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : Work.Drive.Whitney.Mdl k =>
          splitE k ((ξ.1, ξ.2.2.2))) :=
        (LinearEquiv.toContinuousLinearEquiv (splitE k)).contDiff.comp hc
      exact h3.contMDiff
    exact h2.comp h1
  obtain ⟨c₂, hc₂src, hc₂eq, hc₂chart⟩ :=
    exists_smoothChart_of_injOn_immersion_of_nonempty_source
      (fun z : M => splitE k ((Φ (f z)).1, (Φ (f z)).2.2.2)) O hOo
      ⟨p₂, hOarc ⟨0, by norm_num, hγ₂0⟩⟩ hgsm hOinj hOimm
  have hc₂W : c₂.source ⊆ W := by rw [hc₂src]; exact hOW
  have hc₂tgt : c₂.target = c₂ '' O := by
    have h := PartialEquiv.image_source_eq_target (e := c₂.toPartialEquiv)
    rw [hc₂src] at h
    exact h.symm
  set σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M := fun p => c₂.symm (splitE k p) with hσ₂def
  set h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k) :=
    fun p => ((Φ (f (σ₂ p))).2.1, (Φ (f (σ₂ p))).2.2.1) with hhdef
  have hloc : ∀ p : ℝ × EuclideanSpace ℝ (Fin k),
      (|p.1| < X₀ ∧ ‖p.2‖ < R₀) → splitE k p ∈ c₂.target := by
    intro p hp
    obtain ⟨z, hzO, hzg⟩ := hwin p hp.1 hp.2
    rw [hc₂tgt]
    exact ⟨z, hzO, by rw [hc₂eq z hzO]; exact hzg⟩
  have hunpack : ∀ (z : M) (p : ℝ × EuclideanSpace ℝ (Fin k)),
      fingerProj (n := k + 1) Φ f z = splitE k p →
      ((Φ (f z)).1, (Φ (f z)).2.2.2) = p := by
    intro z p hp
    have h2 := congrArg (splitE k).symm hp
    simpa [fingerProj] using h2
  have hgraph : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), splitE k p ∈ c₂.target →
      Φ (f (σ₂ p)) = (p.1, (h p).1, (h p).2, p.2) := by
    intro p hp
    have hsrc : σ₂ p ∈ O := hc₂src ▸ c₂.map_target hp
    have hgc : (fun z : M => splitE k ((Φ (f z)).1, (Φ (f z)).2.2.2)) (σ₂ p) = splitE k p :=
      (hc₂eq (σ₂ p) hsrc).symm.trans (c₂.right_inv hp)
    have hp' : ((Φ (f (σ₂ p))).1, (Φ (f (σ₂ p))).2.2.2) = p := (splitE k).injective hgc
    have hx : (Φ (f (σ₂ p))).1 = p.1 := congrArg Prod.fst hp'
    have hv : (Φ (f (σ₂ p))).2.2.2 = p.2 := congrArg Prod.snd hp'
    exact Prod.ext hx (Prod.ext rfl (Prod.ext rfl hv))
  have hHsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h
      {p : ℝ × EuclideanSpace ℝ (Fin k) | splitE k p ∈ c₂.target} := by
    have hσ₂sm : ContMDiffOn (𝓡 (k + 1)) (𝓡 (k + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (c₂.symm : EuclideanSpace ℝ (Fin (k + 1)) → M) c₂.target := hc₂chart.2
    have h1 : ContMDiffOn (𝓡 (k + 1)) (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u)))
        c₂.target :=
      ContMDiffOn.comp (g := fun z : M => Φ (f z)) (t := Set.univ)
        ((hΦsm.contMDiff.comp hf).contMDiffOn) hσ₂sm (fun u _ => Set.mem_univ (c₂.symm u))
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => Φ (f (c₂.symm u))) c₂.target :=
      (contMDiffOn_iff_contDiffOn).mp h1
    have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin k) => Φ (f (c₂.symm (splitE k p))))
        {p : ℝ × EuclideanSpace ℝ (Fin k) | splitE k p ∈ c₂.target} :=
      h2.comp (splitECLM k).contDiff.contDiffOn (fun p hp => hp)
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun ξ : Work.Drive.Whitney.Mdl k =>
          ((ξ.2.1, ξ.2.2.1) : ℝ × EuclideanSpace ℝ (Fin k))) := by fun_prop
    exact h4.comp_contDiffOn h3
  -- ## 3. the pin rows
  have hgp₂ : fingerProj (n := k + 1) Φ f p₂ = splitE k ((-1 : ℝ), 0) := by
    show splitE k ((Φ (f p₂)).1, (Φ (f p₂)).2.2.2) = splitE k ((-1 : ℝ), 0)
    rw [← hfp, hpinP]
  have hgq₂ : fingerProj (n := k + 1) Φ f q₂ = splitE k ((1 : ℝ), 0) := by
    show splitE k ((Φ (f q₂)).1, (Φ (f q₂)).2.2.2) = splitE k ((1 : ℝ), 0)
    rw [← hfq, hpinQ]
  have hp₂ : σ₂ ((-1 : ℝ), 0) = p₂ := by
    have hcp : c₂ p₂ = splitE k ((-1 : ℝ), 0) :=
      (hc₂eq p₂ (hOarc ⟨0, by norm_num, hγ₂0⟩)).trans hgp₂
    show c₂.symm (splitE k ((-1 : ℝ), 0)) = p₂
    rw [← hcp]
    exact c₂.left_inv (hc₂src ▸ hOarc ⟨0, by norm_num, hγ₂0⟩)
  have hq₂ : σ₂ ((1 : ℝ), 0) = q₂ := by
    have hcp : c₂ q₂ = splitE k ((1 : ℝ), 0) :=
      (hc₂eq q₂ (hOarc ⟨1, by norm_num, hγ₂1⟩)).trans hgq₂
    show c₂.symm (splitE k ((1 : ℝ), 0)) = q₂
    rw [← hcp]
    exact c₂.left_inv (hc₂src ▸ hOarc ⟨1, by norm_num, hγ₂1⟩)
  have hmemP : splitE k ((-1 : ℝ), 0) ∈ c₂.target := by
    rw [hc₂tgt]
    exact ⟨p₂, hOarc ⟨0, by norm_num, hγ₂0⟩,
      (hc₂eq p₂ (hOarc ⟨0, by norm_num, hγ₂0⟩)).trans hgp₂⟩
  have hmemQ : splitE k ((1 : ℝ), 0) ∈ c₂.target := by
    rw [hc₂tgt]
    exact ⟨q₂, hOarc ⟨1, by norm_num, hγ₂1⟩,
      (hc₂eq q₂ (hOarc ⟨1, by norm_num, hγ₂1⟩)).trans hgq₂⟩
  -- ## 4. the core rows
  have hcore : ∀ x : ℝ, |x| < X₀ → h (x, 0) = (c x, 0) := by
    intro x hx
    have hpt : splitE k (x, 0) ∈ c₂.target := hloc (x, 0) ⟨hx, by rw [norm_zero]; linarith [hR₀]⟩
    have hg : fingerProj (n := k + 1) Φ f (σ₂ (x, 0)) = splitE k (x, 0) := by
      have hsrc : σ₂ (x, 0) ∈ O := hc₂src ▸ c₂.map_target hpt
      exact (hc₂eq (σ₂ (x, 0)) hsrc).symm.trans (c₂.right_inv hpt)
    have hsp := hspine x hx (σ₂ (x, 0)) (hc₂src ▸ c₂.map_target hpt) hg
    rw [hhdef]
    exact Prod.ext hsp.1 hsp.2
  have hcm : c (-1) = 0 := by
    have h1 : h (-1, 0) = (c (-1), 0) := hcore (-1) (by norm_num [hX₀])
    have h2 : (h (-1, 0)).1 = 0 := by
      have hg := hgraph ((-1 : ℝ), 0) hmemP
      rw [hp₂] at hg
      have h3 := congrArg (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.1) hg
      rw [← hfp, hpinP] at h3
      exact h3.symm
    rw [h1] at h2
    exact h2
  have hc1 : c 1 = 0 := by
    have h1 : h (1, 0) = (c 1, 0) := hcore 1 (by norm_num [hX₀])
    have h2 : (h (1, 0)).1 = 0 := by
      have hg := hgraph ((1 : ℝ), 0) hmemQ
      rw [hq₂] at hg
      have h3 := congrArg (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.1) hg
      rw [← hfq, hpinQ] at h3
      exact h3.symm
    rw [h1] at h2
    exact h2
  -- ## 5. the sign window and the final window
  obtain ⟨a, b, ha, hb, ha', hb'⟩ := hslope
  obtain ⟨Xg, Xg', hXg, hXg', hneg, -⟩ :=
    exists_window_neg_of_slopes (w := c) hcsm.continuous hcm hc1 ha hb ha' hb' 1 (by norm_num)
  set m : ℝ := min (min X₀ (1 + δ₀)) Xg with hmdef
  have hm1 : 1 < m := lt_min (lt_min hX₀ (by linarith)) hXg
  have hmX₀ : m ≤ X₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmδ : m ≤ 1 + δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmXg : m ≤ Xg := min_le_right _ _
  set X' : ℝ := (1 + m) / 2 with hX'def
  have hX' : 1 < X' := by rw [hX'def]; linarith
  have hX'm : X' < m := by rw [hX'def]; linarith
  have hX'X₀ : X' < X₀ := lt_of_lt_of_le hX'm hmX₀
  have hX'δ : X' < 1 + δ₀ := lt_of_lt_of_le hX'm hmδ
  have hX'Xg : X' < Xg' := lt_of_lt_of_le (lt_of_lt_of_le hX'm hmXg) (le_of_lt hXg')
  have hAsub : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), p ∈ asymReg k X' →
      splitE k p ∈ c₂.target := by
    intro p hp
    exact hloc p ⟨lt_trans hp.1 hX'X₀, lt_trans hp.2 hR₀⟩
  -- ## 6. the finger block rows
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X') :=
    hHsmooth.mono (fun p hp => hAsub p hp)
  have hσ₂row : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2) := by
    intro p hp
    rw [← hΘΦ (f (σ₂ p))]
    congr 1
    exact hgraph p (hAsub p hp)
  have hW₀W : σ₂ '' asymReg k X' ⊆ W := by
    rintro z ⟨p, hp, rfl⟩
    exact hOW (hc₂src ▸ c₂.map_target (hAsub p hp))
  have hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X'') := by
    intro X'' hX'' hX''X'
    have h1 : σ₂ '' asymReg k X'' = c₂.symm '' (splitE k '' asymReg k X'') := by
      ext z; constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨splitE k p, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, hp, rfl⟩
    rw [h1]
    refine OpenPartialHomeomorph.isOpen_image_symm_of_subset_target c₂ ?_ ?_
    · have h2 : asymReg k X'' = Set.Ioo (-X'') X'' ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 := by
        ext p; constructor
        · intro hp
          obtain ⟨h1, h2⟩ := hp
          rw [abs_lt] at h1
          exact ⟨h1, by rwa [Metric.mem_ball, dist_eq_norm, sub_zero]⟩
        · intro hp
          obtain ⟨h1, h2⟩ := hp
          exact ⟨by rw [abs_lt]; exact h1,
            by rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h2; exact h2⟩
      rw [h2]
      exact ((splitECLM k).isOpenMap (splitE k).surjective) _ (isOpen_Ioo.prod Metric.isOpen_ball)
    · rintro y ⟨p, hp, rfl⟩
      exact hloc p ⟨lt_trans (lt_of_lt_of_le hp.1 hX''X') hX'X₀, lt_trans hp.2 hR₀⟩
  -- ## 7. the frontier row
  have hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
      ∀ x ∈ frontier (σ₂ '' asymReg k X''),
        |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1 := by
    intro X'' hX'' hX''X' x hx
    have hsub : Set.Icc (-X'') X'' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
        ⊆ {p : ℝ × EuclideanSpace ℝ (Fin k) | splitE k p ∈ c₂.target} := by
      intro p hp
      exact hloc p ⟨by
        have h := hp.1; rw [Set.mem_Icc] at h
        exact lt_of_le_of_lt (abs_le.mpr ⟨h.1, h.2⟩) (lt_of_le_of_lt hX''X' hX'X₀), by
        have h := hp.2; rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
        exact lt_of_le_of_lt h hR₀⟩
    refine frontier_row_of_graph f Φ σ₂ h X' X'' hX'' hX''X' (hW₀o X'' hX'' hX''X') ?_ ?_ ?_ x hx
    · have h1 : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin k) => splitE k p)
          (Set.Icc (-X'') X'' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :=
        (splitECLM k).continuous.continuousOn.mono (Set.subset_univ _)
      exact (hc₂chart.2.continuousOn).comp' h1 hsub
    · intro p hp q hq hpq
      have hp' := hsub hp
      have hq' := hsub hq
      have h1 : splitE k p = splitE k q :=
        (c₂.right_inv hp').symm.trans ((congrArg c₂ hpq).trans (c₂.right_inv hq'))
      exact (splitE k).injective h1
    · intro p hp
      exact hgraph p (hsub hp)
  -- ## 8. the pin rows
  have hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0) := by rw [← hΘΦ (f p₁), hpinP]
  have hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0) := by rw [← hΘΦ (f q₁), hpinQ]
  -- ## 9. the Lipschitz row
  have hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X', ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖ := by
    set Fl : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k) :=
      fun p => h p - (c p.1, 0) with hFldef
    have hlocopen : IsOpen {p : ℝ × EuclideanSpace ℝ (Fin k) | splitE k p ∈ c₂.target} :=
      c₂.open_target.preimage (splitECLM k).continuous
    have hcsm1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin k) => c p.1) := hcsm.comp contDiff_fst
    have hFlsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl
        {p : ℝ × EuclideanSpace ℝ (Fin k) | splitE k p ∈ c₂.target} := by
      have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × EuclideanSpace ℝ (Fin k) => ((c p.1, 0) : ℝ × EuclideanSpace ℝ (Fin k)))
          {p : ℝ × EuclideanSpace ℝ (Fin k) | splitE k p ∈ c₂.target} := by
        have h2' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
              ((c p.1, 0) : ℝ × EuclideanSpace ℝ (Fin k))) := by
          refine ContDiff.prodMk (hcsm.comp contDiff_fst) contDiff_const
        exact h2'.contDiffOn
      exact ContDiffOn.sub hHsmooth h2
    have hsubwin : Set.Icc (-X') X' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
        ⊆ {p : ℝ × EuclideanSpace ℝ (Fin k) | splitE k p ∈ c₂.target} := by
      intro p hp
      exact hloc p ⟨by
        have h := hp.1; rw [Set.mem_Icc] at h
        exact lt_of_le_of_lt (abs_le.mpr ⟨h.1, h.2⟩) hX'X₀, by
        have h := hp.2; rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
        exact lt_of_le_of_lt h hR₀⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
      ((hFlsm.continuousOn_fderiv_of_isOpen hlocopen (by simp)).mono hsubwin)
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro p hp
    have hbase : ((p.1, 0) : ℝ × EuclideanSpace ℝ (Fin k)) ∈ asymReg k X' :=
      ⟨by simpa using hp.1, by simp⟩
    have hbound : ∀ q ∈ asymReg k X', ‖fderiv ℝ Fl q‖ ≤ max C 0 := by
      intro q hq
      refine le_trans (hC q ?_) (le_max_left _ _)
      exact ⟨by have h := hq.1; rw [abs_lt] at h; exact ⟨le_of_lt h.1, le_of_lt h.2⟩, by
        have h := hq.2; rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_of_lt h⟩
    have hconv : Convex ℝ (asymReg k X') := by
      have hset : asymReg k X' = Set.Ioo (-X') X' ×ˢ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 := by
        ext q; constructor
        · intro hq
          obtain ⟨h1, h2⟩ := hq
          rw [abs_lt] at h1
          exact ⟨h1, by rwa [Metric.mem_ball, dist_eq_norm, sub_zero]⟩
        · intro hq
          obtain ⟨h1, h2⟩ := hq
          exact ⟨by rw [abs_lt]; exact h1,
            by rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h2; exact h2⟩
      rw [hset]
      exact (convex_Ioo _ _).prod (convex_ball _ _)
    have hdiff : ∀ q ∈ asymReg k X', DifferentiableAt ℝ Fl q := by
      intro q hq
      exact (hFlsm.differentiableOn (by simp)).differentiableAt
        (hlocopen.mem_nhds (hAsub q hq))
    have hmvt := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hbase hp
    have hz : Fl (p.1, 0) = 0 := by
      rw [hFldef]
      show h (p.1, 0) - (c p.1, 0) = 0
      rw [hcore p.1 (lt_trans hp.1 hX'X₀)]
      simp
    rw [hz, sub_zero] at hmvt
    have hnorm : ‖p - (p.1, 0)‖ = ‖p.2‖ := by
      have h1 : p - (p.1, 0) = (((0 : ℝ), p.2) : ℝ × EuclideanSpace ℝ (Fin k)) := by
        refine Prod.ext ?_ ?_ <;> simp
      rw [h1, Prod.norm_def]
      simp
    rwa [hnorm] at hmvt
  -- ## 10. the isolation rows
  have hdiscAvoid : ∀ z : M, z ∉ U₁ → z ∉ σ₂ '' asymReg k X' → Φ (f z) ∉ asymDisc k c := by
    intro z hzU hzF hzmem
    have hz1 : |(Φ (f z)).1| ≤ 1 := hzmem.1
    have hz2 : 0 ≤ (Φ (f z)).2.1 := hzmem.2.1
    have hz3 : (Φ (f z)).2.1 ≤ c (Φ (f z)).1 := hzmem.2.2.1
    have hz4 : (Φ (f z)).2.2.1 = 0 := hzmem.2.2.2.1
    have hz5 : (Φ (f z)).2.2.2 = 0 := hzmem.2.2.2.2
    -- the two double points lie on the finger
    have hPinF : p₂ ∈ σ₂ '' asymReg k X' :=
      ⟨((-1 : ℝ), 0), ⟨by constructor <;> norm_num [hX'], by simpa using hp₂⟩⟩
    have hQinF : q₂ ∈ σ₂ '' asymReg k X' :=
      ⟨((1 : ℝ), 0), ⟨by constructor <;> norm_num [hX'], by simpa using hq₂⟩⟩
    by_cases h0 : (Φ (f z)).2.1 = 0
    · -- the arc case: the model arc is covered by the flat tube
      have hξ : Φ (f z) = ((Φ (f z)).1, (0 : ℝ), 0, 0) :=
        Prod.ext rfl (Prod.ext h0 (Prod.ext hz4 hz5))
      obtain ⟨z₁, hz₁U, hz₁eq⟩ := hU₁seg (Φ (f z)).1 (le_trans hz1 (by linarith))
      have hEq : Φ (f z₁) = Φ (f z) := by rw [hz₁eq, hξ]
      have hfEq : f z₁ = f z := by
        have := congrArg Θ hEq
        simpa only [hΘΦ] using this
      have hzW : z ∈ W := by
        by_contra h
        exact hsep z₁ z (hU₁W hz₁U) h hfEq
      rcases hclean z₁ z (hU₁W hz₁U) hzW hfEq with h | h | h | h | h
      · exact hzU (h ▸ hz₁U)
      · exact hzF (h.2.symm ▸ hPinF)
      · exact hp₂U₁ (h.1 ▸ hz₁U)
      · exact hzF (h.2.symm ▸ hQinF)
      · exact hq₂U₁ (h.1 ▸ hz₁U)
    · have hpos : 0 < (Φ (f z)).2.1 := lt_of_le_of_ne hz2 (Ne.symm h0)
      have hlt1 : |(Φ (f z)).1| < 1 := by
        rcases lt_or_eq_of_le hz1 with h | h
        · exact h
        · exfalso
          have hc0 : c (Φ (f z)).1 = 0 := by
            rcases le_total (0 : ℝ) ((Φ (f z)).1) with hge | hle
            · have h2 : (Φ (f z)).1 = 1 := by rw [abs_of_nonneg hge] at h; exact h
              rw [h2, hc1]
            · have h2 : (Φ (f z)).1 = -1 := by
                rw [abs_of_nonpos hle] at h; linarith
              rw [h2, hcm]
          linarith
      rcases lt_or_eq_of_le hz3 with hlt | heq
      · -- the interior of the model disc: the avoidance row
        have hzO' : z ∉ O := by
          intro hzO'
          have hgz : fingerProj (n := k + 1) Φ f z
              = splitE k ((Φ (f z)).1, (Φ (f z)).2.2.2) := rfl
          have hcz : splitE k ((Φ (f z)).1, (Φ (f z)).2.2.2) = c₂ z :=
            ((hc₂eq z hzO').trans hgz).symm
          refine hzF ⟨((Φ (f z)).1, (Φ (f z)).2.2.2),
            ⟨lt_of_le_of_lt hz1 hX', by rw [hz5, norm_zero]; norm_num⟩, ?_⟩
          show c₂.symm (splitE k ((Φ (f z)).1, (Φ (f z)).2.2.2)) = z
          rw [hcz]
          exact c₂.left_inv (hc₂src ▸ hzO')
        exact havoid z hzU hzO' (Φ (f z)).1 hlt1
          ((Φ (f z)).2.1) hpos hlt (Prod.ext rfl (Prod.ext rfl (Prod.ext hz4 hz5)))
      · -- the spine of the model disc: the tube point
        obtain ⟨z₂, hz₂O, hz₂g⟩ := hwin ((Φ (f z)).1, 0) (lt_trans hlt1 hX₀)
          (by rw [norm_zero]; linarith [hR₀])
        have hsp := hspine ((Φ (f z)).1) (lt_trans hlt1 hX₀) z₂ hz₂O hz₂g
        have hun := hunpack z₂ ((Φ (f z)).1, 0) hz₂g
        have hEq : Φ (f z₂) = Φ (f z) :=
          Prod.ext (congrArg (fun w : ℝ × EuclideanSpace ℝ (Fin k) => w.1) hun)
            (Prod.ext (hsp.1.trans heq.symm) (Prod.ext (hsp.2.trans hz4.symm)
              ((congrArg (fun w : ℝ × EuclideanSpace ℝ (Fin k) => w.2) hun).trans hz5.symm)))
        have hfEq : f z₂ = f z := by
          have := congrArg Θ hEq
          simpa only [hΘΦ] using this
        have hzW : z ∈ W := by
          by_contra h
          exact hsep z₂ z (hOW hz₂O) h hfEq
        -- `z₂` is in the window (its `(x,v)` coordinates are `((Φ (f z)).1, 0)`)
        have hz₂F : z₂ ∈ σ₂ '' asymReg k X' := by
          refine ⟨((Φ (f z)).1, 0), ⟨lt_trans hlt1 hX', by rw [norm_zero]; norm_num⟩, ?_⟩
          have hcz : splitE k ((Φ (f z)).1, 0) = c₂ z₂ :=
            ((hc₂eq z₂ hz₂O).trans hz₂g).symm
          show c₂.symm (splitE k ((Φ (f z)).1, 0)) = z₂
          rw [hcz]
          exact c₂.left_inv (hc₂src ▸ hz₂O)
        rcases hclean z₂ z (hOW hz₂O) hzW hfEq with h | h | h | h | h
        · exact hzF (h ▸ hz₂F)
        · exact hzF (h.2.symm ▸ hPinF)
        · exact hzU (h.2.symm ▸ hU₁arc ⟨0, by norm_num, hγ₁0⟩)
        · exact hzF (h.2.symm ▸ hQinF)
        · exact hzU (h.2.symm ▸ hU₁arc ⟨1, by norm_num, hγ₁1⟩)
  obtain ⟨V, hVo, hVD, hVW, hVthin⟩ :=
    exists_isolationRows_of_discAvoid f hf.continuous Φ hΦsm.continuous U₁
      (σ₂ '' asymReg k X') W c hU₁o (hW₀o X' hX' le_rfl) hU₁W hW₀W hdiscAvoid
  -- ## 11. package
  have hcore' : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0) :=
    fun x hx => hcore x (lt_trans hx hX'X₀)
  have hcneg' : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0 :=
    fun x h1 h2 => hneg x h1 (lt_trans h2 hX'Xg)
  exact ⟨hfp, hfq, hclean, k, rfl, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, h, hh, σ₂, hσ₂row,
    hp₂, hq₂, hW₀o, hW₀W, c, hcsm, hcore', hlip, hcm, hc1, hcpos₀, hcneg', hfrontier,
    hp₁c, hq₁c, U₁, hU₁o, hU₁flat, V, hVo, hVD, hVW, hVthin⟩

end Work.Drive.PushDisc
