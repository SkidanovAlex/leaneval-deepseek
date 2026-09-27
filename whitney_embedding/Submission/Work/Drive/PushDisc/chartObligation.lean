import Mathlib
import Submission.Work.Drive.PushDisc.hisoOfModelDisc
import Submission.Work.Drive.Whitney.whitneyDiscSmooth
import Submission.Work.Drive.PushDisc.arcInjOnOfHclean

/-!
# The single chart-construction obligation of the compact `n ≥ 3` case

Everything except the *construction* of the chart of the Whitney disc is now proved: the bridge
`nonempty_asymChartData_of_windowData` to `AsymChartData`, the `hiso` half
(`nonempty_windowChartData_of_isolation`, `nonempty_windowChartData_of_disc`), the assembly
`nonempty_windowChartData_of_rows`, and the reduction `asymChartAll_of_windowChartAll` to
`HasPushSignedSmooth`.  This file bundles the remaining rows — the rows the chart construction
produces, with `hU₁row` (the flat first-sheet tube) and `hVthin` (the isolation) folded in — into the
single structure `ChartObligation`, and reduces `WhitneyChartWindowAll n M` to it.

So the compact `n ≥ 3` case is:

    (∀ configuration, Nonempty (ChartObligation n f W p₁ p₂ q₁ q₂))
      ⟹ WhitneyChartWindowAll n M          (`whitneyChartWindowAll_of_chartObligationAll`)
      ⟹ AsymChartAll n M                   (PROVED, `asymChartAll_of_windowChartAll`)
      ⟹ HasPushSignedSmooth n M            (PROVED, `hasPushSignedSmooth_of_asymChartAll`).

Nothing else is left.  The fields of `ChartObligation` are exactly the rows of the chart that have to
be *constructed* (`D`, `Dm`, `hDm`, `hDclean` are kept as fields too, since they are the frame's
business; they can be folded away entirely with `whitneyDiscSmooth`, see
`Drive/PushDisc/NOTES_hisoHalf_S78.md`).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set

/-- **The rows the chart construction of the Whitney disc has to produce.**  All the mechanical rows
(the model disc's cleanliness `hDclean`, the `hiso` row, and the bridge to `AsymChartData`) are
*proved* from these, so `ChartObligation` is the exact remaining obligation of the compact `n ≥ 3`
case. -/
structure ChartObligation (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  hfp : f p₁ = f p₂
  hfq : f q₁ = f q₂
  hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
    y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁)
  k : ℕ
  hk : n = k + 1
  X' : ℝ
  hX' : 1 < X'
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k
  Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y, Θ (Φ y) = y
  hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ
  h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)
  hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X')
  σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2)
  hp₂ : σ₂ ((-1 : ℝ), 0) = p₂
  hq₂ : σ₂ ((1 : ℝ), 0) = q₂
  hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X'')
  hW₀W : σ₂ '' asymReg k X' ⊆ W
  c : ℝ → ℝ
  hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0)
  hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X', ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖
  hcm : c (-1) = 0
  hc1 : c 1 = 0
  hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x
  hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0
  hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
    ∀ x ∈ frontier (σ₂ '' asymReg k X''),
      |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1
  hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)
  hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0)
  /-- the model Whitney disc (as a map into the model space) -/
  D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))
  Dm : ℝ × ℝ → Work.Drive.Whitney.Mdl k
  hDm : ∀ p : ℝ × ℝ, Dm p = Φ (D p)
  /-- **the cleanliness of the disc** (the interior of the disc's image misses `f '' M`) -/
  hDclean : ∀ z : M, f z ∉ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
  /-- **the flat first-sheet tube** (`hU₁row` folded in): an open tube around the first sheet's arc
  whose image lies in the plane `{y = 0, v = 0}` -/
  U₁ : Set M
  hU₁o : IsOpen U₁
  hU₁row : ∀ x : M, x ∈ U₁ →
    Φ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
  V : Set (Work.Drive.Whitney.Mdl k)
  hVo : IsOpen V
  hVD : asymDisc k c ⊆ V
  hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W
  /-- **the isolation row** (`hVthin` folded in): the preimages of the model neighbourhood `V` lie in
  the flat tube or on the finger.  This is the row produced by
  `Work.Drive.PushDisc.exists_isolation_of_whitneyDisc` together with a thin `V`. -/
  hVthin : ∀ z : M, Φ (f z) ∈ V → z ∈ U₁ ∨ z ∈ σ₂ '' asymReg k X'

/-- **The chart rows give the chart.**  This is the whole remaining content of the compact `n ≥ 3`
case, in one line: the `hiso` half (`mem_cover_of_tubes` + `not_mem_modelDisc_image` +
`hiso_of_modelDisc`), assembled by `nonempty_windowChartData_of_isolation`. -/
theorem nonempty_windowChartData_of_chartObligation {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W : Set M} {p₁ p₂ q₁ q₂ : M}
    (h : ChartObligation n f W p₁ p₂ q₁ q₂) :
    Nonempty (WhitneyChartWindowData n f W p₁ p₂ q₁ q₂) := by
  obtain ⟨hfp, hfq, hclean, k, hk, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, hfun, hh, σ₂, hσ₂,
    hp₂, hq₂, hW₀o, hW₀W, c, hcsm, hcore, hlip, hcm, hc1, hcpos, hcneg, hfrontier, hp₁c, hq₁c,
    D, Dm, hDm, hDclean, U₁, hU₁o, hU₁row, V, hVo, hVD, hVW, hVthin⟩ := h
  subst hk
  exact nonempty_windowChartData_of_isolation (n := k + 1) f W p₁ p₂ q₁ q₂ hfp hfq hclean k rfl X'
    hX' Φ Θ hΦsm hΘsm hΘΦ hΦΘ hfun hh σ₂ hσ₂ hp₂ hq₂ hW₀o hW₀W c hcsm hcore hlip hcm hc1
    hcpos hcneg hfrontier hp₁c hq₁c D Dm hDm hDclean U₁ hU₁row V hVo hVD hVW hVthin

/-- **The chart construction for every configuration of the target.** -/
def ChartObligationAll (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
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
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Nonempty (ChartObligation n f W p₁ p₂ q₁ q₂)

/-- **The collapse**: the single chart-construction obligation implies `WhitneyChartWindowAll`. -/
theorem whitneyChartWindowAll_of_chartObligationAll {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : ChartObligationAll n M) : WhitneyChartWindowAll n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂
    hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨c⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁
    hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  exact nonempty_windowChartData_of_chartObligation c


/-! ## Folding the model disc away

`ChartObligation` still carries the rows `D`, `Dm`, `hDm`, `hDclean` of the model Whitney disc.  Those
are *not* constructor input: `D` is the smooth Whitney disc of the bigon
(`Work.Drive.Whitney.whitneyDiscSmooth`, PROVED, axiom-clean) and `Dm := Φ ∘ D` is a definition, so
`hDclean` follows from the disc's cleanliness (`not_mem_modelDisc_image`).  `exists_disc_of_bigonData`
extracts the two rows of that disc which are needed; `arcInjOnOfHclean` (delegated) supplies the last
missing hypotheses (`f`-injectivity of the two arcs) from the target's own configuration. -/

/-- **The smooth Whitney disc, as the two rows the chart needs**: a `C^∞` map `D : ℝ × ℝ → ℝ^{2n}`
whose open-region image misses `f '' M`. -/
theorem exists_disc_of_bigonData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγv0 : f (γ₁ 0) = f (γ₂ 0)) (hγv1 : f (γ₁ 1) = f (γ₂ 1))
    (hγ₁injf : Set.InjOn (fun s : ℝ => f (γ₁ s)) (Set.Icc (0 : ℝ) 1))
    (hγ₂injf : Set.InjOn (fun s : ℝ => f (γ₂ s)) (Set.Icc (0 : ℝ) 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D ∧
      D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∩ f '' (Set.univ : Set M) = ∅ := by
  obtain ⟨D, hDsm, -, -, -, -, -, hDclean, -, -⟩ :=
    Work.Drive.Whitney.whitneyDiscSmooth hn f hf himm γ₁ γ₂ hγ₁ hγ₂ hγv0 hγv1 hγ₁injf hγ₂injf
      hγend
  exact ⟨D, hDsm, hDclean⟩


/-- **The chart rows, with the disc rows folded away.**  This is the same list of chart-construction
rows as `nonempty_windowChartData_of_isolation`, but the four disc rows (`D`, `Dm`, `hDm`, `hDclean`)
are no longer input: `D` comes from the proved `whitneyDiscSmooth` (whose `f`-injectivity hypotheses on
the two arcs come from `arcInjOnOfHclean`, i.e. from the target's own configuration), `Dm := Φ ∘ D` is
a definition, and `hDclean` is `not_mem_modelDisc_image`.  So the *only* genuine obligations left are
the chart-construction rows. -/
theorem nonempty_chartObligation_of_rows {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (k : ℕ) (hk : n = k + 1) (X' : ℝ) (hX' : 1 < X')
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y, Θ (Φ y) = y) (hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ)
    (h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X'))
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M)
    (hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2))
    (hp₂ : σ₂ ((-1 : ℝ), 0) = p₂) (hq₂ : σ₂ ((1 : ℝ), 0) = q₂)
    (hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X''))
    (hW₀W : σ₂ '' asymReg k X' ⊆ W)
    (c : ℝ → ℝ) (hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0))
    (hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X',
      ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖)
    (hcm : c (-1) = 0) (hc1 : c 1 = 0)
    (hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x)
    (hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0)
    (hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
      ∀ x ∈ frontier (σ₂ '' asymReg k X''),
        |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1)
    (hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0))
    (U₁ : Set M) (hU₁o : IsOpen U₁)
    (hU₁row : ∀ x : M, x ∈ U₁ →
      Φ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0})
    (V : Set (Work.Drive.Whitney.Mdl k)) (hVo : IsOpen V)
    (hVD : asymDisc k c ⊆ V)
    (hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W)
    (hVthin : ∀ z : M, Φ (f z) ∈ V → z ∈ U₁ ∨ z ∈ σ₂ '' asymReg k X') :
    Nonempty (ChartObligation n f W p₁ p₂ q₁ q₂) := by
  subst hk
  obtain ⟨hγ₁injf, hγ₂injf⟩ := arcInjOnOfHclean f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hp₁p₂ hq₁q₂ hclean
  have hγv0 : f (γ₁ 0) = f (γ₂ 0) := by rw [hγ₁0, hγ₂0]; exact hfp
  have hγv1 : f (γ₁ 1) = f (γ₂ 1) := by rw [hγ₁1, hγ₂1]; exact hfq
  obtain ⟨D, hDsm, hDcleanD⟩ := exists_disc_of_bigonData hn f hf himm γ₁ γ₂ hγ₁smooth hγ₂smooth
    hγv0 hγv1 hγ₁injf hγ₂injf hγend
  have hDcl : ∀ z : M, f z ∉ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) := by
    intro z hz
    have hmem : f z ∈ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
        ∩ f '' (Set.univ : Set M) := ⟨hz, ⟨z, Set.mem_univ z, rfl⟩⟩
    rw [hDcleanD] at hmem
    exact hmem
  exact ⟨hfp, hfq, hclean, k, rfl, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, h, hh, σ₂, hσ₂, hp₂, hq₂,
    hW₀o, hW₀W, c, hcsm, hcore, hlip, hcm, hc1, hcpos, hcneg, hfrontier, hp₁c, hq₁c,
    D, fun p => Φ (D p), fun p => rfl, hDcl, U₁, hU₁o, hU₁row, V, hVo, hVD, hVW, hVthin⟩

/-- **The *reduced* chart-construction obligation**: `ChartObligation` with the model disc'i rows
(`D`, `Dm`, `hDm`, `hDclean`) removed.  Those are *not* constructor input: `D` comes from the proved
`Work.Drive.Whitney.whitneyDiscSmooth` (with `arcInjOnOfHclean` supplying the `f`-injectivity of the
two arcs from the configuration), `Dm := Φ ∘ D` is a definition, and `hDclean` is
`not_mem_modelDisc_image` applied downstream.  So this structure is exactly the row list of
`nonempty_chartObligation_of_rows`, i.e. what the chart construction of the Whitney disc has to
produce and nothing else. -/
structure ReducedChartObligation (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  hfp : f p₁ = f p₂
  hfq : f q₁ = f q₂
  hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
    y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁)
  k : ℕ
  hk : n = k + 1
  X' : ℝ
  hX' : 1 < X'
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k
  Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y, Θ (Φ y) = y
  hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ
  h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)
  hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X')
  σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2)
  hp₂ : σ₂ ((-1 : ℝ), 0) = p₂
  hq₂ : σ₂ ((1 : ℝ), 0) = q₂
  hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X'')
  hW₀W : σ₂ '' asymReg k X' ⊆ W
  c : ℝ → ℝ
  hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0)
  hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X', ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖
  hcm : c (-1) = 0
  hc1 : c 1 = 0
  hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x
  hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0
  hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
    ∀ x ∈ frontier (σ₂ '' asymReg k X''),
      |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1
  hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)
  hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0)
  /-- **the flat first-sheet tube** (`hU₁row` folded in): an open tube around the first sheet's arc
  whose image lies in the plane `{y = 0, v = 0}` -/
  U₁ : Set M
  hU₁o : IsOpen U₁
  hU₁row : ∀ x : M, x ∈ U₁ →
    Φ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
  V : Set (Work.Drive.Whitney.Mdl k)
  hVo : IsOpen V
  hVD : asymDisc k c ⊆ V
  hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W
  /-- **the isolation row** (`hVthin` folded in): the preimages of the model neighbourhood `V` lie in
  the flat tube or on the finger.  This is the row produced by
  `Work.Drive.PushDisc.exists_isolation_of_whitneyDisc` together with a thin `V`. -/
  hVthin : ∀ z : M, Φ (f z) ∈ V → z ∈ U₁ ∨ z ∈ σ₂ '' asymReg k X'

/-- **The *reduced* chart construction for every configuration of the target.** -/
def ReducedChartObligationAll (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
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
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Nonempty (ReducedChartObligation n f W p₁ p₂ q₁ q₂)

/-- **The last collapse**: the reduced chart-construction obligation gives `ChartObligationAll`.
Each configuration's reduced rows are turned into `ChartObligation` by
`nonempty_chartObligation_of_rows` (the disc rows `D`, `Dm`, `hDm`, `hDclean` being derived there). -/
theorem chartObligationAll_of_reducedChartObligationAll {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : ReducedChartObligationAll n M) : ChartObligationAll n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂
    hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨c⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁
    hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨hfp', hfq', hclean', k, hk, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, hfun, hh, σ₂, hσ₂,
    hp₂, hq₂, hW₀o, hW₀W, cc, hcsm, hcore, hlip, hcm, hc1, hcpos, hcneg, hfrontier, hp₁c, hq₁c,
    U₁, hU₁o, hU₁row, V, hVo, hVD, hVW, hVthin⟩ := c
  exact nonempty_chartObligation_of_rows hn f hf himm W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁smooth hγ₂smooth
    hp₁p₂ hq₁q₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj hγdisj hγend hfp hfq hclean
    k hk X' hX' Φ Θ hΦsm hΘsm hΘΦ hΦΘ hfun hh σ₂ hσ₂ hp₂ hq₂ hW₀o hW₀W cc hcsm hcore hlip
    hcm hc1 hcpos hcneg hfrontier hp₁c hq₁c U₁ hU₁o hU₁row V hVo hVD hVW hVthin

end Work.Drive.PushDisc
