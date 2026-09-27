import Mathlib
import Submission.Work.Drive.PushDisc.asymChart

/-!
# `Work.Drive.PushDisc.WhitneyChartData`: the chart data of the Whitney disc

This is the input interface of the compact `n ≥ 3` case of the lead's design audit (2026-09-25,
10:10).  It replaces the earlier attempts at the geometric input (the tangent-plane alignment `O2'`,
the "tiny regime" and the `u`-shear "`O2`-straighten") by the *chart of the Whitney disc*:

* global `C^∞` coordinates `Φ, Θ` of `ℝ^{2n}` onto the model space `Mdl k` (`k = n - 1`);
* the **first sheet** is the flat model sheet `{y = 0, v = 0}`: the tube `U₁ ⊆ W` and its
  parametrisation `σ₁` with `f (σ₁ (x,u)) = Θ (x, 0, u, 0)`; the tube is flat in the plane
  (`hU₁row`) and the two double points are pinned to `(-1,0,0,0)`, `(1,0,0,0)`;
* the **second sheet** (the finger) is a graph over the `(x,v)`-window: `σ₂`, `h`;
* the **core** of the finger is `x ↦ σ₂ (x,0)`, its height `c := x ↦ (h (x,0)).1` is a `C^∞`
  function vanishing at `±1`, **positive** on `(-1,1)` and **negative** on `1 < |x| < X'`
  (this is where the opposite-sign hypothesis `OppositeType` of the bigon is spent);
* `hdisc` — the **disc hypothesis**: the interior of the model disc `{y > 0, y < c x}` is *not*
  met by `f '' M`.  This is the content of the existence of the Whitney disc
  (`Work.Drive.PushDisc.exists_whitneyDisc`, the general-position step) transported into the chart.

## Main results

* `Work.Drive.PushDisc.WhitneyChartData` — the structure.
* `Work.Drive.PushDisc.asymChartData_of_whitneyChart` (delegated) — the chart data gives
  `AsymChartData`, hence (through `Work.Drive.PushDisc.hasAmbientPushData_of_asymChartData`) the
  clause set `Work.Whitney.HasAmbientPushData`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set

/-- **The chart data of the Whitney disc.**  See the module docstring. -/
structure WhitneyChartData (n : ℕ) {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  k : ℕ
  hk : n = k + 1
  /-- the half-width of the `x`-window (the core runs from `p₂` at `x = -1` to `q₂` at `x = 1`) -/
  X' : ℝ
  hX' : 1 < X'
  /-- the coordinates of the ambient space -/
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k
  Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y
  hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ
  /-- the first sheet's tube: open, inside the clean region `W`, flattened onto the plane
  `{y = 0, v = 0}` -/
  U₁ : Set M
  hU₁o : IsOpen U₁
  hU₁W : U₁ ⊆ W
  σ₁ : ℝ × EuclideanSpace ℝ (Fin k) → M
  /-- the parametrisation of the first sheet, on the **bounded** window `|x| ≤ X'`, `‖u‖ ≤ 1`.

  The window *must* be bounded: an unbounded row would force
  `{(x, 0, 0, 0) : x : ℝ} ⊆ Φ '' (f '' M)` (take `u = 0` and use `hΦΘ`), and `Φ '' (f '' M)` is
  compact for compact `M` and continuous `f` — so the structure would be empty for every
  configuration (this was found by machine check, see
  `Submission/Work/Drive/PushDisc/whitneyChartDataWindowTrap.lean`). -/
  hσ₁ : ∀ x : ℝ, |x| ≤ X' → ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ 1 →
    f (σ₁ (x, u)) = Θ (x, 0, u, 0)
  hU₁row : ∀ z : M, z ∈ U₁ → (Φ (f z)).2.1 = 0 ∧ (Φ (f z)).2.2.2 = 0
  /-- the `y = 0` edge of the disc lies in the first sheet's tube -/
  hU₁σ₁ : ∀ x : ℝ, |x| ≤ 1 → σ₁ (x, 0) ∈ U₁
  /-- the two double points on the first sheet, in the flat coordinates -/
  hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)
  hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0)
  /-- the height of the second sheet over the `(x,v)`-window -/
  h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)
  hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X')
  /-- the parametrisation of the finger by the `(x,v)`-coordinates -/
  σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2)
  hp₂ : σ₂ ((-1 : ℝ), 0) = p₂
  hq₂ : σ₂ ((1 : ℝ), 0) = q₂
  /-- the finger is open, uniformly in a shrinking of the window (the assemblies below need to
  shrink `X'` down to a small guard band around `±1`) -/
  hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X'')
  hW₀W : σ₂ '' asymReg k X' ⊆ W
  /-- the height of the core of the finger -/
  c : ℝ → ℝ
  hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0)
  /-- **the second sheet is `L`-Lipschitz in the `v`-direction around the core**: this is the row
  that pulls the pushed points (whose `v`-coordinate is small because the amplitude `l` is supported
  in a thin window) back onto the `(u,v) = (0,0)` disc region controlled by `hdisc` -/
  hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X',
    ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖
  /-- the core vanishes at the two double points, is positive between them and negative outside -/
  hcm : c (-1) = 0
  hc1 : c 1 = 0
  hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x
  hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0
  /-- **the disc hypothesis**: the model disc `{0 < y < c x, |x| < 1}` is disjoint from `f '' M` -/
  hdisc : ∀ x y : ℝ, |x| < 1 → 0 < y → y < c x → ∀ z : M, f z ≠ Θ (x, y, 0, 0)
  /-- the frontier of the finger (for any shrinking of the window) sits on the boundary of the
  `(x,v)`-box: this turns the frontier row `Oo`/`hOfront` of `AsymChartData` into a computation with
  `Work.Drive.PushDisc.exists_asymOo_rows` -/
  hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
    ∀ x ∈ frontier (σ₂ '' asymReg k X''),
      |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1

/-- **The chart of the Whitney disc exists for every configuration of the target.**  This is the
form in which the general-position construction (`Work.Drive.PushDisc.exists_whitneyDisc`, the map
`D : [-1,1] × [0,1] → ℝ^{2n}`) and the framing (`whitneyChart_of_disc`, where the opposite-sign
hypothesis `hsign` is spent) deliver the geometric input of the compact `n ≥ 3` case; the assembly
`Work.Drive.PushDisc.asymChartDataOfWhitneyChart` then converts it into `AsymChartAll`
(see `Work.Drive.PushDisc.asymChartAll_of_whitneyChartAll`). -/
def WhitneyChartAll (n : ℕ) (M : Type*) [TopologicalSpace M]
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
    Nonempty (WhitneyChartData n f W p₁ p₂ q₁ q₂)

end Work.Drive.PushDisc
