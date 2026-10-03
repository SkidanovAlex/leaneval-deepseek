import Mathlib
import Submission.Work.PertCrux.crux_limit_v3
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.Fatou

/-!
# `Work.PertCrux.crux_limit_v3_k0`

`crux_limit_v3_k0` is the crux `Work.PertCrux.crux_limit_v3` with the integer `k` of the residual
clause **deleted**: the conclusion reads

`∃ Φp Qp' m, … ∧ ∀ w ∈ K, ‖Φp (invOn τ Qp' (f^[m] (coordP … w))) - (m:ℂ) - d.E w‖ < δ`.

The consumer (`Submission/Work/Pert/pert2_v2.lean`; see
`Submission/Work/Pert/pert2v2/NOTES_pert2v2_session45.md` §2) needs `k = 0`: on the low band
`R_close` compares the crux residual with `Rlow + 1/α - d.E w`, and `‖(k:ℂ) + 1/α‖` can never be
`< δ/2` unless `k = 0`.

## Why `k` is spurious

The only clause of the `k`-version's conclusion in which `k` occurs is the residual, and there it
occurs as an **additive constant**: `Φp ζ - (m:ℂ) - (k:ℂ) - d.E w`.  Adding a constant to a Fatou
coordinate preserves `MandelDim.IsFatouCoordOn` (see `Work.Pert.MandelDim.IsFatouCoordOn.add_const`
and, below, its mirror image `fatouCoord_sub_const`): differentiability on `Q`, injectivity on `Q`
and the Abel equation `Φ (F z) = Φ z + 1` are each invariant under `Φ ↦ Φ - c`.

Hence, from a solution `(Φp, Qp', m, k)` of the `k`-version, the triple

`(fun z => Φp z - (k:ℂ), Qp', m)`

is a solution of the `k0`-version with the *same* `Qp'`, the *same* `m` and the *same* residual
bound `δ` — the subtracted complex constant is absorbed into `Φp`, and the remaining clauses
(`IsOpen`, `⊆ Qp Ξ' α`, `InjOn (tauC σ α)`, the `F`-closedness of the landing points, and the
orbit/`Df` clause) do not mention `Φp` at all.

Consequently the two statements are **interderivable** (`crux_limit_v3_of_k0` below realises the
trivial direction `k := 0`), so deleting the integer neither weakens nor strengthens the crux; and
the proof of `crux_limit_v3` already ends with `(0 : ℤ)`, i.e. it constructs a witness for the
sharper statement.  This file records that and exposes it.  (The requester's note
`NOTES_pert2v2_session45.md` §2 anticipated a verbatim copy of the `crux_limit_v3` proof; the
argument below is the same mathematics in one step.)

Nothing here is `f`-dependent: the argument is a purely formal, uniform transformation of the
existential witness, so it applies verbatim to each `Ξ' ≥ Ξ₀`. -/

namespace Work.PertCrux

/-- Subtracting a complex constant from a Fatou coordinate preserves the property.  The three
clauses of `MandelDim.IsFatouCoordOn` (differentiability on `Q`, injectivity on `Q`, and the Abel
equation `Φ (F z) = Φ z + 1`) are all invariant under `Φ ↦ Φ - c`.
(Mirror image of `Work.Pert.MandelDim.IsFatouCoordOn.add_const`.) -/
theorem fatouCoord_sub_const {F Φ : ℂ → ℂ} {Q : Set ℂ}
    (h : MandelDim.IsFatouCoordOn F Φ Q) (c : ℂ) :
    MandelDim.IsFatouCoordOn F (fun z => Φ z - c) Q := by
  refine ⟨h.1.sub (differentiableOn_const c), ?_, ?_⟩
  · intro x hx y hy hxy
    exact h.2.1 hx hy (sub_left_inj.mp hxy)
  · intro z hz hFz
    change Φ (F z) - c = (Φ z - c) + 1
    rw [h.2.2 z hz hFz]; ring

theorem crux_limit_v3_k0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    (hsize : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ Metric.ball 0 ρ₀ ⊆ D₀ ∧ 16 * Real.pi < ρ₀ * Ξ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ξ₀ : ℝ, ∀ Ξ' : ℝ, Ξ₀ ≤ Ξ' → Ξ ≤ Ξ' →
    ∃ εc : ℝ, 0 < εc ∧
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.ball 0 (16 * Real.pi / Ξ') ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        (∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) →
        MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ' α) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) →
        ∀ Φm : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ' α) →
          K ⊆ Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) →
          (∀ w ∈ K, ‖Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w
            - d.φ w‖ < εc) →
        ∃ Φp : ℂ → ℂ, ∃ Qp' : Set ℂ, ∃ m : ℕ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φp (Work.Pert.Qp Ξ' α) ∧
          IsOpen Qp' ∧ Qp' ⊆ Work.Pert.Qp Ξ' α ∧ Set.InjOn (Work.Pert.tauC σ α) Qp' ∧
          (∀ w ∈ K, Work.Pert.liftF u σ α (Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
              (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))) ∈ Qp') ∧
          (∀ w ∈ K,
            (∀ j : ℕ, j ≤ m →
              f^[j] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) ∈ Df) ∧
            f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
              ∈ Work.Pert.tauC σ α '' Qp') ∧
          ∀ w ∈ K,
            ‖Φp (Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
                (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
              - (m : ℂ) - d.E w‖ < δ := by
  classical
  -- the crux with the (spurious) integer
  obtain ⟨Ξ₀, hcrux⟩ := crux_limit_v3 d hF hd Ξ hΞ hsize hKc hK (δ := δ) hδ
  refine ⟨Ξ₀, ?_⟩
  intro Ξ' hΞ' hΞΞ'
  obtain ⟨εc, hεc, L, hLc, hLD₀, hLball, δ₀, hδ₀, hblk⟩ := hcrux Ξ' hΞ' hΞΞ'
  refine ⟨εc, hεc, L, hLc, hLD₀, hLball, δ₀, hδ₀, ?_⟩
  intro f Df rr u σ α hNear hf0 hInF1 hα hrr hudiff hub hform hexp hQmball hQpball
    hAdm1 hAdm2 hNTm hNTp Φm hΦm hKD hclose
  obtain ⟨Φp, Qp', m, k, hΦp, hQp'open, hQp'sub, hQp'inj, hFcl, horb, hres⟩ :=
    hblk f Df rr u σ α hNear hf0 hInF1 hα hrr hudiff hub hform hexp hQmball hQpball
      hAdm1 hAdm2 hNTm hNTp Φm hΦm hKD hclose
  -- absorb the integer `k` into the additive constant of `Φp`; every other clause of the
  -- conclusion is unchanged (only the residual mentions `Φp`)
  refine ⟨fun z => Φp z - (k : ℂ), Qp', m,
    fatouCoord_sub_const hΦp (k : ℂ), hQp'open, hQp'sub, hQp'inj, hFcl, horb, ?_⟩
  intro w hw
  have h := hres w hw
  convert h using 2
  ring

/-- The converse direction, machine-checked: `crux_limit_v3_k0` implies `crux_limit_v3`
(take `k := 0`).  Together with the proof of `crux_limit_v3_k0` above this shows that the two
versions of the crux are **interderivable** — the integer of the `k`-version is not a genuine
degree of freedom, only the additive-constant freedom of the Fatou coordinate. -/
theorem crux_limit_v3_of_k0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    (Ξ : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    (hsize : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ Metric.ball 0 ρ₀ ⊆ D₀ ∧ 16 * Real.pi < ρ₀ * Ξ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ξ₀ : ℝ, ∀ Ξ' : ℝ, Ξ₀ ≤ Ξ' → Ξ ≤ Ξ' →
    ∃ εc : ℝ, 0 < εc ∧
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ Metric.ball 0 (16 * Real.pi / Ξ') ⊆ L ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        (∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) →
        MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ' α) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) →
        ∀ Φm : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ' α) →
          K ⊆ Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) →
          (∀ w ∈ K, ‖Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w
            - d.φ w‖ < εc) →
        ∃ Φp : ℂ → ℂ, ∃ Qp' : Set ℂ, ∃ m : ℕ, ∃ k : ℤ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φp (Work.Pert.Qp Ξ' α) ∧
          IsOpen Qp' ∧ Qp' ⊆ Work.Pert.Qp Ξ' α ∧ Set.InjOn (Work.Pert.tauC σ α) Qp' ∧
          (∀ w ∈ K, Work.Pert.liftF u σ α (Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
              (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w))) ∈ Qp') ∧
          (∀ w ∈ K,
            (∀ j : ℕ, j ≤ m →
              f^[j] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w) ∈ Df) ∧
            f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)
              ∈ Work.Pert.tauC σ α '' Qp') ∧
          ∀ w ∈ K,
            ‖Φp (Work.Pert.invOn (Work.Pert.tauC σ α) Qp'
                (f^[m] (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm Ξ' α) w)))
              - (m : ℂ) - (k : ℂ) - d.E w‖ < δ := by
  classical
  obtain ⟨Ξ₀, hcrux⟩ := crux_limit_v3_k0 d hF hd Ξ hΞ hsize hKc hK (δ := δ) hδ
  refine ⟨Ξ₀, ?_⟩
  intro Ξ' hΞ' hΞΞ'
  obtain ⟨εc, hεc, L, hLc, hLD₀, hLball, δ₀, hδ₀, hblk⟩ := hcrux Ξ' hΞ' hΞΞ'
  refine ⟨εc, hεc, L, hLc, hLD₀, hLball, δ₀, hδ₀, ?_⟩
  intro f Df rr u σ α hNear hf0 hInF1 hα hrr hudiff hub hform hexp hQmball hQpball
    hAdm1 hAdm2 hNTm hNTp Φm hΦm hKD hclose
  obtain ⟨Φp, Qp', m, hΦp, hQp'open, hQp'sub, hQp'inj, hFcl, horb, hres⟩ :=
    hblk f Df rr u σ α hNear hf0 hInF1 hα hrr hudiff hub hform hexp hQmball hQpball
      hAdm1 hAdm2 hNTm hNTp Φm hΦm hKD hclose
  exact ⟨Φp, Qp', m, 0, hΦp, hQp'open, hQp'sub, hQp'inj, hFcl, horb, fun w hw => by
    have h := hres w hw
    simpa using h⟩

end Work.PertCrux
