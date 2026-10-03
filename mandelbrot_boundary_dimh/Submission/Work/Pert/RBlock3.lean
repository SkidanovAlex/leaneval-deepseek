import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.coordP_level_eq
import Submission.Work.Pert.tools
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow

/-!
# PERT · `Work.Pert.RBlock3`: end asymptotics of a gate coordinate and the level identity

Two elementary bricks of the R-block of `pert2` (see `NOTES_pert2_session8.md`):

* `gate_end_asymptotics` — the `FatouEnds` conjunct of `hF` projected onto the gate `Qm Ξ α`
  (both ends; the lower end with the general translation `ρ` of `liftF_lower_ends`).  This is
  what supplies the constants `c₋`/`c₊` of (A.4.1) and the end limits needed by
  `retOf_sub_id_tendsto_upper`/`..._lower_bdd` and by `mean_le_of_periodic_close`.
* `PhiP_invOn_iterate` — the *level identity* `Φp (τ⁻¹ (f^[m] (τ ς))) = Φp ς + m` along a legal
  walk: `τ` and `f`, `F` intertwine (`τ (F z) = f (τ z)`), so the chosen preimage of
  `f^[m] (τ ς)` in `Q` is `F^[m] ς`, and the iterated Abel equation finishes.  This is the
  identity that identifies the crux's residual `Φp (ζ_w) - m - d.E w` with `Ẽ_f(w) - d.E w`
  at the level-`0` points of the gate.
* `ParabData.E_upper_tendsto` / `ParabData.E_lower_tendsto` — the two end limits of `d.E` in the
  exact shape `norm_le_periodic_ends_local` wants.
-/

namespace Work.Pert

open MandelDim Complex Set Filter Metric
open scoped Topology

noncomputable section

/-- **The end asymptotics of a Fatou coordinate on the gate `Qm Ξ α`.**  Both conclusions are the
corresponding branches of `MandelDim.FatouEndsL1` (equivalently `FatouEnds`) instantiated at
`Q = Qm Ξ α = Qreg (some (Ξ - 1/α)) (some (-Ξ))`, with `ρ = 1` at the upper end and the lower end
translation `ρ` supplied by the caller (for the perturbed lift this is
`Work.Pert.liftF_lower_ends`'s `ρ`, `‖ρ - 1‖ ≤ 1/32`). -/
theorem gate_end_asymptotics {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ} {Φ : ℂ → ℂ}
    (hF : MandelDim.FatouStatement) (hΞ : 0 < Ξ)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φ (Work.Pert.Qm Ξ α))
    (hdecU : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Work.Pert.Qm Ξ α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)))
    (hdecL : ∃ (ρ : ℂ) (M κ Y : ℝ), ‖ρ - 1‖ ≤ 1 / 32 ∧ 0 < M ∧ 0 < κ ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y →
        ‖Work.Pert.liftF u σ α z - (z + ρ)‖ ≤ M * Real.exp (κ * z.im)) :
    (∃ c : ℂ, ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, Y' < z.im →
        |z.re - x| ≤ 2 → ‖Φ z - z - c‖ < ε) ∧
    (∃ (ρ c : ℂ), ‖ρ - 1‖ ≤ 1 / 32 ∧ ∀ x : ℝ, ∀ ε > 0, ∃ Y' : ℝ,
        ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y' → |z.re - x| ≤ 2 → ‖Φ z - z / ρ - c‖ < ε) := by
  have hEnds := (MandelDim.fatouL1_of_fatou hF).2.2.2.2.2
  obtain ⟨M, κ, Y, hM, hκ, hdec⟩ := hdecU
  obtain ⟨ρ, M', κ', Y', hρ1, hM', hκ', hdec'⟩ := hdecL
  have hUp := (hEnds (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) (Work.Pert.liftF u σ α) Φ
    (1 : ℂ) M κ Y hQAdm hNT hΦ hκ (by norm_num)).1
    (fun z hz hY => hdec z hz hY)
  have hDn := (hEnds (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) (Work.Pert.liftF u σ α) Φ
    ρ M' κ' Y' hQAdm hNT hΦ hκ' hρ1).2
    (fun z hz hY => hdec' z hz hY)
  have hQm : Work.Pert.Qm Ξ α = MandelDim.Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) := rfl
  constructor
  · obtain ⟨c, hc⟩ := hUp
    rw [hQm]
    refine ⟨c, ?_⟩
    intro x ε hε
    obtain ⟨Y', hY'⟩ := hc x ε hε
    exact ⟨Y', fun z hz h1 h2 => by
      have h := hY' z hz h1 h2
      simpa only [div_one] using h⟩
  · obtain ⟨c, hc⟩ := hDn
    rw [hQm]
    exact ⟨ρ, c, hρ1, fun x ε hε => hc x ε hε⟩

/-- **The level identity.**  If `τ ∘ F = f ∘ τ` on `Q'`, the walk `F^[j] ς ∈ Q'` is legal for
`j ≤ m` with the endpoint in the subgate `Q ⊆ Q'`, `Φp` satisfies the Abel equation on `Q'`, and `τ`
is injective on `Q`, then the chosen `τ`-preimage in `Q` of `f^[m] (τ ς)` is `F^[m] ς` and `Φp` of it
is `Φp ς + m`.  (Two sets, because the *preimage* is taken in the small subgate `Qp'` while the walk
and the Abel equation live on the whole gate `Qp Ξ α`.) -/
theorem PhiP_invOn_iterate {f F τ Φp : ℂ → ℂ} {Q Q' : Set ℂ} {ς : ℂ} {m : ℕ}
    (hinjτ : Set.InjOn τ Q)
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Q')
    (hτF : ∀ z ∈ Q', τ (F z) = f (τ z))
    (habel : ∀ z ∈ Q', F z ∈ Q' → Φp (F z) = Φp z + 1)
    (hFm : F^[m] ς ∈ Q) :
    Φp (Work.Pert.invOn τ Q (f^[m] (τ ς))) = Φp ς + (m : ℂ) := by
  have h1 : τ (F^[m] ς) = f^[m] (τ ς) := tau_walk_iterate hwalk hτF
  have h2 : Work.Pert.invOn τ Q (f^[m] (τ ς)) = F^[m] ς :=
    Work.Pert.invOn_eq hinjτ ⟨F^[m] ς, hFm, h1⟩ hFm h1
  rw [h2]
  exact abel_iter hwalk habel

namespace ParabData

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)

/-- **The crux's residual is the horn-map residual.**  Combining `PhiP_invOn_iterate` with the
iterated Abel equation of `Φp` along the walk of `ς` in `Qp Ξ α`: if the whole walk of `ς` stays in
`Qp Ξ α` and its `m`-th point lands in the subgate `Qp'`, then
`Φp (τ⁻¹ (f^[m] (τ ς))) = Φp ς + m`.  This is the identity that identifies the crux's quantity
`Φp (invOn τ Qp' (f^[m] (φ w))) - m` with `Ẽ_f(w) = Φp (invOn Φm Q w)` at a level-`0` point `w` of
the gate (see `NOTES_pert2_session8.md` §4(B)); together with it the crux residual
`< δ/2` becomes `‖Ẽ_f w - d.E w‖ < δ/2`, which supplies both `R_close` on the segments and the
(A.4.4) bound `‖d₁ + 1/α‖ < δ/2`. -/
theorem PhiP_invOn_level {f F τ Φp : ℂ → ℂ} {Ξ : ℝ} {α : ℂ} {Qp' : Set ℂ} {ς : ℂ} {m : ℕ}
    (hinjτ : Set.InjOn τ Qp')
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Work.Pert.Qp Ξ α)
    (hτF : ∀ z ∈ Work.Pert.Qp Ξ α, τ (F z) = f (τ z))
    (hAbel : ∀ z ∈ Work.Pert.Qp Ξ α, F z ∈ Work.Pert.Qp Ξ α → Φp (F z) = Φp z + 1)
    (hFm : F^[m] ς ∈ Qp') :
    Φp (Work.Pert.invOn τ Qp' (f^[m] (τ ς))) = Φp ς + (m : ℂ) :=
  PhiP_invOn_iterate (Q := Qp') (Q' := Work.Pert.Qp Ξ α) hinjτ hwalk hτF hAbel hFm

/-- The upper-end limit of `d.E - id` is `0` ((4.1.5) normalisation). -/
theorem E_upper_tendsto : Filter.Tendsto (fun w : ℂ => d.E w - w)
    (Filter.comap Complex.im Filter.atTop) (nhds 0) := d.E_upper

/-- The lower-end limit of `d.E - id` exists. -/
theorem E_lower_tendsto : ∃ cl : ℂ, Filter.Tendsto (fun w : ℂ => d.E w - w)
    (Filter.comap Complex.im Filter.atBot) (nhds cl) := d.E_lower

end ParabData

/-- **`φ_f ∘ R̃_f = φ_f`** — the exact identity (4.3.4) of Shishikura, in its abstract form for
`φ_f = τ ∘ Φ⁻¹` and `R̃_f = Φ ∘ T_f ∘ Φ⁻¹` (`Work.Pert.retOf`).  The whole content is the
periodicity `τ ∘ T_f = τ` of the covering map; this is what drives the orbit relation
`PertData.orbit` (through `Work.Pert.orbit_reduce`). -/
theorem comp_retOf_eq {τ Φ : ℂ → ℂ} {Q : Set ℂ} {α : ℂ} {w : ℂ}
    (hinj : Set.InjOn Φ Q)
    (hτT : ∀ x : ℂ, τ (Work.Pert.Tt α x) = τ x)
    (hw : ∃ ζ ∈ Q, Φ ζ = w)
    (hTw : Work.Pert.Tt α (Work.Pert.invOn Φ Q w) ∈ Q) :
    τ (Work.Pert.invOn Φ Q (Work.Pert.retOf Φ Q α w)) = τ (Work.Pert.invOn Φ Q w) := by
  set ς : ℂ := Work.Pert.invOn Φ Q w with hς
  have hςQ : ς ∈ Q := Work.Pert.invOn_mem hw
  have hΦς : Φ ς = w := Work.Pert.invOn_spec hw
  have hret : Work.Pert.retOf Φ Q α w = Φ (Work.Pert.Tt α ς) :=
    Work.Pert.retOf_eq hinj hw hςQ hΦς
  rw [hret, Work.Pert.invOn_eq hinj ⟨Work.Pert.Tt α ς, hTw, rfl⟩ hTw rfl, hτT ς]

/-- **`1`-periodicity of the horn map.**  With `Φm`, `Φp` both Abelian for the same `F` on `Q` and
`F` mapping the gate into itself, the horn map `w ↦ Φp (Φm⁻¹ w)` satisfies
`Ẽ(w+1) = Ẽ(w) + 1`: `Φm⁻¹(w+1) = F (Φm⁻¹ w)` by injectivity of `Φm`, and the Abel equation for
`Φp` finishes.  This is what lifts a *window* statement about the horn map (correction (C1) of
`NOTES_pert2_session8.md`) to a statement on the whole end, and hence what makes the `∫`-route of
§6 available. -/
theorem hornmap_add_one {F Φm Φp : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hinj : Set.InjOn Φm Q)
    (hAbm : ∀ z ∈ Q, F z ∈ Q → Φm (F z) = Φm z + 1)
    (hAbp : ∀ z ∈ Q, F z ∈ Q → Φp (F z) = Φp z + 1)
    (hw : ∃ z ∈ Q, Φm z = w)
    (hFQ : F (Work.Pert.invOn Φm Q w) ∈ Q) :
    Φp (Work.Pert.invOn Φm Q (w + 1)) = Φp (Work.Pert.invOn Φm Q w) + 1 := by
  set ς : ℂ := Work.Pert.invOn Φm Q w with hς
  have hςQ : ς ∈ Q := Work.Pert.invOn_mem hw
  have hΦς : Φm ς = w := Work.Pert.invOn_spec hw
  have hΦFς : Φm (F ς) = w + 1 := by rw [hAbm ς hςQ hFQ, hΦς]
  have hinv : Work.Pert.invOn Φm Q (w + 1) = F ς :=
    Work.Pert.invOn_eq hinj ⟨F ς, hFQ, hΦFς⟩ hFQ hΦFς
  rw [hinv, hAbp ς hςQ hFQ]

/-- **`φ_f` at a level-`0` point of the gate.**  If `w` lies in the image `Φ '' Q` then its
minimal level is `0` and `coordP f Df τ Φ Q w = τ (invOn Φ Q w)` — i.e. `φ_f = τ ∘ Φ⁻¹` there.
This is the bridge between the gate coordinate `Φ` and the maximal-domain coordinate `coordP`. -/
theorem coordP_eq_tauC_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hinj : Set.InjOn Φ Q) (hw : w ∈ Φ '' Q) :
    coordP f Df τ Φ Q w = τ (Work.Pert.invOn Φ Q w) := by
  classical
  have hgood : GoodP f Df τ Φ Q w := goodP_of_mem_image hw
  have hm : mIdxP f Df τ Φ Q w = 0 := by
    refine le_antisymm ?_ (Nat.zero_le _)
    refine mIdxP_le hgood (n := 0) ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    simpa using hw
  rw [coordP_self, hm]
  simp only [Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero, Work.Pert.seedP]

/-- **The datum-side regularity of `d.E` above its height.**  For `y > d.η₀`, the half plane
`{y ≤ Im w}` lies in `d.DE` (`d.ends_sub`), so `d.E = d.Φ ∘ d.φ` is holomorphic there, is
`1`-equivariant (`ParabData.E_add_one`), and has the upper-end limit `d.E w - w → 0`.  These are the
three inputs of `Work.Pert.norm_le_periodic_ends_local` / `mean_le_periodic_close` at the datum side
and of the `∫`-route of `NOTES_pert2_session8.md` §6. -/
theorem ParabData.E_facts {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {y : ℝ}
    (hy : d.η₀ < y) :
    DifferentiableOn ℂ d.E {w : ℂ | y ≤ w.im} ∧
    (∀ w : ℂ, y ≤ w.im → w ∈ d.DE) ∧
    (∀ w : ℂ, y ≤ w.im → d.E (w + 1) = d.E w + 1) ∧
    Filter.Tendsto (fun w : ℂ => d.E w - w) (Filter.comap Complex.im Filter.atTop) (nhds 0) := by
  have hmem : ∀ w : ℂ, y ≤ w.im → w ∈ d.DE := by
    intro w hw
    have h1 : d.η₀ < |w.im| := lt_of_lt_of_le hy (le_trans hw (le_abs_self w.im))
    exact ⟨(d.ends_sub w h1).1, (d.ends_sub w h1).2⟩
  refine ⟨?_, hmem, fun w hw => Work.Pert.ParabData.E_add_one d (hmem w hw), d.E_upper⟩
  have hsub : {w : ℂ | y ≤ w.im} ⊆ d.Dφ := fun w hw => (hmem w hw).1
  have hmap : Set.MapsTo d.φ {w : ℂ | y ≤ w.im} (MandelDim.ParabolicBasin f₀ D₀) :=
    fun w hw => (hmem w hw).2
  exact d.Φ_holo.comp (d.φ_holo.mono hsub) hmap

/-- **The datum-side mean vanishes**: `∫_0^1 (d.E - id) = 0` on any line above `d.η₀`.  This is
the normalisation (4.1.5) of the datum in the form in which the `∫`-route of
`NOTES_pert2_session8.md` §6 uses it: `d.E - id` is `1`-periodic (`E_facts`) with upper-end limit
`0` (`d.E_upper`), so `Work.Pert.intervalIntegral_period_eq_of_tendsto` gives that its horizontal
mean is that limit.  (The periodicity is only available on `{y ≤ Im w}`; the function is extended by
`0` off it, exactly as in `Work.Pert.norm_le_periodic_ends_local`.) -/
theorem ParabData.integral_E_sub_id {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y : ℝ} (hy : d.η₀ < y) :
    ∫ x in (0 : ℝ)..1, (d.E ((x : ℂ) + y * Complex.I) - ((x : ℂ) + y * Complex.I)) = 0 := by
  obtain ⟨hdiffE, hmem, hper, hlim⟩ := Work.Pert.ParabData.E_facts d hy
  set P : ℂ → ℂ := fun w => if y ≤ w.im then d.E w - w else 0 with hP
  have hmain := intervalIntegral_period_eq_of_tendsto (P := P) (L := 0) (y := y) ?_ ?_ ?_
  · rw [← hmain]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hP]
    rw [if_pos (by simp : y ≤ ((x : ℂ) + y * Complex.I).im)]
  · intro M hM
    have h1 : DifferentiableOn ℂ (fun w : ℂ => d.E w - w) {w : ℂ | y ≤ w.im ∧ w.im ≤ M} :=
      (hdiffE.sub differentiableOn_id).mono (fun w hw => hw.1)
    exact h1.congr (fun w hw => by simp only [hP]; rw [if_pos hw.1])
  · intro w
    have him : (w + 1).im = w.im := by simp
    simp only [hP]
    by_cases h : y ≤ w.im
    · rw [if_pos h, if_pos (by rw [him]; exact h)]
      have h2 := hper w h
      linear_combination h2
    · rw [if_neg h, if_neg (by rw [him]; exact h)]
  · refine Tendsto.congr' ?_ hlim
    refine Filter.eventually_comap.mpr (Filter.eventually_atTop.mpr ⟨y, fun b hb w hwb => ?_⟩)
    simp only [hP]
    rw [if_pos (by rw [hwb]; exact hb)]

/-! ## Lifting a *window* statement to the whole end -/

/-- **A `1`-periodic function whose limit is known on one period window has that limit on the whole
end.**  This is the bridge correction (C1) of `NOTES_pert2_session8.md` demands: the coverage of
the gate image is only available for `0 ≤ Re w ≤ 1` (`Qm Ξ α` is a cone, `Re < Im - Ξ`, so its
image cannot contain a full tail in `im`), but every quantity whose end limit is wanted in the
R-block is `1`-periodic — `R (w+1) = R w + 1` (`R_equiv`), `Ẽ_f (w+1) = Ẽ_f w + 1`
(`hornmap_add_one`) — so the difference to the identity is periodic and the window suffices. -/
theorem tendsto_upperEnd_of_window {D : ℂ → ℂ} {L : ℂ}
    (hper : ∀ w : ℂ, D (w + 1) = D w)
    (hwin : ∀ ε > 0, ∃ Y : ℝ, ∀ w : ℂ, Y ≤ w.im → 0 ≤ w.re → w.re ≤ 1 → ‖D w - L‖ < ε) :
    Filter.Tendsto D (Filter.comap Complex.im Filter.atTop) (nhds L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Y, hY⟩ := hwin ε hε
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨Y, fun b hb w hwb => ?_⟩
  -- `D` is invariant under every integer translation
  have hnat : ∀ m : ℕ, D (w + (m : ℂ)) = D w := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, ← add_assoc, hper, ih]
  have hint : ∀ m : ℕ, D (w - (m : ℂ)) = D w := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h := hper (w - ((k : ℕ) : ℂ) - 1)
      have h2 : w - ((k : ℕ) : ℂ) - 1 + 1 = w - ((k : ℕ) : ℂ) := by ring
      rw [h2] at h
      rw [Nat.cast_succ, show w - (((k : ℕ) : ℂ) + 1) = w - ((k : ℕ) : ℂ) - 1 by ring]
      exact h.symm.trans ih
  have hiter : ∀ n : ℤ, D (w + (n : ℂ)) = D w := by
    intro n
    by_cases h : 0 ≤ n
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
      exact hnat m
    · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero (not_le.mp h)
      rw [show ((Int.negSucc m : ℤ) : ℂ) = -(((m + 1 : ℕ) : ℂ)) by push_cast; ring]
      rw [show w + -(((m + 1 : ℕ) : ℂ)) = w - (((m + 1 : ℕ) : ℂ)) by ring]
      exact hint (m + 1)
  -- shift `w` by the integer taking its real part into `[0,1]`
  set n : ℤ := ⌈-w.re⌉ with hn
  have hle : -w.re ≤ (n : ℝ) := Int.le_ceil _
  have hlt : (n : ℝ) < -w.re + 1 := Int.ceil_lt_add_one _
  have hrec : (w + (n : ℂ)).re = w.re + (n : ℝ) := by simp
  have hre : 0 ≤ (w + (n : ℂ)).re ∧ (w + (n : ℂ)).re ≤ 1 := by
    rw [hrec]; constructor <;> linarith
  have him : (w + (n : ℂ)).im = w.im := by simp
  rw [← hiter n]
  simpa only [dist_eq_norm] using
    hY (w + (n : ℂ)) (by rw [him, hwb]; exact hb) hre.1 hre.2

end

end Work.Pert
