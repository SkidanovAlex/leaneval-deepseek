import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs

/-!
# PERT · `Work.Pert.DphiP_open`: the maximal domain `Dφ_f` is open (Shishikura A.3/A.4)

`DphiP f Df τ Φ Q` (`Submission.Work.Pert.MaxDom`) is Shishikura's maximal domain of the perturbed
coordinate `φ_f`:

> `w ∈ DphiP f Df τ Φ Q` iff `w - n ∈ Φ '' Q` for some `n ≥ 0` and the `f`-orbit of the seed value
> `φ_f(w - n) = τ (Φ⁻¹ (w - n))` stays in `Df` for `j < n`.

This file proves that it is **open** when `Q` and `Df` are open, `Φ, τ` are holomorphic on `Q`,
`Φ` is injective on `Q` with nowhere vanishing derivative there, and `f` is holomorphic on `Df`.

The proof has three independent pieces.

* The gate image `Φ '' Q` is open: `Φ` is analytic at every `ζ₀ ∈ Q` with `deriv Φ ζ₀ ≠ 0`, so
  (inverse function theorem, `HasStrictDerivAt.map_nhds_eq`) it maps neighbourhoods of `ζ₀` onto
  neighbourhoods of `Φ ζ₀`; no connectedness of `Q` is needed.
* The seed value `seedP τ Φ Q = τ ∘ Φ⁻¹` is continuous on `Φ '' Q` (`seedP_holo` in `MaxDom`).
* For an open `U`, a map `g` continuous on `U` and a map `f` continuous on the open set `Df`, the
  set of `w ∈ U` whose `g`-orbit stays in `Df` for `j < n` steps is open.

Writing `DphiP = ⋃_n A_n` with `A_n = {w | w - n ∈ Φ '' Q, f^[j](seedP(w - n)) ∈ Df (j < n)}` and
pushing the shift `w ↦ w - n` into the last two statements gives the result.

Everything here is elementary: no Fredholm/monodromy input, only the open mapping theorem in the
"nonzero derivative" form.
-/

namespace Work.Pert

open MandelDim Complex Set Filter
open scoped Topology

noncomputable section

/-! ## The gate image is open -/

/-- **The gate image of a locally injective holomorphic map is open.**  If `Q` is open, `Φ` is
holomorphic on `Q` and `deriv Φ ≠ 0` on `Q`, then `Φ '' Q` is open.  (Injectivity is not even
needed: `AnalyticAt` with nonzero derivative is a local homeomorphism, so it maps neighbourhoods of
each `ζ₀ ∈ Q` onto neighbourhoods of `Φ ζ₀`.) -/
theorem isOpen_image_of_deriv_ne_zero {Φ : ℂ → ℂ} {Q : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0) : IsOpen (Φ '' Q) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨ζ₀, hζ₀, rfl⟩
  have hana : AnalyticAt ℂ Φ ζ₀ := hΦ.analyticAt (hQ.mem_nhds hζ₀)
  have hmap := hana.hasStrictDerivAt.map_nhds_eq (hder ζ₀ hζ₀)
  rw [← hmap, Filter.mem_map]
  exact Filter.mem_of_superset (hQ.mem_nhds hζ₀) (fun x hx => ⟨x, hx, rfl⟩)

/-! ## The "orbit stays inside an open set" set is open -/

/-- **The set of starting points whose `g`-orbit under `f` stays in `Df` for `n` steps is open.**
`U` open, `g` continuous on `U`, `Df` open and `f` continuous on `Df` (e.g. `f` holomorphic on the
open `Df`).  This is the elementary induction on `n`: at level `n` the map `f^[n] ∘ g` is
continuous on the level-`n` set, where the first `n` iterates are already known to land in `Df`
where `f` is continuous. -/
theorem isOpen_orbitPreimage {U : Set ℂ} (hU : IsOpen U) {g f : ℂ → ℂ} {Df : Set ℂ}
    (hDf : IsOpen Df) (hf : ContinuousOn f Df) (hg : ContinuousOn g U) :
    ∀ n : ℕ, IsOpen {w : ℂ | w ∈ U ∧ ∀ j < n, (f^[j] ∘ g) w ∈ Df} := by
  -- the iterates `f^[j] ∘ g`, `j ≤ n`, are continuous on the level-`n` set
  have key : ∀ m : ℕ, ContinuousOn (fun w => (f^[m] ∘ g) w)
      {w : ℂ | w ∈ U ∧ ∀ j < m, (f^[j] ∘ g) w ∈ Df} := by
    intro m
    induction m with
    | zero => exact hg.mono (fun w hw => hw.1)
    | succ m ihm =>
      have hmono : {w : ℂ | w ∈ U ∧ ∀ j < m + 1, (f^[j] ∘ g) w ∈ Df} ⊆
          {w : ℂ | w ∈ U ∧ ∀ j < m, (f^[j] ∘ g) w ∈ Df} :=
        fun w hw => ⟨hw.1, fun j hj => hw.2 j (Nat.lt_succ_of_lt hj)⟩
      have hprev := ihm.mono hmono
      have hmap : MapsTo (fun w => (f^[m] ∘ g) w)
          {w : ℂ | w ∈ U ∧ ∀ j < m + 1, (f^[j] ∘ g) w ∈ Df} Df :=
        fun w hw => hw.2 m (Nat.lt_succ_self m)
      have heq : (f ∘ fun w => (f^[m] ∘ g) w) = fun w => (f^[m+1] ∘ g) w := by
        funext w
        simp [Function.comp, Function.iterate_succ_apply']
      have hcomp := hf.comp hprev hmap
      rw [heq] at hcomp
      exact hcomp
  intro n
  induction n with
  | zero =>
    have h0 : {w : ℂ | w ∈ U ∧ ∀ j < 0, (f^[j] ∘ g) w ∈ Df} = U := by
      ext w; constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    rw [h0]; exact hU
  | succ k ih =>
    have hcont : ContinuousOn (fun w => (f^[k] ∘ g) w)
        {w : ℂ | w ∈ U ∧ ∀ j < k, (f^[j] ∘ g) w ∈ Df} := key k
    have hgoal : {w : ℂ | w ∈ U ∧ ∀ j < k + 1, (f^[j] ∘ g) w ∈ Df} =
        {w : ℂ | w ∈ U ∧ ∀ j < k, (f^[j] ∘ g) w ∈ Df} ∩
          (fun w => (f^[k] ∘ g) w) ⁻¹' Df := by
      ext w
      constructor
      · rintro ⟨hwU, hw⟩
        exact ⟨⟨hwU, fun j hj => hw j (Nat.lt_succ_of_lt hj)⟩, hw k (Nat.lt_succ_self k)⟩
      · rintro ⟨⟨hwU, hw⟩, hwk⟩
        refine ⟨hwU, fun j hj => ?_⟩
        rw [Nat.lt_succ_iff] at hj
        by_cases h : j = k
        · rw [h]; exact hwk
        · exact hw j (lt_of_le_of_ne hj h)
    rw [hgoal]
    exact hcont.isOpen_inter_preimage ih hDf

/-! ## The maximal domain is open -/

theorem DphiP_open {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} (hDf : IsOpen Df) (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q) (hτ : DifferentiableOn ℂ τ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0) (hf : DifferentiableOn ℂ f Df) : IsOpen (DphiP f Df τ Φ Q) := by
  have hQimg : IsOpen (Φ '' Q) := isOpen_image_of_deriv_ne_zero hQ hΦ hder
  have hseed : ContinuousOn (seedP τ Φ Q) (Φ '' Q) :=
    (seedP_holo hQ hΦ hτ hinj hder).continuousOn
  have hfcont : ContinuousOn f Df := hf.continuousOn
  -- `DphiP` is the union over the level `n` of the sets `A n`
  have hUnion : DphiP f Df τ Φ Q = ⋃ n : ℕ, {w : ℂ |
      w ∈ ({w : ℂ | w - (n : ℂ) ∈ Φ '' Q}) ∧
      ∀ j < n, (f^[j] ∘ fun w => seedP τ Φ Q (w - (n : ℂ))) w ∈ Df} := by
    ext w
    simp only [mem_DphiP, GoodP, Set.mem_iUnion, Set.mem_ofPred_eq, Function.comp_apply]
  rw [hUnion]
  refine isOpen_iUnion fun n => ?_
  have hUn : IsOpen {w : ℂ | w - (n : ℂ) ∈ Φ '' Q} :=
    hQimg.preimage (continuous_id.sub continuous_const)
  have hgn : ContinuousOn (fun w => seedP τ Φ Q (w - (n : ℂ)))
      {w : ℂ | w - (n : ℂ) ∈ Φ '' Q} :=
    hseed.comp ((continuous_id.sub continuous_const).continuousOn) (fun w hw => hw)
  exact isOpen_orbitPreimage hUn hDf hfcont hgn n

end

end Work.Pert
