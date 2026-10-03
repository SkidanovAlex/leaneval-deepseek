import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.DphiP_open
import Submission.Work.Pert.coordP_abel
import Submission.Work.Pert.coordP_level_eq

/-!
# PERT · `Work.Pert.coordP_holo`: the maximal-domain coordinate `φ_f` is holomorphic

`Work.Pert.coordP f Df τ Φ Q` (Shishikura (4.2.1)) is defined on the maximal domain
`Work.Pert.DphiP f Df τ Φ Q` (`Submission.Work.Pert.MaxDom`) by

> `φ_f(w) = f^{mIdx(w)} (τ (Φ⁻¹ (w - mIdx(w))))`, `mIdx(w)` the *minimal* legal level of `w`.

The point of this file is that `φ_f` is **holomorphic on its whole domain**, which is not visible
from the formula (the minimal level `mIdx` depends discontinuously-looking on `w`).

The key structural fact (Shishikura A.4) is that at a *fixed* level `n` the definition is a plain
composite: on the level-`n` piece

`AnP n = {w | w - n ∈ Φ '' Q ∧ ∀ j < n, f^[j](seedP (w - n)) ∈ Df}`

(the set of `w` for which `n` is a legal level) one has the closed formula

`φ_f(w) = f^[n] (seedP τ Φ Q (w - n))`

(`coordP_eq_gdP_of_mem`), because `coordP_level_eq` says that the coordinate has the same value at
*any* legal level.  The right-hand side is holomorphic: `seedP` is holomorphic on `Φ '' Q`
(`seedP_holo`), the orbit condition at level `n` puts the whole `f`-orbit of the seed value inside
the open set `Df` where `f` is holomorphic, and `AnP n` is open (`isOpen_AnP`).  Since
`DphiP = ⋃ n, AnP n`, at every point of `DphiP` one is in a fixed level-`n` piece on an open
neighbourhood, so `φ_f` is differentiable there.

Everything is elementary; the only ingredients are `seedP_holo`, `coordP_level_eq` and the openness
of the level pieces.
-/

namespace Work.Pert

open MandelDim Complex Set Filter
open scoped Topology

noncomputable section

/-! ## The level-`n` pieces of the maximal domain -/

/-- **The set of points of `DphiP` having `n` as a legal level**: `w - n ∈ Φ '' Q` and the
`f`-orbit of the seed value `seedP τ Φ Q (w - n)` stays in `Df` for `j < n`.  The maximal domain is
the union of these sets over `n`, and on each of them `φ_f` has the closed formula
`w ↦ f^[n] (seedP τ Φ Q (w - n))`. -/
def AnP (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) (n : ℕ) : Set ℂ :=
  {w | w - (n : ℂ) ∈ Φ '' Q ∧ ∀ j : ℕ, j < n → f^[j] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df}

/-- A point of `AnP n` is in the maximal domain, at the (legal) level `n`. -/
lemma goodP_of_mem_AnP {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {n : ℕ} {w : ℂ}
    (hw : w ∈ AnP f Df τ Φ Q n) : GoodP f Df τ Φ Q w := ⟨n, hw⟩

/-- **Each level-`n` piece is open.**  This is the same `isOpen_orbitPreimage` argument as in
`DphiP_open`: `w ↦ w - n` pulls the open gate image `Φ '' Q` back to an open set, `seedP` is
continuous there, and the set of points whose `f`-orbit stays in the open set `Df` for `n` steps is
open. -/
lemma isOpen_AnP {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hDf : IsOpen Df) (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q)
    (hτ : DifferentiableOn ℂ τ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0)
    (hf : DifferentiableOn ℂ f Df) (n : ℕ) : IsOpen (AnP f Df τ Φ Q n) := by
  have hQimg : IsOpen (Φ '' Q) := isOpen_image_of_deriv_ne_zero hQ hΦ hder
  have hseed : ContinuousOn (seedP τ Φ Q) (Φ '' Q) :=
    (seedP_holo hQ hΦ hτ hinj hder).continuousOn
  have hU : IsOpen {w : ℂ | w - (n : ℂ) ∈ Φ '' Q} :=
    hQimg.preimage (continuous_id.sub continuous_const)
  have hgn : ContinuousOn (fun w => seedP τ Φ Q (w - (n : ℂ)))
      {w : ℂ | w - (n : ℂ) ∈ Φ '' Q} :=
    hseed.comp ((continuous_id.sub continuous_const).continuousOn) (fun w hw => hw)
  have h := isOpen_orbitPreimage hU hDf hf.continuousOn hgn n
  have hset : {w : ℂ | w ∈ {w : ℂ | w - (n : ℂ) ∈ Φ '' Q} ∧
      ∀ j : ℕ, j < n → (f^[j] ∘ fun w => seedP τ Φ Q (w - (n : ℂ))) w ∈ Df} =
      AnP f Df τ Φ Q n := by
    ext w
    simp only [AnP, Set.mem_ofPred_eq, Function.comp_apply]
  rwa [hset] at h

/-! ## The closed formula on a level piece -/

/-- **`φ_f` on a level piece**: if `n` is a legal level of `w` then

`φ_f(w) = f^[n] (seedP τ Φ Q (w - n))`.

Immediate from `coordP_level_eq` (the value of `φ_f` is the same at every legal level) applied to
the legal level `(n, invOn Φ Q (w - n))`. -/
lemma coordP_eq_gdP_of_mem {f : ℂ → ℂ} {Df : Set ℂ} {F τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : Set.InjOn Φ Q) (hAbel : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    {n : ℕ} {w : ℂ} (hw : w ∈ AnP f Df τ Φ Q n) :
    coordP f Df τ Φ Q w = f^[n] (seedP τ Φ Q (w - (n : ℂ))) := by
  obtain ⟨hmem, horb⟩ := hw
  have hex : ∃ ζ ∈ Q, Φ ζ = w - (n : ℂ) := hmem
  have hζ : invOn Φ Q (w - (n : ℂ)) ∈ Q := invOn_mem hex
  have hΦ : Φ (invOn Φ Q (w - (n : ℂ))) = w - (n : ℂ) := invOn_spec hex
  have hn : ∀ j : ℕ, j < n → f^[j] (τ (invOn Φ Q (w - (n : ℂ)))) ∈ Df := by
    intro j hj
    simpa [seedP] using horb j hj
  have hmain := coordP_level_eq (f := f) (Df := Df) (F := F) (τ := τ) (Φ := Φ) (Q := Q)
    hinj hAbel hτF hOrb ⟨n, hmem, horb⟩ hζ hΦ hn
  simpa [seedP] using hmain

/-- **The model function on a level piece is holomorphic.**  On `AnP f Df τ Φ Q n` the map
`w ↦ f^[n] (seedP τ Φ Q (w - n))` is differentiable: `seedP` is holomorphic on the open gate image
and the orbit condition of `AnP n` keeps the `f`-orbit of the seed value inside the open set `Df`,
where `f` is holomorphic (induction on `n`, composing `f` at each step). -/
lemma differentiableAt_gdP {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hDf : IsOpen Df) (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q)
    (hτ : DifferentiableOn ℂ τ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0)
    (hf : DifferentiableOn ℂ f Df) {n : ℕ} {w : ℂ} (hw : w ∈ AnP f Df τ Φ Q n) :
    DifferentiableAt ℂ (fun w => f^[n] (seedP τ Φ Q (w - (n : ℂ)))) w := by
  obtain ⟨hmem, horb⟩ := hw
  have hQimg : IsOpen (Φ '' Q) := isOpen_image_of_deriv_ne_zero hQ hΦ hder
  have hseedD : DifferentiableOn ℂ (seedP τ Φ Q) (Φ '' Q) := seedP_holo hQ hΦ hτ hinj hder
  have hs : DifferentiableAt ℂ (fun w => seedP τ Φ Q (w - (n : ℂ))) w := by
    have h1 : DifferentiableAt ℂ (seedP τ Φ Q) (w - (n : ℂ)) :=
      hseedD.differentiableAt (hQimg.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w - (n : ℂ)) w :=
      differentiableAt_id.sub (differentiableAt_const _)
    exact h1.comp (f := fun w : ℂ => w - (n : ℂ)) w h2
  have key : ∀ j : ℕ, j ≤ n →
      DifferentiableAt ℂ (fun w => f^[j] (seedP τ Φ Q (w - (n : ℂ)))) w := by
    intro j
    induction j with
    | zero => intro _; simpa using hs
    | succ k ih =>
      intro hk1n
      have hk : k < n := by omega
      have hprev : DifferentiableAt ℂ (fun w => f^[k] (seedP τ Φ Q (w - (n : ℂ)))) w :=
        ih (by omega)
      have hpt : f^[k] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df := horb k hk
      have hfk : DifferentiableAt ℂ f (f^[k] (seedP τ Φ Q (w - (n : ℂ)))) :=
        hf.differentiableAt (hDf.mem_nhds hpt)
      have hcomp := hfk.comp (f := fun w => f^[k] (seedP τ Φ Q (w - (n : ℂ)))) w hprev
      convert hcomp using 1
      funext x
      simp [Function.comp_apply, Function.iterate_succ_apply']
  exact key n le_rfl

/-! ## The coordinate is holomorphic on its maximal domain -/

theorem coordP_holo {f : ℂ → ℂ} {Df Q : Set ℂ} {F τ Φ : ℂ → ℂ}
    (hDf : IsOpen Df) (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q)
    (hτ : DifferentiableOn ℂ τ Q) (hinj : Set.InjOn Φ Q)
    (hder : ∀ z ∈ Q, deriv Φ z ≠ 0) (hf : DifferentiableOn ℂ f Df)
    (hAbel : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z))
    (hOrb : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℕ, Φ z' = Φ z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → F^[j] z ∈ Q) ∧ F^[k] z = z')
    (hseed : ∀ u ∈ Φ '' Q, Work.Pert.seedP τ Φ Q u ∈ Df) :
    DifferentiableOn ℂ (Work.Pert.coordP f Df τ Φ Q) (Work.Pert.DphiP f Df τ Φ Q) := by
  intro w hw
  -- `w` has some legal level `n`
  obtain ⟨n, hmem, horb⟩ := mem_DphiP.mp hw
  have hAn : w ∈ AnP f Df τ Φ Q n := ⟨hmem, horb⟩
  -- the level-`n` piece is an open neighbourhood of `w` on which `φ_f` has the closed formula
  have hOpen := isOpen_AnP hDf hQ hΦ hτ hinj hder hf n
  have hev : coordP f Df τ Φ Q =ᶠ[𝓝 w] (fun w => f^[n] (seedP τ Φ Q (w - (n : ℂ)))) :=
    Filter.eventually_of_mem (hOpen.mem_nhds hAn)
      (fun x hx => coordP_eq_gdP_of_mem hinj hAbel hτF hOrb hx)
  have hd := differentiableAt_gdP hDf hQ hΦ hτ hinj hder hf hAn
  exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt

end

end Work.Pert
