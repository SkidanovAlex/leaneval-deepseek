import Mathlib
import Submission.Work.Pert.AsmDefs
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn

/-!
# PERT · `Work.Pert.MaxDom`: the maximal domain of `φ_f` (Shishikura A.4)

`Setup.Dphi` defines the forward extension of the gate image by walks **inside the gate**; that is
strictly smaller than Shishikura's maximal domain and, in particular, does *not* contain the
vertical strip `{|Re w| ≤ 1, |Im w| ≥ y₁}` at the small heights `y₁ > d.η₀` at which
`PertData.Dφ_strip` demands it (see `NOTES_pert2_findings.md` §G).  The present file formalises the
paper's domain (A.3 / A.4, the same shape as `Work.Parab.coordData.exists_CoordData`'s `Good`):

> `Dom(φ_f) = { w | w - n ∈ Φ_{-,f}(𝒬_f^-) for some n ≥ 0, and f^j(φ_f(w-n)) ∈ Dom f, j < n }`,

with the seed value `φ_f(w) = τ_f (Φ_{-,f}⁻¹ w)` on `Φ_{-,f}(𝒬_f^-)`.

* `seedP τ Φ Q w = τ (invOn Φ Q w)` — the seed value on `Φ '' Q`;
* `GoodP f Df τ Φ Q w` — `w - n ∈ Φ '' Q` and the `f`-orbit of the seed value stays in `Df`;
* `mIdxP`/`coordP` — the *minimal* level and the value `f^{mIdx} (seedP (w - mIdx))`;
* `DphiP` — the maximal domain.

Proved here: `seedP` is holomorphic on `Φ '' Q` (`seedP_holo`, from the inverse function theorem,
via `invOn_eventuallyEq_localInverse`), and the elementary level facts `mIdxP_spec`, `mIdxP_le`.
-/

namespace Work.Pert

open MandelDim Complex Set Filter
open scoped Topology

noncomputable section

/-- The seed value of the maximal-domain construction: `τ (Φ⁻¹ w)` on `Φ '' Q`. -/
def seedP (τ Φ : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : ℂ := τ (invOn Φ Q w)

/-- Near a point `Φ ζ₀` of the image, the chosen preimage `invOn Φ Q` agrees with a holomorphic
local inverse `g` of `Φ`; in particular `g` is analytic there and `g (Φ ζ₀) = ζ₀`. -/
theorem invOn_eventuallyEq_localInverse {Φ : ℂ → ℂ} {Q : Set ℂ} (hQ : IsOpen Q)
    (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ Q)
    (hder : deriv Φ ζ₀ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (Φ ζ₀) ∧ g (Φ ζ₀) = ζ₀ ∧
      ∀ᶠ w in 𝓝 (Φ ζ₀), w ∈ Φ '' Q → invOn Φ Q w = g w := by
  have hana : AnalyticAt ℂ Φ ζ₀ := hΦ.analyticAt (hQ.mem_nhds hζ₀)
  let g : ℂ → ℂ := hana.hasStrictDerivAt.localInverse Φ (deriv Φ ζ₀) ζ₀ hder
  have hga : AnalyticAt ℂ g (Φ ζ₀) := hana.analyticAt_localInverse hder
  have hg0 : g (Φ ζ₀) = ζ₀ := by
    have h2 : (hana.hasStrictDerivAt.hasStrictFDerivAt_equiv hder).localInverse Φ _ _
        (Φ ζ₀) = ζ₀ :=
      HasStrictFDerivAt.localInverse_apply_image _
    simpa [g, HasStrictDerivAt.localInverse] using h2
  refine ⟨g, hga, hg0, ?_⟩
  have hleft : ∀ᶠ x in 𝓝 ζ₀, g (Φ x) = x :=
    hana.hasStrictDerivAt.eventually_left_inverse hder
  have hmap : map Φ (𝓝 ζ₀) = 𝓝 (Φ ζ₀) := hana.hasStrictDerivAt.map_nhds_eq hder
  rw [← hmap, eventually_map]
  filter_upwards [hQ.mem_nhds hζ₀, hleft] with x hxQ hgx
  intro _
  have : invOn Φ Q (Φ x) = x := invOn_eq hinj ⟨x, hxQ, rfl⟩ hxQ rfl
  rw [this, hgx]

/-- **The seed value is holomorphic on `Φ '' Q`** (A.4: `φ_f = τ_f ∘ Φ_{-,f}⁻¹` is analytic on
the gate image). -/
theorem seedP_holo {Φ τ : ℂ → ℂ} {Q : Set ℂ} (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q)
    (hτ : DifferentiableOn ℂ τ Q) (hinj : Set.InjOn Φ Q) (hder : ∀ z ∈ Q, deriv Φ z ≠ 0) :
    DifferentiableOn ℂ (seedP τ Φ Q) (Φ '' Q) := by
  intro w₀ hw₀
  obtain ⟨ζ₀, hζ₀, rfl⟩ := hw₀
  obtain ⟨g, hga, hg0, hge⟩ := invOn_eventuallyEq_localInverse hQ hΦ hinj hζ₀ (hder ζ₀ hζ₀)
  have hτz : DifferentiableAt ℂ τ ζ₀ := hτ.differentiableAt (hQ.mem_nhds hζ₀)
  have hcomp : DifferentiableAt ℂ (fun w => τ (g w)) (Φ ζ₀) := by
    rw [← hg0] at hτz
    exact hτz.comp (Φ ζ₀) hga.differentiableAt
  have hev : seedP τ Φ Q =ᶠ[𝓝[Φ '' Q] (Φ ζ₀)] (fun w => τ (g w)) := by
    show ∀ᶠ w in 𝓝[Φ '' Q] (Φ ζ₀), seedP τ Φ Q w = τ (g w)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hge] with w hw hwQ
    rw [seedP, hw hwQ]
  have hpt : seedP τ Φ Q (Φ ζ₀) = τ (g (Φ ζ₀)) := by
    rw [seedP, invOn_eq hinj ⟨ζ₀, hζ₀, rfl⟩ hζ₀ rfl, hg0]
  exact hcomp.differentiableWithinAt.congr_of_eventuallyEq hev hpt

/-! ## The maximal domain (Shishikura A.3/A.4) -/

/-- **Shishikura's maximal domain, condition**: `w - n ∈ Φ '' Q` for some `n ≥ 0`, and the
`f`-orbit of the seed value `τ (Φ⁻¹ (w - n))` stays in `Df` for `j < n`. -/
def GoodP (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : Prop :=
  ∃ n : ℕ, w - (n : ℂ) ∈ Φ '' Q ∧ ∀ j : ℕ, j < n → f^[j] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df

/-- The minimal admissible level of `w`. -/
noncomputable def mIdxP (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : ℕ := by
  classical
  exact if h : GoodP f Df τ Φ Q w then Nat.find h else 0

/-- **`φ_f`** on its maximal domain: `f^{mIdx} (τ (Φ⁻¹ (w - mIdx)))`. -/
noncomputable def coordP (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) : ℂ :=
  f^[mIdxP f Df τ Φ Q w] (seedP τ Φ Q (w - (mIdxP f Df τ Φ Q w : ℂ)))

/-- The maximal domain `Dφ_f`. -/
def DphiP (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) : Set ℂ :=
  {w | GoodP f Df τ Φ Q w}

theorem mem_DphiP {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ} :
    w ∈ DphiP f Df τ Φ Q ↔ GoodP f Df τ Φ Q w := Iff.rfl

/-- The minimal level is admissible. -/
theorem mIdxP_spec {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (h : GoodP f Df τ Φ Q w) :
    w - (mIdxP f Df τ Φ Q w : ℂ) ∈ Φ '' Q ∧
      ∀ j : ℕ, j < mIdxP f Df τ Φ Q w →
        f^[j] (seedP τ Φ Q (w - (mIdxP f Df τ Φ Q w : ℂ))) ∈ Df := by
  classical
  rw [mIdxP, dite_eq_left h]
  exact Nat.find_spec h

/-- The minimal level is minimal. -/
theorem mIdxP_le {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (h : GoodP f Df τ Φ Q w) {n : ℕ}
    (hn : w - (n : ℂ) ∈ Φ '' Q ∧
      ∀ j : ℕ, j < n → f^[j] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df) :
    mIdxP f Df τ Φ Q w ≤ n := by
  classical
  rw [mIdxP, dite_eq_left h]
  exact Nat.find_min' h hn

theorem coordP_self (f : ℂ → ℂ) (Df : Set ℂ) (τ Φ : ℂ → ℂ) (Q : Set ℂ) (w : ℂ) :
    coordP f Df τ Φ Q w = f^[mIdxP f Df τ Φ Q w]
      (seedP τ Φ Q (w - (mIdxP f Df τ Φ Q w : ℂ))) := rfl

/-- A point of the gate image is in the maximal domain at level `0`. -/
theorem goodP_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hw : w ∈ Φ '' Q) : GoodP f Df τ Φ Q w :=
  ⟨0, by simpa using hw, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

end

end Work.Pert
