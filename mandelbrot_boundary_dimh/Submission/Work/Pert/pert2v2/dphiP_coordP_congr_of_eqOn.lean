import Mathlib
import Submission.Work.Pert.MaxDom

/-!
# PERT · `Work.Pert.pert2v2.dphiP_coordP_congr_of_eqOn`

The maximal-domain coordinate `φ_f = coordP f Df τ Φ Q` of Shishikura A.3/A.4
(`Submission/Work/Pert/MaxDom.lean`) is built from two ingredients attached to the gate map `Φ`:

* the gate image `Φ '' Q`, which enters the *domain* condition `GoodP` (`w - n ∈ Φ '' Q`);
* the chosen preimage `invOn Φ Q`, which enters the seed value `seedP τ Φ Q x = τ (invOn Φ Q x)`.

Consequently the domain `DphiP f Df τ Φ Q` and the value `coordP f Df τ Φ Q w` can only depend on
`Φ` through its restriction to `Q`.  This file makes that explicit: if `Φ` is injective on `Q` and
`Ψ` agrees with `Φ` on `Q`, then `Ψ '' Q = Φ '' Q`, the chosen preimages coincide
(`invOn Ψ Q = invOn Φ Q`, pointwise — the choice is pinned by injectivity, and when the preimage
does not exist both `invOn`s fall back to the junk value `0`), hence the seed values coincide, and
therefore `GoodP`, the minimal level `mIdxP`, the domain `DphiP` and the value `coordP` are all
literally equal.

This is the "independence of the representative of the germ" statement for the perturbed Fatou
coordinate: in the assembly of `PertData` the gate map `Φ_{-,f}` is only ever known through its
values on the gate `Q_f^-`, so any two representatives may be used interchangeably.

Main result: `dphiP_coordP_congr_of_eqOn`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-! ## The chosen preimage and the seed value -/

/-- **The chosen preimage only sees the map on `Q`.**  If `Φ` is injective on `Q` and `Ψ = Φ` on
`Q`, then `invOn Ψ Q = invOn Φ Q` pointwise: in the "exists" case both chosen points lie in `Q`,
map to `w` under `Φ`, and injectivity identifies them; in the "does not exist" case both fall back
to the junk value `0` (the existence statements are equivalent, since `Ψ = Φ` on `Q`). -/
theorem invOn_congr_of_eqOn {Φ Ψ : ℂ → ℂ} {Q : Set ℂ} (hinj : Set.InjOn Φ Q)
    (h : ∀ z ∈ Q, Ψ z = Φ z) (w : ℂ) :
    Work.Pert.invOn Ψ Q w = Work.Pert.invOn Φ Q w := by
  classical
  by_cases hP : ∃ ζ ∈ Q, Φ ζ = w
  · have hP' : ∃ ζ ∈ Q, Ψ ζ = w := by
      obtain ⟨ζ, hζQ, hζw⟩ := hP
      exact ⟨ζ, hζQ, by rw [h ζ hζQ, hζw]⟩
    have hmem : Work.Pert.invOn Ψ Q w ∈ Q := Work.Pert.invOn_mem hP'
    have hval : Ψ (Work.Pert.invOn Ψ Q w) = w := Work.Pert.invOn_spec hP'
    have hΦ : Φ (Work.Pert.invOn Ψ Q w) = w := by rw [← h _ hmem, hval]
    exact (Work.Pert.invOn_eq (Φ := Φ) hinj hP hmem hΦ).symm
  · have hP' : ¬ ∃ ζ ∈ Q, Ψ ζ = w := by
      intro hc
      obtain ⟨ζ, hζQ, hζw⟩ := hc
      exact hP ⟨ζ, hζQ, by rw [← h ζ hζQ, hζw]⟩
    simp only [Work.Pert.invOn, dite_eq_right hP, dite_eq_right hP']

/-- The seed value `seedP τ Φ Q = τ ∘ invOn Φ Q` only sees the map on `Q`. -/
theorem seedP_congr_of_eqOn {τ Φ Ψ : ℂ → ℂ} {Q : Set ℂ} (hinj : Set.InjOn Φ Q)
    (h : ∀ z ∈ Q, Ψ z = Φ z) :
    Work.Pert.seedP τ Ψ Q = Work.Pert.seedP τ Φ Q := by
  funext u
  simp only [Work.Pert.seedP, invOn_congr_of_eqOn hinj h u]

/-- The gate image only sees the map on `Q`. -/
theorem image_congr_of_eqOn {Φ Ψ : ℂ → ℂ} {Q : Set ℂ} (h : ∀ z ∈ Q, Ψ z = Φ z) :
    Ψ '' Q = Φ '' Q := Set.image_congr h

/-! ## The domain, the level and the value -/

/-- **The domain condition `GoodP` only sees the map on `Q`**: both its clauses (`w - n` lies in
the gate image, and the `f`-orbit of the seed value stays in `Df`) are unchanged. -/
theorem goodP_congr_of_eqOn {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ Ψ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hinj : Set.InjOn Φ Q) (h : ∀ z ∈ Q, Ψ z = Φ z) :
    Work.Pert.GoodP f Df τ Ψ Q w ↔ Work.Pert.GoodP f Df τ Φ Q w := by
  have himg := image_congr_of_eqOn (Φ := Φ) (Q := Q) h
  have hseed := seedP_congr_of_eqOn (τ := τ) (Φ := Φ) (Q := Q) hinj h
  constructor
  · rintro ⟨n, hn, hwalk⟩
    refine ⟨n, ?_, fun j hj => ?_⟩
    · rwa [himg] at hn
    · rw [← hseed]; exact hwalk j hj
  · rintro ⟨n, hn, hwalk⟩
    refine ⟨n, ?_, fun j hj => ?_⟩
    · rwa [← himg] at hn
    · rw [hseed]; exact hwalk j hj

/-- **The minimal level `mIdxP` only sees the map on `Q`.**  Both `GoodP`-predicates are
equivalent, so both have the same minimal admissible level: `mIdxP_le` applied to the *specification*
of the other side gives each inequality, using the previous two lemmas to transport the level
condition; in the non-admissible case both minimal levels are the junk value `0`. -/
theorem mIdxP_congr_of_eqOn {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ Ψ : ℂ → ℂ} {Q : Set ℂ} (w : ℂ)
    (hinj : Set.InjOn Φ Q) (h : ∀ z ∈ Q, Ψ z = Φ z) :
    Work.Pert.mIdxP f Df τ Ψ Q w = Work.Pert.mIdxP f Df τ Φ Q w := by
  classical
  have hiff := goodP_congr_of_eqOn (f := f) (Df := Df) (τ := τ) (Q := Q) (w := w) hinj h
  have himg := image_congr_of_eqOn (Φ := Φ) (Q := Q) h
  have hseed := seedP_congr_of_eqOn (τ := τ) (Φ := Φ) (Q := Q) hinj h
  apply le_antisymm
  · by_cases hw : Work.Pert.GoodP f Df τ Φ Q w
    · obtain ⟨hmem, hwalk⟩ := Work.Pert.mIdxP_spec hw
      refine Work.Pert.mIdxP_le (hiff.mpr hw) ⟨?_, fun j hj => ?_⟩
      · rw [himg]; exact hmem
      · rw [hseed]; exact hwalk j hj
    · have hw' : ¬ Work.Pert.GoodP f Df τ Ψ Q w := fun hc => hw (hiff.mp hc)
      rw [Work.Pert.mIdxP, Work.Pert.mIdxP, dite_eq_right hw', dite_eq_right hw]
  · by_cases hw : Work.Pert.GoodP f Df τ Ψ Q w
    · obtain ⟨hmem, hwalk⟩ := Work.Pert.mIdxP_spec hw
      refine Work.Pert.mIdxP_le (hiff.mp hw) ⟨?_, fun j hj => ?_⟩
      · rw [← himg]; exact hmem
      · rw [← hseed]; exact hwalk j hj
    · have hw' : ¬ Work.Pert.GoodP f Df τ Φ Q w := fun hc => hw (hiff.mpr hc)
      rw [Work.Pert.mIdxP, Work.Pert.mIdxP, dite_eq_right hw, dite_eq_right hw']

theorem dphiP_coordP_congr_of_eqOn {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ Ψ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : Set.InjOn Φ Q) (h : ∀ z ∈ Q, Ψ z = Φ z) :
    Work.Pert.DphiP f Df τ Ψ Q = Work.Pert.DphiP f Df τ Φ Q ∧
      ∀ w : ℂ, Work.Pert.coordP f Df τ Ψ Q w = Work.Pert.coordP f Df τ Φ Q w := by
  refine ⟨?_, ?_⟩
  · ext w
    change Work.Pert.GoodP f Df τ Ψ Q w ↔ Work.Pert.GoodP f Df τ Φ Q w
    exact goodP_congr_of_eqOn (f := f) (Df := Df) (τ := τ) (Q := Q) (w := w) hinj h
  · intro w
    have hm := mIdxP_congr_of_eqOn (f := f) (Df := Df) (τ := τ) (Q := Q) w hinj h
    have hseed := seedP_congr_of_eqOn (τ := τ) (Φ := Φ) (Q := Q) hinj h
    simp only [Work.Pert.coordP, hm, hseed]

end

end Work.Pert.pert2v2
