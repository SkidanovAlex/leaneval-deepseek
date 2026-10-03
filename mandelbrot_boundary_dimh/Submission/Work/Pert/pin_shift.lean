import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs

/-!
# PERT · `Work.Pert.pin_shift`: the freedom in `Φm` acts by translation on the value map

For the maximal-domain coordinate `coordP f Df τ Φ Q` (Shishikura (4.2.1), `Work.Pert.MaxDom`) the
*only* freedom left in `Φ` (given `MandelDim.FatouUnique`) is an additive constant, and it acts on
the induced value map by a **translation**: with `Φ_c := fun z => Φ z + c`,

  `coordP f Df τ Φ_c Q (w + c) = coordP f Df τ Φ Q w`
  (equivalently `DphiP … Φ_c Q = {w | w - c ∈ DphiP … Φ Q}`).

This is the precise form of "the conclusion `∃Φm, V ≈ d.φ on K'` is exactly the statement that some
translate of the raw value map matches `d.φ`"; see `NOTES_Ksub_phi_close_session2.md` §0.
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

/-! ## Injectivity and image under `z ↦ Φ z + c` -/

theorem injOn_add_const {Φ : ℂ → ℂ} {Q : Set ℂ} (hinj : InjOn Φ Q) (c : ℂ) :
    InjOn (fun z => Φ z + c) Q := by
  intro a ha b hb hab
  exact hinj ha hb (add_right_cancel hab)

theorem image_add_const (Φ : ℂ → ℂ) (Q : Set ℂ) (c : ℂ) :
    (fun z => Φ z + c) '' Q = (fun w : ℂ => w + c) '' (Φ '' Q) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Φ z, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, hyc⟩
    exact ⟨z, hz, hyc⟩

/-- The chosen preimage is unchanged when the coordinate is shifted by a constant. -/
theorem invOn_add_const {Φ : ℂ → ℂ} {Q : Set ℂ} (hinj : InjOn Φ Q) (c : ℂ) {w : ℂ}
    (hpre : ∃ ζ ∈ Q, Φ ζ = w) : invOn (fun z => Φ z + c) Q (w + c) = invOn Φ Q w := by
  obtain ⟨ζ₀, hζ₀, hΦζ₀⟩ := hpre
  rw [invOn_eq (injOn_add_const hinj c) ⟨ζ₀, hζ₀, by rw [hΦζ₀]⟩ hζ₀ (by rw [hΦζ₀]),
    invOn_eq hinj ⟨ζ₀, hζ₀, hΦζ₀⟩ hζ₀ hΦζ₀]

/-- The seed value is unchanged when the coordinate is shifted by a constant. -/
theorem seedP_add_const {τ Φ : ℂ → ℂ} {Q : Set ℂ} (hinj : InjOn Φ Q) (c : ℂ) {w : ℂ}
    (h : ∃ ζ ∈ Q, Φ ζ = w) :
    seedP τ (fun z => Φ z + c) Q (w + c) = seedP τ Φ Q w := by
  rw [seedP, seedP, invOn_add_const hinj c h]

/-! ## The level structure -/

/-- The level-`n` predicate for `w + c` with the shifted coordinate is the level-`n` predicate for
`w`. -/
theorem level_iff {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : InjOn Φ Q) (c : ℂ) (w : ℂ) (n : ℕ) :
    ((w + c) - (n : ℂ) ∈ (fun z => Φ z + c) '' Q ∧
        ∀ j : ℕ, j < n →
          f^[j] (seedP τ (fun z => Φ z + c) Q ((w + c) - (n : ℂ))) ∈ Df)
      ↔ (w - (n : ℂ) ∈ Φ '' Q ∧
        ∀ j : ℕ, j < n → f^[j] (seedP τ Φ Q (w - (n : ℂ))) ∈ Df) := by
  have hkey : ∀ {y : ℂ}, y ∈ Φ '' Q →
      seedP τ (fun z => Φ z + c) Q (y + c) = seedP τ Φ Q y := by
    rintro y ⟨ζ, hζ, rfl⟩
    exact seedP_add_const hinj c ⟨ζ, hζ, rfl⟩
  constructor
  · rintro ⟨himg, horb⟩
    have himg' : w - (n : ℂ) ∈ Φ '' Q := by
      rw [image_add_const] at himg
      obtain ⟨y, hy, hyc⟩ := himg
      have hyc' : y + c = w + c - (n : ℂ) := hyc
      have hy' : w - (n : ℂ) = y := by linear_combination -hyc'
      show w - (n : ℂ) ∈ Φ '' Q
      rw [hy']
      exact hy
    refine ⟨himg', fun j hj => ?_⟩
    have hc : (w + c) - (n : ℂ) = (w - (n : ℂ)) + c := by ring
    rw [hc, hkey himg'] at horb
    exact horb j hj
  · rintro ⟨himg, horb⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [image_add_const]
      exact ⟨w - (n : ℂ), himg, by ring⟩
    · have hc : (w + c) - (n : ℂ) = (w - (n : ℂ)) + c := by ring
      rw [hc, hkey himg]
      exact horb j hj

theorem GoodP_add_const {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : InjOn Φ Q) (c : ℂ) (w : ℂ) :
    GoodP f Df τ (fun z => Φ z + c) Q (w + c) ↔ GoodP f Df τ Φ Q w :=
  exists_congr (fun n => level_iff hinj c w n)

theorem mIdxP_add_const {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : InjOn Φ Q) (c : ℂ) (w : ℂ) :
    mIdxP f Df τ (fun z => Φ z + c) Q (w + c) = mIdxP f Df τ Φ Q w := by
  by_cases h : GoodP f Df τ Φ Q w
  · have h' : GoodP f Df τ (fun z => Φ z + c) Q (w + c) := (GoodP_add_const hinj c w).mpr h
    have e1 : mIdxP f Df τ (fun z => Φ z + c) Q (w + c) ≤ mIdxP f Df τ Φ Q w :=
      mIdxP_le h' ((level_iff hinj c w _).mpr (mIdxP_spec h))
    have e2 : mIdxP f Df τ Φ Q w ≤ mIdxP f Df τ (fun z => Φ z + c) Q (w + c) :=
      mIdxP_le h ((level_iff hinj c w _).mp (mIdxP_spec h'))
    omega
  · have h' : ¬ GoodP f Df τ (fun z => Φ z + c) Q (w + c) :=
      fun h'' => h ((GoodP_add_const hinj c w).mp h'')
    unfold mIdxP
    rw [dite_eq_right h', dite_eq_right h]

theorem coordP_add_const {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : InjOn Φ Q) (c : ℂ) (w : ℂ) :
    coordP f Df τ (fun z => Φ z + c) Q (w + c) = coordP f Df τ Φ Q w := by
  unfold coordP
  rw [mIdxP_add_const (f := f) (Df := Df) (τ := τ) hinj c w]
  refine congrArg (fun s : ℂ => f^[mIdxP f Df τ Φ Q w] s) ?_
  by_cases h : GoodP f Df τ Φ Q w
  · have himg : w - (mIdxP f Df τ Φ Q w : ℂ) ∈ Φ '' Q := (mIdxP_spec h).1
    have hcast : (w + c) - (mIdxP f Df τ Φ Q w : ℂ)
        = (w - (mIdxP f Df τ Φ Q w : ℂ)) + c := by ring
    rw [hcast, seedP_add_const hinj c himg]
  · have hw : w ∉ Φ '' Q := fun hmem => h (goodP_of_mem_image hmem)
    have hm0 : mIdxP f Df τ Φ Q w = 0 := by
      unfold mIdxP
      exact dite_eq_right h
    have hc0 : (w + c) - (mIdxP f Df τ Φ Q w : ℂ) = w + c := by rw [hm0]; simp
    have hw0 : w - (mIdxP f Df τ Φ Q w : ℂ) = w := by rw [hm0]; simp
    rw [hc0, hw0]
    have hno : ¬ ∃ ζ ∈ Q, Φ ζ = w :=
      fun hx => hw ⟨hx.choose, hx.choose_spec.1, hx.choose_spec.2⟩
    have hno' : ¬ ∃ ζ ∈ Q, Φ ζ + c = w + c :=
      fun hx => hno ⟨hx.choose, hx.choose_spec.1, add_right_cancel hx.choose_spec.2⟩
    rw [seedP, seedP, invOn, invOn, dite_eq_right hno', dite_eq_right hno]

theorem DphiP_add_const {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : InjOn Φ Q) (c : ℂ) (w : ℂ) :
    (w + c ∈ DphiP f Df τ (fun z => Φ z + c) Q) ↔ w ∈ DphiP f Df τ Φ Q :=
  GoodP_add_const hinj c w

end

end Work.Pert
