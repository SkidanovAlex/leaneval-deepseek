import Mathlib
import Submission.Work.ELRig.Inputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `ELRig.exists_liftSidesV2`

The plane-topology ("two-sides") lemma for the two `1`-periodic lift curves `γ₁`, `γ₂` of the ray
tails in the repelling coordinate (the input structure `Work.EL.LiftSides` of ELRig).

Given two `1`-periodic continuous curves `γ₁`, `γ₂ : ℝ → ℂ` whose real part is *strictly
increasing*, and which (for `Re < -R`) stay respectively above and below the real axis, we
construct the three regions `U`, `M`, `L` of the left half plane `{Re < -R}`:

* `U` : above the graph of `γ₁`,
* `M` : between the graphs of `γ₂` and `γ₁` (contains the real axis),
* `L` : below the graph of `γ₂`.

Because `Re ∘ γᵢ` is a strictly increasing continuous bijection `ℝ → ℝ`, each curve is the graph
of a continuous function `hgtᵢ` over the real axis; the three regions are then the (preconnected,
pairwise disjoint, open) connected components of the complement of the two curves in the left half
plane, and the exhaustion `decomp` follows from the elementary topology of a preconnected set.
-/

open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

open Complex

/-! ## One lift curve as a graph over the real axis -/

/-- The real part of a `1`-periodic continuous curve with strictly increasing real part hits every
real value (the range of `Re ∘ γ` is unbounded above and below and `Re ∘ γ` is continuous, so the
intermediate value theorem applies). -/
theorem re_surjective {γ : ℝ → ℂ} (hcont : Continuous γ)
    (hmono : StrictMono fun s => (γ s).re)
    (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) :
    Function.Surjective (fun s => (γ s).re) := by
  have hshift : ∀ (n : ℕ) (s : ℝ), (γ (s + n)).re = (γ s).re + n := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hk, show s + ((k : ℝ) + 1) = (s + (k : ℝ)) + 1 by ring, hper (s + (k : ℝ))]
      simp only [Complex.add_re, Complex.one_re]
      rw [ih s]; push_cast; ring
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt |y - (γ 0).re|
  have hN1 := (abs_lt.mp hN).1
  have hN2 := (abs_lt.mp hN).2
  have hN' : (γ 0).re + (N : ℝ) > y := by linarith
  have hN'' : (γ (-(N : ℝ))).re < y := by
    have h0 : (γ (-(N : ℝ) + (N : ℝ))).re = (γ (-(N : ℝ))).re + (N : ℝ) := hshift N (-(N : ℝ))
    rw [show -(N : ℝ) + (N : ℝ) = (0 : ℝ) by ring] at h0
    linarith
  have hb : (γ (N : ℝ)).re = (γ 0).re + (N : ℝ) := by have := hshift N 0; simpa using this
  have hfb : y < (γ (N : ℝ)).re := by rw [hb]; exact hN'
  have hmem : y ∈ Set.Icc ((fun s => (γ s).re) (-(N : ℝ))) ((fun s => (γ s).re) (N : ℝ)) :=
    ⟨le_of_lt hN'', le_of_lt hfb⟩
  obtain ⟨s, hs⟩ :=
    intermediate_value_univ (-(N : ℝ)) (N : ℝ) (Complex.continuous_re.comp hcont) hmem
  exact ⟨s, hs⟩

/-- The data of a single lift curve: continuity, strictly increasing real part, and the
`1`-periodicity. -/
structure CCurve (γ : ℝ → ℂ) : Type where
  /-- the curve is continuous. -/
  hcont : Continuous γ
  /-- its real part is strictly increasing. -/
  hmono : StrictMono fun s => (γ s).re
  /-- it is `1`-periodic up to the translation `w ↦ w + 1`. -/
  hper : ∀ s : ℝ, γ (s + 1) = γ s + 1

namespace CCurve

variable {γ : ℝ → ℂ}

/-- `Re ∘ γ` is surjective. -/
theorem surj (C : CCurve γ) : Function.Surjective fun s => (γ s).re :=
  re_surjective C.hcont C.hmono C.hper

/-- The order isomorphism `ℝ ≃o ℝ` given by `s ↦ (γ s).re`. -/
noncomputable def σ (C : CCurve γ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun s => (γ s).re) C.hmono C.surj

/-- The inverse of `Re ∘ γ`: the parameter of the curve point of real part `x`. -/
theorem σ_symm_re (C : CCurve γ) (x : ℝ) : (γ ((C.σ).symm x)).re = x :=
  StrictMono.orderIsoOfSurjective_self_symm_apply (fun s => (γ s).re) C.hmono C.surj x

/-- The height function: the curve as a graph over the real axis. -/
noncomputable def hgt (C : CCurve γ) (x : ℝ) : ℝ := (γ ((C.σ).symm x)).im

/-- The height function is continuous. -/
theorem hgt_cont (C : CCurve γ) : Continuous C.hgt :=
  Complex.continuous_im.comp (C.hcont.comp (OrderIso.continuous _))

/-- Membership in the range of the curve is the graph equation. -/
theorem mem_range_iff (C : CCurve γ) (w : ℂ) : w ∈ Set.range γ ↔ w.im = C.hgt w.re := by
  constructor
  · rintro ⟨t, rfl⟩
    have h2 : (C.σ).symm (γ t).re = t := C.hmono.injective (C.σ_symm_re (γ t).re)
    simp only [hgt]; rw [h2]
  · intro h
    refine ⟨(C.σ).symm w.re, ?_⟩
    apply Complex.ext
    · exact C.σ_symm_re w.re
    · exact h.symm

/-- On the left half plane the curve lies above the real axis. -/
theorem hgt_pos (C : CCurve γ) {R : ℝ}
    (habove : ∀ s : ℝ, (γ s).re < -R → 0 < (γ s).im) {x : ℝ} (hx : x < -R) :
    0 < C.hgt x := by
  have h := habove ((C.σ).symm x) (by rw [C.σ_symm_re]; exact hx)
  simpa [hgt] using h

/-- On the left half plane the curve lies below the real axis. -/
theorem hgt_neg (C : CCurve γ) {R : ℝ}
    (hbelow : ∀ s : ℝ, (γ s).re < -R → (γ s).im < 0) {x : ℝ} (hx : x < -R) :
    C.hgt x < 0 := by
  have h := hbelow ((C.σ).symm x) (by rw [C.σ_symm_re]; exact hx)
  simpa [hgt] using h

end CCurve

/-! ## The three regions -/

/-- The upper region: above the graph of `γ₁` in the left half plane. -/
noncomputable def RegU {γ : ℝ → ℂ} (C : CCurve γ) (R : ℝ) : Set ℂ :=
  {w : ℂ | w.re < -R ∧ C.hgt w.re < w.im}

/-- The lower region: below the graph of `γ₂` in the left half plane. -/
noncomputable def RegL {γ : ℝ → ℂ} (C : CCurve γ) (R : ℝ) : Set ℂ :=
  {w : ℂ | w.re < -R ∧ w.im < C.hgt w.re}

/-- The middle region: between the graphs of `γ₂` and `γ₁`. -/
noncomputable def RegM {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) (R : ℝ) : Set ℂ :=
  {w : ℂ | w.re < -R ∧ C₂.hgt w.re < w.im ∧ w.im < C₁.hgt w.re}

/-! #### Parametrisations of the regions (for preconnectedness) -/

/-- Parametrisation of `RegU` by `(-∞,-R) × (0,∞)`. -/
noncomputable def paramU {γ : ℝ → ℂ} (C : CCurve γ) : ℝ × ℝ → ℂ :=
  fun p => (p.1 : ℂ) + Complex.ofReal (C.hgt p.1 + p.2) * Complex.I

/-- Parametrisation of `RegL` by `(-∞,-R) × (0,∞)`. -/
noncomputable def paramL {γ : ℝ → ℂ} (C : CCurve γ) : ℝ × ℝ → ℂ :=
  fun p => (p.1 : ℂ) + Complex.ofReal (C.hgt p.1 - p.2) * Complex.I

/-- Parametrisation of `RegM` by `(-∞,-R) × (0,1)`. -/
noncomputable def paramM {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) : ℝ × ℝ → ℂ :=
  fun p => (p.1 : ℂ) + Complex.ofReal (C₂.hgt p.1 + p.2 * (C₁.hgt p.1 - C₂.hgt p.1)) * Complex.I

theorem paramU_re {γ : ℝ → ℂ} (C : CCurve γ) (p : ℝ × ℝ) : (paramU C p).re = p.1 := by
  simp [paramU]

theorem paramU_im {γ : ℝ → ℂ} (C : CCurve γ) (p : ℝ × ℝ) : (paramU C p).im = C.hgt p.1 + p.2 := by
  simp [paramU]

theorem paramL_re {γ : ℝ → ℂ} (C : CCurve γ) (p : ℝ × ℝ) : (paramL C p).re = p.1 := by
  simp [paramL]

theorem paramL_im {γ : ℝ → ℂ} (C : CCurve γ) (p : ℝ × ℝ) : (paramL C p).im = C.hgt p.1 - p.2 := by
  simp [paramL]

theorem paramM_re {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) (p : ℝ × ℝ) :
    (paramM C₁ C₂ p).re = p.1 := by simp [paramM]

theorem paramM_im {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) (p : ℝ × ℝ) :
    (paramM C₁ C₂ p).im = C₂.hgt p.1 + p.2 * (C₁.hgt p.1 - C₂.hgt p.1) := by simp [paramM]

theorem paramU_cont {γ : ℝ → ℂ} (C : CCurve γ) : Continuous (paramU C) := by
  have h2 : Continuous (fun p : ℝ × ℝ => Complex.ofReal (C.hgt p.1 + p.2)) :=
    Complex.continuous_ofReal.comp ((C.hgt_cont.comp continuous_fst).add continuous_snd)
  exact (Complex.continuous_ofReal.comp continuous_fst).add (h2.mul continuous_const)

theorem paramL_cont {γ : ℝ → ℂ} (C : CCurve γ) : Continuous (paramL C) := by
  have h2 : Continuous (fun p : ℝ × ℝ => Complex.ofReal (C.hgt p.1 - p.2)) :=
    Complex.continuous_ofReal.comp ((C.hgt_cont.comp continuous_fst).sub continuous_snd)
  exact (Complex.continuous_ofReal.comp continuous_fst).add (h2.mul continuous_const)

theorem paramM_cont {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) :
    Continuous (paramM C₁ C₂) := by
  have h2 : Continuous (fun p : ℝ × ℝ => Complex.ofReal
      (C₂.hgt p.1 + p.2 * (C₁.hgt p.1 - C₂.hgt p.1))) :=
    Complex.continuous_ofReal.comp
      ((C₂.hgt_cont.comp continuous_fst).add
        (continuous_snd.mul ((C₁.hgt_cont.comp continuous_fst).sub
          (C₂.hgt_cont.comp continuous_fst))))
  exact (Complex.continuous_ofReal.comp continuous_fst).add (h2.mul continuous_const)

theorem paramU_eq {γ : ℝ → ℂ} (C : CCurve γ) {w : ℂ} {t : ℝ}
    (h : C.hgt w.re + t = w.im) : paramU C (w.re, t) = w := by
  rw [paramU, h, Complex.re_add_im]

theorem paramL_eq {γ : ℝ → ℂ} (C : CCurve γ) {w : ℂ} {t : ℝ}
    (h : C.hgt w.re - t = w.im) : paramL C (w.re, t) = w := by
  rw [paramL, h, Complex.re_add_im]

theorem paramM_eq {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {w : ℂ} {t : ℝ}
    (h : C₂.hgt w.re + t * (C₁.hgt w.re - C₂.hgt w.re) = w.im) :
    paramM C₁ C₂ (w.re, t) = w := by
  rw [paramM, h, Complex.re_add_im]

/-! #### Openness -/

theorem isOpen_RegU {γ : ℝ → ℂ} (C : CCurve γ) (R : ℝ) : IsOpen (RegU C R) := by
  rw [show RegU C R = {w : ℂ | w.re < -R} ∩ {w : ℂ | C.hgt w.re < w.im} from rfl]
  exact (isOpen_lt continuous_re continuous_const).inter
    (isOpen_lt (C.hgt_cont.comp continuous_re) continuous_im)

theorem isOpen_RegL {γ : ℝ → ℂ} (C : CCurve γ) (R : ℝ) : IsOpen (RegL C R) := by
  rw [show RegL C R = {w : ℂ | w.re < -R} ∩ {w : ℂ | w.im < C.hgt w.re} from rfl]
  exact (isOpen_lt continuous_re continuous_const).inter
    (isOpen_lt continuous_im (C.hgt_cont.comp continuous_re))

theorem isOpen_RegM {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) (R : ℝ) :
    IsOpen (RegM C₁ C₂ R) := by
  rw [show RegM C₁ C₂ R = ({w : ℂ | w.re < -R} ∩ {w : ℂ | C₂.hgt w.re < w.im})
        ∩ {w : ℂ | w.im < C₁.hgt w.re} from by
      ext w; simp only [RegM, mem_setOf_eq, mem_inter_iff]; tauto]
  exact ((isOpen_lt continuous_re continuous_const).inter
    (isOpen_lt (C₂.hgt_cont.comp continuous_re) continuous_im)).inter
    (isOpen_lt continuous_im (C₁.hgt_cont.comp continuous_re))

/-! #### Preconnectedness -/

theorem isPreconnected_RegU {γ : ℝ → ℂ} (C : CCurve γ) (R : ℝ) : IsPreconnected (RegU C R) := by
  have hD : IsPreconnected (Set.Iio (-R) ×ˢ Set.Ioi (0 : ℝ)) :=
    isPreconnected_Iio.prod isPreconnected_Ioi
  have himg : paramU C '' (Set.Iio (-R) ×ˢ Set.Ioi (0 : ℝ)) = RegU C R := by
    ext w; constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Set.mem_prod, Set.mem_Iio, Set.mem_Ioi] at hp
      simp only [RegU, mem_setOf_eq, paramU_re, paramU_im]
      exact ⟨hp.1, by linarith [hp.2]⟩
    · intro hw
      exact ⟨(w.re, w.im - C.hgt w.re), by
          rw [Set.mem_prod, Set.mem_Iio, Set.mem_Ioi]
          exact ⟨hw.1, by linarith [hw.2]⟩,
        paramU_eq C (by ring)⟩
  rw [← himg]
  exact hD.image _ (paramU_cont C).continuousOn

theorem isPreconnected_RegL {γ : ℝ → ℂ} (C : CCurve γ) (R : ℝ) : IsPreconnected (RegL C R) := by
  have hD : IsPreconnected (Set.Iio (-R) ×ˢ Set.Ioi (0 : ℝ)) :=
    isPreconnected_Iio.prod isPreconnected_Ioi
  have himg : paramL C '' (Set.Iio (-R) ×ˢ Set.Ioi (0 : ℝ)) = RegL C R := by
    ext w; constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Set.mem_prod, Set.mem_Iio, Set.mem_Ioi] at hp
      simp only [RegL, mem_setOf_eq, paramL_re, paramL_im]
      exact ⟨hp.1, by linarith [hp.2]⟩
    · intro hw
      exact ⟨(w.re, C.hgt w.re - w.im), by
          rw [Set.mem_prod, Set.mem_Iio, Set.mem_Ioi]
          exact ⟨hw.1, by linarith [hw.2]⟩,
        paramL_eq C (by ring)⟩
  rw [← himg]
  exact hD.image _ (paramL_cont C).continuousOn

theorem isPreconnected_RegM {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) :
    IsPreconnected (RegM C₁ C₂ R) := by
  have hD : IsPreconnected (Set.Iio (-R) ×ˢ Set.Ioo (0 : ℝ) 1) :=
    isPreconnected_Iio.prod isPreconnected_Ioo
  have himg : paramM C₁ C₂ '' (Set.Iio (-R) ×ˢ Set.Ioo (0 : ℝ) 1) = RegM C₁ C₂ R := by
    ext w; constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Set.mem_prod, Set.mem_Iio, Set.mem_Ioo] at hp
      obtain ⟨hp1, hp2a, hp2b⟩ := hp
      have hd : 0 < C₁.hgt p.1 - C₂.hgt p.1 := by
        have h1 := C₁.hgt_pos habove hp1
        have h2 := C₂.hgt_neg hbelow hp1
        linarith
      simp only [RegM, mem_setOf_eq, paramM_re, paramM_im]
      refine ⟨hp1, ?_, ?_⟩
      · have := mul_pos hp2a hd; linarith
      · have := mul_lt_mul_of_pos_right hp2b hd; linarith
    · intro hw
      have hd : 0 < C₁.hgt w.re - C₂.hgt w.re := by
        have h1 := C₁.hgt_pos habove hw.1
        have h2 := C₂.hgt_neg hbelow hw.1
        linarith
      refine ⟨(w.re, (w.im - C₂.hgt w.re) / (C₁.hgt w.re - C₂.hgt w.re)), ?_, ?_⟩
      · rw [Set.mem_prod, Set.mem_Iio, Set.mem_Ioo]
        exact ⟨hw.1, div_pos (by linarith [hw.2.1]) hd, by rw [div_lt_one hd]; linarith [hw.2.2]⟩
      · apply paramM_eq
        rw [div_mul_cancel₀ _ (ne_of_gt hd)]
        ring
  rw [← himg]
  exact hD.image _ (paramM_cont C₁ C₂).continuousOn

/-! #### Disjointness -/

theorem RegU_disj_RegM {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ} :
    Disjoint (RegU C₁ R) (RegM C₁ C₂ R) := by
  rw [Set.disjoint_left]
  intro w hwU hwM
  linarith [hwU.2, hwM.2.2]

theorem RegM_disj_RegL {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ} :
    Disjoint (RegM C₁ C₂ R) (RegL C₂ R) := by
  rw [Set.disjoint_left]
  intro w hwM hwL
  linarith [hwM.2.1, hwL.2]

theorem RegU_disj_RegL {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) :
    Disjoint (RegU C₁ R) (RegL C₂ R) := by
  rw [Set.disjoint_left]
  intro w hwU hwL
  have h1 := C₁.hgt_pos habove hwU.1
  have h2 := C₂.hgt_neg hbelow hwU.1
  linarith [hwU.2, hwL.2, h1, h2]

/-! #### The curves avoid the regions -/

theorem RegU_off {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) :
    RegU C₁ R ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
  intro w hwU hwG
  rw [Set.mem_union] at hwG
  rcases hwG with h | h
  · have hh := (C₁.mem_range_iff w).mp h
    linarith [hwU.2, hh]
  · have hh := (C₂.mem_range_iff w).mp h
    have h1 := C₁.hgt_pos habove hwU.1
    have h2 := C₂.hgt_neg hbelow hwU.1
    linarith [hwU.2, hh, h1, h2]

theorem RegL_off {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) :
    RegL C₂ R ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
  intro w hwL hwG
  rw [Set.mem_union] at hwG
  rcases hwG with h | h
  · have hh := (C₁.mem_range_iff w).mp h
    have h1 := C₁.hgt_pos habove hwL.1
    have h2 := C₂.hgt_neg hbelow hwL.1
    linarith [hwL.2, hh, h1, h2]
  · have hh := (C₂.mem_range_iff w).mp h
    linarith [hwL.2, hh]

theorem RegM_off {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) :
    RegM C₁ C₂ R ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
  intro w hwM hwG
  rw [Set.mem_union] at hwG
  rcases hwG with h | h
  · have hh := (C₁.mem_range_iff w).mp h
    linarith [hwM.2.2, hh]
  · have hh := (C₂.mem_range_iff w).mp h
    linarith [hwM.2.1, hh]

/-! #### Cover, the real axis, and the exhaustion -/

/-- Every point of the left half plane lies in one of the regions or on one of the curves. -/
theorem mem_trichotomy {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) {w : ℂ} (hw : w.re < -R) :
    w ∈ RegU C₁ R ∨ w ∈ RegM C₁ C₂ R ∨ w ∈ RegL C₂ R
      ∨ w ∈ Set.range γ₁ ∪ Set.range γ₂ := by
  by_cases h1 : w ∈ Set.range γ₁
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  by_cases h2 : w ∈ Set.range γ₂
  · exact Or.inr (Or.inr (Or.inr (Or.inr h2)))
  have hne1 : w.im ≠ C₁.hgt w.re := fun h => h1 ((C₁.mem_range_iff w).mpr h)
  have hne2 : w.im ≠ C₂.hgt w.re := fun h => h2 ((C₂.mem_range_iff w).mpr h)
  rcases lt_trichotomy w.im (C₁.hgt w.re) with h | h | h
  · rcases lt_trichotomy w.im (C₂.hgt w.re) with h' | h' | h'
    · exact Or.inr (Or.inr (Or.inl ⟨hw, h'⟩))
    · exact absurd h' hne2
    · exact Or.inr (Or.inl ⟨hw, h', h⟩)
  · exact absurd h hne1
  · exact Or.inl ⟨hw, h⟩

/-- The real axis below the level `-R` lies in the middle region. -/
theorem real_mem_RegM {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) {x : ℝ} (hx : x < -R) :
    (x : ℂ) ∈ RegM C₁ C₂ R := by
  refine ⟨by simpa using hx, ?_, ?_⟩
  · simpa using C₂.hgt_neg hbelow hx
  · simpa using C₁.hgt_pos habove hx

/-- A preconnected set covered by two disjoint open sets lies in one of them. -/
theorem preconnected_subset_of_disjoint_open {X : Type*} [TopologicalSpace X]
    {s a b : Set X} (hs : IsPreconnected s) (ha : IsOpen a) (hb : IsOpen b)
    (hd : Disjoint a b) (hcov : s ⊆ a ∪ b) : s ⊆ a ∨ s ⊆ b := by
  by_cases hb' : (s ∩ b).Nonempty
  · by_cases ha' : (s ∩ a).Nonempty
    · exfalso
      obtain ⟨y, hy, hya, hyb⟩ := hs a b ha hb hcov ha' hb'
      exact Set.disjoint_left.mp hd hya hyb
    · right
      intro x hx
      rcases hcov hx with hxa | hxb
      · exact absurd ⟨x, hx, hxa⟩ ha'
      · exact hxb
  · left
    intro x hx
    rcases hcov hx with hxa | hxb
    · exact hxa
    · exact absurd ⟨x, hx, hxb⟩ hb'

/-- The exhaustion: every preconnected subset of the left half plane avoiding the two curves
lies in one of the three regions. -/
theorem decomp {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂) {R : ℝ}
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) :
    ∀ S : Set ℂ, IsPreconnected S → S ⊆ {w : ℂ | w.re < -R} →
      S ∩ (Set.range γ₁ ∪ Set.range γ₂) = ∅ →
      S ⊆ RegU C₁ R ∨ S ⊆ RegM C₁ C₂ R ∨ S ⊆ RegL C₂ R := by
  intro S hpre hsub hdisj
  have hcovU : S ⊆ RegU C₁ R ∪ (RegM C₁ C₂ R ∪ RegL C₂ R) := by
    intro w hw
    rcases mem_trichotomy C₁ C₂ habove hbelow (hsub hw) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exfalso
      have : w ∈ S ∩ (Set.range γ₁ ∪ Set.range γ₂) := ⟨hw, h⟩
      rw [hdisj] at this
      exact this
  have hdU : Disjoint (RegU C₁ R) (RegM C₁ C₂ R ∪ RegL C₂ R) := by
    rw [Set.disjoint_union_right]
    exact ⟨RegU_disj_RegM C₁ C₂, RegU_disj_RegL C₁ C₂ habove hbelow⟩
  rcases preconnected_subset_of_disjoint_open hpre (isOpen_RegU C₁ R)
      ((isOpen_RegM C₁ C₂ R).union (isOpen_RegL C₂ R)) hdU hcovU with h1 | h1
  · exact Or.inl h1
  · rcases preconnected_subset_of_disjoint_open hpre (isOpen_RegM C₁ C₂ R)
        (isOpen_RegL C₂ R) (RegM_disj_RegL C₁ C₂) h1 with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h2)

/-! #### The regions reach the strips `Im > R₀` and `Im < -R₀` -/

/-- The upper region reaches the strip `Im > R₀`. -/
theorem top_mem_RegU {γ : ℝ → ℂ} (C : CCurve γ) (R R₀ : ℝ) :
    ∃ w ∈ RegU C R, R₀ < w.im := by
  let w : ℂ := (-R - 1 : ℝ) + Complex.ofReal (max (C.hgt (-R - 1)) R₀ + 1) * Complex.I
  have hre : w.re = -R - 1 := by simp [w]
  have him : w.im = max (C.hgt (-R - 1)) R₀ + 1 := by simp [w]
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · rw [hre]; linarith
  · rw [hre, him]; have := le_max_left (C.hgt (-R - 1)) R₀; linarith
  · rw [him]; have := le_max_right (C.hgt (-R - 1)) R₀; linarith

/-- The lower region reaches the strip `Im < -R₀`. -/
theorem bottom_mem_RegL {γ : ℝ → ℂ} (C : CCurve γ) (R R₀ : ℝ) :
    ∃ w ∈ RegL C R, w.im < -R₀ := by
  let w : ℂ := (-R - 1 : ℝ) + Complex.ofReal (min (C.hgt (-R - 1)) (-R₀) - 1) * Complex.I
  have hre : w.re = -R - 1 := by simp [w]
  have him : w.im = min (C.hgt (-R - 1)) (-R₀) - 1 := by simp [w]
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · rw [hre]; linarith
  · rw [hre, him]; have := min_le_left (C.hgt (-R - 1)) (-R₀); linarith
  · rw [him]; have := min_le_right (C.hgt (-R - 1)) (-R₀); linarith

/-! ## The target lemma -/

theorem exists_liftSidesV2 {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ}
    {R R₀ : ℝ} (hRR₀ : R₀ < R) {γ₁ γ₂ : ℝ → ℂ}
    (hcont₁ : Continuous γ₁) (hcont₂ : Continuous γ₂)
    (hmono₁ : StrictMono fun s : ℝ => (γ₁ s).re)
    (hmono₂ : StrictMono fun s : ℝ => (γ₂ s).re)
    (hper₁ : ∀ s : ℝ, γ₁ (s + 1) = γ₁ s + 1)
    (hper₂ : ∀ s : ℝ, γ₂ (s + 1) = γ₂ s + 1)
    (habove : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im)
    (hbelow : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0) :
    Nonempty (Work.EL.LiftSides hN z₁ γ₁ γ₂ R R₀) := by
  let C₁ : CCurve γ₁ := ⟨hcont₁, hmono₁, hper₁⟩
  let C₂ : CCurve γ₂ := ⟨hcont₂, hmono₂, hper₂⟩
  refine ⟨hRR₀, RegU C₁ R, RegM C₁ C₂ R, RegL C₂ R,
    (fun w hw => hw.1), (fun w hw => hw.1), (fun w hw => hw.1),
    RegU_off C₁ C₂ habove hbelow, RegM_off C₁ C₂ habove hbelow,
    RegL_off C₁ C₂ habove hbelow,
    isPreconnected_RegU C₁ R, isPreconnected_RegM C₁ C₂ habove hbelow,
    isPreconnected_RegL C₂ R,
    RegU_disj_RegM C₁ C₂, RegU_disj_RegL C₁ C₂ habove hbelow, RegM_disj_RegL C₁ C₂,
    ?_, (fun x hx => real_mem_RegM C₁ C₂ habove hbelow hx),
    decomp C₁ C₂ habove hbelow, top_mem_RegU C₁ R R₀, bottom_mem_RegL C₂ R R₀⟩
  intro w hw
  rcases mem_trichotomy C₁ C₂ habove hbelow hw with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · rcases h with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

end Work.ELRig
