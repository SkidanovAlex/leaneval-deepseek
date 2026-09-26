import Mathlib
import Submission.Work.Smooth.Morse.Defs

import Submission.Work.Smooth.Morse.Sweep.regionEquivalent_locally_of_regularValue
import Submission.Work.Smooth.Morse.MorseModel.windingSpan_locally_const

/-!
# The level family of a smooth function (item 5, existence form)

The sublevel regions `A t = F ∩ {g < t}` of a smooth function `g` on the embedded torus
`F = ψ(standard torus)` form a `Work.Smooth.Morse.LevelFamily` once the levels are reparametrised
so that they run from `a` to `b` over the unit interval:

* `S.region t = F ∩ {g < v t}` where `v : ℝ → [a,b]` is the clamped affine map which equals `a`
  for `t ≤ 0`, `b` for `t ≥ 1` and `a + t (b-a)` in between; in particular `S.region 0 = F ∩ {g < a}`
  and `S.region 1 = F ∩ {g < b}`;
* the exceptional parameters are the finitely many `t ∈ [0,1]` whose level `v t` is a critical
  value (`Work.Smooth.Morse.LocallyFiniteCriticalValues`), where the local model `DiscModel`
  makes the winding span locally constant;
* at every other parameter the region is *locally constant in loop content*: for `t ∉ [0,1]`
  because the reparametrisation is constant there, and for `t ∈ [0,1]` because `v t` is a regular
  value, so a whole neighbourhood of `v t` consists of regular values and the transport across
  regular intervals (`Work.Smooth.Morse.RegularEquivalent`) relates the two regions.

This is the level-family form of item 5: it combines the three inputs of the chapter
(`LocallyFiniteCriticalValues`, `RegularEquivalent`, `DiscModel`) into the single local model that
`Work.Smooth.Morse.windingSpan_eq_of_levelSweep` and
`Work.Smooth.Morse.LevelFamily.windingSpan_eq` consume.
-/

namespace Work.Smooth.Morse.Sweep

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## The clamped affine reparametrisation of the level -/

/-- `clamp01 t = max 0 (min 1 t)`, the projection of `ℝ` onto `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp01_eq_zero {t : ℝ} (h : t ≤ 0) : clamp01 t = 0 :=
  max_eq_left (le_trans (min_le_right _ _) h)

theorem clamp01_eq_one {t : ℝ} (h : 1 ≤ t) : clamp01 t = 1 := by
  rw [clamp01, min_eq_left h, max_eq_right zero_le_one]

theorem clamp01_eq_self {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right h₁, max_eq_right h₀]

/-- `clamp01` is `1`-Lipschitz. -/
theorem abs_clamp01_sub_le (s t : ℝ) : |clamp01 s - clamp01 t| ≤ |s - t| := by
  have h₁ : |clamp01 s - clamp01 t| ≤ |min 1 s - min 1 t| := by
    have := abs_max_sub_max_le_max (0 : ℝ) (min 1 s) 0 (min 1 t)
    simpa [clamp01] using this
  have h₂ : |min 1 s - min 1 t| ≤ |s - t| := by
    have := abs_min_sub_min_le_max (1 : ℝ) s 1 t
    simpa using this
  exact le_trans h₁ h₂

/-- The affine reparametrisation of `[0,1]` onto `[a,b]`, clamped outside: `levelParam a b t = a`
for `t ≤ 0`, `= b` for `t ≥ 1` and `= a + t (b-a)` in between. -/
def levelParam (a b : ℝ) (t : ℝ) : ℝ := a + (b - a) * clamp01 t

theorem levelParam_eq_of_nonpos {a b t : ℝ} (h : t ≤ 0) : levelParam a b t = a := by
  rw [levelParam, clamp01_eq_zero h, mul_zero, add_zero]

theorem levelParam_eq_of_one_le {a b t : ℝ} (h : 1 ≤ t) : levelParam a b t = b := by
  rw [levelParam, clamp01_eq_one h]; ring

theorem levelParam_eq_of_mem_Icc {a b t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    levelParam a b t = a + (b - a) * t := by
  rw [levelParam, clamp01_eq_self h₀ h₁]

theorem levelParam_mem_Icc {a b t : ℝ} (hab : a ≤ b) (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    levelParam a b t ∈ Set.Icc a b := by
  rw [levelParam_eq_of_mem_Icc h₀ h₁, Set.mem_Icc]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hab) h₀]
  · nlinarith [mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr hab)]

theorem abs_levelParam_sub_le {a b : ℝ} (hab : a ≤ b) (s t : ℝ) :
    |levelParam a b s - levelParam a b t| ≤ (b - a) * |s - t| := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsplit : levelParam a b s - levelParam a b t = (b - a) * (clamp01 s - clamp01 t) := by
    simp only [levelParam]
    ring
  rw [hsplit, abs_mul, abs_of_nonneg hba]
  exact mul_le_mul_of_nonneg_left (abs_clamp01_sub_le s t) hba

@[simp] theorem levelParam_zero (a b : ℝ) : levelParam a b 0 = a :=
  levelParam_eq_of_nonpos le_rfl

@[simp] theorem levelParam_one (a b : ℝ) : levelParam a b 1 = b :=
  levelParam_eq_of_one_le le_rfl

/-- The elementary estimate behind the choice of radii: `c · (δ / (2 (c+1))) < δ`. -/
theorem mul_div_two_mul_lt {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    c * (δ / (2 * (c + 1))) < δ := by
  have h2 : 0 < 2 * (c + 1) := by linarith
  rw [mul_div_assoc', div_lt_iff₀ h2]
  nlinarith

/-! ## The exceptional parameters -/

/-- The parameters of the family at which the level `levelParam a b t` is a critical value of
`g|_F`.  Only the parameters in `[0,1]` are recorded, because outside that interval the
reparametrisation is constant and the region is locally constant. -/
def critParams (ψ : Submission.Diffeo) (g : R3 → ℝ) (a b : ℝ) : Set ℝ :=
  {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ levelParam a b t ∈ criticalValues ψ g}

/-- For `a < b` the map `t ↦ levelParam a b t` is injective on `[0,1]`, and its values there lie in
`[a,b]`; since the critical values in `[a,b]` are finite, so are the recorded parameters. -/
theorem finite_critParams (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hcrit : LocallyFiniteCriticalValues ψ g) {a b : ℝ} (hab : a < b) :
    (critParams ψ g a b).Finite := by
  have hT : (criticalValues ψ g ∩ Set.Icc a b).Finite := hcrit a b
  refine Set.Finite.of_finite_image (f := levelParam a b) (hT.subset ?_) ?_
  · rintro u ⟨t, ht, rfl⟩
    exact ⟨ht.2, levelParam_mem_Icc (le_of_lt hab) ht.1.1 ht.1.2⟩
  · intro s hs t ht hst
    rw [critParams, Set.mem_setOf_eq] at hs ht
    rw [levelParam_eq_of_mem_Icc hs.1.1 hs.1.2, levelParam_eq_of_mem_Icc ht.1.1 ht.1.2] at hst
    exact mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_gt hab)) (by linarith)

/-! ## The two cases of the construction -/

/-- The construction when the level interval is nondegenerate: the regions
`region ψ g (levelParam a b t)` are the level family. -/
theorem exists_levelFamily_of_levelData_of_lt (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : Continuous g) (hcrit : LocallyFiniteCriticalValues ψ g)
    (hreg : RegularEquivalent ψ g) (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀)
    {a b : ℝ} (hab : a < b) :
    ∃ S : Work.Smooth.Morse.LevelFamily (torus ψ), S.region 0 = region ψ g a ∧
      S.region 1 = region ψ g b := by
  classical
  have hba : 0 < b - a := sub_pos.mpr hab
  have hfin : (critParams ψ g a b).Finite := finite_critParams ψ hcrit hab
  let exc : Finset ℝ := hfin.toFinset
  have hmem_exc : ∀ t : ℝ, t ∈ exc ↔ t ∈ critParams ψ g a b := fun t => hfin.mem_toFinset
  refine ⟨{ region := fun t => region ψ g (levelParam a b t)
            exc := exc
            regular := ?_
            crossing := ?_ }, ?_, ?_⟩
  · -- the local model at a non-exceptional parameter
    intro t ht
    rcases lt_or_ge t 0 with ht0 | ht0
    · -- `t < 0`: the reparametrisation is constant near `t`
      refine ⟨-t / 2, by linarith, ?_, ?_⟩
      · intro s hs
        intro hsc
        have hs' : s < 0 := by
          have h := abs_lt.mp hs
          linarith [h.2, ht0]
        exact absurd ((hmem_exc s).mp hsc).1.1 (not_le.mpr hs')
      · intro s hs
        have hs' : s < 0 := by
          have h := abs_lt.mp hs
          linarith [h.2, ht0]
        rw [levelParam_eq_of_nonpos (le_of_lt hs'), levelParam_eq_of_nonpos (le_of_lt ht0)]
        exact Work.SurgeryInvariance.RegionEquivalent.refl _
    · rcases lt_or_ge (1 : ℝ) t with ht1 | ht1
      · -- `1 < t`: the reparametrisation is constant near `t`
        refine ⟨(t - 1) / 2, by linarith, ?_, ?_⟩
        · intro s hs
          intro hsc
          have hs' : 1 < s := by
            have h := abs_lt.mp hs
            linarith [h.1, ht1]
          exact absurd ((hmem_exc s).mp hsc).1.2 (not_le.mpr hs')
        · intro s hs
          have hs' : 1 < s := by
            have h := abs_lt.mp hs
            linarith [h.1, ht1]
          rw [levelParam_eq_of_one_le (le_of_lt hs'), levelParam_eq_of_one_le (le_of_lt ht1)]
          exact Work.SurgeryInvariance.RegionEquivalent.refl _
      · -- `0 ≤ t ≤ 1` and `t ∉ exc`, so the level `levelParam a b t` is a regular value
        have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
        have hlev : levelParam a b t ∉ criticalValues ψ g :=
          fun hc => ht ((hmem_exc t).mpr ⟨htI, hc⟩)
        obtain ⟨δ, hδpos, hδ⟩ := exists_notMem_criticalValues_near ψ hcrit hlev
        have hden : 0 < 2 * (b - a + 1) := by linarith
        have hbound : ∀ s : ℝ, |s - t| < δ / (2 * (b - a + 1)) →
            |levelParam a b s - levelParam a b t| < δ := by
          intro s hs
          calc |levelParam a b s - levelParam a b t|
              ≤ (b - a) * |s - t| := abs_levelParam_sub_le (le_of_lt hab) s t
            _ < (b - a) * (δ / (2 * (b - a + 1))) := mul_lt_mul_of_pos_left hs hba
            _ < δ := mul_div_two_mul_lt hba hδpos
        refine ⟨δ / (2 * (b - a + 1)), div_pos hδpos hden, ?_, ?_⟩
        · intro s hs
          intro hsc
          have hsmem := (hmem_exc s).mp hsc
          exact hδ (levelParam a b s) (hbound s hs) hsmem.2
        · intro s hs
          have hclose := hbound s hs
          have hI : ∀ u ∈ Set.Icc (levelParam a b t) (levelParam a b s),
              IsRegularValue ψ g u := by
            intro u hu
            rw [Set.mem_Icc] at hu
            refine hδ u ?_
            rw [abs_lt]
            exact ⟨by linarith [hδpos], by linarith [hu.2, (abs_lt.mp hclose).2]⟩
          rcases le_total (levelParam a b t) (levelParam a b s) with hle | hle
          · exact hreg _ _ hle hI
          · have hI' : ∀ u ∈ Set.Icc (levelParam a b s) (levelParam a b t),
                IsRegularValue ψ g u := by
              intro u hu
              rw [Set.mem_Icc] at hu
              refine hδ u ?_
              rw [abs_lt]
              exact ⟨by linarith [hu.1, (abs_lt.mp hclose).1], by linarith [hδpos]⟩
            exact (hreg _ _ hle hI').symm
  · -- the local model at an exceptional parameter: the winding span is locally constant
    intro t ht
    have hlevel : levelParam a b t ∈ criticalValues ψ g := ((hmem_exc t).mp ht).2
    obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
      Work.Smooth.Morse.MorseModel.windingSpan_locally_const ψ hg (hdisc _ hlevel)
    have hden : 0 < 2 * (b - a + 1) := by linarith
    refine ⟨ε₁ / (2 * (b - a + 1)), div_pos hε₁pos hden, fun s hs => ?_⟩
    have hbnd : |levelParam a b s - levelParam a b t| < ε₁ := by
      calc |levelParam a b s - levelParam a b t|
          ≤ (b - a) * |s - t| := abs_levelParam_sub_le (le_of_lt hab) s t
        _ < (b - a) * (ε₁ / (2 * (b - a + 1))) := mul_lt_mul_of_pos_left hs hba
        _ < ε₁ := mul_div_two_mul_lt hba hε₁pos
    exact hε₁ (levelParam a b s) hbnd
  · simp
  · simp

/-- The construction when the level interval is degenerate: the constant family. -/
theorem exists_levelFamily_of_levelData_of_eq (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hcrit : LocallyFiniteCriticalValues ψ g) (hreg : RegularEquivalent ψ g)
    (hdisc : ∀ t₀ ∈ criticalValues ψ g, DiscModel ψ g t₀) {a b : ℝ} (hab : a = b) :
    ∃ S : Work.Smooth.Morse.LevelFamily (torus ψ), S.region 0 = region ψ g a ∧
      S.region 1 = region ψ g b := by
  subst hab
  refine ⟨{ region := fun _ => region ψ g a
            exc := ∅
            regular := ?_
            crossing := ?_ }, rfl, rfl⟩
  · intro t _
    exact ⟨1, one_pos, by simp, fun s _ => Work.SurgeryInvariance.RegionEquivalent.refl _⟩
  · intro t ht
    exact absurd ht (by simp)

/-! ## The existence of the level family -/

theorem exists_levelFamily_of_levelData (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : Continuous g) (hcrit : Work.Smooth.Morse.LocallyFiniteCriticalValues ψ g) (hreg : Work.Smooth.Morse.RegularEquivalent ψ g) (hdisc : ∀ t₀ ∈ Work.Smooth.Morse.criticalValues ψ g, Work.Smooth.Morse.DiscModel ψ g t₀) (a b : ℝ) (hab : a ≤ b) : ∃ S : Work.Smooth.Morse.LevelFamily (Work.Smooth.Morse.torus ψ), S.region 0 = Work.Smooth.Morse.region ψ g a ∧ S.region 1 = Work.Smooth.Morse.region ψ g b := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact exists_levelFamily_of_levelData_of_lt ψ hg hcrit hreg hdisc hlt
  · exact exists_levelFamily_of_levelData_of_eq ψ hcrit hreg hdisc heq

end

end Work.Smooth.Morse.Sweep
