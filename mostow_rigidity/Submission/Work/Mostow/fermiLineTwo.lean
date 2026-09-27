import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.StabHorosphereBase
import Submission.Work.Mostow.fermiTwoDefs
import Submission.Work.Mostow.geodDetTwo
import Submission.Work.Mostow.stdFermiGeom
import Submission.Work.Mostow.stdFermiVolume
import Submission.Work.Mostow.stdLineStabClass
import Submission.Work.Mostow.existsIsomOfGeodFormula

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Transport of `volH` along the isometry action -/

/-- The chart action of `g : PO n 1` as a measurable equivalence. -/
def smulMeasEquiv (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1) : E n ≃ᵐ E n where
  toFun := fun u => g • u
  invFun := fun u => g⁻¹ • u
  left_inv := fun u => by
    change g⁻¹ • (g • u) = u
    rw [← hA.2.2.2.2.1, inv_mul_cancel, hA.2.2.2.1]
  right_inv := fun u => by
    change g • (g⁻¹ • u) = u
    rw [← hA.2.2.2.2.1, mul_inv_cancel, hA.2.2.2.1]
  measurable_toFun := (HypIsoData.ofProp hI).measurePreserving_smul g |>.measurable
  measurable_invFun := (HypIsoData.ofProp hI).measurePreserving_smul g⁻¹ |>.measurable

/-- The chart action of `g` is injective. -/
lemma smul_injective (hI : HypIsometryProp n) (g : PO n 1) :
    Function.Injective (fun u : E n => g • u) := by
  have hI' := HypIsoData.ofProp hI
  intro u v huv
  change g • u = g • v at huv
  have h : hdist (g • u) (g • v) = 0 := by
    rw [huv, (hI'.eq_zero (g • v) (g • v)).mpr rfl]
  exact (hI'.eq_zero u v).mp (by rw [← hI'.isom_smul g u v]; exact h)

/-- The chart action of `g` is surjective. -/
lemma smul_surjective (hA : POActionProp n) (g : PO n 1) :
    Function.Surjective (fun u : E n => g • u) := by
  intro v
  refine ⟨g⁻¹ • v, ?_⟩
  change g • (g⁻¹ • v) = v
  rw [← hA.2.2.2.2.1, mul_inv_cancel, hA.2.2.2.1]

/-- An isometry preserves `volH` on images of arbitrary sets. -/
theorem volH_smul_image (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1)
    (S : Set (E n)) : volH n ((fun u : E n => g • u) '' S) = volH n S := by
  have hmp := (HypIsoData.ofProp hI).measurePreserving_smul g
  have hmap : (volH n).map (fun u : E n => g • u) = volH n := hmp.map_eq
  have himg : ∀ s : Set (E n),
      (fun u : E n => g • u) '' s = (fun u : E n => g⁻¹ • u) ⁻¹' s := by
    intro s
    ext u
    constructor
    · rintro ⟨v, hv, hvu⟩
      change g⁻¹ • u ∈ s
      rw [← hvu]
      change g⁻¹ • (g • v) ∈ s
      rw [← hA.2.2.2.2.1, inv_mul_cancel, hA.2.2.2.1]
      exact hv
    · intro hu
      refine ⟨g⁻¹ • u, hu, ?_⟩
      change g • (g⁻¹ • u) = u
      rw [← hA.2.2.2.2.1, mul_inv_cancel, hA.2.2.2.1]
  have hemb : MeasurableEmbedding (fun u : E n => g • u) := by
    refine ⟨smul_injective hI g, hmp.measurable, ?_⟩
    intro s hs
    rw [himg s]
    exact ((HypIsoData.ofProp hI).measurePreserving_smul g⁻¹).measurable hs
  calc volH n ((fun u : E n => g • u) '' S)
      = ((volH n).map (fun u : E n => g • u)) ((fun u : E n => g • u) '' S) := by rw [hmap]
    _ = volH n ((fun u : E n => g • u) ⁻¹' ((fun u : E n => g • u) '' S)) :=
        hemb.map_apply (volH n) _
    _ = volH n S := by rw [Set.preimage_image_eq S hemb.injective]

/-! ## The Fermi parametrisation of an arbitrary geodesic line of `E 2` -/

open FermiTwo

/-- The Fermi parametrisation of `line` transported from the standard one by `g₀`. -/
def transportFermi (g₀ : PO 2 1) : ℝ × ℝ → E 2 := fun p => g₀ • stdFermi p

/-- Assembly: an isometry `g₀` carrying the standard geodesic `lineStd` onto `line`, together
with the standard Fermi facts, produces the required Fermi parametrisation of `line`. -/
theorem fermiLineTwo_assembly (hA : Submission.Mostow.POActionProp 2)
    (hI : Submission.Mostow.HypIsometryProp 2) (line : ℝ → Submission.Mostow.E 2)
    (hline : ∀ s t : ℝ, Submission.Mostow.hdist (line s) (line t) = |s - t|)
    (g₀ : LeanEval.Geometry.MostowRigidity.PO 2 1)
    (hg₀ : ∀ s : ℝ, g₀ • lineStd s = line s)
    (hstd0 : ∀ s : ℝ, stdFermi (s, 0) = lineStd s)
    (hstd1 : ∀ s r : ℝ, Submission.Mostow.hdist (stdFermi (s, r)) (lineStd s) = |r|)
    (hstd2 : ∀ s r t : ℝ, Submission.Mostow.hdist (stdFermi (s, r)) (lineStd s)
        ≤ Submission.Mostow.hdist (stdFermi (s, r)) (lineStd t))
    (hstd3 : ∀ s r s' r' : ℝ, |r - r'|
        ≤ Submission.Mostow.hdist (stdFermi (s, r)) (stdFermi (s', r')))
    (hstd4 : ∀ s r t : ℝ, 0 ≤ t →
      Submission.Mostow.hdist (stdFermi (s, r)) (stdFermi (s + t, r))
        = 2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r))
    (hinj : Function.Injective stdFermi) (hsurj : Function.Surjective stdFermi)
    (hvol : ∀ L ρ : ℝ, 0 < L → 0 < ρ →
      Submission.Mostow.volH 2 (stdFermi '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ))
        = ENNReal.ofReal (L * (2 * Real.sinh ρ)))
    (hclass : ∀ g : LeanEval.Geometry.MostowRigidity.PO 2 1,
      (∀ s : ℝ, ∃ s' : ℝ, g • lineStd s = lineStd s') →
      ∃ ε δ c : ℝ, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
        ∀ s r : ℝ, g • stdFermi (s, r) = stdFermi (ε * s + c, δ * r)) :
    ∃ F : ℝ × ℝ → Submission.Mostow.E 2,
      (∀ s : ℝ, F (s, 0) = line s) ∧
      (∀ s r : ℝ, Submission.Mostow.hdist (F (s, r)) (line s) = |r|) ∧
      Function.Injective F ∧
      (∀ s r : ℝ, ∀ t : ℝ,
        Submission.Mostow.hdist (F (s, r)) (line s) ≤ Submission.Mostow.hdist (F (s, r)) (line t)) ∧
      (∀ L ρ : ℝ, 0 < L → 0 < ρ →
        Submission.Mostow.volH 2 (F '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ))
          = ENNReal.ofReal (L * (2 * Real.sinh ρ))) ∧
      (∀ (g : LeanEval.Geometry.MostowRigidity.PO 2 1) (t : ℝ), 0 < t →
        (∀ s : ℝ, g • line s = line (s + t)) →
        (∀ s r : ℝ, g • F (s, r) = F (s + t, r)) →
        ∀ s r : ℝ, Submission.Mostow.hdist (F (s, r)) (g • F (s, r))
          = 2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r)) ∧
      (∀ (g : LeanEval.Geometry.MostowRigidity.PO 2 1),
        (∀ s : ℝ, ∃ s' : ℝ, g • line s = line s') →
        ∃ ε δ c : ℝ, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
          ∀ s r : ℝ, g • F (s, r) = F (ε * s + c, δ * r)) ∧
      (∀ (g : LeanEval.Geometry.MostowRigidity.PO 2 1) (t δ : ℝ), 0 < t → 0 < δ →
        (∀ s : ℝ, g • line s = line (s + t)) →
        (∀ s r : ℝ, g • F (s, r) = F (s + t, r)) →
        ∀ s r : ℝ, |r| + 1 < Real.arcosh (Real.sinh (δ / 2) / Real.sinh (t / 2)) →
          ∀ w : Submission.Mostow.E 2, Submission.Mostow.hdist (F (s, r)) w ≤ 1 →
            Submission.Mostow.hdist w (g • w) < δ) := by
  have hisom := HypIsoData.ofProp hI
  have hmul : ∀ (a b : PO 2 1) (x : E 2), (a * b) • x = a • (b • x) := hA.2.2.2.2.1
  have hinjF : Function.Injective (transportFermi g₀) := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩ hpq
    have hpq' : g₀ • stdFermi (p1, p2) = g₀ • stdFermi (q1, q2) := hpq
    refine hinj ?_
    refine (hisom.eq_zero _ _).mp ?_
    calc Submission.Mostow.hdist (stdFermi (p1, p2)) (stdFermi (q1, q2))
        = Submission.Mostow.hdist (g₀ • stdFermi (p1, p2)) (g₀ • stdFermi (q1, q2)) :=
          (hisom.isom_smul g₀ _ _).symm
      _ = Submission.Mostow.hdist (g₀ • stdFermi (q1, q2)) (g₀ • stdFermi (q1, q2)) := by
          rw [hpq']
      _ = 0 := (hisom.eq_zero _ _).mpr rfl
  have hsurjF : Function.Surjective (transportFermi g₀) := by
    intro w
    obtain ⟨u, hu⟩ := smul_surjective hA g₀ w
    have hu' : g₀ • u = w := hu
    obtain ⟨p, hp⟩ := hsurj u
    refine ⟨p, ?_⟩
    change g₀ • stdFermi p = w
    rw [hp, hu']
  refine ⟨transportFermi g₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- property 1: `F (s,0) = line s`
    intro s
    change g₀ • stdFermi (s, 0) = line s
    rw [hstd0 s]
    exact hg₀ s
  · -- property 2: distance to the line
    intro s r
    change Submission.Mostow.hdist (g₀ • stdFermi (s, r)) (line s) = |r|
    rw [← hg₀ s, hisom.isom_smul g₀]
    exact hstd1 s r
  · -- property 3: injectivity
    exact hinjF
  · -- property 4: the foot is the closest point
    intro s r t
    change Submission.Mostow.hdist (g₀ • stdFermi (s, r)) (line s)
        ≤ Submission.Mostow.hdist (g₀ • stdFermi (s, r)) (line t)
    rw [← hg₀ s, ← hg₀ t, hisom.isom_smul g₀, hisom.isom_smul g₀]
    exact hstd2 s r t
  · -- property 5: volume of a Fermi rectangle
    intro L ρ hL hρ
    have hfun : transportFermi g₀ = (fun u : E 2 => g₀ • u) ∘ stdFermi := by
      funext p
      rfl
    have himg : transportFermi g₀ '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ)
        = (fun u : E 2 => g₀ • u) '' (stdFermi '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ)) := by
      rw [hfun, Set.image_image]
      rfl
    rw [himg, volH_smul_image hA hI g₀, hvol L ρ hL hρ]
  · -- property 6: displacement of a translation along the line
    intro g t ht hgl hgF s r
    rw [hgF s r]
    change Submission.Mostow.hdist (g₀ • stdFermi (s, r)) (g₀ • stdFermi (s + t, r))
        = 2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r)
    rw [hisom.isom_smul g₀]
    exact hstd4 s r t (le_of_lt ht)
  · -- property 7: isometries preserving the line act by `(s,r) ↦ (ε s + c, δ r)`
    intro g hg
    set h : PO 2 1 := g₀⁻¹ * g * g₀ with hh
    have hconj : ∀ x : E 2, g₀ • (h • x) = g • (g₀ • x) := by
      intro x
      rw [← hmul g₀ h x, ← hmul g g₀ x]
      congr 1
      rw [hh]
      group
    have hpres : ∀ s : ℝ, ∃ s' : ℝ, h • lineStd s = lineStd s' := by
      intro s
      obtain ⟨s', hs'⟩ := hg s
      refine ⟨s', ?_⟩
      refine smul_injective hI g₀ ?_
      calc g₀ • (h • lineStd s) = g • (g₀ • lineStd s) := hconj (lineStd s)
        _ = g • line s := by rw [hg₀ s]
        _ = line s' := hs'
        _ = g₀ • lineStd s' := (hg₀ s').symm
    obtain ⟨ε, δ, c, hε, hδ, hform⟩ := hclass h hpres
    refine ⟨ε, δ, c, hε, hδ, ?_⟩
    intro s r
    change g • (g₀ • stdFermi (s, r)) = g₀ • stdFermi (ε * s + c, δ * r)
    calc g • (g₀ • stdFermi (s, r)) = g₀ • (h • stdFermi (s, r)) := (hconj _).symm
      _ = g₀ • stdFermi (ε * s + c, δ * r) := by rw [hform s r]
  · -- property 8: the thick tube meets every orbit in a short displacement
    intro g t δ ht hδ hgl hgF s r hr w hw
    obtain ⟨s₀, r₀, hp₀⟩ : ∃ s₀ r₀ : ℝ, g₀ • stdFermi (s₀, r₀) = w := by
      obtain ⟨u, hu⟩ := smul_surjective hA g₀ w
      have hu' : g₀ • u = w := hu
      obtain ⟨q, hq⟩ := hsurj u
      obtain ⟨s₀, r₀⟩ := q
      exact ⟨s₀, r₀, by rw [hq, hu']⟩
    have hgw : g • w = g₀ • stdFermi (s₀ + t, r₀) := by
      have h1 : g • transportFermi g₀ (s₀, r₀) = transportFermi g₀ (s₀ + t, r₀) := hgF s₀ r₀
      change g • (g₀ • stdFermi (s₀, r₀)) = g₀ • stdFermi (s₀ + t, r₀) at h1
      rw [← hp₀]
      exact h1
    have hdisp : Submission.Mostow.hdist w (g • w)
        = 2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r₀) := by
      rw [hgw, ← hp₀, hisom.isom_smul g₀]
      exact hstd4 s₀ r₀ t (le_of_lt ht)
    have hnear : Submission.Mostow.hdist (g₀ • stdFermi (s₀, r₀)) (g₀ • stdFermi (s, r))
        ≤ 1 := by
      rw [hisom.symm, hp₀]
      exact hw
    have hstep : |r₀ - r| ≤ 1 := by
      have h3 := hstd3 s₀ r₀ s r
      rw [← hisom.isom_smul g₀] at h3
      exact le_trans h3 hnear
    have hb : |r₀| ≤ |r| + 1 := by
      have hsplit : r₀ = (r₀ - r) + r := by ring
      calc |r₀| = |(r₀ - r) + r| := by rw [← hsplit]
        _ ≤ |r₀ - r| + |r| := abs_add_le _ _
        _ ≤ 1 + |r| := by linarith
        _ = |r| + 1 := by ring
    have hc1 : Real.cosh r₀ ≤ Real.cosh (|r| + 1) :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |r| + 1)]
        exact hb)
    have hsin_t : 0 < Real.sinh (t / 2) := Real.sinh_pos_iff.mpr (by linarith)
    have hsin_d : 0 < Real.sinh (δ / 2) := Real.sinh_pos_iff.mpr (by linarith)
    have hposA : 0 < Real.sinh (δ / 2) / Real.sinh (t / 2) := div_pos hsin_d hsin_t
    have h1A : (1 : ℝ) ≤ Real.sinh (δ / 2) / Real.sinh (t / 2) := by
      refine (Real.arcosh_le_arcosh zero_lt_one hposA).mp ?_
      rw [Real.arcosh_zero]
      linarith [hr, abs_nonneg r]
    have hcos_lt : Real.cosh (|r| + 1) < Real.sinh (δ / 2) / Real.sinh (t / 2) := by
      have h := Real.cosh_lt_cosh.mpr (show |(|r| + 1)| < |Real.arcosh
          (Real.sinh (δ / 2) / Real.sinh (t / 2))| from by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (Real.arcosh_nonneg h1A)]
        exact hr)
      rwa [Real.cosh_arcosh h1A] at h
    have hfinal : Real.sinh (t / 2) * Real.cosh r₀ < Real.sinh (δ / 2) := by
      calc Real.sinh (t / 2) * Real.cosh r₀ ≤ Real.sinh (t / 2) * Real.cosh (|r| + 1) :=
            mul_le_mul_of_nonneg_left hc1 (le_of_lt hsin_t)
        _ < Real.sinh (t / 2) * (Real.sinh (δ / 2) / Real.sinh (t / 2)) :=
            mul_lt_mul_of_pos_left hcos_lt hsin_t
        _ = Real.sinh (δ / 2) := by field_simp
    rw [hdisp]
    have hmain : Real.arsinh (Real.sinh (t / 2) * Real.cosh r₀) < δ / 2 := by
      have h := Real.arsinh_lt_arsinh.mpr hfinal
      rwa [Real.arsinh_sinh] at h
    linarith

/-- **The Fermi parametrisation of an arbitrary geodesic line of the hyperbolic plane.**

Given a unit-speed geodesic line `line : ℝ → ℍ²` of the hyperbolic plane `E 2`, there is a
Fermi parametrisation `F : ℝ × ℝ → E 2` of `ℍ²` about `line`: the first coordinate is the
arclength parameter along the line, the second the signed hyperbolic distance to it.  It is
equivariant for the isometries of the line, and its level sets have the expected hyperbolic
volume. -/
theorem fermiLineTwo (hA : Submission.Mostow.POActionProp 2) (hI : Submission.Mostow.HypIsometryProp 2)
    (line : ℝ → Submission.Mostow.E 2)
    (hline : ∀ s t : ℝ, Submission.Mostow.hdist (line s) (line t) = |s - t|) :
    ∃ F : ℝ × ℝ → Submission.Mostow.E 2,
      (∀ s : ℝ, F (s, 0) = line s) ∧
      (∀ s r : ℝ, Submission.Mostow.hdist (F (s, r)) (line s) = |r|) ∧
      Function.Injective F ∧
      (∀ s r : ℝ, ∀ t : ℝ,
        Submission.Mostow.hdist (F (s, r)) (line s) ≤ Submission.Mostow.hdist (F (s, r)) (line t)) ∧
      (∀ L ρ : ℝ, 0 < L → 0 < ρ →
        Submission.Mostow.volH 2 (F '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ))
          = ENNReal.ofReal (L * (2 * Real.sinh ρ))) ∧
      (∀ (g : LeanEval.Geometry.MostowRigidity.PO 2 1) (t : ℝ), 0 < t →
        (∀ s : ℝ, g • line s = line (s + t)) →
        (∀ s r : ℝ, g • F (s, r) = F (s + t, r)) →
        ∀ s r : ℝ, Submission.Mostow.hdist (F (s, r)) (g • F (s, r))
          = 2 * Real.arsinh (Real.sinh (t / 2) * Real.cosh r)) ∧
      (∀ (g : LeanEval.Geometry.MostowRigidity.PO 2 1),
        (∀ s : ℝ, ∃ s' : ℝ, g • line s = line s') →
        ∃ ε δ c : ℝ, (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
          ∀ s r : ℝ, g • F (s, r) = F (ε * s + c, δ * r)) ∧
      (∀ (g : LeanEval.Geometry.MostowRigidity.PO 2 1) (t δ : ℝ), 0 < t → 0 < δ →
        (∀ s : ℝ, g • line s = line (s + t)) →
        (∀ s r : ℝ, g • F (s, r) = F (s + t, r)) →
        ∀ s r : ℝ, |r| + 1 < Real.arcosh (Real.sinh (δ / 2) / Real.sinh (t / 2)) →
          ∀ w : Submission.Mostow.E 2, Submission.Mostow.hdist (F (s, r)) w ≤ 1 →
            Submission.Mostow.hdist w (g • w) < δ) := by
  obtain ⟨hstd0, _hstdA, hstd1, hstd2, _hstdB, hstd3, hstd4, hinj, hsurj⟩ := stdFermiGeom
  obtain ⟨g₀, hg₀⟩ :=
    existsIsomOfGeodFormula hA hI line hline (fun s => geodDetTwo line hline s)
  exact fermiLineTwo_assembly hA hI line hline g₀ hg₀ hstd0 hstd1 hstd2 hstd3 hstd4 hinj hsurj
    stdFermiVolume (fun g hg => stdLineStabClass hA hI g hg)


end

end Work.Mostow
