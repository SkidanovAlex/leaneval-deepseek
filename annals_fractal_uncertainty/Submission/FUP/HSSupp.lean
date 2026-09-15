import Submission.FUP.HSGain
import Submission.FUP.HSInduction
import Submission.Commons.Analysis.Fourier.fourier_mul_toLp_ae_eq_zero_off_add

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 6: the growth of the Fourier support of `f_m`

This module records the *Fourier support induction* of Han–Schlag's §5: the `L²` Fourier transform
of `f_m = (∏_{n<m} Ψ_{nT}) · f` is (a.e.) supported in `Y + ℓ_m • [-1,1]^d`, where
`ℓ_m = ellSum L T m`.

The only non-elementary input is the `L²` product-support transfer
```
FourierProductSupport : ∀ g h, MemLp g 1 → MemLp g ⊤ → MemLp h 2 →
  (∀ ξ, ξ ∉ E → 𝓕g ξ = 0) → (∀ᵐ ξ, 𝓕(h.toLp) ξ ≠ 0 → ξ ∈ F) →
  ∀ᵐ ξ, 𝓕((h.mul htop).toLp (g * h)) ξ ≠ 0 → ξ ∈ E + F
```
which is the statement of the commons lemma
`Commons.Analysis.Fourier.fourier_mul_toLp_ae_eq_zero_off_add` in "support" form; it is kept as an
explicit hypothesis here so that the rest of the assembly can be developed independently of it.
-/

namespace Submission.FUP

/-! ## Minkowski-sum lemmas -/

lemma addSet_mono {A A' B B' : Set ℝᵈ} (hA : A ⊆ A') (hB : B ⊆ B') :
    addSet A B ⊆ addSet A' B' :=
  fun z ⟨a, ha, b, hb, hz⟩ => ⟨a, hA ha, b, hB hb, hz⟩

lemma addSet_comm (A B : Set ℝᵈ) : addSet A B = addSet B A := by
  ext z
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, by abel⟩

lemma addSet_closedBall_subset {a b : ℝ} :
    addSet (closedBall (0:ℝᵈ) a) (closedBall (0:ℝᵈ) b) ⊆ closedBall (0:ℝᵈ) (a + b) := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hx hy ⊢
  calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
    _ ≤ a + b := add_le_add hx hy

/-! ## The product-support transfer -/

/-- The `L²` product-support transfer (the statement of
`Commons.Analysis.Fourier.fourier_mul_toLp_ae_eq_zero_off_add` in support form). -/
def FourierProductSupport : Prop :=
  ∀ (g h : ℝᵈ → ℂ) (hg1 : MemLp g 1 (volume : Measure ℝᵈ))
    (hgtop : MemLp g ⊤ (volume : Measure ℝᵈ)) (hh2 : MemLp h 2 (volume : Measure ℝᵈ))
    (E F : Set ℝᵈ),
    (∀ ξ : ℝᵈ, ξ ∉ E → 𝓕 g ξ = 0) →
    (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ F) →
    ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (((hh2.mul hgtop) : MemLp (fun x => g x * h x) 2 (volume : Measure ℝᵈ)).toLp
        (fun x => g x * h x)) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 →
        ξ ∈ addSet E F

/-- `FourierProductSupport` holds, by the commons lemma
`Commons.Analysis.Fourier.fourier_mul_toLp_ae_eq_zero_off_add`. -/
theorem fourierProductSupport_holds : FourierProductSupport (d := d) := by
  intro g h hg1 hgtop hh2 E F hE hF
  have hF' : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ F →
      ((𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0 := by
    filter_upwards [hF] with ξ hξ hξF
    by_contra hzero
    exact hξF (hξ hzero)
  filter_upwards [Commons.Analysis.Fourier.fourier_mul_toLp_ae_eq_zero_off_add
    g h hg1 hgtop hh2 E F hE hF'] with ξ hξ
  intro hne
  by_contra hcon
  exact hne (hξ fun a ha b hb heq => hcon ⟨a, ha, b, hb, heq⟩)

/-! ## The Fourier support of `f_m` -/

/-- **The Fourier support of `f_m` grows by `ℓ_m`.**  If the `L²` Fourier transform of `f` is a.e.
supported in `Y`, then the `L²` Fourier transform of `f_m` is a.e. supported in
`Y + closedBall 0 (ellSum L T m)`. -/
theorem fourierSupp_indFun (hprod : FourierProductSupport (d := d)) {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (Φ : FupCutoff d) (hΦr : Φ.radius ≤ 1) {X Y : Set ℝᵈ} (hX : X ⊆ cube (-1) 1)
    {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ))
    (hY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y)
    (m : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 ((memLp_indFun_two hL Φ T m hX hf).toLp (indFun Φ L T X m f)) :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 →
        ξ ∈ addSet Y (closedBall (0:ℝᵈ) (ellSum L T m)) := by
  induction m with
  | zero =>
      have hone : closedBall (0:ℝᵈ) (ellSum L T 0) = {0} := by
        rw [show ellSum L T 0 = 0 from by simp [ellSum]]
        ext z
        simp only [Metric.mem_closedBall, dist_zero_right, norm_le_zero_iff, mem_singleton_iff]
      have hadd : addSet Y (closedBall (0:ℝᵈ) (ellSum L T 0)) = Y := by
        rw [hone]
        ext z
        constructor
        · rintro ⟨a, ha, b, hb, rfl⟩
          rw [mem_singleton_iff] at hb
          rwa [hb, add_zero]
        · intro hz
          exact ⟨z, hz, 0, mem_singleton_iff.mpr rfl, by simp⟩
      have hLp : (memLp_indFun_two hL Φ T 0 hX hf).toLp (indFun Φ L T X 0 f) = hf.toLp f :=
        MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => by rw [indFun_zero])
      rw [hadd, hLp]
      exact hY
  | succ m ih =>
      set e' : ℝ := (L : ℝ) ^ (m * T + T) with he'
      set E : Set ℝᵈ := closedBall (0:ℝᵈ) (e' * Φ.radius) with hEdef
      have hEsub : E ⊆ closedBall (0:ℝᵈ) e' := by
        intro z hz
        rw [hEdef] at hz
        simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
        calc ‖z‖ ≤ e' * Φ.radius := hz
          _ ≤ e' * 1 := mul_le_mul_of_nonneg_left hΦr (by positivity)
          _ = e' := mul_one _
      have hE : ∀ ξ : ℝᵈ, ξ ∉ E → 𝓕 (psiC Φ L T X (m * T)) ξ = 0 := by
        intro ξ hξ
        have hlt : e' * Φ.radius < ‖ξ‖ := by
          rw [hEdef, Metric.mem_closedBall, dist_zero_right, not_le] at hξ
          exact hξ
        exact fourier_Psi_eq_zero hL Φ T (m * T) hX (by rw [he'] at hlt; exact hlt)
      have hmain := hprod (psiC Φ L T X (m * T)) (indFun Φ L T X m f)
        (memLp_psiC_one hL Φ T (m * T) hX) (memLp_psiC_top hL Φ T (m * T) hX)
        (memLp_indFun_two hL Φ T m hX hf) E (addSet Y (closedBall (0:ℝᵈ) (ellSum L T m))) hE ih
      have hLp : (((memLp_indFun_two hL Φ T m hX hf).mul (memLp_psiC_top hL Φ T (m * T) hX) :
            MemLp (fun x => psiC Φ L T X (m * T) x * indFun Φ L T X m f x) 2
              (volume : Measure ℝᵈ))).toLp
            (fun x => psiC Φ L T X (m * T) x * indFun Φ L T X m f x)
          = (memLp_indFun_two hL Φ T (m + 1) hX hf).toLp (indFun Φ L T X (m + 1) f) := by
        refine (MemLp.toLp_congr _ _ ?_).symm
        filter_upwards with x
        rw [indFun_succ]
        rfl
      have hSubset : addSet E (addSet Y (closedBall (0:ℝᵈ) (ellSum L T m)))
          ⊆ addSet Y (closedBall (0:ℝᵈ) (ellSum L T (m + 1))) := by
        calc addSet E (addSet Y (closedBall (0:ℝᵈ) (ellSum L T m)))
            ⊆ addSet (closedBall (0:ℝᵈ) e') (addSet Y (closedBall (0:ℝᵈ) (ellSum L T m))) :=
              addSet_mono hEsub (le_refl _)
          _ = addSet (addSet (closedBall (0:ℝᵈ) e') Y) (closedBall (0:ℝᵈ) (ellSum L T m)) :=
              (addSet_assoc _ _ _).symm
          _ = addSet (addSet Y (closedBall (0:ℝᵈ) e')) (closedBall (0:ℝᵈ) (ellSum L T m)) := by
              rw [addSet_comm (closedBall (0:ℝᵈ) e') Y]
          _ = addSet Y (addSet (closedBall (0:ℝᵈ) e') (closedBall (0:ℝᵈ) (ellSum L T m))) :=
              addSet_assoc _ _ _
          _ ⊆ addSet Y (closedBall (0:ℝᵈ) (e' + ellSum L T m)) :=
              addSet_mono (le_refl _) addSet_closedBall_subset
          _ = addSet Y (closedBall (0:ℝᵈ) (ellSum L T (m + 1))) := by
              rw [ellSum_succ, he', show (m + 1) * T = m * T + T from by ring, add_comm]
      filter_upwards [hmain] with ξ hξ
      intro hne
      rw [← hLp] at hne
      exact hSubset (hξ hne)

/-- **The Fourier support of `f_m` grows by `ℓ_m`** (unconditional form). -/
theorem fourierSupp_indFun' {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (Φ : FupCutoff d) (hΦr : Φ.radius ≤ 1) {X Y : Set ℝᵈ} (hX : X ⊆ cube (-1) 1)
    {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ))
    (hY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y)
    (m : ℕ) :
    ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 ((memLp_indFun_two hL Φ T m hX hf).toLp (indFun Φ L T X m f)) :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 →
        ξ ∈ addSet Y (closedBall (0:ℝᵈ) (ellSum L T m)) :=
  fourierSupp_indFun (fourierProductSupport_holds (d := d)) hL hT Φ hΦr hX hf hY m

end Submission.FUP
