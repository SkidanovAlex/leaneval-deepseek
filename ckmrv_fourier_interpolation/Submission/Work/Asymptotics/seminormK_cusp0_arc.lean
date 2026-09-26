import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.arcRegion
import Submission.Work.Asymptotics.arcT_flat
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.Basic
import Submission.Work.Asymptotics.layerLow_local_seminorm
import Submission.Work.Asymptotics.layerTrunc_local_seminorm
import Submission.Work.Asymptotics.paperLayer_local_seminorm
import Submission.Work.Asymptotics.highPart_seminorm_scaled
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.Compact.local_agreement
import Submission.Work.Asymptotics.arcT_smallT
import Submission.Work.Asymptotics.CuspExp.Basic
import Submission.Work.Asymptotics.CuspExp.Exp
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Asymptotics.CuspExp.kernelKfun_cuspExp
import Submission.Work.Asymptotics.CuspExp.cuspModel_bound

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

open MeasureTheory UpperHalfPlane Filter
open scoped Topology ContDiff

namespace Work.Asymptotics

/-! ## Main-free copies of the layer/puncture transfer machinery

The originals (`Work.Asymptotics.paperLayer_neg`, `..._contDiff_of_mem`,
`Work.Asymptotics.kernelTransform_seminorm_of_layer_on_compact`) live in modules whose import
closure contains `Work.Asymptotics.MiddleRange.Main`, which cannot be imported together with the
`KPlusXiDefs` family used by `Work.Asymptotics.arcT_flat`.  The copies below are verbatim. -/

lemma arcT_sinSq_neg (r : ℝ) : sinSq (-r) = sinSq r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [sinSq, hsq]

lemma arcT_layerLow_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    layerLow ℓ d τ (-s) = layerLow ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerLow, sinSq, hsq]

lemma arcT_layerTrunc_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    layerTrunc G ℓ d τ (-s) = layerTrunc G ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerTrunc, sinSq, hsq]

lemma arcT_highPart_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (s : ℝ) :
    highPart G τ (-s) = highPart G τ s := by
  simp only [highPart, neg_sq]

lemma arcT_paperLayer_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    paperLayer G ℓ d τ (-s) = paperLayer G ℓ d τ s := by
  simp only [paperLayer]
  rw [arcT_layerLow_neg, arcT_layerTrunc_neg, arcT_highPart_neg]

/-- The layer is `C^∞` in the radial variable for `τ ∈ K`. -/
lemma arcT_paperLayer_contDiff_of_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) {K : Set UpperHalfPlane}
    (hflatK : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpolyK : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ τ ∈ K, ContDiff ℝ ⊤ (fun s : ℝ => paperLayer G ℓ d τ s) := by
  intro τ hτ
  obtain ⟨h1, h2, h3⟩ := layerPieces_contDiff_of_mem ℓ d hd G hflatK hpolyK τ hτ
  have hfun : (fun s : ℝ => paperLayer G ℓ d τ s)
      = fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s + highPart G τ s := by
    funext s; rw [paperLayer]
  rw [hfun]
  exact (h1.add h2).add h3


/-! ## Transfer from a layer to the naive contour integral (copy) -/

theorem arcT_kernelTransform_of_layer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (F₂ : UpperHalfPlane → ℝ → ℂ) {K : Set UpperHalfPlane}
    (h0 : ∀ τ ∈ K, F₂ τ 0 = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0)
    (hagr : ∀ τ ∈ K, ∀ r : ℝ, r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      F₂ τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r)
    (hsemi : ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖ ≤ C) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨C₀, hC₀, hbound⟩ := hsemi k l
  refine ⟨C₀, hC₀, ?_⟩
  intro τ r hτ
  set Kf : UpperHalfPlane → UpperHalfPlane → ℂ := Work.Kernels.Kfun ℓ d with hKf
  set Gf : ℝ → ℂ := fun s => F₂ τ s with hGf
  set gg : ℝ → ℂ := fun s => Work.Kernels.kernelTransform Kf τ s with hgg
  set P : ℝ → Prop := fun s => MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) with hP
  have hPdef : ∀ s, P s = MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := fun s => rfl
  have hboundG : ∀ s : ℝ, (|s| ^ k) * ‖iteratedDeriv l Gf s‖ ≤ C₀ := fun s => hbound τ s hτ
  have hP0 : ∀ s, ¬ P s → gg s = 0 := by
    intro s hs
    have hI : ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
          * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
      rwa [hPdef s] at hs
    have hz : (∫ t in Set.Ioi (0:ℝ), Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) = 0 := integral_undef hI
    rw [hgg]
    simp only [Work.Kernels.kernelTransform, hz, mul_zero]
  have hP1 : ∀ s, s ≠ 0 → P s → gg s = Gf s := by
    intro s hs0 hs
    rw [hgg, hGf]
    exact (hagr τ hτ s hs0 (by rwa [hPdef s] at hs)).symm
  have hgg0 : gg 0 = Gf 0 := by
    rw [hgg, hGf]
    exact (h0 τ hτ).symm
  have hmono : ∀ s s', P s → |s| ≤ |s'| → P s' := by
    intro s s' hs hsle
    rw [hPdef s']
    exact integrableOn_kaxis_exp_mono_abs (K := Kf) τ hsle (by rwa [hPdef s] at hs)
  by_cases hne : ∃ s, P s
  · set S : Set ℝ := {b | ∃ s, P s ∧ b = |s|} with hS
    have hSne : S.Nonempty := by obtain ⟨s, hs⟩ := hne; exact ⟨|s|, s, hs, rfl⟩
    have hSbdd : BddBelow S := ⟨0, by rintro b ⟨s, _, rfl⟩; positivity⟩
    set ρ : ℝ := sInf S with hρ
    have hρnn : 0 ≤ ρ := by
      rw [hρ]; exact le_csInf hSne (by rintro b ⟨s, _, rfl⟩; positivity)
    have hbig : ∀ s, ρ < |s| → P s := by
      intro s hs
      have hlt : sInf S < |s| := by rw [← hρ]; exact hs
      obtain ⟨b, hbS, hblt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      obtain ⟨s₀, hPs₀, hb_eq⟩ := hbS
      exact hmono s₀ s hPs₀ (le_of_lt (by rw [hb_eq] at hblt; exact hblt))
    have hsmall : ∀ s, |s| < ρ → ¬ P s := by
      intro s hs hPs
      have hle : ρ ≤ |s| := by
        rw [hρ]; exact csInf_le hSbdd ⟨s, hPs, rfl⟩
      linarith
    have hzero : ∀ s, |s| < ρ → gg s = 0 := fun s hs => hP0 s (hsmall s hs)
    have hgood : ∀ s, ρ < |s| → gg s = Gf s := by
      intro s hs
      have hs0 : s ≠ 0 := by
        intro h; subst h; rw [abs_zero] at hs; linarith
      exact hP1 s hs0 (hbig s hs)
    rcases eq_or_lt_of_le hρnn with hρ0 | hρpos
    · have hggG : gg = Gf := by
        funext s
        rcases eq_or_ne s 0 with h | h
        · subst h; exact hgg0
        · exact hgood s (by rw [← hρ0]; exact abs_pos.mpr h)
      rw [hggG]
      exact hboundG r
    · rcases lt_trichotomy r ρ with hr | hr | hr
      · rcases lt_trichotomy r (-ρ) with hr' | hr' | hr'
        · have habs : ρ < |r| := by rw [abs_of_neg (by linarith)]; linarith
          have hGG : gg =ᶠ[𝓝 r] Gf := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
          exact hboundG r
        · subst hr'
          rcases l with _ | l'
          · simp only [iteratedDeriv_zero]
            by_cases hP : P (-ρ)
            · rw [hP1 (-ρ) (by linarith) hP]
              simpa only [iteratedDeriv_zero] using hboundG (-ρ)
            · rw [hP0 (-ρ) hP, norm_zero, mul_zero]
              exact hC₀
          · have hz : iteratedDeriv (l' + 1) gg (-ρ) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right (by linarith : -ρ < ρ)
                (fun y hy => hzero y (by rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩)) l'
            rw [hz, norm_zero, mul_zero]
            exact hC₀
        · have habs : |r| < ρ := by rw [abs_lt]; exact ⟨by linarith, hr⟩
          have hGG : gg =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hzero s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l, iteratedDeriv_zeroFun]
          simp only [norm_zero, mul_zero]
          exact hC₀
      · subst hr
        rcases l with _ | l'
        · simp only [iteratedDeriv_zero]
          by_cases hP : P ρ
          · rw [hP1 ρ hρpos.ne' hP]
            simpa only [iteratedDeriv_zero] using hboundG ρ
          · rw [hP0 ρ hP, norm_zero, mul_zero]
            exact hC₀
        · have hz : iteratedDeriv (l' + 1) gg ρ = 0 :=
            iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hρpos
              (fun y hy => hzero y (by rw [abs_of_pos hy.1]; exact hy.2)) l'
          rw [hz, norm_zero, mul_zero]
          exact hC₀
      · have habs : ρ < |r| := by rw [abs_of_pos (by linarith)]; linarith
        have hGG : gg =ᶠ[𝓝 r] Gf := by
          refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
          exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
        rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
        exact hboundG r
  · have hnone : ∀ s, ¬ P s := fun s hs => hne ⟨s, hs⟩
    have hg0 : gg = fun _ => (0:ℂ) := funext (fun s => hP0 s (hnone s))
    rw [hg0, iteratedDeriv_zeroFun]
    simp only [norm_zero, mul_zero]
    exact hC₀

lemma arcT_cuspW_imagAxis (t : ℝ) (ht : 0 < t) : cuspW (Work.Kernels.imagAxis t ht) = 1 + t := by
  have hcoe : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  have him : (Work.Kernels.imagAxis t ht).im = t := by
    rw [← UpperHalfPlane.coe_im, hcoe]
    simp
  have hre : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = 0 := by
    rw [hcoe]; simp
  unfold cuspW
  rw [him, hre]
  simp

lemma arcT_cuspG_imagAxis_one (t : ℝ) (ht : 0 < t) (M : ℝ) :
    cuspG (Work.Kernels.imagAxis t ht) M 1 = (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  unfold cuspG
  rw [arcT_cuspW_imagAxis t ht, norm_Ept_imagAxis t ht, zpow_one]

/-- The model estimate at a contour point. -/
lemma arcT_mk_bound_axis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧ ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t),
      ‖MK ℓ d τ (Work.Kernels.imagAxis t ht) - AexpZ (Gcusp ℓ d) τ (Work.Kernels.imagAxis t ht)‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, M, hC, hM, hb⟩ := CuspExp.cuspModel_bound ℓ d hd hK
  refine ⟨C, M, hC, hM, fun τ hτ t ht => ?_⟩
  have h1 := hb τ hτ (Work.Kernels.imagAxis t ht)
  rw [arcT_cuspW_imagAxis t ht, norm_Ept_imagAxis t ht] at h1
  exact h1

/-- The kernel estimate at a contour point `z = it`, `t ≥ T`, in terms of `Aexp`. -/
lemma arcT_kernel_axis_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C M T : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 < T ∧ ∀ τ ∈ K, ∀ (t : ℝ), T ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨Cm, Mm, hCm, hMm, hm⟩ := arcT_mk_bound_axis ℓ d hd hK
  obtain ⟨T, hT, C, hC, hCb⟩ := CuspExp.kernelKfun_cuspExp ℓ (K := K) hK
  refine ⟨C + Cm, max 3 Mm, max T 1, by positivity, by positivity, lt_max_of_lt_left hT,
    fun τ hτ t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hT1 : (0 : ℝ) < max T 1 := lt_max_of_lt_left hT
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le hT1 ht
  set z : ℍ := Work.Kernels.imagAxis t htpos with hz
  have hzim : z.im = t := by
    rw [hz]
    rw [← UpperHalfPlane.coe_im, show ((Work.Kernels.imagAxis t htpos : ℍ) : ℂ)
      = (t : ℂ) * Complex.I from rfl]
    simp
  have hAz : Aexp (Gcusp ℓ d) τ t = AexpZ (Gcusp ℓ d) τ z := by
    rw [hz]; exact (AexpZ_imagAxis _ _ _ htpos).symm
  have hsplit : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t =
      (Work.Kernels.Kfun ℓ d τ z - MK ℓ d τ z) + (MK ℓ d τ z - AexpZ (Gcusp ℓ d) τ z) := by
    rw [hAz, Work.Kernels.Kaxis, dif_pos htpos, hz]
    ring
  rcases hd with h8 | h24
  · subst h8
    obtain ⟨hKp, _⟩ := hCb τ hτ z (by rw [hzim]; exact htT)
    have h1 : ‖Work.Kernels.Kfun ℓ 8 τ z - MK ℓ 8 τ z‖ ≤ C * cuspG z 3 1 := hKp
    have h2 : ‖MK ℓ 8 τ z - AexpZ (Gcusp ℓ 8) τ z‖ ≤ Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) := by
      have h := hm τ hτ t htpos
      rwa [← hz] at h
    have h3 : ‖(Work.Kernels.Kfun ℓ 8 τ z - MK ℓ 8 τ z) + (MK ℓ 8 τ z - AexpZ (Gcusp ℓ 8) τ z)‖
        ≤ C * cuspG z 3 1 + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) :=
      le_trans (norm_add_le _ _) (add_le_add h1 h2)
    rw [hsplit]
    refine le_trans h3 ?_
    rw [arcT_cuspG_imagAxis_one t htpos, hz] at *
    have hw : (1:ℝ) ≤ 1 + t := by linarith
    have he : (0:ℝ) < Real.exp (-(Real.pi * t)) := Real.exp_pos _
    have h3' := Real.rpow_le_rpow_of_exponent_le hw (le_max_left (3:ℝ) Mm)
    have hmm' := Real.rpow_le_rpow_of_exponent_le hw (le_max_right (3:ℝ) Mm)
    have hG : (0:ℝ) ≤ (1 + t) ^ max 3 Mm := Real.rpow_nonneg (by linarith) _
    have h3n : (0:ℝ) ≤ (1 + t) ^ (3:ℝ) := Real.rpow_nonneg (by linarith) _
    have hmn : (0:ℝ) ≤ (1 + t) ^ Mm := Real.rpow_nonneg (by linarith) _
    have hkey : C * ((1 + t) ^ (3:ℝ) * Real.exp (-(Real.pi * t)))
        + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t))
        ≤ (C + Cm) * (1 + t) ^ max 3 Mm * Real.exp (-(Real.pi * t)) := by
      nlinarith [h3', hmm', hG, he, hC.le, hCm.le, h3n, hmn,
        mul_pos hC he, mul_pos hCm he]
    exact hkey
  · subst h24
    obtain ⟨_, hKm⟩ := hCb τ hτ z (by rw [hzim]; exact htT)
    have h1 : ‖Work.Kernels.Kfun ℓ 24 τ z - MK ℓ 24 τ z‖ ≤ C * cuspG z 3 1 := hKm
    have h2 : ‖MK ℓ 24 τ z - AexpZ (Gcusp ℓ 24) τ z‖ ≤ Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) := by
      have h := hm τ hτ t htpos
      rwa [← hz] at h
    have h3 : ‖(Work.Kernels.Kfun ℓ 24 τ z - MK ℓ 24 τ z) + (MK ℓ 24 τ z - AexpZ (Gcusp ℓ 24) τ z)‖
        ≤ C * cuspG z 3 1 + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) :=
      le_trans (norm_add_le _ _) (add_le_add h1 h2)
    rw [hsplit]
    refine le_trans h3 ?_
    rw [arcT_cuspG_imagAxis_one t htpos, hz] at *
    have hw : (1:ℝ) ≤ 1 + t := by linarith
    have he : (0:ℝ) < Real.exp (-(Real.pi * t)) := Real.exp_pos _
    have h3' := Real.rpow_le_rpow_of_exponent_le hw (le_max_left (3:ℝ) Mm)
    have hmm' := Real.rpow_le_rpow_of_exponent_le hw (le_max_right (3:ℝ) Mm)
    have hG : (0:ℝ) ≤ (1 + t) ^ max 3 Mm := Real.rpow_nonneg (by linarith) _
    have h3n : (0:ℝ) ≤ (1 + t) ^ (3:ℝ) := Real.rpow_nonneg (by linarith) _
    have hmn : (0:ℝ) ≤ (1 + t) ^ Mm := Real.rpow_nonneg (by linarith) _
    have hkey : C * ((1 + t) ^ (3:ℝ) * Real.exp (-(Real.pi * t)))
        + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t))
        ≤ (C + Cm) * (1 + t) ^ max 3 Mm * Real.exp (-(Real.pi * t)) := by
      nlinarith [h3', hmm', hG, he, hC.le, hCm.le, h3n, hmn,
        mul_pos hC he, mul_pos hCm he]
    exact hkey


/-! ## The cusp expansion on `arcT` -/

theorem arcT_tail_aux (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp (Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨C, M, T, hC, hM, hT, hb⟩ :=
    arcT_kernel_axis_bound ℓ d hd (K := closure (arcT : Set ℍ)) isCompact_closure_arcT'
  obtain ⟨B, hB0, hB⟩ := arcT_smallT ℓ d hd (max T 1) (le_max_right _ _)
  have hT1 : (1 : ℝ) ≤ max T 1 := le_max_right _ _
  have hTle : T ≤ max T 1 := le_max_left _ _
  refine ⟨max C B, M, max T 1, lt_of_lt_of_le hC (le_max_left _ _), hM, by linarith, ?_⟩
  intro τ t hτ ht
  have hR0 : (0 : ℝ) ≤ max C B := le_trans hC.le (le_max_left _ _)
  by_cases htT : t ≤ max T 1
  · have hBt := hB τ t hτ ht htT
    refine le_trans hBt ?_
    have hp1 : (1 : ℝ) ≤ (1 + t) ^ M := Real.one_le_rpow (by linarith) hM
    have hq1 : (1 : ℝ) ≤ Real.exp (-(Real.pi * (t - max T 1))) :=
      Real.one_le_exp (by nlinarith [Real.pi_pos, htT])
    have h2 : (1 : ℝ) ≤ (1 + t) ^ M * Real.exp (-(Real.pi * (t - max T 1))) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (1 + t) ^ M * Real.exp (-(Real.pi * (t - max T 1))) :=
            mul_le_mul hp1 hq1 zero_le_one (Real.rpow_nonneg (by linarith) M)
    calc B ≤ max C B := le_max_right _ _
      _ = (max C B) * 1 := by ring
      _ ≤ (max C B) * ((1 + t) ^ M * Real.exp (-(Real.pi * (t - max T 1)))) :=
          mul_le_mul_of_nonneg_left h2 hR0
      _ = (max C B) * (1 + t) ^ M * Real.exp (-(Real.pi * (t - max T 1))) := by ring
  · rw [not_le] at htT
    have hCt := hb τ (subset_closure hτ) t (le_trans hTle (le_of_lt htT))
    refine le_trans hCt ?_
    have hq : Real.exp (-(Real.pi * t)) ≤ Real.exp (-(Real.pi * (t - max T 1))) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hT1])
    have hpn : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (by linarith) M
    have hCm : C ≤ max C B := le_max_left _ _
    calc C * (1 + t) ^ M * Real.exp (-(Real.pi * t))
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - max T 1))) := by
          exact mul_le_mul_of_nonneg_left hq (mul_nonneg hC.le hpn)
      _ ≤ (max C B) * (1 + t) ^ M * Real.exp (-(Real.pi * (t - max T 1))) := by
          have h1 : C * (1 + t) ^ M ≤ (max C B) * (1 + t) ^ M :=
            mul_le_mul_of_nonneg_right hCm hpn
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)

/-! ## The `r`-seminorm bound for the layer on `arcT` -/

theorem arcT_paperLayer_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn DomainD (G i j))
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpoly : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ arcT →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => paperLayer G ℓ d τ s) r‖
        ≤ c := by
  intro k l
  obtain ⟨c1, hc1, h1⟩ := layerLow_local_seminorm ℓ d hd (K := arcT) hflat k l
  obtain ⟨c2, hc2, h2⟩ := layerTrunc_local_seminorm ℓ d hd G (K := arcT) hpoly k l
  obtain ⟨c3, N3, hc3, h3⟩ := highPart_seminorm_scaled G hG k l
  have h3' : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ arcT →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
        ≤ c3 * max (14 ^ N3) 1 := by
    intro τ r hτ
    have hb := h3 τ r (arcT_subset_DomainD hτ)
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsB : Work.Kernels.scale τ ≤ 14 := arcT_scale_le hτ
    have hN : (Work.Kernels.scale τ) ^ N3 ≤ max (14 ^ N3) 1 := by
      rcases le_or_gt 0 N3 with h | h
      · exact le_trans (Real.rpow_le_rpow (le_trans zero_le_one hs1) hsB h) (le_max_left _ _)
      · have h2'' : (Work.Kernels.scale τ) ^ N3 ≤ (1 : ℝ) ^ N3 :=
          Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hs1 (le_of_lt h)
        rw [Real.one_rpow] at h2''
        exact h2''.trans (le_max_right _ _)
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
        ≤ c3 * (Work.Kernels.scale τ) ^ N3 := hb
      _ ≤ c3 * max (14 ^ N3) 1 := mul_le_mul_of_nonneg_left hN hc3
  refine ⟨c1 + c2 + c3 * max (14 ^ N3) 1, by positivity, fun τ r hτ => ?_⟩
  obtain ⟨hcdL, hcdT, hcdH⟩ := layerPieces_contDiff_of_mem ℓ d hd G (K := arcT) hflat hpoly τ hτ
  have hsplitL : iteratedDeriv l
        (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r :=
    iteratedDeriv_add (f := fun s : ℝ => layerLow ℓ d τ s)
      (g := fun s : ℝ => layerTrunc G ℓ d τ s)
      ((hcdL.contDiffAt).of_le le_top) ((hcdT.contDiffAt).of_le le_top)
  have hsplit : iteratedDeriv l (fun s : ℝ => paperLayer G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r := by
    have hfun : (fun s : ℝ => paperLayer G ℓ d τ s)
        = fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s + highPart G τ s := by
      funext s; rw [paperLayer]
    have hE : (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s + highPart G τ s)
        = (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s)
          + (fun s : ℝ => highPart G τ s) := rfl
    rw [hfun, hE, iteratedDeriv_add
      (f := fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s)
      (g := fun s : ℝ => highPart G τ s)
      (((hcdL.add hcdT).contDiffAt).of_le le_top) ((hcdH.contDiffAt).of_le le_top), hsplitL]
  rw [hsplit]
  have ha := h1 τ r hτ
  have hb := h2 τ r hτ
  have hc := h3' τ r hτ
  have htri : ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
      ≤ ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖ := by
    linarith [norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r),
      norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => highPart G τ s) r)]
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
        + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
        + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖ := by ring
    _ ≤ c1 + c2 + c3 * max (14 ^ N3) 1 := by linarith

theorem arcT_layer_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn DomainD (G i j))
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpoly : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ arcT →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layer G ℓ d τ s) r‖
        ≤ c := by
  intro k l
  obtain ⟨c, hc, hb⟩ := arcT_paperLayer_seminorm ℓ d hd G hG hflat hpoly k l
  refine ⟨c, hc, ?_⟩
  intro τ r hτ
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        have hz : layer G ℓ d τ 0 = 0 := by rw [layer]; simp
        simp only [iteratedDeriv_zero, hz, norm_zero, mul_zero]
        exact hc
      · have hfun : (fun s : ℝ => layer G ℓ d τ s)
            = fun s : ℝ => (if s = 0 then 0 else paperLayer G ℓ d τ s) := by
          funext s; rw [layer]
        rw [hfun, punctured_iteratedDeriv (arcT_paperLayer_neg G ℓ d τ)
          ((arcT_paperLayer_contDiff_of_mem ℓ d hd G hflat hpoly τ hτ).differentiable (by simp))
          l hl]
        simpa using hb τ 0 hτ
    · have hz : (0 : ℝ) ^ k = 0 := zero_pow hk.ne'
      simp only [abs_zero, hz, zero_mul]
      exact hc
  · have heq : (fun s : ℝ => layer G ℓ d τ s)
        =ᶠ[𝓝 r] (fun s : ℝ => paperLayer G ℓ d τ s) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs
      rw [layer, if_neg hs]
    rw [iteratedDeriv_congr_of_eventuallyEq heq l]
    exact hb τ r hτ

/-! ## The target -/

theorem seminormK_cusp0_arc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im → (ModularGroup.S • w).im ≤ 2 →
        (‖(w : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10 ∨
          ‖(w : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10) →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖ ≤ C := by
  intro k l
  set G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ := Gcusp ℓ d with hGdef
  have hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn DomainD (G i j) :=
    fun i j => GcuspInP (ℓ := ℓ) d i j
  have h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0 := by
    intro h8d j
    rw [hGdef, Gcusp, if_pos h8d]
    funext τ
    fin_cases j <;> simp [Gcusp8]
  have hflat := arcT_flat ℓ d hd
  have hpoly := arcT_tail_aux ℓ d hd
  have hlayer := arcT_layer_seminorm ℓ d hd G hG hflat hpoly
  have h0 : ∀ τ : UpperHalfPlane, τ ∈ arcT →
      layer G ℓ d τ 0 = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0 := by
    intro τ _
    have h1 : layer G ℓ d τ 0 = 0 := by rw [layer]; simp
    have h2 : Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0 = 0 := by
      simp [Work.Kernels.kernelTransform]
    rw [h1, h2]
  have hagr : ∀ τ : UpperHalfPlane, τ ∈ arcT → ∀ r : ℝ, r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
        layer G ℓ d τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
    intro τ hτ r hr hInt
    rw [layer, if_neg hr]
    exact Work.Asymptotics.Compact.local_agreement ℓ d hd G hG h8 hflat hpoly τ r hτ hr hInt
  obtain ⟨C, hC, hbound⟩ :=
    arcT_kernelTransform_of_layer ℓ d (fun τ r => layer G ℓ d τ r) h0 hagr hlayer k l
  exact ⟨C, hC, fun w r hw h1 h2 h3 => hbound w r ⟨hw, h1, h2, h3⟩⟩

end Work.Asymptotics


