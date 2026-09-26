import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.layerLow_local_seminorm
import Submission.Work.Asymptotics.paperLayer_local_seminorm
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.Compact.local_agreement
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.HFN.Compact.tail_on_compact

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology

namespace Work.HFN
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

/-! ## Evenness of the layer in the radial variable

Every occurrence of `r` in `paperLayer G ℓ d τ r` is through `r ^ 2`, so each piece — and hence
the layer — is an even function of `r`.  This is what makes the puncture `layer` at `r = 0`
harmless for the positive-order iterated derivatives (`punctured_iteratedDeriv`). -/

lemma sinSq_neg (r : ℝ) : sinSq (-r) = sinSq r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [sinSq, hsq]

lemma layerLow_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    layerLow ℓ d τ (-s) = layerLow ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerLow, sinSq, hsq]

lemma layerTrunc_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    layerTrunc G ℓ d τ (-s) = layerTrunc G ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [layerTrunc, sinSq, hsq]

lemma highPart_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (s : ℝ) :
    highPart G τ (-s) = highPart G τ s := by
  simp only [highPart, neg_sq]

lemma paperLayer_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    paperLayer G ℓ d τ (-s) = paperLayer G ℓ d τ s := by
  simp only [paperLayer]
  rw [layerLow_neg, layerTrunc_neg, highPart_neg]

/-- The layer is `C^∞` in the radial variable for `τ ∈ K`. -/
lemma paperLayer_contDiff_of_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
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

/-! ## The `r`-seminorms of the punctured layer on a compact subset of `𝒟` -/

/-- **The `r`-seminorm bound for the punctured layer `layer` on a compact `K ⊆ 𝒟`.**

`paperLayer = layerLow + layerTrunc + highPart`; the three pieces are bounded on `K` by
`layerLow_local_seminorm`/`paperLayer_local_seminorm` and `highPart_local_seminorm`, so
`paperLayer_local_seminorm` gives the bound for `paperLayer`.  Puncturing at `r = 0` does not
change the positive-order derivatives (`punctured_iteratedDeriv`, using that `paperLayer τ ·` is
even and differentiable), and the remaining cases at `r = 0` are trivial. -/
theorem layer_seminorm_on_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    (h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsub : K ⊆ Work.Asymptotics.DomainD)
    (hflatK : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpolyK : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layer G ℓ d τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨c, hc, hb⟩ := paperLayer_local_seminorm ℓ d hd G hG hK hsub hflatK hpolyK k l
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
      · -- positive order at `r = 0`: puncturing does not change the derivatives
        have hfun : (fun s : ℝ => layer G ℓ d τ s)
            = fun s : ℝ => (if s = 0 then 0 else paperLayer G ℓ d τ s) := by
          funext s; rw [layer]
        rw [hfun, punctured_iteratedDeriv (paperLayer_neg G ℓ d τ)
          ((paperLayer_contDiff_of_mem ℓ d hd G hflatK hpolyK τ hτ).differentiable (by simp)) l hl]
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

/-! ## Transfer from a layer to the naive contour integral -/

/-- **Transfer of the `r`-seminorm bound from a layer to the naive contour integral**, on a set
`K` of parameters.  This is `Work.Asymptotics.kernelTransform_seminorm_of_layer` with the
moderate-growth hypothesis replaced by a uniform bound on `K` and the two agreement clauses
restricted to `τ ∈ K` (and to `r ≠ 0`, the value at `r = 0` being supplied separately by `h0`).

The point is again that `Work.Kernels.kernelTransform` is `0` wherever the contour integrand is
not integrable (`integral_undef`), and that the set of `r` at which the integrand is integrable is
a threshold set in `|r|` (`integrableOn_kaxis_exp_mono_abs`).  Away from the threshold the
transform agrees with the layer, strictly inside it the transform vanishes (so all its iterated
derivatives vanish by the one-sided vanishing lemmas), and at the threshold itself the layer's
bound applies. -/
theorem kernelTransform_seminorm_of_layer_on_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
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

/-! ## The target -/

/-- **CKMRV Proposition 4.6, compact part.**  On a compact subset `K` of the `Γ(2)`-fundamental
domain `𝒟` the `r`-seminorms `|r|^k ∂_r^l` of the CKMRV contour integral are uniformly bounded.

The contour integral is transferred from the paper's layer `F₂` (built from the `low`/`trunc`/`high`
decomposition) by `kernelTransform_seminorm_of_layer_on_compact`; the layer's seminorms are bounded
on `K` by `layer_seminorm_on_compact`, whose inputs are the flatness of the kernel at the cusp `0`
(`flat_on_compact`) and the cusp-`i∞` expansion `K = Aexp G + O(t^M e^{-π(t-T₀)})`
(`tail_on_compact`); the agreement of the layer with the naive integral is `local_agreement`.

On `K` the poles of `z ↦ K(τ,z)` stay a positive distance from the contour, so all the constants
are uniform; the `τ`-dependence of the layer's own estimate is absorbed into a single bound by
compactness (`exists_scale_bound_of_isCompact`). -/
theorem kernelTransform_seminorm_on_compact (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖ ≤ C := by
  obtain ⟨G, hG, h8, htail⟩ := Compact.tail_on_compact ℓ d hd hK hsub
  have hflat := Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd hK hsub
  have hagr := Compact.local_agreement ℓ d hd G hG h8 hflat htail
  refine kernelTransform_seminorm_of_layer_on_compact ℓ d (fun τ r => layer G ℓ d τ r)
    ?_ ?_ ?_
  · intro τ hτ
    have h1 : layer G ℓ d τ 0 = 0 := by rw [layer]; simp
    have h2 : Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0 = 0 := by
      simp [Work.Kernels.kernelTransform]
    rw [h1, h2]
  · intro τ hτ r hr hInt
    rw [layer, if_neg hr]
    exact hagr τ r hτ hr hInt
  · intro k l
    exact layer_seminorm_on_compact ℓ d hd G hG h8 hK hsub hflat htail k l

end Work.HFN
