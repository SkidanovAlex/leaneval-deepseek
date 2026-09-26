/-
# A branch-clean copy of the layer/contour transfer lemma

`Submission/Work/Asymptotics/kernelTransform_seminorm_of_layer_moderate.lean` proves the transfer
of a `τ`-dependent seminorm bound from a layer `F₂` to the naive contour integral
`kernelTransform K τ ·`.  That module transitively imports `MiddleRange.Main`, which declares
`Work.Asymptotics.continuous_jInvariantFun`; the sharp tile analysis
(`Tile/Kplus_tile_bound`, `Kaxis_tile_flat_below_pole`, `EtailE`, ...) transitively imports
`KPlusXiDefs`, which declares the same name, so **no single module can import both branches**.
The present file re-proves the transfer lemma in the branch-clean way (its argument is verbatim
the one in `kernelTransform_seminorm_of_layer_moderate_aux`, which uses only
`integrableOn_kaxis_exp_mono_abs` and the one-sided vanishing lemmas of
`Submission/Work/Asymptotics/kernelTransform_seminorm_of_layer.lean`), so that the assembly of
the cusp-`±1` tile bound can live in the tile branch.

## Main results

* `Work.Asymptotics.tile_layer_transfer_aux`;
* `Work.Asymptotics.tile_layer_transfer`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics

/-- **Transfer of a `τ`-dependent seminorm bound from a layer to the naive contour integral.**

Suppose `F₂` agrees with `kernelTransform Kf τ ·` at `0` and at every `r ≠ 0` where the contour
integrand is integrable, and suppose the `(k,l)`-seminorms of `F₂` are bounded by an arbitrary
nonnegative function `R τ` on `K`.  Then the same holds for `kernelTransform Kf τ ·`.

The argument is the threshold argument: `kernelTransform` is `0` wherever the integrand is not
integrable, and the integrability set is a threshold set in `|r|`
(`integrableOn_kaxis_exp_mono_abs`). -/
theorem tile_layer_transfer_aux
    (Kf : UpperHalfPlane → UpperHalfPlane → ℂ) (F₂ : UpperHalfPlane → ℝ → ℂ)
    (R : UpperHalfPlane → ℝ) (k l : ℕ) {K : Set UpperHalfPlane}
    (hR : ∀ τ ∈ K, 0 ≤ R τ)
    (h0 : ∀ τ ∈ K, F₂ τ 0 = Work.Kernels.kernelTransform Kf τ 0)
    (hagr : ∀ τ ∈ K, ∀ r : ℝ, r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      F₂ τ r = Work.Kernels.kernelTransform Kf τ r)
    (hsemi : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖ ≤ R τ) :
    ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => Work.Kernels.kernelTransform Kf τ s) r‖ ≤ R τ := by
  intro τ r hτ
  set G : ℝ → ℂ := fun s => F₂ τ s with hG
  set gg : ℝ → ℂ := fun s => Work.Kernels.kernelTransform Kf τ s with hgg
  set P : ℝ → Prop := fun s => MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) with hP
  have hPdef : ∀ s, P s = MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := fun s => rfl
  have hRnn : (0:ℝ) ≤ R τ := hR τ hτ
  have hboundG : ∀ s : ℝ, (|s| ^ k) * ‖iteratedDeriv l G s‖ ≤ R τ :=
    fun s => hsemi τ s hτ
  have hP0 : ∀ s, ¬ P s → gg s = 0 := by
    intro s hs
    have hI : ¬ MeasureTheory.IntegrableOn
        (fun t : ℝ => Work.Kernels.Kaxis Kf τ t
          * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
      rwa [hPdef s] at hs
    have hz : (∫ t in Set.Ioi (0:ℝ), Work.Kernels.Kaxis Kf τ t
        * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) = 0 :=
      integral_undef hI
    rw [hgg]
    simp only [Work.Kernels.kernelTransform, hz, mul_zero]
  have hP1 : ∀ s, s ≠ 0 → P s → gg s = G s := by
    intro s hs0 hs
    rw [hgg, hG]
    exact (hagr τ hτ s hs0 (by rwa [hPdef s] at hs)).symm
  have hgg0 : gg 0 = G 0 := by
    rw [hgg, hG]
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
    have hgood : ∀ s, ρ < |s| → gg s = G s := by
      intro s hs
      have hs0 : s ≠ 0 := by
        intro h; subst h; rw [abs_zero] at hs; linarith
      exact hP1 s hs0 (hbig s hs)
    rcases eq_or_lt_of_le hρnn with hρ0 | hρpos
    · have hggG : gg = G := by
        funext s
        rcases eq_or_ne s 0 with h | h
        · subst h; exact hgg0
        · exact hgood s (by rw [← hρ0]; exact abs_pos.mpr h)
      rw [hggG]
      exact hboundG r
    · rcases lt_trichotomy r ρ with hr | hr | hr
      · rcases lt_trichotomy r (-ρ) with hr' | hr' | hr'
        · have habs : ρ < |r| := by rw [abs_of_neg (by linarith)]; linarith
          have hGG : gg =ᶠ[𝓝 r] G := by
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
              exact hRnn
          · have hz : iteratedDeriv (l' + 1) gg (-ρ) = 0 :=
              iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right (by linarith : -ρ < ρ)
                (fun y hy => hzero y (by rw [abs_lt]; exact ⟨by linarith [hy.1], hy.2⟩)) l'
            rw [hz, norm_zero, mul_zero]
            exact hRnn
        · have habs : |r| < ρ := by rw [abs_lt]; exact ⟨by linarith, hr⟩
          have hGG : gg =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := by
            refine Filter.eventually_of_mem ?_ (fun s hs => hzero s hs)
            exact IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) habs
          rw [iteratedDeriv_congr_of_eventuallyEq hGG l, iteratedDeriv_zeroFun]
          simp only [norm_zero, mul_zero]
          exact hRnn
      · subst hr
        rcases l with _ | l'
        · simp only [iteratedDeriv_zero]
          by_cases hP : P ρ
          · rw [hP1 ρ hρpos.ne' hP]
            simpa only [iteratedDeriv_zero] using hboundG ρ
          · rw [hP0 ρ hP, norm_zero, mul_zero]
            exact hRnn
        · have hz : iteratedDeriv (l' + 1) gg ρ = 0 :=
            iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hρpos
              (fun y hy => hzero y (by rw [abs_of_pos hy.1]; exact hy.2)) l'
          rw [hz, norm_zero, mul_zero]
          exact hRnn
      · have habs : ρ < |r| := by rw [abs_of_pos (by linarith)]; linarith
        have hGG : gg =ᶠ[𝓝 r] G := by
          refine Filter.eventually_of_mem ?_ (fun s hs => hgood s hs)
          exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) habs
        rw [iteratedDeriv_congr_of_eventuallyEq hGG l]
        exact hboundG r
  · have hnone : ∀ s, ¬ P s := fun s hs => hne ⟨s, hs⟩
    have hg0 : gg = fun _ => (0:ℂ) := funext (fun s => hP0 s (hnone s))
    rw [hg0, iteratedDeriv_zeroFun]
    simp only [norm_zero, mul_zero]
    exact hRnn

/-- **The branch-clean layer transfer.**  If a layer `F₂` for the kernel `K = Kfun ℓ d` agrees
with the naive contour integral at `r = 0` and at every `r ≠ 0` where the contour integrand is
integrable, and its `r`-seminorms grow at most like `C (B τ)^N` on `K`, then the naive contour
integral itself has the same growth bound with the *same* `C` and `N`. -/
theorem tile_layer_transfer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (F₂ : UpperHalfPlane → ℝ → ℂ) {K : Set UpperHalfPlane}
    {B : UpperHalfPlane → ℝ}
    (hB1 : ∀ τ ∈ K, 1 ≤ B τ)
    (h0 : ∀ τ ∈ K, F₂ τ 0 = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0)
    (hagr : ∀ τ ∈ K, ∀ r : ℝ, r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      F₂ τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r)
    (hsemi : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => F₂ τ s) r‖ ≤ C * (B τ) ^ N) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
        ≤ C * (B τ) ^ N := by
  have _hd : d = 8 ∨ d = 24 := hd
  intro k l
  obtain ⟨C, N, hC, hN, hbound⟩ := hsemi k l
  refine ⟨C, N, hC, hN, ?_⟩
  have hR : ∀ τ ∈ K, 0 ≤ C * (B τ) ^ N :=
    fun τ hτ => mul_nonneg hC (Real.rpow_nonneg (by linarith [hB1 τ hτ]) N)
  intro τ r hτ
  exact tile_layer_transfer_aux (Work.Kernels.Kfun ℓ d) F₂
    (fun τ => C * (B τ) ^ N) k l hR h0 hagr (fun τ r hτ => hbound τ r hτ) τ r hτ

end Work.Asymptotics
