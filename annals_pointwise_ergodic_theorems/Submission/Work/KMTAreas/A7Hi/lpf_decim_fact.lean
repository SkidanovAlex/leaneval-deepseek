import Mathlib
import Submission.Work.KMTAreas.A7Hi2.lacunaryMaxPieceProved
import Submission.Work.KMTPlan.A6.iwConv_comp_of_symbol
import Submission.Work.KMTAreas.A7Hi.fejerSymbolFullGrid
import Submission.Work.KMTAreas.A7Hi.summable_iwKernel_iwSymbolSet_bump
import Submission.Work.KMTAreas.A7Hi.hasSum_fourierSeries_iwSymbolSet_bump
import Submission.Work.KMTAreas.A7Hi.memLp_two_iwSymbolSet_bump
import Submission.Work.KMTAreas.A7Hi.iwSymbolSet_torsFinset_mul_bump

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## The kernel of the `Q`-torsion IW symbol is the decimated kernel

`kmtProj ρ l k` is the IW multiplier with symbol
`ξ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} periodize (η_{≤k}) (ξ - α)` (`Work.KMTContract.kmtProj`, i.e.
`iwConv (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))`).

Here we identify the convolution kernel of the *torsion* symbol
`iwSymbolSet (Decim.torsFinset Q) (Decim.bump L)` — the symbol over the full `Q`-torsion set of
the level-`L` bump — with the *decimated kernel*
`Work.BourgainPlan.Thm52.decimatedKernel Q (etaCut kmtEta (-(L:ℤ)))` of the same level-`L` bump.
This is the kernel-level statement underlying the KMSZ (6.22) factorisation `lpf_decim_fact`:
it says that `iwConv (Decim.torsFinset Q) (Decim.bump L)` *is* the decimated-kernel operator
`h ↦ (y ↦ ∑'_j decimatedKernel Q (η_{≤-L}) (y - j) · h j)`.

The proof has two independent parts.

* The arithmetic-character factorisation `Work.KMTPlan.A6.IwKernelArithChar` writes the kernel as
  the torsion character sum `∑_{a < Q} e(-j a/Q)` times the continuous Fourier transform
  `cw (η_{≤-L}) j`.
* The torsion character sum is `Q · 1_{Q ∣ j}` (`Work.KMTAreas.A7Hi.sum_range_fourier_div`); and
  `cw (η_{≤-L}) j = ∫_{ℝ} η_{≤-L} θ e(-jθ) dθ` equals `∫_{-1/2}^{1/2} η_{≤-L} ξ e(jξ) dξ`, by the
  substitution `ξ ↦ -ξ` (using that `η` is even, hence `η_{≤-L}` is) and the support
  `|ξ| ≤ 2^{-L} ≤ 1/2` of `η_{≤-L}` for `L ≥ 1`. -/

/-- `2 ^ (-(L:ℤ)) ≤ 1/2` for `L ≥ 1`, i.e. the level-`L` bump is supported in the unit arc. -/
private lemma two_zpow_neg_le_half' {L : ℕ} (hL : 1 ≤ L) :
    (2 : ℝ) ^ (-(L : ℤ)) ≤ 1 / 2 := by
  have h1 : (2 : ℝ) ^ (-(L : ℤ)) = (1 / 2 : ℝ) ^ L := by
    rw [zpow_neg, zpow_natCast, one_div, ← inv_pow]
  rw [h1]
  calc (1 / 2 : ℝ) ^ L ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    _ = 1 / 2 := by norm_num

theorem iwKernel_torsFinset_bump_eq_decimatedKernel (Q L : ℕ) (hQ : 1 ≤ Q) (hL : 1 ≤ L)
    (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTPlan.A6.Decim.torsFinset Q)
        (Work.KMTPlan.A6.Decim.bump L)) j
      = Work.BourgainPlan.Thm52.decimatedKernel Q
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) j := by
  set Ψ : ℝ → ℂ := Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ)) with hΨ
  have hΨcont : Continuous Ψ := by
    rw [hΨ]; exact (Work.KMTContract.etaCutRegular (-(L : ℤ))).1.continuous
  have hΨcs : HasCompactSupport Ψ := by
    rw [hΨ]; exact Work.KMTPlan.A6.DecimComp.hasCompactSupport_etaCut L
  have hΨint : Integrable Ψ := hΨcont.integrable_of_hasCompactSupport hΨcs
  have hΨeven : ∀ x : ℝ, Ψ (-x) = Ψ x := by
    intro x
    rw [hΨ]
    rw [(Work.KMTContract.etaCutRegular (-(L : ℤ))).2.1,
      (Work.KMTContract.etaCutRegular (-(L : ℤ))).2.1]
    rw [show -x / (2 : ℝ) ^ (-(L : ℤ)) = -(x / (2 : ℝ) ^ (-(L : ℤ))) by ring,
      Work.KMTContract.kmtEta_neg]
  have hΨzero : ∀ x : ℝ, (1 / 2 : ℝ) ≤ |x| → Ψ x = 0 := by
    intro x hx
    rw [hΨ]
    exact (Work.KMTContract.etaCutRegular (-(L : ℤ))).2.2 x
      (le_trans (two_zpow_neg_le_half' hL) hx)
  -- the arithmetic-character factorisation of the kernel
  have h1 : Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTPlan.A6.Decim.torsFinset Q)
          (Work.KMTPlan.A6.Decim.bump L)) j
      = (∑ α ∈ Work.KMTPlan.A6.Decim.torsFinset Q, fourier (T := 1) (-j) α)
        * Work.KMTAreas.A7.cw Ψ j := by
    have h := Work.KMTPlan.A6.IwKernelArithChar (Work.KMTPlan.A6.Decim.torsFinset Q) hΨint j
    simpa only [Work.KMTPlan.A6.Decim.bump, hΨ] using h
  -- the torsion character sum
  have hsum : (∑ a ∈ Finset.range Q, fourier (T := 1) (-j)
        (Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ)))
      = if (Q : ℤ) ∣ (-j) then (Q : ℂ) else 0 := by
    have h := Work.KMTAreas.A7Hi.sum_range_fourier_div Q (-j)
    rw [← h]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Work.BourgainPlan.IonescuWainger.arcPt]
    norm_num
  have h2 : (∑ α ∈ Work.KMTPlan.A6.Decim.torsFinset Q, fourier (T := 1) (-j) α)
      = if (Q : ℤ) ∣ j then (Q : ℂ) else 0 := by
    rw [show Work.KMTPlan.A6.Decim.torsFinset Q
        = (Finset.range Q).image
            (fun a : ℕ => Work.BourgainPlan.IonescuWainger.arcPt Q (a : ℤ)) from rfl]
    rw [Finset.sum_image]
    · rw [hsum]
      by_cases hj : (Q : ℤ) ∣ j
      · rw [if_pos (Int.dvd_neg.mpr hj), if_pos hj]
      · rw [if_neg (fun hh => hj (Int.dvd_neg.mp hh)), if_neg hj]
    · intro a ha b hb hab
      exact Work.KMTPlan.A6.DecimComp.injOn_arcPt hQ ha hb hab
  -- the continuous Fourier transform of the bump
  set G : ℝ → ℂ := fun ξ => Ψ ξ *
    Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ξ : ℂ))) with hG
  have hcomp : (∫ ξ : ℝ, G (-ξ)) = ∫ ξ : ℝ, G ξ := by
    have h := MeasureTheory.Measure.integral_comp_mul_left G (-1)
    simpa using h
  have hA : Work.KMTAreas.A7.cw Ψ j = ∫ ξ : ℝ, G ξ := by
    rw [Work.KMTAreas.A7.cw, ← hcomp]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only [hG, Work.KMTAreas.A7.ee]
    rw [hΨeven]
    congr 1
    rw [show -(j : ℝ) * ξ = (j : ℝ) * (-ξ) by ring]
    push_cast
    ring
  have hGzero : ∀ θ : ℝ, θ ∉ Set.Ioc (-(1 / 2) : ℝ) (1 / 2) → G θ = 0 := by
    intro θ hθ
    rw [Set.mem_Ioc, not_and_or, not_lt] at hθ
    have habs : (1 / 2 : ℝ) ≤ |θ| := by
      rcases hθ with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        linarith
    simp only [hG]
    rw [hΨzero θ habs, zero_mul]
  have hB : (∫ ξ : ℝ, G ξ) = ∫ ξ in (-(1 / 2))..(1 / 2), G ξ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hGzero).symm
  have hcw : Work.KMTAreas.A7.cw Ψ j = ∫ ξ in (-(1 / 2))..(1 / 2), G ξ := hA.trans hB
  rw [h1, h2, hcw, Work.BourgainPlan.Thm52.decimatedKernel]
  by_cases hj : (Q : ℤ) ∣ j
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]; ring

/-! ## The KMSZ (6.22) decimation factorisation of the low-pass walk

The main theorem `lpf_decim_fact`: for the *fine* level `-(m₀+n)` the IW projection
`kmtProj ρ l₁ (-(m₀+n))` factors as the decimated-kernel operator of the fine bump at the period
`Q = iwQl ρ l₁` composed with the *coarse* projection `kmtProj ρ l₁ (-C₀)`, under the two
separation conditions `3Q < 2^{C₀}` and `C₀ + 1 ≤ m₀ + n`.

The proof is the symbol computation
`iwSymbolSet T (bump L) · iwSymbolSet A (bump C₀) = iwSymbolSet A (bump L)`
(`Work.KMTAreas.A7Hi.iwSymbolSet_torsFinset_mul_bump`, with `A = iwArithFreqs ρ l₁ ⊆ T`),
followed by the composition law `Work.KMTPlan.A6.iwConv_comp_of_symbol` for the convolution
kernels of IW symbols, and the identification of the kernel of the torsion symbol with the
decimated kernel (`iwKernel_torsFinset_bump_eq_decimatedKernel`). -/

theorem lpf_decim_fact (ρ : ℝ) (l₁ m₀ C₀ n : ℕ) (Cρ : ℝ)
    (hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)))
    (hnarrow : 3 * Work.Analysis.IonescuWainger.iwQl ρ l₁ < 2 ^ C₀)
    (hfine : C₀ + 1 ≤ m₀ + n) (f : ℤ →₀ ℂ) :
    Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (n : ℤ))) (⇑f)
      = fun y : ℤ => ∑' j : ℤ,
          Work.BourgainPlan.Thm52.decimatedKernel (Work.Analysis.IonescuWainger.iwQl ρ l₁)
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
              (-((m₀ : ℤ) + (n : ℤ)))) (y - j)
          * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) j := by
  set Q : ℕ := Work.Analysis.IonescuWainger.iwQl ρ l₁ with hQdef
  set L : ℕ := m₀ + n with hLdef
  set A : Finset Circ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ with hAdef
  set T : Finset Circ := Work.KMTPlan.A6.Decim.torsFinset Q with hTdef
  have hQ : 1 ≤ Q := by
    rw [hQdef]; exact Work.Analysis.IonescuWainger.iwQl_pos
  have hC₀ : 1 ≤ C₀ := by
    by_contra h
    have h0 : C₀ = 0 := by omega
    subst h0
    simp only [pow_zero, Nat.lt_one_iff] at hnarrow
    omega
  have hL1 : 1 ≤ L := by rw [hLdef]; omega
  have hAT : A ⊆ T := by
    intro α hα
    rw [hTdef]
    exact Work.KMTPlan.A6.DecimComp.mem_torsFinset_of_mem_iwArithFreqs hα
  -- the three analytic inputs of the composition law, at the fine and the coarse level
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet T (Work.KMTPlan.A6.Decim.bump L)
      * Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump C₀)
      = Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L) :=
    iwSymbolSet_torsFinset_mul_bump Q C₀ L hQ hC₀ hnarrow hfine A hAT
  have hmemD : MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump C₀)) 2
      Work.Analysis.IonescuWainger.circleMeasure :=
    memLp_two_iwSymbolSet_bump A C₀ hC₀
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ m : ℤ, ‖(⇑f : ℤ → ℂ) m‖ ≤ B := by
    refine ⟨∑ m ∈ f.support, ‖f m‖, fun m => ?_⟩
    by_cases hm : m ∈ f.support
    · exact Finset.single_le_sum (f := fun m : ℤ => ‖(⇑f : ℤ → ℂ) m‖)
        (fun i _ => norm_nonneg _) hm
    · have h0 : f m = 0 := by
        by_contra hne
        exact hm (Finsupp.mem_support_iff.mpr hne)
      rw [h0, norm_zero]
      exact Finset.sum_nonneg (fun i _ => norm_nonneg (f i))
  have hcomp := Work.KMTPlan.A6.iwConv_comp_of_symbol
    (A := T) (D := A) (Φ := Work.KMTPlan.A6.Decim.bump L)
    (Ψ := Work.KMTPlan.A6.Decim.bump C₀)
    hsym
    (summable_iwKernel_iwSymbolSet_bump T L)
    (hasSum_fourierSeries_iwSymbolSet_bump T L (summable_iwKernel_iwSymbolSet_bump T L))
    hmemD
    (summable_iwKernel_iwSymbolSet_bump A C₀)
    (f := (⇑f : ℤ → ℂ)) hB
  have hleft : Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + (n : ℤ))) (⇑f)
      = Work.Analysis.IWMultiplier.iwConv A (Work.KMTPlan.A6.Decim.bump L) (⇑f) := by
    have hk : (-((m₀ : ℤ) + (n : ℤ))) = -((L : ℕ) : ℤ) := by rw [hLdef]; push_cast; ring
    rw [Work.KMTContract.kmtProj, hk, Work.KMTPlan.A6.Decim.bump, hAdef]
  have hright : Work.Analysis.IWMultiplier.iwConv A (Work.KMTPlan.A6.Decim.bump C₀) (⇑f)
      = Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) := by
    simp only [Work.KMTContract.kmtProj, Work.KMTPlan.A6.Decim.bump, hAdef]
  have hΨeq : Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
          (-((m₀ : ℤ) + (n : ℤ))) := by
    rw [hLdef]; push_cast; ring
  -- the reindexing `∑_j a (y - j) b j = ∑_j a j b (y - j)`
  have hreindex : ∀ y' : ℤ, (∑' j : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) j
        * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) (y' - j))
      = ∑' j : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) (y' - j)
        * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) j := by
    intro y'
    let e : ℤ ≃ ℤ :=
      { toFun := fun j => y' - j, invFun := fun j => y' - j,
        left_inv := fun j => by ring, right_inv := fun j => by ring }
    have h := Equiv.tsum_eq e (fun k : ℤ => Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) k
        * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) (y' - k))
    have hcongr : (∑' b : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) (e b)
          * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) (y' - e b))
        = ∑' b : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) (y' - b)
          * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) b := by
      refine tsum_congr (fun b => ?_)
      have hb : e b = y' - b := rfl
      rw [hb, show y' - (y' - b) = b from by ring]
    rw [hcongr] at h
    exact h.symm
  rw [hleft, hcomp.symm]
  funext y
  rw [Work.Analysis.IWMultiplier.iwConv_apply, hright]
  simp only [smul_eq_mul]
  rw [show (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet T (Work.KMTPlan.A6.Decim.bump L)) j
        * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) (y - j))
      = ∑' j : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) j
          * Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) (⇑f) (y - j) from
      tsum_congr (fun j => by rw [iwKernel_torsFinset_bump_eq_decimatedKernel Q L hQ hL1])]
  rw [hreindex y]
  rw [hQdef, hΨeq]

end Work.KMTAreas.A7Hi
