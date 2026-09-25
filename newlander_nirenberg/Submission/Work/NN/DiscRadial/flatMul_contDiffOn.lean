import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.DiscRadial.Setup
import Submission.Work.NN.DiscRadial.iterDerivBound
import Submission.Work.NN.Core.contDiff_flatMul

/-!
# `χ (z.2) * h z` is `C^k` where `h` is `C^k` with finite Hölder norm

Let `W ⊆ E` be open, `χ : ℝ → ℝ` smooth and vanishing for `u ≥ 2`, and let `h : E × ℝ → ℂ` be
`C^k` on the slab `W × (0,2)` with finite `C^{k,β}` norm there.  Then

  `z ↦ (χ z.2 : ℂ) * h z`

is `C^k` on the half space `W × (0,∞)`.

The mathematical point is that on `W × (0,2)` the product is `C^k` by Leibniz, on `W × (2,∞)` it
vanishes identically because `χ` does, and across the hyperplane `t = 2` the *flatness* of `χ` at
`t = 2` (a smooth function vanishing on `[2,∞)` is flat at `2`) beats the bounded (not necessarily
continuous) derivatives of `h`: every iterated derivative of the product on the lower slab decays
like `|t-2|`, so all the within-derivatives have limit `0` at the hyperplane and the local gluing
lemma `glueOpen_local` applies.

Everything is proved first for a smooth (i.e. `ContDiff ℝ ∞`) cutoff `χ`, and the statement of the
task (whose hypothesis `ContDiff ℝ ⊤ χ` is the *analytic* level `ω = ⊤`) is deduced from it.
-/

noncomputable section

namespace Work.NN.DiscRadial

open scoped Topology ContDiff NNReal ENNReal
open Metric Set Filter

/-! ## Auxiliary estimates -/

/-- A smooth function on `ℝ` vanishing on `[2,∞)` is flat at `2`. -/
lemma iteratedFDeriv_chi_eq_zero_of_vanishes_above {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ u ≥ 2, χ u = 0) (j : ℕ) : iteratedFDeriv ℝ j χ 2 = 0 := by
  have hU : IsOpen (Set.Ioi (2 : ℝ)) := isOpen_Ioi
  have hcont : Continuous (iteratedFDeriv ℝ j χ) :=
    (hχ.ftaylorSeries).cont j (WithTop.coe_le_coe.mpr le_top)
  have hvan : Set.EqOn (iteratedFDeriv ℝ j χ) (fun _ : ℝ => 0) (Set.Ioi 2) := by
    intro y hy
    have h1 : iteratedFDerivWithin ℝ j χ (Set.Ioi 2) y =
        iteratedFDerivWithin ℝ j (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 2) y := by
      rw [iteratedFDerivWithin_congr (f₁ := fun _ : ℝ => (0 : ℝ)) (s := Set.Ioi 2) (x := y)
        (fun z hz => (hχ0 z (le_of_lt hz)).symm) hy j]
    rw [← iteratedFDerivWithin_of_isOpen (s := Set.Ioi (2 : ℝ)) j hU hy, h1,
      iteratedFDerivWithin_of_isOpen (s := Set.Ioi (2 : ℝ)) j hU hy, iteratedFDeriv_fun_zero]
    rfl
  have h2 := Set.EqOn.closure hvan hcont continuous_const
  exact h2 (by rw [closure_Ioi]; exact Set.mem_Ici.mpr le_rfl)

/-- Decay of the derivatives of the one-variable cutoff, transported to `E × ℝ`:
`‖D^j (q ↦ χ (q.2 + 2))‖ ≤ C |q.2|^N` near `q.2 = 0`. -/
lemma chi_comp_snd_decay_of_flat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hflat : ∀ j : ℕ, iteratedFDeriv ℝ j χ 2 = 0) (j N : ℕ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ p : E × ℝ, |p.2| < δ →
      ‖iteratedFDeriv ℝ j (fun q : E × ℝ => ((χ (q.2 + 2) : ℝ) : ℂ)) p‖ ≤ C * |p.2| ^ N := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := Work.NN.Core.flat_iteratedFDeriv_bound hχ 2 hflat j N
  refine ⟨C, δ, hC, hδ, fun p hp => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ j (fun q : E × ℝ => ((χ (q.2 + 2) : ℝ) : ℂ)) p‖
      = ‖iteratedFDeriv ℝ j (fun q : E × ℝ => χ (q.2 + 2)) p‖ := by
    have hf : ContDiffAt ℝ ∞ (fun q : E × ℝ => χ (q.2 + 2)) p :=
      (hχ.comp (contDiff_snd.add contDiff_const)).contDiffAt
    exact LinearIsometry.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) Complex.ofRealLI hf (i := j)
      (WithTop.coe_le_coe.mpr le_top)
  have h2 : ‖iteratedFDeriv ℝ j (fun q : E × ℝ => χ (q.2 + 2)) p‖
      ≤ ‖iteratedFDeriv ℝ j (fun s : ℝ => χ (s + 2)) p.2‖ := by
    have hf2 : ContDiff ℝ ∞ (fun s : ℝ => χ (s + 2)) := hχ.comp (contDiff_id.add contDiff_const)
    have hkey := ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ)
      (g := ContinuousLinearMap.snd ℝ E ℝ) (f := fun s : ℝ => χ (s + 2)) hf2 p (i := j)
      (WithTop.coe_le_coe.mpr le_top)
    have hL : (fun q : E × ℝ => χ (q.2 + 2))
        = ((fun s : ℝ => χ (s + 2)) ∘ (ContinuousLinearMap.snd ℝ E ℝ)) := rfl
    rw [hL, hkey]
    calc ‖(iteratedFDeriv ℝ j (fun s : ℝ => χ (s + 2)) p.2).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.snd ℝ E ℝ)‖
        ≤ ‖iteratedFDeriv ℝ j (fun s : ℝ => χ (s + 2)) p.2‖ *
            ∏ _i : Fin j, ‖ContinuousLinearMap.snd ℝ E ℝ‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ j (fun s : ℝ => χ (s + 2)) p.2‖ * 1 := by
          gcongr
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E ℝ)
      _ = ‖iteratedFDeriv ℝ j (fun s : ℝ => χ (s + 2)) p.2‖ := mul_one _
  have h3 : ‖iteratedFDeriv ℝ j (fun s : ℝ => χ (s + 2)) p.2‖
      = ‖iteratedFDeriv ℝ j χ (p.2 + 2)‖ := by
    rw [iteratedFDeriv_comp_add_right j 2 p.2]
  calc ‖iteratedFDeriv ℝ j (fun q : E × ℝ => ((χ (q.2 + 2) : ℝ) : ℂ)) p‖
      = ‖iteratedFDeriv ℝ j (fun q : E × ℝ => χ (q.2 + 2)) p‖ := h1
    _ ≤ ‖iteratedFDeriv ℝ j (fun s : ℝ => χ (s + 2)) p.2‖ := h2
    _ = ‖iteratedFDeriv ℝ j χ (p.2 + 2)‖ := h3
    _ ≤ C * |p.2| ^ N := by
        have hp' : |p.2 + 2 - 2| < δ := by
          rw [show p.2 + 2 - 2 = p.2 from by ring]; exact hp
        have hb' := hb (p.2 + 2) hp'
        rwa [Real.norm_eq_abs, show p.2 + 2 - 2 = p.2 from by ring] at hb'


/-! ## The main estimate and the gluing argument -/

/-- **Smooth version.**  Same as `flatMul_contDiffOn` but with a smooth (`C^∞`) cutoff. -/
theorem flatMul_contDiffOn_of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} (hW : IsOpen W) {β : ℝ} (_hβ0 : 0 < β) (_hβ1 : β ≤ 1)
    {k : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ u ≥ 2, χ u = 0)
    {h : E × ℝ → ℂ} (hh : ContDiffOn ℝ (k : WithTop ENat) h (W ×ˢ Set.Ioo 0 2))
    (hfin : Work.CR.Flat.holderNorm k β h (W ×ˢ Set.Ioo 0 2) ≠ ⊤) :
    ContDiffOn ℝ (k : WithTop ENat)
      (fun z : E × ℝ => (χ z.2 : ℂ) * h z) (W ×ˢ Set.Ioi 0) := by
  classical
  have hk_le_inf : (k : WithTop ENat) ≤ (∞ : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤)
  set Ω : Set (E × ℝ) := W ×ˢ Set.Ioo (0 : ℝ) 2 with hΩ
  set Ωt : Set (E × ℝ) := W ×ˢ Set.Ioo (-2 : ℝ) 0 with hΩt
  set V : Set (E × ℝ) := W ×ˢ Set.Ioi (-2 : ℝ) with hV
  have hΩopen : IsOpen Ω := hW.prod isOpen_Ioo
  have hΩtopen : IsOpen Ωt := hW.prod isOpen_Ioo
  have hVopen : IsOpen V := hW.prod isOpen_Ioi
  set Phi : E × ℝ → ℂ := fun q => ((χ (q.2 + 2) : ℝ) : ℂ) with hPhi
  set Psi : E × ℝ → ℂ := fun q => h (q.1, q.2 + 2) with hPsi
  set F : E × ℝ → ℂ := fun q => Phi q * Psi q with hF
  -- a uniform bound for the within-derivatives of `h` on `Ω`
  obtain ⟨Ch, hCh0, hChb⟩ := Work.NN.DiscRadial.iterDerivBound hfin
  -- flatness of `χ` at `2`, and the resulting decay of its derivatives
  have hflat : ∀ j : ℕ, iteratedFDeriv ℝ j χ 2 = 0 :=
    iteratedFDeriv_chi_eq_zero_of_vanishes_above hχ hχ0
  have hdecay : ∀ j : ℕ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ p : E × ℝ, |p.2| < δ → ‖iteratedFDeriv ℝ j Phi p‖ ≤ C * |p.2| := by
    intro j
    obtain ⟨C, δ, hC, hδ, hb⟩ := chi_comp_snd_decay_of_flat (E := E) hχ hflat j 1
    exact ⟨C, δ, hC, hδ, fun p hp => by
      have h := hb p hp
      rwa [pow_one] at h⟩
  -- smoothness of the two factors on the lower slab
  have hPhi_smooth : ContDiff ℝ ∞ Phi := by
    show ContDiff ℝ ∞ (fun q : E × ℝ => ((χ (q.2 + 2) : ℝ) : ℂ))
    exact Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_snd.add contDiff_const))
  have hPsi_smooth : ContDiff ℝ ∞ (fun q : E × ℝ => (q.1, q.2 + 2)) :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  have hPhiOn : ContDiffOn ℝ (k : WithTop ENat) Phi Ωt :=
    (hPhi_smooth.contDiffOn (s := Ωt)).of_le hk_le_inf
  have hPsiOn : ContDiffOn ℝ (k : WithTop ENat) Psi Ωt := by
    have hmap : MapsTo (fun q : E × ℝ => (q.1, q.2 + 2)) Ωt Ω := by
      intro q hq
      exact ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
    have hcomp := hh.comp ((hPsi_smooth.contDiffOn (s := Ωt)).of_le hk_le_inf) hmap
    simpa only [hPsi, Function.comp_def] using hcomp
  -- the master estimate: the derivatives of `F` decay like `|p.2|` near the hyperplane
  have hmaster : ∀ i : ℕ, i ≤ k → ∃ C' δ : ℝ, 0 ≤ C' ∧ 0 < δ ∧
      ∀ p : E × ℝ, p ∈ Ωt → |p.2| < δ → ‖iteratedFDeriv ℝ i F p‖ ≤ C' * |p.2| := by
    intro i hi
    choose Cd δd hCdn hδdp hbd using hdecay
    set δ : ℝ := (Finset.range (i + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos i)⟩ δd
      with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact (Finset.lt_inf'_iff _).mpr fun j _ => hδdp j
    have hδle : ∀ j ∈ Finset.range (i + 1), δ ≤ δd j := fun j hj => by
      rw [hδdef]
      exact Finset.inf'_le δd hj
    refine ⟨(∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * Cd j) * Ch, δ,
      mul_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hCdn j)) hCh0,
      hδpos, ?_⟩
    intro p hpΩt hpδ
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (s := Ωt) (A := ℂ)
      (f := Phi) (g := Psi) (N := (k : WithTop ENat)) hPhiOn hPsiOn hΩtopen.uniqueDiffOn hpΩt
      (by exact_mod_cast hi : ((i : ℕ) : WithTop ENat) ≤ ((k : ℕ) : WithTop ENat))
    have h1 : iteratedFDerivWithin ℝ i (fun y : E × ℝ => Phi y * Psi y) Ωt p
        = iteratedFDeriv ℝ i F p := by
      rw [iteratedFDerivWithin_of_isOpen (s := Ωt) i hΩtopen hpΩt]
    rw [h1] at hleib
    have hterm : ∀ j, j ∈ Finset.range (i + 1) → (i.choose j : ℝ) *
          ‖iteratedFDerivWithin ℝ j Phi Ωt p‖ * ‖iteratedFDerivWithin ℝ (i - j) Psi Ωt p‖
        ≤ (i.choose j : ℝ) * (Cd j * |p.2|) * Ch := by
      intro j hj
      have hbΦ : ‖iteratedFDerivWithin ℝ j Phi Ωt p‖ ≤ Cd j * |p.2| := by
        rw [iteratedFDerivWithin_of_isOpen (s := Ωt) j hΩtopen hpΩt]
        exact hbd j p (lt_of_lt_of_le hpδ (hδle j hj))
      have hbΨ : ‖iteratedFDerivWithin ℝ (i - j) Psi Ωt p‖ ≤ Ch := by
        rw [iteratedFDerivWithin_of_isOpen (s := Ωt) (i - j) hΩtopen hpΩt]
        have hPsi_eq : Psi = fun z : E × ℝ => h (z + ((0 : E), (2 : ℝ))) := by
          funext z
          change h (z.1, z.2 + 2) = h (z + ((0 : E), (2 : ℝ)))
          congr 1
          ext <;> simp
        rw [hPsi_eq, iteratedFDeriv_comp_add_right (i - j) ((0 : E), (2 : ℝ)) p]
        have hmem : p + ((0 : E), (2 : ℝ)) ∈ Ω := by
          rw [hΩ, mem_prod]
          refine ⟨?_, ?_, ?_⟩
          · simpa using hpΩt.1
          · simp only [Prod.snd_add]
            linarith [hpΩt.2.1]
          · simp only [Prod.snd_add]
            linarith [hpΩt.2.2]
        have h2 := hChb (i - j) (le_trans (Nat.sub_le i j) hi) (p + ((0 : E), (2 : ℝ))) hmem
        rwa [iteratedFDerivWithin_of_isOpen (s := Ω) (i - j) hΩopen hmem] at h2
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbΦ (Nat.cast_nonneg _)) hbΨ
        (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCdn j) (abs_nonneg _)))
    have hsum : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDerivWithin ℝ j Phi Ωt p‖ * ‖iteratedFDerivWithin ℝ (i - j) Psi Ωt p‖)
        ≤ ((∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * Cd j) * Ch) * |p.2| := by
      refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    exact le_trans hleib hsum
  -- `F` is continuous on the translated half space
  have hFzero : ∀ q : E × ℝ, 0 ≤ q.2 → F q = 0 := by
    intro q hq
    have h0 : χ (q.2 + 2) = 0 := hχ0 (q.2 + 2) (by linarith)
    change ((χ (q.2 + 2) : ℝ) : ℂ) * h (q.1, q.2 + 2) = 0
    rw [h0]
    simp
  have hc : ContinuousOn F V := by
    intro p hpV
    rcases lt_trichotomy p.2 0 with hneg | hzero | hpos
    · -- below the hyperplane: an honest product of continuous functions
      have hPsiCont : ContinuousAt Psi p := by
        have hmem : (p.1, p.2 + 2) ∈ Ω := by
          have hpV2 : (-2 : ℝ) < p.2 := hpV.2
          exact ⟨hpV.1, by linarith, by linarith⟩
        have hcont : ContinuousAt h (p.1, p.2 + 2) :=
          hh.continuousOn.continuousAt (hΩopen.mem_nhds hmem)
        have h := hcont.comp (f := fun q : E × ℝ => (q.1, q.2 + 2)) (by fun_prop)
        simpa only [hPsi, Function.comp_def] using h
      have hPhiCont : ContinuousAt Phi p := by
        have hcont : Continuous Phi :=
          Complex.continuous_ofReal.comp
            (hχ.continuous.comp (continuous_snd.add continuous_const))
        exact hcont.continuousAt
      exact (hPhiCont.mul hPsiCont).continuousWithinAt
    · -- on the hyperplane: everything is squeezed by `|q.2|`
      have hFp : F p = 0 := hFzero p (le_of_eq hzero.symm)
      rw [ContinuousWithinAt, hFp, tendsto_zero_iff_norm_tendsto_zero]
      obtain ⟨C₀, δ₀, hC₀, hδ₀, hb₀⟩ := hmaster 0 (Nat.zero_le k)
      have hbnd : ∀ᶠ q in 𝓝[V] p, ‖F q‖ ≤ C₀ * dist q p := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hδ₀))]
          with q hqV hqball
        rcases le_or_gt 0 q.2 with hq2 | hq2
        · rw [hFzero q hq2, norm_zero]
          exact mul_nonneg hC₀ dist_nonneg
        · have hqΩt : q ∈ Ωt := ⟨hqV.1, hqV.2, hq2⟩
          have hdist : |q.2| ≤ dist q p := by
            rw [show |q.2| = |q.2 - p.2| by rw [hzero, sub_zero], dist_eq_norm]
            exact le_trans (ContinuousLinearMap.le_opNorm (ContinuousLinearMap.snd ℝ E ℝ) (q - p))
              (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E ℝ))
          have h0 : ‖F q‖ ≤ C₀ * |q.2| := by
            have h := hb₀ q hqΩt (lt_of_le_of_lt hdist hqball)
            rwa [norm_iteratedFDeriv_zero] at h
          calc ‖F q‖ ≤ C₀ * |q.2| := h0
            _ ≤ C₀ * dist q p := mul_le_mul_of_nonneg_left hdist hC₀
      have htend : Tendsto (fun q : E × ℝ => C₀ * dist q p) (𝓝[V] p) (𝓝 0) := by
        have h1 : Tendsto (fun q : E × ℝ => dist q p) (𝓝[V] p) (𝓝 0) := by
          rw [← tendsto_iff_dist_tendsto_zero]
          exact (continuous_id.continuousAt (x := p)).tendsto.mono_left nhdsWithin_le_nhds
        simpa using h1.const_mul C₀
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
        (Filter.Eventually.of_forall fun q => norm_nonneg _) hbnd
    · -- above the hyperplane: `F` vanishes in a whole neighbourhood
      have hev : F =ᶠ[𝓝 p] (fun _ : E × ℝ => (0 : ℂ)) := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hpos] with q hq
        exact hFzero q (le_of_lt hq)
      exact ((continuous_const.continuousAt).congr_of_eventuallyEq hev).continuousWithinAt
  -- the two halves
  have hset : V ∩ {p : E × ℝ | p.2 < 0} = Ωt := by
    rw [hV, hΩt]
    ext q
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_ofPred_eq]
    tauto
  have hN : ContDiffOn ℝ k F (V ∩ {p : E × ℝ | p.2 < 0}) := by
    rw [hset]
    exact hPhiOn.mul hPsiOn
  have hH : ContDiffOn ℝ k F (V ∩ {p : E × ℝ | 0 < p.2}) := by
    refine (contDiffOn_const (c := (0 : ℂ))).congr fun q hq => ?_
    exact hFzero q (le_of_lt hq.2)
  -- the derivatives of `F` have limit `0` at every point of the hyperplane
  have hlim : ∀ i ≤ k, ∀ p ∈ V, p.2 = 0 →
      ∃ L : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ,
        Filter.Tendsto (fun q : E × ℝ => iteratedFDeriv ℝ i F q)
          (𝓝[V ∩ {q : E × ℝ | q.2 ≠ 0}] p) (𝓝 L) := by
    intro i hi p hpV hp2
    refine ⟨0, ?_⟩
    rw [tendsto_zero_iff_norm_tendsto_zero]
    obtain ⟨C, δ, hC0, hδ, hb⟩ := hmaster i hi
    have hbnd : ∀ᶠ q in 𝓝[V ∩ {q : E × ℝ | q.2 ≠ 0}] p,
        ‖iteratedFDeriv ℝ i F q‖ ≤ C * dist q p := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hδ))]
        with q hqmem hqball
      have hdist : |q.2| ≤ dist q p := by
        rw [show |q.2| = |q.2 - p.2| by rw [hp2, sub_zero], dist_eq_norm]
        exact le_trans (ContinuousLinearMap.le_opNorm (ContinuousLinearMap.snd ℝ E ℝ) (q - p))
          (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E ℝ))
      rcases lt_or_gt_of_ne hqmem.2 with hqn | hqp
      · have hqΩt : q ∈ Ωt := ⟨hqmem.1.1, hqmem.1.2, hqn⟩
        have h0 := hb q hqΩt (lt_of_le_of_lt hdist hqball)
        exact le_trans h0 (mul_le_mul_of_nonneg_left hdist hC0)
      · have hev : F =ᶠ[𝓝 q] (fun _ : E × ℝ => (0 : ℂ)) := by
          filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hqp] with r hr
          exact hFzero r (le_of_lt hr)
        have h0 : iteratedFDeriv ℝ i F q = 0 := by
          have h3 : iteratedFDeriv ℝ i F q
              = iteratedFDeriv ℝ i (fun _ : E × ℝ => (0 : ℂ)) q :=
            (Filter.EventuallyEq.iteratedFDeriv ℝ hev i).eq_of_nhds
          rw [h3, iteratedFDeriv_fun_zero]
          simp
        rw [h0, norm_zero]
        exact mul_nonneg hC0 dist_nonneg
    have htend : Tendsto (fun q : E × ℝ => C * dist q p)
        (𝓝[V ∩ {q : E × ℝ | q.2 ≠ 0}] p) (𝓝 0) := by
      have h1 : Tendsto (fun q : E × ℝ => dist q p)
          (𝓝[V ∩ {q : E × ℝ | q.2 ≠ 0}] p) (𝓝 0) := by
        rw [← tendsto_iff_dist_tendsto_zero]
        exact (continuous_id.continuousAt (x := p)).tendsto.mono_left nhdsWithin_le_nhds
      simpa using h1.const_mul C
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
      (Filter.Eventually.of_forall fun q => norm_nonneg _) hbnd
  -- glue, then undo the translation
  have hglue : ContDiffOn ℝ k F V :=
    glueOpen_local (X := E) (Y := ℂ) (m := k) (F := F) (V := V) hVopen hc hN hH hlim
  have hshift : ContDiffOn ℝ (k : WithTop ENat) (fun q : E × ℝ => (q.1, q.2 - 2))
      (W ×ˢ Set.Ioi 0) := by
    have h : ContDiff ℝ ∞ (fun q : E × ℝ => (q.1, q.2 - 2)) :=
      contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
    exact (h.contDiffOn (s := W ×ˢ Set.Ioi 0)).of_le hk_le_inf
  have hmap : MapsTo (fun q : E × ℝ => (q.1, q.2 - 2)) (W ×ˢ Set.Ioi 0) V := by
    intro q hq
    have hq2 : (0 : ℝ) < q.2 := hq.2
    exact ⟨hq.1, by show (-2 : ℝ) < q.2 - 2; linarith⟩
  have hcomp := hglue.comp hshift hmap
  refine hcomp.congr fun q _ => ?_
  simp only [Function.comp_apply]
  have h1 : F (q.1, q.2 - 2) = ((χ q.2 : ℝ) : ℂ) * h q := by
    change ((χ ((q.1, q.2 - 2).2 + 2) : ℝ) : ℂ) * h ((q.1, q.2 - 2).1, (q.1, q.2 - 2).2 + 2)
      = (χ q.2 : ℂ) * h q
    rw [show q.2 - 2 + 2 = q.2 from by ring]
  rw [h1]

/-- The statement of the task: `ContDiff ℝ ⊤ χ` is the analytic level `ω = ⊤`, and analyticity
implies smoothness, to which the previous theorem applies. -/
theorem flatMul_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} (hW : IsOpen W) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ⊤ χ) (hχ0 : ∀ u ≥ 2, χ u = 0)
    {h : E × ℝ → ℂ} (hh : ContDiffOn ℝ (k : WithTop ENat) h (W ×ˢ Set.Ioo 0 2))
    (hfin : Work.CR.Flat.holderNorm k β h (W ×ˢ Set.Ioo 0 2) ≠ ⊤) :
    ContDiffOn ℝ (k : WithTop ENat)
      (fun z : E × ℝ => (χ z.2 : ℂ) * h z) (W ×ˢ Set.Ioi 0) :=
  flatMul_contDiffOn_of_smooth hW hβ0 hβ1 (hχ.of_le le_top) hχ0 hh hfin

end Work.NN.DiscRadial
