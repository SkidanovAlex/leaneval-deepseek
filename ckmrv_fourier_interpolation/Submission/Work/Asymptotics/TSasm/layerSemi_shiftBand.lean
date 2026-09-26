import Mathlib
import Submission.Work.Asymptotics.TSasm.paperLayer_vadd_shift
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion
import Submission.Work.Asymptotics.TSasm.layerSemi_lowHalfFunnelNegRe

namespace Work.Asymptotics

open UpperHalfPlane

/-- **The `r`-seminorm band of the layer at the `T`-translate `1 +ᵥ u`.**

For `u` in the cusp-`0` half tile `Tregion` with `Re u ≥ 1/4` and every `k`, `l`, the weighted
`(k,l)`-seminorm of the layer `layer (Gcusp ℓ 24) ℓ 24 (1 +ᵥ u) ·` is bounded, uniformly in `u`.

The layer at `1 +ᵥ u` is the puncture at `0` of
`2 · paperLayer (Gcusp ℓ 24) ℓ 24 u · - paperLayer (Gcusp ℓ 24) ℓ 24 (-1 +ᵥ u) ·`
(`paperLayer_vadd_shift`); puncturing at `0` does not change the positive-order iterated
derivatives (`punctured_iteratedDeriv`, using the evenness and smoothness of `paperLayer` at `u`
and `-1 +ᵥ u`), while the zeroth-order term at `r = 0` vanishes because `layer · 0 = 0` by
definition.  The two layers on the right live on regions carrying the uniform bounds
`layerSemi_Tregion` and `layerSemi_lowHalfFunnelNegRe`: for `Im u < 1/2` the translate
`-1 +ᵥ u` is again in `Tregion` (`ts_vadd_neg_one_mem_Tregion`), while for `Im u ≥ 1/2` it lies in
`𝒟` with `Re < 0` and `1/2 ≤ Im ≤ 2` (`ts_vadd_neg_one_mem_DomainD_of_pos`, `ts_Tregion_ineqs`). -/
theorem layerSemi_shiftBand (ℓ : Work.Kernels.LogLambdaData) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : UpperHalfPlane) (r : ℝ), u ∈ Work.Asymptotics.Tregion → (1 : ℝ) / 4 ≤ u.re →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) s) r‖ ≤ C := by
  intro k l
  obtain ⟨Ct, hCt, hbt⟩ := Work.Asymptotics.layerSemi_Tregion ℓ 24 (Or.inr rfl) k l
  obtain ⟨Cf, hCf, hbf⟩ := Work.Asymptotics.layerSemi_lowHalfFunnelNegRe ℓ 24 (Or.inr rfl) k l
  refine ⟨3 * Ct + 3 * Cf + 1, by linarith, ?_⟩
  intro u r hu hx
  have hxu : 0 < u.re := by linarith
  have huD : u ∈ Work.Asymptotics.DomainD := hu.1
  have hult : u.re < 1 := hu.1.2.1
  have hvD : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.ts_vadd_neg_one_mem_DomainD_of_pos huD hxu
  -- a uniform bound at the translate `-1 +ᵥ u`, from one of the two region bounds
  have hvbound : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
      Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) r‖
      ≤ Ct + Cf := by
    by_cases hy : u.im < 1 / 2
    · have hvT : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.Tregion :=
        Work.Asymptotics.ts_vadd_neg_one_mem_Tregion u hu hx hy
      exact le_trans (hbt ((-1 : ℝ) +ᵥ u) r hvT) (by linarith)
    · rw [not_lt] at hy
      have hvre : ((-1 : ℝ) +ᵥ u).re < 0 := by
        rw [UpperHalfPlane.vadd_re]; linarith
      have hvim1 : (1 : ℝ) / 2 ≤ ((-1 : ℝ) +ᵥ u).im := by
        rw [UpperHalfPlane.vadd_im]; exact hy
      have hvim2 : ((-1 : ℝ) +ᵥ u).im ≤ 2 := by
        rw [UpperHalfPlane.vadd_im]
        have hineq := (Work.Asymptotics.ts_Tregion_ineqs hu).2
        have hsq : ‖(u : ℂ)‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := Work.Asymptotics.ts_normSq_coe u
        nlinarith [hineq, hsq, sq_nonneg u.re, u.im_pos]
      exact le_trans (hbf ((-1 : ℝ) +ᵥ u) r hvD hvim1 hvim2 hvre) (by linarith)
  have hnorm_aux : ∀ a b : ℂ, ‖2 * a - b‖ ≤ 2 * ‖a‖ + ‖b‖ := by
    intro a b
    calc ‖2 * a - b‖ ≤ ‖2 * a‖ + ‖b‖ := norm_sub_le _ _
      _ = 2 * ‖a‖ + ‖b‖ := by rw [norm_mul]; norm_num
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · -- `l = 0`: at `r = 0` the layer vanishes; at `r ≠ 0` use the ladder pointwise
    subst hl0
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      have hz : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) 0 = 0 := by
        rw [Work.Asymptotics.layer]; simp
      rw [iteratedDeriv_zero, hz, norm_zero, mul_zero]
      positivity
    · have hL : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) r
          = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) r := by
        rw [Work.Asymptotics.layer, if_neg hr]
      have huP : Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r
          = Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r := by
        rw [Work.Asymptotics.layer, if_neg hr]
      have hvP : Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) r
          = Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) r := by
        rw [Work.Asymptotics.layer, if_neg hr]
      have h1 : (|r| ^ k) * ‖Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r‖
          ≤ Ct := by
        simpa only [iteratedDeriv_zero] using hbt u r hu
      have h2 : (|r| ^ k) * ‖Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24
            ((-1 : ℝ) +ᵥ u) r‖ ≤ Ct + Cf := by
        simpa only [iteratedDeriv_zero] using hvbound
      rw [iteratedDeriv_zero, hL, Work.Asymptotics.paperLayer_vadd_shift ℓ u hu hx r, huP, hvP]
      calc (|r| ^ k) * ‖2 * Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r
              - Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) r‖
          ≤ (|r| ^ k) * (2 * ‖Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r‖
              + ‖Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) r‖) :=
            mul_le_mul_of_nonneg_left (hnorm_aux _ _) (by positivity)
        _ = 2 * ((|r| ^ k) * ‖Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r‖)
              + (|r| ^ k) * ‖Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24
                  ((-1 : ℝ) +ᵥ u) r‖ := by ring
        _ ≤ 2 * Ct + (Ct + Cf) := by linarith
        _ ≤ 3 * Ct + 3 * Cf + 1 := by linarith
  · -- `l ≥ 1`: puncture the ladder at `0`
    have hl1 : 1 ≤ l := hlpos
    set K : Set UpperHalfPlane := {u} ∪ {((-1 : ℝ) +ᵥ u)} with hKdef
    have hKc : IsCompact K := isCompact_singleton.union isCompact_singleton
    have hmemu : u ∈ K := by rw [hKdef]; exact Set.mem_union_left _ rfl
    have hmemv : ((-1 : ℝ) +ᵥ u) ∈ K := by rw [hKdef]; exact Set.mem_union_right _ rfl
    have hsubK : K ⊆ Work.Asymptotics.DomainD := by
      rw [hKdef]
      rintro x (hx' | hx')
      · rw [Set.mem_singleton_iff] at hx'; rw [hx']; exact huD
      · rw [Set.mem_singleton_iff] at hx'; rw [hx']; exact hvD
    have hflatK := Work.Asymptotics.MFix.Kaxis_local_flat ℓ 24 (Or.inr rfl) hKc hsubK
    have hpolyK := Work.HFN.cusp_expansion_of_kernel ℓ 24 (Or.inr rfl) hKc hsubK
    have hPLu : ContDiff ℝ ⊤ (fun s : ℝ =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) :=
      Work.HFN.paperLayer_contDiff_of_mem ℓ 24 (Or.inr rfl) (Work.Asymptotics.Gcusp ℓ 24)
        hflatK hpolyK u hmemu
    have hPLv : ContDiff ℝ ⊤ (fun s : ℝ =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) :=
      Work.HFN.paperLayer_contDiff_of_mem ℓ 24 (Or.inr rfl) (Work.Asymptotics.Gcusp ℓ 24)
        hflatK hpolyK ((-1 : ℝ) +ᵥ u) hmemv
    set F : ℝ → ℂ := fun s => 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s
        - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s with hFdef
    have hFeven : ∀ s : ℝ, F (-s) = F s := by
      intro s
      rw [hFdef]
      simp only [Work.HFN.paperLayer_neg]
    have hFdiff : Differentiable ℝ F := by
      rw [hFdef]
      exact ((contDiff_const.mul hPLu).sub hPLv).differentiable (by simp)
    have hlayer_eq : (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) s)
        = fun s : ℝ => if s = 0 then 0 else F s := by
      funext s
      by_cases hs : s = 0
      · subst hs; simp [Work.Asymptotics.layer]
      · simp only [Work.Asymptotics.layer, if_neg hs, hFdef]
        exact Work.Asymptotics.paperLayer_vadd_shift ℓ u hu hx s
    have hpunct := Work.Asymptotics.punctured_iteratedDeriv hFeven hFdiff l hl1
    have hu_punct : iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s)
        = iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) := by
      have h := Work.Asymptotics.punctured_iteratedDeriv
        (f := fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s)
        (fun s => Work.HFN.paperLayer_neg (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s)
        (hPLu.differentiable (by simp)) l hl1
      have hfun : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s)
          = fun r : ℝ => if r = 0 then 0 else
              Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r := by
        funext s; rw [Work.Asymptotics.layer]
      rw [hfun, h]
    have hv_punct : iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s)
        = iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) := by
      have h := Work.Asymptotics.punctured_iteratedDeriv
        (f := fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s)
        (fun s => Work.HFN.paperLayer_neg (Work.Asymptotics.Gcusp ℓ 24) ℓ 24
          ((-1 : ℝ) +ᵥ u) s)
        (hPLv.differentiable (by simp)) l hl1
      have hfun : (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s)
          = fun r : ℝ => if r = 0 then 0 else
              Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) r := by
        funext s; rw [Work.Asymptotics.layer]
      rw [hfun, h]
    have hF_split : iteratedDeriv l F r
        = 2 * iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) r
          - iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24
                ((-1 : ℝ) +ᵥ u) s) r := by
      have hFeq : F = (fun s : ℝ =>
              (2 : ℂ) * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s)
          - (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24
              ((-1 : ℝ) +ᵥ u) s) := by
        rw [hFdef]
        funext s
        rfl
      rw [hFeq, iteratedDeriv_sub
            (((contDiff_const.mul hPLu).contDiffAt).of_le le_top)
            ((hPLv.contDiffAt).of_le le_top), iteratedDeriv_const_mul_field]
    have key : iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) s) r
        = 2 * iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) r
          - iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) r := by
      rw [hlayer_eq, hpunct, hF_split, hu_punct, hv_punct]
    rw [key]
    have h1 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) r‖ ≤ Ct := hbt u r hu
    have h2 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) r‖
        ≤ Ct + Cf := hvbound
    calc (|r| ^ k) * ‖2 * iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) r
            - iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) r‖
        ≤ (|r| ^ k) * (2 * ‖iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) r‖
            + ‖iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) r‖) :=
          mul_le_mul_of_nonneg_left (hnorm_aux _ _) (by positivity)
      _ = 2 * ((|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u s) r‖)
            + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) s) r‖ := by
          ring
      _ ≤ 2 * Ct + (Ct + Cf) := by linarith
      _ ≤ 3 * Ct + 3 * Cf + 1 := by linarith

end Work.Asymptotics
