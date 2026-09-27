import Mathlib

namespace Work.Drive

open Set Filter Topology
open scoped ContDiff

/-- Truncated Taylor series of `g`: the `n`-th jet where `z.2 > 0`, and `0` where `z.2 ≤ 0`. -/
private noncomputable def jet {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : X × ℝ → E) (z : X × ℝ) :
    FormalMultilinearSeries ℝ (X × ℝ) E :=
  fun n => if 0 < z.2 then iteratedFDeriv ℝ n g z else 0

private lemma jet_of_pos {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : X × ℝ → E} {z : X × ℝ}
    (hz : 0 < z.2) (n : ℕ) : jet g z n = iteratedFDeriv ℝ n g z := if_pos hz

private lemma jet_of_nonpos {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : X × ℝ → E} {z : X × ℝ}
    (hz : ¬ 0 < z.2) (n : ℕ) : jet g z n = 0 := if_neg hz

private lemma curryLeft_zero {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    ((0 : (X × ℝ) [×k.succ]→L[ℝ] E).curryLeft : (X × ℝ) →L[ℝ] (X × ℝ) [×k]→L[ℝ] E) = 0 := by
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin k.succ => (X × ℝ)) E)
      (0 : (X × ℝ) [×k.succ]→L[ℝ] E) = 0
  exact LinearIsometryEquiv.map_zero _

theorem contDiffAt_trunc_sqrt_assembly {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : X × ℝ → E} {m K : ℕ} {x₀ : X} {δ : ℝ}
    {C : ℕ → ℝ}
    (hKm : 2 * m + 2 ≤ K) (hC : ∀ k, 0 ≤ C k)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h0 : ∀ z : X × ℝ, z.2 ≤ 0 → g z = 0)
    (hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Set.univ ×ˢ Set.Ioi (0 : ℝ)))
    (hbound : ∀ z : X × ℝ, ‖z.1 - x₀‖ < δ → 0 < z.2 → z.2 < δ →
      ∀ k : ℕ, k ≤ m → ‖iteratedFDeriv ℝ k g z‖ ≤ C k * (Real.sqrt z.2) ^ (K - 2 * k)) :
    ContDiffAt ℝ m g (x₀, 0) := by
  have _hδ1 : δ ≤ 1 := hδ1
  set B : Set (X × ℝ) := {z | ‖z.1 - x₀‖ < δ ∧ |z.2| < δ} with hB
  have hBopen : IsOpen B := by
    rw [hB]
    exact (isOpen_lt ((continuous_fst.sub continuous_const).norm) continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)
  have hxB : (x₀, 0) ∈ B := by
    rw [hB]; simp [hδ]
  have hTF : HasFTaylorSeriesUpToOn ((m : ℕ∞) : WithTop ℕ∞) g (jet g) B := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      by_cases hz0 : 0 < z.2
      · rw [jet_of_pos hz0 0]; simp
      · rw [jet_of_nonpos hz0 0, h0 z (le_of_not_gt hz0)]; simp
    · intro k hk z hz
      have hkm : k < m := by exact_mod_cast hk
      by_cases hz0 : 0 < z.2
      · have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g z :=
          hsmooth.contDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨mem_univ _, hz0⟩)
        have hfd : HasFDerivAt (fun y : X × ℝ => iteratedFDeriv ℝ k g y)
            ((iteratedFDeriv ℝ k.succ g z).curryLeft) z := by
          have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) z :=
            hg.differentiableAt_iteratedFDeriv (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k))
          have hh := hdiff.hasFDerivAt
          rw [fderiv_iteratedFDeriv] at hh
          exact hh
        rw [jet_of_pos hz0 k.succ]
        have hmem : ∀ᶠ y in 𝓝[B] z, (0 : ℝ) < y.2 :=
          nhdsWithin_le_nhds (s := B) (a := z)
            ((isOpen_lt continuous_const continuous_snd).mem_nhds hz0)
        have heq : (fun y : X × ℝ => jet g y k) =ᶠ[𝓝[B] z]
            (fun y => iteratedFDeriv ℝ k g y) :=
          hmem.mono (fun y hy => jet_of_pos hy k)
        exact (hfd.hasFDerivWithinAt (s := B)).congr_of_eventuallyEq heq (jet_of_pos hz0 k)
      · rcases lt_or_eq_of_le (le_of_not_gt hz0) with hzlt | hzeq
        · have hmem : ∀ᶠ y in 𝓝[B] z, y.2 < 0 :=
            nhdsWithin_le_nhds (s := B) (a := z)
              ((isOpen_lt continuous_snd continuous_const).mem_nhds hzlt)
          have heq : (fun y : X × ℝ => jet g y k) =ᶠ[𝓝[B] z]
              (fun _ => (0 : (X × ℝ) [×k]→L[ℝ] E)) :=
            hmem.mono (fun y hy => jet_of_nonpos (not_lt.mpr hy.le) k)
          have hbase : HasFDerivWithinAt (fun _ : X × ℝ => (0 : (X × ℝ) [×k]→L[ℝ] E))
              (0 : (X × ℝ) →L[ℝ] ((X × ℝ) [×k]→L[ℝ] E)) B z :=
            hasFDerivWithinAt_const (𝕜 := ℝ) (0 : (X × ℝ) [×k]→L[ℝ] E) z B
          rw [jet_of_nonpos hz0 k.succ, curryLeft_zero k]
          exact hbase.congr_of_eventuallyEq heq (jet_of_nonpos hz0 k)
        · have he : 0 < K - 2 * k - 2 := by omega
          have hbound_pt : ∀ y ∈ B,
              ‖jet g y k‖ ≤ (C k * (Real.sqrt y.2) ^ (K - 2 * k - 2)) * ‖y - z‖ := by
            intro y hy
            rw [hB] at hy
            rcases hy with ⟨hy1, hy2⟩
            have hy2' : y.2 < δ := (abs_lt.mp hy2).2
            by_cases hy0 : 0 < y.2
            · rw [jet_of_pos hy0 k]
              have hb := hbound y hy1 hy0 hy2' k (le_of_lt hkm)
              have hpow : (Real.sqrt y.2) ^ (K - 2 * k)
                  = (Real.sqrt y.2) ^ (K - 2 * k - 2) * y.2 := by
                have h : K - 2 * k = (K - 2 * k - 2) + 2 := by omega
                conv_lhs => rw [h]
                rw [pow_add, Real.sq_sqrt hy0.le]
              have hnorm : y.2 ≤ ‖y - z‖ := by
                have h1 : y.2 ≤ ‖(y - z).2‖ := by
                  rw [Real.norm_eq_abs]
                  have h2 : (y - z).2 = y.2 - z.2 := rfl
                  rw [h2, hzeq, sub_zero, abs_of_pos hy0]
                rw [Prod.norm_def]
                exact le_trans h1 (le_max_right _ _)
              calc ‖iteratedFDeriv ℝ k g y‖ ≤ C k * (Real.sqrt y.2) ^ (K - 2 * k) := hb
                _ = (C k * (Real.sqrt y.2) ^ (K - 2 * k - 2)) * y.2 := by rw [hpow]; ring
                _ ≤ (C k * (Real.sqrt y.2) ^ (K - 2 * k - 2)) * ‖y - z‖ :=
                    mul_le_mul_of_nonneg_left hnorm
                      (mul_nonneg (hC k) (pow_nonneg (Real.sqrt_nonneg _) _))
            · rw [jet_of_nonpos hy0 k]
              have hy2le : y.2 ≤ 0 := le_of_not_gt hy0
              rw [Real.sqrt_eq_zero_of_nonpos hy2le, zero_pow (by omega : K - 2 * k - 2 ≠ 0)]
              simp
          rw [jet_of_nonpos hz0 k.succ, curryLeft_zero k, hasFDerivWithinAt_iff_isLittleO,
            jet_of_nonpos hz0 k]
          simp only [zero_apply, sub_zero]
          refine Asymptotics.IsLittleO.of_bound (fun c hc => ?_)
          have hφcont : Continuous
              (fun y : X × ℝ => C k * (Real.sqrt y.2) ^ (K - 2 * k - 2)) := by fun_prop
          have hφz : C k * (Real.sqrt z.2) ^ (K - 2 * k - 2) = 0 := by
            rw [hzeq, Real.sqrt_zero, zero_pow he.ne', mul_zero]
          have hlt : ∀ᶠ y in 𝓝[B] z, C k * (Real.sqrt y.2) ^ (K - 2 * k - 2) < c :=
            nhdsWithin_le_nhds (s := B) (a := z)
              (hφcont.continuousAt.tendsto (isOpen_Iio.mem_nhds (by rw [hφz]; exact hc)))
          refine (hlt.and self_mem_nhdsWithin).mono (fun y hy => ?_)
          obtain ⟨hylt, hyB⟩ := hy
          exact le_trans (hbound_pt y hyB) (mul_le_mul_of_nonneg_right hylt.le (norm_nonneg _))
    · intro k hk
      have hkm : k ≤ m := by exact_mod_cast hk
      intro z hz
      by_cases hz0 : 0 < z.2
      · have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g z :=
          hsmooth.contDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds ⟨mem_univ _, hz0⟩)
        have hcont := hg.continuousAt_iteratedFDeriv
          (WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤))
        have hmem : ∀ᶠ y in 𝓝[B] z, (0 : ℝ) < y.2 :=
          nhdsWithin_le_nhds (s := B) (a := z)
            ((isOpen_lt continuous_const continuous_snd).mem_nhds hz0)
        have heq : (fun y : X × ℝ => jet g y k) =ᶠ[𝓝[B] z]
            (fun y => iteratedFDeriv ℝ k g y) := hmem.mono (fun y hy => jet_of_pos hy k)
        exact (hcont.continuousWithinAt).congr_of_eventuallyEq heq (jet_of_pos hz0 k)
      · rcases lt_or_eq_of_le (le_of_not_gt hz0) with hzlt | hzeq
        · have hmem : ∀ᶠ y in 𝓝[B] z, y.2 < 0 :=
            nhdsWithin_le_nhds (s := B) (a := z)
              ((isOpen_lt continuous_snd continuous_const).mem_nhds hzlt)
          have heq : (fun y : X × ℝ => jet g y k) =ᶠ[𝓝[B] z]
              (fun _ => (0 : (X × ℝ) [×k]→L[ℝ] E)) :=
            hmem.mono (fun y hy => jet_of_nonpos (not_lt.mpr hy.le) k)
          exact (continuousWithinAt_const (s := B) (x := z)
            (b := (0 : (X × ℝ) [×k]→L[ℝ] E))).congr_of_eventuallyEq heq (jet_of_nonpos hz0 k)
        · have he : 0 < K - 2 * k := by omega
          have hbound_pt2 : ∀ y ∈ B, ‖jet g y k‖ ≤ C k * (Real.sqrt y.2) ^ (K - 2 * k) := by
            intro y hy
            rw [hB] at hy
            rcases hy with ⟨hy1, hy2⟩
            have hy2' : y.2 < δ := (abs_lt.mp hy2).2
            by_cases hy0 : 0 < y.2
            · rw [jet_of_pos hy0 k]
              exact hbound y hy1 hy0 hy2' k hkm
            · rw [jet_of_nonpos hy0 k]
              have hy2le : y.2 ≤ 0 := le_of_not_gt hy0
              rw [Real.sqrt_eq_zero_of_nonpos hy2le, zero_pow (by omega : K - 2 * k ≠ 0)]
              simp
          rw [Metric.continuousWithinAt_iff]
          intro ε hε
          have hφcont : Continuous (fun y : X × ℝ => C k * (Real.sqrt y.2) ^ (K - 2 * k)) := by
            fun_prop
          have hφz : C k * (Real.sqrt z.2) ^ (K - 2 * k) = 0 := by
            rw [hzeq, Real.sqrt_zero, zero_pow he.ne', mul_zero]
          have hev : ∀ᶠ y in 𝓝 z, C k * (Real.sqrt y.2) ^ (K - 2 * k) < ε :=
            hφcont.continuousAt.tendsto (isOpen_Iio.mem_nhds (by rw [hφz]; exact hε))
          rw [Metric.eventually_nhds_iff] at hev
          obtain ⟨dd, hdd, hdd'⟩ := hev
          refine ⟨dd, hdd, ?_⟩
          intro y hy hyB
          have hjetz : jet g z k = 0 := jet_of_nonpos hz0 k
          rw [hjetz, dist_eq_norm, sub_zero]
          exact lt_of_le_of_lt (hbound_pt2 y hy) (hdd' hyB)
  have hBnhds : B ∈ 𝓝 (x₀, 0) := hBopen.mem_nhds hxB
  show ContDiffWithinAt ℝ (m : ℕ∞) g Set.univ (x₀, 0)
  intro k hk
  exact ⟨B, by simpa using nhdsWithin_le_nhds (s := Set.univ) hBnhds, jet g,
    hTF.of_le (WithTop.coe_le_coe.mpr hk)⟩

end Work.Drive
