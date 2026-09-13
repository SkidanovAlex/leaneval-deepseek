import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.Analysis.Convex.prekopa_leindler_1d

namespace Commons.Analysis.Convex

open MeasureTheory Set Pointwise
open Filter

/-- Translation invariance of Lebesgue measure on `ℝ`. -/
lemma volume_vadd (c : ℝ) (s : Set ℝ) : volume (c +ᵥ s) = volume s := by
  have h : c +ᵥ s = (fun z : ℝ => -c + z) ⁻¹' s := by
    ext y; simp only [mem_vadd_set_iff_neg_vadd_mem, mem_preimage]; tauto
  rw [h, measure_preimage_add]

lemma mem_vadd_iff (c x : ℝ) (s : Set ℝ) : x ∈ c +ᵥ s ↔ -c + x ∈ s := by
  simp only [mem_vadd_set_iff_neg_vadd_mem]; constructor <;> intro h <;> simpa using h

/-- One-dimensional Brunn--Minkowski inequality for compact nonempty sets:
`|A| + |B| ≤ |A + B|`. -/
lemma bm_compact_aux (A B : Set ℝ) (hA : IsCompact A) (hB : IsCompact B)
    (hnA : A.Nonempty) (hnB : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  obtain ⟨a0, ha0A, ha0max⟩ := hA.exists_isMaxOn hnA continuous_id.continuousOn
  obtain ⟨b0, hb0B, hb0min⟩ := hB.exists_isMinOn hnB continuous_id.continuousOn
  have hAle : ∀ x ∈ A, x ≤ a0 := fun x hx => ha0max hx
  have hBge : ∀ y ∈ B, b0 ≤ y := fun y hy => hb0min hy
  set A' := (-a0) +ᵥ A with hA'def
  set B' := (-b0) +ᵥ B with hB'def
  have hmemA' : ∀ x, x ∈ A' ↔ a0 + x ∈ A := by
    intro x; rw [hA'def, mem_vadd_iff]
    constructor <;> intro h <;> simpa using h
  have hmemB' : ∀ y, y ∈ B' ↔ b0 + y ∈ B := by
    intro y; rw [hB'def, mem_vadd_iff]
    constructor <;> intro h <;> simpa using h
  have h0A' : (0:ℝ) ∈ A' := by rw [hmemA']; simpa using ha0A
  have h0B' : (0:ℝ) ∈ B' := by rw [hmemB']; simpa using hb0B
  have hsubA : A' ⊆ Iic 0 := by
    intro x hx; rw [hmemA'] at hx; simp only [mem_Iic]
    have := hAle (a0+x) hx; linarith
  have hsubB : B' ⊆ Ici 0 := by
    intro y hy; rw [hmemB'] at hy; simp only [mem_Ici]
    have := hBge (b0+y) hy; linarith
  have hsum : A' + B' = (-(a0+b0)) +ᵥ (A + B) := by
    ext z
    rw [Set.mem_add, mem_vadd_iff, Set.mem_add]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      rw [hmemA'] at hx; rw [hmemB'] at hy
      exact ⟨a0 + x, hx, b0 + y, hy, by ring⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hxa : a - a0 ∈ A' := by
        rw [hmemA']
        have hh : a0 + (a - a0) = a := by ring
        rwa [hh]
      have hyb : b - b0 ∈ B' := by
        rw [hmemB']
        have hh : b0 + (b - b0) = b := by ring
        rwa [hh]
      exact ⟨a - a0, hxa, b - b0, hyb, by linarith⟩
  have hunion : A' ∪ B' ⊆ A' + B' := by
    intro z hz
    rw [Set.mem_add]
    rcases hz with hz | hz
    · exact ⟨z, hz, 0, h0B', by simp⟩
    · exact ⟨0, h0A', z, hz, by simp⟩
  have hA'mble : MeasurableSet A' := by
    rw [hA'def]; exact (hA.vadd (-a0)).measurableSet
  have hcap : A' ∩ B' ⊆ {(0:ℝ)} := by
    intro z hz
    rw [mem_inter_iff] at hz
    rw [mem_singleton_iff]
    have h1 : z ≤ 0 := hsubA hz.1
    have h2 : 0 ≤ z := hsubB hz.2
    linarith
  have hcap0 : volume (A' ∩ B') = 0 := measure_mono_null hcap (by simp)
  have hunion_meas : volume (A' ∪ B') = volume A' + volume B' := by
    have := measure_union_add_inter' (μ := volume) hA'mble B'
    rw [hcap0, add_zero] at this
    exact this
  have hAB' : volume (A' + B') = volume (A + B) := by rw [hsum, volume_vadd]
  calc volume A + volume B = volume A' + volume B' := by rw [hA'def, hB'def, volume_vadd, volume_vadd]
    _ = volume (A' ∪ B') := hunion_meas.symm
    _ ≤ volume (A' + B') := measure_mono hunion
    _ = volume (A + B) := hAB'

/-! ### Auxiliary analytic lemmas -/

/-- `min (f ·) n` tends to `f` in integral as `n → ∞`, for an integrable `f`. -/
theorem tendsto_integral_min {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫ x, min (f x) (n : ℝ) ∂μ) atTop (nhds (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => |f x|) (fun n => ?_)
    (by simpa only [Real.norm_eq_abs] using hf.abs) (fun n => ?_) ?_
  · exact (hf.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  · filter_upwards with x
    by_cases h : 0 ≤ f x
    · rw [Real.norm_eq_abs, abs_of_nonneg (le_min h (Nat.cast_nonneg n)), abs_of_nonneg h]
      exact min_le_left _ _
    · rw [not_le] at h
      rw [Real.norm_eq_abs, min_eq_left (le_of_lt (lt_of_lt_of_le h (Nat.cast_nonneg n)))]
  · filter_upwards with x
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_atTop.2 ⟨⌈f x⌉₊, fun n hn => by exact_mod_cast hn⟩] with n hn
    exact min_eq_left (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))

theorem min_integrable_of_nonneg {F : ℝ → ℝ} (hF : Integrable F) (hFnn : ∀ a, 0 ≤ F a) (n : ℕ) :
    Integrable (fun a => min (F a) (n:ℝ)) volume := by
  refine hF.mono' ((hF.aemeasurable.min aemeasurable_const).aestronglyMeasurable) ?_
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hFnn a) (Nat.cast_nonneg n))]
  exact min_le_left _ _

/-- Structured one-dimensional Prékopa–Leindler: the hypothesis is only assumed off the
preimage (under the map `(a,a') ↦ (1-lam)*a + lam*a'`) of a null set `S`. -/
theorem PL1_structured {F G H : ℝ → ℝ} (hF : Integrable F) (hG : Integrable G) (hH : Integrable H)
    (hFnn : ∀ a, 0 ≤ F a) (hGnn : ∀ a, 0 ≤ G a) (hHnn : ∀ a, 0 ≤ H a)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (S : Set ℝ) (hSmeas : MeasurableSet S) (hSnull : volume S = 0)
    (hHYP : ∀ a a', (1 - lam) * a + lam * a' ∉ S →
      H ((1 - lam) * a + lam * a') ≥ F a ^ (1 - lam) * G a' ^ lam) :
    (∫ a, F a) ^ (1 - lam) * (∫ a, G a) ^ lam ≤ ∫ a, H a := by
  have h1ml : (0:ℝ) < 1 - lam := by linarith
  have hSreal : volume.real S = 0 := by rw [measureReal_def, hSnull]; simp
  have hSint : Integrable (S.indicator (fun _ => (1:ℝ))) volume :=
    (integrableOn_const (C := (1:ℝ)) (by rw [hSnull]; exact ENNReal.zero_ne_top)).integrable_indicator hSmeas
  have hSint_eq : ∫ a, S.indicator (fun _ => (1:ℝ)) a = 0 := by
    rw [integral_indicator hSmeas, setIntegral_const, hSreal]; simp
  set Ht : ℕ → ℝ → ℝ := fun n a => H a + (n:ℝ) * S.indicator (fun _ => (1:ℝ)) a with hHt
  have key : ∀ n : ℕ, (∫ a, min (F a) (n:ℝ)) ^ (1-lam) * (∫ a, min (G a) (n:ℝ)) ^ lam ≤ ∫ a, H a := by
    intro n
    have hHtint : Integrable (Ht n) volume := by
      simp only [hHt]; exact hH.add (hSint.const_mul (n:ℝ))
    have hHtnn : ∀ a, 0 ≤ Ht n a := by
      intro a; simp only [hHt]
      have hind : (0:ℝ) ≤ S.indicator (fun _ => (1:ℝ)) a := by
        by_cases h : a ∈ S
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h]
      nlinarith [hHnn a, hind, Nat.cast_nonneg (α := ℝ) n]
    have hFmint : Integrable (fun a => min (F a) (n:ℝ)) volume := min_integrable_of_nonneg hF hFnn n
    have hGmint : Integrable (fun a => min (G a) (n:ℝ)) volume := min_integrable_of_nonneg hG hGnn n
    have hFmn : ∀ a, 0 ≤ min (F a) (n:ℝ) := fun a => le_min (hFnn a) (Nat.cast_nonneg n)
    have hGmn : ∀ a, 0 ≤ min (G a) (n:ℝ) := fun a => le_min (hGnn a) (Nat.cast_nonneg n)
    have hhyp : ∀ x y : ℝ, Ht n ((1 - lam) * x + lam * y)
        ≥ min (F x) (n:ℝ) ^ (1 - lam) * min (G y) (n:ℝ) ^ lam := by
      intro x y
      have hminle : min (F x) (n:ℝ) ^ (1 - lam) * min (G y) (n:ℝ) ^ lam
          ≤ F x ^ (1 - lam) * G y ^ lam :=
        mul_le_mul (Real.rpow_le_rpow (le_min (hFnn x) (Nat.cast_nonneg n)) (min_le_left _ _) h1ml.le)
          (Real.rpow_le_rpow (le_min (hGnn y) (Nat.cast_nonneg n)) (min_le_left _ _) hl0.le)
          (Real.rpow_nonneg (le_min (hGnn y) (Nat.cast_nonneg n)) lam) (Real.rpow_nonneg (hFnn x) (1-lam))
      by_cases hmem : (1 - lam) * x + lam * y ∈ S
      · have hEq : Ht n ((1 - lam) * x + lam * y) = H ((1 - lam) * x + lam * y) + (n:ℝ) := by
          simp only [hHt, Set.indicator_of_mem hmem]; ring
        rw [hEq]
        have h1 : (0:ℝ) ≤ min (F x) (n:ℝ) := le_min (hFnn x) (Nat.cast_nonneg n)
        have h2 : (0:ℝ) ≤ min (G y) (n:ℝ) := le_min (hGnn y) (Nat.cast_nonneg n)
        have h3 : min (F x) (n:ℝ) ≤ (n:ℝ) := min_le_right _ _
        have h4 : min (G y) (n:ℝ) ≤ (n:ℝ) := min_le_right _ _
        have h5 : min (F x) (n:ℝ) ^ (1-lam) * min (G y) (n:ℝ) ^ lam
            ≤ (n:ℝ) ^ (1-lam) * (n:ℝ) ^ lam :=
          mul_le_mul (Real.rpow_le_rpow h1 h3 h1ml.le) (Real.rpow_le_rpow h2 h4 hl0.le)
            (Real.rpow_nonneg h2 lam) (Real.rpow_nonneg (Nat.cast_nonneg n) (1-lam))
        have h6 : (n:ℝ) ^ (1-lam) * (n:ℝ) ^ lam ≤ (1-lam) * (n:ℝ) + lam * (n:ℝ) :=
          Real.geom_mean_le_arith_mean2_weighted h1ml.le hl0.le (Nat.cast_nonneg n) (Nat.cast_nonneg n) (by ring)
        linarith [hHnn ((1-lam)*x + lam*y), h5, h6]
      · have hEq : Ht n ((1 - lam) * x + lam * y) = H ((1 - lam) * x + lam * y) := by
          simp only [hHt, Set.indicator_of_notMem hmem]; ring
        rw [hEq]
        exact le_trans hminle (hHYP x y hmem)
    have hPL := prekopa_leindler_1d hFmint hGmint hHtint hFmn hGmn hHtnn lam hl0.le hl1.le hhyp
    refine le_trans hPL ?_
    have : ∫ a, Ht n a = ∫ a, H a := by
      simp only [hHt]
      rw [integral_add hH (hSint.const_mul (n:ℝ)), integral_const_mul, hSint_eq]
      ring
    rw [this]
  have hlimF := tendsto_integral_min hF
  have hlimG := tendsto_integral_min hG
  have hlim : Tendsto (fun n : ℕ => (∫ a, min (F a) (n:ℝ)) ^ (1-lam)
      * (∫ a, min (G a) (n:ℝ)) ^ lam) atTop
      (nhds ((∫ a, F a) ^ (1-lam) * (∫ a, G a) ^ lam)) :=
    (hlimF.rpow_const (Or.inr h1ml.le)).mul (hlimG.rpow_const (Or.inr hl0.le))
  exact le_of_tendsto hlim (Eventually.of_forall key)

/-! ### The product step -/

/-- The Prékopa–Leindler statement on a measure space `(X, ν)`. -/
def PLStmt (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    (ν : Measure X) : Prop :=
  ∀ (f g h : X → ℝ) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) →
    Integrable f ν → Integrable g ν → Integrable h ν →
    (∀ x y, h ((1 - lam) • x + lam • y) ≥ f x ^ (1 - lam) * g y ^ lam) →
    (∫ x, f x ∂ν) ^ (1 - lam) * (∫ x, g x ∂ν) ^ lam ≤ ∫ x, h x ∂ν

/-- If Prékopa–Leindler holds on `(X, ν)` then it holds on `ℝ × X` with the product measure,
using the one-dimensional Prékopa–Leindler inequality on the marginal measures. -/
theorem PL_prod_step {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (IH : PLStmt X ν) : PLStmt (ℝ × X) (volume.prod ν) := by
  intro f g h lam hl0 hl1 hfn hgn hhn hf hg hh hfg
  rcases eq_or_lt_of_le hl0 with rfl | hl0'
  · have hle : ∀ p : ℝ × X, f p ≤ h p := fun p => by
      have h1 := hfg p p
      simpa using h1
    have := integral_mono hf hh hle
    simpa using this
  rcases eq_or_lt_of_le hl1 with rfl | hl1'
  · have hle : ∀ p : ℝ × X, g p ≤ h p := fun p => by
      have h1 := hfg p p
      simpa using h1
    have := integral_mono hg hh hle
    simpa using this
  have h1ml : (0:ℝ) < 1 - lam := by linarith
  set F : ℝ → ℝ := fun a => ∫ y, f (a, y) ∂ν with hFdef
  set G : ℝ → ℝ := fun a => ∫ y, g (a, y) ∂ν with hGdef
  set H : ℝ → ℝ := fun a => ∫ y, h (a, y) ∂ν with hHdef
  have hFint : Integrable F volume := by rw [hFdef]; exact hf.integral_prod_left
  have hGint : Integrable G volume := by rw [hGdef]; exact hg.integral_prod_left
  have hHint : Integrable H volume := by rw [hHdef]; exact hh.integral_prod_left
  have hFnn : ∀ a, 0 ≤ F a := by intro a; rw [hFdef]; exact integral_nonneg (fun y => hfn (a,y))
  have hGnn : ∀ a, 0 ≤ G a := by intro a; rw [hGdef]; exact integral_nonneg (fun y => hgn (a,y))
  have hHnn : ∀ a, 0 ≤ H a := by intro a; rw [hHdef]; exact integral_nonneg (fun y => hhn (a,y))
  have hShnull : volume {z : ℝ | ¬ Integrable (fun y => h (z, y)) ν} = 0 :=
    ae_iff.mpr hh.prod_right_ae
  obtain ⟨S, hShS, hSmeas, hSnull⟩ := exists_measurable_superset_of_null hShnull
  have hHYP : ∀ a a' : ℝ, (1 - lam) * a + lam * a' ∉ S →
      H ((1 - lam) * a + lam * a') ≥ F a ^ (1 - lam) * G a' ^ lam := by
    intro a a' hzS
    have hz : (1 - lam) * a + lam * a' ∉ {z : ℝ | ¬ Integrable (fun y => h (z, y)) ν} :=
      fun hc => hzS (hShS hc)
    have hhint : Integrable (fun y => h ((1 - lam) * a + lam * a', y)) ν := by
      by_contra hc; exact hz hc
    by_cases hfa : Integrable (fun y => f (a, y)) ν
    · by_cases hga : Integrable (fun y => g (a', y)) ν
      · have hIH := IH (fun y => f (a, y)) (fun y => g (a', y))
          (fun y => h ((1 - lam) * a + lam * a', y)) lam hl0'.le hl1'.le
          (fun y => hfn (a,y)) (fun y => hgn (a',y)) (fun y => hhn _) hfa hga hhint ?_
        · rw [hFdef, hGdef, hHdef]; exact hIH
        · intro u v
          have h1 := hfg (a, u) (a', v)
          simpa using h1
      · have hG0 : G a' = 0 := by rw [hGdef]; exact integral_undef hga
        rw [hG0, Real.zero_rpow (ne_of_gt hl0'), mul_zero, hHdef]
        exact integral_nonneg (fun y => hhn ((1-lam)*a + lam*a', y))
    · have hF0 : F a = 0 := by rw [hFdef]; exact integral_undef hfa
      rw [hF0, Real.zero_rpow (ne_of_gt h1ml), zero_mul, hHdef]
      exact integral_nonneg (fun y => hhn ((1-lam)*a + lam*a', y))
  have hmain := PL1_structured hFint hGint hHint hFnn hGnn hHnn hl0' hl1' S hSmeas hSnull hHYP
  have hFeq : ∫ a, F a = ∫ z : ℝ × X, f z ∂(volume.prod ν) := by
    rw [hFdef]; exact (integral_prod f hf).symm
  have hGeq : ∫ a, G a = ∫ z : ℝ × X, g z ∂(volume.prod ν) := by
    rw [hGdef]; exact (integral_prod g hg).symm
  have hHeq : ∫ a, H a = ∫ z : ℝ × X, h z ∂(volume.prod ν) := by
    rw [hHdef]; exact (integral_prod h hh).symm
  rw [hFeq, hGeq, hHeq] at hmain
  exact hmain

/-! ### Transfer to `Fin n → ℝ` -/

lemma succ_symm_apply' (n : ℕ) (p : ℝ × (Fin n → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p = Fin.cons p.1 p.2 := by
  funext i
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero, Fin.consEquiv_apply]

lemma succ_symm_linear (n : ℕ) (p q : ℝ × (Fin n → ℝ)) (a b : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm (a • p + b • q)
      = a • (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm p
        + b • (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm q := by
  rw [succ_symm_apply', succ_symm_apply', succ_symm_apply']
  funext i
  induction i using Fin.cases with
  | zero => simp [Fin.cons_zero]
  | succ j => simp [Fin.cons_succ]

theorem PL_fin_zero : PLStmt (Fin 0 → ℝ) volume := by
  intro f g h lam hl0 hl1 hfn hgn hhn hf hg hh hfg
  have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (0 : Fin 0 → ℝ) := by
    rw [show (volume : Measure (Fin 0 → ℝ)) =
      Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) from rfl]
    exact Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ)) (0 : Fin 0 → ℝ)
  have hfi : ∫ x : Fin 0 → ℝ, f x = f 0 := by rw [hvol]; exact integral_dirac f 0
  have hgi : ∫ x : Fin 0 → ℝ, g x = g 0 := by rw [hvol]; exact integral_dirac g 0
  have hhi : ∫ x : Fin 0 → ℝ, h x = h 0 := by rw [hvol]; exact integral_dirac h 0
  rw [hfi, hgi, hhi]
  have h1 := hfg 0 0
  simpa using h1

theorem PL_fin_succ {n : ℕ} (IH : PLStmt (Fin n → ℝ) volume) :
    PLStmt (Fin (n+1) → ℝ) volume := by
  intro f g h lam hl0 hl1 hfn hgn hhn hf hg hh hfg
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0 with he
  have hMP : MeasurePreserving (e : (Fin (n+1) → ℝ) → ℝ × (Fin n → ℝ))
      (volume : Measure (Fin (n+1) → ℝ)) (volume : Measure (ℝ × (Fin n → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hIH' : PLStmt (ℝ × (Fin n → ℝ)) volume :=
    PL_prod_step (volume : Measure (Fin n → ℝ)) IH
  have hfl : Integrable (fun p : ℝ × (Fin n → ℝ) => f (e.symm p)) volume :=
    (hMP.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)).mpr hf
  have hgl : Integrable (fun p : ℝ × (Fin n → ℝ) => g (e.symm p)) volume :=
    (hMP.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)).mpr hg
  have hhl : Integrable (fun p : ℝ × (Fin n → ℝ) => h (e.symm p)) volume :=
    (hMP.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)).mpr hh
  have hef : ∫ p : ℝ × (Fin n → ℝ), f (e.symm p) = ∫ x : Fin (n+1) → ℝ, f x := by
    rw [← hMP.integral_comp' (g := fun p : ℝ × (Fin n → ℝ) => f (e.symm p))]
    simp
  have heg : ∫ p : ℝ × (Fin n → ℝ), g (e.symm p) = ∫ x : Fin (n+1) → ℝ, g x := by
    rw [← hMP.integral_comp' (g := fun p : ℝ × (Fin n → ℝ) => g (e.symm p))]
    simp
  have heh : ∫ p : ℝ × (Fin n → ℝ), h (e.symm p) = ∫ x : Fin (n+1) → ℝ, h x := by
    rw [← hMP.integral_comp' (g := fun p : ℝ × (Fin n → ℝ) => h (e.symm p))]
    simp
  have hhyp : ∀ p q : ℝ × (Fin n → ℝ),
      (fun p : ℝ × (Fin n → ℝ) => h (e.symm p)) ((1 - lam) • p + lam • q)
        ≥ (fun p : ℝ × (Fin n → ℝ) => f (e.symm p)) p ^ (1 - lam)
          * (fun p : ℝ × (Fin n → ℝ) => g (e.symm p)) q ^ lam := by
    intro p q
    simp only []
    rw [show e.symm ((1 - lam) • p + lam • q) = (1 - lam) • e.symm p + lam • e.symm q from by
      rw [he]; exact succ_symm_linear n p q (1 - lam) lam]
    exact hfg (e.symm p) (e.symm q)
  have hres := hIH' (fun p : ℝ × (Fin n → ℝ) => f (e.symm p))
    (fun p : ℝ × (Fin n → ℝ) => g (e.symm p)) (fun p : ℝ × (Fin n → ℝ) => h (e.symm p))
    lam hl0 hl1 (fun p => hfn _) (fun p => hgn _) (fun p => hhn _) hfl hgl hhl hhyp
  rw [hef, heg, heh] at hres
  exact hres

theorem PL_fin : ∀ n : ℕ, PLStmt (Fin n → ℝ) volume
  | 0 => PL_fin_zero
  | n+1 => PL_fin_succ (PL_fin n)

/-- Prékopa–Leindler inequality on `Fin n → ℝ` with the product Lebesgue measure. -/
theorem prekopa_leindler_pi {n : ℕ} (f g h : (Fin n → ℝ) → ℝ)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g)
    (hh : MeasureTheory.Integrable h)
    (hfg : ∀ x y, h ((1 - lam) • x + lam • y) ≥ f x ^ (1 - lam) * g y ^ lam) :
    (∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam ≤ ∫ x, h x :=
  PL_fin n f g h lam hl0 hl1 hfn hgn hhn hf hg hh hfg

/-! ### Transfer to `EuclideanSpace ℝ (Fin n)` -/

lemma toLp_smul_add {V : Type*} [AddCommGroup V] [Module ℝ V] (p : ENNReal) (x y : V) (a b : ℝ) :
    WithLp.toLp p (a • x + b • y) = a • WithLp.toLp p x + b • WithLp.toLp p y := by
  rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]

theorem PL_euclidean (n : ℕ) : PLStmt (EuclideanSpace ℝ (Fin n)) volume := by
  intro f g h lam hl0 hl1 hfn hgn hhn hf hg hh hfg
  set E := MeasurableEquiv.toLp 2 (Fin n → ℝ) with hE
  have hMP : MeasurePreserving (E : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (volume : Measure (Fin n → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hE]
    exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).symm
  have hfl : Integrable (fun x : Fin n → ℝ => f (E x)) volume :=
    (hMP.integrable_comp_emb (MeasurableEquiv.measurableEmbedding E)).mpr hf
  have hgl : Integrable (fun x : Fin n → ℝ => g (E x)) volume :=
    (hMP.integrable_comp_emb (MeasurableEquiv.measurableEmbedding E)).mpr hg
  have hhl : Integrable (fun x : Fin n → ℝ => h (E x)) volume :=
    (hMP.integrable_comp_emb (MeasurableEquiv.measurableEmbedding E)).mpr hh
  have hef : ∫ x : Fin n → ℝ, f (E x) = ∫ y : EuclideanSpace ℝ (Fin n), f y :=
    hMP.integral_comp' (g := f)
  have heg : ∫ x : Fin n → ℝ, g (E x) = ∫ y : EuclideanSpace ℝ (Fin n), g y :=
    hMP.integral_comp' (g := g)
  have heh : ∫ x : Fin n → ℝ, h (E x) = ∫ y : EuclideanSpace ℝ (Fin n), h y :=
    hMP.integral_comp' (g := h)
  have hhyp : ∀ x y : Fin n → ℝ,
      (fun z : Fin n → ℝ => h (E z)) ((1 - lam) • x + lam • y)
        ≥ (fun z : Fin n → ℝ => f (E z)) x ^ (1 - lam)
          * (fun z : Fin n → ℝ => g (E z)) y ^ lam := by
    intro x y
    simp only []
    rw [show E ((1 - lam) • x + lam • y) = (1 - lam) • E x + lam • E y from by
      rw [hE]
      simp only [MeasurableEquiv.coe_toLp]
      exact toLp_smul_add 2 x y (1 - lam) lam]
    exact hfg (E x) (E y)
  have hres := PL_fin n (fun x : Fin n → ℝ => f (E x)) (fun x : Fin n → ℝ => g (E x))
    (fun x : Fin n → ℝ => h (E x)) lam hl0 hl1 (fun x => hfn _) (fun x => hgn _)
    (fun x => hhn _) hfl hgl hhl hhyp
  rw [hef, heg, heh] at hres
  exact hres

theorem prekopa_leindler_inequality {n : ℕ} (f g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g)
    (hh : MeasureTheory.Integrable h)
    (hfg : ∀ x y, h ((1 - lam) • x + lam • y) ≥ f x ^ (1 - lam) * g y ^ lam) :
    (∫ x, f x) ^ (1 - lam) * (∫ x, g x) ^ lam ≤ ∫ x, h x :=
  PL_euclidean n f g h lam hl0 hl1 hfn hgn hhn hf hg hh hfg

end Commons.Analysis.Convex