import Mathlib
import Submission.Work.BW.PLTensor
import Submission.Work.BW.prekopaLeindlerOneDim
import Submission.Work.BW.layerCakeReduction
import Submission.Work.BW.sliceIntegralEven
import Submission.Work.BW.vaalerSliceMeasurable
import Submission.Work.BW.peakedWeightOneDim
import Submission.Work.BW.vaalerFubiniSliceG
import Submission.Work.BW.logConcaveEvenAntitone
import Submission.Work.BW.sliceVolume_neg
import Submission.Work.BW.sliceFubiniIntegrable
import Submission.Work.BW.peakedDefs
import Submission.Work.BW.vaalerOneDimPeaked
import Submission.Work.BW.orthogonalParameterization
import Submission.Work.BW.vaalerTubeLimit
import Submission.Work.BW.sectionReduction
import Submission.Work.BW.isometricDelta
import Submission.Work.BW.gaussCubeRatio
import Submission.Work.BW.volDilate
import Submission.Work.BW.card_le_of_orthonormal
import Submission.Work.BW.tubeSwap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BW

open MeasureTheory Set Pointwise Filter
open scoped ENNReal Pointwise

private theorem PLm_volume_real : PLm (volume : Measure ℝ) := by
  intro f g m hf hg hm lam h0 h1 hhyp
  exact prekopaLeindlerOneDim f g m hf.aemeasurable hg.aemeasurable hm.aemeasurable h0 h1
    (fun x y => by simpa [smul_eq_mul] using hhyp x y)

private theorem PLm_volume_finZero : PLm (volume : Measure (Fin 0 → ℝ)) := by
  intro f g m hf hg hm lam h0 h1 hhyp
  set x₀ : Fin 0 → ℝ := 0 with hx₀
  have hvol : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [MeasureTheory.volume_pi, Measure.pi_univ]
    simp
  have hInt : ∀ u : (Fin 0 → ℝ) → ℝ≥0∞,
      ∫⁻ x, u x ∂(volume : Measure (Fin 0 → ℝ)) = u x₀ := by
    intro u
    calc ∫⁻ x, u x ∂(volume : Measure (Fin 0 → ℝ))
        = ∫⁻ _x : Fin 0 → ℝ, u x₀ ∂(volume : Measure (Fin 0 → ℝ)) :=
          lintegral_congr fun x => congrArg u (Subsingleton.elim x x₀)
      _ = u x₀ * (volume : Measure (Fin 0 → ℝ)) Set.univ := lintegral_const _
      _ = u x₀ := by rw [hvol, mul_one]
  rw [hInt f, hInt g, hInt m]
  have hpt : lam • x₀ + (1 - lam) • x₀ = x₀ := Subsingleton.elim _ _
  have hh := hhyp x₀ x₀
  rwa [hpt] at hh

private theorem PLm_volume_fin : ∀ n : ℕ, PLm (volume : Measure (Fin n → ℝ))
  | 0 => PLm_volume_finZero
  | (n+1) => by
      haveI : SFinite (volume : Measure (Fin n → ℝ)) := inferInstance
      have hprod : PLm ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
        PLm.tensor (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ))
          (PLm_volume_fin n) PLm_volume_real
      exact PLm.transport (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)
        (piFinSuccAbove_linear n) hprod

private theorem PL_fin {n : ℕ} (f g m : (Fin n → ℝ) → ℝ≥0∞)
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) (hm : AEMeasurable m volume)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (h : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ m (lam • x + (1 - lam) • y)) :
    (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) ≤ ∫⁻ x, m x :=
  (PLm_volume_fin n).to_PL f g m hf hg hm h0 h1 h


private lemma volume_fin_neg {n : ℕ} (S : Set (Fin n → ℝ)) : volume (-S) = volume S := by
  have h : (volume : Measure (Fin n → ℝ)).IsNegInvariant := inferInstance
  exact Measure.measure_neg (volume : Measure (Fin n → ℝ)) S

/-- Non-dependent wrapper for `Fin.insertNth` at a fixed slot. -/
private def ins {n : ℕ} (k : Fin (n+1)) (s : ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) k s x

private lemma ins_apply_self {n : ℕ} (k : Fin (n+1)) (s : ℝ) (x : Fin n → ℝ) :
    ins k s x k = s := by
  simp [ins, Fin.insertNth_apply_same]

private lemma ins_apply_succAbove {n : ℕ} (k : Fin (n+1)) (s : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    ins k s x (k.succAbove j) = x j := by
  simp [ins, Fin.insertNth_apply_succAbove]

private lemma ins_neg {n : ℕ} (k : Fin (n+1)) (s : ℝ) (x : Fin n → ℝ) :
    ins k (-s) (-x) = -ins k s x := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
  · subst h; simp [ins_apply_self]
  · simp [ins_apply_succAbove]

private lemma ins_neg' {n : ℕ} (k : Fin (n+1)) (s : ℝ) (x : Fin n → ℝ) :
    ins k s (-x) = -(ins k (-s) x) := by
  have := ins_neg k (-s) x
  simpa only [neg_neg] using this

private lemma ins_add_smul {n : ℕ} (k : Fin (n+1)) (s₁ s₂ : ℝ) (x y : Fin n → ℝ) (a b : ℝ) :
    ins k (a * s₁ + b * s₂) (a • x + b • y) = a • ins k s₁ x + b • ins k s₂ y := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with h | ⟨i, rfl⟩
  · subst h; simp [ins_apply_self]
  · simp [ins_apply_succAbove]

private lemma convex_sliceSet {n : ℕ} {D : Set (Fin (n+1) → ℝ)} (hconv : Convex ℝ D)
    (k : Fin (n+1)) (s : ℝ) : Convex ℝ {x : Fin n → ℝ | ins k s x ∈ D} := by
  intro x hx y hy a b ha hb hab
  have hx' : ins k s x ∈ D := hx
  have hy' : ins k s y ∈ D := hy
  show ins k s (a • x + b • y) ∈ D
  have h1 : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
  rw [← h1, ins_add_smul]
  exact hconv hx' hy' ha hb hab

private lemma sliceSet_neg {n : ℕ} (D : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (hsym : D = -D) (s : ℝ) :
    {x : Fin n → ℝ | ins k (-s) x ∈ D} = -{x : Fin n → ℝ | ins k s x ∈ D} := by
  have hmem : ∀ y : Fin (n+1) → ℝ, y ∈ D ↔ -y ∈ D :=
    fun y => ((Set.ext_iff.mp hsym) y).trans Set.mem_neg
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_neg]
  constructor
  · intro hx
    rw [ins_neg']
    exact (hmem (ins k (-s) x)).mp hx
  · intro hx
    refine (hmem (ins k (-s) x)).mpr ?_
    rw [← ins_neg']
    exact hx

/-- An even log-concave function `ℝ → ℝ≥0∞` is antitone on `[0, ∞)`. -/
private theorem evenLogConcaveAntitone (V : ℝ → ℝ≥0∞)
    (heven : ∀ s, V (-s) = V s)
    (hlc : ∀ s₁ s₂ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      V (a * s₁ + b * s₂) ≥ V s₁ ^ a * V s₂ ^ b) :
    AntitoneOn V (Set.Ici 0) := by
  intro s hs s' hs' hss'
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ s' from hs') with h0 | hpos
  · have : s = 0 := le_antisymm (h0 ▸ hss') hs
    simp [this, h0]
  · set a : ℝ := (1 - s/s')/2 with ha_def
    set b : ℝ := (1 + s/s')/2 with hb_def
    have ha : 0 ≤ a := by
      have h1 : s/s' ≤ 1 := (div_le_one hpos).mpr hss'
      simp only [ha_def]; linarith
    have hb : 0 ≤ b := by
      have hsdiv : 0 ≤ s/s' := div_nonneg hs (le_of_lt hpos)
      simp only [hb_def]; linarith
    have hab : a + b = 1 := by simp only [ha_def, hb_def]; ring
    have hkey := hlc (-s') s' a b ha hb hab
    have harg : a * (-s') + b * s' = s := by
      simp only [ha_def, hb_def]; field_simp; ring
    rw [harg] at hkey
    rw [heven s'] at hkey
    have hsp : V s' ^ a * V s' ^ b = V s' := by
      rw [← ENNReal.rpow_add_of_nonneg a b ha hb, hab, ENNReal.rpow_one]
    rw [hsp] at hkey
    exact hkey

/-- The abstract Prékopa–Leindler hypothesis for `ℝⁿ`. -/
private def PLHyp (n : ℕ) : Prop :=
  ∀ (f g m : (Fin n → ℝ) → ℝ≥0∞),
    AEMeasurable f volume → AEMeasurable g volume → AEMeasurable m volume →
    ∀ {lam : ℝ}, 0 < lam → lam < 1 →
    (∀ x y, m (lam • x + (1 - lam) • y) ≥ f x ^ lam * g y ^ (1 - lam)) →
    ∫⁻ x, m x ≥ (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam)

/-- Log-concavity of the slice-volume function, from Prékopa–Leindler. -/
private lemma slice_logconcave {n : ℕ} (D : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (hconv : Convex ℝ D)
    (s₁ s₂ a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    volume {x : Fin n → ℝ | ins k (a * s₁ + b * s₂) x ∈ D}
      ≥ (volume {x : Fin n → ℝ | ins k s₁ x ∈ D}) ^ a
        * (volume {x : Fin n → ℝ | ins k s₂ x ∈ D}) ^ b := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simp [ENNReal.rpow_zero, ENNReal.rpow_one]
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simp [ENNReal.rpow_zero, ENNReal.rpow_one]
  have ha1' : a < 1 := by linarith
  have h1a : 1 - a = b := by linarith
  set S₁ : Set (Fin n → ℝ) := {x | ins k s₁ x ∈ D} with hS₁def
  set S₂ : Set (Fin n → ℝ) := {x | ins k s₂ x ∈ D} with hS₂def
  set S₃ : Set (Fin n → ℝ) := {x | ins k (a * s₁ + b * s₂) x ∈ D} with hS₃def
  have hc₁ : Convex ℝ S₁ := convex_sliceSet hconv k s₁
  have hc₂ : Convex ℝ S₂ := convex_sliceSet hconv k s₂
  have hc₃ : Convex ℝ S₃ := convex_sliceSet hconv k (a * s₁ + b * s₂)
  have hf₁ : AEMeasurable (S₁.indicator (fun _ => (1:ℝ≥0∞))) volume :=
    aemeasurable_const.indicator₀ (hc₁.nullMeasurableSet volume)
  have hf₂ : AEMeasurable (S₂.indicator (fun _ => (1:ℝ≥0∞))) volume :=
    aemeasurable_const.indicator₀ (hc₂.nullMeasurableSet volume)
  have hf₃ : AEMeasurable (S₃.indicator (fun _ => (1:ℝ≥0∞))) volume :=
    aemeasurable_const.indicator₀ (hc₃.nullMeasurableSet volume)
  have hmain : ∀ x y, (S₃.indicator (fun _ => (1:ℝ≥0∞))) (a • x + (1 - a) • y)
      ≥ (S₁.indicator (fun _ => (1:ℝ≥0∞))) x ^ a * (S₂.indicator (fun _ => (1:ℝ≥0∞))) y ^ (1 - a) := by
    intro x y
    rw [h1a]
    by_cases hx : x ∈ S₁
    · by_cases hy : y ∈ S₂
      · have hx' : ins k s₁ x ∈ D := by simpa only [hS₁def, Set.mem_setOf_eq] using hx
        have hy' : ins k s₂ y ∈ D := by simpa only [hS₂def, Set.mem_setOf_eq] using hy
        have hmem : a • x + b • y ∈ S₃ := by
          rw [hS₃def]
          show ins k (a * s₁ + b * s₂) (a • x + b • y) ∈ D
          rw [ins_add_smul]
          exact hconv hx' hy' ha hb hab
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        simp [ENNReal.one_rpow]
      · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hbpos, mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hapos, zero_mul]
      exact zero_le
  have happ := PL_fin (S₁.indicator (fun _ => (1:ℝ≥0∞))) (S₂.indicator (fun _ => (1:ℝ≥0∞)))
      (S₃.indicator (fun _ => (1:ℝ≥0∞))) hf₁ hf₂ hf₃ hapos ha1' hmain
  have hvol₁ : ∫⁻ x, (S₁.indicator (fun _ => (1:ℝ≥0∞))) x ∂volume = volume S₁ := by
    rw [lintegral_indicator₀ (hc₁.nullMeasurableSet volume), setLIntegral_one]
  have hvol₂ : ∫⁻ x, (S₂.indicator (fun _ => (1:ℝ≥0∞))) x ∂volume = volume S₂ := by
    rw [lintegral_indicator₀ (hc₂.nullMeasurableSet volume), setLIntegral_one]
  have hvol₃ : ∫⁻ x, (S₃.indicator (fun _ => (1:ℝ≥0∞))) x ∂volume = volume S₃ := by
    rw [lintegral_indicator₀ (hc₃.nullMeasurableSet volume), setLIntegral_one]
  rw [hvol₁, hvol₂, hvol₃, h1a] at happ
  simpa only [hS₁def, hS₂def, hS₃def] using happ

/-- The statement of `unweightedSlice` written with the wrapper `ins`. -/
private theorem unweightedSlice_ins {n : ℕ} (D : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (hconv : Convex ℝ D) (hsym : D = -D) :
    (∀ s, (volume : Measure (Fin n → ℝ)) {x | ins k (-s) x ∈ D}
        = (volume : Measure (Fin n → ℝ)) {x | ins k s x ∈ D}) ∧
    (AntitoneOn (fun s : ℝ => (volume : Measure (Fin n → ℝ))
        {x | ins k s x ∈ D}) (Set.Ici 0)) := by
  constructor
  · intro s
    rw [sliceSet_neg D k hsym s, volume_fin_neg]
  · have hlc : ∀ s₁ s₂ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
        (fun s : ℝ => (volume : Measure (Fin n → ℝ)) {x | ins k s x ∈ D}) (a * s₁ + b * s₂)
          ≥ (fun s : ℝ => (volume : Measure (Fin n → ℝ)) {x | ins k s x ∈ D}) s₁ ^ a
            * (fun s : ℝ => (volume : Measure (Fin n → ℝ)) {x | ins k s x ∈ D}) s₂ ^ b :=
      fun s₁ s₂ a b ha hb hab => slice_logconcave D k hconv s₁ s₂ a b ha hb hab
    have heven : ∀ s : ℝ,
        (fun s : ℝ => (volume : Measure (Fin n → ℝ)) {x | ins k s x ∈ D}) (-s)
          = (fun s : ℝ => (volume : Measure (Fin n → ℝ)) {x | ins k s x ∈ D}) s := by
      intro s
      simp only [sliceSet_neg D k hsym s, volume_fin_neg]
    exact evenLogConcaveAntitone _ heven hlc


private theorem unweightedSliceAux {n : ℕ} (D : Set (Fin (n+1) → ℝ)) (k : Fin (n+1))
    (hconv : Convex ℝ D) (hsym : D = -D) :
    AntitoneOn (fun s : ℝ => (volume : Measure (Fin n → ℝ))
        {x | Fin.insertNth k s x ∈ D}) (Set.Ici 0) :=
  (unweightedSlice_ins D k hconv hsym).2

/-! ## Vaaler's peeling lemma -/

/-! ## Vaaler's peeling lemma -/

theorem vaalerPeelAux {m : ℕ} (U : Set (Fin (m+1) → ℝ)) (j : Fin (m+1))
    (hconv : Convex ℝ U) (hsym : U = -U) (hcl : IsClosed U)
    (g : Fin (m+1) → ℝ → ℝ) (hg_even : ∀ k x, g k (-x) = g k x)
    (hg_anti : ∀ k, AntitoneOn (g k) (Set.Ici 0))
    (hg_nn : ∀ k x, 0 ≤ g k x) (hg_meas : ∀ k, Measurable (g k))
    (hg_int : ∀ k, MeasureTheory.Integrable (g k))
    (ψ : ℝ → ℝ) (hψ_meas : Measurable ψ) (hψ_int : MeasureTheory.Integrable ψ)
    (hpeak : ∀ a, 0 ≤ a → ∫ x in Set.Icc (-a) a, (g j x - ψ x) ≤ 0) :
    ∫ u in U, ∏ k, g k (u k)
      ≤ ∫ u in U, ψ (u j) * ∏ i, g (j.succAbove i) (u (j.succAbove i)) := by
  classical
  have hU : MeasurableSet U := hcl.measurableSet
  -- The remaining weight functions, indexed by `Fin m`.
  set H : Fin m → ℝ → ℝ := fun i => g (j.succAbove i) with hHdef
  have hH_even : ∀ i x, H i (-x) = H i x := fun i x => hg_even (j.succAbove i) x
  have hH_anti : ∀ i, AntitoneOn (H i) (Set.Ici 0) := fun i => hg_anti (j.succAbove i)
  have hH_nn : ∀ i x, 0 ≤ H i x := fun i x => hg_nn (j.succAbove i) x
  have hH_meas : ∀ i, Measurable (H i) := fun i => hg_meas (j.succAbove i)
  have hH_int : ∀ i, MeasureTheory.Integrable (H i) := fun i => hg_int (j.succAbove i)
  -- The peaked slice weight.
  set lam : ℝ → ℝ := fun t =>
    ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i) with hlamdef
  -- Fubini: both sides are integrals against `lam`.
  have hFg := sliceFubiniIntegrable U j hU (g j) (hg_meas j) (hg_int j) H hH_meas hH_int
  have hFp := sliceFubiniIntegrable U j hU ψ hψ_meas hψ_int H hH_meas hH_int
  have hIntG : MeasureTheory.Integrable (fun t : ℝ => g j t * lam t) := by
    change MeasureTheory.Integrable (fun t : ℝ => g j t *
      ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i))
    exact hFg.1
  have hIntP : MeasureTheory.Integrable (fun t : ℝ => ψ t * lam t) := by
    change MeasureTheory.Integrable (fun t : ℝ => ψ t *
      ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i))
    exact hFp.1
  have hLid : (∫ u in U, g j (u j) * ∏ i, H i (u (j.succAbove i))) = ∫ t, g j t * lam t := by
    change (∫ u in U, g j (u j) * ∏ i, H i (u (j.succAbove i)))
      = ∫ t, g j t * ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i)
    exact hFg.2
  have hRid : (∫ u in U, ψ (u j) * ∏ i, H i (u (j.succAbove i))) = ∫ t, ψ t * lam t := by
    change (∫ u in U, ψ (u j) * ∏ i, H i (u (j.succAbove i)))
      = ∫ t, ψ t * ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i)
    exact hFp.2
  -- `lam` is a peaked weight: even, non-negative, measurable and antitone on `[0,∞)`.
  have hlam_even : ∀ t, lam (-t) = lam t := by
    intro t
    change (∫ y in {x : Fin m → ℝ | Fin.insertNth j (-t) x ∈ U}, ∏ i, H i (y i))
      = ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i)
    exact sliceIntegralEven U j hsym hcl H hH_even hH_meas t
  have hlam_anti : AntitoneOn lam (Set.Ici 0) := by
    change AntitoneOn (fun t : ℝ =>
      ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i)) (Set.Ici 0)
    exact layerCakeReduction U j hconv hsym hcl H hH_even hH_anti hH_nn hH_meas hH_int
      (fun D hcv hsy => unweightedSliceAux D j hcv hsy)
  have hlam_meas : Measurable lam := by
    change Measurable (fun t : ℝ =>
      ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i))
    exact vaalerSliceMeasurable U j hcl H hH_meas
  have hlam_nn : ∀ t, 0 ≤ lam t := by
    intro t
    change 0 ≤ ∫ y in {x : Fin m → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, H i (y i)
    exact MeasureTheory.integral_nonneg (fun y => Finset.prod_nonneg (fun i _ => hH_nn i (y i)))
  -- The one-dimensional Vaaler inequality.
  have hint : MeasureTheory.Integrable (fun t : ℝ => (g j t - ψ t) * lam t) := by
    have heq : (fun t : ℝ => (g j t - ψ t) * lam t)
        = fun t : ℝ => g j t * lam t - ψ t * lam t := by
      funext t; ring
    rw [heq]
    exact hIntG.sub hIntP
  have hOne : ∫ t, (fun t : ℝ => g j t - ψ t) t * lam t ≤ 0 :=
    peakedWeightOneDim (φ := fun t : ℝ => g j t - ψ t) (W := lam)
      ((hg_meas j).sub hψ_meas) hlam_meas hlam_even hlam_anti hlam_nn hint
      (fun a ha => hpeak a ha)
  have hsub : ∫ t, (g j t - ψ t) * lam t = (∫ t, g j t * lam t) - (∫ t, ψ t * lam t) := by
    have h1 : (fun t : ℝ => (g j t - ψ t) * lam t)
        = fun t : ℝ => (fun s : ℝ => g j s * lam s) t - (fun s : ℝ => ψ s * lam s) t := by
      funext t
      ring
    rw [h1, MeasureTheory.integral_sub hIntG hIntP]
  have hLHS : ∫ u in U, ∏ k, g k (u k) = ∫ t, g j t * lam t := by
    rw [← hLid]
    refine MeasureTheory.setIntegral_congr_fun hU (fun u _ => ?_)
    simpa only [hHdef] using Fin.prod_univ_succAbove (fun k => g k (u k)) j
  have hRHS : (∫ u in U, ψ (u j) * ∏ i, g (j.succAbove i) (u (j.succAbove i)))
      = ∫ t, ψ t * lam t := hRid
  rw [hLHS, hRHS]
  calc ∫ t, g j t * lam t
      = (∫ t, ψ t * lam t) + ∫ t, (g j t - ψ t) * lam t := by rw [hsub]; ring
    _ ≤ (∫ t, ψ t * lam t) + 0 :=
        add_le_add le_rfl (by simpa using hOne)
    _ = ∫ t, ψ t * lam t := by ring


private lemma hpeak_gd_ud : ∀ a, 0 ≤ a → ∫ x in Set.Icc (-a) a, gd x ≤ ∫ x in Set.Icc (-a) a, ud x := by
  intro a ha
  have h := vaalerOneDimPeaked a ha
  have e1 : (∫ x in Set.Icc (-a) a, gd x)
      = ∫ x in Set.Icc (-a) a, Real.exp (-(Real.pi * x^2)) :=
    setIntegral_congr_fun measurableSet_Icc (fun x _ => rfl)
  have e2 : (∫ x in Set.Icc (-a) a, ud x)
      = ∫ x in Set.Icc (-a) a, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℝ)) x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    unfold ud
    rw [show Set.Icc (-1/2 : ℝ) (1/2) = Set.Icc (-(1/2 : ℝ)) (1/2) from by
      rw [show (-1/2 : ℝ) = -(1/2) by norm_num]]
  rw [e1, e2]; exact h

/-- Difference form of the 1-D peakedness. -/
private lemma hpeak_gd_sub_ud : ∀ a, 0 ≤ a → ∫ x in Set.Icc (-a) a, (gd x - ud x) ≤ 0 := by
  intro a ha
  rw [integral_sub gd_int.integrableOn ud_int.integrableOn]
  linarith [hpeak_gd_ud a ha]

/-- Real-integral form of the theorem. -/
private theorem main_ineq {n : ℕ} (U : Set (Fin n → ℝ))
    (hconv : Convex ℝ U) (hsym : U = -U) (hcl : IsClosed U) :
    ∫ u in U, ∏ i, gd (u i) ≤ ∫ u in U, ∏ i, ud (u i) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact le_refl _
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have key : ∀ S : Finset (Fin (m+1)),
        ∫ u in U, ∏ i, (if i ∈ S then gd else ud) (u i) ≤ ∫ u in U, ∏ i, ud (u i) := by
      intro S
      induction S using Finset.induction with
      | empty =>
          simp only [Finset.notMem_empty, if_false]
          exact le_refl _
      | insert j S' hj ih =>
          have hpeel := vaalerPeelAux U j hconv hsym hcl
            (fun k : Fin (m+1) => if k ∈ insert j S' then gd else ud)
            (fun k x => by
              by_cases hk : k ∈ insert j S'
              · simp only [hk, if_true]; exact gd_even x
              · simp only [hk, if_false]; exact ud_even x)
            (fun k => by
              by_cases hk : k ∈ insert j S'
              · simp only [hk, if_true]; exact gd_anti
              · simp only [hk, if_false]; exact ud_anti)
            (fun k x => by
              by_cases hk : k ∈ insert j S'
              · simp only [hk, if_true]; exact gd_nn x
              · simp only [hk, if_false]; exact ud_nn x)
            (fun k => by
              by_cases hk : k ∈ insert j S'
              · simp only [hk, if_true]; exact gd_meas
              · simp only [hk, if_false]; exact ud_meas)
            (fun k => by
              by_cases hk : k ∈ insert j S'
              · simp only [hk, if_true]; exact gd_int
              · simp only [hk, if_false]; exact ud_int)
            ud ud_meas ud_int
            (fun a ha => by
              simp only [Finset.mem_insert_self, if_true]
              exact hpeak_gd_sub_ud a ha)
          calc ∫ u in U, ∏ i, (if i ∈ insert j S' then gd else ud) (u i)
              ≤ ∫ u in U, ud (u j) *
                  ∏ i, (if j.succAbove i ∈ insert j S' then gd else ud) (u (j.succAbove i)) := hpeel
            _ = ∫ u in U, ∏ i, (if i ∈ S' then gd else ud) (u i) := by
                apply setIntegral_congr_fun hcl.measurableSet
                intro u _
                show ud (u j) *
                      ∏ i, (if j.succAbove i ∈ insert j S' then gd else ud) (u (j.succAbove i))
                    = ∏ i, (if i ∈ S' then gd else ud) (u i)
                rw [Fin.prod_univ_succAbove (fun i : Fin (m+1) =>
                  (if i ∈ S' then gd else ud) (u i)) j]
                simp only [hj, if_false]
                congr 1
                apply Finset.prod_congr rfl
                intro i _
                have hmi : (j.succAbove i ∈ insert j S') ↔ (j.succAbove i ∈ S') := by
                  rw [Finset.mem_insert]
                  constructor
                  · rintro (h | h)
                    · exact absurd h (Fin.succAbove_ne j i)
                    · exact h
                  · exact Or.inr
                simp only [hmi]
            _ ≤ ∫ u in U, ∏ i, ud (u i) := ih
    have hU := key Finset.univ
    simpa only [Finset.mem_univ, if_true] using hU

theorem vaalerPeakedDensityAux (n : ℕ) (U : Set (Fin n → ℝ))
    (hconv : Convex ℝ U) (hsym : U = -U) (hcl : IsClosed U) :
    ∫⁻ u in U, (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i))
      ≥ ∫⁻ u in U, (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))) := by
  have hUi : Integrable (fun u : Fin n → ℝ => ∏ i, ud (u i)) := by
    have h := Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun _ : Fin n => ud) (fun _ => ud_int)
    simpa only [volume_pi] using h
  have hGi : Integrable (fun u : Fin n → ℝ => ∏ i, gd (u i)) := by
    have h := Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℝ))
      (f := fun _ : Fin n => gd) (fun _ => gd_int)
    simpa only [volume_pi] using h
  have hL : (∫⁻ u in U, (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i)))
      = ENNReal.ofReal (∫ u in U, ∏ i, ud (u i)) := by
    have h1 : (∫⁻ u in U, (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i)))
        = ∫⁻ u in U, ENNReal.ofReal (∏ i, ud (u i)) := by
      apply lintegral_congr_ae
      filter_upwards with u
      rw [ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (f := fun i => ud (u i))
        (fun i _ => ud_nn (u i))]
      apply Finset.prod_congr rfl
      intro i _
      unfold ud
      rw [show Set.Icc (-1/2 : ℝ) (1/2) = Set.Icc (-(1/2 : ℝ)) (1/2) from by
        rw [show (-1/2 : ℝ) = -(1/2) by norm_num]]
      by_cases h : u i ∈ Set.Icc (-(1/2 : ℝ)) (1/2)
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hUi.integrableOn
      (ae_of_all _ (fun u => Finset.prod_nonneg (fun i _ => ud_nn (u i))))]
  have hR : (∫⁻ u in U, (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))))
      = ENNReal.ofReal (∫ u in U, ∏ i, gd (u i)) := by
    have h1 : (∫⁻ u in U, (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))))
        = ∫⁻ u in U, ENNReal.ofReal (∏ i, gd (u i)) := by
      apply lintegral_congr_ae
      filter_upwards with u
      rw [ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (f := fun i => gd (u i))
        (fun i _ => gd_nn (u i))]
      apply Finset.prod_congr rfl
      intro i _
      rw [show Real.exp (- Real.pi * (u i)^2) = gd (u i) from by
        unfold gd; rw [neg_mul]]
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hGi.integrableOn
      (ae_of_all _ (fun u => Finset.prod_nonneg (fun i _ => gd_nn (u i))))]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal (main_ineq U hconv hsym hcl)


theorem isometricSectionAux {n k : ℕ} (B : Matrix (Fin n) (Fin k) ℝ)
    (hB : B.transpose * B = 1) (hk : k ≤ n) :
    1 ≤ ∫ x : Fin k → ℝ, (if (∀ i, |(B.mulVec x) i| ≤ 1/2) then (1:ℝ) else 0) := by
  obtain ⟨Bp, hBp, hBo, _hFub⟩ := orthogonalParameterization B hk hB
  have hpeak : ∀ (U : Set (Fin n → ℝ)), Convex ℝ U → U = -U → IsClosed U →
      ∫⁻ u in U, (∏ i, (Set.Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1:ENNReal)) (u i))
        ≥ ∫⁻ u in U, (∏ i, ENNReal.ofReal (Real.exp (- Real.pi * (u i)^2))) :=
    fun U hc hs hcl => vaalerPeakedDensityAux n U hc hs hcl
  have hdelta : ∀ δ : ℝ, 0 < δ →
      (∏ l : Fin (n-k), ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2))
        ≤ ∫ x : Fin k → ℝ,
            ∫ y in Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)),
              (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0) :=
    fun δ hδ => isometricDelta B hB Bp hBp hBo hk hpeak hδ
  have hdelta' : ∀ δ : ℝ, 0 < δ →
      (∏ l : Fin (n-k), ∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2))
        ≤ ∫ y in Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)),
            ∫ x : Fin k → ℝ,
              (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0) := by
    intro δ hδ
    rw [← tubeSwap B hB Bp hδ]
    exact hdelta δ hδ
  have htube := vaalerTubeLimit B hB Bp hBp hBo hk
  have hprod : ∀ δ : ℝ, δ ≠ 0 →
      (∏ _ : Fin (n-k), (1/δ) * (∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2)))
        = (1/δ^(n-k)) * ∏ l : Fin (n-k), (∫ t in Set.Icc (-(δ/2)) (δ/2),
            Real.exp (- Real.pi * t^2)) := by
    intro δ hδ
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, div_pow, one_pow]
  have hb : Tendsto (fun δ : ℝ => (1/δ^(n-k)) *
        ∏ l : Fin (n-k), (∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine (gaussCubeRatio (n-k)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hprod δ (ne_of_gt hδ)
  refine le_of_tendsto_of_tendsto (f := fun δ : ℝ => (1/δ^(n-k) *
        ∏ l : Fin (n-k), (∫ t in Set.Icc (-(δ/2)) (δ/2), Real.exp (- Real.pi * t^2))))
      (g := fun δ : ℝ => (1/δ^(n-k)) *
        ∫ y in Set.pi Set.univ (fun _ : Fin (n-k) => Set.Icc (-(δ/2)) (δ/2)),
          ∫ x : Fin k → ℝ,
            (if (∀ i, |(B.mulVec x + Bp.mulVec y) i| ≤ 1/2) then (1:ℝ) else 0)) hb htube ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδpos : (0:ℝ) < δ := hδ
  exact mul_le_mul_of_nonneg_left (hdelta' δ hδ) (by positivity)

theorem vaalerSectionAux {k n : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) :
    (2 : ℝ) ^ k / Real.sqrt (A.transpose * A).det ≤
      (MeasureTheory.volume {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1}).toReal := by
  by_cases hA : (A.transpose * A).det = 0
  · rw [hA, Real.sqrt_zero, div_zero]
    exact ENNReal.toReal_nonneg
  · obtain ⟨B, hB, hEq⟩ := sectionReduction A hA
    have hk : k ≤ n := card_le_of_orthonormal B hB
    have hiso : 1 ≤ ∫ z : Fin k → ℝ, (if ∀ i, |(B.mulVec z) i| ≤ 1/2 then (1:ℝ) else 0) :=
      isometricSectionAux B hB hk
    have hvol := volDilate A hA
    rw [hvol, hEq, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (Real.sqrt (A.transpose * A).det)⁻¹
        = (Real.sqrt (A.transpose * A).det)⁻¹ * 1 := by ring
      _ ≤ (Real.sqrt (A.transpose * A).det)⁻¹ *
            ∫ z : Fin k → ℝ, (if ∀ i, |(B.mulVec z) i| ≤ 1/2 then (1:ℝ) else 0) :=
          mul_le_mul_of_nonneg_left hiso (by positivity)


end Work.BW
