import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Submission.Commons.Analysis.Calculus.contDiff_setIntegral_isCompact
import Submission.Commons.Analysis.Calculus.contDiff_setIntegral_isCompact_pi
import Submission.Commons.Analysis.Fourier.plancherel_one_sided_schwartz
import Submission.Work.SmallBoxPairRelDecomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-276 — the momentum form of the pair term, part (a):
the relative-coordinate pair density `pairFibreDens`

`SmallBoxPairRelDecomp.q4PairWord_eq_relDens_auto` writes

    q4PairWord = Σ_{i≠j} ∫_u W₁(u)·(∫_z χ(z+u)χ(z)·Q_{ij}(z+u,z) dz)

with `W₁ = wScaled ℓ (g₀ v h)` and `Q_{ij} = pairFibreFun ℓ Φ i j` the peeled pair
fibre.  The next step (D1 step (i), the *momentum* form) is to Plancherel in `u`
against `Ŵ₁`.  This module isolates the `u`-dependent factor

    pairFibreDens ℓ Φ i j u := ∫_{acube ℓ} χ(z+u)χ(z)·Q_{ij}(z+u,z) dz ,

proves that it is exactly the fibre of `pairRelTerm`, that it vanishes off
`acube (2ℓ)` (so it is compactly supported), gives its sup bound on the cube,
and (from continuity of `Φ`) that it is bounded, continuous, integrable and in
`L²`.  These are the hypotheses under which the Plancherel/multiplication
formula can be applied to `∫_u W₁(u)·pairFibreDens u du`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators Convolution
set_option maxHeartbeats 1000000

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The pair density -/

/-- **The relative-coordinate pair density.**  The `u`-fibre of `pairRelTerm`:
the integral over the box coordinate `z` of `χ(z+u)χ(z)` times the peeled pair
fibre `Q_{ij}(z+u,z)` (`SmallBoxPairRelDecomp.pairFibreFun`). -/
noncomputable def pairFibreDens {p : ℕ} (ℓ : ℝ) (Φ : X (p + 2) → ℝ) (i j : Fin (p + 2))
    (u : ℝ³) : ℝ :=
  ∫ z in acube ℓ, chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z

/-- The unrestricted `z`-integral defining `pairFibreDens` equals its restriction
to `acube ℓ` (the bump `χ_ℓ z` vanishes off the cube). -/
lemma pairFibreDens_eq_integral {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (Φ : X (p + 2) → ℝ)
    (i j : Fin (p + 2)) (u : ℝ³) :
    pairFibreDens ℓ Φ i j u
      = ∫ z, chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z := by
  unfold pairFibreDens
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
  have hzc : chiScale ℓ z = 0 :=
    not_ne_iff.mp fun h => hz (chiScale_mem_acube hℓ h)
  rw [hzc]
  ring

/-- **`pairRelTerm` as a `u`-integral against the pair density** (D1 step (i),
first move): the fibre `pairFibreDens` is exactly the `u`-dependent factor of
`pairRelTerm`. -/
theorem pairRelTerm_eq_integral_pairFibreDens {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : X (p + 2) → ℝ) (W : ℝ³ → ℝ) {i j : Fin (p + 2)} (hij : i ≠ j) :
    pairRelTerm ℓ Φ W i j = ∫ u, W u * pairFibreDens ℓ Φ i j u := by
  unfold pairRelTerm
  rw [dif_pos hij]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [pairFibreDens_eq_integral hℓ Φ i j u]

/-! ## 2. Compact support -/

/-- **`pairFibreDens` vanishes off `acube (2ℓ)`.**  If `|u_m| > ℓ` for some `m`
then for every `z ∈ acube ℓ` one has `z + u ∉ acube ℓ`, so `χ_ℓ(z+u) = 0` and
the integrand vanishes identically. -/
lemma pairFibreDens_eq_zero_of_coord {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : X (p + 2) → ℝ) (i j : Fin (p + 2)) {u : ℝ³}
    (hu : ∃ m : Fin 3, u m < -ℓ ∨ ℓ < u m) :
    pairFibreDens ℓ Φ i j u = 0 := by
  rw [pairFibreDens]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  obtain ⟨m, hm⟩ := hu
  have hzm : z m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hz m
  rw [Set.mem_Icc] at hzm
  have h0 : chiScale ℓ (z + u) = 0 := by
    refine not_ne_iff.mp fun h => ?_
    have hzu : z + u ∈ acube ℓ := chiScale_mem_acube hℓ h
    have hsm : (z + u) m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hzu m
    rw [Set.mem_Icc] at hsm
    have hsum1 : z.ofLp m + u.ofLp m ≤ ℓ / 2 := hsm.2
    have hsum2 : -ℓ / 2 ≤ z.ofLp m + u.ofLp m := hsm.1
    rcases hm with hm | hm <;> linarith [hzm.1, hzm.2]
  rw [h0]
  ring

/-- **`pairFibreDens` vanishes off `acube (2ℓ)`.**  If `|u_m| > ℓ` for some `m`
then for every `z ∈ acube ℓ` one has `z + u ∉ acube ℓ`, so `χ_ℓ(z+u) = 0` and
the integrand vanishes identically. -/
theorem pairFibreDens_eq_zero_of_notMem {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : X (p + 2) → ℝ) (i j : Fin (p + 2)) {u : ℝ³} (hu : u ∉ acube (2 * ℓ)) :
    pairFibreDens ℓ Φ i j u = 0 := by
  refine pairFibreDens_eq_zero_of_coord hℓ Φ i j ?_
  by_contra hcon
  push Not at hcon
  apply hu
  rw [mem_acube_iff]
  intro m
  obtain ⟨h1, h2⟩ := hcon m
  rw [Set.mem_Icc]
  have hA : -(2 * ℓ) / 2 = -ℓ := by ring
  have hB : (2 * ℓ) / 2 = ℓ := by ring
  constructor <;> linarith

/-! ## 3. The sup bound on the cube -/

/-- **Bound of the pair density.**  For `Φ` bounded by `B` on the box,

    |pairFibreDens ℓ Φ i j u| ≤ chiSup² · 4B²ℓ^{3p} · ℓ³   for every `u`. -/
theorem abs_pairFibreDens_le {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B)
    (hΦB : ∀ x ∈ abox (p + 2) ℓ, |Φ x| ≤ B) (u : ℝ³) :
    |pairFibreDens ℓ Φ i j u| ≤ chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3 := by
  have hC : 0 ≤ chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) := by positivity
  have hpoint : ∀ᵐ z ∂((volume : Measure ℝ³).restrict (acube ℓ)),
      ‖chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z‖
        ≤ chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) := by
    filter_upwards [ae_restrict_mem (acube_measurable ℓ)] with z hz
    by_cases h1 : chiScale ℓ (z + u) = 0
    · rw [h1]
      simp only [zero_mul, norm_zero]
      exact hC
    · have hzu : z + u ∈ acube ℓ := chiScale_mem_acube hℓ h1
      have hQ : |pairFibreFun ℓ Φ i j (z + u) z| ≤ 4 * B ^ 2 * ℓ ^ (3 * p) :=
        pairFibreFun_abs_le (p := p) hℓ i j hij hΦc hB hΦB hzu hz
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |chiScale ℓ (z + u)| * |chiScale ℓ z| * |pairFibreFun ℓ Φ i j (z + u) z|
          ≤ chiSup * chiSup * (4 * B ^ 2 * ℓ ^ (3 * p)) :=
            mul_le_mul (mul_le_mul (abs_chiScale_le_chiSup ℓ (z + u))
              (abs_chiScale_le_chiSup ℓ z) (abs_nonneg _) (chiSup_pos.le)) hQ
              (abs_nonneg _) (mul_nonneg chiSup_pos.le chiSup_pos.le)
        _ = chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) := by ring
  have _ : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  have hmain : ‖∫ z in acube ℓ,
      chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z‖
      ≤ (chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p))) *
        ((volume : Measure ℝ³).restrict (acube ℓ)).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const hpoint
  rw [real_volume_acube ℓ hℓ.le] at hmain
  rw [Real.norm_eq_abs] at hmain
  unfold pairFibreDens
  calc |∫ z in acube ℓ, chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z|
      ≤ (chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p))) * ℓ ^ 3 := hmain
    _ = chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3 := by ring

/-! ## 4. Measurability, integrability and `L²` membership -/

/-- Joint strong measurability of the peeled pair fibre (for continuous `Φ`). -/
lemma stronglyMeasurable_pairFibreFun {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2))
    (hij : i ≠ j) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    StronglyMeasurable (fun q : ℝ³ × ℝ³ => pairFibreFun ℓ Φ i j q.1 q.2) := by
  set j' := sucAboveInv i j hij with hj'def
  have _ : IsFiniteMeasure ((volume : Measure (X p)).restrict (abox p ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top p ℓ hℓ.le⟩
  have hAc : Continuous (fun r2 : X p => aP ℓ i (aP ℓ j Φ) (rest2 i j' r2)) := by
    have hins : Continuous (fun r2 : X p => rest2 i j' r2) := by
      have h1 : Continuous (fun r2 : X p => ((0 : ℝ³), kcInsN p j' ((0 : ℝ³), r2))) :=
        Continuous.prodMk continuous_const
          ((kcInsN_cont (n := p) j').comp (Continuous.prodMk continuous_const continuous_id))
      exact (kcInsN_cont (n := p + 1) i).comp h1
    exact (aP_continuous hℓ i (aP_continuous hℓ j hΦc)).comp hins
  have hQic : Continuous (aQ ℓ i Φ) := by
    unfold aQ
    exact hΦc.sub (aP_continuous hℓ i hΦc)
  have hQjc : Continuous (aQ ℓ j (aQ ℓ i Φ)) := by
    unfold aQ
    exact hQic.sub (aP_continuous hℓ j hQic)
  have hinsQ : Continuous (fun q : (ℝ³ × ℝ³) × X p => ins2 i j' q.1.1 q.1.2 q.2) :=
    (kcInsN_cont (n := p + 1) i).comp
      (Continuous.prodMk continuous_fst.fst
        ((kcInsN_cont (n := p) j').comp (Continuous.prodMk continuous_fst.snd continuous_snd)))
  have hF : StronglyMeasurable (Function.uncurry (fun (q : ℝ³ × ℝ³) (r2 : X p) =>
      aP ℓ i (aP ℓ j Φ) (rest2 i j' r2) * aQ ℓ j (aQ ℓ i Φ) (ins2 i j' q.1 q.2 r2))) :=
    ((hAc.comp continuous_snd).stronglyMeasurable).mul (hQjc.comp hinsQ).stronglyMeasurable
  have hmain := hF.integral_prod_right (ν := (volume : Measure (X p)).restrict (abox p ℓ))
  have hfun : (fun q : ℝ³ × ℝ³ => ∫ r2, aP ℓ i (aP ℓ j Φ) (rest2 i j' r2)
        * aQ ℓ j (aQ ℓ i Φ) (ins2 i j' q.1 q.2 r2)
        ∂((volume : Measure (X p)).restrict (abox p ℓ)))
      = fun q : ℝ³ × ℝ³ => pairFibreFun ℓ Φ i j q.1 q.2 := by
    funext q
    simp only [pairFibreFun, dif_pos hij, ← hj'def]
  rwa [hfun] at hmain

/-- Strong measurability of the pair density (for continuous `Φ`). -/
lemma stronglyMeasurable_pairFibreDens {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2))
    (hij : i ≠ j) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    StronglyMeasurable (pairFibreDens ℓ Φ i j) := by
  have _ : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  have hcs : Continuous (chiScale ℓ) := chiScale_continuous ℓ
  have hpair := stronglyMeasurable_pairFibreFun hℓ i j hij hΦc
  have hF : StronglyMeasurable (Function.uncurry (fun (u : ℝ³) (z : ℝ³) =>
      chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z)) := by
    have h1 : StronglyMeasurable (fun q : ℝ³ × ℝ³ => chiScale ℓ (q.2 + q.1)) :=
      (hcs.comp (continuous_snd.add continuous_fst)).stronglyMeasurable
    have h2 : StronglyMeasurable (fun q : ℝ³ × ℝ³ => chiScale ℓ q.2) :=
      (hcs.comp continuous_snd).stronglyMeasurable
    have h3 : StronglyMeasurable (fun q : ℝ³ × ℝ³ => pairFibreFun ℓ Φ i j (q.2 + q.1) q.2) :=
      hpair.comp_measurable ((continuous_snd.add continuous_fst).prodMk continuous_snd).measurable
    change StronglyMeasurable (fun q : ℝ³ × ℝ³ =>
      chiScale ℓ (q.2 + q.1) * chiScale ℓ q.2 * pairFibreFun ℓ Φ i j (q.2 + q.1) q.2)
    exact (h1.mul h2).mul h3
  have hmain := hF.integral_prod_right (ν := (volume : Measure ℝ³).restrict (acube ℓ))
  have hfun : (fun u : ℝ³ => ∫ z, chiScale ℓ (z + u) * chiScale ℓ z
        * pairFibreFun ℓ Φ i j (z + u) z ∂((volume : Measure ℝ³).restrict (acube ℓ)))
      = pairFibreDens ℓ Φ i j := by
    funext u
    rfl
  rwa [hfun] at hmain

/-- **Integrability of the pair density**: bounded and compactly supported. -/
lemma integrable_pairFibreDens {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B)
    (hΦB : ∀ x ∈ abox (p + 2) ℓ, |Φ x| ≤ B) :
    Integrable (pairFibreDens ℓ Φ i j) := by
  have hC : 0 ≤ chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3 := by positivity
  have h2ℓ : (0 : ℝ) ≤ 2 * ℓ := by linarith
  have hbound : Integrable (fun u : ℝ³ => Set.indicator (acube (2 * ℓ))
      (fun _ => chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3) u) :=
    (integrableOn_const (μ := (volume : Measure ℝ³)) (s := acube (2 * ℓ))
      (C := chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3)
      (hs := ne_of_lt (acube_lt_top (2 * ℓ) h2ℓ))).integrable_indicator
      (acube_measurable (2 * ℓ))
  refine Integrable.mono' hbound
    (stronglyMeasurable_pairFibreDens hℓ i j hij hΦc).aestronglyMeasurable ?_
  filter_upwards with u
  by_cases hu : u ∈ acube (2 * ℓ)
  · rw [Set.indicator_of_mem hu, Real.norm_eq_abs]
    exact abs_pairFibreDens_le hℓ i j hij hΦc hB hΦB u
  · rw [pairFibreDens_eq_zero_of_notMem hℓ Φ i j hu, Set.indicator_of_notMem hu]
    simp

/-- **`L²` membership of the pair density.** -/
lemma memLp_pairFibreDens {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B)
    (hΦB : ∀ x ∈ abox (p + 2) ℓ, |Φ x| ≤ B) :
    MemLp (fun u => ((pairFibreDens ℓ Φ i j u : ℝ) : ℂ)) 2 volume := by
  have hC : 0 ≤ chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3 := by positivity
  have h2ℓ : (0 : ℝ) ≤ 2 * ℓ := by linarith
  have hsm := stronglyMeasurable_pairFibreDens hℓ i j hij hΦc
  rw [memLp_two_iff_integrable_sq_norm (hsm.aemeasurable.complex_ofReal.aestronglyMeasurable)]
  have hbound : Integrable (fun u : ℝ³ => Set.indicator (acube (2 * ℓ))
      (fun _ => (chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3) ^ 2) u) :=
    (integrableOn_const (μ := (volume : Measure ℝ³)) (s := acube (2 * ℓ))
      (C := (chiSup ^ 2 * (4 * B ^ 2 * ℓ ^ (3 * p)) * ℓ ^ 3) ^ 2)
      (hs := ne_of_lt (acube_lt_top (2 * ℓ) h2ℓ))).integrable_indicator
      (acube_measurable (2 * ℓ))
  have hmeas : AEStronglyMeasurable
      (fun u => ‖((pairFibreDens ℓ Φ i j u : ℝ) : ℂ)‖ ^ 2) volume := by
    refine ((hsm.norm).pow 2).aestronglyMeasurable.congr ?_
    filter_upwards with u
    simp [Complex.norm_real]
  refine Integrable.mono' hbound hmeas ?_
  filter_upwards with u
  by_cases hu : u ∈ acube (2 * ℓ)
  · rw [Set.indicator_of_mem hu, Real.norm_of_nonneg (sq_nonneg _)]
    have hb := abs_pairFibreDens_le hℓ i j hij hΦc hB hΦB u
    have h1 : ‖((pairFibreDens ℓ Φ i j u : ℝ) : ℂ)‖ ^ 2 = |pairFibreDens ℓ Φ i j u| ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  · rw [pairFibreDens_eq_zero_of_notMem hℓ Φ i j hu, Set.indicator_of_notMem hu]
    simp

/-! ## 5. Compact support of the pair density -/

/-- **The pair density is compactly supported** (inside `acube (2ℓ)`). -/
lemma hasCompactSupport_pairFibreDens {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : X (p + 2) → ℝ) (i j : Fin (p + 2)) :
    HasCompactSupport (pairFibreDens ℓ Φ i j) :=
  HasCompactSupport.intro (acube_compact (by linarith : (0:ℝ) < 2 * ℓ))
    (fun u hu => pairFibreDens_eq_zero_of_notMem hℓ Φ i j hu)

/-! ## 6. Smoothness of the insertion maps (for the `ContDiff` chain) -/

/-- The insertion map `kcInsN n i` is smooth. -/
lemma contDiff_kcInsN {n : ℕ} (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (fun q : ℝ³ × X n => kcInsN n i q) := by
  rw [contDiff_pi]
  intro j
  by_cases hj : j = i
  · subst hj
    have h1 : (fun q : ℝ³ × X n => kcInsN n j q j) = fun q => q.1 := by
      funext q
      exact kc_insN_apply_same n j q.1 q.2
    rw [h1]
    fun_prop
  · have h2 : (fun q : ℝ³ × X n => kcInsN n i q j) = fun q => q.2 (sucAboveInv i j (Ne.symm hj)) := by
      funext q
      conv_lhs => rw [← succAbove_sucAboveInv i j (Ne.symm hj)]
      exact kc_insN_apply_succ n i q.1 q.2 (sucAboveInv i j (Ne.symm hj))
    rw [h2]
    fun_prop

/-- Smoothness of the two-slot insertion `ins2` in all its variables. -/
lemma contDiff_ins2 {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    ContDiff ℝ ∞ (fun q : (ℝ³ × ℝ³) × X p => ins2 i j' q.1.1 q.1.2 q.2) := by
  have h1 : ContDiff ℝ ∞ (fun q : (ℝ³ × ℝ³) × X p =>
      ((q.1.1, kcInsN p j' (q.1.2, q.2)) : ℝ³ × X (p + 1))) :=
    ContDiff.prodMk contDiff_fst.fst
      ((contDiff_kcInsN j').comp (ContDiff.prodMk contDiff_fst.snd contDiff_snd))
  exact (contDiff_kcInsN i).comp h1

/-- Smoothness of the two-slot rest map `rest2`. -/
lemma contDiff_rest2 {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1)) :
    ContDiff ℝ ∞ (fun r2 : X p => rest2 i j' r2) := by
  have h1 : ContDiff ℝ ∞ (fun r2 : X p => ((0 : ℝ³), kcInsN p j' ((0 : ℝ³), r2))) :=
    ContDiff.prodMk contDiff_const
      ((contDiff_kcInsN j').comp (ContDiff.prodMk contDiff_const contDiff_id))
  have h2 := (contDiff_kcInsN i).comp h1
  have hgoal : (fun r2 : X p => rest2 i j' r2)
      = (fun r2 : X p => kcInsN (p + 1) i ((0 : ℝ³), kcInsN p j' ((0 : ℝ³), r2))) := by
    funext r2
    rfl
  rw [hgoal]
  exact h2

/-- Smoothness of the slot-update map `x ↦ Function.update x i y`. -/
lemma contDiff_update_coord {N : ℕ} (i : Fin N) :
    ContDiff ℝ ∞ (fun q : X N × ℝ³ => Function.update q.1 i q.2) := by
  rw [contDiff_pi]
  intro j
  by_cases hj : j = i
  · subst hj
    have h1 : (fun q : X N × ℝ³ => Function.update q.1 j q.2 j) = fun q => q.2 := by
      funext q
      simp
    rw [h1]
    fun_prop
  · have h1 : (fun q : X N × ℝ³ => Function.update q.1 i q.2 j) = fun q => q.1 j := by
      funext q
      simp [hj]
    rw [h1]
    fun_prop

/-- **Smoothness of `aP`** (for smooth `Φ`). -/
lemma contDiff_aP {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (aP ℓ i Φ) := by
  set F : X N → ℝ³ → ℝ := fun x y => Φ (Function.update x i y) with hFdef
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := hΦ.comp (contDiff_update_coord i)
  have h := Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (n := (⊤ : ℕ∞))
    (acube_compact hℓ) hF
  have hgoal : (aP ℓ i Φ) = fun x : X N => (1 / ℓ ^ 3) • ∫ y in acube ℓ, Φ (Function.update x i y) := by
    funext x
    rfl
  rw [hgoal]
  simpa only [hFdef] using h.const_smul (1 / ℓ ^ 3)

/-- **Smoothness of `aQ`** (for smooth `Φ`). -/
lemma contDiff_aQ {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (aQ ℓ i Φ) := by
  unfold aQ
  exact hΦ.sub (contDiff_aP hℓ i hΦ)


/-- **Joint smoothness of the peeled pair fibre** (for smooth `Φ`). -/
lemma contDiff_pairFibreFun {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (Function.uncurry (fun y z : ℝ³ => pairFibreFun ℓ Φ i j y z)) := by
  set j' := sucAboveInv i j hij with hj'def
  have hQc : ContDiff ℝ ∞ (aQ ℓ j (aQ ℓ i Φ)) := contDiff_aQ hℓ j (contDiff_aQ hℓ i hΦ)
  have hAc : ContDiff ℝ ∞ (fun r2 : X p => aP ℓ i (aP ℓ j Φ) (rest2 i j' r2)) :=
    (contDiff_aP hℓ i (contDiff_aP hℓ j hΦ)).comp (contDiff_rest2 i j')
  have hF : ContDiff ℝ ∞ (Function.uncurry (fun (q : ℝ³ × ℝ³) (r2 : X p) =>
      aP ℓ i (aP ℓ j Φ) (rest2 i j' r2) * aQ ℓ j (aQ ℓ i Φ) (ins2 i j' q.1 q.2 r2))) := by
    have h1 : ContDiff ℝ ∞ (fun q : (ℝ³ × ℝ³) × X p =>
        aP ℓ i (aP ℓ j Φ) (rest2 i j' q.2) * aQ ℓ j (aQ ℓ i Φ) (ins2 i j' q.1.1 q.1.2 q.2)) :=
      (hAc.comp contDiff_snd).mul (hQc.comp (contDiff_ins2 i j'))
    change ContDiff ℝ ∞ (fun q : (ℝ³ × ℝ³) × X p =>
      aP ℓ i (aP ℓ j Φ) (rest2 i j' q.2) * aQ ℓ j (aQ ℓ i Φ) (ins2 i j' q.1.1 q.1.2 q.2))
    exact h1
  have h := Commons.Analysis.Calculus.contDiff_setIntegral_isCompact_pi (d := p) (m := (⊤ : ℕ∞))
    (F := fun (q : ℝ³ × ℝ³) (r2 : X p) =>
      aP ℓ i (aP ℓ j Φ) (rest2 i j' r2) * aQ ℓ j (aQ ℓ i Φ) (ins2 i j' q.1 q.2 r2))
    (abox_compact p hℓ) hF
  have hgoal : (Function.uncurry (fun y z : ℝ³ => pairFibreFun ℓ Φ i j y z))
      = fun q : (ℝ³ × ℝ³) => ∫ r2 in abox p ℓ,
          aP ℓ i (aP ℓ j Φ) (rest2 i j' r2) * aQ ℓ j (aQ ℓ i Φ) (ins2 i j' q.1 q.2 r2) := by
    funext q
    simp only [Function.uncurry, pairFibreFun, dif_pos hij, ← hj'def]
  rw [hgoal]
  exact h

/-- **Smoothness of the pair density** (for smooth `Φ`). -/
lemma contDiff_pairFibreDens {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (pairFibreDens ℓ Φ i j) := by
  have hχ : ContDiff ℝ ∞ (chiScale ℓ) := chiScale_contDiff hℓ.ne'
  have hpair := contDiff_pairFibreFun hℓ i j hij hΦ
  have hF : ContDiff ℝ ∞ (Function.uncurry (fun (u : ℝ³) (z : ℝ³) =>
      chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z)) := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ³ × ℝ³ => chiScale ℓ (q.2 + q.1)) :=
      (hχ.comp (contDiff_snd.add contDiff_fst))
    have h2 : ContDiff ℝ ∞ (fun q : ℝ³ × ℝ³ => chiScale ℓ q.2) := hχ.comp contDiff_snd
    have h3 : ContDiff ℝ ∞ (fun q : ℝ³ × ℝ³ => pairFibreFun ℓ Φ i j (q.2 + q.1) q.2) :=
      hpair.comp (ContDiff.prodMk (contDiff_snd.add contDiff_fst) contDiff_snd)
    change ContDiff ℝ ∞ (fun q : ℝ³ × ℝ³ =>
      chiScale ℓ (q.2 + q.1) * chiScale ℓ q.2 * pairFibreFun ℓ Φ i j (q.2 + q.1) q.2)
    exact (h1.mul h2).mul h3
  have h := Commons.Analysis.Calculus.contDiff_setIntegral_isCompact (n := (⊤ : ℕ∞))
    (acube_compact hℓ) hF
  have hgoal : (pairFibreDens ℓ Φ i j)
      = fun u : ℝ³ => ∫ z in acube ℓ,
          chiScale ℓ (z + u) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + u) z := by
    funext u
    rfl
  rw [hgoal]
  exact h

/-! ## 7. The momentum (anti-diagonal) form of the pair term

This is the D1 step (i) punchline: the one-sided Plancherel formula
(`Commons.Analysis.Fourier.plancherel_one_sided_schwartz`) applied to the integrable
kernel `W₁` and the Schwartz function `pairFibreDens` converts the relative-coordinate
`u`-integral into the momentum integral against `𝓕W₁`, which is exactly the form in
which the anti-diagonal `(p,−p)` Bogoliubov pairing of FS `lm:appbogolubov` lives. -/

/-- **The momentum form of the pair term.**  For `Φ` smooth and `W` integrable,

    pairRelTerm ℓ Φ W i j = ∫ q, 𝓕W(q)·𝓕(pairFibreDens ℓ Φ i j)(−q) dq

(Mathlib's `e^{−2πi⟪x,q⟫}` convention; substituting `p = 2πq` recovers FS's
`(2π)^{−3}∫Ŵ₁(p)Ĝ(−p)dp`). -/
theorem pairRelTerm_eq_fourier_integral {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin (p + 2))
    (hij : i ≠ j) {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {W : ℝ³ → ℝ}
    (hW : Integrable W) :
    ((pairRelTerm ℓ Φ W i j : ℝ) : ℂ)
      = ∫ q, FourierTransform.fourier (fun x => (W x : ℂ)) q *
          FourierTransform.fourier (fun x => ((pairFibreDens ℓ Φ i j x : ℝ) : ℂ)) (-q) := by
  set G : ℝ³ → ℂ := fun x => ((pairFibreDens ℓ Φ i j x : ℝ) : ℂ) with hGdef
  have hGcd : ContDiff ℝ ∞ G :=
    Complex.ofRealCLM.contDiff.comp (contDiff_pairFibreDens hℓ i j hij hΦ)
  have hGsupp : HasCompactSupport G := by
    have := (hasCompactSupport_pairFibreDens hℓ Φ i j).comp_left
      (g := fun z : ℝ => (z : ℂ)) (by simp)
    simpa only [hGdef, Function.comp_def] using this
  set g : SchwartzMap ℝ³ ℂ := hGsupp.toSchwartzMap hGcd with hgdef
  have hmain := Commons.Analysis.Fourier.plancherel_one_sided_schwartz
    (f := fun x : ℝ³ => (W x : ℂ)) hW.ofReal g
  rw [pairRelTerm_eq_integral_pairFibreDens hℓ Φ W hij]
  have hcast0 : ((∫ u, W u * pairFibreDens ℓ Φ i j u : ℝ) : ℂ)
      = ∫ x, ((W x * pairFibreDens ℓ Φ i j x : ℝ) : ℂ) :=
    (integral_ofReal (𝕜 := ℂ)
      (f := fun u : ℝ³ => W u * pairFibreDens ℓ Φ i j u)).symm
  have hcast : ((∫ u, W u * pairFibreDens ℓ Φ i j u : ℝ) : ℂ)
      = ∫ x, (W x : ℂ) * ((pairFibreDens ℓ Φ i j x : ℝ) : ℂ) := by
    refine hcast0.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.ofReal_mul]
  rw [hcast]
  have hgm : (g : ℝ³ → ℂ) = G := rfl
  rw [hgm] at hmain
  simpa only [hGdef] using hmain

/-- **The whole two-body pairing word `q4PairWord` in momentum form** (D1 step (i)).

    q4PairWord = Σ_{i≠j} ∫ q, 𝓕W₁(q)·𝓕(pairFibreDens ℓ Φ i j)(−q) dq ,   W₁ = wScaled ℓ (g₀ v h)

assembling `q4PairWord_eq_relDens_auto` (relative-coordinate decomposition) with the
one-sided Plancherel identity above.  All hypotheses beyond `ContDiff ℝ ∞ Φ` are the
dilute-regime support conditions of the kernel. -/
theorem q4PairWord_eq_fourier_integral {p : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * chiR0) {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : X (p + 2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ((q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) : ℝ) : ℂ)
      = ∑ q ∈ pairSet (p + 2), ∫ u,
          FourierTransform.fourier (fun x => (wScaled ℓ (g0 v h) x : ℂ)) u *
          FourierTransform.fourier (fun x => ((pairFibreDens ℓ Φ q.1 q.2 x : ℝ) : ℂ)) (-u) := by
  rw [q4PairWord_eq_relDens_auto hℓ hR hRℓ hv_supp h hΦ.continuous]
  push_cast
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
  exact pairRelTerm_eq_fourier_integral (W := wScaled ℓ (g0 v h)) hℓ q.1 q.2 hqne hΦ
    (wScaled_integrable_ae hℓ hR.le hRℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h))

end BoseGases
end Submission
