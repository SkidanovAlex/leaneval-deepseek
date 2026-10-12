import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.NeumannBasics
import Submission.ShiftInt
import Submission.SubaddVol
import Submission.Superadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Neumann ground states are superadditive in the particle number

The mirror of the Dirichlet `Superadd.boxEnergy_superadd`: for `0 < L`,
`0 ≤ v`, `MemLp v 1`,

    eNeu (n₁ + n₂) L v ≥ eNeu n₁ L v + eNeu n₂ L v        (eNeu_superadd)

This is the per-cell ingredient of the count-distribution optimisation
(`Submission.CountDistribution` uses the abstract superadditive-sequence
core).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real ENNReal BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Slices of smooth functions along the block split -/

/-- The first-block slice of a smooth `(N1+N2)`-particle function at frozen `w`. -/
noncomputable def es_slice1 (N1 N2 : ℕ) (Φ : X (N1 + N2) → ℝ) (w : X N2) : X N1 → ℝ :=
  fun u => Φ (mergeBlock N1 N2 (u, w))

/-- The second-block slice of a smooth `(N1+N2)`-particle function at frozen `u`. -/
noncomputable def es_slice2 (N1 N2 : ℕ) (Φ : X (N1 + N2) → ℝ) (u : X N1) : X N2 → ℝ :=
  fun w => Φ (mergeBlock N1 N2 (u, w))

lemma es_merge_add_first (N1 N2 : ℕ) (u : X N1) (w : X N2) :
    mergeBlock N1 N2 (u, w) = sliceL N1 N2 u + mergeBlock N1 N2 (0, w) := by
  calc
    mergeBlock N1 N2 (u, w) = combine u w := by rfl
    _ = combine u (0 : X N2) + combine (0 : X N1) w := by
      have h := combine_add (N1 := N1) (N2 := N2) u (0 : X N1) (0 : X N2) w
      have hu : u + (0 : X N1) = u := by simp
      have hw : (0 : X N2) + w = w := by simp
      rw [hu, hw] at h
      exact h
    _ = sliceL N1 N2 u + mergeBlock N1 N2 (0, w) := by
      rw [sliceL_apply]
      rw [show combine (0 : X N1) w = mergeBlock N1 N2 (0, w) by rfl]

lemma es_merge_add_second (N1 N2 : ℕ) (u : X N1) (w : X N2) :
    mergeBlock N1 N2 (u, w) = sliceR N1 N2 w + mergeBlock N1 N2 (u, 0) := by
  calc
    mergeBlock N1 N2 (u, w) = combine u w := by rfl
    _ = combine (0 : X N1) w + combine u (0 : X N2) := by
      have h := combine_add (N1 := N1) (N2 := N2) (0 : X N1) u w (0 : X N2)
      have hu : (0 : X N1) + u = u := by simp
      have hw : w + (0 : X N2) = w := by simp
      rw [hu, hw] at h
      exact h
    _ = sliceR N1 N2 w + mergeBlock N1 N2 (u, 0) := by
      rw [sliceR_apply]
      rw [show combine u (0 : X N2) = mergeBlock N1 N2 (u, 0) by rfl]

lemma es_hasFDerivAt_slice1_map (N1 N2 : ℕ) (w : X N2) (u : X N1) :
    HasFDerivAt (fun u' : X N1 => mergeBlock N1 N2 (u', w)) (sliceL N1 N2) u := by
  rw [show (fun u' : X N1 => mergeBlock N1 N2 (u', w)) = fun u' : X N1 =>
      sliceL N1 N2 u' + mergeBlock N1 N2 (0, w) by
    funext u'; exact es_merge_add_first N1 N2 u' w]
  exact ((sliceL N1 N2).hasFDerivAt.add_const (mergeBlock N1 N2 (0, w)))

lemma es_hasFDerivAt_slice2_map (N1 N2 : ℕ) (u : X N1) (w : X N2) :
    HasFDerivAt (fun w' : X N2 => mergeBlock N1 N2 (u, w')) (sliceR N1 N2) w := by
  rw [show (fun w' : X N2 => mergeBlock N1 N2 (u, w')) = fun w' : X N2 =>
      sliceR N1 N2 w' + mergeBlock N1 N2 (u, 0) by
    funext w'; exact es_merge_add_second N1 N2 u w']
  exact ((sliceR N1 N2).hasFDerivAt.add_const (mergeBlock N1 N2 (u, 0)))

lemma es_contDiff_slice1_map (N1 N2 : ℕ) (w : X N2) :
    ContDiff ℝ ∞ (fun u : X N1 => mergeBlock N1 N2 (u, w)) := by
  rw [show (fun u : X N1 => mergeBlock N1 N2 (u, w)) = fun u : X N1 =>
      sliceL N1 N2 u + mergeBlock N1 N2 (0, w) by
    funext u; exact es_merge_add_first N1 N2 u w]
  exact ContDiff.add (sliceL N1 N2).contDiff contDiff_const

lemma es_contDiff_slice2_map (N1 N2 : ℕ) (u : X N1) :
    ContDiff ℝ ∞ (fun w : X N2 => mergeBlock N1 N2 (u, w)) := by
  rw [show (fun w : X N2 => mergeBlock N1 N2 (u, w)) = fun w : X N2 =>
      sliceR N1 N2 w + mergeBlock N1 N2 (u, 0) by
    funext w; exact es_merge_add_second N1 N2 u w]
  exact ContDiff.add (sliceR N1 N2).contDiff contDiff_const

lemma es_slice1_contDiff {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (w : X N2) : ContDiff ℝ ∞ (es_slice1 N1 N2 Φ w) := by
  unfold es_slice1
  change ContDiff ℝ ∞ (Φ ∘ (fun u : X N1 => mergeBlock N1 N2 (u, w)))
  exact ContDiff.comp hΦ (es_contDiff_slice1_map N1 N2 w)

lemma es_slice2_contDiff {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (u : X N1) : ContDiff ℝ ∞ (es_slice2 N1 N2 Φ u) := by
  unfold es_slice2
  change ContDiff ℝ ∞ (Φ ∘ (fun w : X N2 => mergeBlock N1 N2 (u, w)))
  exact ContDiff.comp hΦ (es_contDiff_slice2_map N1 N2 u)

lemma es_fderiv_slice1 {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (w : X N2) (u : X N1) (d : X N1) :
    fderiv ℝ (es_slice1 N1 N2 Φ w) u d =
      fderiv ℝ Φ (mergeBlock N1 N2 (u, w)) (sliceL N1 N2 d) := by
  have hAw := es_hasFDerivAt_slice1_map N1 N2 w u
  have hd : DifferentiableAt ℝ Φ (mergeBlock N1 N2 (u, w)) :=
    hΦ.differentiable (by norm_num) (mergeBlock N1 N2 (u, w))
  have hcomp := hd.hasFDerivAt.comp u hAw
  have hfd := hcomp.fderiv
  change fderiv ℝ (Φ ∘ (fun u' : X N1 => mergeBlock N1 N2 (u', w))) u d =
      fderiv ℝ Φ (mergeBlock N1 N2 (u, w)) (sliceL N1 N2 d)
  rw [hfd]
  rfl

lemma es_fderiv_slice2 {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (u : X N1) (w : X N2) (d : X N2) :
    fderiv ℝ (es_slice2 N1 N2 Φ u) w d =
      fderiv ℝ Φ (mergeBlock N1 N2 (u, w)) (sliceR N1 N2 d) := by
  have hAw := es_hasFDerivAt_slice2_map N1 N2 u w
  have hd : DifferentiableAt ℝ Φ (mergeBlock N1 N2 (u, w)) :=
    hΦ.differentiable (by norm_num) (mergeBlock N1 N2 (u, w))
  have hcomp := hd.hasFDerivAt.comp w hAw
  have hfd := hcomp.fderiv
  change fderiv ℝ (Φ ∘ (fun w' : X N2 => mergeBlock N1 N2 (u, w'))) w d =
      fderiv ℝ Φ (mergeBlock N1 N2 (u, w)) (sliceR N1 N2 d)
  rw [hfd]
  rfl

/-- The embedded first-block coordinate direction is the big coordinate direction. -/
lemma es_sliceL_kcDir {N1 N2 : ℕ} (i : Fin N1) (k : Fin 3) :
    sliceL N1 N2 (kcDir N1 i k) = kcDir (N1 + N2) (Fin.castAdd N2 i) k := by
  rw [show sliceL N1 N2 (kcDir N1 i k) = mergeBlock N1 N2 (kcDir N1 i k, 0) by rfl]
  unfold mergeBlock kcDir
  funext j
  cases h : finSplit N1 N2 j with
  | inl ii =>
      have hj : j = Fin.castAdd N2 ii := by
        have h1 : finSplit N1 N2 j = finSplit N1 N2 (Fin.castAdd N2 ii) := by
          rw [h, finSplit_castAdd]
        exact (finSplit N1 N2).injective h1
      rw [hj]
      ext m
      simp
      by_cases heq : ii = i
      · subst ii
        simp
      · simp [heq]
  | inr jj =>
      have hj : j = Fin.natAdd N1 jj := by
        have h1 : finSplit N1 N2 j = finSplit N1 N2 (Fin.natAdd N1 jj) := by
          rw [h, finSplit_natAdd]
        exact (finSplit N1 N2).injective h1
      rw [hj]
      ext m
      simp
      have hne : Fin.castAdd N2 i ≠ Fin.natAdd N1 jj := by
        intro hc
        have hv : (Fin.castAdd N2 i).val < N1 := by simp
        have hv' : (Fin.natAdd N1 jj).val ≥ N1 := by simp
        rw [hc] at hv
        omega
      rw [Function.update_of_ne hne.symm]
      simp

/-- The embedded second-block coordinate direction is the big coordinate direction. -/
lemma es_sliceR_kcDir {N1 N2 : ℕ} (j : Fin N2) (k : Fin 3) :
    sliceR N1 N2 (kcDir N2 j k) = kcDir (N1 + N2) (Fin.natAdd N1 j) k := by
  rw [show sliceR N1 N2 (kcDir N2 j k) = mergeBlock N1 N2 (0, kcDir N2 j k) by rfl]
  unfold mergeBlock kcDir
  funext i
  cases h : finSplit N1 N2 i with
  | inl ii =>
      have hi : i = Fin.castAdd N2 ii := by
        have h1 : finSplit N1 N2 i = finSplit N1 N2 (Fin.castAdd N2 ii) := by
          rw [h, finSplit_castAdd]
        exact (finSplit N1 N2).injective h1
      rw [hi]
      ext m
      simp
      have hne : Fin.natAdd N1 j ≠ Fin.castAdd N2 ii := by
        intro hc
        have hv : (Fin.castAdd N2 ii).val < N1 := by simp
        have hv' : (Fin.natAdd N1 j).val ≥ N1 := by simp
        rw [hc] at hv'
        omega
      rw [Function.update_of_ne hne.symm]
      simp
  | inr jj =>
      have hi : i = Fin.natAdd N1 jj := by
        have h1 : finSplit N1 N2 i = finSplit N1 N2 (Fin.natAdd N1 jj) := by
          rw [h, finSplit_natAdd]
        exact (finSplit N1 N2).injective h1
      rw [hi]
      ext m
      simp
      by_cases heq : jj = j
      · subst jj
        simp
      · simp [heq]

/-! ## The box energy functionals of a smooth (not necessarily admissible) function -/

/-- Kinetic box functional of a smooth function (matches `kinNeu` on `CNeu` states). -/
noncomputable def es_kinF (N : ℕ) (L : ℝ) (f : X N → ℝ) : ℝ :=
  ∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2

/-- Interaction box functional of a smooth function (matches `intNeu` on `CNeu` states). -/
noncomputable def es_intF (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (f : X N → ℝ) : ℝ :=
  ∫ x in box N L, (f x) ^ 2 * intPairSum N v x

/-- The Neumann ground-state energy is a lower bound for the box quotient of any
smooth function (zero-norm case is trivial; positive-norm case uses
`eNeu_le_quot_ofFun`). -/
lemma es_eNeu_mul_le {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) :
    eNeu N L v * (∫ x in box N L, (f x) ^ 2) ≤ es_kinF N L f + es_intF N L v f := by
  by_cases hz : (∫ x in box N L, (f x) ^ 2) = 0
  · rw [hz, mul_zero]
    unfold es_kinF es_intF
    have hk : 0 ≤ ∫ x in box N L, ∑ i : Fin N, ∑ k : Fin 3,
        (fderiv ℝ f x (kcDir N i k)) ^ 2 := by
      exact integral_nonneg (fun x =>
        Finset.sum_nonneg (fun i _ =>
          Finset.sum_nonneg (fun k _ => sq_nonneg (fderiv ℝ f x (kcDir N i k)))))
    have hi : 0 ≤ ∫ x in box N L, (f x) ^ 2 * intPairSum N v x := by
      exact integral_nonneg (fun x => mul_nonneg (sq_nonneg (f x)) (by
        unfold intPairSum
        exact Finset.sum_nonneg (fun p _ => hv (x p.1 - x p.2))))
    exact add_nonneg hk hi
  · have hpos : 0 < ∫ x in box N L, (f x) ^ 2 :=
      lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (f x))) (Ne.symm hz)
    have hne : f ≠ 0 := by
      intro hf0
      apply hz
      simp [hf0]
    have hq := eNeu_le_quot_ofFun (N := N) (L := L) (v := v) hv hf hne hpos
    have hmul := (le_div_iff₀ hpos).mp hq
    change eNeu N L v * (∫ x in box N L, (f x) ^ 2) ≤ es_kinF N L f + es_intF N L v f
    rw [show es_kinF N L f = kinNeu N L (CNeu.ofFun hf hne hpos) by
      unfold es_kinF kinNeu CNeu.ofFun; rfl,
      show es_intF N L v f = intNeu N L v (CNeu.ofFun hf hne hpos) by
      unfold es_intF intNeu intPairSum CNeu.ofFun; rfl]
    exact hmul

/-! ## Integrability of the kinetic and interaction integrands over the box -/

/-- A continuous function is integrable on the box. -/
lemma es_integrableOn_cont {N : ℕ} {L : ℝ} (hL : 0 < L) {f : X N → ℝ}
    (hcont : Continuous f) : IntegrableOn f (box N L) volume := by
  exact hcont.continuousOn.integrableOn_compact (box_compact hL)

/-- The squared values of a continuous function are bounded on the box. -/
lemma es_exists_bound_sq_box {N : ℕ} {L : ℝ} (hL : 0 < L) {f : X N → ℝ}
    (hf : Continuous f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ box N L, (f x) ^ 2 ≤ M := by
  have hcontOn : ContinuousOn (fun x : X N => (f x) ^ 2) (box N L) := hf.continuousOn.pow 2
  rcases IsCompact.exists_bound_of_continuousOn (box_compact hL) hcontOn with ⟨M0, hM0⟩
  refine ⟨max M0 0, le_max_right M0 0, ?_⟩
  intro x hx
  have hb := hM0 x hx
  have hn : 0 ≤ (f x) ^ 2 := sq_nonneg _
  have hsq : (f x) ^ 2 ≤ M0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hn] at hb
    exact hb
  exact le_trans hsq (le_max_left M0 0)

/-- The box-integral norm (squared) of a continuous function is integrable in the box
sense (helper). -/
lemma es_sq_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L) {f : X N → ℝ}
    (hcont : Continuous f) : IntegrableOn (fun x : X N => (f x) ^ 2) (box N L) volume := by
  exact es_integrableOn_cont hL (hcont.pow 2)


/-- The integrand `f²·w(xᵢ−xⱼ)` is integrable over the box (measurable `w` of finite
`L¹`-norm). -/
lemma es_sq_w_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L) {w : ℝ³ → ℝ}
    (hwm : Measurable w) (hfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < (⊤ : ℝ≥0∞)) {f : X N → ℝ}
    (hfcont : Continuous f) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : X N => (f x)^2 * w (x i - x j)) (box N L) volume := by
  let μ_box : Measure (X N) := volume.restrict (box N L)
  rcases es_exists_bound_sq_box hL hfcont with ⟨M, hM0, hM⟩
  have hw : IntegrableOn (fun x : X N => |w (x i - x j)|) (box N L) volume :=
    integrableOn_abs_pair_of_measurable hL hwm hfin i j hij
  have hmeas : AEStronglyMeasurable
      (fun x : X N => (f x)^2 * w (x i - x j)) μ_box := by
    have hw' : Measurable (fun x : X N => w (x i - x j)) := by
      fun_prop
    have hf2 : Measurable (fun x : X N => (f x)^2) := by
      exact hfcont.measurable.pow (measurable_const : Measurable (fun _ : X N => (2 : ℕ)))
    exact (hf2.mul hw').aestronglyMeasurable
  refine Integrable.mono' (μ := μ_box)
    (f := fun x : X N => (f x)^2 * w (x i - x j))
    (g := fun x : X N => M * |w (x i - x j)|) ?_ hmeas ?_
  · exact (hw.integrable.const_mul M)
  · rw [ae_iff]
    apply le_antisymm
    · have hsub : {x : X N | ¬ ‖(f x)^2 * w (x i - x j)‖ ≤ M * |w (x i - x j)|}
          ⊆ (box N L)ᶜ := by
        intro x hx hbox
        apply hx
        have hf2 : (f x)^2 ≤ M := hM x hbox
        calc
          ‖(f x)^2 * w (x i - x j)‖ = |(f x)^2| * |w (x i - x j)| := by
            rw [Real.norm_eq_abs, abs_mul]
          _ ≤ M * |w (x i - x j)| := by
            exact mul_le_mul (by simpa [abs_of_nonneg (sq_nonneg (f x))] using hf2) le_rfl
              (abs_nonneg _) hM0
      calc
        μ_box {x : X N | ¬ ‖(f x)^2 * w (x i - x j)‖ ≤ M * |w (x i - x j)|}
            ≤ μ_box (box N L)ᶜ := measure_mono hsub
        _ = 0 := by
          change (volume.restrict (box N L)) (box N L)ᶜ = 0
          rw [Measure.restrict_apply (box_measurable N L).compl]
          simp
    · exact bot_le

/-- The integrand `f²·v(xᵢ−xⱼ)` is integrable over the box for `v ∈ L¹`. -/
lemma es_sq_v_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ} (hv1 : MemLp v 1)
    {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : X N => (f x)^2 * v (x i - x j)) (box N L) volume := by
  have hvInt : Integrable v := (memLp_one_iff_integrable.mp hv1)
  have hvae : AEMeasurable v := hvInt.aemeasurable
  let w : ℝ³ → ℝ := AEMeasurable.mk v hvae
  have hwm : Measurable w := AEMeasurable.measurable_mk hvae
  have hvw : v =ᵐ[volume] w := AEMeasurable.ae_eq_mk hvae
  have hwInt : Integrable w := hvInt.congr hvw
  have hwfin : (∫⁻ y : ℝ³, ‖w y‖ₑ) < (⊤ : ℝ≥0∞) := hwInt.hasFiniteIntegral
  have hmain : IntegrableOn (fun x : X N => (f x)^2 * w (x i - x j))
      (box N L) volume := es_sq_w_integrableOn hL hwm hwfin hf.continuous hij
  have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
    rw [← ae_iff]
    exact hvw
  rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with
    ⟨t, hNt, htm, ht0⟩
  have hpre : (volume : Measure (X N)).restrict (box N L) {x : X N | x i - x j ∈ t} = 0 :=
    null_preimage_pair hL htm ht0 i j hij
  have hfail : (volume : Measure (X N)).restrict (box N L)
      {x : X N | (f x)^2 * v (x i - x j) ≠ (f x)^2 * w (x i - x j)} = 0 := by
    have hsub : {x : X N | (f x)^2 * v (x i - x j) ≠ (f x)^2 * w (x i - x j)}
        ⊆ {x : X N | x i - x j ∈ t} := by
      intro x hx
      apply hNt
      intro hEq
      exact hx (by rw [hEq])
    apply le_antisymm
    · calc
        (volume : Measure (X N)).restrict (box N L)
            {x : X N | (f x)^2 * v (x i - x j) ≠ (f x)^2 * w (x i - x j)}
            ≤ (volume : Measure (X N)).restrict (box N L) {x : X N | x i - x j ∈ t} :=
              measure_mono hsub
        _ = 0 := hpre
    · exact bot_le
  have hmem : {x : X N | (f x)^2 * v (x i - x j) = (f x)^2 * w (x i - x j)} ∈
      ae (volume.restrict (box N L)) := by
    rw [mem_ae_iff]
    rw [show ({x : X N | (f x)^2 * v (x i - x j) = (f x)^2 * w (x i - x j)}ᶜ) =
        {x : X N | (f x)^2 * v (x i - x j) ≠ (f x)^2 * w (x i - x j)} by ext x; simp]
    exact hfail
  have hae_eq : (fun x : X N => (f x)^2 * v (x i - x j)) =ᵐ[volume.restrict (box N L)]
      (fun x : X N => (f x)^2 * w (x i - x j)) := by
    rw [show (fun x : X N => (f x)^2 * v (x i - x j)) =ᵐ[volume.restrict (box N L)]
          (fun x : X N => (f x)^2 * w (x i - x j)) ↔
        {x : X N | (f x)^2 * v (x i - x j) = (f x)^2 * w (x i - x j)} ∈
          ae (volume.restrict (box N L)) by rfl]
    exact hmem
  exact hmain.integrable.congr hae_eq.symm

/-! ## The block integrands on the big configuration space -/

/-- Kinetic part of block 1 (derivatives w.r.t. the first `N1` particles). -/
noncomputable def es_kinB1 (N1 N2 : ℕ) (Φ : X (N1 + N2) → ℝ) : X (N1 + N2) → ℝ :=
  fun x => ∑ i : Fin N1, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (N1 + N2) (Fin.castAdd N2 i) k)) ^ 2

/-- Kinetic part of block 2 (derivatives w.r.t. the last `N2` particles). -/
noncomputable def es_kinB2 (N1 N2 : ℕ) (Φ : X (N1 + N2) → ℝ) : X (N1 + N2) → ℝ :=
  fun x => ∑ j : Fin N2, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (N1 + N2) (Fin.natAdd N1 j) k)) ^ 2

/-- Interaction part of block 1 (pairs inside the first block). -/
noncomputable def es_intB1 (N1 N2 : ℕ) (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ) : X (N1 + N2) → ℝ :=
  fun x => (Φ x) ^ 2 *
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
      v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2)))

/-- Interaction part of block 2 (pairs inside the second block). -/
noncomputable def es_intB2 (N1 N2 : ℕ) (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ) : X (N1 + N2) → ℝ :=
  fun x => (Φ x) ^ 2 *
    (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
      v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2)))

/-- The block-1 pointwise kinetic integrand of a slice equals the big kinetic block
evaluated at the merged configuration. -/
lemma es_kinB1_merge {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (u : X N1) (w : X N2) :
    (∑ i : Fin N1, ∑ k : Fin 3, (fderiv ℝ (es_slice1 N1 N2 Φ w) u (kcDir N1 i k)) ^ 2) =
      es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_kinB1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [es_fderiv_slice1 hΦ w u (kcDir N1 i k)]
  rw [es_sliceL_kcDir i k]

/-- The block-2 pointwise kinetic integrand of a slice equals the big kinetic block
evaluated at the merged configuration. -/
lemma es_kinB2_merge {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (u : X N1) (w : X N2) :
    (∑ j : Fin N2, ∑ k : Fin 3, (fderiv ℝ (es_slice2 N1 N2 Φ u) w (kcDir N2 j k)) ^ 2) =
      es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_kinB2
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [es_fderiv_slice2 hΦ u w (kcDir N2 j k)]
  rw [es_sliceR_kcDir j k]

/-- Pointwise coordinate relation of the first block. -/
lemma es_merge_first_coord (N1 N2 : ℕ) (u : X N1) (w : X N2) (p : Fin N1) :
    (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 p) = u p := by
  have h := congrFun (mergeBlock_first N1 N2 u w) p
  simpa [firstBlock] using h

/-- Pointwise coordinate relation of the second block. -/
lemma es_merge_last_coord (N1 N2 : ℕ) (u : X N1) (w : X N2) (p : Fin N2) :
    (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 p) = w p := by
  have h := congrFun (mergeBlock_last N1 N2 u w) p
  simpa [lastBlock] using h

/-- The block-1 interaction density of a slice equals the big interaction block. -/
lemma es_intB1_merge {N1 N2 : ℕ} (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ)
    (u : X N1) (w : X N2) :
    (es_slice1 N1 N2 Φ w u) ^ 2 * intPairSum N1 v u =
      es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_intB1 intPairSum
  simp only [es_slice1]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [es_merge_first_coord N1 N2 u w p.1]
  rw [es_merge_first_coord N1 N2 u w p.2]

/-- The block-2 interaction density of a slice equals the big interaction block. -/
lemma es_intB2_merge {N1 N2 : ℕ} (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ)
    (u : X N1) (w : X N2) :
    (es_slice2 N1 N2 Φ u w) ^ 2 * intPairSum N2 v w =
      es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_intB2 intPairSum
  simp only [es_slice2]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [es_merge_last_coord N1 N2 u w p.1]
  rw [es_merge_last_coord N1 N2 u w p.2]

/-- The `L²`-mass of a block-1 slice equals the merged mass. -/
lemma es_mass_slice1_eq {N1 N2 : ℕ} (L : ℝ) (Φ : X (N1 + N2) → ℝ) (w : X N2) :
    (∫ u in box N1 L, (es_slice1 N1 N2 Φ w u) ^ 2) =
      ∫ u in box N1 L, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 := by
  apply integral_congr_ae
  filter_upwards with u
  simp [es_slice1]

/-- The `L²`-mass of a block-2 slice equals the merged mass. -/
lemma es_mass_slice2_eq {N1 N2 : ℕ} (L : ℝ) (Φ : X (N1 + N2) → ℝ) (u : X N1) :
    (∫ w in box N2 L, (es_slice2 N1 N2 Φ u w) ^ 2) =
      ∫ w in box N2 L, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 := by
  apply integral_congr_ae
  filter_upwards with w
  simp [es_slice2]

/-- The kinetic box energy of a block-1 slice equals the merged big kinetic block. -/
lemma es_kinF_slice1_eq {N1 N2 : ℕ} {L : ℝ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (w : X N2) :
    es_kinF N1 L (es_slice1 N1 N2 Φ w) =
      ∫ u in box N1 L, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_kinF
  apply integral_congr_ae
  filter_upwards with u
  exact es_kinB1_merge hΦ u w

/-- The kinetic box energy of a block-2 slice equals the merged big kinetic block. -/
lemma es_kinF_slice2_eq {N1 N2 : ℕ} {L : ℝ} {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (u : X N1) :
    es_kinF N2 L (es_slice2 N1 N2 Φ u) =
      ∫ w in box N2 L, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_kinF
  apply integral_congr_ae
  filter_upwards with w
  exact es_kinB2_merge hΦ u w

/-- The interaction box energy of a block-1 slice equals the merged big interaction block. -/
lemma es_intF_slice1_eq {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ)
    (w : X N2) :
    es_intF N1 L v (es_slice1 N1 N2 Φ w) =
      ∫ u in box N1 L, es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_intF
  apply integral_congr_ae
  filter_upwards with u
  exact es_intB1_merge v Φ u w

/-- The interaction box energy of a block-2 slice equals the merged big interaction block. -/
lemma es_intF_slice2_eq {N1 N2 : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ)
    (u : X N1) :
    es_intF N2 L v (es_slice2 N1 N2 Φ u) =
      ∫ w in box N2 L, es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w)) := by
  unfold es_intF
  apply integral_congr_ae
  filter_upwards with w
  exact es_intB2_merge v Φ u w

/-- The per-`w` variational inequality of the first block, expressed with the big
block integrands. -/
lemma es_slice1_VI {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (w : X N2) :
    eNeu N1 L v * (∫ u in box N1 L, (es_slice1 N1 N2 Φ w u) ^ 2) ≤
      (∫ u in box N1 L, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
      (∫ u in box N1 L, es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) := by
  have hq := es_eNeu_mul_le (N := N1) (L := L) (v := v) hv (es_slice1_contDiff hΦ w)
  rw [es_kinF_slice1_eq hΦ w, es_intF_slice1_eq v Φ w] at hq
  exact hq

/-- The per-`u` variational inequality of the second block, expressed with the big
block integrands. -/
lemma es_slice2_VI {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (u : X N1) :
    eNeu N2 L v * (∫ w in box N2 L, (es_slice2 N1 N2 Φ u w) ^ 2) ≤
      (∫ w in box N2 L, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
      (∫ w in box N2 L, es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) := by
  have hq := es_eNeu_mul_le (N := N2) (L := L) (v := v) hv (es_slice2_contDiff hΦ u)
  rw [es_kinF_slice2_eq hΦ u, es_intF_slice2_eq v Φ u] at hq
  exact hq

/-! ## Fubini for the box split -/

lemma es_box_prod_integral {N1 N2 : ℕ} (L : ℝ) (G : X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (box (N1 + N2) L) volume) :
    (∫ p : X N1 × X N2,
        G (mergeBlock N1 N2 p) ∂((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L)))) =
      ∫ x in box (N1 + N2) L, G x := by
  let μ1 : Measure (X N1) := volume.restrict (box N1 L)
  let μ2 : Measure (X N2) := volume.restrict (box N2 L)
  let μB : Measure (X (N1 + N2)) := volume.restrict (box (N1 + N2) L)
  have hmp : MeasurePreserving (blockSplitEquiv N1 N2) μB (μ1.prod μ2) := by
    simpa [μ1, μ2, μB] using blockSplit_measurePreserving_restrict N1 N2 L
  have h1 : Integrable G μB := by
    change Integrable G (volume.restrict (box (N1 + N2) L))
    exact hG
  have hEq := (hmp.integral_comp (blockSplitEquiv N1 N2).measurableEmbedding
    (fun p : X N1 × X N2 => G (mergeBlock N1 N2 p)))
  calc
    (∫ p : X N1 × X N2, G (mergeBlock N1 N2 p) ∂(μ1.prod μ2))
        = ∫ x : X (N1+N2), G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x)) ∂μB := by
          rw [hEq]
    _ = ∫ x : X (N1+N2), G x ∂μB := by
          congr 1
          funext x
          rw [blockSplitEquiv_apply]
          exact congrArg G (mergeBlock_eq N1 N2 x)
    _ = ∫ x in box (N1 + N2) L, G x := by rfl

lemma es_box_prod_integrable {N1 N2 : ℕ} (L : ℝ) (G : X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (box (N1 + N2) L) volume) :
    Integrable (fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))
      ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) := by
  let μ1 : Measure (X N1) := volume.restrict (box N1 L)
  let μ2 : Measure (X N2) := volume.restrict (box N2 L)
  let μB : Measure (X (N1 + N2)) := volume.restrict (box (N1 + N2) L)
  have hmp : MeasurePreserving (blockSplitEquiv N1 N2) μB (μ1.prod μ2) := by
    simpa [μ1, μ2, μB] using blockSplit_measurePreserving_restrict N1 N2 L
  have h1 : Integrable G μB := by
    change Integrable G (volume.restrict (box (N1 + N2) L))
    exact hG
  have hif := (hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding
    (g := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p)))
  apply hif.1
  change Integrable (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))) μB
  have hpt : (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))) = G := by
    funext x
    rw [blockSplitEquiv_apply]
    exact congrArg G (mergeBlock_eq N1 N2 x)
  rw [hpt]
  exact h1

/-- Restricted Fubini (u-outer order). -/
lemma es_boxFubini {N1 N2 : ℕ} (L : ℝ) (G : X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (box (N1 + N2) L) volume) :
    (∫ u in box N1 L, ∫ w in box N2 L, G (mergeBlock N1 N2 (u, w))) =
      ∫ x in box (N1 + N2) L, G x := by
  let μ1 : Measure (X N1) := volume.restrict (box N1 L)
  let μ2 : Measure (X N2) := volume.restrict (box N2 L)
  have hGe := es_box_prod_integrable (N1 := N1) (N2 := N2) L G hG
  calc
    (∫ u in box N1 L, ∫ w in box N2 L, G (mergeBlock N1 N2 (u, w)))
        = ∫ p : X N1 × X N2, G (mergeBlock N1 N2 p) ∂(μ1.prod μ2) := by
          exact (integral_prod (μ := μ1) (ν := μ2)
            (f := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p)) hGe).symm
    _ = ∫ x in box (N1 + N2) L, G x := es_box_prod_integral (N1 := N1) (N2 := N2) L G hG

/-- Restricted Fubini (w-outer order). -/
lemma es_boxFubini_swapped {N1 N2 : ℕ} (L : ℝ) (G : X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (box (N1 + N2) L) volume) :
    (∫ w in box N2 L, ∫ u in box N1 L, G (mergeBlock N1 N2 (u, w))) =
      ∫ x in box (N1 + N2) L, G x := by
  let μ1 : Measure (X N1) := volume.restrict (box N1 L)
  let μ2 : Measure (X N2) := volume.restrict (box N2 L)
  have hGe := es_box_prod_integrable (N1 := N1) (N2 := N2) L G hG
  have hQ : Integrable (fun q : X N2 × X N1 => G (mergeBlock N1 N2 q.swap)) (μ2.prod μ1) := by
    simpa [Function.comp_def, Prod.swap_prod_mk] using hGe.swap
  calc
    (∫ w in box N2 L, ∫ u in box N1 L, G (mergeBlock N1 N2 (u, w)))
        = ∫ q : X N2 × X N1, G (mergeBlock N1 N2 q.swap) ∂(μ2.prod μ1) := by
          exact (integral_prod (μ := μ2) (ν := μ1)
            (f := fun q : X N2 × X N1 => G (mergeBlock N1 N2 q.swap)) hQ).symm
    _ = ∫ p : X N1 × X N2, G (mergeBlock N1 N2 p) ∂(μ1.prod μ2) := by
          exact MeasureTheory.integral_prod_swap (μ := μ1) (ν := μ2)
            (f := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))
    _ = ∫ x in box (N1 + N2) L, G x := es_box_prod_integral (N1 := N1) (N2 := N2) L G hG

/-! ## Integrability of the block integrands over the box -/

lemma es_kinB1_integrableOn {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) {Φ : X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) : IntegrableOn (es_kinB1 N1 N2 Φ) (box (N1 + N2) L) volume := by
  unfold es_kinB1
  change Integrable (fun x : X (N1+N2) => ∑ i : Fin N1, ∑ k : Fin 3,
      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i) k))^2) (volume.restrict (box (N1+N2) L))
  exact integrable_finsetSum Finset.univ (fun i _ => by
    change Integrable (fun x : X (N1+N2) => ∑ k : Fin 3,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i) k))^2) (volume.restrict (box (N1+N2) L))
    exact integrable_finsetSum Finset.univ (fun k _ => by
      exact es_integrableOn_cont hL
        ((firstDir_contDiff hΦ (kcDir (N1+N2) (Fin.castAdd N2 i) k)).continuous.pow 2)))

lemma es_kinB2_integrableOn {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) {Φ : X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) : IntegrableOn (es_kinB2 N1 N2 Φ) (box (N1 + N2) L) volume := by
  unfold es_kinB2
  change Integrable (fun x : X (N1+N2) => ∑ j : Fin N2, ∑ k : Fin 3,
      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j) k))^2) (volume.restrict (box (N1+N2) L))
  exact integrable_finsetSum Finset.univ (fun j _ => by
    change Integrable (fun x : X (N1+N2) => ∑ k : Fin 3,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j) k))^2) (volume.restrict (box (N1+N2) L))
    exact integrable_finsetSum Finset.univ (fun k _ => by
      exact es_integrableOn_cont hL
        ((firstDir_contDiff hΦ (kcDir (N1+N2) (Fin.natAdd N1 j) k)).continuous.pow 2)))

lemma es_intB1_integrableOn {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ} (hv1 : MemLp v 1)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    IntegrableOn (es_intB1 N1 N2 v Φ) (box (N1 + N2) L) volume := by
  unfold es_intB1
  change Integrable (fun x : X (N1+N2) => (Φ x)^2 *
      (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
        v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2)))) (volume.restrict (box (N1+N2) L))
  have hEq : (fun x : X (N1+N2) => (Φ x)^2 *
        (∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
          v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2))))
      = fun x : X (N1+N2) => ∑ p ∈ (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2)),
          (Φ x)^2 * v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2)) := by
    funext x
    exact Finset.mul_sum (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2))
      (fun p => v (x (Fin.castAdd N2 p.1) - x (Fin.castAdd N2 p.2))) ((Φ x)^2)
  rw [hEq]
  exact integrable_finsetSum (Finset.univ.filter (fun p : Fin N1 × Fin N1 => p.1 < p.2))
    (fun p hp => by
      have hv : p.1.val < p.2.val := (Finset.mem_filter.mp hp).2
      have hval : (Fin.castAdd N2 p.1).val ≠ (Fin.castAdd N2 p.2).val := by
        simp [Fin.castAdd]
        omega
      exact es_sq_v_integrableOn hL hv1 hΦ (Fin.ne_of_val_ne hval))

lemma es_intB2_integrableOn {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ} (hv1 : MemLp v 1)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    IntegrableOn (es_intB2 N1 N2 v Φ) (box (N1 + N2) L) volume := by
  unfold es_intB2
  change Integrable (fun x : X (N1+N2) => (Φ x)^2 *
      (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
        v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2)))) (volume.restrict (box (N1+N2) L))
  have hEq : (fun x : X (N1+N2) => (Φ x)^2 *
        (∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
          v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2))))
      = fun x : X (N1+N2) => ∑ p ∈ (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2)),
          (Φ x)^2 * v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2)) := by
    funext x
    exact Finset.mul_sum (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2))
      (fun p => v (x (Fin.natAdd N1 p.1) - x (Fin.natAdd N1 p.2))) ((Φ x)^2)
  rw [hEq]
  exact integrable_finsetSum (Finset.univ.filter (fun p : Fin N2 × Fin N2 => p.1 < p.2))
    (fun p hp => by
      have hv : p.1.val < p.2.val := (Finset.mem_filter.mp hp).2
      have hval : (Fin.natAdd N1 p.1).val ≠ (Fin.natAdd N1 p.2).val := by
        simp [Fin.natAdd]
        omega
      exact es_sq_v_integrableOn hL hv1 hΦ (Fin.ne_of_val_ne hval))

/-- The interaction density of all pairs, on the big space. -/
noncomputable def es_intAll (N1 N2 : ℕ) (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ) : X (N1 + N2) → ℝ :=
  fun x => (Φ x)^2 * intPairSum (N1 + N2) v x

lemma es_intAll_integrableOn {N1 N2 : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ} (hv1 : MemLp v 1)
    {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    IntegrableOn (es_intAll N1 N2 v Φ) (box (N1 + N2) L) volume := by
  unfold es_intAll
  change Integrable (fun x : X (N1+N2) => (Φ x)^2 *
      (∑ p ∈ (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)),
        v (x p.1 - x p.2))) (volume.restrict (box (N1+N2) L))
  have hEq : (fun x : X (N1+N2) => (Φ x)^2 *
        (∑ p ∈ (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)),
          v (x p.1 - x p.2)))
      = fun x : X (N1+N2) => ∑ p ∈ (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2)),
          (Φ x)^2 * v (x p.1 - x p.2) := by
    funext x
    exact Finset.mul_sum (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2))
      (fun p => v (x p.1 - x p.2)) ((Φ x)^2)
  rw [hEq]
  exact integrable_finsetSum
    (Finset.univ.filter (fun p : Fin (N1+N2) × Fin (N1+N2) => p.1 < p.2))
    (fun p hp => by
      exact es_sq_v_integrableOn hL hv1 hΦ
        (ne_of_lt (Finset.mem_filter.mp hp).2))

/-- The full kinetic density on the big space. -/
noncomputable def es_kinAll (N : ℕ) (Φ : X N → ℝ) : X N → ℝ :=
  fun x => ∑ i : Fin N, ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-! ## The block bounds and the per-state inequality -/

/-- A finite sum of box-integrable functions is box-integrable. -/
lemma es_finset_sum_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L)
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {g : ι → X N → ℝ}
    (hg : ∀ p ∈ S, IntegrableOn (g p) (box N L) volume) :
    IntegrableOn (fun x : X N => ∑ p ∈ S, g p x) (box N L) volume := by
  change Integrable (fun x : X N => ∑ p ∈ S, g p x) (volume.restrict (box N L))
  exact integrable_finsetSum S (fun p hp => hg p hp)

/-- The full kinetic density is box-integrable. -/
lemma es_kinAll_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L) {φ : X N → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : IntegrableOn (es_kinAll N φ) (box N L) volume := by
  unfold es_kinAll
  change Integrable (fun x : X N => ∑ i : Fin N, ∑ k : Fin 3,
      (fderiv ℝ φ x (kcDir N i k))^2) (volume.restrict (box N L))
  exact integrable_finsetSum Finset.univ (fun i _ => by
    change Integrable (fun x : X N => ∑ k : Fin 3,
        (fderiv ℝ φ x (kcDir N i k))^2) (volume.restrict (box N L))
    exact integrable_finsetSum Finset.univ (fun k _ => by
      exact es_integrableOn_cont hL ((firstDir_contDiff hφ (kcDir N i k)).continuous.pow 2)))

/-- Block-1 bound: `E1·‖Φ‖² ≤ ∫(kinB1+intB1)`. -/
lemma es_block1_bound {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    eNeu N1 L v * (∫ x in box (N1 + N2) L, (Φ x)^2) ≤
      ∫ x in box (N1 + N2) L, (es_kinB1 N1 N2 Φ x + es_intB1 N1 N2 v Φ x) := by
  let E1 := eNeu N1 L v
  have hP0 : IntegrableOn (fun x : X (N1+N2) => (Φ x)^2) (box (N1+N2) L) volume :=
    es_sq_integrableOn hL hΦ.continuous
  have hK1 : IntegrableOn (es_kinB1 N1 N2 Φ) (box (N1+N2) L) volume :=
    es_kinB1_integrableOn hL hΦ
  have hI1 : IntegrableOn (es_intB1 N1 N2 v Φ) (box (N1+N2) L) volume :=
    es_intB1_integrableOn (N1 := N1) (N2 := N2) (L := L) hL hv1 hΦ
  have hD1 : IntegrableOn (fun w : X N2 => ∫ u in box N1 L,
      (Φ (mergeBlock N1 N2 (u, w)))^2) (box N2 L) volume := by
    have hFP : Integrable (fun p : X N1 × X N2 => (Φ (mergeBlock N1 N2 p))^2)
        ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) :=
      es_box_prod_integrable (N1 := N1) (N2 := N2) L (fun x : X (N1+N2) => (Φ x)^2) hP0
    have hR := Integrable.integral_prod_right hFP
    change Integrable (fun w : X N2 => ∫ u in box N1 L,
        (Φ (mergeBlock N1 N2 (u, w)))^2) (volume.restrict (box N2 L))
    exact hR
  have hK : IntegrableOn (fun w : X N2 => ∫ u in box N1 L,
      es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) (box N2 L) volume := by
    have hFP : Integrable (fun p : X N1 × X N2 => es_kinB1 N1 N2 Φ (mergeBlock N1 N2 p))
        ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) :=
      es_box_prod_integrable (N1 := N1) (N2 := N2) L (es_kinB1 N1 N2 Φ) hK1
    have hR := Integrable.integral_prod_right hFP
    change Integrable (fun w : X N2 => ∫ u in box N1 L,
        es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) (volume.restrict (box N2 L))
    exact hR
  have hI : IntegrableOn (fun w : X N2 => ∫ u in box N1 L,
      es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) (box N2 L) volume := by
    have hFP : Integrable (fun p : X N1 × X N2 => es_intB1 N1 N2 v Φ (mergeBlock N1 N2 p))
        ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) :=
      es_box_prod_integrable (N1 := N1) (N2 := N2) L (es_intB1 N1 N2 v Φ) hI1
    have hR := Integrable.integral_prod_right hFP
    change Integrable (fun w : X N2 => ∫ u in box N1 L,
        es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) (volume.restrict (box N2 L))
    exact hR
  have hpt : ∀ w : X N2,
      E1 * (∫ u in box N1 L, (Φ (mergeBlock N1 N2 (u, w)))^2) ≤
        (∫ u in box N1 L, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
        (∫ u in box N1 L, es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) := by
    intro w
    have hq := es_slice1_VI (N1 := N1) (N2 := N2) (L := L) (v := v) hv hΦ w
    rw [es_mass_slice1_eq L Φ w] at hq
    simpa [E1] using hq
  have hineq :
      (∫ w in box N2 L, E1 * (∫ u in box N1 L, (Φ (mergeBlock N1 N2 (u, w)))^2)) ≤
      (∫ w in box N2 L,
        ((∫ u in box N1 L, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ u in box N1 L, es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w))))) := by
    refine integral_mono ?_ ?_ ?_
    · exact hD1.const_mul E1
    · exact Integrable.add hK hI
    · intro w
      exact hpt w
  have hstep0 : (∫ w in box N2 L, E1 * (∫ u in box N1 L,
      (Φ (mergeBlock N1 N2 (u, w)))^2))
      = E1 * (∫ x in box (N1 + N2) L, (Φ x)^2) := by
    rw [integral_const_mul]
    congr 1
    exact es_boxFubini_swapped (N1 := N1) (N2 := N2) L (fun x : X (N1+N2) => (Φ x)^2) hP0
  have hstepR :
      (∫ w in box N2 L,
        ((∫ u in box N1 L, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ u in box N1 L, es_intB1 N1 N2 v Φ (mergeBlock N1 N2 (u, w)))))
      = (∫ x in box (N1 + N2) L, es_kinB1 N1 N2 Φ x) +
          (∫ x in box (N1 + N2) L, es_intB1 N1 N2 v Φ x) := by
    rw [integral_add hK hI]
    congr 1
    · exact es_boxFubini_swapped (N1 := N1) (N2 := N2) L (es_kinB1 N1 N2 Φ) hK1
    · exact es_boxFubini_swapped (N1 := N1) (N2 := N2) L (es_intB1 N1 N2 v Φ) hI1
  rw [hstep0, hstepR] at hineq
  rw [← integral_add hK1 hI1] at hineq
  simpa [E1] using hineq

/-- Block-2 bound: `E2·‖Φ‖² ≤ ∫(kinB2+intB2)`. -/
lemma es_block2_bound {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) {Φ : X (N1 + N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    eNeu N2 L v * (∫ x in box (N1 + N2) L, (Φ x)^2) ≤
      ∫ x in box (N1 + N2) L, (es_kinB2 N1 N2 Φ x + es_intB2 N1 N2 v Φ x) := by
  let E2 := eNeu N2 L v
  have hP0 : IntegrableOn (fun x : X (N1+N2) => (Φ x)^2) (box (N1+N2) L) volume :=
    es_sq_integrableOn hL hΦ.continuous
  have hK2 : IntegrableOn (es_kinB2 N1 N2 Φ) (box (N1+N2) L) volume :=
    es_kinB2_integrableOn hL hΦ
  have hI2 : IntegrableOn (es_intB2 N1 N2 v Φ) (box (N1+N2) L) volume :=
    es_intB2_integrableOn (N1 := N1) (N2 := N2) (L := L) hL hv1 hΦ
  have hD2 : IntegrableOn (fun u : X N1 => ∫ w in box N2 L,
      (Φ (mergeBlock N1 N2 (u, w)))^2) (box N1 L) volume := by
    have hFP : Integrable (fun p : X N1 × X N2 => (Φ (mergeBlock N1 N2 p))^2)
        ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) :=
      es_box_prod_integrable (N1 := N1) (N2 := N2) L (fun x : X (N1+N2) => (Φ x)^2) hP0
    have hR := Integrable.integral_prod_left hFP
    change Integrable (fun u : X N1 => ∫ w in box N2 L,
        (Φ (mergeBlock N1 N2 (u, w)))^2) (volume.restrict (box N1 L))
    exact hR
  have hK : IntegrableOn (fun u : X N1 => ∫ w in box N2 L,
      es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) (box N1 L) volume := by
    have hFP : Integrable (fun p : X N1 × X N2 => es_kinB2 N1 N2 Φ (mergeBlock N1 N2 p))
        ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) :=
      es_box_prod_integrable (N1 := N1) (N2 := N2) L (es_kinB2 N1 N2 Φ) hK2
    have hR := Integrable.integral_prod_left hFP
    change Integrable (fun u : X N1 => ∫ w in box N2 L,
        es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) (volume.restrict (box N1 L))
    exact hR
  have hI : IntegrableOn (fun u : X N1 => ∫ w in box N2 L,
      es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) (box N1 L) volume := by
    have hFP : Integrable (fun p : X N1 × X N2 => es_intB2 N1 N2 v Φ (mergeBlock N1 N2 p))
        ((volume.restrict (box N1 L)).prod (volume.restrict (box N2 L))) :=
      es_box_prod_integrable (N1 := N1) (N2 := N2) L (es_intB2 N1 N2 v Φ) hI2
    have hR := Integrable.integral_prod_left hFP
    change Integrable (fun u : X N1 => ∫ w in box N2 L,
        es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) (volume.restrict (box N1 L))
    exact hR
  have hpt : ∀ u : X N1,
      E2 * (∫ w in box N2 L, (Φ (mergeBlock N1 N2 (u, w)))^2) ≤
        (∫ w in box N2 L, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
        (∫ w in box N2 L, es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w))) := by
    intro u
    have hq := es_slice2_VI (N1 := N1) (N2 := N2) (L := L) (v := v) hv hΦ u
    rw [es_mass_slice2_eq L Φ u] at hq
    simpa [E2] using hq
  have hineq :
      (∫ u in box N1 L, E2 * (∫ w in box N2 L, (Φ (mergeBlock N1 N2 (u, w)))^2)) ≤
      (∫ u in box N1 L,
        ((∫ w in box N2 L, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ w in box N2 L, es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w))))) := by
    refine integral_mono ?_ ?_ ?_
    · exact hD2.const_mul E2
    · exact Integrable.add hK hI
    · intro u
      exact hpt u
  have hstep0 : (∫ u in box N1 L, E2 * (∫ w in box N2 L,
      (Φ (mergeBlock N1 N2 (u, w)))^2))
      = E2 * (∫ x in box (N1 + N2) L, (Φ x)^2) := by
    rw [integral_const_mul]
    congr 1
    exact es_boxFubini (N1 := N1) (N2 := N2) L (fun x : X (N1+N2) => (Φ x)^2) hP0
  have hstepR :
      (∫ u in box N1 L,
        ((∫ w in box N2 L, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ w in box N2 L, es_intB2 N1 N2 v Φ (mergeBlock N1 N2 (u, w)))))
      = (∫ x in box (N1 + N2) L, es_kinB2 N1 N2 Φ x) +
          (∫ x in box (N1 + N2) L, es_intB2 N1 N2 v Φ x) := by
    rw [integral_add hK hI]
    congr 1
    · exact es_boxFubini (N1 := N1) (N2 := N2) L (es_kinB2 N1 N2 Φ) hK2
    · exact es_boxFubini (N1 := N1) (N2 := N2) L (es_intB2 N1 N2 v Φ) hI2
  rw [hstep0, hstepR] at hineq
  rw [← integral_add hK2 hI2] at hineq
  simpa [E2] using hineq

/-- Cross interaction density (pairs across the two blocks). -/
noncomputable def es_crossB (N1 N2 : ℕ) (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ) : X (N1 + N2) → ℝ :=
  fun x => (Φ x)^2 * (∑ i : Fin N1, ∑ j : Fin N2,
    v (x (Fin.castAdd N2 i) - x (Fin.natAdd N1 j)))

/-- The cross interaction density is nonnegative for `v ≥ 0`. -/
lemma es_crossB_nonneg {N1 N2 : ℕ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    (Φ : X (N1 + N2) → ℝ) (x : X (N1 + N2)) : 0 ≤ es_crossB N1 N2 v Φ x := by
  unfold es_crossB
  exact mul_nonneg (sq_nonneg (Φ x))
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hv _)))

/-- The full kinetic density splits into the two blocks. -/
lemma es_kinAll_split {N1 N2 : ℕ} (Φ : X (N1 + N2) → ℝ) (x : X (N1 + N2)) :
    es_kinAll (N1 + N2) Φ x = es_kinB1 N1 N2 Φ x + es_kinB2 N1 N2 Φ x := by
  unfold es_kinAll es_kinB1 es_kinB2
  rw [Fin.sum_univ_add (a := N1) (b := N2)
    (f := fun i : Fin (N1 + N2) => ∑ k : Fin 3, (fderiv ℝ Φ x (kcDir (N1 + N2) i k)) ^ 2)]

/-- The full interaction density splits into the two blocks and the cross term. -/
lemma es_intAll_split {N1 N2 : ℕ} (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ) (x : X (N1 + N2)) :
    es_intAll N1 N2 v Φ x = es_intB1 N1 N2 v Φ x + es_intB2 N1 N2 v Φ x + es_crossB N1 N2 v Φ x := by
  unfold es_intAll es_intB1 es_intB2 es_crossB intPairSum
  have hsplit := pairSum_eq_blocks (a := N1) (b := N2)
    (f := fun a b : Fin (N1 + N2) => v (x a - x b))
  rw [hsplit]
  ring

/-- Pointwise: blocks + cross = full (reformulated). -/
lemma es_blocks_add_cross_eq_full {N1 N2 : ℕ} (v : ℝ³ → ℝ) (Φ : X (N1 + N2) → ℝ)
    (x : X (N1 + N2)) :
    es_kinB1 N1 N2 Φ x + es_intB1 N1 N2 v Φ x + es_kinB2 N1 N2 Φ x + es_intB2 N1 N2 v Φ x +
      es_crossB N1 N2 v Φ x =
    es_kinAll (N1 + N2) Φ x + es_intAll N1 N2 v Φ x := by
  rw [es_intAll_split v Φ x, es_kinAll_split Φ x]
  ring

/-- Pointwise: the two blocks together are bounded by the full energy density. -/
lemma es_blocks_le_full {N1 N2 : ℕ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) (Φ : X (N1 + N2) → ℝ)
    (x : X (N1 + N2)) :
    es_kinB1 N1 N2 Φ x + es_intB1 N1 N2 v Φ x + es_kinB2 N1 N2 Φ x + es_intB2 N1 N2 v Φ x ≤
      es_kinAll (N1 + N2) Φ x + es_intAll N1 N2 v Φ x := by
  have hc : 0 ≤ es_crossB N1 N2 v Φ x := es_crossB_nonneg hv Φ x
  have hEq := es_blocks_add_cross_eq_full v Φ x
  linarith

/-- **The per-state inequality** for Neumann states. -/
lemma es_per_state {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (Φ : CNeu (N1 + N2) L) :
    eNeu N1 L v + eNeu N2 L v ≤
      (kinNeu (N1 + N2) L Φ + intNeu (N1 + N2) L v Φ) /
        (∫ x in box (N1 + N2) L, ((Φ : X (N1 + N2) → ℝ) x) ^ 2) := by
  let φ : X (N1 + N2) → ℝ := Φ
  let E1 := eNeu N1 L v
  let E2 := eNeu N2 L v
  let IΦ := ∫ x in box (N1 + N2) L, (φ x) ^ 2
  have hφ : ContDiff ℝ ∞ φ := by simpa [φ] using Φ.contDiff
  have hb1 := es_block1_bound (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv hv1 (Φ := φ) hφ
  have hb2 := es_block2_bound (N1 := N1) (N2 := N2) (L := L) (v := v) hL hv hv1 (Φ := φ) hφ
  have hK1 : IntegrableOn (es_kinB1 N1 N2 φ) (box (N1+N2) L) volume := es_kinB1_integrableOn hL hφ
  have hI1 : IntegrableOn (es_intB1 N1 N2 v φ) (box (N1+N2) L) volume :=
    es_intB1_integrableOn (N1 := N1) (N2 := N2) (L := L) hL hv1 hφ
  have hK2 : IntegrableOn (es_kinB2 N1 N2 φ) (box (N1+N2) L) volume := es_kinB2_integrableOn hL hφ
  have hI2 : IntegrableOn (es_intB2 N1 N2 v φ) (box (N1+N2) L) volume :=
    es_intB2_integrableOn (N1 := N1) (N2 := N2) (L := L) hL hv1 hφ
  have hKAll : IntegrableOn (es_kinAll (N1+N2) φ) (box (N1+N2) L) volume :=
    es_kinAll_integrableOn hL hφ
  have hIAll : IntegrableOn (es_intAll N1 N2 v φ) (box (N1+N2) L) volume :=
    es_intAll_integrableOn (N1 := N1) (N2 := N2) (L := L) hL hv1 hφ
  have hW : (∫ x in box (N1+N2) L,
        (es_kinB1 N1 N2 φ x + es_intB1 N1 N2 v φ x)) +
      (∫ x in box (N1+N2) L, (es_kinB2 N1 N2 φ x + es_intB2 N1 N2 v φ x)) ≤
    ∫ x in box (N1+N2) L, (es_kinAll (N1+N2) φ x + es_intAll N1 N2 v φ x) := by
    have hSum : (∫ x in box (N1+N2) L,
          (es_kinB1 N1 N2 φ x + es_intB1 N1 N2 v φ x)) +
        (∫ x in box (N1+N2) L, (es_kinB2 N1 N2 φ x + es_intB2 N1 N2 v φ x))
        = ∫ x in box (N1+N2) L,
            ((es_kinB1 N1 N2 φ x + es_intB1 N1 N2 v φ x) +
              (es_kinB2 N1 N2 φ x + es_intB2 N1 N2 v φ x)) := by
      exact (integral_add (IntegrableOn.add hK1 hI1) (IntegrableOn.add hK2 hI2)).symm
    rw [hSum]
    refine integral_mono ?_ ?_ ?_
    · exact IntegrableOn.add (IntegrableOn.add hK1 hI1) (IntegrableOn.add hK2 hI2)
    · exact IntegrableOn.add hKAll hIAll
    · intro x
      have hx := es_blocks_le_full (v := v) hv φ x
      nlinarith
  have hsum12 : (E1 + E2) * IΦ ≤
      (∫ x in box (N1+N2) L, (es_kinB1 N1 N2 φ x + es_intB1 N1 N2 v φ x)) +
      (∫ x in box (N1+N2) L, (es_kinB2 N1 N2 φ x + es_intB2 N1 N2 v φ x)) := by
    nlinarith [hb1, hb2]
  have hfull : (E1 + E2) * IΦ ≤ ∫ x in box (N1+N2) L,
      (es_kinAll (N1+N2) φ x + es_intAll N1 N2 v φ x) := by
    exact le_trans hsum12 hW
  have hkin : ∫ x in box (N1+N2) L, es_kinAll (N1+N2) φ x = kinNeu (N1+N2) L Φ := by
    simp [es_kinAll, kinNeu, φ]
  have hint : ∫ x in box (N1+N2) L, es_intAll N1 N2 v φ x = intNeu (N1+N2) L v Φ := by
    simp [es_intAll, intNeu, intPairSum, φ]
  have hfull' : (E1 + E2) * IΦ ≤ kinNeu (N1 + N2) L Φ + intNeu (N1 + N2) L v Φ := by
    have hEqInt : (∫ x in box (N1+N2) L,
          (es_kinAll (N1+N2) φ x + es_intAll N1 N2 v φ x))
        = kinNeu (N1 + N2) L Φ + intNeu (N1 + N2) L v Φ := by
      calc
        (∫ x in box (N1+N2) L, (es_kinAll (N1+N2) φ x + es_intAll N1 N2 v φ x))
            = (∫ x in box (N1+N2) L, es_kinAll (N1+N2) φ x) +
              (∫ x in box (N1+N2) L, es_intAll N1 N2 v φ x) := by
              exact integral_add hKAll hIAll
        _ = kinNeu (N1 + N2) L Φ + intNeu (N1 + N2) L v Φ := by
              rw [hkin, hint]
    rw [hEqInt] at hfull
    exact hfull
  have hpos : 0 < IΦ := by
    simpa [IΦ, φ] using (Φ.sq_pos : 0 < ∫ x in box (N1 + N2) L,
      ((Φ : X (N1 + N2) → ℝ) x) ^ 2)
  have hdiv := (le_div_iff₀ hpos).mpr hfull'
  simpa [E1, E2, IΦ, φ] using hdiv

/-- **Neumann ground states are superadditive in the particle number** (the
mirror of `Superadd.boxEnergy_superadd`). -/
lemma eNeu_superadd {n₁ n₂ : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) : eNeu n₁ L v + eNeu n₂ L v ≤ eNeu (n₁ + n₂) L v := by
  have hper : ∀ Φ : CNeu (n₁ + n₂) L,
      eNeu n₁ L v + eNeu n₂ L v ≤
        (kinNeu (n₁ + n₂) L Φ + intNeu (n₁ + n₂) L v Φ) /
          (∫ x in box (n₁ + n₂) L, ((Φ : X (n₁ + n₂) → ℝ) x) ^ 2) := by
    intro Φ
    exact es_per_state (N1 := n₁) (N2 := n₂) (L := L) (v := v) hL hv hv1 Φ
  unfold eNeu
  haveI : Nonempty (CNeu (n₁ + n₂) L) := nonempty_CNeu (n₁ + n₂) hL
  exact le_ciInf hper
