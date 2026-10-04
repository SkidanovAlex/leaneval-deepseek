import Mathlib
import Submission.Work.Diff.STE.GN.tools
import Submission.Work.Diff.STE.GN.discrete_convex
import Submission.Work.Diff.STE.GN.holder2_int
import Submission.Work.Diff.STE.GN.gnLevStepOneClean
import Submission.Work.Diff.STE.GN.ibpRpowComplexClean
import Submission.Work.Diff.STE.GN.gnLevStepGenClean
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.Lead.Gal.pdVec_gard_defect_bound
import Submission.Work.Diff.STE.Lead.GalTame.ENormSq_pd_le
import Submission.Work.Diff.STE.Lead.GalTame.ENormSq_pd_pd_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary helpers -/

/-- `ENormSq 0` is the square of the `L²` norm on the unit cube. -/
lemma ENormSq_zero_eq_int (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 f = ∫ x in Work.Diff.STE.unitCube, ‖f x‖ ^ 2 := by
  simp only [Work.Diff.STE.ENormSq, Finset.univ_unique, Finset.sum_singleton,
    Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]

/-- Iterated partial derivatives of a smooth function are smooth. -/
lemma contDiff_pd_top {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (i : ι) : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Work.Diff.STE.pd i f) := by
  have h : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fderiv ℝ f) :=
    hf.fderiv_right (m := ((⊤ : ENat) : WithTop ENat)) (by simp)
  have h2 : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun x => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) := by
    simpa [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single i (1 : ℝ))).contDiff.comp h
  exact h2

/-- The partial derivative of a periodic smooth function is periodic. -/
lemma periodic1_pd {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (hper : Work.Diff.STE.Periodic1 f) (i : ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pd i f) :=
  fun j => Work.Diff.STE.ga_periodicIn_pd j i hper (hf.differentiable (by simp))

/-- Complexification preserves periodicity. -/
lemma periodic1_ofReal {F : (ι → ℝ) → ℝ} (h : Work.Diff.STE.Periodic1 F) :
    Work.Diff.STE.Periodic1 (fun y => ((F y : ℝ) : ℂ)) := fun i x => by simp [h i x]

/-- The complexification of a smooth real function is smooth. -/
lemma contDiff_ofReal {F : (ι → ℝ) → ℝ}
    (hF : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun y => ((F y : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hF

/-- The list sum of the values of a function is the corresponding `Fin`-indexed sum. -/
lemma list_sum_map_eq_sum_fin {α : Type*} (L : List α) (g : α → ℂ) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.map_cons, List.sum_cons, ih]
      change g a + ∑ i : Fin L.length, g (L.get i) = ∑ i : Fin (L.length + 1), g ((a :: L).get i)
      rw [Fin.sum_univ_succ]
      simp

/-- Cauchy–Schwarz for a finite sum of complex numbers. -/
lemma norm_sum_sq_le_card_mul {β : Type*} (s : Finset β) (v : β → ℂ) :
    ‖∑ b ∈ s, v b‖ ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  have h1 : ‖∑ b ∈ s, v b‖ ≤ ∑ b ∈ s, ‖v b‖ := norm_sum_le s v
  have h3 : (∑ b ∈ s, ‖v b‖) ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖v b‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h3

/-- Cauchy–Schwarz, integrated over the cube, for a finite family of continuous functions. -/
lemma integral_norm_sum_sq_le {β : Type*} [Fintype β] (f : β → (ι → ℝ) → ℂ)
    (hf : ∀ b, Continuous (f b)) :
    ∫ x in Work.Diff.STE.unitCube, ‖∑ b, f b x‖ ^ 2
      ≤ (Fintype.card β : ℝ) * ∑ b, ∫ x in Work.Diff.STE.unitCube, ‖f b x‖ ^ 2 := by
  have hpt : ∀ x, ‖∑ b, f b x‖ ^ 2 ≤ (Fintype.card β : ℝ) * ∑ b, ‖f b x‖ ^ 2 :=
    fun x => norm_sum_sq_le_card_mul Finset.univ (fun b => f b x)
  have hcont1 : Continuous (fun x => ‖∑ b, f b x‖ ^ 2) :=
    (continuous_finsetSum _ (fun b _ => hf b)).norm.pow 2
  have hcont2 : Continuous (fun x => (Fintype.card β : ℝ) * ∑ b, ‖f b x‖ ^ 2) :=
    continuous_const.mul (continuous_finsetSum _ (fun b _ => (hf b).norm.pow 2))
  calc ∫ x in Work.Diff.STE.unitCube, ‖∑ b, f b x‖ ^ 2
      ≤ ∫ x in Work.Diff.STE.unitCube, (Fintype.card β : ℝ) * ∑ b, ‖f b x‖ ^ 2 :=
        integral_mono (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous hcont1)
          (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous hcont2) hpt
    _ = (Fintype.card β : ℝ) * ∑ b, ∫ x in Work.Diff.STE.unitCube, ‖f b x‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum]
        exact fun b _ => Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hf b).norm.pow 2)

/-- Continuity of `∂^q` of a complexified smooth function. -/
lemma cont_pdList_ofReal {A : (ι → ℝ) → ℝ}
    (hA : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A) (q : List ι) :
    Continuous (Work.Diff.STE.pdList q (fun y => ((A y : ℝ) : ℂ))) := by
  have h : ContDiff ℝ (↑(q.length)) (fun y => ((A y : ℝ) : ℂ)) :=
    (contDiff_ofReal hA).of_le (WithTop.coe_le_coe.mpr le_top)
  exact (Work.Diff.STE.cm_contDiff_pdList q 0 _ h).continuous

/-- Continuity of `∂^q` of `∂_c∂_d u`. -/
lemma cont_pdList_pair {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
    (c d : ι) (q : List ι) :
    Continuous (Work.Diff.STE.pdList q (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)) := by
  have h1 : ContDiff ℝ (↑(2 + q.length)) u :=
    hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have h2 : ContDiff ℝ (↑(q.length))
      (Work.Diff.STE.pdList [c, d] u) :=
    Work.Diff.STE.cm_contDiff_pdList [c, d] q.length u (by simpa using h1)
  have h3 : ContDiff ℝ (↑(q.length + 0))
      (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) := by
    simpa [Work.Diff.STE.pdList] using h2
  exact (Work.Diff.STE.cm_contDiff_pdList q 0 _ h3).continuous

/-- Differentiability of `∂^q` of a complexified smooth function. -/
lemma diff_pdList_ofReal {A : (ι → ℝ) → ℝ}
    (hA : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A) (q : List ι) :
    Differentiable ℝ (Work.Diff.STE.pdList q (fun y => ((A y : ℝ) : ℂ))) := by
  have h : ContDiff ℝ (↑(q.length + 1)) (fun y => ((A y : ℝ) : ℂ)) :=
    (contDiff_ofReal hA).of_le (WithTop.coe_le_coe.mpr le_top)
  exact (Work.Diff.STE.cm_contDiff_pdList q 1 _ h).differentiable (by norm_num)

/-- Differentiability of `∂^q` of `∂_c∂_d u`, for `q.length < k`. -/
lemma diff_pdList_pair {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
    (k : ℕ) (c d : ι) {q : List ι} (hq : q.length < k) :
    Differentiable ℝ (Work.Diff.STE.pdList q (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)) := by
  have h1 : ContDiff ℝ (↑(k + 2)) u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  exact Work.Diff.STE.cm_diff_pdList_pair k u h1 c d hq

/-- Differentiability of `∂^q` of the product `A · ∂_c∂_d u`. -/
lemma diff_pdList_mul2 {A : (ι → ℝ) → ℝ}
    (hA : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A)
    {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
    (k : ℕ) (c d : ι) {q : List ι} (hq : q.length < k) :
    Differentiable ℝ (Work.Diff.STE.pdList q (fun z => ((A z : ℝ) : ℂ)
        * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z)) := by
  have hF : ContDiff ℝ (↑(q.length + 1)) (fun y => ((A y : ℝ) : ℂ)) :=
    (contDiff_ofReal hA).of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 : ContDiff ℝ (↑([c, d].length + (q.length + 1))) u :=
    hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have h2 := Work.Diff.STE.cm_contDiff_pdList [c, d] (q.length + 1) u h1
  have hG : ContDiff ℝ (↑(q.length + 1))
      (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) := by
    simpa [Work.Diff.STE.pdList] using h2
  exact (Work.Diff.STE.cm_contDiff_pdList q 1 _ (hF.mul hG)).differentiable (by norm_num)

/-! ## The sharp product interpolation (self-contained proof)

We prove here the analytic input used by the main theorem, so that the file is self-contained.
The route is: Gagliardo–Nirenberg (`Work.Diff.STE.GN_torus`) for each factor separately, with
`L^{2m/α}` (resp. `L^{2m/β}`) norms whose Hölder exponents add up to `1/2` because
`α + β = m`; the sharp `S²` prefactor comes from the two sup bounds `‖f‖_∞, ‖g‖_∞ ≤ S`, and the
weighted AM–GM inequality `A^{α/m} B^{β/m} ≤ A + B` linearises the result. -/

/-- `x ^ θ ≤ max x 1` for `0 ≤ x`, `0 ≤ θ ≤ 1`. -/
private lemma rpow_le_max_one {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    x ^ θ ≤ max x 1 := by
  rcases le_total x 1 with h | h
  · have h1 : x ^ θ ≤ (1 : ℝ) ^ θ := Real.rpow_le_rpow hx h hθ0
    rw [Real.one_rpow] at h1
    exact h1.trans (le_max_right _ _)
  · have h1 : x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hθ1
    rw [Real.rpow_one] at h1
    exact h1.trans (le_max_left _ _)

/-- Weighted AM–GM in the form used below: `A ^ θ * B ^ (1 - θ) ≤ A + B`. -/
private lemma geom_mean_le_add {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : A ^ θ * B ^ (1 - θ) ≤ A + B := by
  have h1 : A ^ θ * B ^ (1 - θ) ≤ θ * A + (1 - θ) * B :=
    Real.geom_mean_le_arith_mean2_weighted hθ0 (by linarith) hA hB (by ring)
  have h2 : θ * A ≤ A := by nlinarith
  have h3 : (1 - θ) * B ≤ B := by nlinarith
  linarith

/-- `(a / b) * (b / a) = 1` for nonzero `a`, `b`. -/
private lemma div_mul_div_swap (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a / b) * (b / a) = 1 := by
  field_simp

/-! ## The sharp Gagliardo–Nirenberg inequality on the torus (clean chain)

We rebuild `Work.Diff.STE.GN_torus` here on top of the clean components that are being proved in
parallel (`GN/ibpRpowComplexClean`, `GN/gnLevStepOneClean`, `GN/gnLevStepGenClean`); the versions
below are placeholders with the same statements, to be replaced by the imports once the colleagues
have delivered.  The assembly (Nirenberg's discrete log-convexity `GN/discrete_convex` applied to
the level sequence `gnLev`) is copied from `GN_torus`. -/

section GNclean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Nirenberg recursion assembled from the two clean step lemmas. -/
private lemma gnSeq_step_clean (m : ℕ) (hm : 2 ≤ m)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f)
    (U : ℝ) (hU0 : 0 ≤ U) (hU : ∀ x : ι → ℝ, ‖f x‖ ≤ U)
    (hibp : ∀ (p : ℝ) (hp : 2 ≤ p) (g : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) g →
      Work.Diff.STE.Periodic1 g → ∀ i : ι,
      ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i g x‖ ^ p
        ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖g x‖ * ‖Work.Diff.STE.pd i g x‖ ^ (p - 2)
              * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖)
    {k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m) :
    (Work.Diff.STE.gnSeq (ι := ι) m U f k) ^ 2
      ≤ Work.Diff.STE.gnC (ι := ι) m k * Work.Diff.STE.gnSeq (ι := ι) m U f (k - 1)
        * Work.Diff.STE.gnSeq (ι := ι) m U f (k + 1) := by
  rcases eq_or_lt_of_le hk with h1 | h2
  · subst h1
    have hm1 : 1 ≤ m := by omega
    have hp1 : 2 ≤ Work.Diff.STE.gnP m 1 := Work.Diff.STE.gnP_two_le (m := m) (k := 1) le_rfl hm1
    have h := Work.Diff.STE.GN.gnLevStepOneClean m hm f hf hper U hU0 hU
      (fun i => hibp (Work.Diff.STE.gnP m 1) hp1 f hf hper i)
    rw [Work.Diff.STE.gnSeq_of_pos m U f (le_refl 1), Work.Diff.STE.gnSeq_zero,
      Work.Diff.STE.gnSeq_of_pos m U f (by norm_num : 1 ≤ 2)]
    exact h
  · obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    subst hk'
    have hk1 : 1 ≤ k' := by omega
    have hkm' : k' + 2 ≤ m := by omega
    have hp2 : 2 ≤ Work.Diff.STE.gnP m (k' + 1) :=
      Work.Diff.STE.gnP_two_le (m := m) (k := k' + 1) (by omega) (by omega)
    have h := Work.Diff.STE.GN.gnLevStepGenClean m hm f hf hper k' hk1 hkm'
      (fun g i hg hgper => hibp (Work.Diff.STE.gnP m (k' + 1)) hp2 g hg hgper i)
    rw [show k' + 1 - 1 = k' from by omega, show k' + 1 + 1 = k' + 2 from by omega]
    rw [Work.Diff.STE.gnSeq_of_pos m U f (by omega : 1 ≤ k' + 1),
      Work.Diff.STE.gnSeq_of_pos m U f hk1, Work.Diff.STE.gnSeq_of_pos m U f (by omega : 1 ≤ k' + 2)]
    exact h

/-- `ENormSq` is nonnegative (local copy of `Work.Diff.STE.GN_torus`'s helper). -/
private lemma ENormSq_nonneg_aux (m : ℕ) (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq m f :=
  Finset.sum_nonneg fun l _ => integral_nonneg fun x => pow_nonneg (norm_nonneg _) 2

/-- **The sharp Gagliardo–Nirenberg inequality on the torus**, with the integration by parts
supplied as a hypothesis. -/
private lemma GN_torus_clean_of_ibp (m : ℕ)
    (hibp : ∀ (p : ℝ) (hp : 2 ≤ p) (g : (ι → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) g →
      Work.Diff.STE.Periodic1 g → ∀ i : ι,
      ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i g x‖ ^ p
        ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖g x‖ * ‖Work.Diff.STE.pd i g x‖ ^ (p - 2)
              * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : ℝ) (f : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f → (∀ x : ι → ℝ, ‖f x‖ ≤ U) →
      ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (β : Fin j → ι),
        ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec j β f x‖ ^ ((2 * (m : ℝ)) / (j : ℝ))
          ≤ C * U ^ ((2 * (m : ℝ)) / (j : ℝ) - 2) * Work.Diff.STE.ENormSq m f := by
  classical
  rcases Nat.lt_or_ge m 2 with hm01 | hm2
  · rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      refine ⟨0, le_refl 0, ?_⟩
      intro U f hf hper hU j hj hjm β
      exfalso
      omega
    · have hm1 : m = 1 := by omega
      subst hm1
      refine ⟨1, zero_le_one, ?_⟩
      intro U f hf hper hU j hj hjm β
      have hj1 : j = 1 := by omega
      subst hj1
      have hsingle : ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec 1 β f x‖ ^ ((2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ))
          ≤ Work.Diff.STE.ENormSq 1 f := by
        have hcongr : (∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec 1 β f x‖ ^ ((2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ)))
            = ∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec 1 β f x‖ ^ (2 : ℕ) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [show (2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) = 2 by norm_num]
          exact Real.rpow_natCast _ _
        rw [hcongr, Work.Diff.STE.ENormSq]
        have hnn : ∀ l : Fin 1 → ι,
            0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec 1 l f x‖ ^ (2 : ℕ) :=
          fun l => integral_nonneg fun x => by positivity
        exact Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ β)
      refine le_trans hsingle ?_
      rw [show (2 * ((1 : ℕ) : ℝ)) / ((1 : ℕ) : ℝ) - 2 = 0 by norm_num, Real.rpow_zero]
      exact le_of_eq (by ring)
  · obtain ⟨K, hK0, hK⟩ :=
      Work.Diff.STE.GN.discrete_convex m (Work.Diff.STE.gnC (ι := ι) m)
        (Work.Diff.STE.gnC_nonneg (ι := ι) m)
    refine ⟨(max K 1) ^ (2 * (m : ℝ)), Real.rpow_nonneg (by linarith [le_max_right K 1]) _, ?_⟩
    intro U f hf hper hU j hj hjm β
    by_cases hUneg : U < 0
    · exfalso
      have h3 : ‖f 0‖ ≤ U := hU 0
      have h4 : (0 : ℝ) ≤ ‖f 0‖ := norm_nonneg _
      linarith
    have hU0 : 0 ≤ U := le_of_not_gt hUneg
    have hstep : ∀ k, 1 ≤ k → k + 1 ≤ m →
        (Work.Diff.STE.gnSeq (ι := ι) m U f k) ^ 2
          ≤ Work.Diff.STE.gnC (ι := ι) m k * Work.Diff.STE.gnSeq (ι := ι) m U f (k - 1)
            * Work.Diff.STE.gnSeq (ι := ι) m U f (k + 1) :=
      fun k hk hkm => gnSeq_step_clean m hm2 f hf hper U hU0 hU hibp hk hkm
    have hmain := hK (Work.Diff.STE.gnSeq (ι := ι) m U f)
      (Work.Diff.STE.gnSeq_nonneg m hU0 f) hstep j hjm
    rw [Work.Diff.STE.gnSeq_zero, Work.Diff.STE.gnSeq_of_pos m U f hj,
      Work.Diff.STE.gnSeq_of_pos m U f (by omega : 1 ≤ m)] at hmain
    have hL2 : (Work.Diff.STE.gnLev (ι := ι) m f m) ^ (2 : ℝ) = Work.Diff.STE.ENormSq m f := by
      rw [← Work.Diff.STE.gnP_self m (by omega : 1 ≤ m)]
      rw [Work.Diff.STE.gnLev_rpow m f (by omega : 1 ≤ m) (le_refl m)]
      rw [Work.Diff.STE.gnP_self m (by omega : 1 ≤ m)]
      rw [Work.Diff.STE.ENormSq]
      refine Finset.sum_congr rfl fun l _ => ?_
      refine integral_congr_ae ?_
      filter_upwards with x
      exact Real.rpow_natCast _ _
    set q : ℝ := (2 * (m : ℝ)) / (j : ℝ) with hq
    have hqeq : q = Work.Diff.STE.gnP m j := by rw [hq, Work.Diff.STE.gnP]
    have hq0 : 0 ≤ q := by
      rw [hq]
      have hj0 : (0 : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j)
      exact div_nonneg (by positivity) (le_of_lt hj0)
    have hqM : q ≤ 2 * (m : ℝ) := by
      rw [hq]
      have hj0 : (0 : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j)
      rw [div_le_iff₀ hj0]
      have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj
      nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
    have hsingle : ∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖Work.Diff.STE.pdVec j β f x‖ ^ q ≤ (Work.Diff.STE.gnLev (ι := ι) m f j) ^ q := by
      rw [hqeq, Work.Diff.STE.gnLev_rpow m f hj hjm]
      have hnn : ∀ l : Fin j → ι,
          0 ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec j l f x‖ ^ (Work.Diff.STE.gnP m j) :=
        fun l => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
      exact Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ β)
    have hstep2 : (Work.Diff.STE.gnLev (ι := ι) m f j) ^ q ≤
        (K * U ^ (1 - (j : ℝ) / m) * (Work.Diff.STE.gnLev (ι := ι) m f m) ^ ((j : ℝ) / m)) ^ q :=
      Real.rpow_le_rpow (Work.Diff.STE.gnLev_nonneg m f j) hmain hq0
    have hexp : (K * U ^ (1 - (j : ℝ) / m)
          * (Work.Diff.STE.gnLev (ι := ι) m f m) ^ ((j : ℝ) / m)) ^ q
        = K ^ q * U ^ (q - 2) * Work.Diff.STE.ENormSq m f := by
      rw [show K * U ^ (1 - (j : ℝ) / m) * (Work.Diff.STE.gnLev (ι := ι) m f m) ^ ((j : ℝ) / m)
            = (K * U ^ (1 - (j : ℝ) / m)) * (Work.Diff.STE.gnLev (ι := ι) m f m) ^ ((j : ℝ) / m)
          from by ring]
      rw [Real.mul_rpow (mul_nonneg hK0 (Real.rpow_nonneg hU0 _))
            (Real.rpow_nonneg (Work.Diff.STE.gnLev_nonneg m f m) _),
          Real.mul_rpow hK0 (Real.rpow_nonneg hU0 _),
          ← Real.rpow_mul hU0, ← Real.rpow_mul (Work.Diff.STE.gnLev_nonneg m f m)]
      rw [show (1 - (j : ℝ) / m) * q = q - 2 from by
            rw [hqeq]; exact (Work.Diff.STE.gnP_endpoint m j hj hjm).1,
          show ((j : ℝ) / m) * q = 2 from by
            rw [hqeq]; exact (Work.Diff.STE.gnP_endpoint m j hj hjm).2,
          hL2]
    have hKbound : K ^ q ≤ (max K 1) ^ (2 * (m : ℝ)) := by
      refine le_trans (Real.rpow_le_rpow hK0 (le_max_left K 1) hq0) ?_
      exact Real.rpow_le_rpow_of_exponent_le (le_max_right K 1) hqM
    have hENN : 0 ≤ Work.Diff.STE.ENormSq m f := ENormSq_nonneg_aux m f
    have hUU : 0 ≤ U ^ (q - 2) := Real.rpow_nonneg hU0 _
    calc ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j β f x‖ ^ q
        ≤ (Work.Diff.STE.gnLev (ι := ι) m f j) ^ q := hsingle
      _ ≤ (K * U ^ (1 - (j : ℝ) / m)
            * (Work.Diff.STE.gnLev (ι := ι) m f m) ^ ((j : ℝ) / m)) ^ q := hstep2
      _ = K ^ q * U ^ (q - 2) * Work.Diff.STE.ENormSq m f := hexp
      _ ≤ (max K 1) ^ (2 * (m : ℝ)) * U ^ (q - 2) * Work.Diff.STE.ENormSq m f := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hKbound hUU
          · exact hENN

/-- The sharp Gagliardo–Nirenberg inequality on the torus (clean). -/
private lemma GN_torus_clean (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : ℝ) (f : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f → (∀ x : ι → ℝ, ‖f x‖ ≤ U) →
      ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (β : Fin j → ι),
        ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec j β f x‖ ^ ((2 * (m : ℝ)) / (j : ℝ))
          ≤ C * U ^ ((2 * (m : ℝ)) / (j : ℝ) - 2) * Work.Diff.STE.ENormSq m f :=
  GN_torus_clean_of_ibp m (fun p hp g hg hper i =>
    Work.Diff.STE.GN.ibpRpowComplexClean i p hp g hg hper)

end GNclean

lemma prod_interp_le_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f g : (ι → ℝ) → ℂ) (S A B : ℝ)
        (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
        (hg : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) g)
        (hfp : Work.Diff.STE.Periodic1 f) (hgp : Work.Diff.STE.Periodic1 g)
        (hS : 0 ≤ S) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
        (hfs : ∀ x : ι → ℝ, ‖f x‖ ≤ S) (hgs : ∀ x : ι → ℝ, ‖g x‖ ≤ S)
        (hfe : Work.Diff.STE.ENormSq m f ≤ A) (hge : Work.Diff.STE.ENormSq m g ≤ B),
        ∀ (α β : ℕ) (hαβ : α + β = m) (a : Fin α → ι) (b : Fin β → ι),
          ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2
            ≤ C * (S ^ 2 * (A + B)) := by
  classical
  obtain ⟨CG, hCG0, hCG⟩ := GN_torus_clean (ι := ι) m
  refine ⟨(max CG 1 + 1) * (max CG 1 + 1), by positivity, ?_⟩
  have hC1 : (1 : ℝ) ≤ (max CG 1 + 1) * (max CG 1 + 1) := by
    have h := le_max_right CG 1
    nlinarith
  intro f g S A B hf hg hfp hgp hS hA0 hB0 hfs hgs hfe hge α β hαβ a b
  have hcontF : Continuous (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x‖ ^ 2) :=
    ((Work.Diff.STE.cm_contDiff_pdList (List.ofFn a) 0 f
      (hf.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.norm).pow 2
  have hcontG : Continuous (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec β b g x‖ ^ 2) :=
    ((Work.Diff.STE.cm_contDiff_pdList (List.ofFn b) 0 g
      (hg.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.norm).pow 2
  -- the common final step: `Y ≤ C * (S^2 * (A + B))` for `Y ≤ S^2 * Z`, `Z ≤ A + B`
  have htail : ∀ Y Z : ℝ, Y ≤ S ^ 2 * Z → Z ≤ A + B →
      Y ≤ (max CG 1 + 1) * (max CG 1 + 1) * (S ^ 2 * (A + B)) := by
    intro Y Z hYZ hZ
    have h1 : S ^ 2 * Z ≤ S ^ 2 * (A + B) := mul_le_mul_of_nonneg_left hZ (sq_nonneg S)
    have h2 : S ^ 2 * (A + B)
        ≤ (max CG 1 + 1) * (max CG 1 + 1) * (S ^ 2 * (A + B)) := by
      have h3 : (1 : ℝ) * (S ^ 2 * (A + B))
          ≤ ((max CG 1 + 1) * (max CG 1 + 1)) * (S ^ 2 * (A + B)) :=
        mul_le_mul_of_nonneg_right hC1 (by positivity)
      linarith
    linarith
  rcases Nat.eq_zero_or_pos α with hα0 | hα1
  · -- ## `α = 0`: only the sup bound on `f` and the energy of `g` are used
    have hβm : β = m := by omega
    rw [← hβm] at hge
    have hof : (List.ofFn a : List ι) = [] := List.ofFn_eq_nil_iff.mpr hα0
    have hpd : Work.Diff.STE.pdVec α a f = f := by
      simp only [Work.Diff.STE.pdVec, hof, Work.Diff.STE.pdList, List.foldr_nil]
    rw [show (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
        = fun x : ι → ℝ => ‖f x‖ ^ 2 * ‖Work.Diff.STE.pdVec β b g x‖ ^ 2 from by
      funext x
      rw [show Work.Diff.STE.pdVec α a f x = f x from congrFun hpd x, norm_mul, mul_pow]]
    refine htail _ (Work.Diff.STE.ENormSq β g) ?_ ?_
    · calc ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖f x‖ ^ 2 * ‖Work.Diff.STE.pdVec β b g x‖ ^ 2
          ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι),
              S ^ 2 * ‖Work.Diff.STE.pdVec β b g x‖ ^ 2 := by
            refine integral_mono_of_nonneg ?_ ?_ ?_
            · filter_upwards with x; positivity
            · exact Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
                (continuous_const.mul hcontG)
            · filter_upwards with x
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hfs x) 2)
                (by positivity)
        _ = S ^ 2 * ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec β b g x‖ ^ 2 := by
            rw [integral_const_mul]
        _ ≤ S ^ 2 * Work.Diff.STE.ENormSq β g := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg S)
            have h := Work.Diff.STE.cm_integral_pdList_le_ENormSq (List.ofFn b) g
            simpa [Work.Diff.STE.pdVec] using h
    · exact le_trans hge (by linarith)
  · rcases Nat.eq_zero_or_pos β with hβ0 | hβ1
    · -- ## `β = 0`: symmetric
      have hαm : α = m := by omega
      rw [← hαm] at hfe
      have hof : (List.ofFn b : List ι) = [] := List.ofFn_eq_nil_iff.mpr hβ0
      have hpd : Work.Diff.STE.pdVec β b g = g := by
        simp only [Work.Diff.STE.pdVec, hof, Work.Diff.STE.pdList, List.foldr_nil]
      rw [show (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
          = fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x‖ ^ 2 * ‖g x‖ ^ 2 from by
        funext x
        rw [show Work.Diff.STE.pdVec β b g x = g x from congrFun hpd x, norm_mul, mul_pow]]
      refine htail _ (Work.Diff.STE.ENormSq α f) ?_ ?_
      · calc ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x‖ ^ 2 * ‖g x‖ ^ 2
            ≤ ∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec α a f x‖ ^ 2 * S ^ 2 := by
              refine integral_mono_of_nonneg ?_ ?_ ?_
              · filter_upwards with x; positivity
              · exact Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
                  (hcontF.mul continuous_const)
              · filter_upwards with x
                exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgs x) 2)
                  (by positivity)
          _ = (∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec α a f x‖ ^ 2) * S ^ 2 := by
              rw [integral_mul_const]
          _ ≤ Work.Diff.STE.ENormSq α f * S ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg S)
              have h := Work.Diff.STE.cm_integral_pdList_le_ENormSq (List.ofFn a) f
              simpa [Work.Diff.STE.pdVec] using h
          _ = S ^ 2 * Work.Diff.STE.ENormSq α f := by ring
      · exact le_trans hfe (by linarith)
    · -- ## `α, β ≥ 1`: sharp interpolation between the two energies
      have hαm : α ≤ m := by omega
      have hβm : β ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      have hαR : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα1
      have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ1
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hαne : (α : ℝ) ≠ 0 := ne_of_gt hαR
      have hβne : (β : ℝ) ≠ 0 := ne_of_gt hβR
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
      have hθ0 : 0 ≤ (α : ℝ) / (m : ℝ) := by positivity
      have hθ1 : (α : ℝ) / (m : ℝ) ≤ 1 := by
        rw [div_le_one hmR]; exact_mod_cast hαm
      have hφ0 : 0 ≤ (β : ℝ) / (m : ℝ) := by positivity
      have hφ1 : (β : ℝ) / (m : ℝ) ≤ 1 := by
        rw [div_le_one hmR]; exact_mod_cast hβm
      have hsum : (α : ℝ) / (m : ℝ) + (β : ℝ) / (m : ℝ) = 1 := by
        rw [← add_div, ← Nat.cast_add, hαβ, div_self hmne]
      have hφeq : (β : ℝ) / (m : ℝ) = 1 - (α : ℝ) / (m : ℝ) := by linarith
      -- Hölder's inequality with the exponents `m/α`, `m/β`
      have hbE1 : 1 ≤ (m : ℝ) / (α : ℝ) := by
        rw [le_div_iff₀ hαR, one_mul]; exact_mod_cast hαm
      have hcE1 : 1 ≤ (m : ℝ) / (β : ℝ) := by
        rw [le_div_iff₀ hβR, one_mul]; exact_mod_cast hβm
      have hone : 1 / ((m : ℝ) / (α : ℝ)) = (α : ℝ) / (m : ℝ) := one_div_div _ _
      have hone' : 1 / ((m : ℝ) / (β : ℝ)) = (β : ℝ) / (m : ℝ) := one_div_div _ _
      have hbc : 1 / ((m : ℝ) / (α : ℝ)) + 1 / ((m : ℝ) / (β : ℝ)) = 1 := by
        rw [hone, hone']; exact hsum
      have hHolder := Work.Diff.STE.GN.holder2_int ((m : ℝ) / (α : ℝ)) ((m : ℝ) / (β : ℝ))
          hbE1 hcE1 hbc
          (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec α a f x‖ ^ 2)
          (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec β b g x‖ ^ 2)
          hcontF hcontG (fun x => by positivity) (fun x => by positivity)
      have hLHS : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
          = ∫ x in Work.Diff.STE.unitCube (ι := ι),
              (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) * (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [norm_mul, mul_pow]
      -- ### the `f`-factor
      have hFbase : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) ^ ((m : ℝ) / (α : ℝ)))
          = ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ)) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [show (‖Work.Diff.STE.pdVec α a f x‖ ^ (2 : ℕ) : ℝ)
              = ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 : ℝ) from (Real.rpow_natCast _ 2).symm]
        rw [← Real.rpow_mul (norm_nonneg _) 2 ((m : ℝ) / (α : ℝ))]
        congr 1
        ring
      have hGNf : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ)))
          ≤ CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A := by
        have h := hCG S f hf hfp hfs α hα1 hαm a
        exact h.trans (mul_le_mul_of_nonneg_left hfe (by positivity))
      have hexp1 : (2 * (m : ℝ) / (α : ℝ) - 2) * ((α : ℝ) / (m : ℝ))
          = 2 - 2 * ((α : ℝ) / (m : ℝ)) := by
        calc (2 * (m : ℝ) / (α : ℝ) - 2) * ((α : ℝ) / (m : ℝ))
            = 2 * (((m : ℝ) / (α : ℝ)) * ((α : ℝ) / (m : ℝ))) - 2 * ((α : ℝ) / (m : ℝ)) := by
              ring
          _ = 2 * 1 - 2 * ((α : ℝ) / (m : ℝ)) := by
              rw [div_mul_div_swap (m : ℝ) (α : ℝ) hmne hαne]
          _ = 2 - 2 * ((α : ℝ) / (m : ℝ)) := by ring
      have hstepF : (CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A) ^ ((α : ℝ) / (m : ℝ))
          = CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
              * A ^ ((α : ℝ) / (m : ℝ)) := by
        rw [Real.mul_rpow (mul_nonneg hCG0 (Real.rpow_nonneg hS _)) hA0,
            Real.mul_rpow hCG0 (Real.rpow_nonneg hS _)]
        rw [← Real.rpow_mul hS (2 * (m : ℝ) / (α : ℝ) - 2) ((α : ℝ) / (m : ℝ))]
        rw [hexp1]
      have hstepF2 : CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
            * A ^ ((α : ℝ) / (m : ℝ))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) := by
        have hle := rpow_le_max_one hCG0 hθ0 hθ1
        have h1 : (0 : ℝ) ≤ S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) := Real.rpow_nonneg hS _
        have h2 : (0 : ℝ) ≤ A ^ ((α : ℝ) / (m : ℝ)) := Real.rpow_nonneg hA0 _
        calc CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
                * A ^ ((α : ℝ) / (m : ℝ))
            = CG ^ ((α : ℝ) / (m : ℝ))
                * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) := by ring
          _ ≤ (max CG 1)
                * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg h1 h2)
      have hFb : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) ^ ((m : ℝ) / (α : ℝ))) ^ (1 / ((m : ℝ) / (α : ℝ)))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) := by
        have hstep1 : (∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ))) ^ ((α : ℝ) / (m : ℝ))
            ≤ (CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A) ^ ((α : ℝ) / (m : ℝ)) :=
          Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hGNf
            (by positivity)
        calc (∫ x in Work.Diff.STE.unitCube (ι := ι),
              (‖Work.Diff.STE.pdVec α a f x‖ ^ 2) ^ ((m : ℝ) / (α : ℝ))) ^ (1 / ((m : ℝ) / (α : ℝ)))
            = (∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec α a f x‖ ^ (2 * (m : ℝ) / (α : ℝ))) ^ ((α : ℝ) / (m : ℝ)) := by
              rw [hFbase, hone]
          _ ≤ (CG * S ^ (2 * (m : ℝ) / (α : ℝ) - 2) * A) ^ ((α : ℝ) / (m : ℝ)) := hstep1
          _ = CG ^ ((α : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((α : ℝ) / (m : ℝ)))
                * A ^ ((α : ℝ) / (m : ℝ)) := hstepF
          _ ≤ (max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))) :=
              hstepF2
      -- ### the `g`-factor
      have hGbase : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) ^ ((m : ℝ) / (β : ℝ)))
          = ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ)) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        rw [show (‖Work.Diff.STE.pdVec β b g x‖ ^ (2 : ℕ) : ℝ)
              = ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 : ℝ) from (Real.rpow_natCast _ 2).symm]
        rw [← Real.rpow_mul (norm_nonneg _) 2 ((m : ℝ) / (β : ℝ))]
        congr 1
        ring
      have hGNg : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ)))
          ≤ CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B := by
        have h := hCG S g hg hgp hgs β hβ1 hβm b
        exact h.trans (mul_le_mul_of_nonneg_left hge (by positivity))
      have hexp2 : (2 * (m : ℝ) / (β : ℝ) - 2) * ((β : ℝ) / (m : ℝ))
          = 2 - 2 * ((β : ℝ) / (m : ℝ)) := by
        calc (2 * (m : ℝ) / (β : ℝ) - 2) * ((β : ℝ) / (m : ℝ))
            = 2 * (((m : ℝ) / (β : ℝ)) * ((β : ℝ) / (m : ℝ))) - 2 * ((β : ℝ) / (m : ℝ)) := by
              ring
          _ = 2 * 1 - 2 * ((β : ℝ) / (m : ℝ)) := by
              rw [div_mul_div_swap (m : ℝ) (β : ℝ) hmne hβne]
          _ = 2 - 2 * ((β : ℝ) / (m : ℝ)) := by ring
      have hstepG : (CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B) ^ ((β : ℝ) / (m : ℝ))
          = CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
              * B ^ ((β : ℝ) / (m : ℝ)) := by
        rw [Real.mul_rpow (mul_nonneg hCG0 (Real.rpow_nonneg hS _)) hB0,
            Real.mul_rpow hCG0 (Real.rpow_nonneg hS _)]
        rw [← Real.rpow_mul hS (2 * (m : ℝ) / (β : ℝ) - 2) ((β : ℝ) / (m : ℝ))]
        rw [hexp2]
      have hstepG2 : CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
            * B ^ ((β : ℝ) / (m : ℝ))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) := by
        have hle := rpow_le_max_one hCG0 hφ0 hφ1
        have h1 : (0 : ℝ) ≤ S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) := Real.rpow_nonneg hS _
        have h2 : (0 : ℝ) ≤ B ^ ((β : ℝ) / (m : ℝ)) := Real.rpow_nonneg hB0 _
        calc CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
                * B ^ ((β : ℝ) / (m : ℝ))
            = CG ^ ((β : ℝ) / (m : ℝ))
                * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) := by ring
          _ ≤ (max CG 1)
                * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg h1 h2)
      have hGb : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) ^ ((m : ℝ) / (β : ℝ))) ^ (1 / ((m : ℝ) / (β : ℝ)))
          ≤ (max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) := by
        have hstep1 : (∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ))) ^ ((β : ℝ) / (m : ℝ))
            ≤ (CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B) ^ ((β : ℝ) / (m : ℝ)) :=
          Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hGNg
            (by positivity)
        calc (∫ x in Work.Diff.STE.unitCube (ι := ι),
              (‖Work.Diff.STE.pdVec β b g x‖ ^ 2) ^ ((m : ℝ) / (β : ℝ))) ^ (1 / ((m : ℝ) / (β : ℝ)))
            = (∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec β b g x‖ ^ (2 * (m : ℝ) / (β : ℝ))) ^ ((β : ℝ) / (m : ℝ)) := by
              rw [hGbase, hone']
          _ ≤ (CG * S ^ (2 * (m : ℝ) / (β : ℝ) - 2) * B) ^ ((β : ℝ) / (m : ℝ)) := hstep1
          _ = CG ^ ((β : ℝ) / (m : ℝ)) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
                * B ^ ((β : ℝ) / (m : ℝ)) := hstepG
          _ ≤ (max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))) :=
              hstepG2
      -- ### assembly
      have hAMGM : A ^ ((α : ℝ) / (m : ℝ)) * B ^ ((β : ℝ) / (m : ℝ)) ≤ A + B := by
        have h := geom_mean_le_add hA0 hB0 hθ0 hθ1
        rw [← hφeq] at h
        exact h
      have hScomb : S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
          = S ^ 2 := by
        have h2 : (2 - 2 * ((α : ℝ) / (m : ℝ))) + (2 - 2 * ((β : ℝ) / (m : ℝ))) = 2 := by
          linarith [hsum]
        have hne : (2 - 2 * ((α : ℝ) / (m : ℝ))) + (2 - 2 * ((β : ℝ) / (m : ℝ))) ≠ 0 := by
          rw [h2]; norm_num
        calc S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ)))
            = S ^ ((2 - 2 * ((α : ℝ) / (m : ℝ))) + (2 - 2 * ((β : ℝ) / (m : ℝ)))) :=
              (Real.rpow_add' hS hne).symm
          _ = S ^ (2 : ℝ) := by rw [h2]
          _ = S ^ 2 := Real.rpow_natCast _ 2
      have hBound : (∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖Work.Diff.STE.pdVec α a f x * Work.Diff.STE.pdVec β b g x‖ ^ 2)
          ≤ ((max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))))
            * ((max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ)))) := by
        rw [hLHS]
        exact hHolder.trans (mul_le_mul hFb hGb (by positivity) (by positivity))
      refine hBound.trans ?_
      have hmax0 : (0 : ℝ) ≤ max CG 1 := le_trans hCG0 (le_max_left CG 1)
      calc ((max CG 1) * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * A ^ ((α : ℝ) / (m : ℝ))))
            * ((max CG 1) * (S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))) * B ^ ((β : ℝ) / (m : ℝ))))
          = ((max CG 1) * (max CG 1))
              * (S ^ (2 - 2 * ((α : ℝ) / (m : ℝ))) * S ^ (2 - 2 * ((β : ℝ) / (m : ℝ))))
              * (A ^ ((α : ℝ) / (m : ℝ)) * B ^ ((β : ℝ) / (m : ℝ))) := by ring
        _ = ((max CG 1) * (max CG 1)) * S ^ 2
              * (A ^ ((α : ℝ) / (m : ℝ)) * B ^ ((β : ℝ) / (m : ℝ))) := by
            rw [hScomb]
        _ ≤ ((max CG 1) * (max CG 1)) * S ^ 2 * (A + B) := by
            have h1 : (0 : ℝ) ≤ ((max CG 1) * (max CG 1)) * S ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left hAMGM h1
        _ ≤ ((max CG 1 + 1) * (max CG 1 + 1)) * (S ^ 2 * (A + B)) := by
            have h1 : (max CG 1) * (max CG 1) ≤ (max CG 1 + 1) * (max CG 1 + 1) := by
              nlinarith [hmax0]
            have h2 : (0 : ℝ) ≤ S ^ 2 * (A + B) := by positivity
            calc ((max CG 1) * (max CG 1)) * S ^ 2 * (A + B)
                = ((max CG 1) * (max CG 1)) * (S ^ 2 * (A + B)) := by ring
              _ ≤ ((max CG 1 + 1) * (max CG 1 + 1)) * (S ^ 2 * (A + B)) :=
                  mul_le_mul_of_nonneg_right h1 h2

/-! ## The main theorem -/

theorem pdVec_defect_sharp {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ι → ι → (ι → ℝ) → ℝ) (u : (ι → ℝ) → ℂ) (KA S Q1 : ℝ)
        (hA : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
        (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
        (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
        (hup : Work.Diff.STE.Periodic1 u)
        (hKA : 0 ≤ KA) (hS : 0 ≤ S) (hQ1 : 0 ≤ Q1)
        (hk : Fintype.card ι + 4 ≤ k),
        (∀ (z : ι → ℝ) (c d : ι), |A c d z| ≤ S) →
        (∀ (z : ι → ℝ) (r c d : ι),
          |Work.Diff.STE.pdR r (fun y : ι → ℝ => A c d y) z| ≤ S) →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → ι) (c d : ι),
          Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
            (fun y : ι → ℝ => ((A c d y : ℝ) : ℂ))) ≤ KA) →
        (∀ (m : ℕ) (hm : m ≤ 2) (β : Fin m → ι) (z : ι → ℝ),
          ‖Work.Diff.STE.pdVec m β u z‖ ≤ S) →
        (∀ β : Fin (k + 1) → ι,
          Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (k + 1) β u) ≤ Q1) →
        ∀ l : Fin k → ι,
          Work.Diff.STE.ENormSq 0 (fun z : ι → ℝ =>
              Work.Diff.STE.pdVec k l
                  (fun y : ι → ℝ => ∑ c, ∑ d,
                    ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
                - ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                    * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
            ≤ C * (S ^ 2 * (1 + KA + Q1)) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- the index type is empty: `Fin k → ι` is empty since `k ≥ 4`
    refine ⟨0, le_rfl, ?_⟩
    intro A u KA S Q1 hA hAper hu hup hKA hS hQ1 hk h1 h2 h3 h4 h5 l
    exact (hι.false (l ⟨0, by omega⟩)).elim
  · obtain ⟨Cint, hCint0, hCint⟩ := prod_interp_le_aux (ι := ι) (k - 1)
    set N : ℝ := (Fintype.card ι : ℝ) ^ 2 * 2 ^ k with hN
    refine ⟨N * N * Cint * (Fintype.card ι : ℝ) ^ (k - 1), by positivity, ?_⟩
    intro A u KA S Q1 hA hAper hu hup hKA hS hQ1 hk hsupA hsupdA henA hsupu henU l
    have hk1 : 1 ≤ k := by omega
    -- the list of Leibniz splits
    set Sf : List (List ι × List ι) :=
      (Work.Diff.STE.splits (List.ofFn l)).filter (fun p => decide (p.1 ≠ [])) with hSf
    -- the individual terms of the Leibniz expansion
    let T : ι × ι × Fin Sf.length → (ι → ℝ) → ℂ := fun q z =>
      Work.Diff.STE.pdList (Sf.get q.2.2).1 (fun y => ((A q.1 q.2.1 y : ℝ) : ℂ)) z
        * Work.Diff.STE.pdList (Sf.get q.2.2).2
            (fun y => Work.Diff.STE.pd q.1 (Work.Diff.STE.pd q.2.1 u) y) z
    -- ## the bound for a single Leibniz term
    have hterm : ∀ (c d : ι) (p : List ι × List ι), p ∈ Sf →
        ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdList p.1 (fun y => ((A c d y : ℝ) : ℂ)) x
              * Work.Diff.STE.pdList p.2
                  (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) x‖ ^ 2
          ≤ Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * KA
              + (Fintype.card ι : ℝ) ^ (k - 1) * Q1)) := by
      intro c d p hp
      rw [hSf] at hp
      obtain ⟨hp_splits, hp_ne⟩ := List.mem_filter.mp hp
      have hne : p.1 ≠ [] := of_decide_eq_true hp_ne
      have hlen : p.1.length + p.2.length = k := by
        have h := Work.Diff.STE.cm_splits_mem_length (List.ofFn l) p hp_splits
        simpa using h
      have hq1 : p.1.dropLast ++ [p.1.getLast hne] = p.1 := List.dropLast_append_getLast hne
      have hlen1 : p.1.dropLast.length + 1 = p.1.length := by
        have h := congrArg List.length hq1
        simpa using h
      have hαβ : p.1.dropLast.length + p.2.length = k - 1 := by omega
      have hpd1 : Work.Diff.STE.pdList p.1 (fun y => ((A c d y : ℝ) : ℂ))
          = Work.Diff.STE.pdList p.1.dropLast
              (Work.Diff.STE.pd (p.1.getLast hne) (fun y => ((A c d y : ℝ) : ℂ))) := by
        conv_lhs => rw [← hq1]
        rw [Work.Diff.STE.cm_pdList_append]
        rfl
      have hpd2 : Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
          = Work.Diff.STE.pdVec p.2.length (fun i => p.2.get i)
              (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) :=
        Work.Diff.STE.Lead.Gal.pdList_eq_pdVec_gal p.2 _
      have hfs : ∀ x : ι → ℝ,
          ‖Work.Diff.STE.pd (p.1.getLast hne) (fun y => ((A c d y : ℝ) : ℂ)) x‖ ≤ S := by
        intro x
        have hdiff : DifferentiableAt ℝ (A c d) x :=
          ((hA c d).differentiable (by simp)).differentiableAt
        rw [Work.Diff.STE.ga_pd_ofReal _ _ x hdiff]
        simpa using hsupdA x (p.1.getLast hne) c d
      have hgs : ∀ x : ι → ℝ, ‖Work.Diff.STE.pd c (Work.Diff.STE.pd d u) x‖ ≤ S := by
        intro x
        have h := hsupu 2 (by norm_num) (Fin.cons c (Fin.cons d (Fin.elim0 : Fin 0 → ι))) x
        simpa [Work.Diff.STE.pdVec, Work.Diff.STE.pdList] using h
      have hmain := hCint
        (Work.Diff.STE.pd (p.1.getLast hne) (fun y => ((A c d y : ℝ) : ℂ)))
        (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
        S ((Fintype.card ι : ℝ) ^ (k - 1) * KA) ((Fintype.card ι : ℝ) ^ (k - 1) * Q1)
        (contDiff_pd_top (contDiff_ofReal (hA c d)) (p.1.getLast hne))
        (contDiff_pd_top (contDiff_pd_top hu d) c)
        (periodic1_pd (contDiff_ofReal (hA c d)) (periodic1_ofReal (hAper c d))
          (p.1.getLast hne))
        (periodic1_pd (contDiff_pd_top hu d) (periodic1_pd hu hup d) c)
        hS (by positivity) (by positivity)
        hfs hgs
        (ENormSq_pd_le k hk1 (fun y => ((A c d y : ℝ) : ℂ)) (p.1.getLast hne) KA hKA
          (fun β => henA k le_rfl β c d))
        (ENormSq_pd_pd_le k hk1 u c d Q1 hQ1 henU)
        (p.1.dropLast.length) (p.2.length) hαβ
        (fun i => (p.1.dropLast).get i) (fun i => p.2.get i)
      have hfun : (fun x : ι → ℝ => ‖Work.Diff.STE.pdList p.1 (fun y => ((A c d y : ℝ) : ℂ)) x
              * Work.Diff.STE.pdList p.2 (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) x‖ ^ 2)
          = fun x : ι → ℝ => ‖Work.Diff.STE.pdVec (p.1.dropLast.length)
                (fun i => (p.1.dropLast).get i)
                (Work.Diff.STE.pd (p.1.getLast hne) (fun y => ((A c d y : ℝ) : ℂ))) x
              * Work.Diff.STE.pdVec (p.2.length) (fun i => p.2.get i)
                (fun y => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) x‖ ^ 2 := by
        funext x
        rw [hpd1, hpd2, Work.Diff.STE.Lead.Gal.pdList_eq_pdVec_gal]
      rw [hfun]
      exact hmain
    -- ## the pointwise Leibniz expansion
    have hident : (fun z : ι → ℝ =>
          Work.Diff.STE.pdVec k l (fun y : ι → ℝ => ∑ c, ∑ d,
              ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
            - ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
        = fun z : ι → ℝ => ∑ q : ι × ι × Fin Sf.length, T q z := by
      funext z
      have hfun1 : (fun y : ι → ℝ => ∑ c, ∑ d,
            ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
          = fun y : ι → ℝ => ∑ p : ι × ι,
            ((A p.1 p.2 y : ℝ) : ℂ) * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y := by
        funext y
        rw [← Finset.univ_product_univ, Finset.sum_product]
      have hlin : Work.Diff.STE.pdVec k l (fun y : ι → ℝ => ∑ c, ∑ d,
            ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y)
          = fun y : ι → ℝ => ∑ p : ι × ι, Work.Diff.STE.pdVec k l
              (fun z' : ι → ℝ => ((A p.1 p.2 z' : ℝ) : ℂ)
                * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) z') y := by
        rw [hfun1]
        have hsum := Work.Diff.STE.cm_pdList_sum (List.ofFn l) (Finset.univ : Finset (ι × ι))
            (fun p : ι × ι => fun z' : ι → ℝ => ((A p.1 p.2 z' : ℝ) : ℂ)
              * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) z')
            (fun p _ q _ hlen => diff_pdList_mul2 (hA p.1 p.2) hu k p.1 p.2 (by simpa using hlen))
        simpa [Work.Diff.STE.pdVec] using hsum
      have hsub : (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
            * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
          = ∑ p : ι × ι, ((A p.1 p.2 z : ℝ) : ℂ) * Work.Diff.STE.pdVec k l
              (fun y : ι → ℝ => Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z := by
        have hcd : ∀ c d : ι, ((A c d z : ℝ) : ℂ)
              * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z
            = ((A c d z : ℝ) : ℂ) * Work.Diff.STE.pdVec k l
                (fun y : ι → ℝ => Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z := by
          intro c d
          rw [← Work.Diff.STE.cm_pdVec_pd_pd k l c d u
            (hu.of_le (WithTop.coe_le_coe.mpr le_top))]
        simp only [hcd]
        rw [← Finset.univ_product_univ, Finset.sum_product]
      have hterm_eq : ∀ p : ι × ι, Work.Diff.STE.pdVec k l
            (fun y : ι → ℝ => ((A p.1 p.2 y : ℝ) : ℂ)
              * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
            - ((A p.1 p.2 z : ℝ) : ℂ) * Work.Diff.STE.pdVec k l
                (fun y : ι → ℝ => Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
          = ∑ i : Fin Sf.length, T (p.1, p.2, i) z := by
        intro p
        have hleib := congrFun (Work.Diff.STE.pdList_mul_sub (List.ofFn l)
            (fun y => ((A p.1 p.2 y : ℝ) : ℂ))
            (fun y => Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y)
            (fun q _ _ => diff_pdList_ofReal (hA p.1 p.2) q)
            (fun q _ hlen => diff_pdList_pair hu k p.1 p.2 (by simpa using hlen))) z
        have hmid := list_sum_map_eq_sum_fin Sf (fun s : List ι × List ι =>
            Work.Diff.STE.pdList s.1 (fun y => ((A p.1 p.2 y : ℝ) : ℂ)) z
              * Work.Diff.STE.pdList s.2
                  (fun y => Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z)
        show Work.Diff.STE.pdList (List.ofFn l) (fun y => ((A p.1 p.2 y : ℝ) : ℂ)
              * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
            - ((A p.1 p.2 z : ℝ) : ℂ) * Work.Diff.STE.pdList (List.ofFn l)
                (fun y => Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
          = ∑ i : Fin Sf.length, T (p.1, p.2, i) z
        rw [hleib, ← hSf, hmid]
      calc (Work.Diff.STE.pdVec k l (fun y : ι → ℝ => ∑ c, ∑ d,
              ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
            - ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
          = ∑ p : ι × ι, (Work.Diff.STE.pdVec k l (fun y : ι → ℝ => ((A p.1 p.2 y : ℝ) : ℂ)
                * Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z
              - ((A p.1 p.2 z : ℝ) : ℂ) * Work.Diff.STE.pdVec k l
                  (fun y : ι → ℝ => Work.Diff.STE.pd p.1 (Work.Diff.STE.pd p.2 u) y) z) := by
            simp only [hlin, hsub, Finset.sum_sub_distrib]
        _ = ∑ p : ι × ι, ∑ i : Fin Sf.length, T (p.1, p.2, i) z :=
            Finset.sum_congr rfl (fun p _ => hterm_eq p)
        _ = ∑ q : ι × ι × Fin Sf.length, T q z := by
            simp only [Fintype.sum_prod_type]
    -- ## the assembly
    have hcontT : ∀ q : ι × ι × Fin Sf.length, Continuous (T q) :=
      fun q => (cont_pdList_ofReal (hA q.1 q.2.1) _).mul (cont_pdList_pair hu q.1 q.2.1 _)
    have hsum : (∑ q : ι × ι × Fin Sf.length,
          ∫ x in Work.Diff.STE.unitCube, ‖T q x‖ ^ 2)
        ≤ (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
            * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * KA
                + (Fintype.card ι : ℝ) ^ (k - 1) * Q1))) := by
      calc ∑ q : ι × ι × Fin Sf.length, ∫ x in Work.Diff.STE.unitCube, ‖T q x‖ ^ 2
          ≤ ∑ _q : ι × ι × Fin Sf.length, (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * KA
                + (Fintype.card ι : ℝ) ^ (k - 1) * Q1))) :=
            Finset.sum_le_sum (fun q _ => hterm q.1 q.2.1 (Sf.get q.2.2) (List.get_mem Sf q.2.2))
        _ = (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
            * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * KA
                + (Fintype.card ι : ℝ) ^ (k - 1) * Q1))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcardβ : (Fintype.card (ι × ι × Fin Sf.length) : ℝ) ≤ N := by
      rw [hN, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
      have hSfl : Sf.length ≤ 2 ^ k := by
        have h1 : Sf.length ≤ (Work.Diff.STE.splits (List.ofFn l)).length := by
          rw [hSf]; exact List.length_filter_le _ _
        rwa [Work.Diff.STE.cm_splits_length_count, List.length_ofFn] at h1
      have hmul : Fintype.card ι * (Fintype.card ι * Sf.length)
          ≤ Fintype.card ι * (Fintype.card ι * 2 ^ k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hSfl)
      have hval : Fintype.card ι * (Fintype.card ι * 2 ^ k)
          = (Fintype.card ι) ^ 2 * 2 ^ k := by ring
      rw [hval] at hmul
      exact_mod_cast hmul
    have hnorm : (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec k l
            (fun y : ι → ℝ => ∑ c, ∑ d,
              ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) x
          - ∑ c, ∑ d, ((A c d x : ℝ) : ℂ)
              * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x‖ ^ 2)
        = fun x : ι → ℝ => ‖∑ q : ι × ι × Fin Sf.length, T q x‖ ^ 2 := by
      funext x
      have hx : (Work.Diff.STE.pdVec k l
              (fun y : ι → ℝ => ∑ c, ∑ d,
                ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) x
            - ∑ c, ∑ d, ((A c d x : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
          = ∑ q : ι × ι × Fin Sf.length, T q x := by
        simpa using congrFun hident x
      rw [hx]
    rw [ENormSq_zero_eq_int, hnorm]
    calc ∫ x in Work.Diff.STE.unitCube, ‖∑ q : ι × ι × Fin Sf.length, T q x‖ ^ 2
        ≤ (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
            * ∑ q : ι × ι × Fin Sf.length, ∫ x in Work.Diff.STE.unitCube, ‖T q x‖ ^ 2 :=
          integral_norm_sum_sq_le T hcontT
      _ ≤ (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
            * ((Fintype.card (ι × ι × Fin Sf.length) : ℝ)
              * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * KA
                  + (Fintype.card ι : ℝ) ^ (k - 1) * Q1)))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ N * N * Cint * (Fintype.card ι : ℝ) ^ (k - 1) * (S ^ 2 * (1 + KA + Q1)) := by
          have hc0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ (k - 1) := by positivity
          have hkey : (Fintype.card ι : ℝ) ^ (k - 1) * KA
                + (Fintype.card ι : ℝ) ^ (k - 1) * Q1
              ≤ (Fintype.card ι : ℝ) ^ (k - 1) * (1 + KA + Q1) := by nlinarith [hc0, hKA, hQ1]
          have hN0 : (0 : ℝ) ≤ N := by rw [hN]; positivity
          calc (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                * ((Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                  * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * KA
                      + (Fintype.card ι : ℝ) ^ (k - 1) * Q1))))
              ≤ (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                * ((Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                  * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * (1 + KA + Q1))))) := by
                gcongr
            _ ≤ N * N * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * (1 + KA + Q1)))) := by
                have hX0 : (0 : ℝ) ≤ Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1)
                    * (1 + KA + Q1))) := by
                  have h1 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ (k - 1) := hc0
                  have h2 : (0 : ℝ) ≤ 1 + KA + Q1 := by linarith
                  have h3 : (0 : ℝ) ≤ S ^ 2 := sq_nonneg S
                  exact mul_nonneg hCint0 (mul_nonneg h3 (mul_nonneg h1 h2))
                have h1 : (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                      * (Fintype.card (ι × ι × Fin Sf.length) : ℝ) ≤ N * N :=
                  mul_le_mul hcardβ hcardβ (by positivity) hN0
                calc (Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                      * ((Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                        * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * (1 + KA + Q1)))))
                    = ((Fintype.card (ι × ι × Fin Sf.length) : ℝ)
                        * (Fintype.card (ι × ι × Fin Sf.length) : ℝ))
                      * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1) * (1 + KA + Q1)))) := by
                        ring
                  _ ≤ N * N * (Cint * (S ^ 2 * ((Fintype.card ι : ℝ) ^ (k - 1)
                        * (1 + KA + Q1)))) :=
                      mul_le_mul h1 le_rfl hX0 (by positivity)
            _ = N * N * Cint * (Fintype.card ι : ℝ) ^ (k - 1)
                  * (S ^ 2 * (1 + KA + Q1)) := by ring

end

end Work.Diff.STE.Lead.GalTame
