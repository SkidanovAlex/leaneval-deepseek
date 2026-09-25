import Mathlib
import Submission.Work.BourgainPlan.Maximal.dilation_hl
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type
import Submission.Work.BourgainPlan.Maximal.piece_le_hlMax_of_deriv_pos
import Submission.Work.BourgainPlan.Maximal.flat_piece_le_hlMax
import Submission.Work.BourgainPlan.Maximal.exists_cover_deriv_ne
import Submission.Work.BourgainPlan.Maximal.poly_growth
import Submission.Work.BourgainPlan.Maximal.tail_le_hlMax

open MeasureTheory Set
open scoped ENNReal

set_option maxHeartbeats 4000000

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open Commons.Analysis.Maximal (hlMax)

/-! ## Elementary tools for the Hardy–Littlewood maximal function -/

/-- Reflection of the integral over a closed interval. -/
lemma lintegral_Icc_neg (F : ℝ → ℝ≥0∞) (a b : ℝ) :
    ∫⁻ z in Set.Icc a b, F (-z) = ∫⁻ z in Set.Icc (-b) (-a), F z := by
  rw [← lintegral_indicator measurableSet_Icc (fun z => F (-z)),
    ← lintegral_indicator measurableSet_Icc F]
  rw [← lintegral_neg_eq_self (fun z => (Set.Icc a b).indicator (fun z => F (-z)) z)]
  apply lintegral_congr
  intro z
  by_cases hz : -z ∈ Set.Icc a b
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ Set.Icc (-b) (-a) from by
      rw [Set.mem_Icc] at hz ⊢; constructor <;> linarith [hz.1, hz.2])]
    simp
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (show z ∉ Set.Icc (-b) (-a) from by
      intro h; exact hz (by rw [Set.mem_Icc] at h ⊢; constructor <;> linarith [h.1, h.2]))]

/-- `hlMax` is invariant under reflection of the variable. -/
lemma hlMax_reflect (ψ : ℝ → ℝ≥0∞) (y : ℝ) :
    hlMax (fun z => ψ (-z)) y = hlMax ψ (-y) := by
  unfold hlMax
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rw [lintegral_Icc_neg]
    have h1 : -b ≤ -y := by linarith [hab.2]
    have h2 : -y ≤ -a := by linarith [hab.1]
    have := Commons.Analysis.Maximal.hlMax_le_of_mem ψ h1 h2
    rwa [show -a - -b = b - a by ring] at this
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    have h1 : -b ≤ y := by linarith [hab.1]
    have h2 : y ≤ -a := by linarith [hab.2]
    have hkey : ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, ψ y
        = ENNReal.ofReal ((-a) - (-b))⁻¹
            * ∫⁻ y in Set.Icc (-b) (-a), (fun z => ψ (-z)) y := by
      rw [lintegral_Icc_neg]
      simp only [neg_neg]
      congr 1
      ring
    rw [hkey]
    exact le_iSup_of_le (-b) (le_iSup_of_le (-a) (le_iSup_of_le ⟨h1, h2⟩ le_rfl))

/-- Monotonicity of `hlMax`. -/
lemma hlMax_mono {f g : ℝ → ℝ≥0∞} (h : f ≤ g) (x : ℝ) : hlMax f x ≤ hlMax g x := by
  unfold hlMax
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
  refine le_trans (mul_le_mul_right (lintegral_mono h) _) ?_
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl))

/-- The integral of `ψ` over an interval containing `x` is at most its length times `hlMax ψ x`. -/
lemma lintegral_Icc_le_hlMax (ψ : ℝ → ℝ≥0∞) {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    ∫⁻ y in Set.Icc a b, ψ y ≤ ENNReal.ofReal (b - a) * hlMax ψ x := by
  rcases eq_or_lt_of_le (le_trans ha hb) with hab | hab
  · rw [← hab, Set.Icc_self]
    simp
  · have hpos : 0 < b - a := sub_pos.mpr hab
    have h := Commons.Analysis.Maximal.hlMax_le_of_mem ψ ha hb
    have hcancel : ENNReal.ofReal (b - a) * (ENNReal.ofReal ((b - a)⁻¹) * ∫⁻ y in Set.Icc a b, ψ y)
        = ∫⁻ y in Set.Icc a b, ψ y := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
        ENNReal.ofReal_one, one_mul]
    calc ∫⁻ y in Set.Icc a b, ψ y
        = ENNReal.ofReal (b - a) * (ENNReal.ofReal ((b - a)⁻¹) * ∫⁻ y in Set.Icc a b, ψ y) :=
          hcancel.symm
      _ ≤ ENNReal.ofReal (b - a) * hlMax ψ x := mul_le_mul_right h _

/-- Reflection of the integral of `F (c - ·)` over `[0,D]` as an integral of `F` over `[c-D,c]`. -/
lemma lintegral_Icc_sub_reflect (F : ℝ → ℝ≥0∞) (c D : ℝ) :
    ∫⁻ z in Set.Icc (0:ℝ) D, F (c - z) = ∫⁻ z in Set.Icc (c - D) c, F z := by
  have hderiv : ∀ x ∈ Set.Icc (0:ℝ) D,
      HasDerivWithinAt (fun z : ℝ => c - z) (-1) (Set.Icc (0:ℝ) D) x :=
    fun x _ => by
      have h : HasDerivAt (fun z : ℝ => c - z) (-1) x := by
        simpa using ((hasDerivAt_id x).const_sub c)
      exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun z : ℝ => c - z) (Set.Icc (0:ℝ) D) := by
    intro x _ y _ hxy
    simp only at hxy
    linarith
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv hinj F
  have himg : (fun z : ℝ => c - z) '' Set.Icc (0:ℝ) D = Set.Icc (c - D) c := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Set.mem_Icc] at hz ⊢
      constructor <;> linarith [hz.1, hz.2]
    · intro hw
      rw [Set.mem_Icc] at hw
      exact ⟨c - w, by rw [Set.mem_Icc]; constructor <;> linarith [hw.1, hw.2], by ring⟩
  rw [himg] at h
  simpa only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] using h.symm

/-- The integral of `ψ (c - ·)` over `(0,D]` is at most `D * hlMax ψ c`. -/
lemma lintegral_Ioc_sub_le_hlMax (ψ : ℝ → ℝ≥0∞) {c D : ℝ} (hD : 0 ≤ D) :
    ∫⁻ v in Set.Ioc (0:ℝ) D, ψ (c - v) ≤ ENNReal.ofReal D * hlMax ψ c := by
  have h1 : ∫⁻ v in Set.Ioc (0:ℝ) D, ψ (c - v) ≤ ∫⁻ v in Set.Icc (0:ℝ) D, ψ (c - v) :=
    lintegral_mono_set (fun _ hv => ⟨le_of_lt hv.1, hv.2⟩)
  have h2 : ∫⁻ v in Set.Icc (0:ℝ) D, ψ (c - v) ≤ ENNReal.ofReal D * hlMax ψ c := by
    rw [lintegral_Icc_sub_reflect]
    have h3 := lintegral_Icc_le_hlMax ψ (show c - D ≤ c by linarith [hD]) le_rfl
    rwa [show c - (c - D) = D by ring] at h3
  exact le_trans h1 h2

/-- Reflection of the integral over a half-open interval. -/
lemma lintegral_Ioc_reflect (F : ℝ → ℝ≥0∞) (a b : ℝ) :
    ∫⁻ u in Set.Ioc a b, F (a + b - u) = ∫⁻ u in Set.Ioc a b, F u := by
  have hderiv : ∀ x ∈ Set.Ioc a b,
      HasDerivWithinAt (fun u : ℝ => a + b - u) (-1) (Set.Ioc a b) x :=
    fun x _ => by
      have h : HasDerivAt (fun u : ℝ => a + b - u) (-1) x := by
        simpa using ((hasDerivAt_id x).const_sub (a + b))
      exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => a + b - u) (Set.Ioc a b) := by
    intro x _ y _ hxy
    simp only at hxy
    linarith
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj F
  rw [show (fun u : ℝ => a + b - u) = (fun u : ℝ => (a + b) - u) from rfl,
    Set.image_const_sub_Ioc] at h
  rw [show (a + b) - b = a by ring, show (a + b) - a = b by ring] at h
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] at h
  have hae : Set.Ico a b =ᵐ[volume] Set.Ioc a b := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (measure_singleton a)
      intro x hx
      rw [Set.mem_diff, Set.mem_Ico, Set.mem_Ioc] at hx
      simp only [Set.mem_singleton_iff]
      by_contra hne
      exact hx.2 ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hne), le_of_lt hx.1.2⟩
    · refine measure_mono_null ?_ (measure_singleton b)
      intro x hx
      rw [Set.mem_diff, Set.mem_Ioc, Set.mem_Ico] at hx
      simp only [Set.mem_singleton_iff]
      by_contra hne
      exact hx.2 ⟨le_of_lt hx.1.1, lt_of_le_of_ne hx.1.2 hne⟩
  rw [← h, Measure.restrict_congr_set hae]

/-- The change of variables `u = N s` in the lower Lebesgue integral over `(0,1]`. -/
lemma lintegral_Ioc_comp_mul (F : ℝ → ℝ≥0∞) {N : ℝ} (hN : 0 < N) :
    ∫⁻ s in Set.Ioc (0:ℝ) 1, F (N * s)
      = (ENNReal.ofReal N)⁻¹ * ∫⁻ u in Set.Ioc (0:ℝ) N, F u := by
  have hderiv : ∀ x ∈ Set.Ioc (0:ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => N * s) N (Set.Ioc (0:ℝ) 1) x :=
    fun x _ => by simpa using ((hasDerivAt_id x).const_mul N).hasDerivWithinAt
  have hinj : Set.InjOn (fun s : ℝ => N * s) (Set.Ioc (0:ℝ) 1) := by
    intro x _ y _ hxy
    exact mul_left_cancel₀ (ne_of_gt hN) hxy
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc hderiv hinj F
  rw [Set.image_mul_left_Ioc hN, mul_zero, mul_one, abs_of_pos hN] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  rw [h, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hN).ne' ENNReal.ofReal_ne_top, one_mul]

/-! ### `rpow`-shaped restatements of the `ENNReal` power lemmas -/

lemma rpow_mul_const (a b : ℝ≥0∞) {c : ℝ} (hc : 0 ≤ c) :
    (a * b) ^ c = a ^ c * b ^ c := ENNReal.mul_rpow_of_nonneg a b hc

lemma ofReal_rpow {x : ℝ} (hx : 0 ≤ x) {c : ℝ} (hc : 0 ≤ c) :
    (ENNReal.ofReal x) ^ c = ENNReal.ofReal (x ^ c) :=
  ENNReal.ofReal_rpow_of_nonneg hx hc

lemma rpow_add_const {a : ℝ≥0∞} (b c : ℝ) (h0 : a ≠ 0) (ht : a ≠ ⊤) :
    a ^ (b + c) = a ^ b * a ^ c := ENNReal.rpow_add b c h0 ht

lemma rpow_sub_one_mul (a : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ⊤) {c : ℝ} :
    a ^ (c - 1) * a = a ^ c := by
  have h : a ^ (c - 1) * a ^ (1 : ℝ) = a ^ ((c - 1) + 1) :=
    (rpow_add_const (c - 1) 1 ha0 hat).symm
  rw [show (c - 1) + 1 = c by ring] at h
  rw [show a ^ (1 : ℝ) = a from ENNReal.rpow_one a] at h
  exact h

lemma rpow_sum_le_const_mul_sum_rpow' {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {c : ℝ}
    (hc : 1 ≤ c) :
    (∑ i ∈ s, f i) ^ c ≤ (s.card : ℝ≥0∞) ^ (c - 1) * ∑ i ∈ s, (f i) ^ c :=
  ENNReal.rpow_sum_le_const_mul_sum_rpow s f hc

lemma natCast_rpow (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ((n : ℝ≥0∞)) ^ c = ENNReal.ofReal ((n : ℝ) ^ c) := by
  rw [show ((n : ℝ≥0∞)) = ENNReal.ofReal (n : ℝ) from (ENNReal.ofReal_natCast n).symm]
  exact ofReal_rpow (Nat.cast_nonneg n) hc

/-- **Assembling the `L^p` bound.**  If the maximal function `⨆ N, F N` is pointwise dominated by
`K` times a finite sum of translated Hardy–Littlewood maximal functions of `ψ`, then its `L^p`
norm is controlled by that of `ψ`. -/
lemma lintegral_rpow_iSup_le_of_finset_hlMax (F : ℕ → ℝ → ℝ≥0∞) (ψ : ℝ → ℝ≥0∞) (s : Finset ℝ)
    {K : ℝ} (hK : 0 < K) (hsc : 0 < s.card)
    (hψ : Measurable ψ) (hψfin : ∀ x, ψ x ≠ ⊤) {p : ℝ} (hp : 1 < p)
    (hH : ∫⁻ x, (ψ x) ^ p < ⊤)
    (hb : ∀ N x, F N x ≤ ENNReal.ofReal K * ∑ c ∈ s, hlMax ψ (x - c)) :
    ∫⁻ x, (⨆ N, F N x) ^ p
      ≤ ENNReal.ofReal ((K * s.card) ^ p * (8 * p * 2 ^ (p - 1) / (p - 1)))
          * ∫⁻ x, (ψ x) ^ p := by
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have hcard0 : (s.card : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hcardtop : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top s.card
  have hmeas : ∀ c ∈ s, Measurable (fun x : ℝ => (hlMax ψ (x - c)) ^ p) := by
    intro c _
    exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp
      ((Commons.Analysis.Maximal.measurable_hlMax ψ).comp (measurable_id.sub measurable_const))
  have hsummeas : Measurable (fun x : ℝ => ∑ c ∈ s, (hlMax ψ (x - c)) ^ p) :=
    Finset.measurable_sum _ hmeas
  -- step 1: replace by the pointwise bound
  have hstep1 : ∫⁻ x, (⨆ N, F N x) ^ p
      ≤ ∫⁻ x, (ENNReal.ofReal K * ∑ c ∈ s, hlMax ψ (x - c)) ^ p :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (iSup_le fun N => hb N x) hp0
  -- step 2: pull out `K`
  have hpoint : ∀ x, (ENNReal.ofReal K * ∑ c ∈ s, hlMax ψ (x - c)) ^ p
      = ENNReal.ofReal (K ^ p) * (∑ c ∈ s, hlMax ψ (x - c)) ^ p := by
    intro x
    rw [rpow_mul_const _ _ hp0, ofReal_rpow hK.le hp0]
  have hstep2 : ∫⁻ x, (ENNReal.ofReal K * ∑ c ∈ s, hlMax ψ (x - c)) ^ p
      = ENNReal.ofReal (K ^ p) * ∫⁻ x, (∑ c ∈ s, hlMax ψ (x - c)) ^ p := by
    rw [lintegral_congr hpoint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 3: expand the finite sum
  have hstep3 : ∫⁻ x, (∑ c ∈ s, hlMax ψ (x - c)) ^ p
      ≤ (s.card : ℝ≥0∞) ^ p * ∫⁻ x, (hlMax ψ x) ^ p := by
    have h1 : ∀ x, (∑ c ∈ s, hlMax ψ (x - c)) ^ p
        ≤ (s.card : ℝ≥0∞) ^ (p - 1) * ∑ c ∈ s, (hlMax ψ (x - c)) ^ p :=
      fun x => rpow_sum_le_const_mul_sum_rpow' s _ hp.le
    have h2 : ∫⁻ x, ∑ c ∈ s, (hlMax ψ (x - c)) ^ p = ∑ c ∈ s, ∫⁻ x, (hlMax ψ x) ^ p := by
      rw [lintegral_finsetSum s (fun c hc => hmeas c hc)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← MeasureTheory.lintegral_add_right_eq_self (fun y : ℝ => (hlMax ψ y) ^ p) (-c)]
      exact lintegral_congr fun x => by simp only [sub_eq_add_neg]
    calc ∫⁻ x, (∑ c ∈ s, hlMax ψ (x - c)) ^ p
        ≤ ∫⁻ x, (s.card : ℝ≥0∞) ^ (p - 1) * ∑ c ∈ s, (hlMax ψ (x - c)) ^ p :=
          lintegral_mono h1
      _ = (s.card : ℝ≥0∞) ^ (p - 1) * ∫⁻ x, ∑ c ∈ s, (hlMax ψ (x - c)) ^ p :=
          lintegral_const_mul _ hsummeas
      _ = (s.card : ℝ≥0∞) ^ (p - 1) * ∑ c ∈ s, ∫⁻ x, (hlMax ψ x) ^ p := by rw [h2]
      _ = (s.card : ℝ≥0∞) ^ p * ∫⁻ x, (hlMax ψ x) ^ p := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
            rpow_sub_one_mul _ hcard0 hcardtop]
  -- step 4: the Hardy–Littlewood maximal theorem
  have hstep4 := Commons.Analysis.Maximal.lintegral_rpow_hlMax_le hψ hψfin hp hH
  -- step 5: collect the constants
  have hcardpow : (s.card : ℝ≥0∞) ^ p = ENNReal.ofReal ((s.card : ℝ) ^ p) :=
    natCast_rpow s.card hp0
  have hconst : ENNReal.ofReal (K ^ p) * (s.card : ℝ≥0∞) ^ p
      = ENNReal.ofReal ((K * s.card) ^ p) := by
    rw [hcardpow, ← ENNReal.ofReal_mul (by positivity),
      show K ^ p * (s.card : ℝ) ^ p = (K * (s.card : ℝ)) ^ p from
        (Real.mul_rpow hK.le (Nat.cast_nonneg _)).symm]
  calc ∫⁻ x, (⨆ N, F N x) ^ p
      ≤ ENNReal.ofReal (K ^ p) * ((s.card : ℝ≥0∞) ^ p * ∫⁻ x, (hlMax ψ x) ^ p) :=
        le_trans hstep1 (le_trans (le_of_eq hstep2) (mul_le_mul_right hstep3 _))
    _ ≤ ENNReal.ofReal (K ^ p) * ((s.card : ℝ≥0∞) ^ p
          * (ENNReal.ofReal (8 * p * 2 ^ (p - 1) / (p - 1)) * ∫⁻ x, (ψ x) ^ p)) :=
        mul_le_mul_right (mul_le_mul_right hstep4 _) _
    _ = ENNReal.ofReal ((K * s.card) ^ p * (8 * p * 2 ^ (p - 1) / (p - 1)))
          * ∫⁻ x, (ψ x) ^ p := by
        rw [← mul_assoc, hconst, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

/-- Translation invariance of the lower integral: `∫ F (x - c) dx = ∫ F x dx`. -/
lemma lintegral_sub_shift (F : ℝ → ℝ≥0∞) (c : ℝ) : ∫⁻ x, F (x - c) = ∫⁻ x, F x := by
  simpa only [sub_eq_add_neg] using MeasureTheory.lintegral_add_right_eq_self F (-c)

/-- The integral over `[a,b]` agrees with the integral over `(a,b]`. -/
lemma lintegral_Icc_eq_lintegral_Ioc (F : ℝ → ℝ≥0∞) (a b : ℝ) :
    ∫⁻ u in Set.Icc a b, F u = ∫⁻ u in Set.Ioc a b, F u := by
  by_cases hab : a ≤ b
  · have h : Set.Icc a b = {a} ∪ Set.Ioc a b := by
      ext x
      simp only [Set.mem_Icc, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨h, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨le_rfl, hab⟩
        · exact ⟨le_of_lt h1, h2⟩
    rw [h, lintegral_union measurableSet_Ioc (by
      rw [Set.disjoint_left]
      rintro x hx1 hx2
      rw [Set.mem_singleton_iff] at hx1
      rw [Set.mem_Ioc] at hx2
      rw [hx1] at hx2
      exact lt_irrefl a hx2.1),
      setLIntegral_measure_zero _ _ (measure_singleton a), zero_add]
  · have hba : b < a := not_le.mp hab
    have h1 : Set.Icc a b = ∅ := Set.Icc_eq_empty hab
    have h2 : Set.Ioc a b = ∅ := Set.Ioc_eq_empty (not_lt.mpr hba.le)
    rw [h1, h2]

/-! ### Piece bounds (the derivatives of a polynomial, split at its critical points) -/

/-- If the derivative of `q` does not vanish on `(a,b]`, the average over the piece `(a,b]` of
`ψ (x - q ·)` is dominated by the Hardy–Littlewood maximal function of `ψ` at `x - q a`.
Derived from the increasing case by reflecting the values (`q ↦ -q`, `ψ ↦ ψ (-·)`). -/
lemma piece_bound_anchor_left
    (hI : ∀ (p : Polynomial ℝ) {a b : ℝ}, a < b →
      (∀ u ∈ Set.Ioc a b, 0 < p.derivative.eval u) →
      ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
        ∫⁻ u in Set.Ioc a b, ψ (x - p.eval u) ≤ ENNReal.ofReal C * hlMax ψ (x - p.eval a))
    (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hderiv : ∀ u ∈ Set.Ioc a b, q.derivative.eval u ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u) ≤ ENNReal.ofReal C * hlMax ψ (x - q.eval a) := by
  have hsign : (∀ u ∈ Set.Ioc a b, 0 < q.derivative.eval u) ∨
      (∀ u ∈ Set.Ioc a b, q.derivative.eval u < 0) := by
    have hcont : ∀ u : ℝ, ContinuousOn (fun v : ℝ => q.derivative.eval v) (Set.Icc u b) :=
      fun u => (Polynomial.continuous q.derivative).continuousOn
    rcases lt_trichotomy (q.derivative.eval b) 0 with hb | hb | hb
    · refine Or.inr fun u hu => ?_
      by_contra hcon
      push Not at hcon
      have hpos : 0 < q.derivative.eval u :=
        lt_of_le_of_ne hcon (Ne.symm (hderiv u hu))
      obtain ⟨ξ, hξ, hξ0⟩ := (intermediate_value_Icc' hu.2 (hcont u))
        (show (0:ℝ) ∈ Set.Icc (q.derivative.eval b) (q.derivative.eval u)
          from ⟨hb.le, hpos.le⟩)
      exact hderiv ξ ⟨lt_of_lt_of_le hu.1 hξ.1, hξ.2⟩ hξ0
    · exact absurd hb (hderiv b ⟨hab, le_rfl⟩)
    · refine Or.inl fun u hu => ?_
      by_contra hcon
      push Not at hcon
      obtain ⟨ξ, hξ, hξ0⟩ := (intermediate_value_Icc hu.2 (hcont u))
        (show (0:ℝ) ∈ Set.Icc (q.derivative.eval u) (q.derivative.eval b) from ⟨hcon, hb.le⟩)
      exact hderiv ξ ⟨lt_of_lt_of_le hu.1 hξ.1, hξ.2⟩ hξ0
  rcases hsign with hpos | hneg
  · exact hI q hab hpos
  · -- reflect the values
    have hderiv' : ∀ u ∈ Set.Ioc a b, 0 < ((-q).derivative).eval u := by
      intro u hu
      rw [Polynomial.derivative_neg, Polynomial.eval_neg]
      linarith [hneg u hu]
    obtain ⟨C, hC, hb⟩ := hI (-q) hab hderiv'
    refine ⟨C, hC, fun ψ hψ x => ?_⟩
    have hmeas : Measurable (fun z : ℝ => ψ (-z)) := hψ.comp measurable_neg
    have h := hb (fun z : ℝ => ψ (-z)) hmeas (-x)
    have hfun : ∀ u : ℝ, (fun z : ℝ => ψ (-z)) (-x - (-q).eval u) = ψ (x - q.eval u) := by
      intro u
      rw [Polynomial.eval_neg]
      congr 1
      ring_nf
    rw [show (∫⁻ u in Set.Ioc a b, (fun z : ℝ => ψ (-z)) (-x - (-q).eval u))
        = ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u) from lintegral_congr hfun,
      show (-x - (-q).eval a) = -(x - q.eval a) by
        rw [Polynomial.eval_neg]; ring,
      hlMax_reflect] at h
    simpa only [neg_neg] using h




/-- The `[a,b)`-form of the piece bound (derivative nonvanishing on `[a,b)`), with the anchor at
the right endpoint, obtained from the `(a,b]`-form by the reflection `u ↦ a + b - u`. -/
lemma piece_bound_anchor_right
    (hLeft : ∀ (p : Polynomial ℝ) {a b : ℝ}, a < b →
      (∀ u ∈ Set.Ioc a b, p.derivative.eval u ≠ 0) →
      ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
        ∫⁻ u in Set.Ioc a b, ψ (x - p.eval u) ≤ ENNReal.ofReal C * Commons.Analysis.Maximal.hlMax ψ (x - p.eval a))
    (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hderiv : ∀ u ∈ Set.Ico a b, q.derivative.eval u ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u) ≤ ENNReal.ofReal C * Commons.Analysis.Maximal.hlMax ψ (x - q.eval b) := by
  set qhat : Polynomial ℝ := q.comp (Polynomial.C (a + b) - Polynomial.X) with hqhat
  have hqhat_eval : ∀ u : ℝ, qhat.eval u = q.eval (a + b - u) := by
    intro u
    rw [hqhat, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  have hqhat_deriv : ∀ u : ℝ, qhat.derivative.eval u = -q.derivative.eval (a + b - u) := by
    intro u
    have hd : Polynomial.eval u (Polynomial.derivative (Polynomial.C (a + b) - Polynomial.X)) = -1 := by
      simp [Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X]
    rw [hqhat, Polynomial.derivative_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, hd]
    ring
  have hderiv' : ∀ u ∈ Set.Ioc a b, qhat.derivative.eval u ≠ 0 := by
    intro u hu
    rw [hqhat_deriv]
    exact neg_ne_zero.mpr (hderiv _ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  obtain ⟨C, hC, hb⟩ := hLeft qhat hab hderiv'
  refine ⟨C, hC, fun ψ hψ x => ?_⟩
  have hL : ∫⁻ u in Set.Ioc a b, ψ (x - qhat.eval u) = ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u) := by
    rw [← lintegral_Ioc_reflect (fun v : ℝ => ψ (x - q.eval v)) a b]
    exact lintegral_congr fun u => by rw [hqhat_eval]
  have h := hb ψ hψ x
  rw [hL, hqhat_eval a, show a + b - a = b by ring] at h
  exact h

/-- The piece bound used for the cover: on any piece on which the derivative of `q` is
nonvanishing on one of the half-open intervals, the average over the piece is bounded by the
Hardy–Littlewood maximal function at *both* endpoint values. -/
lemma cover_piece_bound
    (hLeft : ∀ (p : Polynomial ℝ) {a b : ℝ}, a < b →
      (∀ u ∈ Set.Ioc a b, p.derivative.eval u ≠ 0) →
      ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
        ∫⁻ u in Set.Ioc a b, ψ (x - p.eval u) ≤ ENNReal.ofReal C * Commons.Analysis.Maximal.hlMax ψ (x - p.eval a))
    (hRight : ∀ (p : Polynomial ℝ) {a b : ℝ}, a < b →
      (∀ u ∈ Set.Ico a b, p.derivative.eval u ≠ 0) →
      ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
        ∫⁻ u in Set.Ioc a b, ψ (x - p.eval u) ≤ ENNReal.ofReal C * Commons.Analysis.Maximal.hlMax ψ (x - p.eval b))
    (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (h : (∀ u ∈ Set.Ioc a b, q.derivative.eval u ≠ 0) ∨
         (∀ u ∈ Set.Ico a b, q.derivative.eval u ≠ 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ u in Set.Ioc a b, ψ (x - q.eval u)
        ≤ ENNReal.ofReal C * (Commons.Analysis.Maximal.hlMax ψ (x - q.eval a) + Commons.Analysis.Maximal.hlMax ψ (x - q.eval b)) := by
  rcases h with h1 | h2
  · obtain ⟨C, hC, hb⟩ := hLeft q hab h1
    exact ⟨C, hC, fun ψ hψ x =>
      le_trans (hb ψ hψ x) (mul_le_mul_right le_self_add _)⟩
  · obtain ⟨C, hC, hb⟩ := hRight q hab h2
    exact ⟨C, hC, fun ψ hψ x =>
      le_trans (hb ψ hψ x) (mul_le_mul_right le_add_self _)⟩




theorem poly_dilation_lp (P : Polynomial ℤ)
    (hP : ∀ x : ℝ, 0 ≤ x → 0 ≤ (P.map (Int.castRingHom ℝ)).eval x) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → (∀ x, ψ x ≠ ⊤) →
      (MeasureTheory.lintegral MeasureTheory.volume (fun x => ENNReal.rpow (ψ x) p) < ⊤) →
      MeasureTheory.lintegral MeasureTheory.volume
          (fun x => ENNReal.rpow (iSup fun N : ℕ =>
            MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))
              (fun s => ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s)))) p)
        ≤ ENNReal.ofReal C *
          MeasureTheory.lintegral MeasureTheory.volume (fun x => ENNReal.rpow (ψ x) p) := by
  classical
  set q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hq
  have hqnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ q.eval x := by
    intro x hx; rw [hq]; exact hP x hx
  have hp0 : (0:ℝ) ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  have heval : ∀ (N : ℕ) (s : ℝ),
      (P.map (Int.castRingHom ℝ)).eval ((N:ℝ) * s) = q.eval ((N:ℝ) * s) := fun N s => by rw [hq]
  rcases eq_or_ne q.natDegree 0 with hdeg0 | hdeg0
  · -- constant polynomial: the averages do not depend on `N`
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hF : ∀ (ψ : ℝ → ℝ≥0∞) (N : ℕ) (x : ℝ),
        ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))
          = ψ (x - q.coeff 0) := by
      intro ψ N x
      have h1 : (∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
          = ∫⁻ _s in Set.Ioc (0:ℝ) 1, ψ (x - q.coeff 0) :=
        lintegral_congr fun s => by rw [heval N s, hqC]; simp
      rw [h1, setLIntegral_const, Real.volume_Ioc]
      simp
    refine ⟨1, one_pos, fun ψ hψ hψfin hH => ?_⟩
    show (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p)
      ≤ ENNReal.ofReal (1:ℝ) * ∫⁻ x, (ψ x) ^ p
    have hsup : ∀ x : ℝ, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) = ψ (x - q.coeff 0) := by
      intro x
      rw [show (fun N : ℕ => ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) = (fun _ : ℕ => ψ (x - q.coeff 0))
        from funext fun N => hF ψ N x]
      exact iSup_const
    rw [ENNReal.ofReal_one, one_mul]
    have hcongr1 : (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p)
        = ∫⁻ x, (ψ (x - q.coeff 0)) ^ p := lintegral_congr fun x => by rw [hsup x]
    have hcongr2 : (∫⁻ x, (ψ (x - q.coeff 0)) ^ p) = ∫⁻ x, (ψ x) ^ p :=
      lintegral_sub_shift (fun y : ℝ => (ψ y) ^ p) (q.coeff 0)
    exact le_of_eq (hcongr1.trans hcongr2)
  · -- nonconstant polynomial
    have hdeg : 1 ≤ q.natDegree := Nat.one_le_iff_ne_zero.mpr hdeg0
    have hq'ne : q.derivative ≠ 0 := fun h => hdeg0 (Polynomial.derivative_eq_zero.mp h)
    obtain ⟨U, cB, C₀, hU1, hcB, hC₀, _hlead, hderivU, hupperU⟩ := poly_growth hqnn hdeg
    have hU0 : 0 ≤ U := le_trans zero_le_one hU1
    obtain ⟨n, a, b, hlt, hsign, hcover⟩ := exists_cover_deriv_ne q hq'ne hU0
    have hLeft := piece_bound_anchor_left piece_le_hlMax_of_deriv_pos
    have hRight := piece_bound_anchor_right hLeft
    have hpiece : ∀ i : Fin n, ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
        ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u)
          ≤ ENNReal.ofReal C * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))) :=
      fun i => cover_piece_bound hLeft hRight q (hlt i) (hsign i)
    set Cp : Fin n → ℝ := fun i => Classical.choose (hpiece i) with hCpdef
    have hCpspec : ∀ i, 0 < Cp i ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
        ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u)
          ≤ ENNReal.ofReal (Cp i) * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))) :=
      fun i => Classical.choose_spec (hpiece i)
    have hSC_nonneg : 0 ≤ ∑ i : Fin n, Cp i :=
      Finset.sum_nonneg fun i _ => (hCpspec i).1.le
    set T : Finset ℝ := (Finset.univ.image fun i : Fin n => q.eval (a i))
        ∪ (Finset.univ.image fun i : Fin n => q.eval (b i)) ∪ {0} with hTdef
    have hTmem_a : ∀ i : Fin n, q.eval (a i) ∈ T := by intro i; rw [hTdef]; simp
    have hTmem_b : ∀ i : Fin n, q.eval (b i) ∈ T := by intro i; rw [hTdef]; simp
    have hT0 : (0:ℝ) ∈ T := by rw [hTdef]; simp
    have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨0, hT0⟩
    obtain ⟨CB, hCB, htail⟩ := tail_le_hlMax q hU1 hcB hC₀ hderivU hupperU
      (fun u hu => hqnn u (le_trans hU0 hu))
    set KA : ℝ := (∑ i : Fin n, Cp i) * ((2 * n : ℕ) : ℝ) with hKAdef
    have hKA_nonneg : 0 ≤ KA := by rw [hKAdef]; positivity
    have hKB_nonneg : 0 ≤ CB := hCB.le
    -- ### Region A: the integral over `(0,U]`
    have hregionA : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
        ∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u)
          ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) := by
      intro ψ hψ x
      have hsub : Set.Ioc (0:ℝ) U ⊆ ⋃ i : Fin n, Set.Icc (a i) (b i) :=
        fun v hv => hcover ⟨le_of_lt hv.1, hv.2⟩
      have h1 : ∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u)
          ≤ ∫⁻ u in (⋃ i : Fin n, Set.Icc (a i) (b i)), ψ (x - q.eval u) :=
        lintegral_mono_set hsub
      have h2 : ∫⁻ u in (⋃ i : Fin n, Set.Icc (a i) (b i)), ψ (x - q.eval u)
          ≤ ∑ i : Fin n, ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u) := by
        refine le_trans (lintegral_iUnion_le _ _) ?_
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun i _ => le_of_eq (lintegral_Icc_eq_lintegral_Ioc _ _ _)
      have h4 : ∑ i : Fin n, ∫⁻ u in Set.Ioc (a i) (b i), ψ (x - q.eval u)
          ≤ ∑ i : Fin n, ENNReal.ofReal (Cp i)
              * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))) :=
        Finset.sum_le_sum fun i _ => (hCpspec i).2 ψ hψ x
      have hTsum : ∀ c ∈ T, hlMax ψ (x - c) ≤ ∑ c' ∈ T, hlMax ψ (x - c') :=
        fun c hc => Finset.single_le_sum (f := fun c' => hlMax ψ (x - c'))
          (fun c' _ => bot_le) hc
      have hCp_le : ∀ i : Fin n, ENNReal.ofReal (Cp i) ≤ ENNReal.ofReal (∑ j : Fin n, Cp j) := by
        intro i
        refine ENNReal.ofReal_le_ofReal ?_
        exact Finset.single_le_sum (fun j _ => (hCpspec j).1.le) (Finset.mem_univ i)
      have h5 : ∑ i : Fin n, ENNReal.ofReal (Cp i)
            * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i)))
          ≤ ENNReal.ofReal (∑ j : Fin n, Cp j)
              * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c))) := by
        calc ∑ i : Fin n, ENNReal.ofReal (Cp i)
              * (hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i)))
            ≤ ∑ _i : Fin n, ENNReal.ofReal (∑ j : Fin n, Cp j)
                * (2 * ∑ c ∈ T, hlMax ψ (x - c)) := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine mul_le_mul' (hCp_le i) ?_
              have ha := hTsum (q.eval (a i)) (hTmem_a i)
              have hb := hTsum (q.eval (b i)) (hTmem_b i)
              calc hlMax ψ (x - q.eval (a i)) + hlMax ψ (x - q.eval (b i))
                  ≤ ∑ c ∈ T, hlMax ψ (x - c) + ∑ c ∈ T, hlMax ψ (x - c) := add_le_add ha hb
                _ = 2 * ∑ c ∈ T, hlMax ψ (x - c) := by rw [two_mul]
          _ = ENNReal.ofReal (∑ j : Fin n, Cp j)
                * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c))) := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
              ring
      have h6 : ENNReal.ofReal (∑ j : Fin n, Cp j)
              * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c)))
          ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) := by
        have hcast : ((n : ℝ≥0∞)) * 2 = ENNReal.ofReal ((2 * n : ℕ) : ℝ) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from (ENNReal.ofReal_ofNat 2).symm,
            ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
            show (n : ℝ) * 2 = ((2 * n : ℕ) : ℝ) by push_cast; ring]
        have hconst : ENNReal.ofReal (∑ j : Fin n, Cp j) * ((n : ℝ≥0∞) * 2) = ENNReal.ofReal KA := by
          rw [hcast, hKAdef, ← ENNReal.ofReal_mul hSC_nonneg]
        calc ENNReal.ofReal (∑ j : Fin n, Cp j) * ((n : ℝ≥0∞) * (2 * ∑ c ∈ T, hlMax ψ (x - c)))
            = (ENNReal.ofReal (∑ j : Fin n, Cp j) * ((n : ℝ≥0∞) * 2))
                * ∑ c ∈ T, hlMax ψ (x - c) := by ring
          _ ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) := le_of_eq (by rw [hconst])
      exact le_trans h1 (le_trans h2 (le_trans h4 (le_trans h5 h6)))
    -- ### Region B: the tail
    have hregionB : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ (N x : ℝ), U ≤ N →
        ∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)
          ≤ ENNReal.ofReal (CB * N) * ∑ c ∈ T, hlMax ψ (x - c) := by
      intro ψ hψ N x hN
      refine le_trans (htail ψ hψ N x hN) ?_
      refine mul_le_mul_right ?_ _
      simpa using Finset.single_le_sum (f := fun c' => hlMax ψ (x - c')) (fun c' _ => bot_le) hT0
    -- ### the bound for a single average
    have hmain : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ (N x : ℝ), 1 ≤ N →
        ∫⁻ u in Set.Ioc (0:ℝ) N, ψ (x - q.eval u)
          ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N * ∑ c ∈ T, hlMax ψ (x - c) := by
      intro ψ hψ N x hN
      have hN1 : (1:ℝ≥0∞) ≤ ENNReal.ofReal N := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hN
      have hKA_le : ENNReal.ofReal KA ≤ ENNReal.ofReal KA * ENNReal.ofReal N := by
        calc ENNReal.ofReal KA = ENNReal.ofReal KA * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal KA * ENNReal.ofReal N := mul_le_mul_right hN1 _
      rcases lt_or_ge N U with hNU | hUN
      · have hsubN : Set.Ioc (0:ℝ) N ⊆ Set.Ioc (0:ℝ) U :=
          fun v hv => ⟨hv.1, le_trans hv.2 hNU.le⟩
        have h1 : ∫⁻ u in Set.Ioc (0:ℝ) N, ψ (x - q.eval u)
            ≤ ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c) :=
          le_trans (lintegral_mono_set hsubN) (hregionA ψ hψ x)
        have hKN : ENNReal.ofReal KA ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N :=
          calc ENNReal.ofReal KA ≤ ENNReal.ofReal (KA + CB) :=
                ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hKB_nonneg)
            _ = ENNReal.ofReal (KA + CB) * 1 := (mul_one _).symm
            _ ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N := mul_le_mul_right hN1 _
        exact le_trans h1 (mul_le_mul_left hKN _)
      · have hsplit : (∫⁻ u in Set.Ioc (0:ℝ) N, ψ (x - q.eval u))
            ≤ (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
              + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u)) := by
          have hunion : Set.Ioc (0:ℝ) U ∪ Set.Ioc U N = Set.Ioc (0:ℝ) N := by
            ext y
            simp only [Set.mem_union, Set.mem_Ioc]
            constructor
            · rintro (⟨hy1, hy2⟩ | ⟨hy1, hy2⟩)
              · exact ⟨hy1, hy2.trans hUN⟩
              · exact ⟨lt_trans (lt_of_lt_of_le zero_lt_one hU1) hy1, hy2⟩
            · rintro ⟨hy1, hy2⟩
              rcases lt_trichotomy y U with hy | rfl | hy
              · exact Or.inl ⟨hy1, hy.le⟩
              · exact Or.inl ⟨hy1, le_rfl⟩
              · exact Or.inr ⟨hy, hy2⟩
          rw [← hunion]
          exact lintegral_union_le (fun u : ℝ => ψ (x - q.eval u))
            (Set.Ioc (0:ℝ) U) (Set.Ioc U N)
        have hA := hregionA ψ hψ x
        have hB := hregionB ψ hψ N x hUN
        have hsum : (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
              + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u))
            ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N * ∑ c ∈ T, hlMax ψ (x - c) := by
          have hstep1 : (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
                + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u))
              ≤ (ENNReal.ofReal KA * ∑ c ∈ T, hlMax ψ (x - c))
                + (ENNReal.ofReal (CB * N) * ∑ c ∈ T, hlMax ψ (x - c)) := add_le_add hA hB
          calc (∫⁻ u in Set.Ioc (0:ℝ) U, ψ (x - q.eval u))
                + (∫⁻ u in Set.Ioc U N, ψ (x - q.eval u))
              ≤ (ENNReal.ofReal KA + ENNReal.ofReal (CB * N)) * ∑ c ∈ T, hlMax ψ (x - c) := by
                rw [← add_mul] at hstep1
                exact hstep1
            _ ≤ (ENNReal.ofReal KA * ENNReal.ofReal N
                  + ENNReal.ofReal CB * ENNReal.ofReal N) * ∑ c ∈ T, hlMax ψ (x - c) := by
                refine mul_le_mul_left ?_ _
                refine add_le_add hKA_le ?_
                rw [ENNReal.ofReal_mul hKB_nonneg]
            _ ≤ ENNReal.ofReal (KA + CB) * ENNReal.ofReal N * ∑ c ∈ T, hlMax ψ (x - c) := by
                rw [← add_mul, ← ENNReal.ofReal_add hKA_nonneg hKB_nonneg, mul_assoc]
        exact le_trans hsplit hsum
    -- ### the averages in the `s`-form
    have hFN : ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ (N : ℕ) (x : ℝ),
        ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))
          ≤ ENNReal.ofReal (KA + CB) * ∑ c ∈ T, hlMax ψ (x - c) := by
      intro ψ hψ N x
      have hNnpos : (0:ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have hNn1 : (1:ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
      have hstep : ∫⁻ s in Set.Ioc (0:ℝ) 1, (fun u : ℝ => ψ (x - q.eval u))
            ((((N + 1 : ℕ) : ℝ)) * s)
          = (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹
            * ∫⁻ u in Set.Ioc (0:ℝ) ((N + 1 : ℕ) : ℝ), ψ (x - q.eval u) :=
        lintegral_Ioc_comp_mul (fun u : ℝ => ψ (x - q.eval u)) hNnpos
      rw [show (∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s)))
          = ∫⁻ s in Set.Ioc (0:ℝ) 1, (fun u : ℝ => ψ (x - q.eval u)) ((((N + 1 : ℕ) : ℝ)) * s) from
            lintegral_congr fun s => by rw [heval], hstep]
      have hm := hmain ψ hψ ((N + 1 : ℕ) : ℝ) x hNn1
      refine le_trans (mul_le_mul_right hm _) ?_
      rw [show (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹
            * (ENNReal.ofReal (KA + CB) * ENNReal.ofReal ((N + 1 : ℕ) : ℝ)
              * ∑ c ∈ T, hlMax ψ (x - c))
          = (ENNReal.ofReal ((N + 1 : ℕ) : ℝ))⁻¹ * ENNReal.ofReal ((N + 1 : ℕ) : ℝ)
            * (ENNReal.ofReal (KA + CB) * ∑ c ∈ T, hlMax ψ (x - c)) from by ring,
        ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]
    -- ### the split of the supremum
    have hsplit_sup : ∀ (ψ : ℝ → ℝ≥0∞) (x : ℝ),
        (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
          ≤ (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
              ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s)))
            + ∫⁻ s in Set.Ioc (0:ℝ) 1,
                ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((0:ℕ) : ℝ)) * s)) := by
      intro ψ x
      refine iSup_le fun N => ?_
      rcases N with _ | k
      · exact le_add_self
      · refine le_trans (le_iSup (fun N : ℕ => ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) k) ?_
        exact le_self_add
    -- ### the conclusion
    set B : ℝ := ((KA + CB) * T.card) ^ p * (8 * p * 2 ^ (p - 1) / (p - 1)) with hBdef
    have hBpos : 0 < B := by
      rw [hBdef]
      have h1 : (0:ℝ) < ((KA + CB) * (T.card : ℝ)) :=
        mul_pos (by linarith [hKA_nonneg, hCB]) (by exact_mod_cast hTpos)
      have h2 : (0:ℝ) < 8 * p * (2:ℝ) ^ (p - 1) / (p - 1) := by
        have h3 : (0:ℝ) < (2:ℝ) ^ (p - 1) := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (p - 1)
        exact div_pos (mul_pos (mul_pos (by norm_num) (by linarith)) h3) (by linarith)
      exact mul_pos (Real.rpow_pos_of_pos h1 _) h2
    have htwopos : (0:ℝ) < (2:ℝ) ^ (p - 1) :=
      Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (p - 1)
    refine ⟨(2:ℝ) ^ (p - 1) * (B + 1), mul_pos htwopos (by linarith [hBpos]),
      fun ψ hψ hψfin hH => ?_⟩
    show ((∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p))
      ≤ ENNReal.ofReal ((2:ℝ) ^ (p - 1) * (B + 1)) * (∫⁻ x, (ψ x) ^ p)
    have hlen := lintegral_rpow_iSup_le_of_finset_hlMax
      (fun N x => ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s)))
      ψ T (by linarith [hKA_nonneg, hKB_nonneg]) hTpos hψ hψfin hp hH (hFN ψ hψ)
    have hc2 : (2:ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal ((2:ℝ) ^ (p - 1)) := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) from (ENNReal.ofReal_ofNat 2).symm]
      exact ofReal_rpow (x := 2) (by norm_num) (c := p - 1) (by linarith)
    have hc2top : (2:ℝ≥0∞) ^ (p - 1) ≠ ⊤ := by rw [hc2]; exact ENNReal.ofReal_ne_top
    have hF0eq : ∀ x : ℝ, (∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((0:ℕ) : ℝ)) * s))) = ψ (x - q.eval 0) := by
      intro x
      have h1 : (∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((0:ℕ) : ℝ))*s)))
          = ∫⁻ _s in Set.Ioc (0:ℝ) 1, ψ (x - q.eval 0) :=
        lintegral_congr fun s => by
          rw [heval 0 s]
          simp only [Nat.cast_zero, zero_mul]
      rw [h1, setLIntegral_const, Real.volume_Ioc]
      simp
    have hmeasY : Measurable (fun x : ℝ => (ψ (x - q.eval 0)) ^ p) :=
      (ENNReal.continuous_rpow_const (y := p)).measurable.comp
        (hψ.comp (measurable_id.sub measurable_const))
    have hI0 : (∫⁻ x, (ψ (x - q.eval 0)) ^ p) = (∫⁻ x, (ψ x) ^ p) :=
      lintegral_sub_shift (fun y : ℝ => (ψ y) ^ p) (q.eval 0)
    have hpoint : ∀ x : ℝ,
        (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p
          ≤ (2:ℝ≥0∞) ^ (p - 1)
              * ((⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                    ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p
                + (ψ (x - q.eval 0)) ^ p) := by
      intro x
      have hs := hsplit_sup ψ x
      rw [hF0eq x] at hs
      exact le_trans (ENNReal.rpow_le_rpow hs hp0)
        (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp.le)
    have hIform : (∫⁻ x, (2:ℝ≥0∞) ^ (p - 1)
            * ((⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p
                + (ψ (x - q.eval 0)) ^ p))
        = (2:ℝ≥0∞) ^ (p - 1)
            * ((∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p)
                + (∫⁻ x, (ψ x) ^ p)) := by
      have h1 : (∫⁻ x, (2:ℝ≥0∞) ^ (p - 1)
            * ((⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p
                + (ψ (x - q.eval 0)) ^ p))
          = (2:ℝ≥0∞) ^ (p - 1)
            * ∫⁻ x, ((⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p
                + (ψ (x - q.eval 0)) ^ p) :=
        lintegral_const_mul' _ _ hc2top
      have h2 : (∫⁻ x, ((⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p
                + (ψ (x - q.eval 0)) ^ p))
          = (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p)
            + (∫⁻ x, (ψ (x - q.eval 0)) ^ p) :=
        lintegral_add_right (f := fun x : ℝ => (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p) hmeasY
      rw [h1, h2, hI0]
    have hconst : ENNReal.ofReal B * (∫⁻ x, (ψ x) ^ p) + (∫⁻ x, (ψ x) ^ p)
        = ENNReal.ofReal (B + 1) * (∫⁻ x, (ψ x) ^ p) := by
      have h1 : ENNReal.ofReal B * (∫⁻ x, (ψ x) ^ p) + (∫⁻ x, (ψ x) ^ p)
          = (ENNReal.ofReal B + 1) * (∫⁻ x, (ψ x) ^ p) := by
        rw [add_mul, one_mul]
      have h2 : ENNReal.ofReal B + 1 = ENNReal.ofReal (B + 1) := by
        rw [show (1:ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
          ← ENNReal.ofReal_add hBpos.le zero_le_one]
      exact h1.trans (congrArg (fun z => z * (∫⁻ x, (ψ x) ^ p)) h2)
    have hlast : (2:ℝ≥0∞) ^ (p - 1) * (ENNReal.ofReal (B + 1) * (∫⁻ x, (ψ x) ^ p))
        = ENNReal.ofReal ((2:ℝ) ^ (p - 1) * (B + 1)) * (∫⁻ x, (ψ x) ^ p) := by
      rw [hc2, ← mul_assoc, ← ENNReal.ofReal_mul htwopos.le]
    calc ((∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p))
        ≤ ∫⁻ x, (2:ℝ≥0∞) ^ (p - 1)
            * ((⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p
                + (ψ (x - q.eval 0)) ^ p) := lintegral_mono hpoint
      _ = (2:ℝ≥0∞) ^ (p - 1)
            * ((∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
                  ψ (x - (P.map (Int.castRingHom ℝ)).eval ((((N + 1 : ℕ) : ℝ)) * s))) ^ p)
                + (∫⁻ x, (ψ x) ^ p)) := hIform
      _ ≤ (2:ℝ≥0∞) ^ (p - 1)
            * (ENNReal.ofReal B * (∫⁻ x, (ψ x) ^ p) + (∫⁻ x, (ψ x) ^ p)) :=
          mul_le_mul_right (add_le_add hlen le_rfl) _
      _ = (2:ℝ≥0∞) ^ (p - 1) * (ENNReal.ofReal (B + 1) * (∫⁻ x, (ψ x) ^ p)) := by
          rw [hconst]
      _ = ENNReal.ofReal ((2:ℝ) ^ (p - 1) * (B + 1)) * (∫⁻ x, (ψ x) ^ p) := hlast

end Work.BourgainPlan.Maximal
