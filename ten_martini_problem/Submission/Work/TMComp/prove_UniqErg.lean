import Mathlib
import Submission.Work.TMContract.Components

/-! Guidance from the project lead (the requester):

Component C0 (P_UniqErg) of the Ten Martini formalisation. The FROZEN statement is Work.TMContract.P_UniqErg (Submission/Work/TMContract/Components.lean; definitions in TMContract/Defs.lean; read TMContract/README.md). The proof route for C0 is in Submission/Work/TMPlan/ROUTE_LEAD.md; the source is Avila–Jitomirskaya, The Ten Martini Problem.

Proof route (Weyl equidistribution, uniform form):
* Fourier monomials: for `m ≠ 0`, `fourier m (u + j • a) = fourier m u * (fourier m a) ^ j`
  and `fourier m a ≠ 1` (non-torsion `a`), so the geometric sum is bounded by `2 / ‖1 - fourier m a‖`;
  the mean of `fourier m` over the circle is `0` (`1` for `m = 0`).
* Density: `span ℂ (range fourier)` is sup-norm dense in `C(AddCircle 1, ℂ)`
  (`span_fourier_closure_eq_top`), so the uniform Birkhoff statement extends from the span to all
  continuous functions by a 3-epsilon argument.
* Transfer back to `ℝ` through the periodic lift `Function.Periodic.lift` and
  `AddCircle.intervalIntegral_preimage`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace Work.TMComp

/-! ### Fourier monomials -/

/-- The geometric sum of a point `q` on the unit circle, `q ≠ 1`, is bounded by `2 / ‖1 - q‖`. -/
lemma uniqerg_geom_bound {q : ℂ} (hq : q ≠ 1) (hqn : ‖q‖ = 1) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, q ^ j‖ ≤ 2 / ‖1 - q‖ := by
  have h1 : ‖(1 : ℂ) - q‖ = ‖q - 1‖ := by
    rw [show (1 : ℂ) - q = -(q - 1) by ring, norm_neg]
  rw [h1]
  have hpos : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  rw [le_div_iff₀ hpos]
  calc ‖∑ j ∈ Finset.range N, q ^ j‖ * ‖q - 1‖
      = ‖(∑ j ∈ Finset.range N, q ^ j) * (q - 1)‖ := by rw [norm_mul]
    _ = ‖q ^ N - 1‖ := by rw [geom_sum_mul]
    _ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hqn, one_pow, norm_one]; norm_num

/-- `fourier m` is a character: `fourier m (u + j • a) = fourier m u * (fourier m a) ^ j`. -/
lemma uniqerg_fourier_add_pow (m : ℤ) (u a : AddCircle (1 : ℝ)) (j : ℕ) :
    fourier m (u + j • a) = fourier m u * (fourier m a) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (u + (j • a + a) : AddCircle (1 : ℝ)) = (u + j • a) + a := by abel
    rw [succ_nsmul, h1]
    rw [show fourier m ((u + j • a) + a) = fourier m (u + j • a) * fourier m a from by
      rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add]; rfl]
    rw [ih]; ring

/-- For non-torsion `a` and `m ≠ 0`, the monomial `fourier m` does not take the value `1` at `a`. -/
lemma uniqerg_fourier_ne_one (a : AddCircle (1 : ℝ))
    (ha : ∀ m : ℤ, m ≠ 0 → m • a ≠ 0) (m : ℤ) (hm : m ≠ 0) : fourier m a ≠ 1 := by
  intro h
  have h2 : AddCircle.toCircle (m • a) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    rw [AddCircle.toCircle_zero]
    exact Circle.coe_injective (by simpa [fourier_apply] using h)
  exact ha m hm ((AddCircle.injective_toCircle one_ne_zero) h2)

/-- The mean of `fourier m` over the circle is `0` for `m ≠ 0`. -/
lemma uniqerg_fourier_integral_zero (m : ℤ) (hm : m ≠ 0) :
    (∫ z : AddCircle (1 : ℝ), fourier m z) = 0 := by
  have h1 : (∫ z : AddCircle (1 : ℝ), fourier m z)
      = ∫ z : AddCircle (1 : ℝ), fourier m z ∂(AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))]; simp
  rw [h1]
  have h2 : fourierCoeff (T := (1 : ℝ)) (E := ℂ) (⇑(fourier (T := (1 : ℝ)) m)) = Pi.single m 1 :=
    fourierCoeff_fourier (T := (1 : ℝ)) m
  have h3 : fourierCoeff (T := (1 : ℝ)) (E := ℂ) (⇑(fourier (T := (1 : ℝ)) m)) 0
      = ∫ z : AddCircle (1 : ℝ), fourier m z ∂(AddCircle.haarAddCircle (T := (1 : ℝ))) := by
    simp [fourierCoeff]
  rw [← h3, h2, Pi.single_eq_of_ne]
  intro h; exact hm h.symm

/-- The mean of `fourier 0 = 1` over the circle is `1`. -/
lemma uniqerg_fourier_integral_one : (∫ z : AddCircle (1 : ℝ), fourier 0 z) = 1 := by
  have hvol : (volume : Measure (AddCircle (1 : ℝ))).real Set.univ = 1 := by
    unfold Measure.real; rw [AddCircle.measure_univ]; simp
  simp only [fourier_zero]
  rw [integral_const, hvol, one_smul]

/-- Uniform Birkhoff averages of a Fourier monomial converge to its mean. -/
lemma uniqerg_fourier_aux (a : AddCircle (1 : ℝ))
    (ha : ∀ m : ℤ, m ≠ 0 → m • a ≠ 0) (m : ℤ) :
    TendstoUniformly
      (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
        (∑ j ∈ Finset.range N, fourier m (u + j • a)) / (N : ℂ))
      (fun _ => ∫ z : AddCircle (1 : ℝ), fourier m z) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  rcases eq_or_ne m 0 with rfl | hm
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    intro u
    rw [dist_eq_norm, uniqerg_fourier_integral_one]
    have hN : (N : ℂ) ≠ 0 := by
      have : N ≠ 0 := by omega
      exact_mod_cast this
    have hsum : (∑ j ∈ Finset.range N, fourier 0 (u + j • a)) / (N : ℂ) = 1 := by
      simp only [fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact div_self hN
    rw [hsum, sub_self, norm_zero]; exact hε
  · have hq : fourier m a ≠ 1 := uniqerg_fourier_ne_one a ha m hm
    have hqn : ‖fourier m a‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
    have hw : 0 < ‖(1 : ℂ) - fourier m a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hq))
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 / (ε * ‖(1 : ℂ) - fourier m a‖))
    refine Filter.eventually_atTop.2 ⟨max N₀ 1, fun N hN => ?_⟩
    have hNge : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    intro u
    rw [dist_eq_norm, uniqerg_fourier_integral_zero m hm, zero_sub, norm_neg]
    have hfmu : ‖fourier m u‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
    have hNF : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    have hrew : (∑ j ∈ Finset.range N, fourier m (u + j • a))
        = fourier m u * (∑ j ∈ Finset.range N, (fourier m a) ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [uniqerg_fourier_add_pow]
    rw [hrew, norm_div, hNF, norm_mul, hfmu, one_mul]
    calc ‖∑ j ∈ Finset.range N, (fourier m a) ^ j‖ / (N : ℝ)
        ≤ (2 / ‖(1 : ℂ) - fourier m a‖) / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hNpos.le
          exact uniqerg_geom_bound hq hqn N
      _ < ε := by
          have hb2 : 2 < (N : ℝ) * (ε * ‖(1 : ℂ) - fourier m a‖) :=
            (div_lt_iff₀ (mul_pos hε hw)).mp (lt_of_lt_of_le hN₀ (by exact_mod_cast hNge))
          rw [div_div,
            div_lt_iff₀ (by positivity : (0 : ℝ) < ‖(1 : ℂ) - fourier m a‖ * (N : ℝ))]
          nlinarith [hb2]

/-! ### The density / 3-epsilon argument -/

/-- Multiplying the values of a uniformly convergent sequence of `ℂ`-valued functions by a
constant preserves uniform convergence. -/
lemma uniqerg_const_mul {ι β : Type*} {l : Filter ι} {f : ι → β → ℂ} {g : β → ℂ} (c : ℂ)
    (h : TendstoUniformly f g l) :
    TendstoUniformly (fun N u => c * f N u) (fun u => c * g u) l := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  rcases eq_or_ne c 0 with rfl | hc
  · filter_upwards with N u
    simp [hε]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    filter_upwards [h (ε / ‖c‖) (div_pos hε hcpos)] with N hN
    intro u
    have hNu := hN u
    rw [dist_eq_norm] at hNu
    rw [dist_eq_norm]
    rw [← mul_sub, norm_mul]
    calc ‖c‖ * ‖g u - f N u‖ < ‖c‖ * (ε / ‖c‖) := mul_lt_mul_of_pos_left hNu hcpos
      _ = ε := by field_simp

/-- **Weyl equidistribution within the circle.**  For a non-torsion rotation `a` of
`AddCircle 1`, the Birkhoff averages of any continuous complex function converge uniformly to its
mean with respect to the Haar probability measure. -/
theorem uniqerg_circle_aux (a : AddCircle (1 : ℝ))
    (ha : ∀ m : ℤ, m ≠ 0 → m • a ≠ 0) (F : C(AddCircle (1 : ℝ), ℂ)) :
    TendstoUniformly
      (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
        (∑ j ∈ Finset.range N, F (u + j • a)) / (N : ℂ))
      (fun _ => ∫ z : AddCircle (1 : ℝ), F z) atTop := by
  have hInt : ∀ q : C(AddCircle (1 : ℝ), ℂ), Integrable (fun z : AddCircle (1 : ℝ) => q z) :=
    fun q => q.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace q)
  have hvol : (volume : Measure (AddCircle (1 : ℝ))).real Set.univ = 1 := by
    unfold Measure.real
    rw [AddCircle.measure_univ]
    simp
  let P : C(AddCircle (1 : ℝ), ℂ) → Prop := fun q =>
    TendstoUniformly (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
        (∑ j ∈ Finset.range N, q (u + j • a)) / (N : ℂ))
      (fun _ => ∫ z : AddCircle (1 : ℝ), q z) atTop
  have hmem : ∀ q ∈ (Set.range (fourier (T := (1 : ℝ)))), P q := by
    rintro q ⟨n, rfl⟩
    exact uniqerg_fourier_aux a ha n
  have hzero : P 0 := by
    change TendstoUniformly (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
        (∑ j ∈ Finset.range N, (0 : C(AddCircle (1 : ℝ), ℂ)) (u + j • a)) / (N : ℂ))
      (fun _ => ∫ z : AddCircle (1 : ℝ), (0 : C(AddCircle (1 : ℝ), ℂ)) z) atTop
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards with N u
    simp [hε]
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    have h := hx.add hy
    change TendstoUniformly
      (fun (N : ℕ) (u : AddCircle (1 : ℝ)) => (∑ j ∈ Finset.range N, (x + y) (u + j • a)) / (N : ℂ))
      (fun _ => ∫ z : AddCircle (1 : ℝ), (x + y) z) atTop
    have key1 : (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
          (∑ j ∈ Finset.range N, (x + y) (u + j • a)) / (N : ℂ))
        = ((fun (N : ℕ) (u : AddCircle (1 : ℝ)) => (∑ j ∈ Finset.range N, x (u + j • a)) / (N : ℂ))
            + (fun (N : ℕ) (u : AddCircle (1 : ℝ)) => (∑ j ∈ Finset.range N, y (u + j • a)) / (N : ℂ))) := by
      funext N u
      simp only [Pi.add_apply, ContinuousMap.add_apply]
      rw [Finset.sum_add_distrib, add_div]
    have key2 : (fun (u : AddCircle (1 : ℝ)) => ∫ z : AddCircle (1 : ℝ), (x + y) z)
        = ((fun (u : AddCircle (1 : ℝ)) => ∫ z : AddCircle (1 : ℝ), x z)
            + (fun (u : AddCircle (1 : ℝ)) => ∫ z : AddCircle (1 : ℝ), y z)) := by
      funext u
      simp only [Pi.add_apply, ContinuousMap.add_apply]
      rw [integral_add (hInt x) (hInt y)]
    rw [key1, key2]
    exact h
  have hsmul : ∀ (c : ℂ) (x : C(AddCircle (1 : ℝ), ℂ)), P x → P (c • x) := by
    intro (c : ℂ) (x : C(AddCircle (1 : ℝ), ℂ)) hx
    change TendstoUniformly
      (fun (N : ℕ) (u : AddCircle (1 : ℝ)) => (∑ j ∈ Finset.range N, (c • x) (u + j • a)) / (N : ℂ))
      (fun _ => ∫ z : AddCircle (1 : ℝ), (c • x) z) atTop
    have key1 : (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
          (∑ j ∈ Finset.range N, (c • x) (u + j • a)) / (N : ℂ))
        = (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
            c * ((∑ j ∈ Finset.range N, x (u + j • a)) / (N : ℂ))) := by
      funext N u
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    have key2 : (fun (u : AddCircle (1 : ℝ)) => ∫ z : AddCircle (1 : ℝ), (c • x) z)
        = (fun (u : AddCircle (1 : ℝ)) => c * (∫ z : AddCircle (1 : ℝ), x z)) := by
      funext u
      simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
    rw [key1, key2]
    exact uniqerg_const_mul c hx
  have key : ∀ q ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))), P q :=
    fun q hq => Submodule.span_induction hmem hzero
      (fun x y _ _ ihx ihy => hadd x y ihx ihy)
      (fun c x _ ih => hsmul c x ih) hq
  change TendstoUniformly (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
        (∑ j ∈ Finset.range N, F (u + j • a)) / (N : ℂ))
      (fun _ => ∫ z : AddCircle (1 : ℝ), F z) atTop
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hdense : Dense ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) :
      Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      span_fourier_closure_eq_top (T := (1 : ℝ))]
    rfl
  obtain ⟨p, hpball, hpmem⟩ := Metric.dense_iff.mp hdense F (ε / 3) (by linarith)
  rw [Metric.mem_ball, dist_eq_norm] at hpball
  have hFp : ‖F - p‖ < ε / 3 := by rwa [norm_sub_rev] at hpball
  have hpP := key p hpmem
  change TendstoUniformly (fun (N : ℕ) (u : AddCircle (1 : ℝ)) =>
      (∑ j ∈ Finset.range N, p (u + j • a)) / (N : ℂ))
    (fun _ => ∫ z : AddCircle (1 : ℝ), p z) atTop at hpP
  rw [Metric.tendstoUniformly_iff] at hpP
  filter_upwards [hpP (ε / 3) (by linarith), eventually_ge_atTop (1 : ℕ)] with N hN hN1
  intro u
  have hNu := hN u
  rw [dist_eq_norm] at hNu
  rw [dist_eq_norm]
  have hb1 : ‖(∫ z : AddCircle (1 : ℝ), F z) - (∫ z : AddCircle (1 : ℝ), p z)‖ ≤ ‖F - p‖ := by
    rw [← integral_sub (hInt F) (hInt p)]
    have hle := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (AddCircle (1 : ℝ))))
      (f := fun z => F z - p z) (C := ‖F - p‖)
      (Filter.Eventually.of_forall (fun z => by
        rw [← ContinuousMap.sub_apply]
        exact ContinuousMap.norm_coe_le_norm (F - p) z))
    rwa [hvol, mul_one] at hle
  have hb3 : ‖(∑ j ∈ Finset.range N, p (u + j • a)) / (N : ℂ)
        - (∑ j ∈ Finset.range N, F (u + j • a)) / (N : ℂ)‖ ≤ ‖F - p‖ := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [← sub_div, ← Finset.sum_sub_distrib, norm_div]
    have hNF : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    rw [hNF]
    calc ‖∑ j ∈ Finset.range N, (p (u + j • a) - F (u + j • a))‖ / (N : ℝ)
        ≤ ((N : ℝ) * ‖p - F‖) / (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hNpos.le
          calc ‖∑ j ∈ Finset.range N, (p (u + j • a) - F (u + j • a))‖
              ≤ ∑ j ∈ Finset.range N, ‖p (u + j • a) - F (u + j • a)‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range N, ‖p - F‖ := by
                apply Finset.sum_le_sum
                intro j hj
                rw [← ContinuousMap.sub_apply]
                exact ContinuousMap.norm_coe_le_norm (p - F) (u + j • a)
            _ = (N : ℝ) * ‖p - F‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ‖p - F‖ := by field_simp
      _ = ‖F - p‖ := norm_sub_rev _ _
  calc ‖(∫ z : AddCircle (1 : ℝ), F z) - (∑ j ∈ Finset.range N, F (u + j • a)) / (N : ℂ)‖
      = ‖(((∫ z : AddCircle (1 : ℝ), F z) - (∫ z : AddCircle (1 : ℝ), p z))
          + ((∫ z : AddCircle (1 : ℝ), p z) - (∑ j ∈ Finset.range N, p (u + j • a)) / (N : ℂ))
          + ((∑ j ∈ Finset.range N, p (u + j • a)) / (N : ℂ)
              - (∑ j ∈ Finset.range N, F (u + j • a)) / (N : ℂ)))‖ := by ring_nf
    _ ≤ ‖(∫ z : AddCircle (1 : ℝ), F z) - (∫ z : AddCircle (1 : ℝ), p z)‖
        + ‖(∫ z : AddCircle (1 : ℝ), p z) - (∑ j ∈ Finset.range N, p (u + j • a)) / (N : ℂ)‖
        + ‖(∑ j ∈ Finset.range N, p (u + j • a)) / (N : ℂ)
            - (∑ j ∈ Finset.range N, F (u + j • a)) / (N : ℂ)‖ := norm_add₃_le
    _ < ε := by linarith [lt_of_le_of_lt hb1 hFp, hNu, lt_of_le_of_lt hb3 hFp]

/-! ### Transfer to `ℝ` -/

/-- **C0**: unique ergodicity of an irrational rotation, in its uniform form (Weyl). -/
theorem prove_UniqErg : Work.TMContract.P_UniqErg := by
  intro α hα f hfcont hfper
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hnorm : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => RCLike.norm_ofReal r
  have hp : Function.Periodic f 1 := fun x => by simpa using hfper x
  have hcont_lift : Continuous hp.lift := by
    have hq := QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))
    rw [hq.continuous_iff]
    have : hp.lift ∘ QuotientAddGroup.mk = f := by
      ext x; exact Function.Periodic.lift_coe hp x
    rw [this]; exact hfcont
  let F : C(AddCircle (1 : ℝ), ℝ) := ⟨hp.lift, hcont_lift⟩
  let Fc : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun u => (F u : ℂ), Complex.continuous_ofReal.comp F.continuous⟩
  have hFc : ∀ a : ℝ, Fc ↑a = (f a : ℂ) := fun a => by
    simp only [Fc, F, ContinuousMap.coe_mk]
    rw [Function.Periodic.lift_coe hp a]
  have ha : ∀ m : ℤ, m ≠ 0 → m • (α : AddCircle (1 : ℝ)) ≠ 0 := by
    intro m hm h
    rw [← AddCircle.coe_zsmul (1 : ℝ)] at h
    rw [AddCircle.coe_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk' : α * (m : ℝ) = (k : ℝ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hk
      linarith [hk]
    exact (hα.mul_intCast hm).ne_int k hk'
  have hconv := uniqerg_circle_aux (α : AddCircle (1 : ℝ)) ha Fc
  rw [Metric.tendstoUniformly_iff] at hconv
  filter_upwards [hconv ε hε] with N hN
  intro x
  have hx := hN (x : AddCircle (1 : ℝ))
  have hsum : (∑ j ∈ Finset.range N, Fc ((x : AddCircle (1 : ℝ)) + j • (α : AddCircle (1 : ℝ))))
      = ((∑ j ∈ Finset.range N, f (x + (j : ℝ) * α) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hxj : (x : AddCircle (1 : ℝ)) + j • (α : AddCircle (1 : ℝ)) = ↑(x + (j : ℝ) * α) := by
      rw [← AddCircle.coe_nsmul (1 : ℝ), ← AddCircle.coe_add]
      congr 1
      simp [nsmul_eq_mul]
    rw [hxj, hFc]
  have hint : (∫ z : AddCircle (1 : ℝ), Fc z) = ((∫ y in (0 : ℝ)..1, f y : ℝ) : ℂ) := by
    rw [← AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) 0 Fc]
    simp only [zero_add]
    simp_rw [hFc]
    rw [intervalIntegral.integral_ofReal]
  have key : (∫ z : AddCircle (1 : ℝ), Fc z)
        - (∑ j ∈ Finset.range N, Fc ((x : AddCircle (1 : ℝ)) + j • (α : AddCircle (1 : ℝ))))
            / (N : ℂ)
      = (((∫ y in (0 : ℝ)..1, f y)
            - (∑ j ∈ Finset.range N, f (x + (j : ℝ) * α)) / (N : ℝ) : ℝ) : ℂ) := by
    rw [hint, hsum]
    push_cast
    ring
  rw [dist_eq_norm] at hx ⊢
  rw [key] at hx
  rw [hnorm] at hx
  simpa using hx

end Work.TMComp
