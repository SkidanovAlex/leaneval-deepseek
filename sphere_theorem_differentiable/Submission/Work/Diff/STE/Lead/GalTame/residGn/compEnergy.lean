import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.GalTame.residGn.gnSharp
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.Comp3.faaDiBruno_vec
import Submission.Work.Diff.STE.flat.jet_comp_l2_unif

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `composite_gn`: the composite (Moser) Gagliardo–Nirenberg estimate

For `Φ : ℝ^n × Mat × Ten → ℝ`, smooth `1`-periodic `M`, `N` with `|M|, |N| ≤ B`, and with all
iterated derivatives of `Φ` at the state `(z, M z, N z)` bounded by `D` up to order `m`, the
`L²` norm over the unit cube of the order-`m` partial derivative of `z ↦ Φ (z, M z, N z)` is
bounded by `C (1 + Σ ENormSq m M + Σ ENormSq m N)`, with `C` uniform in `Φ, M, N`.

The proof is the classical Moser tame estimate:

* Faà di Bruno (order-`m` chain rule) expands `∂^β (Φ ∘ V)` (`V z = (z, M z, N z)`) as a sum
  over ordered partitions `c` of `Fin m`, the `c`-term being `(D^{c.length} Φ)(V x)` applied to
  the block derivatives `D^{c.partSize i} V x`;
* the operator norm of `D^{c.length} Φ (V x)` is `≤ D`, and the norm of `D^{p} V x` is at most
  `1` (identity block) plus the components of `M` and `N` (`norm_iteratedFDeriv_triple_apply_le`);
* weighted AM–GM turns the *product* of the block norms into a *sum* of `(block norm)^{2m/p i}`
  (`prod_sq_le_sum_weighted_rpow`), i.e. into the exponents at which
  Gagliardo–Nirenberg (`Work.Diff.STE.GN_torus`) controls each block;
* the sup bound `|M|, |N| ≤ B` is exactly the `L^∞` input of the sharp torus Gagliardo–Nirenberg
  inequality; the `2m/p i - 2` powers of `B` are absorbed into the constant.

The finite sums (over partitions and blocks) and the `L²` bookkeeping are handled by
`integral_mono_ae` for continuous integrands on the compact cube.
-/

noncomputable section

namespace Work.Diff.STE.Lead.GalTame.ResidGn

open MeasureTheory BigOperators
open scoped ContDiff

/-- `ENormSq` is nonnegative (local copy). -/
lemma ENormSq_nonnegR {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : (ι → ℝ) → ℂ) :
    0 ≤ Work.Diff.STE.ENormSq m f :=
  Finset.sum_nonneg fun l _ => integral_nonneg fun x => pow_nonneg (norm_nonneg _) 2

set_option maxHeartbeats 1000000

/-! ## 0. The Faà di Bruno term of the composite -/

/-- The `c`-th Faà di Bruno term of `∂^β (Φ ∘ V)`, `V z = (z, M z, N z)`: the `c.length`-th
Fréchet derivative of `Φ` at the state, applied to the tuple of block derivatives of `V`. -/
noncomputable def fbTerm {n m : ℕ}
    (Φ : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) → ℝ)
    (M : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (N : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (β : Fin m → Fin n) (c : OrderedFinpartition m) (x : Fin n → ℝ) : ℝ :=
  (iteratedFDeriv ℝ c.length Φ (x, M x, N x))
    (fun i => iteratedFDeriv ℝ (c.partSize i) (fun z : Fin n → ℝ => (z, M z, N z)) x
      (fun j' => Pi.single (β (c.emb i j')) (1 : ℝ)))

/-! ## 1. Elementary analytic lemmas -/

/-- `ENormSq 0` is the `L²` norm squared on the cube: there is exactly one `0`-fold derivative. -/
lemma ENormSq_zero_unitCube {n : ℕ} (g : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 g = ∫ x in Work.Diff.STE.unitCube, ‖g x‖ ^ 2 := by
  rw [Work.Diff.STE.ENormSq, Finset.univ_unique, Finset.sum_singleton]
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]

/-- The integral of a constant over the unit cube. -/
lemma integral_const_unitCube' {n : ℕ} (c : ℝ) :
    ∫ x in Work.Diff.STE.unitCube (ι := Fin n), c = c := by
  rw [show (∫ x in Work.Diff.STE.unitCube (ι := Fin n), c)
      = c * ∫ x in Work.Diff.STE.unitCube (ι := Fin n), (1 : ℝ) from by
        rw [← MeasureTheory.integral_const_mul]; simp]
  rw [Work.Diff.STE.flat.integral_one_unitCube, mul_one]

/-- The integral of `1 + f + g` over the unit cube. -/
lemma integral_one_add_add_unitCube {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hf : Integrable f (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))))
    (hg : Integrable g (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n)))) :
    ∫ a in Work.Diff.STE.unitCube, (1 + f a + g a)
      = 1 + (∫ a in Work.Diff.STE.unitCube, f a) + ∫ a in Work.Diff.STE.unitCube, g a := by
  haveI : IsFiniteMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    Work.Diff.STE.GN.unitCube_isFiniteMeasure_restrict (ι := Fin n)
  have h1 : Integrable (fun a : Fin n → ℝ => (1 : ℝ) + f a)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    (integrable_const 1).add hf
  have h2 : Integrable (fun _ : Fin n → ℝ => (1 : ℝ))
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    integrable_const 1
  calc ∫ a in Work.Diff.STE.unitCube, (1 + f a + g a)
      = (∫ a in Work.Diff.STE.unitCube, (1 + f a)) + ∫ a in Work.Diff.STE.unitCube, g a :=
        MeasureTheory.integral_add h1 hg
    _ = ((∫ a in Work.Diff.STE.unitCube, (1 : ℝ)) + ∫ a in Work.Diff.STE.unitCube, f a)
          + ∫ a in Work.Diff.STE.unitCube, g a := by
        rw [MeasureTheory.integral_add h2 hf]
    _ = 1 + (∫ a in Work.Diff.STE.unitCube, f a) + ∫ a in Work.Diff.STE.unitCube, g a := by
        rw [integral_const_unitCube']

/-- A continuous real function is integrable on the (bounded) unit cube. -/
lemma integrableOn_unitCube_of_continuous_real {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (Work.Diff.STE.unitCube)) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : Work.Diff.STE.unitCube ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hf.continuousOn).mono_set hsub

/-- The norm of a `Pi.single` is at most the norm of its value. -/
lemma norm_pi_single_le' {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    [SeminormedAddGroup α] (i : ι) (a : α) : ‖(Pi.single i a : ι → α)‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr fun j => by
    rcases eq_or_ne j i with h | h
    · subst h; rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]; simpa using norm_nonneg a

/-- **Power-mean inequality** for a finite family of nonnegative reals: for `e ≥ 1`,
`(∑ i ∈ s, f i)^e ≤ s.card^{e-1} * ∑ i ∈ s, (f i)^e`. -/
theorem rpow_sum_le_card_mul_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {e : ℝ} (he : 1 ≤ e) :
    (∑ i ∈ s, f i) ^ e ≤ (s.card : ℝ) ^ (e - 1) * ∑ i ∈ s, (f i) ^ e := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow s f he
  have h1 : ∑ i ∈ s, |f i| = ∑ i ∈ s, f i :=
    Finset.sum_congr rfl fun i hi => abs_of_nonneg (hf i hi)
  have h2 : ∑ i ∈ s, (|f i|) ^ e = ∑ i ∈ s, (f i) ^ e :=
    Finset.sum_congr rfl fun i hi => by rw [abs_of_nonneg (hf i hi)]
  rwa [h1, h2] at h

/-- The three-term case of the power-mean inequality. -/
theorem rpow_three_le (a b c e : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 1 ≤ e) :
    (a + b + c) ^ e ≤ 3 ^ (e - 1) * (a ^ e + b ^ e + c ^ e) := by
  have h := rpow_sum_le_card_mul_sum_rpow (Finset.univ : Finset (Fin 3)) ![a, b, c]
    (by intro i _; fin_cases i <;> assumption) he
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
  have hcard : ((Finset.univ : Finset (Fin 3)).card : ℝ) = 3 := by simp
  rw [hcard] at h
  simpa [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

/-- The two-level iterated power-mean inequality: `(∑_q ∑_q' a)^e ≤ (n²)^{e-1} ∑_q ∑_q' a^e`. -/
theorem rpow_sum_sum_le {n : ℕ} (a : Fin n → Fin n → ℝ) (ha : ∀ q q', 0 ≤ a q q')
    {e : ℝ} (he : 1 ≤ e) :
    (∑ q : Fin n, ∑ q' : Fin n, a q q') ^ e
      ≤ ((n : ℝ) ^ 2) ^ (e - 1) * ∑ q : Fin n, ∑ q' : Fin n, (a q q') ^ e := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (∑ q : Fin n, ∑ q' : Fin n, a q q') ^ e
      ≤ (n : ℝ) ^ (e - 1) * ∑ q : Fin n, (∑ q' : Fin n, a q q') ^ e := by
    have h := rpow_sum_le_card_mul_sum_rpow (Finset.univ : Finset (Fin n))
      (fun q => ∑ q' : Fin n, a q q') (fun q _ => Finset.sum_nonneg fun q' _ => ha q q') he
    simpa using h
  have h2 : ∀ q : Fin n, (∑ q' : Fin n, a q q') ^ e
      ≤ (n : ℝ) ^ (e - 1) * ∑ q' : Fin n, (a q q') ^ e := by
    intro q
    have h := rpow_sum_le_card_mul_sum_rpow (Finset.univ : Finset (Fin n))
      (fun q' => a q q') (fun q' _ => ha q q') he
    simpa using h
  refine h1.trans ?_
  calc (n : ℝ) ^ (e - 1) * ∑ q : Fin n, (∑ q' : Fin n, a q q') ^ e
      ≤ (n : ℝ) ^ (e - 1) * ∑ q : Fin n, ((n : ℝ) ^ (e - 1) * ∑ q' : Fin n, (a q q') ^ e) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => h2 q) (Real.rpow_nonneg hn _)
    _ = ((n : ℝ) ^ 2) ^ (e - 1) * ∑ q : Fin n, ∑ q' : Fin n, (a q q') ^ e := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rw [sq, ← Real.mul_rpow hn hn]

/-- The three-level iterated power-mean inequality. -/
theorem rpow_sum_sum_sum_le {n : ℕ} (a : Fin n → Fin n → Fin n → ℝ)
    (ha : ∀ q q' q'', 0 ≤ a q q' q'') {e : ℝ} (he : 1 ≤ e) :
    (∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n, a q q' q'') ^ e
      ≤ ((n : ℝ) ^ 3) ^ (e - 1)
        * ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n, (a q q' q'') ^ e := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n, a q q' q'') ^ e
      ≤ (n : ℝ) ^ (e - 1)
        * ∑ q : Fin n, (∑ q' : Fin n, ∑ q'' : Fin n, a q q' q'') ^ e := by
    have h := rpow_sum_le_card_mul_sum_rpow (Finset.univ : Finset (Fin n))
      (fun q => ∑ q' : Fin n, ∑ q'' : Fin n, a q q' q'')
      (fun q _ => Finset.sum_nonneg fun q' _ => Finset.sum_nonneg fun q'' _ => ha q q' q'') he
    simpa using h
  have h2 : ∀ q : Fin n, (∑ q' : Fin n, ∑ q'' : Fin n, a q q' q'') ^ e
      ≤ ((n : ℝ) ^ 2) ^ (e - 1) * ∑ q' : Fin n, ∑ q'' : Fin n, (a q q' q'') ^ e :=
    fun q => rpow_sum_sum_le (fun q' q'' => a q q' q'') (fun q' q'' => ha q q' q'') he
  refine h1.trans ?_
  calc (n : ℝ) ^ (e - 1) * ∑ q : Fin n, (∑ q' : Fin n, ∑ q'' : Fin n, a q q' q'') ^ e
      ≤ (n : ℝ) ^ (e - 1) * ∑ q : Fin n,
          (((n : ℝ) ^ 2) ^ (e - 1) * ∑ q' : Fin n, ∑ q'' : Fin n, (a q q' q'') ^ e) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => h2 q) (Real.rpow_nonneg hn _)
    _ = ((n : ℝ) ^ 3) ^ (e - 1) * ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n, (a q q' q'') ^ e := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rw [← Real.mul_rpow hn (pow_nonneg hn 2)]
        congr 1
        rw [sq]
        ring

/-- Weighted AM–GM for a product of squares: for block sizes `p i ≥ 1` with `∑ p i = m ≥ 1`
and nonnegative `F i`, `∏ i (F i)^2 ≤ ∑ i (p i/m) (F i)^{2m/p i}`. -/
theorem prod_sq_le_sum_weighted_rpow {r m : ℕ} (p : Fin r → ℕ) (hp : ∀ i, 1 ≤ p i)
    (hsum : ∑ i, p i = m) (hm : 1 ≤ m) (F : Fin r → ℝ) (hF : ∀ i, 0 ≤ F i) :
    ∏ i : Fin r, (F i) ^ 2
      ≤ ∑ i : Fin r, ((p i : ℝ) / (m : ℝ)) * (F i) ^ ((2 * (m : ℝ)) / (p i : ℝ)) := by
  classical
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm0ne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ (p i : ℝ) / (m : ℝ) :=
    fun i _ => div_nonneg (by positivity) hm0.le
  have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin r)), (p i : ℝ) / (m : ℝ) = 1 := by
    rw [← Finset.sum_div]
    rw [show ∑ i : Fin r, (p i : ℝ) = (m : ℝ) from by rw [← Nat.cast_sum, hsum]]
    exact div_self hm0ne
  have hz0 : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      0 ≤ (F i) ^ ((2 * (m : ℝ)) / (p i : ℝ)) := fun i _ => Real.rpow_nonneg (hF i) _
  have h := Real.geom_mean_le_arith_mean_weighted (s := (Finset.univ : Finset (Fin r)))
    (w := fun i => (p i : ℝ) / (m : ℝ))
    (z := fun i => (F i) ^ ((2 * (m : ℝ)) / (p i : ℝ))) hw0 hw1 hz0
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      ((F i) ^ ((2 * (m : ℝ)) / (p i : ℝ))) ^ ((p i : ℝ) / (m : ℝ)) = (F i) ^ 2 := by
    intro i _
    rw [← Real.rpow_mul (hF i)]
    have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast hp i
    have hexp : ((2 * (m : ℝ)) / (p i : ℝ)) * ((p i : ℝ) / (m : ℝ)) = 2 := by
      rw [div_mul_div_comm]
      field_simp
    rw [hexp, Real.rpow_two]
  rw [Finset.prod_congr rfl hfac] at h
  simpa using h

/-! ## 2. The real/complex bridge and the component computation -/

/-- The `k`-th iterated Fréchet derivative of a real-valued smooth function, evaluated on the
constant directions `Pi.single (γ j) 1`, has the same norm as the `k`-th iterated partial
derivative of its complexification. -/
theorem norm_iteratedFDeriv_eq_norm_pdVec_ofReal {n : ℕ} (k : ℕ) (γ : Fin k → Fin n)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k f x (fun j => Pi.single (γ j) (1 : ℝ))‖
      = ‖Work.Diff.STE.pdVec k γ (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) x‖ := by
  have hof : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) := by
    have h := Complex.ofRealCLM.contDiff.comp hf
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv k _ hof x γ]
  have hfun : (fun z : Fin n → ℝ => ((f z : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ f := by
    funext z; rw [Function.comp_apply, Complex.ofRealCLM_apply]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) Complex.ofRealCLM (f := f) (x := x) hf.contDiffAt
      (i := k) (WithTop.coe_le_coe.mpr le_top),
    ContinuousLinearMap.compContinuousMultilinearMap_coe]
  simp only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs]

/-- The `j`-th component of the `k`-th iterated derivative of a `Pi`-valued map is the `k`-th
iterated derivative of the `j`-th component. -/
lemma iteratedFDeriv_pi_apply {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (k : ℕ)
    (V : (Fin n → ℝ) → (ι → G)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (x : Fin n → ℝ) (w : Fin k → (Fin n → ℝ)) (j : ι) :
    (iteratedFDeriv ℝ k V x w) j = iteratedFDeriv ℝ k (fun y => V y j) x w := by
  have hfun : (fun y : Fin n → ℝ => V y j)
      = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => G) j) ∘ V := by
    funext y; rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => G) j) (f := V) (x := x) hV.contDiffAt
      (i := k) (WithTop.coe_le_coe.mpr le_top),
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **Block-norm bound for the state map `z ↦ (z, M z, N z)`.** -/
theorem norm_iteratedFDeriv_triple_apply_le {n p : ℕ} (hp : 1 ≤ p)
    (M : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (N : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (hM : ContDiff ℝ (⊤ : ℕ∞) M) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (x : Fin n → ℝ) (γ : Fin p → Fin n) :
    ‖iteratedFDeriv ℝ p (fun z : Fin n → ℝ => (z, (M z, N z))) x
        (fun j => Pi.single (γ j) (1 : ℝ))‖
      ≤ 1 + (∑ q : Fin n, ∑ q' : Fin n,
              ‖Work.Diff.STE.pdVec p γ (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
          + (∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n,
              ‖Work.Diff.STE.pdVec p γ (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖) := by
  have hMq : ∀ q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => M z q) :=
    fun q => contDiff_pi.mp hM q
  have hMqq : ∀ q q' : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => M z q q') :=
    fun q q' => contDiff_pi.mp (hMq q) q'
  have hNq : ∀ q : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => N z q) :=
    fun q => contDiff_pi.mp hN q
  have hNqq : ∀ q q' : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => N z q q') :=
    fun q q' => contDiff_pi.mp (hNq q) q'
  have hNqqq : ∀ q q' q'' : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => N z q q' q'') :=
    fun q q' q'' => contDiff_pi.mp (hNqq q q') q''
  set tup : Fin p → (Fin n → ℝ) := fun j => Pi.single (γ j) (1 : ℝ) with htup
  -- the iterated derivative of the tuple map is the tuple of the iterated derivatives
  have hprod : iteratedFDeriv ℝ p (fun z : Fin n → ℝ => (z, (M z, N z))) x
      = ((iteratedFDeriv ℝ p (fun z : Fin n → ℝ => z) x).prod
          ((iteratedFDeriv ℝ p M x).prod (iteratedFDeriv ℝ p N x))) := by
    rw [iteratedFDeriv_prodMk (f := fun z : Fin n → ℝ => z)
        (g := fun z : Fin n → ℝ => (M z, N z)) contDiff_id.contDiffAt
        (hM.contDiffAt.prodMk hN.contDiffAt) (i := p) (WithTop.coe_le_coe.mpr le_top),
      iteratedFDeriv_prodMk (f := M) (g := N) hM.contDiffAt hN.contDiffAt (i := p)
        (WithTop.coe_le_coe.mpr le_top)]
  rw [hprod, ContinuousMultilinearMap.prod_apply, ContinuousMultilinearMap.prod_apply,
    Prod.norm_mk, Prod.norm_mk]
  have hSM : 0 ≤ ∑ q : Fin n, ∑ q' : Fin n, ‖Work.Diff.STE.pdVec p γ
      (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖ :=
    Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun q' _ => norm_nonneg _
  have hSN : 0 ≤ ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n, ‖Work.Diff.STE.pdVec p γ
      (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖ :=
    Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun q' _ =>
      Finset.sum_nonneg fun q'' _ => norm_nonneg _
  refine max_le ?_ (max_le ?_ ?_)
  · -- the identity block
    have hsingle : ∀ j : Fin p, ‖tup j‖ ≤ 1 := by
      intro j
      rw [htup]
      simpa using norm_pi_single_le' (γ j) (1 : ℝ)
    have hprod1 : ∏ j : Fin p, ‖tup j‖ ≤ 1 :=
      Finset.prod_le_one₀ (s := (Finset.univ : Finset (Fin p))) (f := fun j => ‖tup j‖)
        (fun j _ => norm_nonneg (tup j)) (fun j _ => hsingle j)
    calc ‖(iteratedFDeriv ℝ p (fun z : Fin n → ℝ => z) x) tup‖
        ≤ ‖iteratedFDeriv ℝ p (fun z : Fin n → ℝ => z) x‖ * ∏ j, ‖tup j‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ 1 * 1 :=
          mul_le_mul (Work.Diff.STE.flat.norm_iteratedFDeriv_self_le x hp) hprod1
            (Finset.prod_nonneg fun j _ => norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
      _ ≤ 1 + (∑ q, ∑ q', ‖Work.Diff.STE.pdVec p γ
              (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
            + (∑ q, ∑ q', ∑ q'', ‖Work.Diff.STE.pdVec p γ
              (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖) := by linarith
  · -- the matrix block
    have hMeq : ‖(iteratedFDeriv ℝ p M x) tup‖ ≤ ∑ q : Fin n, ∑ q' : Fin n,
        ‖Work.Diff.STE.pdVec p γ (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖ := by
      have hpi1 : ‖(iteratedFDeriv ℝ p M x) tup‖
          ≤ ∑ q : Fin n, ‖((iteratedFDeriv ℝ p M x) tup) q‖ :=
        (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun q _ => norm_nonneg _)).mpr
          fun q => Finset.single_le_sum (fun q _ => norm_nonneg _) (Finset.mem_univ q)
      have hpi2 : ∀ q : Fin n, ‖((iteratedFDeriv ℝ p M x) tup) q‖
          ≤ ∑ q' : Fin n, ‖(((iteratedFDeriv ℝ p M x) tup) q) q'‖ := fun q =>
        (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun q' _ => norm_nonneg _)).mpr
          fun q' => Finset.single_le_sum (fun q' _ => norm_nonneg _) (Finset.mem_univ q')
      have hcoord : ∀ q q' : Fin n,
          (((iteratedFDeriv ℝ p M x) tup) q) q'
            = iteratedFDeriv ℝ p (fun z : Fin n → ℝ => M z q q') x tup := by
        intro q q'
        rw [iteratedFDeriv_pi_apply p M hM x tup q]
        exact iteratedFDeriv_pi_apply p (fun z : Fin n → ℝ => M z q) (hMq q) x tup q'
      refine hpi1.trans (Finset.sum_le_sum fun q _ =>
        (hpi2 q).trans (Finset.sum_le_sum fun q' _ => ?_))
      rw [hcoord q q', norm_iteratedFDeriv_eq_norm_pdVec_ofReal p γ _ (hMqq q q') x]
    exact hMeq.trans (by linarith)
  · -- the tensor block
    have hNeq : ‖(iteratedFDeriv ℝ p N x) tup‖ ≤ ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n,
        ‖Work.Diff.STE.pdVec p γ (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖ := by
      have hpi1 : ‖(iteratedFDeriv ℝ p N x) tup‖
          ≤ ∑ q : Fin n, ‖((iteratedFDeriv ℝ p N x) tup) q‖ :=
        (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun q _ => norm_nonneg _)).mpr
          fun q => Finset.single_le_sum (fun q _ => norm_nonneg _) (Finset.mem_univ q)
      have hpi2 : ∀ q : Fin n, ‖((iteratedFDeriv ℝ p N x) tup) q‖
          ≤ ∑ q' : Fin n, ‖(((iteratedFDeriv ℝ p N x) tup) q) q'‖ := fun q =>
        (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun q' _ => norm_nonneg _)).mpr
          fun q' => Finset.single_le_sum (fun q' _ => norm_nonneg _) (Finset.mem_univ q')
      have hpi3 : ∀ q q' : Fin n, ‖(((iteratedFDeriv ℝ p N x) tup) q) q'‖
          ≤ ∑ q'' : Fin n, ‖((((iteratedFDeriv ℝ p N x) tup) q) q') q''‖ := fun q q' =>
        (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun q'' _ => norm_nonneg _)).mpr
          fun q'' => Finset.single_le_sum (fun q'' _ => norm_nonneg _) (Finset.mem_univ q'')
      have hcoord : ∀ q q' q'' : Fin n,
          ((((iteratedFDeriv ℝ p N x) tup) q) q') q''
            = iteratedFDeriv ℝ p (fun z : Fin n → ℝ => N z q q' q'') x tup := by
        intro q q' q''
        rw [iteratedFDeriv_pi_apply p N hN x tup q,
          iteratedFDeriv_pi_apply p (fun z : Fin n → ℝ => N z q) (hNq q) x tup q']
        exact iteratedFDeriv_pi_apply p (fun z : Fin n → ℝ => N z q q') (hNqq q q') x tup q''
      refine hpi1.trans (Finset.sum_le_sum fun q _ => (hpi2 q).trans (Finset.sum_le_sum fun q' _ =>
        (hpi3 q q').trans (Finset.sum_le_sum fun q'' _ => ?_)))
      rw [hcoord q q' q'', norm_iteratedFDeriv_eq_norm_pdVec_ofReal p γ _ (hNqqq q q' q'') x]
    exact hNeq.trans (by linarith)

/-- **Faà di Bruno for the smooth composite `z ↦ Φ (z, M z, N z)`.** -/
theorem pdVec_triple_expand {n m : ℕ}
    (Φ : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (M : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (N : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (hM : ContDiff ℝ (⊤ : ℕ∞) M) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (β : Fin m → Fin n) (x : Fin n → ℝ) :
    Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((Φ (z, M z, N z) : ℝ) : ℂ)) x
      = ((∑ c : OrderedFinpartition m,
            (iteratedFDeriv ℝ c.length Φ (x, M x, N x))
              (fun i => iteratedFDeriv ℝ (c.partSize i)
                (fun z : Fin n → ℝ => (z, M z, N z)) x
                (fun j' => Pi.single (β (c.emb i j')) (1 : ℝ))) : ℝ) : ℂ) := by
  have hVsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => (z, (M z, N z))) :=
    contDiff_id.prodMk (hM.prodMk hN)
  have hφsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => Φ (z, M z, N z)) := hΦ.comp hVsm
  have hcsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => ((Φ (z, M z, N z) : ℝ) : ℂ)) := by
    have h := Complex.ofRealCLM.contDiff.comp hφsm
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ hcsm x β]
  have hfun : (fun z : Fin n → ℝ => ((Φ (z, M z, N z) : ℝ) : ℂ))
      = ⇑Complex.ofRealCLM ∘ (fun z : Fin n → ℝ => Φ (z, M z, N z)) := by
    funext z; rw [Function.comp_apply, Complex.ofRealCLM_apply]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) Complex.ofRealCLM
      (f := fun z : Fin n → ℝ => Φ (z, M z, N z)) (x := x) hφsm.contDiffAt
      (i := m) (WithTop.coe_le_coe.mpr le_top),
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    Complex.ofRealCLM_apply]
  congr 1
  have hFdB : (iteratedFDeriv ℝ m
        (fun y : Fin n → ℝ => Φ ((fun z : Fin n → ℝ => (z, M z, N z)) y)) x)
        (fun j => Pi.single (β j) (1 : ℝ))
      = ∑ c : OrderedFinpartition m,
            (iteratedFDeriv ℝ c.length Φ ((fun z : Fin n → ℝ => (z, M z, N z)) x))
              (fun i => iteratedFDeriv ℝ (c.partSize i)
                (fun z : Fin n → ℝ => (z, M z, N z)) x
                ((fun j => Pi.single (β j) (1 : ℝ)) ∘ c.emb i)) :=
    Work.Diff.STE.flat.iteratedFDeriv_comp_sum_gen m Φ hΦ
      (fun z : Fin n → ℝ => (z, M z, N z)) hVsm x (fun j => Pi.single (β j) (1 : ℝ))
  rw [show (iteratedFDeriv ℝ m (fun z : Fin n → ℝ => Φ (z, M z, N z)) x)
        (fun j => Pi.single (β j) (1 : ℝ))
      = (iteratedFDeriv ℝ m
          (fun y : Fin n → ℝ => Φ ((fun z : Fin n → ℝ => (z, M z, N z)) y)) x)
          (fun j => Pi.single (β j) (1 : ℝ)) from rfl]
  rw [hFdB]
  rfl

/-! ## 3. The composite Gagliardo–Nirenberg estimate -/

theorem compositeGnR (n m : ℕ) (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ) → ℝ)
        (M : (Fin n → ℝ) → Fin n → Fin n → ℝ)
        (N : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
        (β : Fin m → Fin n),
        ContDiff ℝ (⊤ : ℕ∞) Φ →
        (∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun z => M z p q)) →
        (∀ p q r, ContDiff ℝ (⊤ : ℕ∞) (fun z => N z p q r)) →
        (∀ p q, Work.Diff.STE.Periodic1 (fun z => M z p q)) →
        (∀ p q r, Work.Diff.STE.Periodic1 (fun z => N z p q r)) →
        (∀ z p q, |M z p q| ≤ B) →
        (∀ z p q r, |N z p q r| ≤ B) →
        (∀ (k' : ℕ), k' ≤ m → ∀ z, ‖iteratedFDeriv ℝ k' Φ (z, M z, N z)‖ ≤ D) →
        Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
            (fun z => ((Φ (z, M z, N z) : ℝ) : ℂ)))
          ≤ C * (1 + ∑ p : Fin n, ∑ q : Fin n,
                    Work.Diff.STE.ENormSq m (fun z => ((M z p q : ℝ) : ℂ))
                  + ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
                    Work.Diff.STE.ENormSq m (fun z => ((N z p q r : ℝ) : ℂ))) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- ## The case `m = 0`
    subst hm0
    haveI : IsFiniteMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      Work.Diff.STE.GN.unitCube_isFiniteMeasure_restrict (ι := Fin n)
    refine ⟨max (D ^ 2) 1, le_trans zero_le_one (le_max_right (D ^ 2) 1), ?_⟩
    intro Φ M N β hΦ hMsm hNsm hMper hNper hMb hNb hjet
    rw [ENormSq_zero_unitCube]
    have hpv : Work.Diff.STE.pdVec 0 β (fun z : Fin n → ℝ => ((Φ (z, M z, N z) : ℝ) : ℂ))
        = fun z : Fin n → ℝ => ((Φ (z, M z, N z) : ℝ) : ℂ) := by
      funext z
      simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]
    rw [hpv]
    have hD0 : ∀ x : Fin n → ℝ, |Φ (x, M x, N x)| ≤ D := by
      intro x
      have h := hjet 0 (le_refl 0) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
      exact h
    have hE0 : 0 ≤ (∑ p : Fin n, ∑ q : Fin n,
          Work.Diff.STE.ENormSq 0 (fun z => ((M z p q : ℝ) : ℂ)))
        + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
          Work.Diff.STE.ENormSq 0 (fun z => ((N z p q r : ℝ) : ℂ))) :=
      add_nonneg
        (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ENormSq_nonnegR 0 _)
        (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
          Finset.sum_nonneg fun r _ => ENormSq_nonnegR 0 _)
    calc ∫ x in Work.Diff.STE.unitCube, ‖((Φ (x, M x, N x) : ℝ) : ℂ)‖ ^ 2
        ≤ ∫ x in Work.Diff.STE.unitCube, (D ^ 2 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => by positivity)
            (integrable_const _) (Filter.Eventually.of_forall fun x => ?_)
          show ‖((Φ (x, M x, N x) : ℝ) : ℂ)‖ ^ 2 ≤ D ^ 2
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hD0 x) 2
      _ = D ^ 2 := integral_const_unitCube' _
      _ ≤ max (D ^ 2) 1 * (1 + (∑ p : Fin n, ∑ q : Fin n,
              Work.Diff.STE.ENormSq 0 (fun z => ((M z p q : ℝ) : ℂ)))
            + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
              Work.Diff.STE.ENormSq 0 (fun z => ((N z p q r : ℝ) : ℂ)))) := by
          have h1 : (1 : ℝ) ≤ 1 + (∑ p : Fin n, ∑ q : Fin n,
                Work.Diff.STE.ENormSq 0 (fun z => ((M z p q : ℝ) : ℂ)))
              + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
                Work.Diff.STE.ENormSq 0 (fun z => ((N z p q r : ℝ) : ℂ))) := by
            linarith
          have h2 : 0 ≤ max (D ^ 2) 1 := le_trans zero_le_one (le_max_right (D ^ 2) 1)
          calc D ^ 2 ≤ max (D ^ 2) 1 := le_max_left _ _
            _ = max (D ^ 2) 1 * 1 := (mul_one _).symm
            _ ≤ max (D ^ 2) 1 * (1 + (∑ p : Fin n, ∑ q : Fin n,
                  Work.Diff.STE.ENormSq 0 (fun z => ((M z p q : ℝ) : ℂ)))
                + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
                  Work.Diff.STE.ENormSq 0 (fun z => ((N z p q r : ℝ) : ℂ)))) :=
                mul_le_mul_of_nonneg_left h1 h2
  · -- ## The case `m ≥ 1`
    obtain ⟨CGN, hCGN0, hGN⟩ := Work.Diff.STE.Lead.GalTame.ResidGn.gnSharpR (ι := Fin n) m
    haveI : IsFiniteMeasure (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
      Work.Diff.STE.GN.unitCube_isFiniteMeasure_restrict (ι := Fin n)
    set CGN' : ℝ := max 1 CGN with hCGN'def
    set B' : ℝ := max 1 B with hB'def
    have hCGN'0 : 0 ≤ CGN' := by rw [hCGN'def]; positivity
    have hB'0 : 0 ≤ B' := by rw [hB'def]; positivity
    have hB'1 : 1 ≤ B' := by rw [hB'def]; exact le_max_left 1 B
    set KM : ℝ := ((n : ℝ) ^ 2 + 1) ^ (2 * (m : ℝ)) * CGN' * B' ^ (2 * (m : ℝ)) with hKMdef
    set KN : ℝ := ((n : ℝ) ^ 3 + 1) ^ (2 * (m : ℝ)) * CGN' * B' ^ (2 * (m : ℝ)) with hKNdef
    have hKM0 : 0 ≤ KM := by rw [hKMdef]; positivity
    have hKN0 : 0 ≤ KN := by rw [hKNdef]; positivity
    set Q : ℝ := 3 ^ (2 * (m : ℝ)) * (1 + (KM + KN)) with hQdef
    have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
    set Np : ℝ := (Fintype.card (OrderedFinpartition m) : ℝ) with hNpdef
    have hNp0 : 0 ≤ Np := by rw [hNpdef]; positivity
    set Cst : ℝ := Np ^ 2 * (D ^ 2 + 1) * ((m : ℝ) + 1) * (Q + 1) with hCstdef
    refine ⟨Cst, ?_, ?_⟩
    · rw [hCstdef, hNpdef, hQdef, hKMdef, hKNdef, hCGN'def, hB'def]; positivity
    · intro Φ M N β hΦ hMsm hNsm hMper hNper hMb hNb hjet
      have hM : ContDiff ℝ (⊤ : ℕ∞) M := contDiff_pi.mpr fun p => contDiff_pi.mpr fun q => hMsm p q
      have hN : ContDiff ℝ (⊤ : ℕ∞) N :=
        contDiff_pi.mpr fun p => contDiff_pi.mpr fun q => contDiff_pi.mpr fun r => hNsm p q r
      -- complexified components
      have hMcs : ∀ p q : Fin n, ContDiff ℝ (⊤ : ℕ∞)
          (fun z : Fin n → ℝ => ((M z p q : ℝ) : ℂ)) := by
        intro p q
        have h := Complex.ofRealCLM.contDiff.comp (hMsm p q)
        simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
      have hNcs : ∀ p q r : Fin n, ContDiff ℝ (⊤ : ℕ∞)
          (fun z : Fin n → ℝ => ((N z p q r : ℝ) : ℂ)) := by
        intro p q r
        have h := Complex.ofRealCLM.contDiff.comp (hNsm p q r)
        simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
      have hMcp : ∀ p q : Fin n,
          Work.Diff.STE.Periodic1 (fun z : Fin n → ℝ => ((M z p q : ℝ) : ℂ)) := by
        intro p q i z
        exact congrArg (fun t : ℝ => ((t : ℂ))) (hMper p q i z)
      have hNcp : ∀ p q r : Fin n,
          Work.Diff.STE.Periodic1 (fun z : Fin n → ℝ => ((N z p q r : ℝ) : ℂ)) := by
        intro p q r i z
        exact congrArg (fun t : ℝ => ((t : ℂ))) (hNper p q r i z)
      have hMcb : ∀ p q : Fin n, ∀ z, ‖(fun y : Fin n → ℝ => ((M y p q : ℝ) : ℂ)) z‖ ≤ B' := by
        intro p q z
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_trans (hMb z p q) (le_max_right 1 B)
      have hNcb : ∀ p q r : Fin n, ∀ z, ‖(fun y : Fin n → ℝ => ((N y p q r : ℝ) : ℂ)) z‖ ≤ B' := by
        intro p q r z
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_trans (hNb z p q r) (le_max_right 1 B)
      -- the Gagliardo–Nirenberg wrapper
      have hGNapp : ∀ (f : (Fin n → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f →
          Work.Diff.STE.Periodic1 f → (∀ x, ‖f x‖ ≤ B') →
          ∀ (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) (γ : Fin j → Fin n),
          ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec j γ f x‖ ^ ((2 * (m : ℝ)) / (j : ℝ))
            ≤ CGN' * B' ^ (2 * (m : ℝ)) * Work.Diff.STE.ENormSq m f := by
        intro f hf hper hfU j hj hjm γ
        have h := hGN B' f hf hper hfU j hj hjm γ
        have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
        have hjm' : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hjm
        have hq2 : 0 ≤ (2 * (m : ℝ)) / (j : ℝ) - 2 := by
          have h2 : 2 ≤ (2 * (m : ℝ)) / (j : ℝ) := by
            rw [le_div_iff₀ hj0]
            nlinarith
          linarith
        have hq2le : (2 * (m : ℝ)) / (j : ℝ) - 2 ≤ 2 * (m : ℝ) := by
          have h2 : (2 * (m : ℝ)) / (j : ℝ) ≤ 2 * (m : ℝ) := by
            rw [div_le_iff₀ hj0]
            have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
            nlinarith
          linarith
        have hEN : 0 ≤ Work.Diff.STE.ENormSq m f := ENormSq_nonnegR m f
        have hpow : B' ^ (2 * (m : ℝ) / (j : ℝ) - 2) ≤ B' ^ (2 * (m : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hB'1 hq2le
        refine h.trans ?_
        refine mul_le_mul_of_nonneg_right ?_ hEN
        exact (mul_le_mul_of_nonneg_right (le_max_right 1 CGN)
          (Real.rpow_nonneg hB'0 _)).trans (mul_le_mul_of_nonneg_left hpow hCGN'0)
      -- the Faà di Bruno expansion
      have hexpand : ∀ x : Fin n → ℝ,
          Work.Diff.STE.pdVec m β (fun z => ((Φ (z, M z, N z) : ℝ) : ℂ)) x
            = ((∑ c : OrderedFinpartition m, fbTerm Φ M N β c x : ℝ) : ℂ) := by
        intro x
        rw [pdVec_triple_expand Φ hΦ M N hM hN β x]
        congr 1
      rw [ENormSq_zero_unitCube]
      have hnorm : ∀ x : Fin n → ℝ,
          ‖Work.Diff.STE.pdVec m β (fun z => ((Φ (z, M z, N z) : ℝ) : ℂ)) x‖
            = |∑ c : OrderedFinpartition m, fbTerm Φ M N β c x| := by
        intro x
        rw [hexpand x, Complex.norm_real, Real.norm_eq_abs]
      set Einner : ℝ := (∑ p : Fin n, ∑ q : Fin n,
            Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((M z p q : ℝ) : ℂ)))
          + (∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
            Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((N z p q r : ℝ) : ℂ))) with hEinnerdef
      have hEinner0 : 0 ≤ Einner := by
        rw [hEinnerdef]
        exact add_nonneg
          (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ENormSq_nonnegR m _)
          (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
            Finset.sum_nonneg fun r _ => ENormSq_nonnegR m _)
      -- the two sums of block norms and the block bound
      set SM : (c : OrderedFinpartition m) → Fin c.length → (Fin n → ℝ) → ℝ := fun c i x =>
        ∑ q : Fin n, ∑ q' : Fin n, ‖Work.Diff.STE.pdVec (c.partSize i)
            (fun j' => β (c.emb i j')) (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖ with hSMdef
      set SN : (c : OrderedFinpartition m) → Fin c.length → (Fin n → ℝ) → ℝ := fun c i x =>
        ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n, ‖Work.Diff.STE.pdVec (c.partSize i)
            (fun j' => β (c.emb i j')) (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖ with hSNdef
      set BB : (c : OrderedFinpartition m) → Fin c.length → (Fin n → ℝ) → ℝ :=
        fun c i x => 1 + SM c i x + SN c i x with hBBdef
      have hSM0 : ∀ (c : OrderedFinpartition m) (i : Fin c.length) (x : Fin n → ℝ), 0 ≤ SM c i x := by
        intro c i x
        rw [hSMdef]
        exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun q' _ => norm_nonneg _
      have hSN0 : ∀ (c : OrderedFinpartition m) (i : Fin c.length) (x : Fin n → ℝ), 0 ≤ SN c i x := by
        intro c i x
        rw [hSNdef]
        exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun q' _ =>
          Finset.sum_nonneg fun q'' _ => norm_nonneg _
      have hBB0 : ∀ (c : OrderedFinpartition m) (i : Fin c.length) (x : Fin n → ℝ), 0 ≤ BB c i x := by
        intro c i x
        rw [hBBdef]
        linarith [hSM0 c i x, hSN0 c i x]
      have hSMcont : ∀ (c : OrderedFinpartition m) (i : Fin c.length),
          Continuous (fun x : Fin n → ℝ => SM c i x) := by
        intro c i
        rw [hSMdef]
        exact continuous_finset_sum _ fun q _ => continuous_finset_sum _ fun q' _ =>
          (Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
            (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ))
            ((hMcs q q').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm
      have hSNcont : ∀ (c : OrderedFinpartition m) (i : Fin c.length),
          Continuous (fun x : Fin n → ℝ => SN c i x) := by
        intro c i
        rw [hSNdef]
        exact continuous_finset_sum _ fun q _ => continuous_finset_sum _ fun q' _ =>
          continuous_finset_sum _ fun q'' _ =>
            (Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
              (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ))
              ((hNcs q q' q'').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm
      have hBBcont : ∀ (c : OrderedFinpartition m) (i : Fin c.length),
          Continuous (fun x : Fin n → ℝ => BB c i x) := by
        intro c i
        rw [hBBdef]
        exact (continuous_const.add (hSMcont c i)).add (hSNcont c i)
      have hepos : ∀ (c : OrderedFinpartition m) (i : Fin c.length),
          0 < (2 * (m : ℝ)) / (c.partSize i : ℝ) := by
        intro c i
        have hp0 : (0 : ℝ) < (c.partSize i : ℝ) := by exact_mod_cast c.partSize_pos i
        have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
        exact div_pos (by linarith) hp0
      have he1 : ∀ (c : OrderedFinpartition m) (i : Fin c.length),
          1 ≤ (2 * (m : ℝ)) / (c.partSize i : ℝ) := by
        intro c i
        have hp0 : (0 : ℝ) < (c.partSize i : ℝ) := by exact_mod_cast c.partSize_pos i
        have hple : (c.partSize i : ℝ) ≤ (m : ℝ) := by exact_mod_cast c.partSize_le i
        rw [le_div_iff₀ hp0]
        nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
      have he2m : ∀ (c : OrderedFinpartition m) (i : Fin c.length),
          (2 * (m : ℝ)) / (c.partSize i : ℝ) - 1 ≤ 2 * (m : ℝ) := by
        intro c i
        have hp0 : (0 : ℝ) < (c.partSize i : ℝ) := by exact_mod_cast c.partSize_pos i
        have hp1 : (1 : ℝ) ≤ (c.partSize i : ℝ) := by exact_mod_cast c.partSize_pos i
        have h2 : (2 * (m : ℝ)) / (c.partSize i : ℝ) ≤ 2 * (m : ℝ) := by
          rw [div_le_iff₀ hp0]
          nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
        linarith
      -- (1) the Faà di Bruno term is bounded by the block bound
      have hfb : ∀ (c : OrderedFinpartition m) (x : Fin n → ℝ),
          |fbTerm Φ M N β c x| ≤ D * ∏ i : Fin c.length, BB c i x := by
        intro c x
        rw [show fbTerm Φ M N β c x
            = (iteratedFDeriv ℝ c.length Φ (x, M x, N x))
              (fun i : Fin c.length => iteratedFDeriv ℝ (c.partSize i)
                (fun z : Fin n → ℝ => (z, M z, N z)) x
                (fun j' => Pi.single (β (c.emb i j')) (1 : ℝ))) from rfl]
        rw [← Real.norm_eq_abs]
        have hop := ContinuousMultilinearMap.le_opNorm
          (iteratedFDeriv ℝ c.length Φ (x, M x, N x))
          (fun i : Fin c.length => iteratedFDeriv ℝ (c.partSize i)
            (fun z : Fin n → ℝ => (z, M z, N z)) x
            (fun j' => Pi.single (β (c.emb i j')) (1 : ℝ)))
        have hjetD : ‖iteratedFDeriv ℝ c.length Φ (x, M x, N x)‖ ≤ D :=
          hjet c.length c.length_le x
        have hbb : ∀ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i)
            (fun z : Fin n → ℝ => (z, M z, N z)) x
            (fun j' => Pi.single (β (c.emb i j')) (1 : ℝ))‖ ≤ BB c i x := by
          intro i
          have h := norm_iteratedFDeriv_triple_apply_le (c.partSize_pos i) M N hM hN x
            (fun j' => β (c.emb i j'))
          rw [hBBdef, hSMdef, hSNdef]
          exact h
        have hprod : ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i)
              (fun z : Fin n → ℝ => (z, M z, N z)) x
              (fun j' => Pi.single (β (c.emb i j')) (1 : ℝ))‖ ≤ ∏ i : Fin c.length, BB c i x :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hbb i)
        exact hop.trans (mul_le_mul hjetD hprod (Finset.prod_nonneg fun i _ => norm_nonneg _) hD)
      -- (2) AM-GM
      have hagm : ∀ (c : OrderedFinpartition m) (x : Fin n → ℝ),
          ∏ i : Fin c.length, (BB c i x) ^ 2
            ≤ ∑ i : Fin c.length, ((c.partSize i : ℝ) / (m : ℝ))
                * (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) := fun c x =>
        prod_sq_le_sum_weighted_rpow (fun i => c.partSize i) (fun i => c.partSize_pos i)
          (Work.Diff.STE.flat.sum_partSize_flat c) hmpos (fun i => BB c i x) (fun i => hBB0 c i x)
      have hwsum : ∀ c : OrderedFinpartition m,
          ∑ i : Fin c.length, ((c.partSize i : ℝ) / (m : ℝ)) = 1 := by
        intro c
        rw [← Finset.sum_div,
          show (∑ i : Fin c.length, ((c.partSize i : ℕ) : ℝ)) = (m : ℝ) from by
            rw [← Nat.cast_sum, Work.Diff.STE.flat.sum_partSize_flat c]]
        exact div_self (by exact_mod_cast (ne_of_gt hmpos))
      -- (3) the bound on each block, by power mean and Gagliardo–Nirenberg
      have hblock : ∀ (c : OrderedFinpartition m) (i : Fin c.length),
          ∫ x in Work.Diff.STE.unitCube, (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
            ≤ Q * (1 + Einner) := by
        intro c i
        have hpm : ∀ x : Fin n → ℝ, (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
            ≤ 3 ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
              * (1 + (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
                   + (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) := by
          intro x
          have h := rpow_three_le 1 (SM c i x) (SN c i x) ((2 * (m : ℝ)) / (c.partSize i : ℝ))
            (by norm_num) (hSM0 c i x) (hSN0 c i x) (he1 c i)
          rw [Real.one_rpow] at h
          simp only [hBBdef]
          exact h
        have hSMpow : Continuous (fun x : Fin n → ℝ =>
            (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) :=
          (hSMcont c i).rpow_const (fun x => Or.inr (le_of_lt (hepos c i)))
        have hSNpow : Continuous (fun x : Fin n → ℝ =>
            (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) :=
          (hSNcont c i).rpow_const (fun x => Or.inr (le_of_lt (hepos c i)))
        have hUp : Continuous (fun x : Fin n → ℝ =>
            3 ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
              * (1 + (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
                   + (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))) :=
          continuous_const.mul ((continuous_const.add hSMpow).add hSNpow)
        have hint2 : ∫ x in Work.Diff.STE.unitCube,
              3 ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
                * (1 + (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
                     + (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))
            = 3 ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
              * (1 + (∫ x in Work.Diff.STE.unitCube,
                    (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))
                   + (∫ x in Work.Diff.STE.unitCube,
                    (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))) := by
          rw [MeasureTheory.integral_const_mul]
          congr 1
          exact integral_one_add_add_unitCube
            (fun x : Fin n → ℝ => (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))
            (fun x : Fin n → ℝ => (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))
            (integrableOn_unitCube_of_continuous_real hSMpow)
            (integrableOn_unitCube_of_continuous_real hSNpow)
        have hSMbound : ∫ x in Work.Diff.STE.unitCube,
              (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) ≤ KM * Einner := by
          have hpm2 : ∀ x : Fin n → ℝ, (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
              ≤ ((n : ℝ) ^ 2 + 1) ^ (2 * (m : ℝ))
                * ∑ q : Fin n, ∑ q' : Fin n,
                    (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                      (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
                      ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) := by
            intro x
            have h1 := rpow_sum_sum_le (fun q q' : Fin n =>
                ‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                  (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
              (fun q q' => norm_nonneg _) (he1 c i)
            rw [hSMdef]
            refine h1.trans ?_
            have hbase : ((n : ℝ) ^ 2) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
                ≤ ((n : ℝ) ^ 2 + 1) ^ (2 * (m : ℝ)) :=
              (Real.rpow_le_rpow (sq_nonneg (n : ℝ))
                (by linarith [sq_nonneg (n : ℝ)]) (by linarith [he1 c i])).trans
                (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (n : ℝ)]) (by linarith [he2m c i]))
            exact mul_le_mul_of_nonneg_right hbase (Finset.sum_nonneg fun q _ =>
              Finset.sum_nonneg fun q' _ => Real.rpow_nonneg (norm_nonneg _) _)
          have hsumcont : Continuous (fun x : Fin n → ℝ => ∑ q : Fin n, ∑ q' : Fin n,
              (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
                ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) := by
            refine continuous_finset_sum _ fun q _ => continuous_finset_sum _ fun q' _ => ?_
            exact ((Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
              (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ))
              ((hMcs q q').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm).rpow_const
              (fun x => Or.inr (le_of_lt (hepos c i)))
          have hterm : ∀ q q' : Fin n, ∫ x in Work.Diff.STE.unitCube,
                (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                  (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
                  ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
              ≤ CGN' * B' ^ (2 * (m : ℝ))
                * Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) :=
            fun q q' => hGNapp (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ))
              (hMcs q q') (hMcp q q') (hMcb q q') (c.partSize i) (c.partSize_pos i)
              (c.partSize_le i) (fun j' => β (c.emb i j'))
          have heqM : (∑ q : Fin n, ∑ q' : Fin n, CGN' * B' ^ (2 * (m : ℝ))
                * Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)))
              = CGN' * B' ^ (2 * (m : ℝ)) * ∑ q : Fin n, ∑ q' : Fin n,
                  Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) := by
            simp only [Finset.mul_sum]
          calc ∫ x in Work.Diff.STE.unitCube, (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
              ≤ ∫ x in Work.Diff.STE.unitCube, ((n : ℝ) ^ 2 + 1) ^ (2 * (m : ℝ))
                  * ∑ q : Fin n, ∑ q' : Fin n,
                      (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                        (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
                        ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) :=
                MeasureTheory.integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hSM0 c i x) _)
                  (integrableOn_unitCube_of_continuous_real (continuous_const.mul hsumcont))
                  (Filter.Eventually.of_forall hpm2)
            _ = ((n : ℝ) ^ 2 + 1) ^ (2 * (m : ℝ)) * ∑ q : Fin n, ∑ q' : Fin n,
                  ∫ x in Work.Diff.STE.unitCube,
                    (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                      (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) x‖)
                      ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) := by
                rw [MeasureTheory.integral_const_mul]
                congr 1
                rw [MeasureTheory.integral_finsetSum]
                · refine Finset.sum_congr rfl fun q _ => ?_
                  rw [MeasureTheory.integral_finsetSum]
                  exact fun q' _ => integrableOn_unitCube_of_continuous_real
                    (((Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                      (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ))
                      ((hMcs q q').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm).rpow_const
                      (fun x => Or.inr (le_of_lt (hepos c i))))
                · intro q _
                  exact integrableOn_unitCube_of_continuous_real
                    (continuous_finset_sum _ fun q' _ =>
                      ((Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                        (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ))
                        ((hMcs q q').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm).rpow_const
                        (fun x => Or.inr (le_of_lt (hepos c i))))
            _ ≤ ((n : ℝ) ^ 2 + 1) ^ (2 * (m : ℝ)) * ∑ q : Fin n, ∑ q' : Fin n,
                  CGN' * B' ^ (2 * (m : ℝ))
                    * Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((M z q q' : ℝ) : ℂ)) := by
                refine mul_le_mul_of_nonneg_left
                  (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun q' _ => hterm q q')
                  (by positivity)
            _ ≤ ((n : ℝ) ^ 2 + 1) ^ (2 * (m : ℝ))
                  * (CGN' * B' ^ (2 * (m : ℝ)) * Einner) := by
                rw [heqM, hEinnerdef]
                refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
                  (by positivity)
                exact le_add_of_nonneg_right (Finset.sum_nonneg fun p _ =>
                  Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun r _ => ENormSq_nonnegR m _)
            _ = KM * Einner := by rw [hKMdef]; ring
        have hSNbound : ∫ x in Work.Diff.STE.unitCube,
              (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) ≤ KN * Einner := by
          have hpm2 : ∀ x : Fin n → ℝ, (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
              ≤ ((n : ℝ) ^ 3 + 1) ^ (2 * (m : ℝ))
                * ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n,
                    (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                      (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖)
                      ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) := by
            intro x
            have h1 := rpow_sum_sum_sum_le (fun q q' q'' : Fin n =>
                ‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                  (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖)
              (fun q q' q'' => norm_nonneg _) (he1 c i)
            rw [hSNdef]
            refine h1.trans ?_
            have hbase : ((n : ℝ) ^ 3) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
                ≤ ((n : ℝ) ^ 3 + 1) ^ (2 * (m : ℝ)) :=
              (Real.rpow_le_rpow (by positivity)
                (by linarith [show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity])
                (by linarith [he1 c i])).trans
                (Real.rpow_le_rpow_of_exponent_le (by nlinarith [show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity]) (by linarith [he2m c i]))
            exact mul_le_mul_of_nonneg_right hbase (Finset.sum_nonneg fun q _ =>
              Finset.sum_nonneg fun q' _ => Finset.sum_nonneg fun q'' _ =>
                Real.rpow_nonneg (norm_nonneg _) _)
          have hsumcont : Continuous (fun x : Fin n → ℝ => ∑ q : Fin n, ∑ q' : Fin n,
              ∑ q'' : Fin n,
              (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖)
                ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) := by
            refine continuous_finset_sum _ fun q _ => continuous_finset_sum _ fun q' _ =>
              continuous_finset_sum _ fun q'' _ => ?_
            exact ((Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
              (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ))
              ((hNcs q q' q'').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm).rpow_const
              (fun x => Or.inr (le_of_lt (hepos c i)))
          have hterm : ∀ q q' q'' : Fin n, ∫ x in Work.Diff.STE.unitCube,
                (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                  (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖)
                  ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
              ≤ CGN' * B' ^ (2 * (m : ℝ))
                * Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) :=
            fun q q' q'' => hGNapp (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ))
              (hNcs q q' q'') (hNcp q q' q'') (hNcb q q' q'') (c.partSize i) (c.partSize_pos i)
              (c.partSize_le i) (fun j' => β (c.emb i j'))
          have heqN : (∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n, CGN' * B' ^ (2 * (m : ℝ))
                * Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)))
              = CGN' * B' ^ (2 * (m : ℝ)) * ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n,
                  Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) := by
            simp only [Finset.mul_sum]
          calc ∫ x in Work.Diff.STE.unitCube, (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
              ≤ ∫ x in Work.Diff.STE.unitCube, ((n : ℝ) ^ 3 + 1) ^ (2 * (m : ℝ))
                  * ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n,
                      (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                        (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖)
                        ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) :=
                MeasureTheory.integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hSN0 c i x) _)
                  (integrableOn_unitCube_of_continuous_real (continuous_const.mul hsumcont))
                  (Filter.Eventually.of_forall hpm2)
            _ = ((n : ℝ) ^ 3 + 1) ^ (2 * (m : ℝ)) * ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n,
                  ∫ x in Work.Diff.STE.unitCube,
                    (‖Work.Diff.STE.pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                      (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) x‖)
                      ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) := by
                rw [MeasureTheory.integral_const_mul]
                congr 1
                rw [MeasureTheory.integral_finsetSum]
                · refine Finset.sum_congr rfl fun q _ => ?_
                  rw [MeasureTheory.integral_finsetSum]
                  · refine Finset.sum_congr rfl fun q' _ => ?_
                    rw [MeasureTheory.integral_finsetSum]
                    exact fun q'' _ => integrableOn_unitCube_of_continuous_real
                      (((Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                        (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ))
                        ((hNcs q q' q'').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm).rpow_const
                        (fun x => Or.inr (le_of_lt (hepos c i))))
                  · intro q' _
                    exact integrableOn_unitCube_of_continuous_real
                      (continuous_finset_sum _ fun q'' _ =>
                        ((Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                          (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ))
                          ((hNcs q q' q'').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm).rpow_const
                          (fun x => Or.inr (le_of_lt (hepos c i))))
                · intro q _
                  exact integrableOn_unitCube_of_continuous_real
                    (continuous_finset_sum _ fun q' _ => continuous_finset_sum _ fun q'' _ =>
                      ((Work.Diff.STE.continuous_pdVec (c.partSize i) (fun j' => β (c.emb i j'))
                        (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ))
                        ((hNcs q q' q'').of_le (WithTop.coe_le_coe.mpr le_top : ((((c.partSize i : ℕ)) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)))).norm).rpow_const
                        (fun x => Or.inr (le_of_lt (hepos c i))))
            _ ≤ ((n : ℝ) ^ 3 + 1) ^ (2 * (m : ℝ)) * ∑ q : Fin n, ∑ q' : Fin n, ∑ q'' : Fin n,
                  CGN' * B' ^ (2 * (m : ℝ))
                    * Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((N z q q' q'' : ℝ) : ℂ)) := by
                refine mul_le_mul_of_nonneg_left
                  (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun q' _ =>
                    Finset.sum_le_sum fun q'' _ => hterm q q' q'') (by positivity)
            _ ≤ ((n : ℝ) ^ 3 + 1) ^ (2 * (m : ℝ))
                  * (CGN' * B' ^ (2 * (m : ℝ)) * Einner) := by
                rw [heqN, hEinnerdef]
                refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
                  (by positivity)
                exact le_add_of_nonneg_left (Finset.sum_nonneg fun p _ =>
                  Finset.sum_nonneg fun q _ => ENormSq_nonnegR m _)
            _ = KN * Einner := by rw [hKNdef]; ring
        have h3pow : (3 : ℝ) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1) ≤ 3 ^ (2 * (m : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (he2m c i)
        have hfinal : 3 ^ (2 * (m : ℝ)) * (1 + KM * Einner + KN * Einner) ≤ Q * (1 + Einner) := by
          rw [hQdef]
          have h1 : 1 + KM * Einner + KN * Einner ≤ (1 + KM + KN) * (1 + Einner) := by
            nlinarith [hKM0, hKN0, hEinner0]
          calc 3 ^ (2 * (m : ℝ)) * (1 + KM * Einner + KN * Einner)
              ≤ 3 ^ (2 * (m : ℝ)) * ((1 + KM + KN) * (1 + Einner)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = 3 ^ (2 * (m : ℝ)) * (1 + (KM + KN)) * (1 + Einner) := by ring
        calc ∫ x in Work.Diff.STE.unitCube, (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
            ≤ ∫ x in Work.Diff.STE.unitCube, 3 ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
                * (1 + (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))
                     + (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) :=
              MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hBB0 c i x) _)
                (integrableOn_unitCube_of_continuous_real hUp)
                (Filter.Eventually.of_forall hpm)
          _ = 3 ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ) - 1)
                * (1 + (∫ x in Work.Diff.STE.unitCube,
                      (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))
                     + (∫ x in Work.Diff.STE.unitCube,
                      (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)))) := hint2
          _ ≤ 3 ^ (2 * (m : ℝ)) * (1 + KM * Einner + KN * Einner) := by
              refine mul_le_mul h3pow ?_ ?_ (by positivity)
              · have h1 : 0 ≤ ∫ x in Work.Diff.STE.unitCube,
                    (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) :=
                  integral_nonneg fun x => Real.rpow_nonneg (hSM0 c i x) _
                have h2 : 0 ≤ ∫ x in Work.Diff.STE.unitCube,
                    (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) :=
                  integral_nonneg fun x => Real.rpow_nonneg (hSN0 c i x) _
                linarith
              · have h1 : 0 ≤ ∫ x in Work.Diff.STE.unitCube,
                    (SM c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) :=
                  integral_nonneg fun x => Real.rpow_nonneg (hSM0 c i x) _
                have h2 : 0 ≤ ∫ x in Work.Diff.STE.unitCube,
                    (SN c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) :=
                  integral_nonneg fun x => Real.rpow_nonneg (hSN0 c i x) _
                linarith
          _ ≤ Q * (1 + Einner) := hfinal
      -- (4) the per-partition integral bound
      have hg : ∀ c : OrderedFinpartition m,
          ∫ x in Work.Diff.STE.unitCube, (D * ∏ i : Fin c.length, BB c i x) ^ 2
            ≤ D ^ 2 * Q * (1 + Einner) := by
        intro c
        have hBBp : ∀ i : Fin c.length, Continuous (fun x : Fin n → ℝ =>
            (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) := fun i =>
          (hBBcont c i).rpow_const (fun x => Or.inr (le_of_lt (hepos c i)))
        have hcont : Continuous (fun x : Fin n → ℝ => D ^ 2 * ∑ i : Fin c.length,
            ((c.partSize i : ℝ) / (m : ℝ))
              * (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ))) :=
          continuous_const.mul (continuous_finset_sum _ fun i _ =>
            continuous_const.mul (hBBp i))
        calc ∫ x in Work.Diff.STE.unitCube, (D * ∏ i : Fin c.length, BB c i x) ^ 2
            = ∫ x in Work.Diff.STE.unitCube, D ^ 2 * ∏ i : Fin c.length, (BB c i x) ^ 2 := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
              simp only [mul_pow, Finset.prod_pow]
          _ ≤ ∫ x in Work.Diff.STE.unitCube, D ^ 2 * ∑ i : Fin c.length,
                ((c.partSize i : ℝ) / (m : ℝ))
                  * (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) :=
              MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun x => by positivity)
                (integrableOn_unitCube_of_continuous_real hcont)
                (Filter.Eventually.of_forall fun x =>
                  mul_le_mul_of_nonneg_left (hagm c x) (sq_nonneg D))
          _ = D ^ 2 * ∑ i : Fin c.length, ((c.partSize i : ℝ) / (m : ℝ))
                * ∫ x in Work.Diff.STE.unitCube,
                    (BB c i x) ^ ((2 * (m : ℝ)) / (c.partSize i : ℝ)) := by
              rw [MeasureTheory.integral_const_mul]
              congr 1
              rw [MeasureTheory.integral_finsetSum]
              · exact Finset.sum_congr rfl fun i _ => by rw [MeasureTheory.integral_const_mul]
              · intro i _
                exact Integrable.const_mul
                  (integrableOn_unitCube_of_continuous_real (hBBp i)) _
          _ ≤ D ^ 2 * ∑ i : Fin c.length, ((c.partSize i : ℝ) / (m : ℝ)) * (Q * (1 + Einner)) := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (sq_nonneg D)
              exact mul_le_mul_of_nonneg_left (hblock c i)
                (div_nonneg (by positivity) (Nat.cast_nonneg m))
          _ = D ^ 2 * Q * (1 + Einner) := by
              rw [← Finset.sum_mul, hwsum c, one_mul]
              ring
      -- (5) the pointwise bound of the Faà di Bruno sum
      have hsumabs : ∀ x : Fin n → ℝ,
          |∑ c : OrderedFinpartition m, fbTerm Φ M N β c x|
            ≤ ∑ c : OrderedFinpartition m, D * ∏ i : Fin c.length, BB c i x := by
        intro x
        calc |∑ c : OrderedFinpartition m, fbTerm Φ M N β c x|
            ≤ ∑ c : OrderedFinpartition m, |fbTerm Φ M N β c x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ c : OrderedFinpartition m, D * ∏ i : Fin c.length, BB c i x :=
              Finset.sum_le_sum fun c _ => hfb c x
      have hgcont : Continuous (fun x : Fin n → ℝ => ∑ c : OrderedFinpartition m,
          D * ∏ i : Fin c.length, BB c i x) :=
        continuous_finset_sum _ fun c _ =>
          continuous_const.mul (continuous_finsetProd Finset.univ fun i _ => hBBcont c i)
      have hsqcont : Continuous (fun x : Fin n → ℝ => (∑ c : OrderedFinpartition m,
          D * ∏ i : Fin c.length, BB c i x) ^ 2) := hgcont.pow 2
      -- (6) the final chain
      calc ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec m β (fun z => ((Φ (z, M z, N z) : ℝ) : ℂ)) x‖ ^ 2
          = ∫ x in Work.Diff.STE.unitCube,
              (∑ c : OrderedFinpartition m, fbTerm Φ M N β c x) ^ 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only [hnorm x, sq_abs]
        _ = ∫ x in Work.Diff.STE.unitCube,
              |∑ c : OrderedFinpartition m, fbTerm Φ M N β c x| ^ 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only [sq_abs]
        _ ≤ ∫ x in Work.Diff.STE.unitCube,
              (∑ c : OrderedFinpartition m, D * ∏ i : Fin c.length, BB c i x) ^ 2 := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun x => by positivity)
              (integrableOn_unitCube_of_continuous_real hsqcont)
              (Filter.Eventually.of_forall fun x => ?_)
            exact pow_le_pow_left₀ (abs_nonneg _) (hsumabs x) 2
        _ ≤ ∫ x in Work.Diff.STE.unitCube, Np * ∑ c : OrderedFinpartition m,
              (D * ∏ i : Fin c.length, BB c i x) ^ 2 := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun x => by positivity)
              (integrableOn_unitCube_of_continuous_real
                (continuous_const.mul (continuous_finset_sum _ fun c _ =>
                  (continuous_const.mul (continuous_finsetProd Finset.univ fun i _ =>
                    hBBcont c i)).pow 2)))
              (Filter.Eventually.of_forall fun x => ?_)
            have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (OrderedFinpartition m)))
              (f := fun c => D * ∏ i : Fin c.length, BB c i x)
            simpa [hNpdef, Finset.card_univ] using h
        _ = Np * ∑ c : OrderedFinpartition m, ∫ x in Work.Diff.STE.unitCube,
              (D * ∏ i : Fin c.length, BB c i x) ^ 2 := by
            rw [MeasureTheory.integral_const_mul]
            congr 1
            rw [MeasureTheory.integral_finsetSum]
            exact fun c _ => integrableOn_unitCube_of_continuous_real
              ((continuous_const.mul (continuous_finsetProd Finset.univ fun i _ =>
                hBBcont c i)).pow 2)
        _ ≤ Np * ∑ _c : OrderedFinpartition m, (D ^ 2 * Q * (1 + Einner)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hg c) hNp0
        _ = Np * (Np * (D ^ 2 * Q * (1 + Einner))) := by
            rw [Finset.sum_const, Finset.card_univ, hNpdef, nsmul_eq_mul]
        _ ≤ Cst * (1 + Einner) := by
            rw [hCstdef]
            have h1 : D ^ 2 * Q ≤ (D ^ 2 + 1) * ((m : ℝ) + 1) * (Q + 1) := by
              have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
              have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
                have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
                linarith
              have hQ1 : (1 : ℝ) ≤ Q + 1 := by linarith
              have h21 : 0 ≤ D ^ 2 + 1 := by linarith
              have hQp : 0 ≤ Q + 1 := by linarith
              have hkey : D ^ 2 * Q ≤ (D ^ 2 + 1) * (Q + 1) := by nlinarith
              have hkey2 : (D ^ 2 + 1) * (Q + 1) ≤ (D ^ 2 + 1) * (Q + 1) * ((m : ℝ) + 1) :=
                le_mul_of_one_le_right (by positivity) hm1
              linarith
            calc Np * (Np * (D ^ 2 * Q * (1 + Einner)))
                = Np ^ 2 * (1 + Einner) * (D ^ 2 * Q) := by ring
              _ ≤ Np ^ 2 * (1 + Einner) * ((D ^ 2 + 1) * ((m : ℝ) + 1) * (Q + 1)) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = Np ^ 2 * (D ^ 2 + 1) * ((m : ℝ) + 1) * (Q + 1) * (1 + Einner) := by ring
        _ = Cst * (1 + (∑ p : Fin n, ∑ q : Fin n,
                Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((M z p q : ℝ) : ℂ)))
              + ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n,
                Work.Diff.STE.ENormSq m (fun z : Fin n → ℝ => ((N z p q r : ℝ) : ℂ))) := by
            rw [hEinnerdef]
            ring

end Work.Diff.STE.Lead.GalTame.ResidGn
