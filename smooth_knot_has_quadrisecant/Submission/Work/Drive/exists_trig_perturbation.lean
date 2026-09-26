import Mathlib
import Submission.Work.Drive.curvatureAPI
import Submission.Work.Drive.trigPerturbDefs

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# The trigonometric perturbation lemma

`Work.Drive.exists_trig_perturbation`: given a finite set `S` of parameters in `[0, period)` and
*arbitrary* prescribed vectors `B : ℝ → Space`, there is an analytic `period`-periodic curve `φ`
whose velocity vanishes at every `i ∈ S` and whose acceleration at `i ∈ S` is a nonzero multiple
of `B i`.

The construction is `φ = pertCurve S B = pertWeight S • pertField S B` from
`Submission.Work.Drive.trigPerturbDefs`:

* `pertWeight S t = ∏_{j ∈ S} (1 - cos (t - j))` has, at every `i ∈ S`, value `0`, first
  derivative `0` and second derivative `∏_{l ∈ S.erase i} (1 - cos (i - l)) ≠ 0`;
* `pertField S B = Σ_{j ∈ S} η_j • B j` interpolates `B` on `S`.

Hence `deriv φ i = 0` and `deriv (deriv φ) i = (∏_{l ∈ S.erase i} (1 - cos (i - l))) • B i`.
-/

/-! ## Auxiliary calculus lemmas -/

/-- A finite product of scalar functions is `C^n` if all factors are. -/
lemma contDiff_finset_prod {ι : Type*} (f : ι → ℝ → ℝ) (n : WithTop ℕ∞) :
    ∀ s : Finset ι, (∀ i ∈ s, ContDiff ℝ n (f i)) →
      ContDiff ℝ n (fun t : ℝ => ∏ i ∈ s, f i t) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using (contDiff_const : ContDiff ℝ n (fun _ : ℝ => (1 : ℝ)))
  | insert a s ha ih =>
      intro h
      have h1 : ContDiff ℝ n (fun t : ℝ => f a t * ∏ i ∈ s, f i t) :=
        (h a (Finset.mem_insert_self a s)).mul
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.prod_insert ha] using h1

/-- A finite product of scalar functions is periodic if all factors are. -/
lemma periodic_finset_prod {ι : Type*} (f : ι → ℝ → ℝ) (c : ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, Function.Periodic (f i) c) →
      Function.Periodic (fun t : ℝ => ∏ i ∈ s, f i t) c := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ x; simp
  | insert a s ha ih =>
      intro h
      have h1 : Function.Periodic (fun t : ℝ => f a t * ∏ i ∈ s, f i t) c :=
        (h a (Finset.mem_insert_self a s)).mul
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      intro x
      simpa only [Finset.prod_insert ha] using h1 x

/-- A finite sum of vector-valued functions is periodic if all summands are. -/
lemma periodic_finset_sum {ι : Type*} (f : ι → ℝ → Space) (c : ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, Function.Periodic (f i) c) →
      Function.Periodic (fun t : ℝ => ∑ i ∈ s, f i t) c := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ x; simp
  | insert a s ha ih =>
      intro h
      have h1 : Function.Periodic (fun t : ℝ => f a t + ∑ i ∈ s, f i t) c :=
        (h a (Finset.mem_insert_self a s)).add
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      intro x
      simpa only [Finset.sum_insert ha] using h1 x

/-- Second derivative of a product of two scalar functions. -/
lemma deriv_deriv_mul (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    deriv (deriv (f * g)) x
      = deriv (deriv f) x * g x + 2 * deriv f x * deriv g x + f x * deriv (deriv g) x := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have hddf : Differentiable ℝ (deriv f) := (hf.deriv' (n := 1)).differentiable (by simp)
  have hddg : Differentiable ℝ (deriv g) := (hg.deriv' (n := 1)).differentiable (by simp)
  have h1 : deriv (f * g) = fun y => deriv f y * g y + f y * deriv g y := by
    funext y
    exact deriv_mul (hdf y) (hdg y)
  have key : deriv (fun y => deriv f y * g y + f y * deriv g y) x
      = deriv (fun y => deriv f y * g y) x + deriv (fun y => f y * deriv g y) x :=
    deriv_add ((hddf x).mul (hdg x)) ((hdf x).mul (hddg x))
  have hA : deriv (fun y => deriv f y * g y) x
      = deriv (deriv f) x * g x + deriv f x * deriv g x :=
    deriv_mul (hddf x) (hdg x)
  have hB : deriv (fun y => f y * deriv g y) x
      = deriv f x * deriv g x + f x * deriv (deriv g) x :=
    deriv_mul (hdf x) (hddg x)
  rw [h1, key, hA, hB]
  ring

/-- First and second derivative of a scalar multiple of a vector-valued function. -/
lemma deriv_deriv_smul_fun {q : ℝ → ℝ} {r : ℝ → Space} (hq : ContDiff ℝ 2 q)
    (hr : ContDiff ℝ 2 r) (t : ℝ) :
    deriv (fun s => q s • r s) t = q t • deriv r t + deriv q t • r t ∧
      deriv (deriv (fun s => q s • r s)) t
        = q t • deriv (deriv r) t + (deriv q t • deriv r t + deriv q t • deriv r t)
          + deriv (deriv q) t • r t := by
  have hdq : Differentiable ℝ q := hq.differentiable (by simp)
  have hdr : Differentiable ℝ r := hr.differentiable (by simp)
  have hddq : Differentiable ℝ (deriv q) := (hq.deriv' (n := 1)).differentiable (by simp)
  have hddr : Differentiable ℝ (deriv r) := (hr.deriv' (n := 1)).differentiable (by simp)
  have hderiv : deriv (fun s => q s • r s) = fun s => q s • deriv r s + deriv q s • r s := by
    funext s
    exact deriv_smul (hdq s) (hdr s)
  refine ⟨congrFun hderiv t, ?_⟩
  have key : deriv (fun s => q s • deriv r s + deriv q s • r s) t
      = deriv (fun s => q s • deriv r s) t + deriv (fun s => deriv q s • r s) t :=
    deriv_add ((hdq t).smul (hddr t)) ((hddq t).smul (hdr t))
  have hA : deriv (fun s => q s • deriv r s) t = q t • deriv (deriv r) t + deriv q t • deriv r t :=
    deriv_smul (hdq t) (hddr t)
  have hB : deriv (fun s => deriv q s • r s) t = deriv q t • deriv r t + deriv (deriv q) t • r t :=
    deriv_smul (hddq t) (hdr t)
  rw [hderiv, key, hA, hB]
  abel

/-! ## Facts about the scalar weight -/

/-- For distinct points `a, b` of `S ⊆ [0, period)` the difference `a - b` is not a multiple of
`2π`, so `cos (a - b) ≠ 1`. -/
lemma cos_ne_one_of_mem (S : Finset ℝ) (hS : ∀ i ∈ S, i ∈ Set.Ico 0 period)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) : Real.cos (a - b) ≠ 1 := by
  intro h
  have ha' := hS a ha
  have hb' := hS b hb
  rw [show period = 2 * Real.pi by simp [LeanEval.KnotTheory.Quadrisecant.period]] at ha' hb'
  have h1 : -(2 * Real.pi) < a - b := by linarith [ha'.1, hb'.2]
  have h2 : a - b < 2 * Real.pi := by linarith [ha'.2, hb'.1]
  exact hne (sub_eq_zero.mp ((Real.cos_eq_one_iff_of_lt_of_lt h1 h2).1 h))

/-- The scalar weight is analytic. -/
lemma pertWeight_contDiff (S : Finset ℝ) : ContDiff ℝ ⊤ (pertWeight S) := by
  unfold pertWeight
  exact contDiff_finset_prod (fun j : ℝ => fun t : ℝ => 1 - Real.cos (t - j)) ⊤ S
    (fun j _ => by fun_prop)

/-- The scalar weight is `period`-periodic. -/
lemma pertWeight_periodic (S : Finset ℝ) : Function.Periodic (pertWeight S) period := by
  unfold pertWeight
  refine periodic_finset_prod (fun j : ℝ => fun t : ℝ => 1 - Real.cos (t - j)) period S ?_
  intro j _
  have h1 : Function.Periodic (fun _ : ℝ => (1 : ℝ)) period := fun _ => rfl
  have hcos : Function.Periodic (fun t : ℝ => Real.cos (t - j)) period := by
    rw [show period = 2 * Real.pi by simp [LeanEval.KnotTheory.Quadrisecant.period]]
    exact Real.cos_periodic.sub_const j
  exact h1.sub hcos

/-- The scalar weight vanishes at every point of `S`. -/
lemma pertWeight_apply_zero (S : Finset ℝ) {i : ℝ} (hi : i ∈ S) : pertWeight S i = 0 := by
  unfold pertWeight
  exact Finset.prod_eq_zero hi (by simp)

/-- Splitting off the factor of the scalar weight indexed by `i ∈ S`. -/
lemma pertWeight_eq_mul_cofactor (S : Finset ℝ) {i : ℝ} (hi : i ∈ S) :
    pertWeight S = (fun t : ℝ => 1 - Real.cos (t - i)) *
      (fun t : ℝ => ∏ l ∈ S.erase i, (1 - Real.cos (t - l))) := by
  funext t
  simp only [pertWeight, Pi.mul_apply]
  rw [← Finset.prod_erase_mul S (fun j : ℝ => (1 - Real.cos (t - j))) hi]
  ring

/-- The derivative of the scalar weight vanishes at every point of `S`. -/
lemma deriv_pertWeight_apply_zero (S : Finset ℝ) {i : ℝ} (hi : i ∈ S) :
    deriv (pertWeight S) i = 0 := by
  have hf : ContDiff ℝ 1 (fun t : ℝ => 1 - Real.cos (t - i)) := by fun_prop
  have hG : ContDiff ℝ 1 (fun t : ℝ => ∏ l ∈ S.erase i, (1 - Real.cos (t - l))) :=
    contDiff_finset_prod _ 1 _ fun l _ => by fun_prop
  rw [pertWeight_eq_mul_cofactor S hi,
    deriv_mul (hf.differentiable (by simp) i) (hG.differentiable (by simp) i)]
  rw [show deriv (fun t : ℝ => 1 - Real.cos (t - i)) i = 0 by simp]
  simp

/-- The second derivative of the scalar weight at `i ∈ S`. -/
lemma deriv_deriv_pertWeight_apply (S : Finset ℝ) {i : ℝ} (hi : i ∈ S) :
    deriv (deriv (pertWeight S)) i = ∏ l ∈ S.erase i, (1 - Real.cos (i - l)) := by
  have hf : ContDiff ℝ 2 (fun t : ℝ => 1 - Real.cos (t - i)) := by fun_prop
  have hG : ContDiff ℝ 2 (fun t : ℝ => ∏ l ∈ S.erase i, (1 - Real.cos (t - l))) :=
    contDiff_finset_prod _ 2 _ fun l _ => by fun_prop
  rw [pertWeight_eq_mul_cofactor S hi, deriv_deriv_mul _ _ hf hG i]
  rw [show deriv (deriv (fun t : ℝ => 1 - Real.cos (t - i))) i = 1 by simp]
  simp

/-- The second derivative of the scalar weight at a point of `S` is nonzero. -/
lemma prod_erase_one_sub_cos_ne_zero (S : Finset ℝ)
    (hS : ∀ i ∈ S, i ∈ Set.Ico 0 period) {i : ℝ} (hi : i ∈ S) :
    (∏ l ∈ S.erase i, (1 - Real.cos (i - l))) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro l hl
  have hlS : l ∈ S := (Finset.mem_erase.mp hl).2
  have hli : l ≠ i := (Finset.mem_erase.mp hl).1
  have hcos : Real.cos (i - l) ≠ 1 := cos_ne_one_of_mem S hS hi hlS (Ne.symm hli)
  intro h
  exact hcos (by linarith)

/-! ## Facts about the interpolating field -/

/-- The interpolation weight `pertEta S j` takes the value `1` at `j` and `0` at the other points
of `S`. -/
lemma pertEta_apply (S : Finset ℝ) (hS : ∀ i ∈ S, i ∈ Set.Ico 0 period)
    {i j : ℝ} (hi : i ∈ S) (hj : j ∈ S) : pertEta S j i = if i = j then 1 else 0 := by
  rcases eq_or_ne i j with hij | hij
  · rw [hij, if_pos rfl]
    unfold pertEta
    refine Finset.prod_eq_one fun l hl => ?_
    have hlS : l ∈ S := (Finset.mem_erase.mp hl).2
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hden : 1 - Real.cos (l - j) ≠ 0 := by
      have hc := cos_ne_one_of_mem S hS hlS hj hlj
      intro h
      exact hc (by linarith)
    simp only [sub_self, Real.cos_zero]
    exact div_self hden
  · rw [if_neg hij]
    unfold pertEta
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, hi⟩) ?_
    simp

/-- The interpolation weight `pertEta S j` is analytic. -/
lemma pertEta_contDiff (S : Finset ℝ) (j : ℝ) : ContDiff ℝ ⊤ (pertEta S j) := by
  unfold pertEta
  refine contDiff_finset_prod (fun l : ℝ => fun t : ℝ =>
    (Real.cos (t - j) - Real.cos (l - j)) / (1 - Real.cos (l - j))) ⊤ (S.erase j) ?_
  intro l _
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => Real.cos (t - j) - Real.cos (l - j)) := by fun_prop
  have h := hc.mul (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (1 - Real.cos (l - j))⁻¹))
  simpa [div_eq_mul_inv] using h

/-- The interpolation weight `pertEta S j` is `period`-periodic. -/
lemma pertEta_periodic (S : Finset ℝ) (j : ℝ) : Function.Periodic (pertEta S j) period := by
  unfold pertEta
  refine periodic_finset_prod (fun l : ℝ => fun t : ℝ =>
    (Real.cos (t - j) - Real.cos (l - j)) / (1 - Real.cos (l - j))) period (S.erase j) ?_
  intro l _
  have hcos : Function.Periodic (fun t : ℝ => Real.cos (t - j)) period := by
    rw [show period = 2 * Real.pi by simp [LeanEval.KnotTheory.Quadrisecant.period]]
    exact Real.cos_periodic.sub_const j
  have h1 : Function.Periodic (fun t : ℝ => Real.cos (t - j) - Real.cos (l - j)) period :=
    hcos.sub (fun _ => rfl)
  have h2 : Function.Periodic
      (fun t : ℝ => (Real.cos (t - j) - Real.cos (l - j)) * (1 - Real.cos (l - j))⁻¹)
      period := h1.mul (fun _ => rfl)
  simpa [div_eq_mul_inv] using h2

/-- The interpolating field is analytic. -/
lemma pertField_contDiff (S : Finset ℝ) (_hS : ∀ i ∈ S, i ∈ Set.Ico 0 period)
    (B : ℝ → Space) : ContDiff ℝ ⊤ (pertField S B) := by
  unfold pertField
  exact ContDiff.sum fun j hj => (pertEta_contDiff S j).smul_const (B j)

/-- The interpolating field is `period`-periodic. -/
lemma pertField_periodic (S : Finset ℝ) (B : ℝ → Space) :
    Function.Periodic (pertField S B) period := by
  unfold pertField
  refine periodic_finset_sum (fun j : ℝ => fun t : ℝ => pertEta S j t • B j) period S ?_
  intro j _ x
  show pertEta S j (x + period) • B j = pertEta S j x • B j
  rw [pertEta_periodic S j x]

/-- The interpolating field takes the prescribed value `B i` at every `i ∈ S`. -/
lemma pertField_apply (S : Finset ℝ) (hS : ∀ i ∈ S, i ∈ Set.Ico 0 period)
    (B : ℝ → Space) {i : ℝ} (hi : i ∈ S) : pertField S B i = B i := by
  unfold pertField
  refine Eq.trans (Finset.sum_eq_single i ?_ ?_) ?_
  · intro j hj hji
    rw [pertEta_apply S hS hi hj, if_neg (Ne.symm hji), zero_smul]
  · intro hi'
    exact absurd hi hi'
  · rw [pertEta_apply S hS hi hi, if_pos rfl, one_smul]

/-! ## The trigonometric perturbation -/

theorem exists_trig_perturbation (S : Finset ℝ)
    (hS : ∀ i ∈ S, i ∈ Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period)
    (B : ℝ → LeanEval.KnotTheory.Quadrisecant.Space) :
    ∃ φ : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      ContDiff ℝ ⊤ φ ∧ Function.Periodic φ LeanEval.KnotTheory.Quadrisecant.period ∧
      (∀ i ∈ S, deriv φ i = 0) ∧
      (∀ i ∈ S, ∃ c : ℝ, c ≠ 0 ∧ deriv (deriv φ) i = c • B i) := by
  refine ⟨pertCurve S B, ?_, ?_, ?_, ?_⟩
  · exact (pertWeight_contDiff S).smul (pertField_contDiff S hS B)
  · intro t
    show pertWeight S (t + period) • pertField S B (t + period)
      = pertWeight S t • pertField S B t
    rw [pertWeight_periodic S t, pertField_periodic S B t]
  · intro i hi
    have hq : ContDiff ℝ 2 (pertWeight S) := (pertWeight_contDiff S).of_le le_top
    have hr : ContDiff ℝ 2 (pertField S B) := (pertField_contDiff S hS B).of_le le_top
    obtain ⟨h1, -⟩ := deriv_deriv_smul_fun hq hr i
    show deriv (fun s : ℝ => pertWeight S s • pertField S B s) i = 0
    rw [h1, pertWeight_apply_zero S hi, deriv_pertWeight_apply_zero S hi]
    simp
  · intro i hi
    have hq : ContDiff ℝ 2 (pertWeight S) := (pertWeight_contDiff S).of_le le_top
    have hr : ContDiff ℝ 2 (pertField S B) := (pertField_contDiff S hS B).of_le le_top
    obtain ⟨-, h2⟩ := deriv_deriv_smul_fun hq hr i
    refine ⟨∏ l ∈ S.erase i, (1 - Real.cos (i - l)),
      prod_erase_one_sub_cos_ne_zero S hS hi, ?_⟩
    show deriv (deriv (fun s : ℝ => pertWeight S s • pertField S B s)) i
      = (∏ l ∈ S.erase i, (1 - Real.cos (i - l))) • B i
    rw [h2, pertWeight_apply_zero S hi, deriv_pertWeight_apply_zero S hi,
      deriv_deriv_pertWeight_apply S hi, pertField_apply S hS B hi]
    simp

end Work.Drive
