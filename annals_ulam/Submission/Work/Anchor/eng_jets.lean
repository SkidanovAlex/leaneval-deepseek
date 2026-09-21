import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.Rnu_spec
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.KernelExt.JM_diag
import Submission.Work.Anchor.eng_reg

/-!
# The Bell recursion of the odd Abel kernel: jets in the first slot

`Rnu ν h init m` is the manifest (Bell-polynomial) numerator of the odd Abel kernel; it satisfies
the recursion `R_{m+1} = Zrad h · ∂_a R_m + (ν - m) · ∂_a (Zrad h) · R_m` (`Rnu_succ_apply`).
This file collects, in the local region `Reg` of the anchor,

* `ZJ h j a σ t`, the `j`-th `a`-derivative of the radicand `Zrad h (·,σ,t)` at `a`;
* `Rjet ν h init m j a σ t`, the `j`-th `a`-derivative of `Rnu ν h init m (·,σ,t)` at `a`;
* the Leibniz recursion `Rjet_succ` for the jets of the Bell numerator;
* the bound constants `Abound`/`Db` and their nonnegativity;
* `Rnu_jet_bounds`, the induction that bounds the jets (and their difference against the
  unperturbed `h = 0`) in terms of bounds on the jets of the radicand and of the init.

The content is the one of `Work.OddVolterra.Window.thetaM_close`, with the region `Reg`
(`σ ∈ [7/10,1]`) replaced by the anchor region `Reg` (`σ ∈ [1/2,19/20]`); its proofs only ever
use the region through the hypotheses.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 4000000

namespace Work.Anchor

open Work.OddVolterra

/-! ## The jets and their recursion -/


/-- The `i`-th `a`-derivative of the radicand `Zrad h (·,σ,t)` at `a`. -/
noncomputable def ZJ (h : ℝ → ℝ) (i : ℕ) (a σ t : ℝ) : ℝ :=
  iteratedDeriv i (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) a

/-- The `j`-th `a`-derivative of the `m`-th Bell numerator `Rnu ν h init m (·,σ,t)` at `a`. -/
noncomputable def Rjet (ν : ℝ) (h : ℝ → ℝ) (init : ℝ × ℝ × ℝ → ℝ) (m j : ℕ) (a σ t : ℝ) : ℝ :=
  iteratedDeriv j (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t)) a

lemma iteratedDeriv_deriv_eq (f : ℝ → ℝ) (i : ℕ) (a : ℝ) :
    iteratedDeriv i (deriv f) a = iteratedDeriv (i + 1) f a := by
  induction i generalizing a with
  | zero => rw [iteratedDeriv_zero, iteratedDeriv_one]
  | succ i ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    rw [show iteratedDeriv i (deriv f) = iteratedDeriv (i + 1) f from funext fun x => ih x]

/-- The derivative of the section `a ↦ F (a,σ,t)` is the application of `fderiv F` to `(1,0,0)`. -/
lemma deriv_section_eq_fderiv {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (ν : ℝ) (m : ℕ) (σ t : ℝ) :
    deriv (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t)) =
      fun a' : ℝ => (fderiv ℝ (KernelExt.Rnu ν h init m) (a', σ, t)) (1, 0, 0) := by
  funext a'
  exact (KernelExt.hasDerivAt_section (a', σ, t)
    (((KernelExt.Rnu_contDiff_aux ν hh hinit m).contDiffAt).differentiableAt (by simp))).deriv

lemma deriv_section_eq_fderiv_Zrad {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    deriv (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) =
      fun a' : ℝ => (fderiv ℝ (KernelExt.Zrad h) (a', σ, t)) (1, 0, 0) := by
  funext a'
  exact (KernelExt.hasDerivAt_section (a', σ, t)
    (((KernelExt.Zrad_contDiff_aux hh).contDiffAt).differentiableAt (by simp))).deriv

lemma contDiff_Zrad_section {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) :=
  (KernelExt.Zrad_contDiff_aux hh).comp (by fun_prop)

lemma contDiff_Rnu_section (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t)) :=
  (KernelExt.Rnu_contDiff_aux ν hh hinit m).comp (by fun_prop)

/-- The `a`-derivative of the `m`-th Bell numerator section is smooth. -/
lemma contDiff_deriv_Rnu_section (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t))) := by
  simpa only [Function.iterate_one] using
    (contDiff_Rnu_section ν hh hinit m σ t).iterate_deriv 1

/-- The `a`-derivative of the radicand section is smooth. -/
lemma contDiff_deriv_Zrad_section {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv (fun a' : ℝ => KernelExt.Zrad h (a', σ, t))) := by
  simpa only [Function.iterate_one] using (contDiff_Zrad_section hh σ t).iterate_deriv 1

/-- The recursion in function form: for fixed `(σ,t)` the `(m+1)`-st Bell numerator is
`Z·(R_m)' + (ν-m)·(∂_a Z)·R_m` as a function of its first variable. -/
lemma Rnu_succ_apply (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) (a σ t : ℝ) :
    KernelExt.Rnu ν h init (m + 1) (a, σ, t) =
      KernelExt.Zrad h (a, σ, t) * deriv (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t)) a
      + (ν - (m : ℝ)) * deriv (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) a *
        KernelExt.Rnu ν h init m (a, σ, t) := by
  have hF : DifferentiableAt ℝ (KernelExt.Rnu ν h init m) (a, σ, t) :=
    ((KernelExt.Rnu_contDiff_aux ν hh hinit m).contDiffAt).differentiableAt (by simp)
  have hZ : DifferentiableAt ℝ (KernelExt.Zrad h) (a, σ, t) :=
    ((KernelExt.Zrad_contDiff_aux hh).contDiffAt).differentiableAt (by simp)
  rw [KernelExt.Rnu]
  beta_reduce
  rw [← (KernelExt.hasDerivAt_section (a, σ, t) hF).deriv,
    ← (KernelExt.hasDerivAt_section (a, σ, t) hZ).deriv]

/-- **The recursion at the level of the jet of `Rnu`.** -/
lemma Rjet_succ (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m j : ℕ) (a σ t : ℝ) :
    Rjet ν h init (m + 1) j a σ t =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (ZJ h i a σ t * Rjet ν h init m (j - i + 1) a σ t
         + (ν - (m : ℝ)) * (ZJ h (i + 1) a σ t * Rjet ν h init m (j - i) a σ t)) := by
  have hZh : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) :=
    contDiff_Zrad_section hh σ t
  have hRh : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t)) :=
    contDiff_Rnu_section ν hh hinit m σ t
  have hdRh : ContDiff ℝ (⊤ : ℕ∞)
      (deriv (fun a'' : ℝ => KernelExt.Rnu ν h init m (a'', σ, t))) :=
    contDiff_deriv_Rnu_section ν hh hinit m σ t
  have hdZh : ContDiff ℝ (⊤ : ℕ∞)
      (deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t))) :=
    contDiff_deriv_Zrad_section hh σ t
  have hid : (fun a' : ℝ => KernelExt.Rnu ν h init (m + 1) (a', σ, t)) =
      fun a' : ℝ => KernelExt.Zrad h (a', σ, t) *
          deriv (fun a'' : ℝ => KernelExt.Rnu ν h init m (a'', σ, t)) a'
        + ((ν - (m : ℝ)) * deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t)) a') *
          KernelExt.Rnu ν h init m (a', σ, t) := by
    funext a'; exact Rnu_succ_apply ν hh hinit m a' σ t
  rw [Rjet, hid]
  have hZj : ContDiffAt ℝ (j : ℕ) (fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) a :=
    hZh.contDiffAt.of_le (by exact_mod_cast le_top)
  have hdRj : ContDiffAt ℝ (j : ℕ)
      (deriv (fun a'' : ℝ => KernelExt.Rnu ν h init m (a'', σ, t))) a :=
    hdRh.contDiffAt.of_le (by exact_mod_cast le_top)
  have hRj : ContDiffAt ℝ (j : ℕ) (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t)) a :=
    hRh.contDiffAt.of_le (by exact_mod_cast le_top)
  have hdZj : ContDiffAt ℝ (j : ℕ)
      (deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t))) a :=
    hdZh.contDiffAt.of_le (by exact_mod_cast le_top)
  have hcd1 : ContDiffAt ℝ (j : ℕ)
      (fun a' : ℝ => KernelExt.Zrad h (a', σ, t) *
        deriv (fun a'' : ℝ => KernelExt.Rnu ν h init m (a'', σ, t)) a') a := hZj.mul hdRj
  have hcd2 : ContDiffAt ℝ (j : ℕ)
      (fun a' : ℝ => ((ν - (m : ℝ)) * deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t)) a') *
        KernelExt.Rnu ν h init m (a', σ, t)) a :=
    (contDiffAt_const.mul hdZj).mul hRj
  change iteratedDeriv j (((fun a' : ℝ => KernelExt.Zrad h (a', σ, t) *
        deriv (fun a'' : ℝ => KernelExt.Rnu ν h init m (a'', σ, t)) a'))
      + (fun a' : ℝ => ((ν - (m : ℝ)) * deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t)) a') *
          KernelExt.Rnu ν h init m (a', σ, t))) a = _
  rw [iteratedDeriv_add hcd1 hcd2]
  have h1 : iteratedDeriv j (fun a' : ℝ => KernelExt.Zrad h (a', σ, t) *
        deriv (fun a'' : ℝ => KernelExt.Rnu ν h init m (a'', σ, t)) a') a
      = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ZJ h i a σ t *
          Rjet ν h init m (j - i + 1) a σ t := by
    change iteratedDeriv j ((fun a' : ℝ => KernelExt.Zrad h (a', σ, t)) *
      deriv (fun a'' : ℝ => KernelExt.Rnu ν h init m (a'', σ, t))) a = _
    rw [iteratedDeriv_mul hZj hdRj]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [iteratedDeriv_deriv_eq]
    rfl
  have h2 : iteratedDeriv j (fun a' : ℝ =>
        ((ν - (m : ℝ)) * deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t)) a') *
        KernelExt.Rnu ν h init m (a', σ, t)) a
      = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ((ν - (m : ℝ)) * (ZJ h (i + 1) a σ t * Rjet ν h init m (j - i) a σ t)) := by
    change iteratedDeriv j ((fun a' : ℝ =>
        (ν - (m : ℝ)) * deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t)) a') *
      (fun a' : ℝ => KernelExt.Rnu ν h init m (a', σ, t))) a = _
    rw [iteratedDeriv_mul (contDiffAt_const.mul hdZj) hRj]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hdZi : ContDiffAt ℝ (i : ℕ)
        (deriv (fun a'' : ℝ => KernelExt.Zrad h (a'', σ, t))) a :=
      hdZh.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_const_mul (c := ν - (m : ℝ)) hdZi]
    rw [iteratedDeriv_deriv_eq]
    simp only [ZJ, Rjet]
    ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  ring

/-! ## The uniform bounds for the Bell recursion -/

/-- The constant bounding the jets of the Bell recursion. -/
noncomputable def Abound (ν B I : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => I
  | m + 1, j =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (B * Abound ν B I m (j - i + 1) + |ν - (m : ℝ)| * B * Abound ν B I m (j - i))

/-- The constant bounding the difference of the jets of the Bell recursion (at `h` and at `0`). -/
noncomputable def Db (ν B I Id δ : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => Id * δ
  | m + 1, j =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (B * δ * Abound ν B I m (j - i + 1) + B * Db ν B I Id δ m (j - i + 1)
         + |ν - (m : ℝ)| * (B * δ * Abound ν B I m (j - i)
            + B * Db ν B I Id δ m (j - i)))

lemma Abound_nonneg (ν B I : ℝ) (hB : 0 ≤ B) (hI : 0 ≤ I) :
    ∀ m j, 0 ≤ Abound ν B I m j := by
  intro m
  induction m with
  | zero => intro j; simp only [Abound]; exact hI
  | succ m ih =>
    intro j
    rw [Abound]
    refine Finset.sum_nonneg fun i hi => ?_
    have h1 := ih (j - i + 1)
    have h2 := ih (j - i)
    have h3 : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ |ν - (m : ℝ)| := abs_nonneg _
    have e1 : 0 ≤ B * Abound ν B I m (j - i + 1) := mul_nonneg hB h1
    have e2 : 0 ≤ |ν - (m : ℝ)| * B * Abound ν B I m (j - i) :=
      mul_nonneg (mul_nonneg h4 hB) h2
    exact mul_nonneg h3 (add_nonneg e1 e2)

lemma Db_nonneg (ν B I Id δ : ℝ) (hB : 0 ≤ B) (hI : 0 ≤ I) (hId : 0 ≤ Id)
    (hδ : 0 ≤ δ) : ∀ m j, 0 ≤ Db ν B I Id δ m j := by
  intro m
  induction m with
  | zero => intro j; simp only [Db]; exact mul_nonneg hId hδ
  | succ m ih =>
    intro j
    rw [Db]
    refine Finset.sum_nonneg fun i hi => ?_
    have h1 := Abound_nonneg ν B I hB hI m (j - i + 1)
    have h2 := Abound_nonneg ν B I hB hI m (j - i)
    have h3 := ih (j - i + 1)
    have h4 := ih (j - i)
    have h5 : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    have h6 : (0 : ℝ) ≤ |ν - (m : ℝ)| := abs_nonneg _
    have e1 : 0 ≤ B * δ * Abound ν B I m (j - i + 1) := mul_nonneg (mul_nonneg hB hδ) h1
    have e2 : 0 ≤ B * Db ν B I Id δ m (j - i + 1) := mul_nonneg hB h3
    have e3 : 0 ≤ B * δ * Abound ν B I m (j - i) := mul_nonneg (mul_nonneg hB hδ) h2
    have e4 : 0 ≤ B * Db ν B I Id δ m (j - i) := mul_nonneg hB h4
    exact mul_nonneg h5 (add_nonneg (add_nonneg e1 e2) (mul_nonneg h6 (add_nonneg e3 e4)))

/-- **The uniform jet bounds for the Bell recursion.** -/
theorem Rnu_jet_bounds (ν : ℝ) (N : ℕ) (B I Id δ : ℝ)
    (init initd : ℝ × ℝ × ℝ → ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (hinitd : ContDiff ℝ (⊤ : ℕ∞) initd)
    (hB : 0 ≤ B) (hI : 0 ≤ I) (hId : 0 ≤ Id) (hδ : 0 < δ)
    (hz : ∀ j, j ≤ N → ∀ a σ t, Reg a σ t →
        |ZJ h j a σ t| ≤ B ∧ |ZJ 0 j a σ t| ≤ B ∧ |ZJ h j a σ t - ZJ 0 j a σ t| ≤ B * δ)
    (hi : ∀ j, j ≤ N → ∀ a σ t, Reg a σ t →
        |iteratedDeriv j (fun a' : ℝ => init (a', σ, t)) a| ≤ I ∧
        |iteratedDeriv j (fun a' : ℝ => initd (a', σ, t)) a| ≤ I ∧
        |iteratedDeriv j (fun a' : ℝ => init (a', σ, t)) a -
         iteratedDeriv j (fun a' : ℝ => initd (a', σ, t)) a| ≤ Id * δ) :
    ∀ m j, j + m ≤ N → ∀ a σ t, Reg a σ t →
        |Rjet ν h init m j a σ t| ≤ Abound ν B I m j ∧
        |Rjet ν 0 initd m j a σ t| ≤ Abound ν B I m j ∧
        |Rjet ν h init m j a σ t - Rjet ν 0 initd m j a σ t| ≤ Db ν B I Id δ m j := by
  intro m
  induction m with
  | zero =>
    intro j hj a σ t hreg
    have hjN : j ≤ N := by omega
    have h0 : Rjet ν h init 0 j a σ t = iteratedDeriv j (fun a' : ℝ => init (a', σ, t)) a := rfl
    have h0' : Rjet ν 0 initd 0 j a σ t = iteratedDeriv j (fun a' : ℝ => initd (a', σ, t)) a := rfl
    have hAb : Abound ν B I 0 j = I := rfl
    have hDb : Db ν B I Id δ 0 j = Id * δ := rfl
    obtain ⟨h1, h2, h3⟩ := hi j hjN a σ t hreg
    rw [h0, h0', hAb, hDb]
    exact ⟨h1, h2, h3⟩
  | succ m ih =>
    intro j hj a σ t hreg
    have hexp := Rjet_succ ν hh hinit m j a σ t
    have hexp0 := Rjet_succ ν (h := 0) contDiff_const hinitd m j a σ t
    have hAb : Abound ν B I (m + 1) j =
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (B * Abound ν B I m (j - i + 1) + |ν - (m : ℝ)| * B * Abound ν B I m (j - i)) := rfl
    have hDb : Db ν B I Id δ (m + 1) j =
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (B * δ * Abound ν B I m (j - i + 1) + B * Db ν B I Id δ m (j - i + 1)
           + |ν - (m : ℝ)| * (B * δ * Abound ν B I m (j - i)
              + B * Db ν B I Id δ m (j - i))) := rfl
    have ihA : ∀ i ≤ j, |Rjet ν h init m (j - i + 1) a σ t| ≤ Abound ν B I m (j - i + 1) :=
      fun i hi' => (ih (j - i + 1) (by omega) a σ t hreg).1
    have ihA0 : ∀ i ≤ j, |Rjet ν 0 initd m (j - i + 1) a σ t| ≤ Abound ν B I m (j - i + 1) :=
      fun i hi' => (ih (j - i + 1) (by omega) a σ t hreg).2.1
    have ihB : ∀ i ≤ j, |Rjet ν h init m (j - i) a σ t| ≤ Abound ν B I m (j - i) :=
      fun i hi' => (ih (j - i) (by omega) a σ t hreg).1
    have ihB0 : ∀ i ≤ j, |Rjet ν 0 initd m (j - i) a σ t| ≤ Abound ν B I m (j - i) :=
      fun i hi' => (ih (j - i) (by omega) a σ t hreg).2.1
    have ihD : ∀ i ≤ j,
        |Rjet ν h init m (j - i + 1) a σ t - Rjet ν 0 initd m (j - i + 1) a σ t| ≤
          Db ν B I Id δ m (j - i + 1) :=
      fun i hi' => (ih (j - i + 1) (by omega) a σ t hreg).2.2
    have ihD0 : ∀ i ≤ j,
        |Rjet ν h init m (j - i) a σ t - Rjet ν 0 initd m (j - i) a σ t| ≤
          Db ν B I Id δ m (j - i) :=
      fun i hi' => (ih (j - i) (by omega) a σ t hreg).2.2
    have hZi : ∀ i ≤ j, |ZJ h i a σ t| ≤ B := fun i hi' => (hz i (by omega) a σ t hreg).1
    have hZi0 : ∀ i ≤ j, |ZJ 0 i a σ t| ≤ B := fun i hi' => (hz i (by omega) a σ t hreg).2.1
    have hZi1 : ∀ i ≤ j, |ZJ h (i + 1) a σ t| ≤ B :=
      fun i hi' => (hz (i + 1) (by omega) a σ t hreg).1
    have hZi10 : ∀ i ≤ j, |ZJ 0 (i + 1) a σ t| ≤ B :=
      fun i hi' => (hz (i + 1) (by omega) a σ t hreg).2.1
    have hZid : ∀ i ≤ j, |ZJ h i a σ t - ZJ 0 i a σ t| ≤ B * δ :=
      fun i hi' => (hz i (by omega) a σ t hreg).2.2
    have hZi1d : ∀ i ≤ j, |ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t| ≤ B * δ :=
      fun i hi' => (hz (i + 1) (by omega) a σ t hreg).2.2
    have hAn : ∀ i, 0 ≤ Abound ν B I m i := Abound_nonneg ν B I hB hI m
    have hDn : ∀ i, 0 ≤ Db ν B I Id δ m i := Db_nonneg ν B I Id δ hB hI hId hδ.le m
    refine ⟨?_, ?_, ?_⟩
    · rw [hexp, hAb]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i hi' => ?_
      have hi'' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      have hC : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      have h1 := ihA i hi''
      have h2 := ihB i hi''
      have h3 := hZi i hi''
      have h4 := hZi1 i hi''
      have h5 : (0 : ℝ) ≤ |ν - (m : ℝ)| := abs_nonneg _
      rw [abs_mul, abs_of_nonneg hC]
      refine mul_le_mul_of_nonneg_left ?_ hC
      have e1 : |ZJ h i a σ t * Rjet ν h init m (j - i + 1) a σ t| ≤
          B * Abound ν B I m (j - i + 1) := by
        rw [abs_mul]; exact mul_le_mul h3 h1 (abs_nonneg _) hB
      have e2 : |(ν - (m : ℝ)) * (ZJ h (i + 1) a σ t * Rjet ν h init m (j - i) a σ t)| ≤
          |ν - (m : ℝ)| * (B * Abound ν B I m (j - i)) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ h5
        rw [abs_mul]
        exact mul_le_mul h4 h2 (abs_nonneg _) hB
      calc |ZJ h i a σ t * Rjet ν h init m (j - i + 1) a σ t +
            (ν - (m : ℝ)) * (ZJ h (i + 1) a σ t * Rjet ν h init m (j - i) a σ t)|
          ≤ |ZJ h i a σ t * Rjet ν h init m (j - i + 1) a σ t| +
            |(ν - (m : ℝ)) * (ZJ h (i + 1) a σ t * Rjet ν h init m (j - i) a σ t)| :=
            abs_add_le _ _
        _ ≤ B * Abound ν B I m (j - i + 1) + |ν - (m : ℝ)| * (B * Abound ν B I m (j - i)) :=
            add_le_add e1 e2
        _ = B * Abound ν B I m (j - i + 1) + |ν - (m : ℝ)| * B * Abound ν B I m (j - i) := by
            ring
    · rw [hexp0, hAb]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i hi' => ?_
      have hi'' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      have hC : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      have h1 := ihA0 i hi''
      have h2 := ihB0 i hi''
      have h3 := hZi0 i hi''
      have h4 := hZi10 i hi''
      have h5 : (0 : ℝ) ≤ |ν - (m : ℝ)| := abs_nonneg _
      rw [abs_mul, abs_of_nonneg hC]
      refine mul_le_mul_of_nonneg_left ?_ hC
      have e1 : |ZJ 0 i a σ t * Rjet ν 0 initd m (j - i + 1) a σ t| ≤
          B * Abound ν B I m (j - i + 1) := by
        rw [abs_mul]; exact mul_le_mul h3 h1 (abs_nonneg _) hB
      have e2 : |(ν - (m : ℝ)) * (ZJ 0 (i + 1) a σ t * Rjet ν 0 initd m (j - i) a σ t)| ≤
          |ν - (m : ℝ)| * (B * Abound ν B I m (j - i)) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ h5
        rw [abs_mul]
        exact mul_le_mul h4 h2 (abs_nonneg _) hB
      calc |ZJ 0 i a σ t * Rjet ν 0 initd m (j - i + 1) a σ t +
            (ν - (m : ℝ)) * (ZJ 0 (i + 1) a σ t * Rjet ν 0 initd m (j - i) a σ t)|
          ≤ |ZJ 0 i a σ t * Rjet ν 0 initd m (j - i + 1) a σ t| +
            |(ν - (m : ℝ)) * (ZJ 0 (i + 1) a σ t * Rjet ν 0 initd m (j - i) a σ t)| :=
            abs_add_le _ _
        _ ≤ B * Abound ν B I m (j - i + 1) + |ν - (m : ℝ)| * (B * Abound ν B I m (j - i)) :=
            add_le_add e1 e2
        _ = B * Abound ν B I m (j - i + 1) + |ν - (m : ℝ)| * B * Abound ν B I m (j - i) := by
            ring
    · rw [hexp, hexp0, hDb]
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i hi' => ?_
      have hi'' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
      have hC : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
      have h1 := ihA i hi''
      have h2 := ihB i hi''
      have h3 := hZi i hi''
      have h4 := hZi1 i hi''
      have h5 : (0 : ℝ) ≤ |ν - (m : ℝ)| := abs_nonneg _
      have h8 := ihD i hi''
      have h9 := ihD0 i hi''
      have h10 := hZid i hi''
      have h11 := hZi1d i hi''
      have h12 := hDn (j - i + 1)
      have h13 := hDn (j - i)
      have hDnn : (0 : ℝ) ≤ δ := hδ.le
      rw [← mul_sub, abs_mul, abs_of_nonneg hC]
      refine mul_le_mul_of_nonneg_left ?_ hC
      have hsplit :
          (ZJ h i a σ t * Rjet ν h init m (j - i + 1) a σ t
             + (ν - (m : ℝ)) * (ZJ h (i + 1) a σ t * Rjet ν h init m (j - i) a σ t))
          - (ZJ 0 i a σ t * Rjet ν 0 initd m (j - i + 1) a σ t
             + (ν - (m : ℝ)) * (ZJ 0 (i + 1) a σ t * Rjet ν 0 initd m (j - i) a σ t)) =
          ((ZJ h i a σ t - ZJ 0 i a σ t) * Rjet ν h init m (j - i + 1) a σ t
            + ZJ 0 i a σ t * (Rjet ν h init m (j - i + 1) a σ t
                - Rjet ν 0 initd m (j - i + 1) a σ t))
          + (ν - (m : ℝ)) * ((ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t)
              * Rjet ν h init m (j - i) a σ t
            + ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
                - Rjet ν 0 initd m (j - i) a σ t)) := by ring
      rw [hsplit]
      have e1 : |(ZJ h i a σ t - ZJ 0 i a σ t) * Rjet ν h init m (j - i + 1) a σ t| ≤
          B * δ * Abound ν B I m (j - i + 1) := by
        rw [abs_mul]
        exact mul_le_mul h10 h1 (abs_nonneg _) (mul_nonneg hB hDnn)
      have e2 : |ZJ 0 i a σ t * (Rjet ν h init m (j - i + 1) a σ t
            - Rjet ν 0 initd m (j - i + 1) a σ t)| ≤ B * Db ν B I Id δ m (j - i + 1) := by
        rw [abs_mul]
        exact mul_le_mul (hZi0 i hi'') h8 (abs_nonneg _) hB
      have e3 : |(ν - (m : ℝ)) * ((ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t)
              * Rjet ν h init m (j - i) a σ t
            + ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
                - Rjet ν 0 initd m (j - i) a σ t))| ≤
          |ν - (m : ℝ)| * (B * δ * Abound ν B I m (j - i) + B * Db ν B I Id δ m (j - i)) := by
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ h5
        have f1 : |(ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t) * Rjet ν h init m (j - i) a σ t| ≤
            B * δ * Abound ν B I m (j - i) := by
          rw [abs_mul]
          exact mul_le_mul h11 h2 (abs_nonneg _) (mul_nonneg hB hDnn)
        have f2 : |ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
              - Rjet ν 0 initd m (j - i) a σ t)| ≤ B * Db ν B I Id δ m (j - i) := by
          rw [abs_mul]
          exact mul_le_mul (hZi10 i hi'') h9 (abs_nonneg _) hB
        calc |(ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t) * Rjet ν h init m (j - i) a σ t
              + ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
                  - Rjet ν 0 initd m (j - i) a σ t)|
            ≤ |(ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t) * Rjet ν h init m (j - i) a σ t|
              + |ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
                  - Rjet ν 0 initd m (j - i) a σ t)| := abs_add_le _ _
            _ ≤ B * δ * Abound ν B I m (j - i) + B * Db ν B I Id δ m (j - i) := add_le_add f1 f2
      have etot : |((ZJ h i a σ t - ZJ 0 i a σ t) * Rjet ν h init m (j - i + 1) a σ t
            + ZJ 0 i a σ t * (Rjet ν h init m (j - i + 1) a σ t
                - Rjet ν 0 initd m (j - i + 1) a σ t))
          + (ν - (m : ℝ)) * ((ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t)
              * Rjet ν h init m (j - i) a σ t
            + ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
                - Rjet ν 0 initd m (j - i) a σ t))| ≤
          B * δ * Abound ν B I m (j - i + 1) + B * Db ν B I Id δ m (j - i + 1)
          + |ν - (m : ℝ)| * (B * δ * Abound ν B I m (j - i) + B * Db ν B I Id δ m (j - i)) := by
        calc |((ZJ h i a σ t - ZJ 0 i a σ t) * Rjet ν h init m (j - i + 1) a σ t
              + ZJ 0 i a σ t * (Rjet ν h init m (j - i + 1) a σ t
                  - Rjet ν 0 initd m (j - i + 1) a σ t))
            + (ν - (m : ℝ)) * ((ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t)
                * Rjet ν h init m (j - i) a σ t
              + ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
                  - Rjet ν 0 initd m (j - i) a σ t))|
            ≤ |(ZJ h i a σ t - ZJ 0 i a σ t) * Rjet ν h init m (j - i + 1) a σ t
              + ZJ 0 i a σ t * (Rjet ν h init m (j - i + 1) a σ t
                  - Rjet ν 0 initd m (j - i + 1) a σ t)|
              + |(ν - (m : ℝ)) * ((ZJ h (i + 1) a σ t - ZJ 0 (i + 1) a σ t)
                * Rjet ν h init m (j - i) a σ t
              + ZJ 0 (i + 1) a σ t * (Rjet ν h init m (j - i) a σ t
                  - Rjet ν 0 initd m (j - i) a σ t))| := abs_add_le _ _
            _ ≤ (B * δ * Abound ν B I m (j - i + 1) + B * Db ν B I Id δ m (j - i + 1))
              + |ν - (m : ℝ)| * (B * δ * Abound ν B I m (j - i) + B * Db ν B I Id δ m (j - i)) := by
                refine add_le_add ?_ e3
                exact le_trans (abs_add_le _ _) (add_le_add e1 e2)
            _ = B * δ * Abound ν B I m (j - i + 1) + B * Db ν B I Id δ m (j - i + 1)
              + |ν - (m : ℝ)| * (B * δ * Abound ν B I m (j - i)
                  + B * Db ν B I Id δ m (j - i)) := by ring
      exact etot


end Work.Anchor
