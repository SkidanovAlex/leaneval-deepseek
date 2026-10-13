import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.sphAux
import Submission.Work.WilE3.Taylor.CaseII.PertShear

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **`C¹` regularity of the master data**.

  The master system of the boundary case is

  * `Amas c Φ y i₀ j₀ : (Fin k → ℝ) → (Fin k → ℝ)`, with rows `Φ`, `Sq y = ∑(x-y)²` and the radial
    shear coefficients `shAₗ`;
  * `bmas c Φ y i₀ j₀ : (Fin k → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin k → ℝ)`, the parameter directions
    `shB1ₗ · θ₀ + shB2ₗ · θ₁`.

  All of these are built from evaluations `eaEval c Q` of EA polynomials (analytic everywhere, hence
  `C¹`) and from *divisions* by `μ = ∂_{i₀}Φ (x_{j₀}-y_{j₀}) - ∂_{j₀}Φ (x_{i₀}-y_{i₀})` (and, in
  `shA`, additionally by `G = ∑ₗ (∂ₗΦ)²`).  On `Uset = {μ ≠ 0}` the denominator `μ` is non-zero by
  definition; `G` is non-zero there too, because `G` is a sum of squares, so `G = 0` forces
  `∇Φ = 0` and hence `μ = 0`.  This is the `hA`, `hb`, `hφ` input of the parametric Sard lemma
  `Work.WilE3.Taylor.CaseII.ae_regular_shear`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-! ## The individual `C¹` pieces -/

/-- `eaEval c Q` is real analytic, hence `C¹` on every set. -/
@[fun_prop]
lemma contDiffOn_eaEval' (c : EAChain k r) (Q : EAPoly k r) (s : Set (Fin k → ℝ)) :
    ContDiffOn ℝ 1 (fun x : Fin k → ℝ => eaEval c Q x) s :=
  fun x _ => (Work.WilE3.eaEval_analytic c Q x).contDiffAt.contDiffWithinAt

/-- `Wq c Φ i = ∂ᵢΦ` is `C¹` on every set. -/
@[fun_prop]
lemma contDiffOn_Wq (c : EAChain k r) (Φ : EAPoly k r) (i : Fin k) (s : Set (Fin k → ℝ)) :
    ContDiffOn ℝ 1 (Wq c Φ i) s :=
  contDiffOn_eaEval' c (eaD c i Φ) s

/-- `dGq c Φ i = ∂ᵢG`, `G = sqGrad c Φ`, is `C¹` on every set. -/
@[fun_prop]
lemma contDiffOn_dGq (c : EAChain k r) (Φ : EAPoly k r) (i : Fin k) (s : Set (Fin k → ℝ)) :
    ContDiffOn ℝ 1 (dGq c Φ i) s :=
  contDiffOn_eaEval' c (eaD c i (sqGrad c Φ)) s

/-- `Gq c Φ = G = ∑ₗ (∂ₗΦ)²` is `C¹` on every set. -/
@[fun_prop]
lemma contDiffOn_Gq (c : EAChain k r) (Φ : EAPoly k r) (s : Set (Fin k → ℝ)) :
    ContDiffOn ℝ 1 (Gq c Φ) s :=
  contDiffOn_eaEval' c (sqGrad c Φ) s

/-- `Tq y i = xᵢ - yᵢ` is `C¹` on every set. -/
@[fun_prop]
lemma contDiffOn_Tq (y : Fin k → ℝ) (i : Fin k) (s : Set (Fin k → ℝ)) :
    ContDiffOn ℝ 1 (Tq y i) s :=
  (contDiffOn_apply ℝ ℝ i s).sub (contDiffOn_const (c := y i) (s := s))

/-- `muq c Φ y i₀ j₀ = ∂_{i₀}Φ (x_{j₀}-y_{j₀}) - ∂_{j₀}Φ (x_{i₀}-y_{i₀})` is `C¹` on every set. -/
@[fun_prop]
lemma contDiffOn_muq (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k)
    (s : Set (Fin k → ℝ)) : ContDiffOn ℝ 1 (muq c Φ y i₀ j₀) s := by
  have h : muq c Φ y i₀ j₀
      = fun x => Wq c Φ i₀ x * Tq y j₀ x - Wq c Φ j₀ x * Tq y i₀ x := rfl
  rw [h]
  exact ((contDiffOn_Wq c Φ i₀ s).mul (contDiffOn_Tq y j₀ s)).sub
    ((contDiffOn_Wq c Φ j₀ s).mul (contDiffOn_Tq y i₀ s))

/-- The squared distance `Sq y = ∑ᵢ (xᵢ-yᵢ)²` is `C¹` (a polynomial). -/
lemma contDiffOn_Sq (y : Fin k → ℝ) (s : Set (Fin k → ℝ)) : ContDiffOn ℝ 1 (Sq y) s := by
  have h : Sq y = fun x : Fin k → ℝ => ∑ i : Fin k, (x i - y i) ^ 2 := rfl
  rw [h]
  exact ContDiffOn.sum (fun i _ =>
    ((contDiffOn_apply ℝ ℝ i s).sub (contDiffOn_const (c := y i) (s := s))).pow 2)

/-! ## Non-vanishing of `G` on `Uset` -/

/-- A sum of squares of reals vanishes only if every term does. -/
lemma sum_sq_eq_zero {k : ℕ} (f : Fin k → ℝ) (h : ∑ i, (f i) ^ 2 = 0) : ∀ i, f i = 0 := by
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin k)), (0 : ℝ) ≤ (f i) ^ 2 :=
    fun i _ => sq_nonneg _
  intro i
  exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i))

/-- On `Uset = {μ ≠ 0}` the squared gradient norm `G = ∑ₗ (∂ₗΦ)²` does not vanish: `G = 0` forces
`∇Φ = 0`, hence `μ = 0`.  This is what makes the division in `shA` legitimate. -/
lemma Gq_ne_zero_of_muq_ne_zero (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (i₀ j₀ : Fin k) {x : Fin k → ℝ} (hx : muq c Φ y i₀ j₀ x ≠ 0) : Gq c Φ x ≠ 0 := by
  intro h
  have hG : Gq c Φ x = ∑ l : Fin k, (Wq c Φ l x) ^ 2 :=
    Work.WilE3.Taylor.eaEval_sqGrad c Φ x
  have hsum : ∑ l : Fin k, (Wq c Φ l x) ^ 2 = 0 := by rw [← hG]; exact h
  have hsq : ∀ l : Fin k, Wq c Φ l x = 0 := sum_sq_eq_zero _ hsum
  have h0 : muq c Φ y i₀ j₀ x = 0 := by
    rw [muq, hsq i₀, hsq j₀]
    ring
  exact hx h0

/-! ## `C¹` regularity of the shear coefficients on `Uset` -/

/-- `shAₗ = Pₗ/(G·μ)` is `C¹` on `Uset`.  Both factors of the denominator are non-zero there:
`μ` by definition of `Uset`, and `G` by `Gq_ne_zero_of_muq_ne_zero`. -/
lemma contDiffOn_shA (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ l : Fin k) :
    ContDiffOn ℝ 1 (shA c Φ y i₀ j₀ l) (Uset c Φ y i₀ j₀) := by
  refine ContDiffOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro x hx
    exact mul_ne_zero (Gq_ne_zero_of_muq_ne_zero c Φ y i₀ j₀ hx) hx

/-- `shB1ₗ = (∂_{j₀}Φ (xₗ-yₗ) - ∂ₗΦ (x_{j₀}-y_{j₀}))/μ` is `C¹` on `Uset`. -/
lemma contDiffOn_shB1 (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ l : Fin k) :
    ContDiffOn ℝ 1 (shB1 c Φ y i₀ j₀ l) (Uset c Φ y i₀ j₀) := by
  refine ContDiffOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro x hx; exact hx

/-- `shB2ₗ = -(∂_{i₀}Φ (xₗ-yₗ) - ∂ₗΦ (x_{i₀}-y_{i₀}))/μ` is `C¹` on `Uset`. -/
lemma contDiffOn_shB2 (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ l : Fin k) :
    ContDiffOn ℝ 1 (shB2 c Φ y i₀ j₀ l) (Uset c Φ y i₀ j₀) := by
  refine (ContDiffOn.div ?_ ?_ ?_).neg
  · fun_prop
  · fun_prop
  · intro x hx; exact hx

/-! ## The master data -/

theorem contDiffOn_master_data {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) :
    ContDiffOn ℝ 1 (Work.WilE3.Taylor.CaseII.Amas c Φ y i₀ j₀)
        (Work.WilE3.Taylor.CaseII.Uset c Φ y i₀ j₀) ∧
      ContDiffOn ℝ 1 (Work.WilE3.Taylor.CaseII.bmas c Φ y i₀ j₀)
        (Work.WilE3.Taylor.CaseII.Uset c Φ y i₀ j₀) ∧
      ContDiffOn ℝ 1 (fun x : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ x)
        (Work.WilE3.Taylor.CaseII.Uset c Φ y i₀ j₀) := by
  refine ⟨?_, ?_, contDiffOn_eaEval' c Φ _⟩
  · -- `Amas`: reduce to the `k` components.
    rw [contDiffOn_pi]
    intro i
    by_cases hi : i = i₀
    · exact (contDiffOn_eaEval' c Φ (Uset c Φ y i₀ j₀)).congr
        (fun x _ => by simp [Amas, hi])
    · by_cases hj : i = j₀
      · have hji : ¬ (j₀ = i₀) := fun h => hi (hj.trans h)
        exact (contDiffOn_Sq y (Uset c Φ y i₀ j₀)).congr
          (fun x _ => by simp [Amas, hj, hji])
      · exact (contDiffOn_shA c Φ y i₀ j₀ i).congr
          (fun x _ => by simp [Amas, hi, hj])
  · -- `bmas`: a family of continuous linear maps, tested against every `w : Fin 2 → ℝ`.
    rw [contDiffOn_clm_apply]
    intro w
    rw [contDiffOn_pi]
    intro i
    simp only [bmas, ContinuousLinearMap.pi_apply]
    split_ifs with h
    · simpa using (contDiffOn_const (c := (0 : ℝ)) (s := Uset c Φ y i₀ j₀))
    · simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] at *
      exact ((contDiffOn_shB1 c Φ y i₀ j₀ i).mul (contDiffOn_const (c := w 0))).add
        ((contDiffOn_shB2 c Φ y i₀ j₀ i).mul (contDiffOn_const (c := w 1)))

end Work.WilE3.Taylor.CaseII
