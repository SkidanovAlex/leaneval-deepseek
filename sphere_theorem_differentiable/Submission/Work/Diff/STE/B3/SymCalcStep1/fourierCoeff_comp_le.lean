import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.pdVecMulCompExpansion
import Submission.Work.Diff.STE.B3.integralCompPeriodicLe
import Submission.Work.Diff.STE.B3.pdVec_integral_le_CSq
import Submission.Work.Diff.STE.CSq_le_ENormSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `Hˢ`-continuity of the pull-back `u ↦ u ∘ T` for a periodic diffeomorphism `T` of the torus

For a `C^∞` map `T : (ι → ℝ) → (ι → ℝ)` which

* commutes with the unit translations (`hTper`), i.e. descends to the torus,
* is injective (`hinj`), and
* has everywhere invertible differential (`hdet`),

the composition map `u ↦ u ∘ T` is bounded on the Sobolev scale `CSq s` (the weighted `ℓ²` norm of
the Fourier coefficient family):

  `CSq s (fourierCoeff (u ∘ T)) ≤ C · CSq s (fourierCoeff u)`,

with a constant `C` depending only on `T` and `s`, uniformly in the `C^∞` `1`-periodic `u`.

## Route

* `CSq_le_ENormSq` : the weighted coefficient norm is bounded by the physical `Hᵏ` energy
  `ENormSq k v + ENormSq 0 v`; it applies to `v = u ∘ T` because `hTper` and the periodicity of
  `u` make `u ∘ T` periodic.
* `comp_ENormSq_le` (proved here): every level-`m` energy, `m ≤ s`, of `u ∘ T` is bounded by
  `C · CSq s (fourierCoeff u)`.  This is the heart of the estimate.
* `comp_pdV_integral_le` (proved here): the single term
  `∫_{cube} ‖∂^m_l (u ∘ T)‖² ≤ C · CSq s (fourierCoeff u)`.  Three ingredients:

  1. **Faà di Bruno / Leibniz** (`pdVecMulCompExpansion` with the constant factor `1`): the
     iterated derivative `∂^m_l (u ∘ T)` is a finite sum
     `Σ_i c_i(z) · (∂^{ord i}_{dir i} u)(T z)` with `ord i ≤ m` and smooth coefficients `c_i`
     depending only on `T` (and `m`, `l`).  Unlike the "localised" form of the same expansion,
     no support hypothesis on a cut-off is needed here — the coefficients are bounded on the
     compact cube with a bound independent of `u`.
  2. **Change of variables along `T`** (`integralCompPeriodicLe` at `K = [0,1]^ι`, where `T` is
     injective with invertible differential): each `∫_{cube} ‖(∂^{j} u)(T z)‖²` is bounded by
     `C · ∫_{cube} ‖∂^{j} u‖²`.
  3. **Sobolev comparison** (`pdVec_integral_le_CSq`): `∫_{cube} ‖∂^{j} u‖² ≤ C · CSq s
     (fourierCoeff u)` for `j ≤ s`.

No Sobolev embedding / sup-norm bound of `u` is used, so the result holds for all `s : ℕ` and all
index types `ι` (in particular for `s = 0` and for `Fintype.card ι ≥ 2 * s`).
-/

namespace Work.Diff.STE.B3.SymCalcStep1

open MeasureTheory BigOperators

noncomputable section

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The closed unit cube `[0,1]^ι`, used as a compact fundamental domain for the torus. -/
def closedCube : Set (ι → ℝ) := Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)

/-- The half open unit cube sits inside the closed one. -/
lemma unitCube_subset_closedCube : unitCube (ι := ι) ⊆ closedCube (ι := ι) := by
  intro x hx i _
  have h := Set.mem_pi.mp hx i (Set.mem_univ i)
  rw [Set.mem_Ioc] at h
  exact ⟨le_of_lt h.1, h.2⟩

lemma isCompact_closedCube : IsCompact (closedCube (ι := ι)) :=
  isCompact_univ_pi (fun _ : ι => isCompact_Icc)

/-- A partial derivative of a `1`-periodic differentiable function is `1`-periodic. -/
lemma periodic_pd {w : (ι → ℝ) → ℂ} (hw : Differentiable ℝ w) (hwp : Periodic1 w) (i : ι) :
    Periodic1 (pd i w) := by
  intro j x
  simp only [pd]
  have h1 : (fun y : ι → ℝ => w (y + Pi.single j 1)) = w := funext fun y => hwp j y
  have h2 : fderiv ℝ w x = fderiv ℝ (fun y : ι → ℝ => w (y + Pi.single j 1)) x := by rw [h1]
  have h3 : fderiv ℝ (fun y : ι → ℝ => w (y + Pi.single j 1)) x
      = (fderiv ℝ w (x + Pi.single j 1)) ∘SL
        (fderiv ℝ (fun y : ι → ℝ => y + Pi.single j 1) x) :=
    fderiv_comp x (hw.differentiableAt) (differentiableAt_id.add_const _)
  rw [h2, h3]
  have h4 : fderiv ℝ (fun y : ι → ℝ => y + Pi.single j 1) x = 1 := by
    rw [fderiv_add_const]
    exact fderiv_id
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

/-- Iterated partial derivatives of a `1`-periodic smooth function are `1`-periodic. -/
lemma periodic_pdVec {v : (ι → ℝ) → ℂ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvp : Periodic1 v)
    (m : ℕ) (l : Fin m → ι) : Periodic1 (pdVec m l v) := by
  induction m with
  | zero =>
    simpa [pdVec, pdList] using hvp
  | succ m ih =>
    rw [pdMulComp_pdVec_succ_cons m l v]
    exact periodic_pd ((pdMulComp_contDiff_pdVec m (Fin.tail l) hv).differentiable (by simp))
      (ih (Fin.tail l)) (l 0)

/-- **The `L²` energy of a single iterated derivative of a pull-back.**  For `m ≤ s`, the square
integral over the cube of `∂^m_l (v ∘ T)` is bounded by `C · CSq s (fourierCoeff v)`, the constant
depending only on `T` (and `m`, `l`, `s`). -/
lemma comp_pdV_integral_le (s : ℕ) (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hinj : Function.Injective T) (hdet : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0)
    (m : ℕ) (l : Fin m → ι) (hm : m ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) v → Periodic1 v →
      ∫ x in unitCube (ι := ι), ‖pdVec m l (fun x : ι → ℝ => v (T x)) x‖ ^ 2
        ≤ C * CSq s (fourierCoeff v) := by
  classical
  -- the change-of-variables constant and the Sobolev-comparison constant
  obtain ⟨Cj, hCjnn, hCjb⟩ := integralCompPeriodicLe T hT (closedCube (ι := ι))
    isCompact_closedCube hinj.injOn (fun z _ => hdet z)
  obtain ⟨C1, hC1nn, hC1b⟩ := pdVec_integral_le_CSq (ι := ι) s
  -- the Faà di Bruno expansion of `∂^m_l (v ∘ T)` (with the constant factor `1`)
  obtain ⟨α, hαft, ord, dir, c, hord, hcs, _hvan, hexp⟩ :=
    pdVecMulCompExpansion T hT (fun _ : ι → ℝ => (1 : ℂ)) contDiff_const m l
  letI : Fintype α := hαft
  -- a uniform bound for the coefficients on (the cube contained in) the closed cube
  have hbound : ∀ i : α, ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedCube (ι := ι), ‖c i z‖ ≤ M := by
    intro i
    obtain ⟨Mi, hMi⟩ := isCompact_closedCube.exists_bound_of_continuousOn
      ((hcs i).continuous.norm.continuousOn)
    exact ⟨max Mi 0, le_max_right _ _,
      fun z hz => le_trans (by simpa using hMi z hz) (le_max_left _ _)⟩
  choose Mfun hMfunn hMfunb using hbound
  set M : ℝ := ∑ i : α, Mfun i with hMdef
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun i _ => hMfunn i
  have hcz : ∀ (i : α) (z : ι → ℝ), z ∈ unitCube (ι := ι) → ‖c i z‖ ≤ M := by
    intro i z hz
    refine le_trans (hMfunb i z (unitCube_subset_closedCube hz)) ?_
    rw [hMdef]
    exact Finset.single_le_sum (fun j _ => hMfunn j) (Finset.mem_univ i)
  refine ⟨(Fintype.card α : ℝ) ^ 2 * M ^ 2 * Cj * C1, by positivity, ?_⟩
  intro v hv hvp
  -- the pointwise bound coming from the expansion
  have hpoint : ∀ z ∈ unitCube (ι := ι),
      ‖pdVec m l (fun x : ι → ℝ => v (T x)) z‖ ^ 2
        ≤ (Fintype.card α : ℝ) * M ^ 2
            * ∑ i : α, ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 := by
    intro z hz
    have hexpz : pdVec m l (fun x : ι → ℝ => v (T x)) z
        = ∑ i : α, c i z * pdVec (ord i) (dir i) v (T z) := by
      simpa only [Pi.one_apply, one_mul] using hexp v hv z
    rw [hexpz]
    calc ‖∑ i : α, c i z * pdVec (ord i) (dir i) v (T z)‖ ^ 2
        ≤ (∑ i : α, ‖c i z * pdVec (ord i) (dir i) v (T z)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (Finset.univ.card : ℝ)
            * ∑ i ∈ Finset.univ, ‖c i z * pdVec (ord i) (dir i) v (T z)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (Fintype.card α : ℝ)
            * ∑ i : α, M ^ 2 * ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg _) (hcz i z hz) 2
      _ = (Fintype.card α : ℝ) * M ^ 2
            * ∑ i : α, ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 := by
          rw [← Finset.mul_sum]
          ring
  -- integrability on the cube
  have hcont_lhs : Continuous (fun z : ι → ℝ => ‖pdVec m l (fun x : ι → ℝ => v (T x)) z‖ ^ 2) := by
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => v (T x)) := hv.comp hT
    exact (((pdMulComp_contDiff_pdVec m l hcd).continuous).norm).pow 2
  have hcont_rhs : Continuous (fun z : ι → ℝ => (Fintype.card α : ℝ) * M ^ 2
      * ∑ i : α, ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2) := by
    refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
    exact ((((continuous_pdVec (ord i) (dir i) v (hv.of_le (by simp))).comp
      hT.continuous).norm).pow 2)
  have hInt1 : IntegrableOn (fun z : ι → ℝ =>
      ‖pdVec m l (fun x : ι → ℝ => v (T x)) z‖ ^ 2) (unitCube (ι := ι)) volume :=
    (ContinuousOn.integrableOn_compact isCompact_closedCube
      hcont_lhs.continuousOn).mono_set unitCube_subset_closedCube
  have hInt2 : IntegrableOn (fun z : ι → ℝ => (Fintype.card α : ℝ) * M ^ 2
      * ∑ i : α, ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2) (unitCube (ι := ι)) volume :=
    (ContinuousOn.integrableOn_compact isCompact_closedCube
      hcont_rhs.continuousOn).mono_set unitCube_subset_closedCube
  have hmono := setIntegral_mono_on hInt1 hInt2 BesselCont.measSet_unitCube hpoint
  -- split the integral of the majorant
  have hsplit : ∫ z in unitCube (ι := ι), (Fintype.card α : ℝ) * M ^ 2
        * ∑ i : α, ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2
      = (Fintype.card α : ℝ) * M ^ 2 * ∑ i : α,
          ∫ z in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum]
    intro i _
    exact (ContinuousOn.integrableOn_compact isCompact_closedCube
      ((((continuous_pdVec (ord i) (dir i) v (hv.of_le (by simp))).comp
        hT.continuous).norm).pow 2).continuousOn).mono_set unitCube_subset_closedCube
  -- the bound for a single term
  have hterm : ∀ i : α, ∫ z in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2
      ≤ Cj * (C1 * CSq s (fourierCoeff v)) := by
    intro i
    have hg : Continuous (pdVec (ord i) (dir i) v) :=
      continuous_pdVec (ord i) (dir i) v (hv.of_le (by simp))
    have hgp : Periodic1 (pdVec (ord i) (dir i) v) := periodic_pdVec hv hvp (ord i) (dir i)
    have hstep1 : ∫ z in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2
        ≤ ∫ z in closedCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 :=
      setIntegral_mono_set
        (ContinuousOn.integrableOn_compact isCompact_closedCube
          (((hg.norm.pow 2).comp hT.continuous).continuousOn))
        (Filter.Eventually.of_forall fun _ => by positivity)
        (Filter.Eventually.of_forall fun z hz => unitCube_subset_closedCube hz)
    have hstep2 : ∫ z in closedCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2
        ≤ Cj * ∫ x in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v x‖ ^ 2 := hCjb _ hg hgp
    have hstep3 : ∫ x in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v x‖ ^ 2
        ≤ C1 * CSq s (fourierCoeff v) :=
      hC1b v hv hvp (ord i) (le_trans (hord i) hm) (dir i)
    calc ∫ z in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2
        ≤ ∫ z in closedCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 := hstep1
      _ ≤ Cj * ∫ x in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v x‖ ^ 2 := hstep2
      _ ≤ Cj * (C1 * CSq s (fourierCoeff v)) := mul_le_mul_of_nonneg_left hstep3 hCjnn
  have hsum : ∑ i : α, ∫ z in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2
      ≤ (Fintype.card α : ℝ) * (Cj * (C1 * CSq s (fourierCoeff v))) := by
    calc ∑ i : α, ∫ z in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2
        ≤ ∑ _i : α, Cj * (C1 * CSq s (fourierCoeff v)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (Fintype.card α : ℝ) * (Cj * (C1 * CSq s (fourierCoeff v))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ∫ x in unitCube (ι := ι), ‖pdVec m l (fun x : ι → ℝ => v (T x)) x‖ ^ 2
      ≤ ∫ z in unitCube (ι := ι), (Fintype.card α : ℝ) * M ^ 2
          * ∑ i : α, ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 := hmono
    _ = (Fintype.card α : ℝ) * M ^ 2 * ∑ i : α,
          ∫ z in unitCube (ι := ι), ‖pdVec (ord i) (dir i) v (T z)‖ ^ 2 := hsplit
    _ ≤ (Fintype.card α : ℝ) * M ^ 2
          * ((Fintype.card α : ℝ) * (Cj * (C1 * CSq s (fourierCoeff v)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Fintype.card α : ℝ) ^ 2 * M ^ 2 * Cj * C1 * CSq s (fourierCoeff v) := by ring

/-- **The energy of a pull-back at a single level.**  For `m ≤ s` there is a constant `C` with
`ENormSq m (v ∘ T) ≤ C · CSq s (fourierCoeff v)` for all smooth `1`-periodic `v`. -/
lemma comp_ENormSq_le (s : ℕ) (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hinj : Function.Injective T) (hdet : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0)
    (m : ℕ) (hm : m ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) v → Periodic1 v →
      ENormSq m (fun x : ι → ℝ => v (T x)) ≤ C * CSq s (fourierCoeff v) := by
  classical
  choose C' hC'nn hC'b using fun l : Fin m → ι =>
    comp_pdV_integral_le s T hT hinj hdet m l hm
  refine ⟨∑ l : Fin m → ι, C' l, Finset.sum_nonneg fun l _ => hC'nn l, ?_⟩
  intro v hv hvp
  rw [show ENormSq m (fun x : ι → ℝ => v (T x))
      = ∑ l : Fin m → ι, ∫ x in unitCube (ι := ι), ‖pdVec m l (fun x : ι → ℝ => v (T x)) x‖ ^ 2
      from rfl]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun l _ => hC'b l v hv hvp

end Helpers

theorem fourierCoeff_comp_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ)
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hinj : Function.Injective T) (hdet : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => u (T x)))
        ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) := by
  classical
  obtain ⟨Cs, hCsnn, hCsb⟩ := comp_ENormSq_le s T hT hinj hdet s le_rfl
  obtain ⟨Cz, hCznn, hCzb⟩ := comp_ENormSq_le s T hT hinj hdet 0 (Nat.zero_le s)
  obtain ⟨C0, hC0nn, hC0b⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := ι) s
  refine ⟨C0 * (Cs + Cz), mul_nonneg hC0nn (add_nonneg hCsnn hCznn), ?_⟩
  intro u hu hup
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => u (T x)) := hu.comp hT
  have hcompp : Work.Diff.STE.Periodic1 (fun x : ι → ℝ => u (T x)) := by
    intro i x
    show u (T (x + Pi.single i 1)) = u (T x)
    rw [hTper i x, hup i (T x)]
  have h0 := hC0b (fun x : ι → ℝ => u (T x)) (hcomp.of_le (by simp)) hcompp
  have h1 := hCsb u hu hup
  have h2 := hCzb u hu hup
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => u (T x)))
      ≤ C0 * (Work.Diff.STE.ENormSq s (fun x : ι → ℝ => u (T x))
          + Work.Diff.STE.ENormSq 0 (fun x : ι → ℝ => u (T x))) := h0
    _ ≤ C0 * (Cs * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u)
          + Cz * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC0nn
    _ = C0 * (Cs + Cz) * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) := by ring

end

end Work.Diff.STE.B3.SymCalcStep1
