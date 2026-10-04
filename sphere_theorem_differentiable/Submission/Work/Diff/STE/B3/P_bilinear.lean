import Mathlib
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.flat.level_linear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-!
# `P_bilinear`: the bilinearity of the Layer B3 pairing

This file contains, above the target `P_bilinear`, the auxiliary lemmas its proof is assembled
from.  All of them are `private` (they are used only here).

The mathematical content, in the order of the file:

* `R_per` is linear in the *section*: `D.R i (u+v) a b = D.R i u a b + D.R i v a b` and
  `D.R i (r • u) a b = r • D.R i u a b` — this is `B3Data.R = ψ·√dens·D.mat`, and `B3Data.mat` is
  the evaluation of the section in the frame, which is additive/homogeneous because `Bil` is a Pi
  type of continuous linear maps.  No smoothness at all is needed for these two.
* The periodisation `D.Rper i h a b = perFun (D.R i h a b)` inherits this linearity from
  `perFun_add_fun` and `perFun_smul`, the support hypothesis being `D.psi_supp` transported to
  `D.R` (`R_support_Ioc`); note that no `[I.Boundaryless]` is needed.  The finite-sum version
  `R_finset_sum_smul` is the induction.
* `pdList`/`pdVec` are additive and homogeneous in the *function* as soon as the functions are
  smooth (`pdList_add`, `pdList_smul`): Mathlib's `fderiv` is junk-`0` off the differentiability
  set, so the smoothness hypotheses are essential here.
* `L2re` is symmetric (`L2re_comm`), homogeneous (`L2re_smul_left`), and its quadratic form is the
  physical `L²` norm squared (`L2re_self`); in the last two the Bochner integral of a scalar
  multiple and of the complexification of a real function are handled by the *unconditional*
  lemmas `integral_smul`, `integral_conj`, `integral_ofReal` (no integrability hypothesis).
* Combining these gives the six laws of `P_bilinear`: additivity (`ENormB_pair_add`), homogeneity
  (`ENormB_pair_smul`), the quadratic form (`ENormB_pair_self`), symmetry (`ENormB_pair_comm`),
  and the two finite-sum expansions (`ENormB_pair_sum_smul`, `ENormB_pair_sum_smul_self`), the
  induction for the last two using the smoothness of the partial sums
  (`ContDiff_R_finset_sum_smul`).
-/

section BilinearAux

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The localised component is linear in the section -/

/-- The support of the localised component lies in the half-open unit cube (from
`D.psi_supp`; no `[I.Boundaryless]`).  This is the hypothesis of `perFun_add`/`perFun_smul`. -/
private theorem R_support_Ioc (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun z hz => Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self)
    (D.psi_supp i (fun h0 => hz (by simp only [Work.Diff.STE.B3Data.R, h0, zero_mul])))

/-- `B3Data.R` is additive in the section (pointwise, no smoothness). -/
private theorem R_add (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u v : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (u + v) a b = D.R i u a b + D.R i v a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.add_apply, add_apply]
  ring

/-- `B3Data.R` is homogeneous in the section (pointwise, no smoothness). -/
private theorem R_smul (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Bil (I := I) (M := M)) (r : ℝ) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (r • u) a b = r • D.R i u a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.smul_apply, smul_apply,
    smul_eq_mul]
  ring

/-- The localised component of the zero section vanishes. -/
private theorem R_zero (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.R i (0 : Bil (I := I) (M := M)) a b = 0 := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
  simp

/-! ## 2. The periodisation is linear in the section -/

/-- The periodisation of the zero function vanishes. -/
private theorem perFun_zero {n : ℕ} : perFun (0 : (Fin n → ℝ) → ℝ) = 0 := by
  funext y
  simp [perFun]

/-- The periodisation of a real scalar multiple: `r • g` is the function `z ↦ r * g z`, and the
lattice sum is exchanged with the scalar with `Summable.tsum_const_smul`. -/
private theorem perFun_smul {n : ℕ} (g : (Fin n → ℝ) → ℝ) (r : ℝ)
    (hs : Function.support g ⊆ Set.pi Set.univ
      (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) :
    perFun (r • g) = r • perFun g := by
  funext y
  simp only [perFun]
  have hpt : ∀ k : Fin n → ℤ,
      (((r • g) (y + iVec k) : ℝ) : ℂ) = r • ((g (y + iVec k) : ℝ) : ℂ) := by
    intro k
    rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Algebra.smul_def]
    rfl
  rw [tsum_congr hpt]
  exact Summable.tsum_const_smul r (summable_perFun hs y)

/-- `D.Rper i · a b` is additive in the section. -/
private theorem Rper_add (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u v : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (u + v) a b = D.Rper i u a b + D.Rper i v a b := by
  show perFun (D.R i (u + v) a b) = perFun (D.R i u a b) + perFun (D.R i v a b)
  rw [R_add D i u v a b]
  exact perFun_add_fun _ _ (R_support_Ioc D i u a b) (R_support_Ioc D i v a b)

/-- `D.Rper i · a b` is homogeneous in the section. -/
private theorem Rper_smul (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Bil (I := I) (M := M)) (r : ℝ) (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (r • u) a b = r • D.Rper i u a b := by
  show perFun (D.R i (r • u) a b) = r • perFun (D.R i u a b)
  rw [R_smul D i u r a b]
  exact perFun_smul _ r (R_support_Ioc D i u a b)

/-- The periodised component of the zero section vanishes. -/
private theorem Rper_zero (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (0 : Bil (I := I) (M := M)) a b = 0 := by
  show perFun (D.R i (0 : Bil (I := I) (M := M)) a b) = 0
  rw [R_zero D i a b]
  exact perFun_zero

/-- `D.R i · a b` is additive over finite sums of scaled sections. -/
private theorem R_finset_sum_smul {ι : Type*} [DecidableEq ι]
    (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (s : Finset ι)
    (B : ι → Bil (I := I) (M := M)) (w : ι → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (∑ z ∈ s, w z • B z) a b = ∑ z ∈ s, w z • D.R i (B z) a b := by
  classical
  induction s using Finset.induction with
  | empty => simpa using R_zero D i a b
  | insert z s hz ih =>
      rw [Finset.sum_insert hz, R_add D i (w z • B z) (∑ x ∈ s, w x • B x) a b,
        R_smul D i (B z) (w z) a b, ih, Finset.sum_insert hz]

/-- `D.Rper i · a b` is additive over finite sums of scaled sections. -/
private theorem Rper_finset_sum_smul {ι : Type*} [DecidableEq ι]
    (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (s : Finset ι)
    (B : ι → Bil (I := I) (M := M)) (w : ι → ℝ) (a b : Fin (Module.finrank ℝ E)) :
    D.Rper i (∑ z ∈ s, w z • B z) a b = ∑ z ∈ s, w z • D.Rper i (B z) a b := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Rper_zero D i a b
  | insert z s hz ih =>
      rw [Finset.sum_insert hz, Rper_add D i (w z • B z) (∑ x ∈ s, w x • B x) a b,
        Rper_smul D i (B z) (w z) a b, ih, Finset.sum_insert hz]

/-! ## 3. The iterated partial derivatives and the `L²` pairing -/

/-- `pd` of the zero function vanishes. -/
private theorem pd_zero {n : ℕ} (i : Fin n) :
    Work.Diff.STE.pd i (0 : (Fin n → ℝ) → ℂ) = 0 := by
  funext x
  simp only [Work.Diff.STE.pd]
  simp

/-- `pdList` of the zero function vanishes. -/
private theorem pdList_zero {n : ℕ} (L : List (Fin n)) :
    Work.Diff.STE.pdList L (0 : (Fin n → ℝ) → ℂ) = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      show Work.Diff.STE.pd a (Work.Diff.STE.pdList L (0 : (Fin n → ℝ) → ℂ)) = 0
      rw [ih, pd_zero]

/-- `pdVec` of the zero function vanishes. -/
private theorem pdVec_zero {n k : ℕ} (l : Fin k → Fin n) :
    Work.Diff.STE.pdVec k l (0 : (Fin n → ℝ) → ℂ) = 0 := by
  simp only [Work.Diff.STE.pdVec]
  exact pdList_zero (List.ofFn l)

/-- `pd` is homogeneous over a constant real factor, for a smooth function.  (The smoothness is
needed: `fderiv` is junk-`0` where the function is not differentiable, and `fderiv_const_smul`
requires differentiability.) -/
private theorem pd_smul {n : ℕ} (i : Fin n) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℝ) :
    Work.Diff.STE.pd i (r • f) = r • Work.Diff.STE.pd i f := by
  funext x
  simp only [Work.Diff.STE.pd]
  rw [fderiv_const_smul (hf.differentiable (by simp) x) r]
  rfl

/-- `pdList` is homogeneous over a constant real factor, for a smooth function. -/
private theorem pdList_smul {n : ℕ} (L : List (Fin n)) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℝ) :
    Work.Diff.STE.pdList L (r • f) = r • Work.Diff.STE.pdList L f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      show Work.Diff.STE.pd a (Work.Diff.STE.pdList L (r • f))
        = r • Work.Diff.STE.pd a (Work.Diff.STE.pdList L f)
      rw [ih]
      exact pd_smul a (Work.Diff.STE.flat.contDiff_pdList_top hf L) r

/-- `pdVec` is homogeneous over a constant real factor, for a smooth function. -/
private theorem pdVec_smul {n k : ℕ} (l : Fin k → Fin n) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℝ) :
    Work.Diff.STE.pdVec k l (r • f) = r • Work.Diff.STE.pdVec k l f := by
  simp only [Work.Diff.STE.pdVec]
  exact pdList_smul (List.ofFn l) hf r

/-- **The quadratic form of `L2re` is the physical `L²` norm squared**: `L2re g g = ∫ ‖g‖²`.
This holds for *every* `g` (no measurability or smoothness): the pointwise identity
`z * conj z = ↑‖z‖²` turns the integrand into the complexification of a real function, and
`integral_ofReal` (`Complex.ofRealLI` is a linear *equivalence*, so no integrability hypothesis). -/
private theorem L2re_self {n : ℕ} (g : (Fin n → ℝ) → ℂ) :
    L2re g g = ∫ x in unitCube, ‖g x‖ ^ 2 := by
  have hpt : (fun x : Fin n → ℝ => g x * star (g x))
      = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [show star (g x) = starRingEnd ℂ (g x) from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  simp only [L2re, hpt]
  rw [integral_complex_ofReal]
  rfl

/-- `L2re` is symmetric.  (`integral_conj` is unconditional.) -/
private theorem L2re_comm {n : ℕ} (f g : (Fin n → ℝ) → ℂ) : L2re f g = L2re g f := by
  simp only [L2re]
  have h1 : (∫ x in unitCube (ι := Fin n), g x * star (f x))
      = ∫ x in unitCube (ι := Fin n), (starRingEnd ℂ) (f x * star (g x)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [map_mul]
    simp [mul_comm]
  rw [h1, integral_conj]
  simp

/-- `L2re` is homogeneous in its first argument.  (`integral_smul` is unconditional.) -/
private theorem L2re_smul_left {n : ℕ} (r : ℝ) (f g : (Fin n → ℝ) → ℂ) :
    L2re (r • f) g = r * L2re f g := by
  have hsm : ∀ z : ℂ, r • z = (r : ℂ) * z := fun z => by rw [Algebra.smul_def]; rfl
  simp only [L2re]
  have hpt : (fun x : Fin n → ℝ => (r • f) x * star (g x))
      = fun x => r • (f x * star (g x)) := by
    funext x
    rw [Pi.smul_apply, hsm, hsm]
    ring
  rw [hpt, MeasureTheory.integral_smul, hsm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `L2re` of the zero function vanishes. -/
private theorem L2re_zero_left {n : ℕ} (g : (Fin n → ℝ) → ℂ) :
    L2re (0 : (Fin n → ℝ) → ℂ) g = 0 := by
  simp only [L2re]
  simp

/-- `L2re` of a sum of two smooth functions, differentiated `k` times. -/
private theorem L2re_pdVec_add {n k : ℕ} (l : Fin k → Fin n) {f₁ f₂ g : (Fin n → ℝ) → ℂ}
    (h1 : ContDiff ℝ (⊤ : ℕ∞) f₁) (h2 : ContDiff ℝ (⊤ : ℕ∞) f₂) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    L2re (Work.Diff.STE.pdVec k l (f₁ + f₂)) (Work.Diff.STE.pdVec k l g)
      = L2re (Work.Diff.STE.pdVec k l f₁) (Work.Diff.STE.pdVec k l g)
        + L2re (Work.Diff.STE.pdVec k l f₂) (Work.Diff.STE.pdVec k l g) := by
  simp only [Work.Diff.STE.pdVec]
  rw [Work.Diff.STE.flat.pdList_add (List.ofFn l) h1 h2]
  exact Work.Diff.STE.flat.L2re_add_left
    (Work.Diff.STE.flat.contDiff_pdList_top h1 _).continuous
    (Work.Diff.STE.flat.contDiff_pdList_top h2 _).continuous
    (Work.Diff.STE.flat.contDiff_pdList_top hg _).continuous

/-- `L2re` of a constant real multiple of a smooth function, differentiated `k` times. -/
private theorem L2re_pdVec_smul {n k : ℕ} (l : Fin k → Fin n) (r : ℝ)
    {f g : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (_hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    L2re (Work.Diff.STE.pdVec k l (r • f)) (Work.Diff.STE.pdVec k l g)
      = r * L2re (Work.Diff.STE.pdVec k l f) (Work.Diff.STE.pdVec k l g) := by
  simp only [Work.Diff.STE.pdVec]
  rw [pdList_smul (List.ofFn l) hf r]
  exact L2re_smul_left r _ _

/-! ## 4. The pairing `ENormB_pair` -/

/-- The pairing of the zero section (on the left) vanishes. -/
private theorem ENormB_pair_zero_left (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (W : Bil (I := I) (M := M)) :
    D.ENormB_pair k (0 : Bil (I := I) (M := M)) W = 0 := by
  simp only [Work.Diff.STE.B3Data.ENormB_pair]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun a _ =>
    Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun l _ => ?_))))
  rw [show D.Rper i (0 : Bil (I := I) (M := M)) a b = 0 from Rper_zero D i a b,
    pdVec_zero, L2re_zero_left]

/-- **Additivity of the pairing in its first argument.**  For each `(i,a,b,l)` the summand is
`L2re (pdVec k l (Rper i (u+v) a b)) (pdVec k l (Rper i W a b))`; `Rper` is additive in the
section, `pdVec` is additive on smooth functions, and `L2re` is additive in its first argument
(continuity from `Rper_contDiff_periodic_of_R_contDiff`); then distribute the finite sums. -/
private theorem ENormB_pair_add (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (u v W : Bil (I := I) (M := M))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b))
    (hv : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i v a b))
    (hW : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i W a b)) :
    D.ENormB_pair k (u + v) W = D.ENormB_pair k u W + D.ENormB_pair k v W := by
  have hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (f : Bil (I := I) (M := M)),
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) →
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i f a b) :=
    fun i a b f hf => (Rper_contDiff_periodic_of_R_contDiff D i f a b (hf i a b)).1
  have key : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (l : Fin k → Fin (Module.finrank ℝ E)),
      L2re (Work.Diff.STE.pdVec k l (D.Rper i (u + v) a b))
          (Work.Diff.STE.pdVec k l (D.Rper i W a b))
        = L2re (Work.Diff.STE.pdVec k l (D.Rper i u a b))
            (Work.Diff.STE.pdVec k l (D.Rper i W a b))
          + L2re (Work.Diff.STE.pdVec k l (D.Rper i v a b))
            (Work.Diff.STE.pdVec k l (D.Rper i W a b)) := by
    intro i a b l
    rw [Rper_add D i u v a b]
    exact L2re_pdVec_add l (hsm i a b u hu) (hsm i a b v hv) (hsm i a b W hW)
  simp only [Work.Diff.STE.B3Data.ENormB_pair]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun l _ => key i a b l))))

/-- **Homogeneity of the pairing in its first argument.** -/
private theorem ENormB_pair_smul (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (r : ℝ)
    (u W : Bil (I := I) (M := M))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b))
    (hW : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i W a b)) :
    D.ENormB_pair k (r • u) W = r * D.ENormB_pair k u W := by
  have hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (f : Bil (I := I) (M := M)),
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) →
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i f a b) :=
    fun i a b f hf => (Rper_contDiff_periodic_of_R_contDiff D i f a b (hf i a b)).1
  have key : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (l : Fin k → Fin (Module.finrank ℝ E)),
      L2re (Work.Diff.STE.pdVec k l (D.Rper i (r • u) a b))
          (Work.Diff.STE.pdVec k l (D.Rper i W a b))
        = r * L2re (Work.Diff.STE.pdVec k l (D.Rper i u a b))
            (Work.Diff.STE.pdVec k l (D.Rper i W a b)) := by
    intro i a b l
    rw [Rper_smul D i u r a b]
    exact L2re_pdVec_smul l r (hsm i a b u hu) (hsm i a b W hW)
  simp only [Work.Diff.STE.B3Data.ENormB_pair]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun l _ => key i a b l))))

/-- **The quadratic form of the pairing is the physical energy `D.ENormB`** (no smoothness
hypothesis is needed: this is `L2re_self`, component by component, plus the definitions of
`ENormB` and `ENormSq`). -/
private theorem ENormB_pair_self (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (u : Bil (I := I) (M := M)) :
    D.ENormB_pair k u u = D.ENormB k u := by
  simp only [Work.Diff.STE.B3Data.ENormB_pair, Work.Diff.STE.B3Data.ENormB,
    Work.Diff.STE.ENormSq]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun l _ => L2re_self _))))

/-- **Symmetry of the pairing** (no smoothness hypothesis is needed). -/
private theorem ENormB_pair_comm (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (u v : Bil (I := I) (M := M)) :
    D.ENormB_pair k u v = D.ENormB_pair k v u := by
  simp only [Work.Diff.STE.B3Data.ENormB_pair]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun l _ => L2re_comm _ _))))

/-- The localised components of a finite linear combination of sections are smooth, whenever the
individual components are.  (`Finset.sum` in a function type is pointwise, so the `ContDiff.sum`
conclusion is re-written with `Finset.sum_apply`.) -/
private theorem ContDiff_R_finset_sum_smul {ι : Type*} [DecidableEq ι]
    (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (s : Finset ι)
    (B : ι → Bil (I := I) (M := M)) (w : ι → ℝ) (a b : Fin (Module.finrank ℝ E))
    (hs : ∀ z ∈ s, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (B z) a b)) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (∑ z ∈ s, w z • B z) a b) := by
  rw [R_finset_sum_smul D i s B w a b]
  have h : (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ z ∈ s, (w z • D.R i (B z) a b) x) = ∑ z ∈ s, w z • D.R i (B z) a b := by
    funext x
    rw [Finset.sum_apply]
  rw [← h]
  exact ContDiff.sum (fun z' hz' => (hs z' hz' i a b).const_smul (w z'))

/-- **The finite-sum expansion of the pairing** (the general `Finset` form; the target uses
`s = Finset.univ`).  The induction is over the finite set, the step being `ENormB_pair_add` and
`ENormB_pair_smul`; the smoothness of the partial sums is `ContDiff_R_finset_sum_smul`. -/
private theorem ENormB_pair_sum_smul {ι : Type*} [DecidableEq ι]
    (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (s : Finset ι)
    (B : ι → Bil (I := I) (M := M)) (w : ι → ℝ) (W : Bil (I := I) (M := M))
    (hs : ∀ z ∈ s, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (B z) a b))
    (hW : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i W a b)) :
    D.ENormB_pair k (∑ z ∈ s, w z • B z) W = ∑ z ∈ s, w z * D.ENormB_pair k (B z) W := by
  classical
  induction s using Finset.induction with
  | empty => simpa using ENormB_pair_zero_left D k W
  | insert z s hz ih =>
      have hzsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (w z • B z) a b) := by
        intro i a b
        rw [R_smul D i (B z) (w z) a b]
        exact (hs z (Finset.mem_insert_self z s) i a b).const_smul (w z)
      have hssm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (D.R i (∑ x ∈ s, w x • B x) a b) :=
        fun i a b => ContDiff_R_finset_sum_smul D i s B w a b
          (fun z' hz' => hs z' (Finset.mem_insert_of_mem hz'))
      rw [Finset.sum_insert hz]
      rw [ENormB_pair_add D k (w z • B z) (∑ x ∈ s, w x • B x) W hzsm hssm hW]
      rw [ih (fun z' hz' => hs z' (Finset.mem_insert_of_mem hz'))]
      rw [ENormB_pair_smul D k (w z) (B z) W (hs z (Finset.mem_insert_self z s)) hW,
        Finset.sum_insert hz]

/-- **The diagonal finite-sum expansion of the pairing** (the general `Finset` form): expand `S`
on the left with `ENormB_pair_sum_smul`, then expand each `D.ENormB_pair k (B z) S` on the right
(after symmetrising), and use `ENormB_pair_comm`. -/
private theorem ENormB_pair_sum_smul_self {ι : Type*} [DecidableEq ι]
    (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (s : Finset ι)
    (B : ι → Bil (I := I) (M := M)) (w : ι → ℝ)
    (hs : ∀ z ∈ s, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (B z) a b)) :
    D.ENormB_pair k (∑ z ∈ s, w z • B z) (∑ z ∈ s, w z • B z)
      = ∑ z ∈ s, ∑ z' ∈ s, w z * w z' * D.ENormB_pair k (B z) (B z') := by
  classical
  have hS : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (D.R i (∑ z ∈ s, w z • B z) a b) :=
    fun i a b => ContDiff_R_finset_sum_smul D i s B w a b hs
  rw [ENormB_pair_sum_smul D k s B w (∑ z ∈ s, w z • B z) hs hS]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [ENormB_pair_comm D k (B z) (∑ z ∈ s, w z • B z)]
  rw [ENormB_pair_sum_smul D k s B w (B z) hs (fun i a b => hs z hz i a b)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun z' hz' => ?_)
  rw [ENormB_pair_comm D k (B z') (B z), mul_assoc]

end BilinearAux

/-- **The `Hᵏ` pairing of the Layer B3 components is a symmetric bilinear form, whose quadratic form is the physical energy `D.ENormB`.**

Recall (`B3/BNorm_ENormB_equiv.lean`)
`D.ENormB_pair k u v = Σ i a b l, L2re (pdVec k l (D.Rper i u a b)) (pdVec k l (D.Rper i v a b))` and
`D.ENormB k u = Σ i a b, ENormSq k (D.Rper i u a b)`, where `ENormSq k f = Σ l, ∫‖pdVec k l f‖²`.

The hypothesis on a section `u` (written out below as `∀ i a b, ContDiff ℝ ∞ (D.R i u a b)`) is the standard component-smoothness assumption used everywhere in Layer B3; all the linearity statements are FALSE for arbitrary sections (Mathlib's `fderiv` is junk-`0` at non-differentiable points, so `pdVec` is only additive on smooth functions).

Ingredients:
* additivity/homogeneity of `D.Rper` in the section: `D.Rper i u a b` is by definition `Work.Diff.STE.B3.perFun (D.R i u a b)`, so `Work.Diff.STE.B3.perFun_add`/`perFun_add_fun` (from `B3/scoeff_add_of_support.lean`) apply, with the support hypothesis `Work.Diff.STE.B3Data.R_support` (support inside the open cube); homogeneity is `Summable.tsum_mul_left` with `summable_perFun`.  The pointwise facts `D.R i (u+v) a b = D.R i u a b + D.R i v a b` and `D.R i (r • u) a b = r • D.R i u a b` follow from the definitions (`B3Data.R`, `B3Data.mat`) by `funext z; simp only [B3Data.R, B3Data.mat, Pi.add_apply, add_apply]; ring` — do NOT import `Submission.Work.Diff.STE.D.Gal2.Inst`, whose import chain currently fails.
* additivity of `pdVec` over sums of smooth functions and over finite sums: `Work.Diff.STE.flat.pdList_add`, `Work.Diff.STE.flat.pdVec_finset_sum` (`flat/level_linear.lean`), together with the scalar-multiple case `pdList L (r • f) = r • pdList L f` (provable from `Work.Diff.STE.pd_mul_fn` with the constant function).
* additivity of `L2re` in its first argument: `Work.Diff.STE.flat.L2re_add_left` (needs `Continuous` of the entries, available from `ContDiff ℝ ∞` via `Rper_contDiff_periodic_of_R_contDiff`, `B3/ENormSq_le_CSq.lean`); symmetry of `L2re` (`L2re f g = L2re g f`, from `MeasureTheory.integral_conj` and `Complex.conj_re`).
* the quadratic form: `L2re g g = ∫ x in unitCube, ‖g x‖²` (from `Complex.mul_conj`, `MeasureTheory.integral_ofReal`, `Complex.ofReal_re`), which yields `D.ENormB_pair k u u = D.ENormB k u` with no smoothness hypothesis.
* the last two items follow from the first two by `Finset.induction`, the smoothness of the partial sums being derived from the hypothesis `∀ z, ∀ i a b, ContDiff ℝ ∞ (D.R i (B z) a b)`. -/
theorem P_bilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    (∀ (u v w : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)) →
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i v a b)) →
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i w a b)) →
        D.ENormB_pair k (u + v) w = D.ENormB_pair k u w + D.ENormB_pair k v w)
    ∧ (∀ (r : ℝ) (u w : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)) →
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i w a b)) →
        D.ENormB_pair k (r • u) w = r * D.ENormB_pair k u w)
    ∧ (∀ (u : Work.Diff.STE.Bil (I := I) (M := M)),
        D.ENormB_pair k u u = D.ENormB k u)
    ∧ (∀ u v : Work.Diff.STE.Bil (I := I) (M := M),
        D.ENormB_pair k u v = D.ENormB_pair k v u)
    ∧ (∀ {ι : Type*} [Fintype ι] (B : ι → Work.Diff.STE.Bil (I := I) (M := M)) (w : ι → ℝ)
        (W : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ z : ι, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (B z) a b)) →
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i W a b)) →
        D.ENormB_pair k (∑ z, w z • B z) W = ∑ z, w z * D.ENormB_pair k (B z) W)
    ∧ (∀ {ι : Type*} [Fintype ι] (B : ι → Work.Diff.STE.Bil (I := I) (M := M)) (w : ι → ℝ),
        (∀ z : ι, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (B z) a b)) →
        D.ENormB_pair k (∑ z, w z • B z) (∑ z, w z • B z)
          = ∑ z, ∑ z', w z * w z' * D.ENormB_pair k (B z) (B z')) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v w hu hv hw
    exact ENormB_pair_add D k u v w hu hv hw
  · intro r u w hu hw
    exact ENormB_pair_smul D k r u w hu hw
  · intro u
    exact ENormB_pair_self D k u
  · intro u v
    exact ENormB_pair_comm D k u v
  · intro ι _ B w W hB hW
    exact ENormB_pair_sum_smul D k Finset.univ B w W (fun z _ => hB z) hW
  · intro ι _ B w hB
    exact ENormB_pair_sum_smul_self D k Finset.univ B w (fun z _ => hB z)

end Work.Diff.STE.B3
