import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.gardClauses
import Submission.Work.Diff.STE.Lead.Gal.gardJet_holds
import Submission.Work.Diff.STE.Lead.Gal.ofRealPdVecDict
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.Rres_eq_residualLow
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From the `R_j`-level transport identity to `GardData`

`Work.Diff.STE.B3.Rres_eq_residualLow` (PROVED) is the transport identity at the level of the
*localised* components, with the principal coefficient the inverse of the *coordinate* chart matrix:

`D.R j (P h) a b z = Σ_{pq} ((Gf j z)⁻¹)_{pq} ∂_p∂_q (D.R j h a b) z + residualLow D h j z a b`
for `‖z‖ ≤ 2 σ j` (this is `Rres` unfolded).

The Gårding assembly `Work.Diff.STE.Lead.Gal.gardingAssembly` needs the same identity for the
*periodised* components `D.Rper` (valid for every `z`), with a **1-periodic** coefficient `A`
agreeing with `(Gf j ·)⁻¹` on the `2σ j`-ball, and with the energy bounds of the residual.

The three inputs of `GardData_of_data` are the three work packages (see `gardClauses.lean`):

* `hA` — `Work.Diff.STE.Lead.Gal.gardAuniform`, i.e. `GardA`;
* `hP` — `Work.Diff.STE.Lead.Gal.residualDataPsi`, i.e. `GardP`;
* `hL` — `Work.Diff.STE.Lead.Gal.gardingLowEnergy`, i.e. `GardL`.

## The proof

Fix `j`, unpack `A` (`GardA`) and `Ψ` (`GardP`), and put `Th a b := gardPerC (Ψ a b)`, the
`1`-periodisation of `Ψ a b` (the same construction as `B3Data.Rper`).

1. `Th` is smooth (`periodization_contDiff_periodic`, using that `support (Ψ a b)` lies in the open
   `σ j`-ball and `σ j ≤ 1/8 < 1/2`) and `1`-periodic.  Its `pdVec`-jets of order `≤ k` are bounded
   by `2^n · CR` (`per_jets_le`), whence `ENormSq k (Th a b) ≤ card (Fin k → Idx) · (2^n · CR)²`
   (`ENormSq_le_of_sup_bound_b`).
2. The identity.  Let `F` be the difference of the two sides.  `F` is `1`-periodic (periodisations,
   `A` and `pd` of periodic functions are periodic) and continuous (all terms smooth).
   * On the open centred cube:
     - `D.Rper j P a b z = ((D.R j P a b z : ℝ) : ℂ)` and `Th a b z = Ψ a b z`
       (`periodization_eq_self`, since both supports lie in the open cube);
     - `pd c (pd d (D.Rper j h a b)) z = ((pdR c (pdR d (D.R j h a b)) z : ℝ) : ℂ)`
       (the two functions agree on the open cube, a neighbourhood of `z`, and `ofRealPdVecDict`
       identifies the complex and the real iterated partial derivatives);
     - if `‖z‖ ≤ 2 σ j`, `Rres_eq_residualLow` gives the identity, with `(Gf)⁻¹` replaced by `A`
       (`hA`) and `residualLow` replaced by `Ψ` (`hP`);
     - if `2 σ j < ‖z‖`, both sides vanish: the support of `R j P a b` (resp. of `Ψ a b`) lies in
       the open `σ j`-ball, and `Rper j h a b` vanishes on a neighbourhood of `z`, so its two
       partial derivatives vanish there as well.
   * Consequently `F` vanishes on the open cube, hence — being `1`-periodic and continuous —
     everywhere, by the usual `Int.fract`-shift plus radial limit argument.
3. The `H^{k-1}`/`L²` bounds are `GardL` (with `CL ≤ C`).
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-! ## 0. The `1`-periodisation of a complex-valued function -/

/-- The `1`-periodisation of a complex-valued function (the same construction as `B3Data.Rper`). -/
noncomputable def gardPerC {n : ℕ} (f : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun z => ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m)

lemma gardPerC_periodic {n : ℕ} (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.Periodic1 (gardPerC f) :=
  Work.Diff.STE.periodization_periodic f

lemma gardPerC_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ENat) f)
    (hsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ContDiff ℝ (⊤ : ENat) (gardPerC f) :=
  (Work.Diff.STE.periodization_contDiff_periodic f hf hsupp).1

/-! ## 1. Elementary periodicity bookkeeping -/

lemma periodic1_mul_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (f * g) := fun i x => by
  simp only [Pi.mul_apply, hf i x, hg i x]

lemma periodic1_add_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (f + g) := fun i x => by
  simp only [Pi.add_apply, hf i x, hg i x]

lemma periodic1_sub_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (f - g) := fun i x => by
  simp only [Pi.sub_apply, hf i x, hg i x]

lemma periodic1_ofReal_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : Work.Diff.STE.Periodic1 f) :
    Work.Diff.STE.Periodic1 (fun z => ((f z : ℝ) : ℂ)) := fun i x => by
  simp only [hf i x]

lemma periodic1_sum_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [Fintype α]
    (f : α → (ι → ℝ) → ℂ) (hf : ∀ a, Work.Diff.STE.Periodic1 (f a)) :
    Work.Diff.STE.Periodic1 (fun x => ∑ a, f a x) := fun i x =>
  Finset.sum_congr rfl (fun a _ => hf a i x)

/-- The `i`-th partial derivative of a `1`-periodic complex-valued function is `1`-periodic. -/
lemma pd_periodic_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (i : ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pd i f) := by
  intro j x
  have h1 : (fun y : ι → ℝ => f (y + Pi.single j 1)) = f := by
    funext y; exact hf j y
  have h2 : Work.Diff.STE.pd i (fun y : ι → ℝ => f (y + Pi.single j 1)) x
      = Work.Diff.STE.pd i f (x + Pi.single j 1) := by
    simp only [Work.Diff.STE.pd, fderiv_comp_add_right]
  rw [← h2, h1]

/-- The first partial derivative of a smooth function is smooth. -/
lemma contDiff_pd_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ENat) f) (i : ι) :
    ContDiff ℝ (⊤ : ENat) (Work.Diff.STE.pd i f) := by
  have h1 : ContDiff ℝ (⊤ : ENat) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ENat)) (by norm_num)
  have h2 : ContDiff ℝ (⊤ : ENat) (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) :=
    h1.clm_apply contDiff_const
  rw [show Work.Diff.STE.pd i f = (fun x : ι → ℝ => (fderiv ℝ f x) (Pi.single i 1)) from rfl]
  exact h2

/-- The second partial derivative of a smooth function is smooth. -/
lemma contDiff_pd_pd_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hsm : ContDiff ℝ (⊤ : ENat) f) (j i : ι) :
    ContDiff ℝ (⊤ : ENat) (Work.Diff.STE.pd i (Work.Diff.STE.pd j f)) :=
  contDiff_pd_rj (contDiff_pd_rj hsm j) i

/-- The complexification of a smooth real function is smooth. -/
lemma contDiff_ofReal_comp_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ENat) f) :
    ContDiff ℝ (⊤ : ENat) (fun z => ((f z : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-! ## 2. The dictionary between the complex `pd` of `Rper` and the real `pdR` of `R` -/

/-- `pd` depends only on the germ of the function. -/
lemma pd_congr_of_eventuallyEq_rj {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℂ}
    {x : ι → ℝ} (h : f =ᶠ[𝓝 x] g) (i : ι) :
    Work.Diff.STE.pd i f x = Work.Diff.STE.pd i g x := by
  rw [Work.Diff.STE.pd, Work.Diff.STE.pd, h.fderiv_eq]

/-- `pd c (pd d f)` is the `pdVec` of order two with directions `(c, d)`. -/
lemma pd_pd_eq_pdVec_two {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι)
    (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pd c (Work.Diff.STE.pd d f)
      = Work.Diff.STE.pdVec 2 (fun j : Fin 2 => if j = 0 then c else d) f := by
  have hfin : (fun j : Fin 2 => if j = 0 then c else d)
      = Fin.cons c (Fin.cons d (fun j : Fin 0 => j.elim0)) := by
    funext j
    fin_cases j <;> simp
  rw [hfin, Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_cons, List.ofFn_cons,
    List.ofFn_zero, List.foldr_cons, List.foldr_cons, List.foldr_nil]

/-- The real analogue of `pd_pd_eq_pdVec_two`. -/
lemma pdR_pdR_eq_pdRVec_two {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ι)
    (f : (ι → ℝ) → ℝ) :
    Work.Diff.STE.pdR c (Work.Diff.STE.pdR d f)
      = Work.Diff.STE.pdRVec 2 (fun j : Fin 2 => if j = 0 then c else d) f := by
  have hfin : (fun j : Fin 2 => if j = 0 then c else d)
      = Fin.cons c (Fin.cons d (fun j : Fin 0 => j.elim0)) := by
    funext j
    fin_cases j <;> simp
  rw [hfin, Work.Diff.STE.pdRVec, Work.Diff.STE.pdRList, List.ofFn_cons, List.ofFn_cons,
    List.ofFn_zero, List.foldr_cons, List.foldr_cons, List.foldr_nil]

/-- **The two-level dictionary**: the complex iterated partial derivatives of the complexification
of a real function are the complexifications of the real iterated partial derivatives. -/
lemma pd_pd_ofReal_rj {n : ℕ} (c d : Fin n) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pd c (Work.Diff.STE.pd d (fun y => ((f y : ℝ) : ℂ)))
      = fun z => ((Work.Diff.STE.pdR c (Work.Diff.STE.pdR d f) z : ℝ) : ℂ) := by
  have h2 := pd_pd_eq_pdVec_two c d (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
  have h3 := pdR_pdR_eq_pdRVec_two c d f
  rw [h2, h3, ofRealPdVecDict]

/-! ## 3. Elementary helpers -/

/-- A function vanishing near a point has vanishing first partial derivatives there. -/
lemma pd_eq_zero_of_eventuallyEq_zero {n : ℕ} {f : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ}
    (h : f =ᶠ[𝓝 x] 0) (i : Fin n) : Work.Diff.STE.pd i f x = 0 := by
  rw [Work.Diff.STE.pd, h.fderiv_eq]
  simp

/-- Each `pdVec` of a smooth function is smooth. -/
lemma contDiff_pdVec_b {n m : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) f) (l : Fin m → Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdVec m l f) :=
  Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn l) hsm

/-- The integral of the square of a continuous function bounded by `C` is at most `C ^ 2`. -/
lemma integral_normSq_le_b {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ z, ‖f z‖ ≤ C) :
    ∫ z in Work.Diff.STE.unitCube (ι := ι), ‖f z‖ ^ 2 ≤ C ^ 2 := by
  have hvol : (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι)) :
      MeasureTheory.Measure (ι → ℝ)).real Set.univ = 1 := by
    show ((MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι)) :
      MeasureTheory.Measure (ι → ℝ)) Set.univ).toReal = 1
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
    simp
  have h1 : ∫ z in Work.Diff.STE.unitCube (ι := ι), ‖f z‖ ^ 2
      ≤ ∫ _z in Work.Diff.STE.unitCube (ι := ι), C ^ 2 := by
    refine MeasureTheory.integral_mono_ae
      (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous (hf.norm.pow 2))
      (MeasureTheory.integrable_const _) ?_
    filter_upwards with z
    exact pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
  rwa [MeasureTheory.integral_const, smul_eq_mul, hvol, one_mul] at h1

/-- The energy of a continuous function whose `m`-th derivatives are pointwise bounded by `C`. -/
lemma ENormSq_le_of_sup_bound_b {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {C : ℝ}
    (hc : ∀ l : Fin m → Fin n, Continuous (Work.Diff.STE.pdVec m l f))
    (hb : ∀ (l : Fin m → Fin n) (z : Fin n → ℝ), ‖Work.Diff.STE.pdVec m l f z‖ ≤ C) :
    Work.Diff.STE.ENormSq m f ≤ (Fintype.card (Fin m → Fin n) : ℝ) * C ^ 2 := by
  have hterm : ∀ l : Fin m → Fin n,
      ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l f z‖ ^ 2 ≤ C ^ 2 :=
    fun l => integral_normSq_le_b (hc l) (hb l)
  rw [Work.Diff.STE.ENormSq]
  calc ∑ l : Fin m → Fin n,
        ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l f z‖ ^ 2
      ≤ ∑ _l : Fin m → Fin n, C ^ 2 := Finset.sum_le_sum (fun l _ => hterm l)
    _ = (Fintype.card (Fin m → Fin n) : ℝ) * C ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma ENormSq_nonneg_b {n m : ℕ} (f : (Fin n → ℝ) → ℂ) :
    0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- A function supported in the `σ`-ball with `σ ≤ 1/8` is supported in the open centred cube. -/
lemma support_cube_of_ball_rj {n : ℕ} {f : (Fin n → ℝ) → ℂ} {σ : ℝ} (hσ : σ ≤ 1 / 8)
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) σ) :
    Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro y hy
  rw [Set.mem_pi]
  intro i _
  have h1 : ‖y‖ < σ := by
    have := hsupp hy
    rwa [Metric.mem_ball, dist_zero_right] at this
  have h2 : |y i| ≤ ‖y‖ := norm_le_pi_norm y i
  have h3 : |y i| < 1 / 2 := lt_of_le_of_lt h2 (by linarith)
  exact ⟨by linarith [(abs_lt.mp h3).1], by linarith [(abs_lt.mp h3).2]⟩

/-! ## 4. The bridge -/

/-- **From the three work packages to `GardData`.**  See the module docstring for the proof. -/
theorem GardData_of_data
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k)
    (hA : ∀ (lam K : ℝ), 0 < lam → 0 < K → GardA (I := I) (M := M) D k lam K)
    (hP : ∀ (lam K : ℝ), 0 < lam → 0 < K → GardP (I := I) (M := M) D k lam K)
    (hL : ∀ (lam K : ℝ), 0 < lam → 0 < K → GardL (I := I) (M := M) D hLC k lam K) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d : Idx) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Idx) (z : Idx → ℝ),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
          GardData (I := I) (M := M) D hLC k lam' C h hsym hpos hsmooth := by
  intro lam K hlam hK
  obtain ⟨lam', CA, hlam'0, hCA0, hAb⟩ := hA lam K hlam hK
  obtain ⟨CR, hCR0, hPb⟩ := hP lam K hlam hK
  obtain ⟨CL, hCL0, hLb⟩ := hL lam K hlam hK
  set X : ℝ := (Fintype.card (Fin k → Idx) : ℝ)
    * ((2 : ℝ) ^ Module.finrank ℝ E * CR) ^ 2 with hXdef
  set C0 : ℝ := max (max CA X) CL with hC0def
  have hCAC : CA ≤ C0 := by
    rw [hC0def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hXC : X ≤ C0 := by
    rw [hC0def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCLC : CL ≤ C0 := by rw [hC0def]; exact le_max_right _ _
  have hC00 : 0 ≤ C0 := le_trans hCA0 hCAC
  refine ⟨lam', C0, hlam'0, hC00, ?_⟩
  intro h hsym hpos hsmooth hell hub hjet
  -- the open centred cube is open
  have hopenCube : IsOpen (Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  -- the DeTurck section has smooth chart data
  have hchP : Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) :=
    Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC h hsym hpos hsmooth
  refine fun j => ?_
  have hjet' : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → Idx) (z : Idx → ℝ)
      (c d : Idx),
      ‖z‖ ≤ 2 * D.σ i →
      ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ => ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K :=
    fun i m hm β z c d => hjet i c d m hm β z
  obtain ⟨A, hAsym, hAell, hAsmA, hAper, hAjet, hAeq⟩ := hAb h hsym hsmooth hell hub hjet' j
  obtain ⟨Ψ, hΨsm, hΨsupp, hΨjet, hΨeq⟩ := hPb h hsym hsmooth hell hub hjet' j
  -- ## the `Th` clauses
  have hσ8 : D.σ j ≤ 1 / 8 := by have := D.hσ2 j; linarith
  have hΨcube : ∀ a b, Function.support (Ψ a b) ⊆
      Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun a b => support_cube_of_ball_rj hσ8 (hΨsupp a b)
  have hThsm : ∀ a b, ContDiff ℝ (⊤ : ENat) (gardPerC (Ψ a b)) :=
    fun a b => gardPerC_smooth (hΨsm a b) (hΨcube a b)
  have hThper : ∀ a b, Work.Diff.STE.Periodic1 (gardPerC (Ψ a b)) :=
    fun a b => gardPerC_periodic (Ψ a b)
  have hThself : ∀ a b, ∀ z, (∀ i, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      gardPerC (Ψ a b) z = Ψ a b z :=
    fun a b z hz => (Work.Diff.STE.periodization_contDiff_periodic (Ψ a b)
      (hΨsm a b) (hΨcube a b)).2.2 z hz
  have hThjet : ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx) (z : Idx → ℝ) (a b : Idx),
      ‖Work.Diff.STE.pdVec m β (gardPerC (Ψ a b)) z‖
        ≤ (2 : ℝ) ^ Module.finrank ℝ E * CR := by
    intro m hm β z a b
    exact per_jets_le (n := Module.finrank ℝ E) (N := k) (σ := D.σ j) (B := CR)
      (le_of_lt (D.hσ j)) hσ8 hCR0 (hΨsm a b) (hΨsupp a b)
      (fun m' hm' γ w _ => hΨjet m' hm' γ w a b) m hm β z
  have hThen : ∀ a b, Work.Diff.STE.ENormSq k (gardPerC (Ψ a b)) ≤ X := by
    intro a b
    have h := ENormSq_le_of_sup_bound_b (n := Module.finrank ℝ E) (m := k)
      (f := gardPerC (Ψ a b)) (C := (2 : ℝ) ^ Module.finrank ℝ E * CR)
      (fun l => (contDiff_pdVec_b (hThsm a b) l).continuous)
      (fun l z => hThjet k le_rfl l z a b)
    rw [hXdef]
    exact h
  -- ## the identity
  have hId : ∀ a b z, D.Rper j
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
      = (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
          * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)
        + gardPerC (Ψ a b) z := by
    intro a b
    set F : (Idx → ℝ) → ℂ := fun z => D.Rper j
          (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
        - ((∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
            * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)
          + gardPerC (Ψ a b) z) with hFdef
    -- the dictionary on the open cube
    have hpdAll : ∀ (c d : Idx) (z : Idx → ℝ),
        (∀ i, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
        Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z
          = ((Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h a b)) z : ℝ) : ℂ) := by
      intro c d z hz
      have hmem : z ∈ Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
        simpa [Set.mem_pi] using hz
      have hevR : D.Rper j h a b =ᶠ[𝓝 z] (fun y => ((D.R j h a b y : ℝ) : ℂ)) :=
        Filter.eventually_of_mem (hopenCube.mem_nhds hmem)
          (fun y hy => D.Rper_eq_R j h a b (by simpa [Set.mem_pi] using hy))
      have hpd : Work.Diff.STE.pd d (D.Rper j h a b)
          =ᶠ[𝓝 z] Work.Diff.STE.pd d (fun y : Idx → ℝ => ((D.R j h a b y : ℝ) : ℂ)) := by
        filter_upwards [hevR.fderiv (𝕜 := ℝ)] with y hy
        simp only [Work.Diff.STE.pd]
        rw [hy]
      rw [pd_congr_of_eventuallyEq_rj hpd c]
      exact congrFun (pd_pd_ofReal_rj c d (D.R j h a b)) z
    -- periodicity and continuity of the difference
    have hsmL : ContDiff ℝ (⊤ : ENat) (D.Rper j
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b) :=
      (Work.Diff.STE.periodization_contDiff_periodic
        (f := fun y : Idx → ℝ =>
          ((D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b y
            : ℝ) : ℂ))
        (contDiff_ofReal_comp_rj
          (Work.Diff.STE.B3.R_contDiff_of_chartData D
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) hchP j a b))
        (support_cube_of_ball_rj hσ8
          (support_R_subset_ball D
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) j a b))).1
    have hsmH : ContDiff ℝ (⊤ : ENat) (D.Rper j h a b) :=
      (Work.Diff.STE.periodization_contDiff_periodic
        (f := fun y : Idx → ℝ => ((D.R j h a b y : ℝ) : ℂ))
        (contDiff_ofReal_comp_rj
          (Work.Diff.STE.B3.R_contDiff_of_chartData D h hsmooth j a b))
        (support_cube_of_ball_rj hσ8 (support_R_subset_ball D h j a b))).1
    have hperL : Work.Diff.STE.Periodic1 (D.Rper j
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b) :=
      Work.Diff.STE.periodization_periodic
        (fun y : Idx → ℝ =>
          ((D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b y
            : ℝ) : ℂ))
    have hperh : Work.Diff.STE.Periodic1 (D.Rper j h a b) :=
      Work.Diff.STE.periodization_periodic (fun y : Idx → ℝ => ((D.R j h a b y : ℝ) : ℂ))
    have hperR : Work.Diff.STE.Periodic1 (fun z => ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
        * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z) := by
      refine periodic1_sum_rj (fun c z => ∑ d, ((A c d z : ℝ) : ℂ)
        * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z) (fun c => ?_)
      refine periodic1_sum_rj (fun d z => ((A c d z : ℝ) : ℂ)
        * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z) (fun d => ?_)
      exact periodic1_mul_rj (periodic1_ofReal_rj (hAper c d))
        (pd_periodic_rj (pd_periodic_rj hperh d) c)
    have hsmS : ContDiff ℝ (⊤ : ENat) (fun z => ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
        * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z) := by
      refine ContDiff.sum (fun c _ => ContDiff.sum (fun d _ => ?_))
      exact (contDiff_ofReal_comp_rj (hAsmA c d)).mul (contDiff_pd_pd_rj hsmH d c)
    have hperF : Work.Diff.STE.Periodic1 F := by
      rw [hFdef]
      exact periodic1_sub_rj hperL (periodic1_add_rj hperR (gardPerC_periodic (Ψ a b)))
    have hcontF : Continuous F := by
      rw [hFdef]
      exact (hsmL.sub (hsmS.add (hThsm a b))).continuous
    -- vanishing on the open cube
    have hFcube : ∀ z, (∀ i, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) → F z = 0 := by
      intro z hz
      simp only [hFdef]
      by_cases hcase : ‖z‖ ≤ 2 * D.σ j
      · -- case 1: the transport identity applies
        have hres := Work.Diff.STE.B3.Rres_eq_residualLow D hLC h hsym hpos hsmooth j hcase a b
        rw [Work.Diff.STE.B3.Rres] at hres
        have hkey : D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
            = (∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
                * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
              + Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b := by
          linarith [hres]
        have hterm : ∀ p q : Idx,
            ((((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
                * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z : ℝ) : ℂ)
              = ((A p q z : ℝ) : ℂ)
                * Work.Diff.STE.pd p (Work.Diff.STE.pd q (D.Rper j h a b)) z := by
          intro p q
          rw [Complex.ofReal_mul, hAeq z hcase p q, (hpdAll p q z hz).symm]
        have hgoal : D.Rper j
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
            = (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)
              + gardPerC (Ψ a b) z := by
          rw [D.Rper_eq_R j
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b hz,
            hkey, Complex.ofReal_add, hThself a b z hz, hΨeq a b z hcase]
          congr 1
          · rw [Complex.ofReal_sum]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Complex.ofReal_sum]
            exact Finset.sum_congr rfl (fun q _ => hterm p q)
        exact sub_eq_zero.mpr hgoal
      · -- case 2: both sides vanish
        have hlt : D.σ j < ‖z‖ := by
          have h := D.hσ j
          push_neg at hcase
          linarith
        have hLHS : D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
            a b z = 0 := by
          rw [D.Rper_eq_R j
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b hz]
          have h0 : D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
              a b z = 0 := by
            by_contra hne
            have hmem : z ∈ Function.support (fun z : Idx → ℝ =>
                ((D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
                  a b z : ℝ) : ℂ)) := by
              simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hne
            have hb := support_R_subset_ball D
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) j a b hmem
            rw [Metric.mem_ball, dist_zero_right] at hb
            linarith
          rw [h0, Complex.ofReal_zero]
        have hΨ0 : Ψ a b z = 0 := by
          by_contra hne
          have hmem : z ∈ Function.support (Ψ a b) := hne
          have hb := hΨsupp a b hmem
          rw [Metric.mem_ball, dist_zero_right] at hb
          linarith
        have hpd0 : ∀ c d : Idx,
            Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z = 0 := by
          intro c d
          have hmem : z ∈ Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
            simpa [Set.mem_pi] using hz
          have hev0 : D.Rper j h a b =ᶠ[𝓝 z] (fun _ : Idx → ℝ => 0) := by
            filter_upwards [hopenCube.mem_nhds hmem,
              (isOpen_lt continuous_const continuous_norm).mem_nhds hlt] with y hy hy2
            rw [D.Rper_eq_R j h a b (by simpa [Set.mem_pi] using hy)]
            have h0 : D.R j h a b y = 0 := by
              by_contra hne
              have hmem' : y ∈ Function.support (fun z : Idx → ℝ =>
                  ((D.R j h a b z : ℝ) : ℂ)) := by
                simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hne
              have hb := support_R_subset_ball D h j a b hmem'
              rw [Metric.mem_ball, dist_zero_right] at hb
              linarith
            rw [h0, Complex.ofReal_zero]
          have hpd0' : Work.Diff.STE.pd d (D.Rper j h a b)
              =ᶠ[𝓝 z] (fun _ : Idx → ℝ => 0) := by
            filter_upwards [hev0.fderiv (𝕜 := ℝ)] with y hy
            simp only [Work.Diff.STE.pd]
            rw [hy]
            simp
          have hpd0'' : Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b))
              =ᶠ[𝓝 z] (fun _ : Idx → ℝ => 0) := by
            filter_upwards [hpd0'.fderiv (𝕜 := ℝ)] with y hy
            simp only [Work.Diff.STE.pd]
            rw [hy]
            simp
          simpa using hpd0''.eq_of_nhds
        have hsum0 : (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
            * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z) = 0 :=
          Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero
            (fun d _ => by rw [hpd0 c d, mul_zero]))
        rw [hLHS, hThself a b z hz, hΨ0, hsum0]
        simp
    -- extend from the open cube by `1`-periodicity and continuity
    intro z
    set z' : Idx → ℝ := fun i => Int.fract (z i + 1 / 2) - 1 / 2 with hz'def
    set m : Idx → ℤ := fun i => ⌊z i + 1 / 2⌋ with hmdef
    have hz'le : ∀ i, z' i ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2) := by
      intro i
      have h1 := Int.fract_nonneg (z i + 1 / 2)
      have h2 := Int.fract_lt_one (z i + 1 / 2)
      simp only [hz'def]
      exact ⟨by linarith, by linarith⟩
    have hshift : z = z' + Work.Diff.STE.iVec m := by
      funext i
      have h2 := Int.fract_add_floor (z i + 1 / 2)
      simp only [hz'def, hmdef]
      simp only [Work.Diff.STE.iVec_apply, Pi.add_apply]
      linarith
    have hz'z : F z' = F z := by
      rw [hshift, periodic1_add_iVec hperF]
    have htend : Tendsto (fun n : ℕ => (1 - 1 / (n + 1 : ℝ)) • z') atTop (𝓝 z') := by
      have h1 : Tendsto (fun n : ℕ => (1 - 1 / (n + 1 : ℝ))) atTop (𝓝 1) := by
        have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds.sub h2)
      simpa using h1.smul_const z'
    have hlim : Tendsto (fun n : ℕ => F ((1 - 1 / (n + 1 : ℝ)) • z')) atTop (𝓝 (F z')) :=
      hcontF.continuousAt.tendsto.comp htend
    have hcube' : ∀ n : ℕ, ∀ i, ((1 - 1 / (n + 1 : ℝ)) • z') i
        ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      intro n i
      have hden : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have hc0 : 0 ≤ 1 - 1 / (n + 1 : ℝ) := by
        have h2 : 1 / (n + 1 : ℝ) ≤ 1 := by
          rw [div_le_one hden]
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        linarith
      have hc2 : 1 - 1 / (n + 1 : ℝ) < 1 := by
        have h3 : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith
      have habs : |z' i| ≤ 1 / 2 := by
        have hh := hz'le i
        exact abs_le.mpr ⟨hh.1, by linarith [hh.2]⟩
      have hlt : |(1 - 1 / (n + 1 : ℝ)) * z' i| < 1 / 2 := by
        rw [abs_mul, abs_of_nonneg hc0]
        calc (1 - 1 / (n + 1 : ℝ)) * |z' i| ≤ (1 - 1 / (n + 1 : ℝ)) * (1 / 2) :=
              mul_le_mul_of_nonneg_left habs hc0
          _ < 1 * (1 / 2) := mul_lt_mul_of_pos_right hc2 (by norm_num)
          _ = 1 / 2 := by norm_num
      rw [Pi.smul_apply, smul_eq_mul]
      exact ⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩
    have hseq : ∀ n : ℕ, F ((1 - 1 / (n + 1 : ℝ)) • z') = 0 :=
      fun n => hFcube _ (hcube' n)
    have hzero : Tendsto (fun n : ℕ => F ((1 - 1 / (n + 1 : ℝ)) • z')) atTop (𝓝 0) := by
      have hc : (fun _ : ℕ => (0 : ℂ))
          = (fun n : ℕ => F ((1 - 1 / (n + 1 : ℝ)) • z')) := funext (fun n => (hseq n).symm)
      rw [← hc]
      exact tendsto_const_nhds
    have hFz' : F z' = 0 := (tendsto_nhds_unique hzero hlim).symm
    have hFz : F z = 0 := by rw [← hz'z]; exact hFz'
    have hfin := hFz
    simp only [hFdef] at hfin
    exact sub_eq_zero.mp hfin
  refine ⟨A, fun a b => gardPerC (Ψ a b), hAsym, hAell, hAsmA, hAper,
    (fun m hm β z c d => le_trans (hAjet m hm β z c d) hCAC), hThsm, hThper,
    (fun a b => le_trans (hThen a b) hXC), hId, ?_, ?_⟩
  · intro a b
    have h1 : Work.Diff.STE.ENormSq (k - 1) (D.Rper j
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        ≤ CL * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b)) :=
      le_trans (le_add_of_nonneg_right (ENormSq_nonneg_b _))
        (hLb h hsym hpos hsmooth hell hub hjet' j a b)
    have h2 : 0 ≤ 1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b) := by
      have := ENormSq_nonneg_b (n := Module.finrank ℝ E) (m := k + 1) (D.Rper j h a b)
      linarith
    exact le_trans h1 (mul_le_mul_of_nonneg_right hCLC h2)
  · intro a b
    have h1 : Work.Diff.STE.ENormSq 0 (D.Rper j
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        ≤ CL * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b)) :=
      le_trans (le_add_of_nonneg_left (ENormSq_nonneg_b _))
        (hLb h hsym hpos hsmooth hell hub hjet' j a b)
    have h2 : 0 ≤ 1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b) := by
      have := ENormSq_nonneg_b (n := Module.finrank ℝ E) (m := k + 1) (D.Rper j h a b)
      linarith
    exact le_trans h1 (mul_le_mul_of_nonneg_right hCLC h2)

end

end Work.Diff.STE.Lead.Gal
