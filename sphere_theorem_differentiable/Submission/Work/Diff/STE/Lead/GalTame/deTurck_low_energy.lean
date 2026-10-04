import Mathlib
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.ENormSq_basic
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.GalTame.core_estimate
import Submission.Work.Diff.STE.Lead.GalTame.ENormB_mono_level
import Submission.Work.Diff.STE.Lead.GalTame.Rper_sup_bound
import Submission.Work.Diff.STE.Lead.GalTame.sharpTrans
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.Lead.Gal.gardingAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The low-order energy of the DeTurck section

`Work.Diff.STE.Lead.GalTame.deTurck_low_energy`: the `H^{k-1}` and `L²` energies of the DeTurck
section `P h = deTurckSec h` are bounded by a constant (uniform in the section and in its pinching
constants `lam`, `K`) times `1 + ENormB (k+1) h`.

## Route

The tame transport datum `Work.Diff.STE.Lead.GalTame.sharpTrans` (used at level `k + 1`) supplies,
for every chart `j`, a smooth `1`-periodic coefficient family `A` with

* the pointwise bound `|A c d z| ≤ CA`, and
* `ENormSq 0 (∂^m A_{cd}) ≤ CA (1 + ENormB m h)` for every `m ≤ k + 1`,

together with a smooth `1`-periodic residual `Th` with

* `ENormSq 0 (∂^m Th_{ab}) ≤ CT (1 + ENormB (m+1) h)` for every `m ≤ k + 1`, and
* the *global* identity `Rper_j (P h)_{ab} = Σ_{cd} A_{cd} ∂_c∂_d (Rper_j h)_{ab} + Th_{ab}`.

Writing `w = Σ_{cd} A_{cd} ∂_c∂_d (Rper_j h)_{ab}` for the transport term, subadditivity of the
energy gives

`ENormSq m (Rper_j (P h)_{ab}) ≤ 2 ENormSq m w + 2 ENormSq m (Th_{ab})`.

For `m = k - 1` the transport term is bounded by `Work.Diff.STE.Lead.GalTame.core_estimate` at
level `k` (whose hypotheses are exactly the `H^{k+1}` energies of `A` and of the component
`Rper_j h a b`, plus the sup bounds), and for `m = 0` by `core_estimate` at level `1` (the `H²`
energies).  The residual is bounded directly by its clause, using the level-monotonicity
`ENormB_mono_level` of the energy (to replace `ENormB k` and `ENormB 1` by `ENormB (k+1)`).
Summing over the charts `j` and the frame indices `a b` finishes.
-/

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory BigOperators
open scoped ContDiff

noncomputable section

set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The norm of a real number seen in `ℂ` is its absolute value. -/
private lemma norm_ofReal_g (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

/-- The energy `ENormSq` is nonnegative. -/
private lemma ENormSq_nonneg_g {n : ℕ} (m : ℕ) (f : (Fin n → ℝ) → ℂ) :
    0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => integral_nonneg fun x => by positivity

/-- The physical energy `ENormB` is nonnegative. -/
private lemma ENormB_nonneg_g (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (m : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) : 0 ≤ D.ENormB m h := by
  rw [Work.Diff.STE.B3Data.ENormB]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => ENormSq_nonneg_g m _

/-- **Subadditivity of the energy under a sum of two smooth functions.** -/
private lemma ENormSq_add_le_g {n : ℕ} (m : ℕ) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.Diff.STE.ENormSq m (f + g)
      ≤ 2 * Work.Diff.STE.ENormSq m f + 2 * Work.Diff.STE.ENormSq m g := by
  classical
  rw [Work.Diff.STE.ENormSq, Work.Diff.STE.ENormSq, Work.Diff.STE.ENormSq, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun γ _ => ?_
  have hpd : Work.Diff.STE.pdVec m γ (f + g)
      = Work.Diff.STE.pdVec m γ f + Work.Diff.STE.pdVec m γ g :=
    Work.Diff.STE.flat.invJetSymm_pdVec_add m γ hf hg
  have hcontF : Continuous (Work.Diff.STE.pdVec m γ f) :=
    (Work.Diff.STE.flat.contDiff_pdVec_top hf γ).continuous
  have hcontG : Continuous (Work.Diff.STE.pdVec m γ g) :=
    (Work.Diff.STE.flat.contDiff_pdVec_top hg γ).continuous
  have hpt : ∀ x : Fin n → ℝ,
      ‖Work.Diff.STE.pdVec m γ f x + Work.Diff.STE.pdVec m γ g x‖ ^ 2
        ≤ 2 * ‖Work.Diff.STE.pdVec m γ f x‖ ^ 2
          + 2 * ‖Work.Diff.STE.pdVec m γ g x‖ ^ 2 := by
    intro x
    have h1 : ‖Work.Diff.STE.pdVec m γ f x + Work.Diff.STE.pdVec m γ g x‖
        ≤ ‖Work.Diff.STE.pdVec m γ f x‖ + ‖Work.Diff.STE.pdVec m γ g x‖ := norm_add_le _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg
      (Work.Diff.STE.pdVec m γ f x + Work.Diff.STE.pdVec m γ g x)) h1 2
    nlinarith [norm_nonneg (Work.Diff.STE.pdVec m γ f x),
      norm_nonneg (Work.Diff.STE.pdVec m γ g x), h2,
      sq_nonneg (‖Work.Diff.STE.pdVec m γ f x‖ - ‖Work.Diff.STE.pdVec m γ g x‖)]
  have hIntL : Integrable (fun x : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m γ f x + Work.Diff.STE.pdVec m γ g x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hcontF.add hcontG).norm.pow 2)
  have hIntR : Integrable (fun x : Fin n → ℝ =>
      2 * ‖Work.Diff.STE.pdVec m γ f x‖ ^ 2 + 2 * ‖Work.Diff.STE.pdVec m γ g x‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
        (continuous_const.mul (hcontF.norm.pow 2))).add
      (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
        (continuous_const.mul (hcontG.norm.pow 2)))
  rw [hpd]
  calc (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ‖Work.Diff.STE.pdVec m γ f x + Work.Diff.STE.pdVec m γ g x‖ ^ 2)
      ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          (2 * ‖Work.Diff.STE.pdVec m γ f x‖ ^ 2 + 2 * ‖Work.Diff.STE.pdVec m γ g x‖ ^ 2) :=
        integral_mono hIntL hIntR hpt
    _ = 2 * (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖Work.Diff.STE.pdVec m γ f x‖ ^ 2)
          + 2 * (∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖Work.Diff.STE.pdVec m γ g x‖ ^ 2) := by
        rw [integral_add
            (f := fun x : Fin n → ℝ => 2 * ‖Work.Diff.STE.pdVec m γ f x‖ ^ 2)
            (g := fun x : Fin n → ℝ => 2 * ‖Work.Diff.STE.pdVec m γ g x‖ ^ 2)
            (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
              (continuous_const.mul (hcontF.norm.pow 2)))
            (Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
              (continuous_const.mul (hcontG.norm.pow 2))),
          integral_const_mul, integral_const_mul]

/-- A triple sum of a constant over the chart and frame indices. -/
private lemma sum3_const_g {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ℝ) :
    (∑ _ : ι, ∑ _ : κ, ∑ _ : κ, c)
      = (Fintype.card ι : ℝ) * (Fintype.card κ : ℝ) * (Fintype.card κ : ℝ) * c := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The energy of one periodised component is dominated by the physical energy of the section. -/
private lemma ENormSq_Rper_le_ENormB_g (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (m : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.ENormSq m (D.Rper i h a b) ≤ D.ENormB m h := by
  rw [Work.Diff.STE.B3Data.ENormB]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun i : ι₀ => ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h a' b'))
    (fun i _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ =>
      ENormSq_nonneg_g m _)
    (Finset.mem_univ i))
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun a' : Fin (Module.finrank ℝ E) => ∑ b' : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h a' b'))
    (fun a' _ => Finset.sum_nonneg fun b' _ => ENormSq_nonneg_g m _)
    (Finset.mem_univ a))
  exact Finset.single_le_sum
    (f := fun b' : Fin (Module.finrank ℝ E) => Work.Diff.STE.ENormSq m (D.Rper i h a b'))
    (fun b' _ => ENormSq_nonneg_g m _) (Finset.mem_univ b)

theorem deTurck_low_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k)
    (hk2 : Module.finrank ℝ E + 4 ≤ k) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
            |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
          D.ENormB (k - 1)
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
            + D.ENormB 0
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
          ≤ C * (1 + D.ENormB (k + 1) h) := by
  intro lam K hlam hK
  classical
  by_cases hn0 : Module.finrank ℝ E = 0
  · -- degenerate case: the frame index type is empty
    refine ⟨1, zero_le_one, ?_⟩
    intro h hsym hpos hsmooth hell hub hjet
    have hz : ∀ m : ℕ, D.ENormB m
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) = 0 := by
      intro m
      rw [Work.Diff.STE.B3Data.ENormB]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ =>
        Finset.sum_eq_zero fun b _ => ?_
      exact Fin.elim0 (hn0 ▸ a)
    rw [hz (k - 1), hz 0]
    have h1 : (0 : ℝ) ≤ 1 + D.ENormB (k + 1) h := by
      have := ENormB_nonneg_g D (k + 1) h; linarith
    linarith
  · have hK0 : 0 ≤ K := le_of_lt hK
    obtain ⟨U0, hU00, hU0b⟩ := Rper_sup_bound (I := I) (M := M) D
    obtain ⟨CMono, hCMono0, hCMono⟩ := ENormB_mono_level (I := I) (M := M) D (k + 1)
    obtain ⟨Ck, hCk0, hCkb⟩ := core_estimate (ι := Fin (Module.finrank ℝ E)) k hk
    obtain ⟨C1, hC10, hC1b⟩ := core_estimate (ι := Fin (Module.finrank ℝ E)) 1 (le_refl 1)
    obtain ⟨lam', CA, CT, hlam'0, hCA0, hCT0, hS⟩ :=
      sharpTrans (I := I) (M := M) D hLC (k + 1) (by omega) lam K hlam hK
    -- ### the constants (all uniform in the section `h`)
    set G : ℝ := U0 * (K + 1) with hGdef
    have hG0 : 0 ≤ G := by
      rw [hGdef]
      have : (0 : ℝ) ≤ K + 1 := by linarith
      positivity
    set nK : ℝ := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) with hnKdef
    set KI : ℝ := (Fintype.card ι₀ : ℝ) with hKIdef
    set ck1 : ℝ := (Fintype.card (Fin (k + 1) → Fin (Module.finrank ℝ E)) : ℝ) with hck1def
    set ckm1 : ℝ := (Fintype.card (Fin (k - 1) → Fin (Module.finrank ℝ E)) : ℝ) with hckm1def
    set c2 : ℝ := (Fintype.card (Fin 2 → Fin (Module.finrank ℝ E)) : ℝ) with hc2def
    have hck10 : 0 ≤ ck1 := by rw [hck1def]; positivity
    have hckm10 : 0 ≤ ckm1 := by rw [hckm1def]; positivity
    have hc20 : 0 ≤ c2 := by rw [hc2def]; positivity
    have hKI0 : 0 ≤ KI := by rw [hKIdef]; positivity
    have hnK0 : 0 ≤ nK := by rw [hnKdef]; positivity
    clear_value G
    clear_value nK
    clear_value KI
    clear_value ck1
    clear_value ckm1
    clear_value c2
    set CkA : ℝ := Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + ck1 * CA) with hCkAdef
    set C10 : ℝ := C1 * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + c2 * CA) * (1 + CMono)
      with hC10def
    set BT : ℝ := (ckm1 + 1) * CT * (1 + CMono) with hBTdef
    have hCkA0 : 0 ≤ CkA := by rw [hCkAdef]; positivity
    have hC100 : 0 ≤ C10 := by rw [hC10def]; positivity
    have hBT0 : 0 ≤ BT := by rw [hBTdef]; positivity
    set K1 : ℝ := 2 * CkA + 2 * BT + 1 with hK1def
    set K0 : ℝ := 2 * C10 + 2 * BT + 1 with hK0def
    have hK10 : 0 ≤ K1 := by rw [hK1def]; positivity
    have hK00 : 0 ≤ K0 := by rw [hK0def]; positivity
    clear_value CkA
    clear_value C10
    clear_value BT
    clear_value K1
    clear_value K0
    refine ⟨KI * nK * nK * (K1 + K0) + 1, ?_, ?_⟩
    · have h1 : 0 ≤ KI * nK * nK * (K1 + K0) := by positivity
      linarith
    · intro h hsym hpos hsmooth hell hub hjet
      set P : Work.Diff.STE.Bil (I := I) (M := M) :=
        Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth with hPdef
      set E1 : ℝ := D.ENormB (k + 1) h with hE1def
      clear_value E1
      have hE10 : 0 ≤ E1 := by rw [hE1def]; exact ENormB_nonneg_g D (k + 1) h
      -- ### the per-component estimate
      have hcomp : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          (Work.Diff.STE.ENormSq (k - 1) (D.Rper i
              (P) a b)
            ≤ K1 * (1 + E1))
          ∧ (Work.Diff.STE.ENormSq 0 (D.Rper i
              (P) a b)
            ≤ K0 * (1 + E1)) := by
        intro i a b
        obtain ⟨A, Th, hAsym, hAell, hAsm, hAper, hAb, hAd, hAen, hThsm, hThper, hThen, hid⟩ :=
          hS h hsym hpos hsmooth hell hub hjet i
        obtain ⟨hua, hup⟩ :=
          Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D h hsmooth i a b
        have hUbound : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖D.Rper i h a b z‖ ≤ G := by
          intro z
          rw [hGdef]
          exact hU0b h lam K hlam hK0 hsym hell hub i a b z
        -- the complexified coefficient
        set Ac : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun c d z => ((A c d z : ℝ) : ℂ) with hAcdef
        have hAcsm : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (Ac c d) := by
          intro c d
          rw [hAcdef]
          exact Complex.ofRealCLM.contDiff.comp (hAsm c d)
        have hAcper : ∀ c d, Work.Diff.STE.Periodic1 (Ac c d) := by
          intro c d
          rw [hAcdef]
          exact Work.Diff.STE.Lead.Gal.periodic1_ofReal (hAper c d)
        have hAcb : ∀ c d z, ‖Ac c d z‖ ≤ CA := by
          intro c d z
          rw [hAcdef, norm_ofReal_g]
          exact hAb z c d
        -- the transport term
        have hWsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
            Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z) := by
          refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
          exact (hAcsm c d).mul (Work.Diff.STE.flat.contDiff_pdList_top hua [c, d])
        have hidfun : D.Rper i
            (P) a b
            = (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
                Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z)
              + Th a b := by
          funext z
          simpa only [Pi.add_apply, hAcdef] using hid a b z
        -- ### the `H^{k+1}` energy of the coefficient
        set KA : ℝ := ck1 * CA * (1 + E1) with hKAdef
        have hKA0 : 0 ≤ KA := by rw [hKAdef]; positivity
        clear_value KA
        have hEf : ∀ c d, Work.Diff.STE.ENormSq (k + 1) (Ac c d) ≤ KA := by
          intro c d
          rw [Work.Diff.STE.ENormSq]
          have h1 : (∑ β : Fin (k + 1) → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec (k + 1) β (Ac c d) x‖ ^ 2)
              ≤ ∑ _β : Fin (k + 1) → Fin (Module.finrank ℝ E), CA * (1 + E1) :=
            Finset.sum_le_sum fun β _ => by
              rw [← Work.Diff.STE.B3.ENormSq_zero_eq, hE1def]
              exact hAen (k + 1) le_rfl β c d
          have h2 : (∑ _β : Fin (k + 1) → Fin (Module.finrank ℝ E), CA * (1 + E1)) = KA := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hKAdef, hck1def]
            ring
          exact h1.trans (le_of_eq h2)
        -- ### the residuals
        have hThk : Work.Diff.STE.ENormSq (k - 1) (Th a b)
            ≤ ckm1 * (CT * (1 + CMono * E1)) := by
          have hsingle : ∀ β : Fin (k - 1) → Fin (Module.finrank ℝ E),
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (k - 1) β (Th a b))
                ≤ CT * (1 + CMono * E1) := by
            intro β
            have h1 := hThen (k - 1) (by omega) β a b
            have hkB : k - 1 + 1 = k := by omega
            rw [hkB] at h1
            have h2 : D.ENormB k h ≤ CMono * E1 := by
              rw [hE1def]
              exact hCMono h hsmooth k hk (by omega)
            exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) hCT0)
          rw [Work.Diff.STE.ENormSq]
          have h1 : (∑ β : Fin (k - 1) → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec (k - 1) β (Th a b) x‖ ^ 2)
              ≤ ∑ _β : Fin (k - 1) → Fin (Module.finrank ℝ E),
                  CT * (1 + CMono * E1) :=
            Finset.sum_le_sum fun β _ => by
              rw [← Work.Diff.STE.B3.ENormSq_zero_eq]
              exact hsingle β
          have h2 : (∑ _β : Fin (k - 1) → Fin (Module.finrank ℝ E),
                CT * (1 + CMono * E1)) = ckm1 * (CT * (1 + CMono * E1)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hckm1def]
          exact h1.trans (le_of_eq h2)
        have hTh0 : Work.Diff.STE.ENormSq 0 (Th a b) ≤ BT * (1 + E1) := by
          have h1 := hThen 0 (by omega) (fun j : Fin 0 => j.elim0) a b
          rw [Work.Diff.STE.B3.pdVec_zero_apply] at h1
          have h2 : D.ENormB 1 h ≤ CMono * E1 := by
            rw [hE1def]
            exact hCMono h hsmooth 1 (by norm_num) (by omega)
          have h3 : CT * (1 + CMono * E1) ≤ BT * (1 + E1) := by
            rw [hBTdef]
            have h6 : 0 ≤ 1 + E1 := by linarith
            have h4 : CT * (1 + CMono * E1) ≤ CT * (1 + CMono) * (1 + E1) := by
              have h5 : (1 + CMono * E1) ≤ (1 + CMono) * (1 + E1) := by
                nlinarith [hCMono0, hE10]
              calc CT * (1 + CMono * E1) = CT * (1 + CMono * E1) := rfl
                _ ≤ CT * ((1 + CMono) * (1 + E1)) :=
                    mul_le_mul_of_nonneg_left h5 hCT0
                _ = CT * (1 + CMono) * (1 + E1) := by ring
            have h7 : CT * (1 + CMono) * (1 + E1)
                ≤ (ckm1 + 1) * CT * (1 + CMono) * (1 + E1) := by
              have h8 : 0 ≤ CT * (1 + CMono) * (1 + E1) := by positivity
              nlinarith [hckm10, h8]
            linarith [h4, h7]
          calc Work.Diff.STE.ENormSq 0 (Th a b) ≤ CT * (1 + D.ENormB 1 h) := h1
            _ ≤ CT * (1 + CMono * E1) := by
                exact mul_le_mul_of_nonneg_left (by linarith) hCT0
            _ ≤ BT * (1 + E1) := h3
        -- ### the transport term at level `k - 1`
        have hWk : Work.Diff.STE.ENormSq (k - 1)
            (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
              Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z)
            ≤ Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA + E1) :=
          hCkb Ac (D.Rper i h a b) CA G KA E1 hAcsm hAcper hua hup hCA0 hG0 hKA0 hE10
            hAcb hUbound hEf (by rw [hE1def]; exact ENormSq_Rper_le_ENormB_g D (k + 1) h i a b)
        -- ### the transport term at level `0`
        set KA2 : ℝ := c2 * CA * (1 + CMono * E1) with hKA2def
        have hKA20 : 0 ≤ KA2 := by rw [hKA2def]; positivity
        clear_value KA2
        have hCM2 : D.ENormB 2 h ≤ CMono * E1 := by
          rw [hE1def]
          exact hCMono h hsmooth 2 (by norm_num) (by omega)
        have hU2 : Work.Diff.STE.ENormSq 2 (D.Rper i h a b) ≤ CMono * E1 :=
          (ENormSq_Rper_le_ENormB_g D 2 h i a b).trans hCM2
        have hEf2 : ∀ c d, Work.Diff.STE.ENormSq 2 (Ac c d) ≤ KA2 := by
          intro c d
          rw [Work.Diff.STE.ENormSq]
          have h2 : D.ENormB 2 h ≤ CMono * E1 := by
            rw [hE1def]
            exact hCMono h hsmooth 2 (by norm_num) (by omega)
          have h1 : (∑ β : Fin 2 → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec 2 β (Ac c d) x‖ ^ 2)
              ≤ ∑ _β : Fin 2 → Fin (Module.finrank ℝ E), CA * (1 + CMono * E1) :=
            Finset.sum_le_sum fun β _ => by
              rw [← Work.Diff.STE.B3.ENormSq_zero_eq]
              exact (hAen 2 (by omega) β c d).trans
                (mul_le_mul_of_nonneg_left (by linarith) hCA0)
          have h3 : (∑ _β : Fin 2 → Fin (Module.finrank ℝ E), CA * (1 + CMono * E1)) = KA2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hKA2def, hc2def]
            ring
          exact h1.trans (le_of_eq h3)
        have hW0 : Work.Diff.STE.ENormSq 0
            (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
              Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z)
            ≤ C1 * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA2 + CMono * E1) :=
          hC1b Ac (D.Rper i h a b) CA G KA2 (CMono * E1) hAcsm hAcper hua hup hCA0 hG0
            hKA20 (by positivity) hAcb hUbound hEf2 hU2
        constructor
        · -- ### the `H^{k-1}` energy
          have hdec : Work.Diff.STE.ENormSq (k - 1) (D.Rper i
                (P) a b)
              ≤ 2 * Work.Diff.STE.ENormSq (k - 1) (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
                    Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z)
                + 2 * Work.Diff.STE.ENormSq (k - 1) (Th a b) := by
            rw [hidfun]
            exact ENormSq_add_le_g (k - 1) hWsm (hThsm a b)
          have hstepA : Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA + E1) ≤ CkA * (1 + E1) := by
            rw [hCkAdef]
            have h0 : 0 ≤ Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 := by positivity
            have h1 : 1 + KA + E1 ≤ (1 + ck1 * CA) * (1 + E1) := by
              rw [hKAdef]; nlinarith [hCA0, hE10, hck10]
            calc Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA + E1)
                ≤ Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 * ((1 + ck1 * CA) * (1 + E1)) :=
                  mul_le_mul_of_nonneg_left h1 h0
              _ = Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + ck1 * CA) * (1 + E1) := by ring
          have hstepB : ckm1 * (CT * (1 + CMono * E1)) ≤ BT * (1 + E1) := by
            rw [hBTdef]
            have h1 : (1 + CMono * E1) ≤ (1 + CMono) * (1 + E1) := by
              rw [show (1 + CMono) * (1 + E1) = 1 + CMono + E1 + CMono * E1 from by ring]
              linarith [hCMono0, hE10]
            calc ckm1 * (CT * (1 + CMono * E1))
                ≤ ckm1 * (CT * ((1 + CMono) * (1 + E1))) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hCT0) hckm10
              _ = (ckm1 * CT * (1 + CMono)) * (1 + E1) := by ring
              _ ≤ ((ckm1 + 1) * CT * (1 + CMono)) * (1 + E1) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by linarith)
                  have h2 : 0 ≤ CT * (1 + CMono) := by positivity
                  nlinarith [hckm10, hCT0, hCMono0]
          calc Work.Diff.STE.ENormSq (k - 1) (D.Rper i
                (P) a b)
              ≤ 2 * Work.Diff.STE.ENormSq (k - 1) (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
                    Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z)
                + 2 * Work.Diff.STE.ENormSq (k - 1) (Th a b) := hdec
            _ ≤ 2 * (Ck * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA + E1))
                + 2 * (ckm1 * (CT * (1 + CMono * E1))) := by
                exact add_le_add (mul_le_mul_of_nonneg_left hWk (by norm_num))
                  (mul_le_mul_of_nonneg_left hThk (by norm_num))
            _ ≤ K1 * (1 + E1) := by
                rw [hK1def]
                linarith [hstepA, hstepB, hE10]
        · -- ### the `L²` energy
          have hdec : Work.Diff.STE.ENormSq 0 (D.Rper i
                (P) a b)
              ≤ 2 * Work.Diff.STE.ENormSq 0 (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
                    Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z)
                + 2 * Work.Diff.STE.ENormSq 0 (Th a b) := by
            rw [hidfun]
            exact ENormSq_add_le_g 0 hWsm (hThsm a b)
          have hstepA : C1 * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA2 + CMono * E1)
              ≤ C10 * (1 + E1) := by
            rw [hC10def]
            have h0 : 0 ≤ C1 * (1 + CA) ^ 2 * (1 + G) ^ 2 := by positivity
            have h1 : 1 + KA2 + CMono * E1 ≤ (1 + c2 * CA) * (1 + CMono) * (1 + E1) := by
              rw [hKA2def]
              nlinarith [hCA0, hE10, hCMono0, hc20, mul_nonneg hc20 hCA0,
                mul_nonneg hCMono0 hE10]
            calc C1 * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA2 + CMono * E1)
                ≤ C1 * (1 + CA) ^ 2 * (1 + G) ^ 2
                    * ((1 + c2 * CA) * (1 + CMono) * (1 + E1)) :=
                  mul_le_mul_of_nonneg_left h1 h0
              _ = C1 * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + c2 * CA) * (1 + CMono)
                    * (1 + E1) := by ring
          have hstepB : CT * (1 + CMono * E1) ≤ BT * (1 + E1) := by
            rw [hBTdef]
            calc CT * (1 + CMono * E1) ≤ CT * ((1 + CMono) * (1 + E1)) :=
                  mul_le_mul_of_nonneg_left (by rw [show (1 + CMono) * (1 + E1) = 1 + CMono + E1 + CMono * E1 from by ring]; linarith [hCMono0, hE10]) hCT0
              _ = CT * (1 + CMono) * (1 + E1) := by ring
              _ ≤ ((ckm1 + 1) * CT * (1 + CMono)) * (1 + E1) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by linarith)
                  have h2 : 0 ≤ CT * (1 + CMono) := by positivity
                  nlinarith [hckm10, hCT0, hCMono0]
          calc Work.Diff.STE.ENormSq 0 (D.Rper i
                (P) a b)
              ≤ 2 * Work.Diff.STE.ENormSq 0 (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
                    Ac c d z * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) z)
                + 2 * Work.Diff.STE.ENormSq 0 (Th a b) := hdec
            _ ≤ 2 * (C1 * (1 + CA) ^ 2 * (1 + G) ^ 2 * (1 + KA2 + CMono * E1))
                + 2 * (BT * (1 + E1)) := by
                refine add_le_add (mul_le_mul_of_nonneg_left hW0 (by norm_num)) ?_
                linarith [hTh0]
            _ ≤ K0 * (1 + E1) := by
                rw [hK0def]
                linarith [hstepA, hE10]
      -- ### summing over the charts and the frame indices
      have hsum1 : D.ENormB (k - 1)
          (P)
          ≤ KI * nK * nK * K1 * (1 + E1) := by
        rw [Work.Diff.STE.B3Data.ENormB]
        calc (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq (k - 1)
              (D.Rper i (P) a b))
            ≤ ∑ _i : ι₀, ∑ _a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E), K1 * (1 + E1) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
                Finset.sum_le_sum fun b _ => (hcomp i a b).1
          _ = KI * nK * nK * (K1 * (1 + E1)) := by
              rw [sum3_const_g, hKIdef, hnKdef]
          _ = KI * nK * nK * K1 * (1 + E1) := by ring
      have hsum0 : D.ENormB 0
          (P)
          ≤ KI * nK * nK * K0 * (1 + E1) := by
        rw [Work.Diff.STE.B3Data.ENormB]
        calc (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq 0
              (D.Rper i (P) a b))
            ≤ ∑ _i : ι₀, ∑ _a : Fin (Module.finrank ℝ E), ∑ _b : Fin (Module.finrank ℝ E), K0 * (1 + E1) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
                Finset.sum_le_sum fun b _ => (hcomp i a b).2
          _ = KI * nK * nK * (K0 * (1 + E1)) := by
              rw [sum3_const_g, hKIdef, hnKdef]
          _ = KI * nK * nK * K0 * (1 + E1) := by ring
      calc D.ENormB (k - 1) (P)
            + D.ENormB 0 (P)
          ≤ KI * nK * nK * K1 * (1 + E1) + KI * nK * nK * K0 * (1 + E1) :=
            add_le_add hsum1 hsum0
        _ = KI * nK * nK * (K1 + K0) * (1 + E1) := by ring
        _ ≤ (KI * nK * nK * (K1 + K0) + 1) * (1 + E1) := by
            have h1 : 0 ≤ KI * nK * nK * (K1 + K0) := by positivity
            have h2 : 0 ≤ 1 + E1 := by linarith
            nlinarith [h1, h2]

end

end Work.Diff.STE.Lead.GalTame
