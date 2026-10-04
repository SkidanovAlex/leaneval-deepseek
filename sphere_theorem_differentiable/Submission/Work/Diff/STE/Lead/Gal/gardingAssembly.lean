import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.GardDef
import Submission.Work.Diff.STE.Lead.Gal.gardTransport_holds
import Submission.Work.Diff.STE.Lead.Gal.gardJet_holds
import Submission.Work.Diff.STE.Lead.Gal.pdVec_gard_defect_bound
import Submission.Work.Diff.STE.garding_vec_uniform
import Submission.Work.Diff.STE.ENormSq_pairing_le
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.densGood_noT2
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.fourierCoeff_iterate_pd
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.fourierCoeff_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000

/-!
# The Gårding assembly for the DeTurck operator on the Layer B3 components

This module proves `Work.Diff.STE.Lead.Gal.gardingAssembly`: the level-`k` dissipation estimate
for the DeTurck operator, in the localised component picture of Layer B3.

The proof is split into two independent halves:

* **the geometry** (`Work.Diff.STE.Lead.Gal.gardTransport_holds`): in each chart and component,
  `Rper j (P h) a b = Σ_{cd} A_{cd} ∂_c∂_d (Rper j h a b) + Th` with an elliptic periodic
  coefficient `A` and a bounded lower-order term `Th` (`Work.Diff.STE.Lead.Gal.GardData`);
* **the analysis** (this file): the Gårding dissipation (`garding_vec_uniform`), the Leibniz
  defect bound (`pdVec_gard_defect_bound`) and the Cauchy–Schwarz bound, together with the static
  jet bound (`gardJet_holds`).

Since every one of these bounds is uniform in `h`, the two target inequalities are obtained by
absorbing the (bounded) dissipative term into the constant.

## Structure of this file

* the two targets are proved from the auxiliary `gardingAssembly_aux`, which takes the three
  analytic inputs as *explicit hypotheses* (`hJet`, `hTrans`, `hDef`) — so it is axiom-clean and
  reusable with any other proof of the same three statements;
* `Work.Diff.STE.Lead.Gal.GardData` (in `GardDef.lean`) is the transport interface: it is the only
  genuinely hard input, and the auxiliary `Work.Diff.STE.Lead.Gal.gardTransport_holds` (in flight,
  see also `Work.Diff.STE.Lead.Gal.gardTransport_holdsB`) is the only gap;
* an *independent* route to `GardData` is being built in `Work.Diff.STE.B3` (the modules
  `TransportDefs`, `transport_exists_A_uniform`, `transport_low_jet_bound`, ...): with
  `Work.Diff.STE.B3.transport_exists_A_uniform` (the elliptic coefficient, matching
  `(Gf)⁻¹` on the ball), `Work.Diff.STE.B3.transport_low_jet_bound` (the jet bounds of
  `residualLow`) and `Work.Diff.STE.B3.Rres_eq_residualLow` (the identity
  `Rres ((Gf)⁻¹) = residualLow`), one proves `GardData` by taking the coefficient
  `A := (Gf)⁻¹`, the lower-order term `Th a b := Rper j (P h) a b − Σ A ∂∂(Rper j h a b)`
  (the identity is then `rfl`; `Th = residualLow` holds on the `σ j`-ball, which contains its
  support) and bounding the two `ENormSq`'s by the pointwise bounds.
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

/-! ## Elementary integral and periodicity helpers -/

/-- The volume of the unit cube `(0,1]^ι` is `1`. -/
lemma volume_unitCube_toReal {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (MeasureTheory.volume (Work.Diff.STE.unitCube (ι := ι))).toReal = 1 := by
  rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
  simp

/-- The integral over the unit cube of the square of the norm of a continuous function that is
pointwise bounded by `C` is at most `C ^ 2`. -/
lemma integral_normSq_le {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ} {C : ℝ}
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

/-- `√x ≤ 1 + x` for `x ≥ 0`. -/
lemma sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have hb : (0 : ℝ) ≤ 1 + x := by linarith
  rw [Real.sqrt_le_iff]
  exact ⟨hb, by nlinarith⟩

/-- The arithmetic–geometric mean inequality for square roots. -/
lemma sqrt_mul_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  have h1 : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb] at h1
  nlinarith

/-- The energy of a continuous function whose `m`-th derivatives are pointwise bounded by `C`. -/
lemma ENormSq_le_of_sup_bound {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {C : ℝ}
    (hc : ∀ l : Fin m → Fin n, Continuous (Work.Diff.STE.pdVec m l f))
    (hb : ∀ (l : Fin m → Fin n) (z : Fin n → ℝ), ‖Work.Diff.STE.pdVec m l f z‖ ≤ C) :
    Work.Diff.STE.ENormSq m f ≤ (Fintype.card (Fin m → Fin n) : ℝ) * C ^ 2 := by
  have hterm : ∀ l : Fin m → Fin n,
      ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l f z‖ ^ 2 ≤ C ^ 2 :=
    fun l => integral_normSq_le (hc l) (hb l)
  rw [Work.Diff.STE.ENormSq]
  calc ∑ l : Fin m → Fin n,
        ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m l f z‖ ^ 2
      ≤ ∑ _l : Fin m → Fin n, C ^ 2 := Finset.sum_le_sum (fun l _ => hterm l)
    _ = (Fintype.card (Fin m → Fin n) : ℝ) * C ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma ENormSq_nonneg {n m : ℕ} (f : (Fin n → ℝ) → ℂ) :
    0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-! ## Periodicity and smoothness helpers -/

lemma periodic1_add {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (f + g) := fun i x => by
  simp only [Pi.add_apply, hf i x, hg i x]

lemma periodic1_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (hg : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (f * g) := fun i x => by
  simp only [Pi.mul_apply, hf i x, hg i x]

lemma periodic1_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} (s : Finset α)
    (f : α → (ι → ℝ) → ℂ) (hf : ∀ a ∈ s, Work.Diff.STE.Periodic1 (f a)) :
    Work.Diff.STE.Periodic1 (fun x => ∑ a ∈ s, f a x) := fun i x => by
  exact Finset.sum_congr rfl (fun a ha => hf a ha i x)

/-- The complexification of a periodic real function is periodic. -/
lemma periodic1_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : Work.Diff.STE.Periodic1 f) :
    Work.Diff.STE.Periodic1 (fun z => ((f z : ℝ) : ℂ)) := fun i x => by
  simp only [hf i x]

/-- The partial derivative of a smooth periodic function is periodic. -/
lemma periodic1_pd_ga {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hf : Work.Diff.STE.Periodic1 f) (hsm : ContDiff ℝ (⊤ : ENat) f) (j : ι) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.pd j f) :=
  fun i => Work.Diff.STE.periodicIn_pd_of_differentiable i j (hsm.differentiable (by simp)) (hf i)

/-- The iterated partial derivative of a smooth function is smooth. -/
lemma contDiff_pdList {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hsm : ContDiff ℝ (⊤ : ENat) f) (L : List ι) :
    ContDiff ℝ (⊤ : ENat) (Work.Diff.STE.pdList L f) := by
  induction L with
  | nil => simpa only [Work.Diff.STE.pdList, List.foldr_nil] using hsm
  | cons a t ih =>
      rw [Work.Diff.STE.pdList, List.foldr_cons]
      exact Work.Diff.STE.contDiff_pd_of_contDiff_top ih

lemma contDiff_pdVec {n m : ℕ} {f : (Fin n → ℝ) → ℂ} (hsm : ContDiff ℝ (⊤ : ENat) f)
    (l : Fin m → Fin n) :
    ContDiff ℝ (⊤ : ENat) (Work.Diff.STE.pdVec m l f) :=
  contDiff_pdList hsm (List.ofFn l)

/-- The second partial derivative of a smooth function is smooth. -/
lemma contDiff_pd_pd {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℂ}
    (hsm : ContDiff ℝ (⊤ : ENat) f) (j i : ι) :
    ContDiff ℝ (⊤ : ENat) (Work.Diff.STE.pd i (Work.Diff.STE.pd j f)) :=
  Work.Diff.STE.contDiff_pd_of_contDiff_top (i := i)
    (Work.Diff.STE.contDiff_pd_of_contDiff_top (i := j) hsm)

lemma contDiff_ofReal_comp {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ENat) f) :
    ContDiff ℝ (⊤ : ENat) (fun z => ((f z : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-! ## The per-component Gårding estimate -/

/-- **The level-`k` pairing of one DeTurck component.**  Given the decomposition
`v = Σ_{cd} A_{cd} ∂_c∂_d u + Th`, the Gårding dissipation `hg` of the principal part and the
Leibniz defect bound `hdef`, the level-`k` pairing of `v` against `u` is bounded by the dissipation
plus a multiple of `1 + ENormSq k u`. -/
lemma component_garding_bound {n : ℕ} (k : ℕ)
    (A : Fin n → Fin n → (Fin n → ℝ) → ℝ) (Th u v : (Fin n → ℝ) → ℂ)
    (lamT CT F Cd Q : ℝ)
    (hsmA : ∀ c d, ContDiff ℝ (⊤ : ENat) (A c d))
    (hperA : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
    (hCT0 : 0 ≤ CT)
    (hsmT : ContDiff ℝ (⊤ : ENat) Th)
    (hperT : Work.Diff.STE.Periodic1 Th)
    (henT : Work.Diff.STE.ENormSq k Th ≤ CT)
    (hid : ∀ z, v z =
      (∑ c, ∑ d, ((A c d z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z) + Th z)
    (hsmu : ContDiff ℝ (⊤ : ENat) u) (hperu : Work.Diff.STE.Periodic1 u)
    (hQ0 : 0 ≤ Q)
    (hF0 : 0 ≤ F)
    (hg : (∑ l : Fin k → Fin n,
        Work.Diff.STE.L2re
          (fun z => ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
            * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
          (Work.Diff.STE.pdVec k l u))
        ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u + F * Work.Diff.STE.ENormSq k u)
    (hCd0 : 0 ≤ Cd)
    (hdef : ∀ (l : Fin k → Fin n) (z : Fin n → ℝ),
        ‖Work.Diff.STE.pdVec k l
            (fun y => ∑ c, ∑ d, ((A c d y : ℝ) : ℂ)
              * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
          - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
              * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)‖
          ≤ Cd * (1 + CT) * (1 + Q)) :
    (∑ l : Fin k → Fin n,
        Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u))
      ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u
        + (F + Cd * (1 + CT) * (1 + Q) * ((Fintype.card (Fin k → Fin n) : ℝ) + 1)
            + (CT + 1)) * (1 + Work.Diff.STE.ENormSq k u) := by
  classical
  set w : (Fin n → ℝ) → ℂ :=
    fun y => ∑ c, ∑ d, ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y with hw
  set FL : (Fin k → Fin n) → (Fin n → ℝ) → ℂ := fun l z => ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
      * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z with hFL
  have hws : ContDiff ℝ (⊤ : ENat) w := by
    rw [hw]
    refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
    exact (contDiff_ofReal_comp (hsmA c d)).mul (contDiff_pd_pd hsmu d c)
  have hwper : Work.Diff.STE.Periodic1 w := by
    rw [hw]
    refine periodic1_sum Finset.univ _ fun c _ => ?_
    refine periodic1_sum Finset.univ _ fun d _ => ?_
    exact periodic1_mul (periodic1_ofReal (hperA c d))
      (periodic1_pd_ga (periodic1_pd_ga hperu hsmu d)
        (Work.Diff.STE.contDiff_pd_of_contDiff_top (i := d) hsmu) c)
  have hv_eq : v = w + Th := by
    rw [hw]
    funext z
    simpa only [Pi.add_apply] using hid z
  have hcw : ∀ l : Fin k → Fin n, Continuous (Work.Diff.STE.pdVec k l w) :=
    fun l => (contDiff_pdVec hws l).continuous
  have hcF : ∀ l : Fin k → Fin n, Continuous (FL l) := by
    intro l
    rw [hFL]
    refine continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
    exact ((contDiff_ofReal_comp (hsmA c d)).continuous).mul
      ((contDiff_pd_pd (contDiff_pdVec hsmu l) d c).continuous)
  have hcT : ∀ l : Fin k → Fin n, Continuous (Work.Diff.STE.pdVec k l Th) :=
    fun l => (contDiff_pdVec hsmT l).continuous
  have hcu : ∀ l : Fin k → Fin n, Continuous (Work.Diff.STE.pdVec k l u) :=
    fun l => (contDiff_pdVec hsmu l).continuous
  -- ### the per-`l` decomposition
  have hstep : ∀ l : Fin k → Fin n,
      Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u)
        ≤ Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u)
          + |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
              (Work.Diff.STE.pdVec k l u)|
          + |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)| := by
    intro l
    have h1 : Work.Diff.STE.pdVec k l v = Work.Diff.STE.pdVec k l (w + Th) := by rw [hv_eq]
    have h2 : Work.Diff.STE.pdVec k l (w + Th)
        = Work.Diff.STE.pdVec k l w + Work.Diff.STE.pdVec k l Th := by
      rw [Work.Diff.STE.pdVec]
      exact Work.Diff.STE.flat.pdList_add (List.ofFn l) hws hsmT
    have h3 : Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u)
        = Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l w) (Work.Diff.STE.pdVec k l u)
          + Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u) := by
      rw [h1, h2]
      exact Work.Diff.STE.cm_L2re_add _ _ _ (hcw l) (hcT l) (hcu l)
    have h4 : Work.Diff.STE.pdVec k l w
        = FL l + (Work.Diff.STE.pdVec k l w - FL l) := by
      funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring
    have h5 : Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l w) (Work.Diff.STE.pdVec k l u)
        = Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u)
          + Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
              (Work.Diff.STE.pdVec k l u) := by
      conv_lhs => rw [h4]
      exact Work.Diff.STE.cm_L2re_add _ _ _ (hcF l) ((hcw l).sub (hcF l)) (hcu l)
    rw [h3, h5]
    have a := le_abs_self (Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
      (Work.Diff.STE.pdVec k l u))
    have b := le_abs_self (Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th)
      (Work.Diff.STE.pdVec k l u))
    linarith
  -- ### the defect sum
  have hCdn : 0 ≤ Cd * (1 + CT) * (1 + Q) := by
    have h1 : (0 : ℝ) ≤ 1 + CT := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Q := by linarith
    exact mul_nonneg (mul_nonneg hCd0 h1) h2
  have hsumG : (∑ l : Fin k → Fin n,
        |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
            (Work.Diff.STE.pdVec k l u)|)
      ≤ Cd * (1 + CT) * (1 + Q) *
          ((Fintype.card (Fin k → Fin n) : ℝ) + Work.Diff.STE.ENormSq k u) := by
    have hterm : ∀ l : Fin k → Fin n,
        |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
            (Work.Diff.STE.pdVec k l u)|
          ≤ Cd * (1 + CT) * (1 + Q) *
              (1 + ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l u z‖ ^ 2) := by
      intro l
      have hcontG : Continuous (fun z => Work.Diff.STE.pdVec k l w z - FL l z) :=
        (hcw l).sub (hcF l)
      have hint1 : MeasureTheory.Integrable
          (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k l w z - FL l z‖ ^ 2)
          (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
        Work.Diff.STE.cm_integrableOn_unitCube_of_continuous (hcontG.norm.pow 2)
      have hint2 : MeasureTheory.Integrable
          (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k l u z‖ ^ 2)
          (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
        Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hcu l).norm.pow 2)
      have hcs := Work.Diff.STE.L2re_abs_le_sqrt _ _ hint1 hint2
      have hbdd : ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l w z - FL l z‖ ^ 2
          ≤ (Cd * (1 + CT) * (1 + Q)) ^ 2 :=
        integral_normSq_le hcontG fun z => hdef l z
      have hs1 : Real.sqrt (∫ z in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec k l w z - FL l z‖ ^ 2) ≤ Cd * (1 + CT) * (1 + Q) := by
        refine le_trans (Real.sqrt_le_sqrt hbdd) (le_of_eq ?_)
        exact Real.sqrt_sq hCdn
      have hs2 : Real.sqrt (∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l u z‖ ^ 2)
          ≤ 1 + ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l u z‖ ^ 2 :=
        sqrt_le_one_add (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
      exact le_trans hcs (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) hCdn)
    refine le_trans (Finset.sum_le_sum fun l _ => hterm l) ?_
    rw [← Finset.mul_sum]
    have hEq : (∑ l : Fin k → Fin n,
          (1 + ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l u z‖ ^ 2))
        = ((Fintype.card (Fin k → Fin n) : ℝ) + Work.Diff.STE.ENormSq k u) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    rw [hEq]
  -- ### the lower-order sum
  have hsumT : (∑ l : Fin k → Fin n,
        |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|)
      ≤ (CT + 1) * (1 + Work.Diff.STE.ENormSq k u) := by
    have hterm : ∀ l : Fin k → Fin n,
        |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|
          ≤ ((∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l Th z‖ ^ 2)
              + (∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l u z‖ ^ 2)) / 2 := by
      intro l
      have hint1 : MeasureTheory.Integrable
          (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k l Th z‖ ^ 2)
          (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
        Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hcT l).norm.pow 2)
      have hint2 : MeasureTheory.Integrable
          (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k l u z‖ ^ 2)
          (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
        Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hcu l).norm.pow 2)
      have hcs := Work.Diff.STE.L2re_abs_le_sqrt _ _ hint1 hint2
      have ha : (0 : ℝ) ≤ ∫ z in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec k l Th z‖ ^ 2 :=
        MeasureTheory.integral_nonneg fun _ => sq_nonneg _
      have hb : (0 : ℝ) ≤ ∫ z in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec k l u z‖ ^ 2 :=
        MeasureTheory.integral_nonneg fun _ => sq_nonneg _
      exact le_trans hcs (sqrt_mul_sqrt_le ha hb)
    refine le_trans (Finset.sum_le_sum fun l _ => hterm l) ?_
    have h2 : (∑ l : Fin k → Fin n,
          ((∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l Th z‖ ^ 2)
            + (∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l u z‖ ^ 2)) / 2)
        = (Work.Diff.STE.ENormSq k Th + Work.Diff.STE.ENormSq k u) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      rfl
    rw [h2]
    nlinarith [henT, ENormSq_nonneg (m := k) u, hCT0]
  -- ### assembly
  have hsum : (∑ l : Fin k → Fin n,
        Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u))
      ≤ (∑ l : Fin k → Fin n, Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u))
        + (∑ l : Fin k → Fin n,
            |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
              (Work.Diff.STE.pdVec k l u)|)
        + (∑ l : Fin k → Fin n,
            |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|) := by
    calc (∑ l : Fin k → Fin n,
          Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u))
        ≤ ∑ l : Fin k → Fin n, (Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u)
            + |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
                (Work.Diff.STE.pdVec k l u)|
            + |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th)
                (Work.Diff.STE.pdVec k l u)|) :=
          Finset.sum_le_sum fun l _ => hstep l
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hFLsum : (∑ l : Fin k → Fin n, Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u))
      = (∑ l : Fin k → Fin n,
        Work.Diff.STE.L2re
          (fun z => ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
            * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
          (Work.Diff.STE.pdVec k l u)) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hFL]
  have hcard : (0 : ℝ) ≤ (Fintype.card (Fin k → Fin n) : ℝ) := by positivity
  have hE1 : 0 ≤ Work.Diff.STE.ENormSq k u := ENormSq_nonneg u
  calc (∑ l : Fin k → Fin n,
        Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u))
      ≤ (∑ l : Fin k → Fin n, Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u))
        + (∑ l : Fin k → Fin n,
            |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
              (Work.Diff.STE.pdVec k l u)|)
        + (∑ l : Fin k → Fin n,
            |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|) := hsum
    _ ≤ (-(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u + F * Work.Diff.STE.ENormSq k u)
        + Cd * (1 + CT) * (1 + Q) *
            ((Fintype.card (Fin k → Fin n) : ℝ) + Work.Diff.STE.ENormSq k u)
        + (CT + 1) * (1 + Work.Diff.STE.ENormSq k u) := by
        rw [hFLsum]
        exact add_le_add (add_le_add hg hsumG) hsumT
    _ ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u
        + (F + Cd * (1 + CT) * (1 + Q) * ((Fintype.card (Fin k → Fin n) : ℝ) + 1)
            + (CT + 1)) * (1 + Work.Diff.STE.ENormSq k u) := by
        nlinarith [hE1, hcard, hCdn, hF0, hCT0,
          mul_nonneg hCdn hcard, mul_nonneg hCdn hE1, mul_nonneg hF0 hE1,
          mul_nonneg (mul_nonneg hCdn hcard) hE1, mul_nonneg hCT0 hE1]


/-! ## Two bridges between `pdR`/`pdVec` and the complex coercion -/

lemma pdVec_one_pd {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => i) f = Work.Diff.STE.pd i f := by
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
  norm_num

lemma norm_pd_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : DifferentiableAt ℝ f x) (i : ι) :
    ‖Work.Diff.STE.pd i (fun y => ((f y : ℝ) : ℂ)) x‖ = |Work.Diff.STE.pdR i f x| := by
  have h1 : Work.Diff.STE.pd i (fun y => ((f y : ℝ) : ℂ)) x
      = ((Work.Diff.STE.pdR i f x : ℝ) : ℂ) := by
    rw [Work.Diff.STE.pd, Work.Diff.STE.pdR]
    rw [show (fun y : ι → ℝ => ((f y : ℝ) : ℂ))
        = ⇑(Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ f from rfl]
    rw [fderiv_comp x (ContinuousLinearMap.differentiableAt _) hf]
    rw [ContinuousLinearMap.fderiv]
    rfl
  rw [h1]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The first derivative of a smooth real function, in the `pdVec` and the `pdR` form. -/
lemma abs_pdR_le {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ENat) f) {i : ι} {x : ι → ℝ} {C : ℝ}
    (h : ‖Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => i) (fun y => ((f y : ℝ) : ℂ)) x‖ ≤ C) :
    |Work.Diff.STE.pdR i f x| ≤ C := by
  rw [pdVec_one_pd] at h
  rwa [norm_pd_ofReal (hf.differentiable (by simp) x) i] at h

/-- **The periodised localised component of a section with smooth chart data** is smooth and
`1`-periodic. -/
lemma Rper_contDiff_periodic_of_chartData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hh : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) hh)
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ENat) (D.Rper j hh a b) ∧
      Work.Diff.STE.Periodic1 (D.Rper j hh a b) := by
  have hR : ContDiff ℝ (⊤ : ENat) (D.R j hh a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData D hh hsm j a b
  have hF : ContDiff ℝ (⊤ : ENat) (fun z => ((D.R j hh a b z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hR
  have hFsup : Function.support (fun z => ((D.R j hh a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    exact D.R_support j hh a b (by
      simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hz)
  obtain ⟨hcd, hper, -⟩ := Work.Diff.STE.periodization_contDiff_periodic _ hF hFsup
  exact ⟨hcd, hper⟩

/-! ## The assembly given the three analytic inputs -/

/-- **The assembly**: the target `gardingAssembly` follows from the three analytic inputs
(the DeTurck transport, the static jet bound of the localised components and the Leibniz defect
bound), all of which are uniform in `h`. -/
theorem gardingAssembly_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : Module.finrank ℝ E + 12 < 2 * k)
    (hJet : ∀ K : ℝ, 0 < K → GardJet (I := I) (M := M) D k K)
    (hTrans : ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
          GardData (I := I) (M := M) D hLC k lam' C h hsym hpos hsmooth)
    (hDef : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : ι → ι → (ι → ℝ) → ℝ) (K P : ℝ)
        (hA : ∀ c d, ContDiff ℝ (⊤ : ENat) (A c d))
        (hK : ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → ι) (c d : ι) (z : ι → ℝ),
            ‖Work.Diff.STE.pdVec m β (fun y => ((A c d y : ℝ) : ℂ)) z‖ ≤ K)
        (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ (⊤ : ENat) u)
        (hP : ∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → ι) (z : ι → ℝ),
            ‖Work.Diff.STE.pdVec m β u z‖ ≤ P)
        (l : Fin k → ι) (z : ι → ℝ),
        ‖Work.Diff.STE.pdVec k l (fun y => ∑ c, ∑ d,
            ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
            - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)‖
          ≤ C * (1 + K) * (1 + P)) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K)
          (B : ℝ) (hB : D.ENormB k h ≤ B),
          D.ENormB_pair k
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
            ≤ -(lam' / 2) * D.ENormB (k + 1) h + C * (1 + B) ^ 2 ∧
          D.ENormB (k - 1) (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
              + D.ENormB 0 (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
            ≤ C * (1 + B) ^ 2 * (1 + D.ENormB (k + 1) h) := by
  intro lam K hlam hK
  obtain ⟨lamT, CT, hlamT, hCT, hGard⟩ := hTrans lam K hlam hK
  have hCT0 : 0 ≤ CT := hCT
  obtain ⟨CJ, hCJ0, hJetB⟩ := hJet K hK
  obtain ⟨Cdf, hCdf0, hDefB⟩ := hDef (ι := Fin (Module.finrank ℝ E)) k
  obtain ⟨F, hFnn, hGardv⟩ := garding_vec_uniform (ι := Fin (Module.finrank ℝ E)) k
  set Q : ℝ := CJ * (1 + K) ^ (k + 1) with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg hCJ0 (pow_nonneg (by linarith) _)
  set Acomp : ℝ := F lamT CT + Cdf * (1 + CT) * (1 + Q)
      * ((Fintype.card (Fin k → Fin (Module.finrank ℝ E)) : ℝ) + 1) + (CT + 1) with hAcomp
  have hAcomp0 : 0 ≤ Acomp := by
    rw [hAcomp]
    refine add_nonneg (add_nonneg (hFnn lamT hlamT CT) ?_) (by linarith)
    refine mul_nonneg (mul_nonneg (mul_nonneg hCdf0 (by linarith)) (by linarith)) ?_
    positivity
  set Ntot : ℝ := (Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ)
      * (Module.finrank ℝ E : ℝ) with hNtot
  have hNtot0 : 0 ≤ Ntot := by rw [hNtot]; positivity
  refine ⟨lamT, max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1)), hlamT, ?_, ?_⟩
  · exact le_trans (mul_nonneg hAcomp0 (by linarith)) (le_max_left _ _)
  · intro h hsym hpos hsmooth hell hub hjet B hB
    have hG := hGard h hsym hpos hsmooth hell hub hjet
    have hB0 : 0 ≤ B := by
      refine le_trans ?_ hB
      simp only [Work.Diff.STE.B3Data.ENormB]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => ENormSq_nonneg (m := k) _
    -- ### the per-component bound
    have hcomp : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
        (∑ l : Fin k → Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re
            (Work.Diff.STE.pdVec k l
              (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b))
            (Work.Diff.STE.pdVec k l (D.Rper j h a b)))
        ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b)
          + Acomp * (1 + Work.Diff.STE.ENormSq k (D.Rper j h a b)) := by
      intro j a b
      obtain ⟨A, Th, hAsym, hAell, hAsm, hAper, hAbd, hTsm, hTper, hTen, hTid,
        hTlow, _hT0⟩ := hG j
      obtain ⟨husm, huper⟩ := Rper_contDiff_periodic_of_chartData D h hsmooth j a b
      refine component_garding_bound (n := Module.finrank ℝ E) k A (Th a b)
        (D.Rper j h a b)
        (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
        lamT CT (F lamT CT) Cdf Q
        hAsm hAper hCT0 (hTsm a b) (hTper a b) (hTen a b) (fun z => hTid a b z) husm huper hQ0
        (hFnn lamT hlamT CT) ?_ hCdf0 ?_
      · simpa only [neg_mul] using hGardv lamT hlamT CT A hAsm hAper hAsym (fun z ξ => hAell z ξ)
          (fun c d i x => abs_pdR_le (hAsm c d)
            (hAbd 1 (by omega) (fun _ : Fin 1 => i) x c d))
          (D.Rper j h a b) (husm.of_le (WithTop.coe_le_coe.mpr
            (le_top : ((k + 2 : ℕ) : ℕ∞) ≤ ⊤))) huper
      · intro l z
        exact hDefB A CT Q hAsm (fun m hm β c d z' => hAbd m hm β z' c d)
          (D.Rper j h a b) husm
          (fun m hm β z' => hJetB h hsmooth hjet j a b m hm β z') l z
    -- ### the two directional bounds
    have hE2 : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b))
        = -(lamT / 2) * D.ENormB (k + 1) h := by
      rw [Work.Diff.STE.B3Data.ENormB]
      simp only [← Finset.mul_sum]
    have hE1 : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            Acomp * (1 + Work.Diff.STE.ENormSq k (D.Rper i h a b)))
        = Acomp * (Ntot + D.ENormB k h) := by
      rw [Work.Diff.STE.B3Data.ENormB, hNtot]
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    have hpair : D.ENormB_pair k
          (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
        ≤ -(lamT / 2) * D.ENormB (k + 1) h + Acomp * (Ntot + D.ENormB k h) := by
      have h1 : D.ENormB_pair k
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
          = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
              ∑ b : Fin (Module.finrank ℝ E),
                ∑ l : Fin k → Fin (Module.finrank ℝ E),
                  Work.Diff.STE.L2re
                    (Work.Diff.STE.pdVec k l
                      (D.Rper i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos
                        hsmooth) a b))
                    (Work.Diff.STE.pdVec k l (D.Rper i h a b)) := rfl
      rw [h1, ← hE2, ← hE1]
      refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ => hcomp i a b) ?_
      simp only [Finset.sum_add_distrib]
      exact le_refl _
    -- ### the first inequality
    have hCl : (0 : ℝ) ≤ max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1)) :=
      le_trans (mul_nonneg hAcomp0 (by linarith)) (le_max_left _ _)
    have hineq1 : D.ENormB_pair k
          (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
        ≤ -(lamT / 2) * D.ENormB (k + 1) h
          + max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1)) * (1 + B) ^ 2 := by
      refine le_trans hpair ?_
      have h1 : Ntot + D.ENormB k h ≤ (Ntot + 1) * (1 + B) := by
        nlinarith [hNtot0, hB0, hB]
      have h2 : (1 : ℝ) + B ≤ (1 + B) ^ 2 := by nlinarith [hB0]
      have h3 : Acomp * (Ntot + D.ENormB k h)
          ≤ Acomp * (Ntot + 1) * (1 + B) ^ 2 := by
        calc Acomp * (Ntot + D.ENormB k h) ≤ Acomp * ((Ntot + 1) * (1 + B)) :=
              mul_le_mul_of_nonneg_left h1 hAcomp0
          _ = Acomp * (Ntot + 1) * (1 + B) := by ring
          _ ≤ Acomp * (Ntot + 1) * (1 + B) ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hAcomp0 (by linarith))
      have h4 : Acomp * (Ntot + 1) * (1 + B) ^ 2
          ≤ max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1)) * (1 + B) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith [h3, h4]
    -- ### the second inequality
    have hlow1 : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq (k - 1)
            (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
          ≤ CT * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b)) ∧
        Work.Diff.STE.ENormSq 0
            (D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
          ≤ CT * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b)) := by
      intro j a b
      obtain ⟨A, Th, -, -, -, -, -, -, -, -, -, hTen', hTen0⟩ := hG j
      exact ⟨hTen' a b, hTen0 a b⟩
    have hsumCT : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            CT * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b)))
        = CT * (Ntot + D.ENormB (k + 1) h) := by
      rw [Work.Diff.STE.B3Data.ENormB, hNtot]
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    have hlow : D.ENormB (k - 1)
          (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
        + D.ENormB 0 (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
        ≤ 2 * CT * (Ntot + D.ENormB (k + 1) h) := by
      have h2 : D.ENormB (k - 1)
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
          ≤ CT * (Ntot + D.ENormB (k + 1) h) := by
        rw [Work.Diff.STE.B3Data.ENormB, ← hsumCT]
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => (hlow1 i a b).1
      have h0 : D.ENormB 0
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
          ≤ CT * (Ntot + D.ENormB (k + 1) h) := by
        rw [Work.Diff.STE.B3Data.ENormB, ← hsumCT]
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => (hlow1 i a b).2
      linarith
    have hENB0 : 0 ≤ D.ENormB (k + 1) h := by
      simp only [Work.Diff.STE.B3Data.ENormB]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => ENormSq_nonneg (m := k + 1) _
    have hineq2 : D.ENormB (k - 1)
          (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
        + D.ENormB 0 (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
        ≤ max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1)) * (1 + B) ^ 2
          * (1 + D.ENormB (k + 1) h) := by
      refine le_trans hlow ?_
      have hB1 : (1 : ℝ) ≤ (1 + B) ^ 2 := by nlinarith [hB0]
      have h1 : Ntot + D.ENormB (k + 1) h ≤ (Ntot + 1) * (1 + D.ENormB (k + 1) h) := by
        nlinarith [hNtot0, hENB0]
      have h2 : 2 * CT * (Ntot + D.ENormB (k + 1) h)
          ≤ 2 * CT * (Ntot + 1) * (1 + D.ENormB (k + 1) h) := by
        calc 2 * CT * (Ntot + D.ENormB (k + 1) h)
            ≤ 2 * CT * ((Ntot + 1) * (1 + D.ENormB (k + 1) h)) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = 2 * CT * (Ntot + 1) * (1 + D.ENormB (k + 1) h) := by ring
      have h3 : 2 * CT * (Ntot + 1) * (1 + D.ENormB (k + 1) h)
          ≤ max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1))
            * (1 + B) ^ 2 * (1 + D.ENormB (k + 1) h) := by
        have h33 : 2 * CT * (Ntot + 1) * (1 + D.ENormB (k + 1) h)
            ≤ max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1))
              * (1 + D.ENormB (k + 1) h) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
        have h34 : max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1))
              * (1 + D.ENormB (k + 1) h)
            ≤ max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1))
              * (1 + B) ^ 2 * (1 + D.ENormB (k + 1) h) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          conv_lhs => rw [← mul_one (max (Acomp * (Ntot + 1)) (2 * CT * (Ntot + 1)))]
          exact mul_le_mul_of_nonneg_left hB1 hCl
        linarith
      linarith [h2, h3]
    exact ⟨hineq1, hineq2⟩


/-! ## The target theorem -/

theorem gardingAssembly
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : Module.finrank ℝ E + 12 < 2 * k) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K)
          (B : ℝ) (hB : D.ENormB k h ≤ B),
          D.ENormB_pair k
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
            ≤ -(lam' / 2) * D.ENormB (k + 1) h + C * (1 + B) ^ 2 ∧
          D.ENormB (k - 1) (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
              + D.ENormB 0 (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
            ≤ C * (1 + B) ^ 2 * (1 + D.ENormB (k + 1) h) :=
  gardingAssembly_aux (I := I) (M := M) D hLC k hk
    (fun K hK => gardJet_holds (I := I) (M := M) D k K hK)
    (fun lam K hlam hK =>
      gardTransport_holds (I := I) (M := M) D hLC k (by omega) lam K hlam hK)
    (fun {ι} _ _ k => pdVec_gard_defect_bound (ι := ι) k)

end

end Work.Diff.STE.Lead.Gal
