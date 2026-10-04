import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Defs
import Submission.Work.Diff.STE.Lead.GalTame.component_garding_sharp
import Submission.Work.Diff.STE.Lead.GalTame.sharpTrans
import Submission.Work.Diff.STE.Lead.GalTame.sup_pdList_le_of_energy
import Submission.Work.Diff.STE.Lead.GalTame.Rper_ENormSq_zero_pdVec_le_top

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The energy is nonnegative. -/
lemma ENormSq_nonneg_gt {n : ℕ} (m : ℕ) (f : (Fin n → ℝ) → ℂ) :
    0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => integral_nonneg fun x => by positivity

/-- `ENormSq 0` is the square of the `L²` norm. -/
lemma ENormSq_zero_gt {n : ℕ} (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 f = ∫ x in Work.Diff.STE.unitCube, ‖f x‖ ^ 2 := by
  rw [Work.Diff.STE.ENormSq, Finset.univ_unique, Finset.sum_singleton]
  simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]

/-- A single top-order jet is dominated by the full energy. -/
lemma ENormSq_zero_pdVec_le_gt {n : ℕ} (N : ℕ) (β : Fin N → Fin n)
    (g : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec N β g) ≤ Work.Diff.STE.ENormSq N g := by
  rw [ENormSq_zero_gt, Work.Diff.STE.ENormSq]
  exact Finset.single_le_sum
    (f := fun l : Fin N → Fin n =>
      ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec N l g x‖ ^ 2)
    (fun l _ => integral_nonneg fun x => by positivity) (Finset.mem_univ β)

/-- The composite energy is nonnegative. -/
lemma ENormB_nonneg_gt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (m : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) : 0 ≤ D.ENormB m h := by
  simp only [Work.Diff.STE.B3Data.ENormB]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    ENormSq_nonneg_gt m _

/-- A single component of `ENormB` is bounded by `ENormB`. -/
lemma ENormSq_le_ENormB_gt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (m : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.ENormSq m (D.Rper i h a b) ≤ D.ENormB m h := by
  rw [Work.Diff.STE.B3Data.ENormB]
  have h1 : Work.Diff.STE.ENormSq m (D.Rper i h a b)
      ≤ ∑ b' : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h a b') :=
    Finset.single_le_sum (fun b' _ => ENormSq_nonneg_gt m _) (Finset.mem_univ b)
  have h2 : (∑ b' : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h a b'))
      ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq m (D.Rper i h a' b') :=
    Finset.single_le_sum
      (f := fun a' : Fin (Module.finrank ℝ E) =>
        ∑ b' : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h a' b'))
      (fun a' _ => Finset.sum_nonneg fun b' _ => ENormSq_nonneg_gt m _) (Finset.mem_univ a)
  have h3 : (∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        Work.Diff.STE.ENormSq m (D.Rper i h a' b'))
      ≤ ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq m (D.Rper i' h a' b') :=
    Finset.single_le_sum
      (f := fun i' : ι₀ => ∑ a' : Fin (Module.finrank ℝ E),
        ∑ b' : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i' h a' b'))
      (fun i' _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ =>
        ENormSq_nonneg_gt m _) (Finset.mem_univ i)
  exact le_trans h1 (le_trans h2 h3)

theorem gardingSharp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k k₀ : ℕ)
    (hk : Module.finrank ℝ E + 4 ≤ k)
    (hk₀ : Module.finrank ℝ E + 4 < 2 * k₀)
    (hDefSharp : ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
            (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
        (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ) (KA S Q1 : ℝ)
        (hA : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
        (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
        (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
        (hup : Work.Diff.STE.Periodic1 u)
        (hKA : 0 ≤ KA) (hS : 0 ≤ S) (hQ1 : 0 ≤ Q1),
        (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
          |A c d z| ≤ S) →
        (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (r c d : Fin (Module.finrank ℝ E)),
          |Work.Diff.STE.pdR r (fun y : Fin (Module.finrank ℝ E) → ℝ => A c d y) z| ≤ S) →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
          (c d : Fin (Module.finrank ℝ E)),
          Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
            (fun y : Fin (Module.finrank ℝ E) → ℝ => ((A c d y : ℝ) : ℂ))) ≤ KA) →
        (∀ (m : ℕ) (hm : m ≤ 2) (β : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ), ‖Work.Diff.STE.pdVec m β u z‖ ≤ S) →
        (∀ β : Fin (k + 1) → Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (k + 1) β u) ≤ Q1) →
        ∀ l : Fin k → Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq 0 (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.pdVec k l
                  (fun y : Fin (Module.finrank ℝ E) → ℝ => ∑ c, ∑ d,
                    ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
                - ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                    * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
            ≤ Cd * (S ^ 2 * (1 + KA + Q1))) :
    ∀ (lam K B₀ : ℝ), 0 < lam → 0 < K → 0 ≤ B₀ →
      ∃ (lam' Cg : ℝ), 0 < lam' ∧ 0 ≤ Cg ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
            |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
          D.ENormB k₀ h + D.ENormB 0 h ≤ B₀ →
          D.ENormB_pair k
              (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
            ≤ -(lam' / 2) * D.ENormB (k + 1) h + Cg * (1 + D.ENormB k h) := by
  intro lam K B₀ hlam hK hB₀
  classical
  obtain ⟨Cd, hCd0, hDefB⟩ := hDefSharp
  -- the level of the estimate is at least one
  have hk1 : 1 ≤ k := by
    have h0 : 0 ≤ Module.finrank ℝ E := Nat.cast_nonneg _
    omega
  -- the sharp transport data
  obtain ⟨lamT, CA, CT, hlamT, hCA0, hCT0, hTransB⟩ :=
    sharpTrans (I := I) (M := M) D hLC k hk1 lam K hlam hK
  -- the Sobolev sup bound at level `k₀`
  obtain ⟨Csob, hCsob0, hSobb⟩ := sup_pdList_le_of_energy (ι := Fin (Module.finrank ℝ E)) k₀
  -- the Fourier-interpolation constant for the level comparison
  obtain ⟨Clev2, hClev20, hLev2⟩ :=
    Rper_ENormSq_zero_pdVec_le_top (I := I) (M := M) D k hk1
  set Clev : ℝ := max 1 (Clev2 * (∑ j ∈ Finset.range (k + 1),
    (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ))) with hClev
  have hClev0 : 0 ≤ Clev := le_trans zero_le_one (by rw [hClev]; exact le_max_left _ _)
  have hClev1 : 1 ≤ Clev := by rw [hClev]; exact le_max_left _ _
  -- the uniform Gårding constant
  obtain ⟨Fg, hFg0, hFgB⟩ := garding_vec_uniform (ι := Fin (Module.finrank ℝ E)) k
  -- the number of charts and of multi-indices
  set Nd : ℝ := (Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)
    with hNd
  set Nc : ℝ := (Fintype.card (Fin k → Fin (Module.finrank ℝ E)) : ℝ) with hNc
  have hNd0 : 0 ≤ Nd := by rw [hNd]; positivity
  have hNc0 : 0 ≤ Nc := by rw [hNc]; positivity
  set Nd1 : ℝ := max Nd 1 with hNd1
  have hNd10 : 0 ≤ Nd1 := le_trans zero_le_one (by rw [hNd1]; exact le_max_right _ _)
  have hNd11 : 1 ≤ Nd1 := by rw [hNd1]; exact le_max_right _ _
  have hNd_le : Nd ≤ Nd1 := by rw [hNd1]; exact le_max_left _ _
  -- the absorption parameter of the top-order term
  set e : ℝ := lamT / (8 * (Nd * Nc + 1)) with he
  have hepos : 0 < e := by rw [he]; positivity
  have heabs : Nd * (Nc * (2 * e)) ≤ lamT / 4 := by
    rw [he]
    have hstep : Nd * (Nc * (2 * (lamT / (8 * (Nd * Nc + 1)))))
        = lamT * ((Nd * Nc) / (4 * (Nd * Nc + 1))) := by
      field_simp
      ring
    rw [hstep]
    have h2 : (Nd * Nc) / (4 * (Nd * Nc + 1)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hNd0, hNc0]
    calc lamT * ((Nd * Nc) / (4 * (Nd * Nc + 1))) ≤ lamT * (1 / 4) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hlamT)
      _ = lamT / 4 := by ring
  -- the sup bound of the coefficient, of its first derivative, and of the `2`-jets of the section
  set Ssp : ℝ := max CA (max 1 (Csob * Real.sqrt B₀)) with hSsp
  have hSsp0 : 0 ≤ Ssp := by
    rw [hSsp]
    exact le_trans hCA0 (le_max_left _ _)
  have hSspCA : CA ≤ Ssp := by rw [hSsp]; exact le_max_left _ _
  have hSspsob : Csob * Real.sqrt B₀ ≤ Ssp := by
    rw [hSsp]
    exact le_trans (le_max_right 1 _) (le_max_right _ _)
  -- the per-component sharp estimate
  obtain ⟨Cg, hCg0, hCompB⟩ :=
    component_garding_sharp (n := Module.finrank ℝ E) k lamT Ssp (Fg lamT CA) Cd CT e
      hepos hSsp0 hCd0 hCT0 (hFg0 lamT hlamT CA)
  -- the final constant
  set C1 : ℝ := Cg * Nd1 * (1 + CA * (1 + Clev * (1 + B₀))) with hC1
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  refine ⟨lamT / 2, C1, by linarith, hC10, ?_⟩
  intro h hsym hpos hsmooth hell hub hjet hB
  -- ## the transport data
  have hData := hTransB h hsym hpos hsmooth hell hub hjet
  choose Aof Thof hAofAsym hAofEll hAofSm hAofPer hAofBd hAofBdD hAofEN hThofSm hThofPer
    hThofEN hIdof using hData
  -- ## elementary bounds
  have hB0 : 0 ≤ B₀ := le_trans (add_nonneg (ENormB_nonneg_gt D k₀ h) (ENormB_nonneg_gt D 0 h)) hB
  have hENB00 : 0 ≤ D.ENormB 0 h := ENormB_nonneg_gt D 0 h
  have hENBk0 : 0 ≤ D.ENormB k h := ENormB_nonneg_gt D k h
  have hENBk10 : 0 ≤ D.ENormB (k + 1) h := ENormB_nonneg_gt D (k + 1) h
  have hENBk₀0 : 0 ≤ D.ENormB k₀ h := ENormB_nonneg_gt D k₀ h
  have hEk₀ : D.ENormB k₀ h ≤ B₀ := by linarith
  have hE0 : D.ENormB 0 h ≤ B₀ := by linarith
  set Q1 : ℝ := D.ENormB (k + 1) h with hQ1
  have hQ10 : 0 ≤ Q1 := by rw [hQ1]; exact hENBk10
  set KA : ℝ := CA * (1 + Clev * (D.ENormB k h + B₀)) with hKA
  have hKA0 : 0 ≤ KA := by rw [hKA]; positivity
  -- ## smoothness and periodicity of the components
  have hRper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.Rper i h a b) ∧
        Work.Diff.STE.Periodic1 (D.Rper i h a b) := fun i a b =>
    Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth i a b
  -- ## the Sobolev sup bound for the `2`-jets of the components
  have hsob : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ 2)
      (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖Work.Diff.STE.pdVec m β (D.Rper i h a b) z‖ ≤ Ssp := by
    intro i a b m hm β z
    obtain ⟨hsm, hper⟩ := hRper i a b
    have h1 : Work.Diff.STE.ENormSq k₀ (D.Rper i h a b) ≤ B₀ :=
      le_trans (ENormSq_le_ENormB_gt D k₀ h i a b) hEk₀
    have h2 : Work.Diff.STE.ENormSq 0 (D.Rper i h a b) ≤ B₀ :=
      le_trans (ENormSq_le_ENormB_gt D 0 h i a b) hE0
    have hlen : Fintype.card (Fin (Module.finrank ℝ E)) + 2 * (List.ofFn β).length < 2 * k₀ := by
      rw [List.length_ofFn, Fintype.card_fin]
      omega
    have h3 := hSobb (D.Rper i h a b) B₀ hsm hper h1 h2 (List.ofFn β) hlen z
    have h4 : ‖Work.Diff.STE.pdVec m β (D.Rper i h a b) z‖ ≤ Csob * Real.sqrt B₀ := by
      simpa only [Work.Diff.STE.pdVec] using h3
    exact le_trans h4 hSspsob
  -- ## the level-monotonicity of the composite energy
  have hLevB : ∀ (m : ℕ), 1 ≤ m → m ≤ k → D.ENormB m h ≤ Clev * (D.ENormB k h + B₀) := by
    intro m hm hmk
    have hcompL : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq m (D.Rper i h a b)
          ≤ Clev2 * (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ)
              * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
                + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
      intro i a b
      calc Work.Diff.STE.ENormSq m (D.Rper i h a b)
          = ∑ β : Fin m → Fin (Module.finrank ℝ E),
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β (D.Rper i h a b)) := by
            rw [Work.Diff.STE.ENormSq]
            refine Finset.sum_congr rfl fun β _ => ?_
            rw [ENormSq_zero_gt]
        _ ≤ ∑ _β : Fin m → Fin (Module.finrank ℝ E),
              Clev2 * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
                + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) :=
            Finset.sum_le_sum fun β _ => hLev2 h hsmooth i a b m hmk β
        _ = Clev2 * (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ)
              * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
                + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    have hstep : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq m (D.Rper i h a b))
        ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Clev2 * (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ)
              * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
                + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        hcompL i a b
    have hcollapse : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            Clev2 * (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ)
              * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
                + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)))
        = Clev2 * (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ)
            * (D.ENormB k h + D.ENormB 0 h) := by
      simp only [Work.Diff.STE.B3Data.ENormB, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsumL : D.ENormB m h
        ≤ Clev2 * (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ)
            * (D.ENormB k h + D.ENormB 0 h) := by
      rw [Work.Diff.STE.B3Data.ENormB]
      exact le_trans hstep (le_of_eq hcollapse)
    have hcard : (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ)
        ≤ ∑ j ∈ Finset.range (k + 1),
          (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ) :=
      Finset.single_le_sum
        (f := fun j : ℕ => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ))
        (fun j _ => by positivity) (Finset.mem_range.mpr (by omega : m < k + 1))
    have hprod : Clev2 * (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ) ≤ Clev := by
      refine le_trans (mul_le_mul_of_nonneg_left hcard hClev20) ?_
      rw [hClev]
      exact le_max_right _ _
    have hEtot : 0 ≤ D.ENormB k h + D.ENormB 0 h := by linarith
    refine le_trans hsumL ?_
    exact mul_le_mul hprod (by linarith [hE0]) hEtot hClev0
  -- ## the global bounds `KA` and `Q1` are admissible
  have hKAb : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
      (c d : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
        (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Aof i c d y : ℝ) : ℂ))) ≤ KA := by
    intro i m hm β c d
    refine le_trans (hAofEN i m hm β c d) ?_
    have h1 : D.ENormB m h ≤ Clev * (D.ENormB k h + B₀) := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0]
        have h3 : B₀ ≤ Clev * (D.ENormB k h + B₀) := by
          nlinarith [hClev1, hB0, hENBk0]
        linarith
      · exact hLevB m hpos hm
    rw [hKA]
    exact mul_le_mul_of_nonneg_left (by linarith) hCA0
  have hQ1b : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (β : Fin (k + 1) → Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (k + 1) β (D.Rper i h a b)) ≤ Q1 := by
    intro i a b β
    have h1 := ENormSq_zero_pdVec_le_gt (k + 1) β (D.Rper i h a b)
    have h2 := ENormSq_le_ENormB_gt D (k + 1) h i a b
    rw [hQ1]
    exact le_trans h1 h2
  -- ## the Gårding lower bound for each component
  have hgard : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      (∑ l : Fin k → Fin (Module.finrank ℝ E), Work.Diff.STE.L2re
          (fun z => ∑ c, ∑ d, ((Aof i c d z : ℝ) : ℂ) *
            Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l (D.Rper i h a b))) z)
          (Work.Diff.STE.pdVec k l (D.Rper i h a b)))
        ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b)
          + (Fg lamT CA) * Work.Diff.STE.ENormSq k (D.Rper i h a b) := by
    intro i a b
    obtain ⟨hsm, hper⟩ := hRper i a b
    have h := hFgB lamT hlamT CA (Aof i) (hAofSm i) (hAofPer i) (fun c d x => hAofAsym i x c d)
      (fun x ξ => hAofEll i x ξ) (fun c d r x => hAofBdD i x r c d) (D.Rper i h a b)
      (hsm.of_le (WithTop.coe_le_coe.mpr (le_top : ((k + 2 : ℕ) : ℕ∞) ≤ ⊤))) hper
    simpa only [neg_mul] using h
  -- ## the defect bound for each component
  have hdef : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (l : Fin k → Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq 0 (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.pdVec k l (fun y => ∑ c, ∑ d, ((Aof i c d y : ℝ) : ℂ) *
              Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper i h a b)) y) z
            - ∑ c, ∑ d, ((Aof i c d z : ℝ) : ℂ) *
              Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l (D.Rper i h a b))) z)
        ≤ Cd * (Ssp ^ 2 * (1 + KA + Q1)) := by
    intro i a b l
    obtain ⟨hsm, hper⟩ := hRper i a b
    exact hDefB (Aof i) (D.Rper i h a b) KA Ssp Q1 (hAofSm i) (hAofPer i) hsm hper hKA0
      hSsp0 hQ10 (fun z c d => le_trans (hAofBd i z c d) hSspCA)
      (fun z r c d => le_trans (hAofBdD i z r c d) hSspCA) (hKAb i)
      (fun m hm β z => hsob i a b m hm β z) (fun β => hQ1b i a b β) l
  -- ## the residual bound for each component
  have hTh : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (l : Fin k → Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l (Thof i a b)) ≤ CT * (1 + Q1) := by
    intro i a b l
    have h1 := hThofEN i k le_rfl l a b
    rw [hQ1]
    exact h1
  -- ## the per-component sharp estimate
  have hcomp : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      (∑ l : Fin k → Fin (Module.finrank ℝ E), Work.Diff.STE.L2re
          (Work.Diff.STE.pdVec k l
            (D.Rper i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b))
          (Work.Diff.STE.pdVec k l (D.Rper i h a b)))
        ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b)
          + Cg * (1 + Work.Diff.STE.ENormSq k (D.Rper i h a b) + KA) + Nc * (2 * e) * Q1 := by
    intro i a b
    obtain ⟨hsm, hper⟩ := hRper i a b
    exact hCompB (Aof i) (Thof i a b) (D.Rper i h a b)
      (D.Rper i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b)
      (hAofSm i) (hAofPer i) (hThofSm i a b) (hThofPer i a b) hsm hper (hIdof i a b)
      (hgard i a b) KA Q1 hKA0 hQ10 (hdef i a b) (hTh i a b)
  -- ## summing over the components
  have hsumA : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b))
      = -(lamT / 2) * D.ENormB (k + 1) h := by
    rw [Work.Diff.STE.B3Data.ENormB]
    simp only [← Finset.mul_sum]
  have hsumB : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Cg * (1 + Work.Diff.STE.ENormSq k (D.Rper i h a b) + KA))
      = Cg * (Nd + D.ENormB k h + Nd * KA) := by
    rw [Work.Diff.STE.B3Data.ENormB, hNd]
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hsumC : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Nc * (2 * e) * Q1) = Nd * (Nc * (2 * e) * Q1) := by
    rw [hNd]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hpair1 : D.ENormB_pair k
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑ l : Fin k → Fin (Module.finrank ℝ E), Work.Diff.STE.L2re
            (Work.Diff.STE.pdVec k l
              (D.Rper i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b))
            (Work.Diff.STE.pdVec k l (D.Rper i h a b)) := rfl
  have hpair2 : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑ l : Fin k → Fin (Module.finrank ℝ E), Work.Diff.STE.L2re
          (Work.Diff.STE.pdVec k l
            (D.Rper i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b))
          (Work.Diff.STE.pdVec k l (D.Rper i h a b)))
      ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (-(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b)
            + Cg * (1 + Work.Diff.STE.ENormSq k (D.Rper i h a b) + KA)
            + Nc * (2 * e) * Q1) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      hcomp i a b
  have hpair3 : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (-(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b)
            + Cg * (1 + Work.Diff.STE.ENormSq k (D.Rper i h a b) + KA)
            + Nc * (2 * e) * Q1))
      = -(lamT / 2) * D.ENormB (k + 1) h + Cg * (Nd + D.ENormB k h + Nd * KA)
        + Nd * (Nc * (2 * e) * Q1) := by
    have hsplit : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (-(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b)
            + Cg * (1 + Work.Diff.STE.ENormSq k (D.Rper i h a b) + KA)
            + Nc * (2 * e) * Q1))
        = (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) (D.Rper i h a b))
          + (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              Cg * (1 + Work.Diff.STE.ENormSq k (D.Rper i h a b) + KA))
          + (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              Nc * (2 * e) * Q1) := by
      simp only [Finset.sum_add_distrib]
    rw [hsplit, hsumA, hsumB, hsumC]
  -- ## the final arithmetic
  have hfin : -(lamT / 2) * D.ENormB (k + 1) h + Cg * (Nd + D.ENormB k h + Nd * KA)
        + Nd * (Nc * (2 * e) * Q1)
      ≤ -(lamT / 4) * D.ENormB (k + 1) h + C1 * (1 + D.ENormB k h) := by
    have h1 : Nd * (Nc * (2 * e)) * D.ENormB (k + 1) h ≤ lamT / 4 * D.ENormB (k + 1) h :=
      mul_le_mul_of_nonneg_right heabs hENBk10
    have h2 : Nd * (Nc * (2 * e) * Q1) = Nd * (Nc * (2 * e)) * D.ENormB (k + 1) h := by
      rw [hQ1]; ring
    rw [h2]
    have hstep1 : -(lamT / 2) * D.ENormB (k + 1) h
          + Nd * (Nc * (2 * e)) * D.ENormB (k + 1) h
        ≤ -(lamT / 4) * D.ENormB (k + 1) h := by linarith
    have hstep2 : Cg * (Nd + D.ENormB k h + Nd * KA) ≤ C1 * (1 + D.ENormB k h) := by
      have hKAb2 : KA ≤ CA * (1 + Clev * (1 + B₀)) * (1 + D.ENormB k h) := by
        rw [hKA]
        have hX : 1 + Clev * (D.ENormB k h + B₀)
            ≤ (1 + Clev * (1 + B₀)) * (1 + D.ENormB k h) := by
          have h3 : 0 ≤ Clev * B₀ * D.ENormB k h := by positivity
          nlinarith [h3, hClev0, hENBk0]
        calc CA * (1 + Clev * (D.ENormB k h + B₀))
            ≤ CA * ((1 + Clev * (1 + B₀)) * (1 + D.ENormB k h)) :=
              mul_le_mul_of_nonneg_left hX hCA0
          _ = CA * (1 + Clev * (1 + B₀)) * (1 + D.ENormB k h) := by ring
      have hA : Cg * (Nd + D.ENormB k h) ≤ Cg * (Nd1 * (1 + D.ENormB k h)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCg0
        nlinarith [hNd_le, hNd11, hENBk0, hNd10]
      have hB : Cg * (Nd * KA)
          ≤ Cg * (Nd1 * (CA * (1 + Clev * (1 + B₀))) * (1 + D.ENormB k h)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCg0
        calc Nd * KA ≤ Nd * (CA * (1 + Clev * (1 + B₀)) * (1 + D.ENormB k h)) :=
              mul_le_mul_of_nonneg_left hKAb2 hNd0
          _ ≤ Nd1 * (CA * (1 + Clev * (1 + B₀)) * (1 + D.ENormB k h)) :=
              mul_le_mul_of_nonneg_right hNd_le (by positivity)
          _ = Nd1 * (CA * (1 + Clev * (1 + B₀))) * (1 + D.ENormB k h) := by ring
      have hAB : Cg * (Nd + D.ENormB k h + Nd * KA)
          ≤ Cg * (Nd1 * (1 + D.ENormB k h))
            + Cg * (Nd1 * (CA * (1 + Clev * (1 + B₀))) * (1 + D.ENormB k h)) := by
        have hsplit : Cg * (Nd + D.ENormB k h + Nd * KA)
            = Cg * (Nd + D.ENormB k h) + Cg * (Nd * KA) := by ring
        rw [hsplit]
        exact add_le_add hA hB
      calc Cg * (Nd + D.ENormB k h + Nd * KA)
          ≤ Cg * (Nd1 * (1 + D.ENormB k h))
            + Cg * (Nd1 * (CA * (1 + Clev * (1 + B₀))) * (1 + D.ENormB k h)) := hAB
        _ = C1 * (1 + D.ENormB k h) := by rw [hC1]; ring_nf
    linarith [hstep1, hstep2]
  have hmain : D.ENormB_pair k
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
      ≤ -(lamT / 4) * D.ENormB (k + 1) h + C1 * (1 + D.ENormB k h) := by
    rw [hpair1]
    exact (le_trans hpair2 (le_of_eq hpair3)).trans hfin
  have hkey : -(lamT / 2 / 2) = -(lamT / 4) := by ring
  rw [hkey]
  exact hmain

end

end Work.Diff.STE.Lead.GalTame
