import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.energy_apriori
import Submission.Work.Diff.STE.flat.galerkin_ode_existence
import Submission.Work.Diff.STE.flat.energy_differentiable
import Submission.Work.Diff.STE.flat.seriesFunM_eq_sum
import Submission.Work.Diff.STE.flat.exists_radius_det_ne_zero
import Submission.Work.Diff.STE.flat.GalerkinLip
import Submission.Work.Diff.STE.flat.GalerkinJet
import Submission.Work.Diff.STE.flat.rhsExp_lipschitz
import Submission.Work.Diff.STE.flat.exists_uniform_local_solution
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 6000000

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open Work.Diff.STE.Flat.Galerkin
open MeasureTheory

noncomputable section

/-- The energy of a Galerkin coefficient family, as a function of the coefficients. -/
def bootE {n N : ℕ} (k : ℕ) (a : Coeff n N) : ℝ := ENormSqFull k (seriesFunM (toCoeff a))

/-- The quadratic form of the real part of the matrix `seriesFunM (toCoeff a) x`. -/
def bootForm {n N : ℕ} (a : Coeff n N) (x v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, reMat (seriesFunM (toCoeff a) x) i j * v i * v j

/-- The energy is nonnegative. -/
lemma bootE_nonneg {n N k : ℕ} (a : Coeff n N) : 0 ≤ bootE k a := by
  unfold bootE ENormSqFull
  refine add_nonneg ?_ ?_
  · unfold ENormSqM ENormSq
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun l _ => integral_nonneg (fun x => by positivity))))
  · unfold ENormSqM ENormSq
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun l _ => integral_nonneg (fun x => by positivity))))

/-- The quadratic form, written as a finite sum of characters. -/
lemma bootForm_eq_sum {n N : ℕ} (a : Coeff n N) (x v : Fin n → ℝ) :
    bootForm a x v = ∑ i : Fin n, ∑ j : Fin n,
      (∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 x).re * v i * v j := by
  have h : (seriesFunM (toCoeff a) x)
      = fun i j => ∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 x := by
    funext i j
    exact seriesFunM_toCoeff_apply a x i j
  unfold bootForm
  rw [h]
  simp only [reMat_apply]

/-- The value of the Fourier series of a box-supported family as a finite sum. -/
lemma seriesFunM_toCoeff_apply {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) (i j : Fin n) :
    seriesFunM (toCoeff a) x i j
      = ∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 x := by
  rw [seriesFunM_eq_sum (toCoeff a) (fun k hk => toCoeff_apply_not_mem a hk) x i j]
  exact Finset.sum_congr rfl (fun m _ => by rw [toCoeff_apply_mem a m.2])

/-- Continuity of the quadratic form of a fixed pair `(x, v)` in the coefficients. -/
lemma continuous_bootForm_fixed {n N : ℕ} (x v : Fin n → ℝ) :
    Continuous fun a : Coeff n N => bootForm a x v := by
  have hcont : Continuous fun a : Coeff n N =>
      ∑ i : Fin n, ∑ j : Fin n,
        (∑ m : box n N, a m i j * Work.Diff.STE.fourierExp m.1 x).re * v i * v j := by
    fun_prop
  refine Continuous.congr hcont (fun a => ?_)
  exact (bootForm_eq_sum a x v).symm

/-- Continuity of the level-`m` energy of the coefficient family `toCoeff a`. -/
lemma continuous_ENormSqM_toCoeff {n N : ℕ} (m : ℕ) :
    Continuous fun a : Coeff n N => ENormSqM m (seriesFunM (toCoeff a)) := by
  have key : ∀ a : Coeff n N, ENormSqM m (seriesFunM (toCoeff a))
      = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m → Fin n,
          ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => toCoeff a k i j) k'‖ ^ 2 :=
    fun a => ENormSqM_seriesFunM_eq (n := n) N m (toCoeff a)
      (fun k hk => toCoeff_apply_not_mem a hk)
  rw [funext key]
  refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
    continuous_finset_sum _ (fun l _ => continuous_finset_sum _ (fun k' hk' => ?_))))
  have hcont : Continuous fun a : Coeff n N =>
      ‖((List.ofFn l).map (fun c => (2 * Real.pi * Complex.I * (k' c : ℂ)))).prod
        * a ⟨k', hk'⟩ i j‖ ^ 2 := by
    fun_prop
  have hcongr : (fun a : Coeff n N => ‖dmulV (List.ofFn l) (fun k => toCoeff a k i j) k'‖ ^ 2)
      = fun a : Coeff n N =>
      ‖((List.ofFn l).map (fun c => (2 * Real.pi * Complex.I * (k' c : ℂ)))).prod
        * a ⟨k', hk'⟩ i j‖ ^ 2 := by
    funext a
    simp only [dmulV, toCoeff_apply_mem a hk']
  rw [hcongr]
  exact hcont

/-- Continuity of the energy in the coefficients. -/
lemma continuous_bootE {n N k : ℕ} :
    Continuous fun a : Coeff n N => bootE k a := by
  unfold bootE ENormSqFull
  exact (continuous_ENormSqM_toCoeff (n := n) (N := N) k).add
    (continuous_ENormSqM_toCoeff (n := n) (N := N) 0)

/-- The `ℓ²` norm squared of the coefficients is bounded by the energy: this is what makes the
sublevel sets of the energy bounded. -/
lemma sum_norm_sq_le_bootE {n N k : ℕ} (a : Coeff n N) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ m : box n N, ‖a m i j‖ ^ 2) ≤ bootE k a := by
  have hpar : ∀ i j : Fin n, (∑ m : box n N, ‖a m i j‖ ^ 2)
      = ∫ x in unitCube, ‖seriesFun (fun k => toCoeff a k i j) x‖ ^ 2 := by
    intro i j
    have h1 : (∑' k : Fin n → ℤ, ‖toCoeff a k i j‖ ^ 2)
        = ∑ m : box n N, ‖a m i j‖ ^ 2 := by
      rw [tsum_eq_sum (s := box n N) (f := fun k : Fin n → ℤ => ‖toCoeff a k i j‖ ^ 2)
        (fun k hk => by rw [toCoeff_apply_not_mem a hk]; simp)]
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [toCoeff_apply_mem a m.2]
    have h2 : (∑' k : Fin n → ℤ, ‖toCoeff a k i j‖ ^ 2)
        = ∫ x in unitCube, ‖seriesFun (fun k => toCoeff a k i j) x‖ ^ 2 :=
      (ens_integral_normSq_seriesFun _
        (summable_of_ne_finset_zero (s := box n N) (fun k hk => by
          rw [toCoeff_apply_not_mem a hk]; simp))).symm
    exact h1.symm.trans h2
  have hzero : ENormSqM 0 (seriesFunM (toCoeff a))
      = ∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube,
          ‖seriesFun (fun k => toCoeff a k i j) x‖ ^ 2 := by
    rw [ENormSqM]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [ENormSq_zero_eq]
    rfl
  have hnonneg : 0 ≤ ENormSqM k (seriesFunM (toCoeff a)) := by
    unfold ENormSqM ENormSq
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun l _ => integral_nonneg (fun x => by positivity))))
  calc (∑ i : Fin n, ∑ j : Fin n, ∑ m : box n N, ‖a m i j‖ ^ 2)
      = ∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube,
          ‖seriesFun (fun k => toCoeff a k i j) x‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        exact hpar i j
    _ = ENormSqM 0 (seriesFunM (toCoeff a)) := hzero.symm
    _ ≤ ENormSqFull k (seriesFunM (toCoeff a)) := by
        rw [ENormSqFull]
        exact le_add_of_nonneg_left hnonneg
    _ = bootE k a := rfl

/-- The determinant of the real part is nonzero as soon as the quadratic form is bounded below by a
positive multiple of `∑ vᵢ²`. -/
lemma det_bootForm_ne_zero {n N : ℕ} (a : Coeff n N) (x : Fin n → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ bootForm a x v) :
    (reMat (valExp a x)).det ≠ 0 := by
  rw [valExp_eq_seriesFunM a x]
  exact det_ne_zero_of_quadForm_le (reMat (seriesFunM (toCoeff a) x)) hlam h

/-- The set `W` on which the Galerkin jet stays non-degenerate, and on which the Galerkin
right-hand side is locally Lipschitz. -/
def bootW {n N : ℕ} : Set (Coeff n N) :=
  {a | ∀ x ∈ closedCube n, (reMat (valExp a x)).det ≠ 0}

lemma isOpen_bootW {n N : ℕ} : IsOpen (bootW (n := n) (N := N)) := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨r, hr, hr'⟩ := exists_radius_det_ne_zero a ha
  refine Filter.mem_of_superset (Metric.ball_mem_nhds a hr) (fun b hb => ?_)
  intro x hx
  exact hr' b (le_of_lt (by rwa [Metric.mem_ball] at hb)) x hx

/-- The Galerkin right-hand side is locally Lipschitz at every point of `W`, with an explicit
Lipschitz ball. -/
lemma locallyLipschitz_bootW {n N : ℕ}
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0})) :
    ∀ a ∈ bootW (n := n) (N := N), ∃ L : NNReal, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith L (rhsExp Φ) (Metric.closedBall a r) := by
  intro a ha
  obtain ⟨K, r, hr, hLip⟩ := Phi_jetExp_lipschitz Φ hΦ a ha
  obtain ⟨K', hK', L, hL⟩ := rhsExp_lipschitz Φ K r hr a hLip
  exact ⟨K', (r : ℝ), NNReal.coe_pos.mpr hr, hK'⟩

/-- **From a solution of the Galerkin ODE in coefficient space to the ODE in the form in which the
a priori estimates are stated.** -/
lemma hasDerivAt_toCoeff {n N : ℕ} {Φ : (Fin n → ℝ) × Jet n → MatC n}
    {α : ℝ → Coeff n N} {t : ℝ} (h : HasDerivAt α (rhsExp Φ (α t)) t) :
    ∀ (k' : Fin n → ℤ), k' ∈ box n N → ∀ i j : Fin n,
      HasDerivAt (fun σ => toCoeff (α σ) k' i j)
        (Work.Diff.STE.fourierCoeff
          (fun x => Φ (x, jetM (seriesFunM (toCoeff (α t))) x) i j) k') t := by
  intro k' hk' i j
  let Lc : Coeff n N →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℂ) j).comp
      ((ContinuousLinearMap.proj (φ := fun _ : Fin n => (Fin n → ℂ)) i).comp
        (ContinuousLinearMap.proj (φ := fun _ : box n N => MatC n) ⟨k', hk'⟩))
  have h1 : HasDerivAt (fun s : ℝ => α s ⟨k', hk'⟩ i j)
      ((rhsExp Φ (α t)) ⟨k', hk'⟩ i j) t := Lc.hasFDerivAt.comp_hasDerivAt t h
  have hfun : (fun s : ℝ => toCoeff (α s) k' i j) = fun s : ℝ => α s ⟨k', hk'⟩ i j := by
    funext s
    rw [toCoeff_apply_mem]
  have hkey : (rhsExp Φ (α t)) ⟨k', hk'⟩ i j
      = Work.Diff.STE.fourierCoeff
          (fun x => Φ (x, jetM (seriesFunM (toCoeff (α t))) x) i j) k' := by
    show Work.Diff.STE.fourierCoeff (fun x => Φ (x, jetExp (α t) x) i j)
        (⟨k', hk'⟩ : box n N).1 = _
    congr 1
    funext x
    rw [← jetM_seriesFunM_toCoeff (α t) x]
  rw [hfun, ← hkey]
  exact h1

theorem galerkin_bootstrap {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      (Set.univ ×ˢ {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 < B)
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hCauchy : ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ)
        (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t))
            ≤ (Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c 0)) + 1)
                * Real.exp (C * t) - 1)
    (hEll : ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ)
        (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c 0) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          (lam - M * t) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j)
    (τ : ℝ) (hτ : 0 < τ)
    (hτC : (B ^ 2 / 2 + 1) * Real.exp (C * τ) - 1 < B ^ 2)
    (hτM : M * τ < lam / 2)
    (N : ℕ) (c₀ : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hc₀ : ∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c₀ k' = 0)
    (hell₀ : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c₀ x) i j * v i * v j)
    (hE₀ : Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c₀) ≤ B ^ 2 / 2) :
    ∃ c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n, c 0 = c₀ ∧
      (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
        HasDerivAt (fun σ => c σ k' i j)
          (Work.Diff.STE.fourierCoeff (fun x =>
            Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ,
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B ^ 2) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) := by
  classical
  -- ## Setup
  set a₀ : Coeff n N := ofCoeff c₀ hc₀ with ha₀
  have hcoeff : toCoeff a₀ = c₀ := toCoeff_ofCoeff c₀ hc₀
  have hE₀' : bootE k a₀ ≤ B ^ 2 / 2 := by
    rw [bootE, hcoeff]
    exact hE₀
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  set β : ℝ := (B ^ 2 / 2 + 1) * Real.exp (C * τ) - 1 with hβdef
  have hβlt : β < B ^ 2 := by rw [hβdef]; exact hτC
  -- ## The invariant region
  set Kc : Set (Coeff n N) :=
    {a | bootE k a ≤ B ^ 2 ∧ ∀ x v, (lam / 2) * ∑ i, (v i) ^ 2 ≤ bootForm a x v} with hKc
  have ha₀K : a₀ ∈ Kc := by
    rw [hKc]
    refine ⟨le_trans hE₀' (by linarith [hB2]), ?_⟩
    intro x v
    have hv : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h := hell₀ x v
    rw [← hcoeff] at h
    unfold bootForm
    have hhalf : (lam / 2) * ∑ i, (v i) ^ 2 ≤ lam * ∑ i, (v i) ^ 2 := by
      nlinarith [hlam, hv]
    linarith
  -- ## Compactness of the invariant region
  have hKc_closed : IsClosed Kc := by
    rw [hKc]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_bootE continuous_const
    · have hset : (⋂ p : (Fin n → ℝ) × (Fin n → ℝ),
            {a : Coeff n N | (lam / 2) * ∑ i, (p.2 i) ^ 2 ≤ bootForm a p.1 p.2})
          = {a : Coeff n N | ∀ x v, (lam / 2) * ∑ i, (v i) ^ 2 ≤ bootForm a x v} := by
        ext a
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        exact ⟨fun h x v => h (x, v), fun h (p : (Fin n → ℝ) × (Fin n → ℝ)) => h p.1 p.2⟩
      have h2 : IsClosed (⋂ p : (Fin n → ℝ) × (Fin n → ℝ),
          {a : Coeff n N | (lam / 2) * ∑ i, (p.2 i) ^ 2 ≤ bootForm a p.1 p.2}) :=
        isClosed_iInter (fun p => isClosed_le continuous_const (continuous_bootForm_fixed p.1 p.2))
      rw [hset] at h2
      exact h2
  have hKc_sub : Kc ⊆ Metric.closedBall (0 : Coeff n N) B := by
    rw [hKc]
    intro a ha
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hB.le).mpr (fun m => ?_)
    refine (pi_norm_le_iff_of_nonneg hB.le).mpr (fun i => ?_)
    refine (pi_norm_le_iff_of_nonneg hB.le).mpr (fun j => ?_)
    have hsum := sum_norm_sq_le_bootE (n := n) (N := N) (k := k) a
    have h2 : ‖a m i j‖ ^ 2 ≤ ∑ i' : Fin n, ∑ j' : Fin n, ‖a m i' j'‖ ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun j' => ‖a m i j'‖ ^ 2)
          (fun j' _ => by positivity) (Finset.mem_univ j))
        (Finset.single_le_sum (f := fun i' => ∑ j', ‖a m i' j'‖ ^ 2)
          (fun i' _ => Finset.sum_nonneg (fun j' _ => by positivity)) (Finset.mem_univ i))
    have h3 : (∑ i' : Fin n, ∑ j' : Fin n, ‖a m i' j'‖ ^ 2)
        ≤ ∑ i' : Fin n, ∑ j' : Fin n, ∑ m' : box n N, ‖a m' i' j'‖ ^ 2 := by
      refine Finset.sum_le_sum (fun i' _ => ?_)
      refine Finset.sum_le_sum (fun j' _ => ?_)
      exact Finset.single_le_sum (f := fun m' : box n N => ‖a m' i' j'‖ ^ 2)
        (fun m' _ => by positivity) (Finset.mem_univ m)
    have h4 : ‖a m i j‖ ^ 2 ≤ B ^ 2 := le_trans (le_trans h2 h3) (le_trans hsum ha.1)
    nlinarith [h4, norm_nonneg (a m i j), hB.le]
  have hKc_cpt : IsCompact Kc :=
    (isCompact_closedBall (0 : Coeff n N) B).of_isClosed_subset hKc_closed hKc_sub
  -- ## The trapping argument: any solution keeps its energy below `B ^ 2` up to time `τ`
  have trapping : ∀ (T' : ℝ) (α : ℝ → Coeff n N), 0 ≤ T' → α 0 = a₀ →
      (∀ t ∈ Set.Icc 0 T', HasDerivAt α (rhsExp Φ (α t)) t) →
      ∀ t ∈ Set.Icc 0 T', t ≤ τ → bootE k (α t) ≤ B ^ 2 := by
    intro T' α hT' hα0 hαode
    have hsupp : ∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → toCoeff (α t) k' = 0 :=
      fun t k' hk' => toCoeff_apply_not_mem (α t) hk'
    have hell0 : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2
          ≤ ∑ i, ∑ j, reMat (seriesFunM (toCoeff (α 0)) x) i j * v i * v j := by
      intro x v
      rw [hα0, hcoeff]
      exact hell₀ x v
    have hstrict : ∀ t₀ ∈ Set.Icc 0 T', bootE k (α t₀) < B ^ 2 → ∃ δ > 0,
        ∀ s ∈ Set.Icc 0 T', |s - t₀| < δ → bootE k (α s) < B ^ 2 := by
      intro t₀ ht₀ hlt
      have hcont : ContinuousAt (fun s => bootE k (α s)) t₀ :=
        continuous_bootE.continuousAt.comp (hαode t₀ ht₀).continuousAt
      have hmem : {y : ℝ | y < B ^ 2} ∈ nhds (bootE k (α t₀)) := isOpen_Iio.mem_nhds hlt
      obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp (hcont.tendsto.eventually hmem)
      exact ⟨δ, hδ, fun s _ hsd => hδ' (by rw [Metric.mem_ball, Real.dist_eq]; exact hsd)⟩
    intro t htI hτt
    by_contra hcon
    have htbad : B ^ 2 < bootE k (α t) := not_le.mp hcon
    set S : Set ℝ := Set.Icc 0 (min T' τ) ∩ {s : ℝ | B ^ 2 < bootE k (α s)} with hS
    have hS₁ : ∀ s ∈ S, 0 ≤ s := fun s hs => by
      have h := hs
      rw [hS] at h
      exact h.1.1
    have hS₂ : ∀ s ∈ S, s ≤ min T' τ := fun s hs => by
      have h := hs
      rw [hS] at h
      exact h.1.2
    have hS₃ : ∀ s ∈ S, B ^ 2 < bootE k (α s) := fun s hs => by
      have h := hs
      rw [hS] at h
      exact h.2
    have hSne : S.Nonempty := ⟨t, ⟨⟨htI.1, le_min htI.2 hτt⟩, htbad⟩⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hS₁ s hs⟩
    set T₁ : ℝ := sInf S with hT₁def
    have hT₁le : T₁ ≤ min T' τ := by
      obtain ⟨s₁, hs₁⟩ := hSne
      exact le_trans (csInf_le hSbdd hs₁) (hS₂ s₁ hs₁)
    have hT₁ge : 0 ≤ T₁ := le_csInf hSne (fun s hs => hS₁ s hs)
    have hT₁leT' : T₁ ≤ T' := le_trans hT₁le (min_le_left _ _)
    have hT₁leτ : T₁ ≤ τ := le_trans hT₁le (min_le_right _ _)
    have hT₁Icc : T₁ ∈ Set.Icc 0 T' := ⟨hT₁ge, hT₁leT'⟩
    have hbelow : ∀ s ∈ Set.Ico 0 T₁, bootE k (α s) ≤ B ^ 2 := by
      intro s hs
      by_contra hc
      have hsS : s ∈ S := ⟨⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 hT₁le)⟩, not_le.mp hc⟩
      have hle := csInf_le hSbdd hsS
      linarith [hs.2]
    have hT₁pos : 0 < T₁ := by
      have hB2pos : 0 < B ^ 2 := pow_pos hB 2
      have h0 : bootE k (α 0) < B ^ 2 := by
        rw [hα0]
        exact lt_of_le_of_lt hE₀' (by linarith [hB2pos])
      obtain ⟨δ, hδ, hδ'⟩ := hstrict 0 ⟨le_rfl, hT'⟩ h0
      have hle : δ ≤ T₁ := le_csInf hSne (fun s hs => by
        by_contra hlt
        have hsT' : s ∈ Set.Icc 0 T' := ⟨hS₁ s hs, le_trans (hS₂ s hs) (min_le_left _ _)⟩
        have hmem := hδ' s hsT'
          (by rw [sub_zero, abs_of_nonneg (hS₁ s hs)]; exact not_le.mp hlt)
        linarith [hS₃ s hs, hmem])
      linarith
    have hT₁bnd : bootE k (α T₁) ≤ β := by
      have hode₁ : ∀ t₀ ∈ Set.Ico 0 T₁, ∀ k' ∈ box n N, ∀ i j,
          HasDerivAt (fun σ => toCoeff (α σ) k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, jetM (seriesFunM (toCoeff (α t₀))) x) i j) k') t₀ :=
        fun t₀ ht₀ k' hk' i j => hasDerivAt_toCoeff (Φ := Φ)
          (hαode t₀ ⟨ht₀.1, le_of_lt (lt_of_lt_of_le ht₀.2 hT₁leT')⟩) k' hk' i j
      have hellT₁ := hEll T₁ hT₁pos N (fun s => toCoeff (α s)) hode₁ hsupp hell0
        (fun t₀ ht₀ => hbelow t₀ ht₀)
      have hhalf : ∀ t₀ ∈ Set.Ico 0 T₁, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          (lam / 2) * ∑ i, (v i) ^ 2
            ≤ ∑ i, ∑ j, reMat (seriesFunM (toCoeff (α t₀)) x) i j * v i * v j := by
        intro t₀ ht₀ x v
        have h1 := hellT₁ t₀ ht₀ x v
        have hv : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
        have hMel : lam / 2 ≤ lam - M * t₀ := by
          have : M * t₀ ≤ M * τ :=
            mul_le_mul_of_nonneg_left (le_of_lt (lt_of_lt_of_le ht₀.2 hT₁leτ)) hM
          linarith [hτM]
        linarith [mul_le_mul_of_nonneg_right hMel hv]
      have hcau := hCauchy T₁ hT₁pos N (fun s => toCoeff (α s)) hode₁ hsupp hhalf
        (fun t₀ ht₀ => hbelow t₀ ht₀)
      have hcont : ContinuousAt (fun s => bootE k (α s)) T₁ :=
        continuous_bootE.continuousAt.comp (hαode T₁ hT₁Icc).continuousAt
      have hlim : Filter.Tendsto (fun s => bootE k (α s)) (nhdsWithin T₁ (Set.Iio T₁))
          (nhds (bootE k (α T₁))) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hmax : max 0 (T₁ - 1) < T₁ := max_lt hT₁pos (by linarith)
      have hle : bootE k (α T₁) ≤ (bootE k a₀ + 1) * Real.exp (C * T₁) - 1 := by
        refine le_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsLT hmax] with s hs
        have hs' : s ∈ Set.Ico 0 T₁ :=
          ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs.1), hs.2⟩
        have h2 : bootE k (α s) ≤ (bootE k a₀ + 1) * Real.exp (C * s) - 1 := by
          have h2' := hcau s hs'
          rw [show ENormSqFull k (seriesFunM (toCoeff (α 0))) = bootE k a₀ by
            rw [hα0]; rfl] at h2'
          exact h2'
        have h4 : Real.exp (C * s) ≤ Real.exp (C * T₁) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hs.2) hC)
        have h5 : 0 ≤ bootE k a₀ + 1 := by
          linarith [bootE_nonneg (k := k) a₀]
        nlinarith [h2, h4, h5]
      have h1 : bootE k a₀ + 1 ≤ B ^ 2 / 2 + 1 := by linarith [hE₀']
      have h2 : Real.exp (C * T₁) ≤ Real.exp (C * τ) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT₁leτ hC)
      calc bootE k (α T₁) ≤ (bootE k a₀ + 1) * Real.exp (C * T₁) - 1 := hle
        _ ≤ β := by
            rw [hβdef]
            have h4 := mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith [hE₀', hB2])
            nlinarith [h4]
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := hstrict T₁ hT₁Icc (lt_of_le_of_lt hT₁bnd hβlt)
    obtain ⟨s, hsS, hslt⟩ : ∃ s ∈ S, s < T₁ + δ₂ := by
      by_contra hcon'
      push_neg at hcon'
      have : T₁ + δ₂ ≤ T₁ := le_csInf hSne (fun s hs => hcon' s hs)
      linarith
    have hsge : T₁ ≤ s := csInf_le hSbdd hsS
    have hsT' : s ∈ Set.Icc 0 T' := ⟨hS₁ s hsS, le_trans (hS₂ s hsS) (min_le_left _ _)⟩
    have hmem := hδ₂' s hsT' (by rw [abs_of_nonneg (by linarith)]; linarith)
    linarith [hS₃ s hsS, hmem]
  -- ## Local Lipschitz data on the invariant region and uniform local existence
  have hloc : ∀ p ∈ Kc, ∃ L : NNReal, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith L (rhsExp Φ) (Metric.closedBall p r) := by
    intro p hp
    have hpW : p ∈ bootW (n := n) (N := N) := by
      intro x _
      exact det_bootForm_ne_zero p x (by linarith) (fun v => hp.2 x v)
    exact locallyLipschitz_bootW Φ hΦ p hpW
  obtain ⟨ρ, hρpos, hflow⟩ := exists_uniform_local_solution (F := rhsExp Φ) hKc_cpt hloc
  -- ## The induction
  have hind : ∀ m : ℕ, ∃ α : ℝ → Coeff n N, α 0 = a₀ ∧
      (∀ t ∈ Set.Icc 0 (min ((m : ℝ) * ρ) τ), HasDerivAt α (rhsExp Φ (α t)) t) ∧
      (∀ t ∈ Set.Icc 0 (min ((m : ℝ) * ρ) τ), bootE k (α t) ≤ B ^ 2) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨α, hα0, hαd⟩ := hflow a₀ ha₀K
      have hzero : min (((0 : ℕ) : ℝ) * ρ) τ = 0 := by
        rw [Nat.cast_zero, zero_mul, min_eq_left hτ.le]
      refine ⟨α, hα0, ?_, ?_⟩
      · intro t ht
        have ht0 : t = 0 := by
          have h1 := ht.2
          rw [hzero] at h1
          exact le_antisymm h1 ht.1
        rw [ht0]
        exact hαd 0 (by rw [abs_zero]; exact hρpos.le)
      · intro t ht
        have ht0 : t = 0 := by
          have h1 := ht.2
          rw [hzero] at h1
          exact le_antisymm h1 ht.1
        rw [ht0, hα0]
        exact le_trans hE₀' (by linarith [hB2])
    | succ m ih =>
      obtain ⟨α, hα0, hαode, hαE⟩ := ih
      by_cases hmτ : τ ≤ (m : ℝ) * ρ
      · have h1 : min (((m + 1 : ℕ) : ℝ) * ρ) τ = τ := by
          rw [min_eq_right]
          have hcast : ((m + 1 : ℕ) : ℝ) * ρ = (m : ℝ) * ρ + ρ := by push_cast; ring
          rw [hcast]; linarith [hmτ, hρpos.le]
        have h2 : min ((m : ℝ) * ρ) τ = τ := min_eq_right hmτ
        refine ⟨α, hα0, ?_, ?_⟩
        · intro t ht
          rw [h1] at ht
          exact hαode t (by rw [h2]; exact ht)
        · intro t ht
          rw [h1] at ht
          exact hαE t (by rw [h2]; exact ht)
      · have hmτ' : (m : ℝ) * ρ < τ := lt_of_not_ge hmτ
        set T : ℝ := (m : ℝ) * ρ with hT
        have hTmin : min T τ = T := min_eq_left hmτ'.le
        have hT0 : 0 ≤ T := by rw [hT]; positivity
        have hodeT : ∀ t ∈ Set.Icc 0 T, HasDerivAt α (rhsExp Φ (α t)) t := by
          intro t ht; exact hαode t (by rw [hTmin]; exact ht)
        have hET : ∀ t ∈ Set.Icc 0 T, bootE k (α t) ≤ B ^ 2 := by
          intro t ht; exact hαE t (by rw [hTmin]; exact ht)
        have hpell : ∀ x v, (lam / 2) * ∑ i, (v i) ^ 2 ≤ bootForm (α T) x v := by
          intro x v
          have hv : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
          rcases eq_or_lt_of_le hT0 with hT0eq | hT0pos
          · rw [hT0eq.symm, hα0]
            unfold bootForm
            have h := hell₀ x v
            rw [← hcoeff] at h
            have hhalf : (lam / 2) * ∑ i, (v i) ^ 2 ≤ lam * ∑ i, (v i) ^ 2 := by
              nlinarith [hlam, hv]
            linarith
          · have hsuppT : ∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → toCoeff (α t) k' = 0 :=
              fun t k' hk' => toCoeff_apply_not_mem (α t) hk'
            have hellT := hEll T hT0pos N (fun s => toCoeff (α s))
              (fun t₀ ht₀ k' hk' i j => hasDerivAt_toCoeff (Φ := Φ)
                (hodeT t₀ ⟨ht₀.1, le_of_lt ht₀.2⟩) k' hk' i j)
              hsuppT
              (fun x' v' => by rw [hα0, hcoeff]; exact hell₀ x' v')
              (fun t₀ ht₀ => hET t₀ ⟨ht₀.1, le_of_lt ht₀.2⟩)
            have hcont : ContinuousAt (fun s => bootForm (α s) x v) T :=
              (continuous_bootForm_fixed x v).continuousAt.comp
                (hodeT T ⟨hT0, le_rfl⟩).continuousAt
            have hlim : Filter.Tendsto (fun s => bootForm (α s) x v)
                (nhdsWithin T (Set.Iio T)) (nhds (bootForm (α T) x v)) :=
              hcont.tendsto.mono_left nhdsWithin_le_nhds
            have hmax : max 0 (T - 1) < T := max_lt hT0pos (by linarith)
            have hle : (lam - M * T) * ∑ i, (v i) ^ 2 ≤ bootForm (α T) x v := by
              refine ge_of_tendsto hlim ?_
              filter_upwards [Ioo_mem_nhdsLT hmax] with s hs
              have hs' : s ∈ Set.Ico 0 T :=
                ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs.1), hs.2⟩
              have h1 := hellT s hs' x v
              have h2 : lam - M * T ≤ lam - M * s := by
                have h3 : M * s ≤ M * T := mul_le_mul_of_nonneg_left (le_of_lt hs.2) hM
                linarith
              exact le_trans (mul_le_mul_of_nonneg_right h2 hv) h1
            have hMel : lam / 2 ≤ lam - M * T := by
              have h1 : M * T < lam / 2 :=
                lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmτ'.le hM) hτM
              linarith
            linarith [mul_le_mul_of_nonneg_right hMel hv]
        have hpK : α T ∈ Kc := ⟨hET T ⟨hT0, le_rfl⟩, hpell⟩
        obtain ⟨γ, hγ0, hγd⟩ := hflow (α T) hpK
        let α' : ℝ → Coeff n N := fun t => if t ≤ T then α t else γ (t - T)
        have hα'0 : α' 0 = a₀ := by
          dsimp only [α']
          rw [if_pos hT0]
          exact hα0
        have hα'T : α' T = α T := by
          dsimp only [α']
          rw [if_pos le_rfl]
        have hα'ode : ∀ t ∈ Set.Icc 0 (T + ρ), HasDerivAt α' (rhsExp Φ (α' t)) t := by
          intro t ht
          rcases lt_trichotomy t T with hlt | heq | hgt
          · have hev : α' =ᶠ[nhds t] α := by
              filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
              dsimp only [α']
              rw [if_pos hs.le]
            have hα't : α' t = α t := by
              dsimp only [α']
              rw [if_pos hlt.le]
            rw [hα't]
            exact (hodeT t ⟨ht.1, hlt.le⟩).congr_of_eventuallyEq hev
          · subst heq
            have hleft : HasDerivWithinAt α' (rhsExp Φ (α' T)) (Set.Iic T) T := by
              rw [hα'T]
              refine (((hodeT T ⟨hT0, le_rfl⟩).hasDerivWithinAt).mono (Set.subset_univ _)).congr
                ?_ ?_
              · intro s hs
                dsimp only [α']
                rw [if_pos (Set.mem_Iic.mp hs)]
              · exact hα'T
            have hright : HasDerivWithinAt α' (rhsExp Φ (α' T)) (Set.Ici T) T := by
              have hbase : HasDerivAt γ (rhsExp Φ (γ (T - T))) (T - T) := by
                rw [sub_self]
                exact hγd 0 (by rw [abs_zero]; exact hρpos.le)
              have h2 : HasDerivAt (fun s : ℝ => γ (s - T)) (rhsExp Φ (γ (T - T))) T :=
                HasDerivAt.comp_sub_const T T hbase
              have hγT : γ (T - T) = α' T := by
                rw [sub_self, hγ0]
                exact hα'T.symm
              rw [hγT] at h2
              refine h2.hasDerivWithinAt.congr ?_ ?_
              · intro s hs
                rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with h | h
                · rw [← h]
                  dsimp only [α']
                  rw [if_pos le_rfl, sub_self, hγ0]
                · dsimp only [α']
                  rw [if_neg (not_le.mpr h)]
              · dsimp only [α']
                rw [if_pos le_rfl, sub_self, hγ0]
            have hunion := hleft.union hright
            rw [Set.Iic_union_Ici] at hunion
            exact hunion.hasDerivAt Filter.univ_mem
          · have htval : α' t = γ (t - T) := by
              dsimp only [α']
              rw [if_neg (not_le.mpr hgt)]
            have hev : α' =ᶠ[nhds t] (fun s => γ (s - T)) := by
              filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
              dsimp only [α']
              rw [if_neg (not_le.mpr hs)]
            have hle : |t - T| ≤ ρ := by
              rw [abs_of_pos (sub_pos.mpr hgt)]
              linarith [ht.2]
            have hbase : HasDerivAt γ (rhsExp Φ (γ (t - T))) (t - T) := hγd (t - T) hle
            have h2 : HasDerivAt (fun s : ℝ => γ (s - T)) (rhsExp Φ (γ (t - T))) t :=
              HasDerivAt.comp_sub_const t T hbase
            rw [htval]
            exact h2.congr_of_eventuallyEq hev
        have htr := trapping (T + ρ) α' (by linarith [hT0, hρpos.le]) hα'0 hα'ode
        have hcast : (((m + 1 : ℕ) : ℝ) * ρ) = T + ρ := by rw [hT]; push_cast; ring
        refine ⟨α', hα'0, ?_, ?_⟩
        · intro t ht
          rw [hcast] at ht
          exact hα'ode t ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
        · intro t ht
          rw [hcast] at ht
          exact htr t ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩ (le_trans ht.2 (min_le_right _ _))
  -- ## Final assembly
  obtain ⟨m, hm⟩ : ∃ m : ℕ, τ ≤ (m : ℝ) * ρ := by
    obtain ⟨m, hm⟩ := exists_nat_ge (τ / ρ)
    refine ⟨m, ?_⟩
    rw [div_le_iff₀ hρpos] at hm
    linarith [hm]
  obtain ⟨α, hα0, hαode, hαE⟩ := hind m
  have hminτ : min ((m : ℝ) * ρ) τ = τ := min_eq_right hm
  have hsupp : ∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → toCoeff (α t) k' = 0 :=
    fun t k' hk' => toCoeff_apply_not_mem (α t) hk'
  have hodeτ : ∀ t ∈ Set.Ico 0 τ, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => toCoeff (α σ) k' i j)
        (Work.Diff.STE.fourierCoeff (fun x =>
          Φ (x, jetM (seriesFunM (toCoeff (α t))) x) i j) k') t :=
    fun t ht k' hk' i j => hasDerivAt_toCoeff (Φ := Φ)
      (hαode t (by rw [hminτ]; exact ⟨ht.1, le_of_lt ht.2⟩)) k' hk' i j
  have hEτ : ∀ t ∈ Set.Ico 0 τ, ENormSqFull k (seriesFunM (toCoeff (α t))) ≤ B ^ 2 :=
    fun t ht => hαE t (by rw [hminτ]; exact ⟨ht.1, le_of_lt ht.2⟩)
  have hellτ := hEll τ hτ N (fun s => toCoeff (α s)) hodeτ hsupp
    (fun x v => by rw [hα0, hcoeff]; exact hell₀ x v) hEτ
  refine ⟨fun t => toCoeff (α t), ?_, ?_, ?_, ?_, ?_⟩
  · show toCoeff (α 0) = c₀
    rw [hα0, hcoeff]
  · exact fun t k' hk' => hsupp t k' hk'
  · exact hodeτ
  · exact hEτ
  · intro t ht x v
    have h1 := hellτ t ht x v
    have hv : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hMel : lam / 2 ≤ lam - M * t := by
      have : M * t < lam / 2 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt ht.2) hM) hτM
      linarith
    linarith [mul_le_mul_of_nonneg_right hMel hv]

end

end Work.Diff.STE.flat
