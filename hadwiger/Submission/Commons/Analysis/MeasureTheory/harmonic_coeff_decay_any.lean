import Mathlib
import Submission.Commons.Analysis.MeasureTheory.sphere_laplacian_pairing
import Submission.Commons.Algebra.MvPolynomial.contDiff_eval

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory Metric Filter Bornology

namespace Commons.Analysis.MeasureTheory

noncomputable section

/-! ## Helper definitions for the radial (degree-zero homogeneous) extension

These repeat, in this file, the machinery of `harmonic_coeff_decay_uniform`, but
stated so that the polynomial `Y` may depend on the degree `k`. -/

/-- The `i`-th standard basis vector of `EuclideanSpace ℝ (Fin n)`. -/
private def evec {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1

/-- Radial projection `x ↦ ‖x‖⁻¹ • x`. -/
private def radProj {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖x‖⁻¹ • x

/-- Homogeneous-degree-zero extension of a function on the sphere. -/
private def radial {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ := fun x => f (radProj x)

/-- The explicit Laplacian `∑ᵢ ∂ᵢ∂ᵢ G`. -/
private def lapEx {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ G y (evec i)) x (evec i)

/-- The iterated chain `G₀ = radial p`, `G_{j+1} = radial (Δ G_j)`. -/
private def Gseq {n : ℕ} (p : EuclideanSpace ℝ (Fin n) → ℝ) :
    ℕ → (EuclideanSpace ℝ (Fin n) → ℝ)
  | 0 => radial p
  | (j + 1) => radial (lapEx (Gseq p j))

/-- The spherical function associated with a polynomial `Y`. -/
private def polyFun {n : ℕ} (Y : MvPolynomial (Fin n) ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
  fun θ => MvPolynomial.eval (fun i => (θ : EuclideanSpace ℝ (Fin n)) i) Y

/-! ## Basic properties of the radial extension -/

private lemma radial_apply_of_norm_eq_one {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) : radial f x = f x := by
  unfold radial radProj
  rw [hx, inv_one, one_smul]

private lemma radProj_smul {n : ℕ} {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    radProj (t • x) = radProj x := by
  unfold radProj
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [mul_comm t ‖x‖, mul_inv_rev, smul_smul]
  congr 1
  field_simp

private lemma radial_smul {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) : radial f (t • x) = radial f x := by
  unfold radial
  rw [radProj_smul ht x]

private lemma radProj_contDiffOn {n : ℕ} :
    ContDiffOn ℝ ⊤ (radProj : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      {x : EuclideanSpace ℝ (Fin n) | x ≠ 0} := by
  have hnorm : ContDiffOn ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) {x | x ≠ 0} :=
    fun x hx => (contDiffAt_norm ℝ (show x ≠ 0 from hx)).contDiffWithinAt
  have hinv : ContDiffOn ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖⁻¹) {x | x ≠ 0} :=
    hnorm.inv (fun x hx => norm_ne_zero_iff.mpr (show x ≠ 0 from hx))
  exact hinv.smul contDiff_id.contDiffOn

private lemma radProj_ne_zero {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    radProj x ≠ 0 := by
  unfold radProj
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hx

private lemma radial_contDiffOn {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ⊤ f {x : EuclideanSpace ℝ (Fin n) | x ≠ 0}) :
    ContDiffOn ℝ ⊤ (radial f) {x : EuclideanSpace ℝ (Fin n) | x ≠ 0} := by
  unfold radial
  refine hf.comp radProj_contDiffOn ?_
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  exact radProj_ne_zero hx

private lemma lapEx_contDiffOn {n : ℕ} {G : EuclideanSpace ℝ (Fin n) → ℝ}
    (hG : ContDiffOn ℝ ⊤ G {x : EuclideanSpace ℝ (Fin n) | x ≠ 0}) :
    ContDiffOn ℝ ⊤ (lapEx G) {x : EuclideanSpace ℝ (Fin n) | x ≠ 0} := by
  set s : Set (EuclideanSpace ℝ (Fin n)) := {x | x ≠ 0} with hs
  have hso : IsOpen s := isOpen_ne
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ G) s := hG.fderiv_of_isOpen hso (by simp)
  have hstep1 : ∀ i : Fin n, ContDiffOn ℝ ⊤ (fun y => fderiv ℝ G y (evec i)) s := by
    intro i
    have := hfd.clm_apply (contDiffOn_const (c := evec i))
    simpa using this
  have hstep2 : ∀ i : Fin n,
      ContDiffOn ℝ ⊤ (fun y => fderiv ℝ (fun z => fderiv ℝ G z (evec i)) y (evec i)) s := by
    intro i
    have hfdi : ContDiffOn ℝ ⊤ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ G z (evec i))) s := (hstep1 i).fderiv_of_isOpen hso (by simp)
    have := hfdi.clm_apply (contDiffOn_const (c := evec i))
    simpa using this
  unfold lapEx
  exact ContDiffOn.sum (fun i _ => hstep2 i)

private lemma Gseq_contDiffOn {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → ℝ}
    (hps : ContDiffOn ℝ ⊤ p {x : EuclideanSpace ℝ (Fin n) | x ≠ 0}) :
    ∀ m : ℕ, ContDiffOn ℝ ⊤ (Gseq p m) {x : EuclideanSpace ℝ (Fin n) | x ≠ 0} := by
  intro m
  induction m with
  | zero => exact radial_contDiffOn hps
  | succ m ih => exact radial_contDiffOn (lapEx_contDiffOn ih)

private lemma Gseq_smul {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → ℝ} :
    ∀ (m : ℕ) (t : ℝ), 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      Gseq p m (t • x) = Gseq p m x := by
  intro m
  induction m with
  | zero => intro t ht x; exact radial_smul p ht x
  | succ m ih => intro t ht x; exact radial_smul (lapEx (Gseq p m)) ht x

private lemma norm_coe_sphere {n : ℕ} (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  rw [← dist_zero_right, ← mem_sphere]
  exact θ.2

private lemma Gseq_succ_sphere {n : ℕ} {p : EuclideanSpace ℝ (Fin n) → ℝ} (m : ℕ)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Gseq p (m + 1) (θ : EuclideanSpace ℝ (Fin n)) =
      lapEx (Gseq p m) (θ : EuclideanSpace ℝ (Fin n)) := by
  show radial (lapEx (Gseq p m)) (θ : EuclideanSpace ℝ (Fin n)) = _
  rw [radial_apply_of_norm_eq_one _ (norm_coe_sphere θ)]

/-! ## Measure-theoretic helpers -/

private lemma memLp_of_continuous_compact {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [CompactSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Continuous f) : MemLp f 2 μ := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ (f '' (Set.univ : Set α) : Set ℝ), ‖x‖ ≤ C :=
    IsBounded.exists_norm_le (isCompact_univ.image_of_continuousOn hf.continuousOn).isBounded
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards with θ
  exact hC (f θ) ⟨θ, trivial, rfl⟩

private lemma abs_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {u v : α → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hv2 : ∫ a, (v a) ^ 2 ∂μ = 1) :
    |∫ a, u a * v a ∂μ| ≤ (∫ a, (u a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2) hpq
    (by simpa using hu) (by simpa using hv)
  have hv2' : ∫ a, ‖v a‖ ^ 2 ∂μ = (1 : ℝ) := by
    rw [← hv2]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
  have hu2' : ∫ a, ‖u a‖ ^ 2 ∂μ = ∫ a, (u a) ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
  have hholder' : ∫ a, ‖u a‖ * ‖v a‖ ∂μ ≤ (∫ a, (u a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simp only [Real.rpow_ofNat] at hholder
    rw [hv2'] at hholder
    rw [hu2'] at hholder
    rw [Real.one_rpow, mul_one] at hholder
    exact hholder
  calc |∫ a, u a * v a ∂μ|
      = ‖∫ a, u a * v a ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ a, ‖u a * v a‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ a, ‖u a‖ * ‖v a‖ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun a => ?_)
          simp only [norm_mul]
    _ ≤ (∫ a, (u a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := hholder'

private lemma continuous_polyFun {n : ℕ} (Y : MvPolynomial (Fin n) ℝ) :
    Continuous (polyFun Y) :=
  (Commons.Algebra.MvPolynomial.contDiff_eval Y).continuous.comp continuous_subtype_val

/-! ## The main theorem

The pairing identity of `sphere_laplacian_pairing` is iterated for the radial
extension of `p`; the iterated radial extension is bounded in `L²` on the sphere
independently of the polynomial `Y`, which yields the decay. -/

set_option linter.style.haveILetI false in
theorem harmonic_coeff_decay_any
    {n : ℕ} [Nonempty (Fin n)] (N : ℕ)
    (p : EuclideanSpace ℝ (Fin n) → ℝ)
    (hpcont : Continuous p)
    (hps : ContDiffOn ℝ ⊤ p {x : EuclideanSpace ℝ (Fin n) | x ≠ 0}) :
    ∃ C : ℝ, ∀ (k : ℕ) (Y : MvPolynomial (Fin n) ℝ),
      Y ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Y)) = 0 →
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) Y)^2
        ∂MeasureTheory.volume.toSphere) = 1 →
      |(∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          p (θ : EuclideanSpace ℝ (Fin n)) *
          MvPolynomial.eval (fun l : Fin n => (θ : EuclideanSpace ℝ (Fin n)) l) Y
        ∂MeasureTheory.volume.toSphere)|
        ≤ C * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by
  set S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  set μ : Measure S := MeasureTheory.volume.toSphere with hμdef
  haveI : IsFiniteMeasure μ := by rw [hμdef]; infer_instance
  have hnpos : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  set K : ℝ := (∫ θ, ((Gseq p N) (θ : EuclideanSpace ℝ (Fin n))) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
    with hKdef
  set K₀ : ℝ := (∫ θ, (p (θ : EuclideanSpace ℝ (Fin n))) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
    with hK₀def
  have hKnn : 0 ≤ K := by
    rw [hKdef]; exact Real.rpow_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _) _
  have hK₀nn : 0 ≤ K₀ := by
    rw [hK₀def]; exact Real.rpow_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _) _
  have hcontP : Continuous (fun θ : S => p (θ : EuclideanSpace ℝ (Fin n))) :=
    hpcont.comp continuous_subtype_val
  have hcontGN : Continuous (fun θ : S => (Gseq p N) (θ : EuclideanSpace ℝ (Fin n))) :=
    ((Gseq_contDiffOn hps N).continuousOn).comp_continuous continuous_subtype_val
      (fun θ => norm_ne_zero_iff.mp (by rw [norm_coe_sphere θ]; norm_num))
  have hmemP : MemLp (fun θ : S => p (θ : EuclideanSpace ℝ (Fin n))) 2 μ :=
    memLp_of_continuous_compact _ hcontP
  have hmemGN : MemLp (fun θ : S => (Gseq p N) (θ : EuclideanSpace ℝ (Fin n))) 2 μ :=
    memLp_of_continuous_compact _ hcontGN
  refine ⟨max K K₀ * (2 : ℝ) ^ N, fun k Y hYhom hYhar hYL2 => ?_⟩
  have hmemY : MemLp (polyFun Y) 2 μ :=
    memLp_of_continuous_compact _ (continuous_polyFun Y)
  by_cases hk1 : k ≤ 1
  · -- Small `k`: use the Cauchy–Schwarz bound for `p`.
    have hcs := abs_integral_mul_le hmemP hmemY hYL2
    have hb : |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)| ≤ K₀ := by
      rw [hK₀def]; exact hcs
    have ha1 : ((k : ℝ) + 1) ≤ 2 := by
      have : (k : ℝ) ≤ 1 := by exact_mod_cast hk1
      linarith
    have hpow2 : ((k : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) ha1 N
    have hle1 : (1 : ℝ) ≤ (2 : ℝ) ^ N * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by
      rw [zpow_neg, zpow_natCast]
      rw [le_mul_inv_iff₀ (by positivity)]
      simpa using hpow2
    calc |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|
        ≤ K₀ := hb
      _ ≤ max K K₀ := le_max_right _ _
      _ = max K K₀ * 1 := (mul_one _).symm
      _ ≤ max K K₀ * ((2 : ℝ) ^ N * ((k : ℝ) + 1) ^ (-(N : ℤ))) :=
            mul_le_mul_of_nonneg_left hle1 (le_max_of_le_left hKnn)
      _ = max K K₀ * (2 : ℝ) ^ N * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by ring
  · -- Large `k`: iterate the pairing identity.
    have hk2 : 2 ≤ k := by omega
    have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hlam : 0 < (k : ℝ) * ((k : ℝ) + (n : ℝ) - 2) := by
      have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
      have hknpos : (0 : ℝ) < (k : ℝ) + (n : ℝ) - 2 := by linarith
      exact mul_pos hkpos hknpos
    set lam : ℝ := (k : ℝ) * ((k : ℝ) + (n : ℝ) - 2) with hlamdef
    have hlampos : 0 < lam := hlam
    -- The iterated pairing identity.
    have key : ∀ m : ℕ,
        (∫ θ, (Gseq p m) (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)
          = (-((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2))) ^ m *
            (∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ) := by
      intro m
      induction m with
      | zero =>
          have h0 : (fun θ : S => (Gseq p 0) (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ)
              = (fun θ : S => p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ) := by
            funext θ
            rw [show Gseq p 0 = radial p from rfl,
              radial_apply_of_norm_eq_one p (norm_coe_sphere θ)]
          rw [h0, pow_zero, one_mul]
      | succ m ih =>
          have hp := sphere_laplacian_pairing (Gseq p m) (Gseq_contDiffOn hps m)
            (fun t x ht => Gseq_smul m t ht x) Y k (by omega) hYhom hYhar
          calc (∫ θ, (Gseq p (m + 1)) (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)
              = ∫ θ, (lapEx (Gseq p m)) (θ : EuclideanSpace ℝ (Fin n)) *
                  polyFun Y θ ∂μ := by
                refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
                dsimp only
                rw [Gseq_succ_sphere m θ]
            _ = -((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2)) *
                  (∫ θ, (Gseq p m) (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ) := by
                simpa only [lapEx, evec, polyFun] using hp
            _ = -((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2)) *
                  ((-((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2))) ^ m *
                    (∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)) := by
                rw [ih]
            _ = (-((k : ℝ) * ((k : ℝ) + (n : ℝ) - 2))) ^ (m + 1) *
                  (∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ) := by
                rw [pow_succ]; ring
    have hiter := key N
    have hcs := abs_integral_mul_le hmemGN hmemY hYL2
    have habs : |(-lam) ^ N| = lam ^ N := by
      rw [abs_pow, abs_neg, abs_of_pos hlampos]
    have hlamK : lam ^ N * |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|
        ≤ K := by
      have hAB : lam ^ N * |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|
          = |(∫ θ, (Gseq p N) (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)| := by
        rw [hiter, abs_mul, habs]
      rw [hAB, hKdef]
      exact hcs
    -- Convert to the stated bound.
    have ha2 : (2 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hapos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hkey : ((k : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * lam ^ N := by
      have h2lam : (k : ℝ) + 1 ≤ 2 * lam := by
        have hkn : (1 : ℝ) ≤ (k : ℝ) + (n : ℝ) - 2 := by linarith
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
        have hle : (k : ℝ) ≤ lam := by
          rw [hlamdef]
          have := mul_le_mul_of_nonneg_left hkn hk0
          simpa using this
        linarith
      calc ((k : ℝ) + 1) ^ N ≤ (2 * lam) ^ N := pow_le_pow_left₀ (by linarith) h2lam N
        _ = (2 : ℝ) ^ N * lam ^ N := by rw [mul_pow]
    have hstep : ((k : ℝ) + 1) ^ N *
        |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)| ≤ (2 : ℝ) ^ N * K := by
      calc ((k : ℝ) + 1) ^ N *
            |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|
          ≤ ((2 : ℝ) ^ N * lam ^ N) *
            |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)| :=
            mul_le_mul_of_nonneg_right hkey (abs_nonneg _)
        _ = (2 : ℝ) ^ N * (lam ^ N *
            |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|) := by ring
        _ ≤ (2 : ℝ) ^ N * K := mul_le_mul_of_nonneg_left hlamK (by positivity)
    have hfinal : |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|
        ≤ (2 : ℝ) ^ N * K * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by
      have h := mul_le_mul_of_nonneg_left hstep
        (inv_nonneg.mpr (pow_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1) N))
      rw [zpow_neg, zpow_natCast]
      have hcancel : (((k : ℝ) + 1) ^ N)⁻¹ *
          (((k : ℝ) + 1) ^ N *
            |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|)
          = |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)| :=
        inv_mul_cancel_left₀ (by positivity) _
      rw [hcancel] at h
      calc |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|
          ≤ (((k : ℝ) + 1) ^ N)⁻¹ * ((2 : ℝ) ^ N * K) := h
        _ = (2 : ℝ) ^ N * K * (((k : ℝ) + 1) ^ N)⁻¹ := by ring
    calc |(∫ θ, p (θ : EuclideanSpace ℝ (Fin n)) * polyFun Y θ ∂μ)|
        ≤ (2 : ℝ) ^ N * K * ((k : ℝ) + 1) ^ (-(N : ℤ)) := hfinal
      _ ≤ (2 : ℝ) ^ N * max K K₀ * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by
            have h1 : K ≤ max K K₀ := le_max_left _ _
            have h2 : 0 ≤ (2 : ℝ) ^ N * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by
              rw [zpow_neg, zpow_natCast]; positivity
            calc (2 : ℝ) ^ N * K * ((k : ℝ) + 1) ^ (-(N : ℤ))
                = K * ((2 : ℝ) ^ N * ((k : ℝ) + 1) ^ (-(N : ℤ))) := by ring
              _ ≤ max K K₀ * ((2 : ℝ) ^ N * ((k : ℝ) + 1) ^ (-(N : ℤ))) :=
                    mul_le_mul_of_nonneg_right h1 h2
              _ = (2 : ℝ) ^ N * max K K₀ * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by ring
      _ = max K K₀ * (2 : ℝ) ^ N * ((k : ℝ) + 1) ^ (-(N : ℤ)) := by ring

end

end Commons.Analysis.MeasureTheory
