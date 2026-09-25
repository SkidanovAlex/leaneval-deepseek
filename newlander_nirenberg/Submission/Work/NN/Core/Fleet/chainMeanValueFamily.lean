import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Lev.nnMoserBoost
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.Fleet.prodBoundQuant
import Submission.Work.NN.Core.Lev.moserTheta
import Submission.Work.NN.Core.Lev.ofReal_norm_le_liminf_eLpNorm_on
import Submission.Work.NN.Core.Lev.exists_polydisc_cutoff_lipschitz
import Submission.Work.NN.Core.volume_polydisc
import Submission.Work.NN.Core.Fleet.cmvfProdBound
import Submission.Work.NN.Core.Fleet.cmvfLevelGrowth

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

namespace Work.NN.Core.Fleet

/-! ## The geometry: the geometric family `Λ j` and the chain family `R j m` -/

/-- The geometric family of multiradii `Λ j = σ + (ρ★ - σ)(1 - 2^{-j})` (`j : ℕ`): `Λ 0 = σ` and
`Λ j ↑ ρ★`. -/
def Lam {n : ℕ} (σ ρstar : Fin n → ℝ) (j : ℕ) : Fin n → ℝ :=
  fun i => σ i + (ρstar i - σ i) * (1 - (1 / 2 : ℝ) ^ j)

/-- The chain multiradii `R j m = Λ j + (Λ (j+1) - Λ j)·2^{-m}`, interpolating between
`Λ (j+1)` (at `m = 0`) and `Λ j` (as `m → ∞`). -/
def Rrad {n : ℕ} (σ ρstar : Fin n → ℝ) (j m : ℕ) : Fin n → ℝ :=
  fun i => Lam σ ρstar j i + (Lam σ ρstar (j+1) i - Lam σ ρstar j i) * (1 / 2 : ℝ) ^ m

lemma Lam_def {n : ℕ} (σ ρstar : Fin n → ℝ) (j : ℕ) :
    Lam σ ρstar j = fun i => σ i + (ρstar i - σ i) * (1 - (1 / 2 : ℝ) ^ j) := rfl

@[simp] lemma Lam_zero {n : ℕ} (σ ρstar : Fin n → ℝ) : Lam σ ρstar 0 = σ := by
  funext i; simp [Lam]

@[simp] lemma Rrad_zero {n : ℕ} (σ ρstar : Fin n → ℝ) (j : ℕ) :
    Rrad σ ρstar j 0 = Lam σ ρstar (j+1) := by
  funext i; simp [Rrad]

lemma Lam_le_of_le {n : ℕ} {σ ρstar : Fin n → ℝ} (hσρ : ∀ i, σ i ≤ ρstar i) {j j' : ℕ}
    (h : j ≤ j') (i : Fin n) : Lam σ ρstar j i ≤ Lam σ ρstar j' i := by
  have h2 : (1 / 2 : ℝ) ^ j' ≤ (1 / 2 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have h3 : 0 ≤ ρstar i - σ i := sub_nonneg.mpr (hσρ i)
  simp only [Lam]
  nlinarith [mul_le_mul_of_nonneg_left h2 h3, h3]

lemma Lam_self_le {n : ℕ} {σ ρstar : Fin n → ℝ} (hσρ : ∀ i, σ i ≤ ρstar i) (j : ℕ) (i : Fin n) :
    σ i ≤ Lam σ ρstar j i := by
  have := Lam_le_of_le (σ := σ) (ρstar := ρstar) hσρ (Nat.zero_le j) i
  simpa using this

lemma Lam_lt_ρstar {n : ℕ} {σ ρstar : Fin n → ℝ} (hσρ : ∀ i, σ i < ρstar i)
    (j : ℕ) (i : Fin n) : Lam σ ρstar j i < ρstar i := by
  have h3 : 0 < ρstar i - σ i := sub_pos.mpr (hσρ i)
  have h4 : (0:ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have h5 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [Lam]
  nlinarith

lemma Lam_pos {n : ℕ} {σ ρstar : Fin n → ℝ} (hσ0 : ∀ i, 0 < σ i) (hσρ : ∀ i, σ i < ρstar i)
    (j : ℕ) (i : Fin n) : 0 < Lam σ ρstar j i :=
  lt_of_lt_of_le (hσ0 i) (Lam_self_le (fun i => (hσρ i).le) j i)

lemma Lam_succ_sub {n : ℕ} (σ ρstar : Fin n → ℝ) (j : ℕ) (i : Fin n) :
    Lam σ ρstar (j+1) i - Lam σ ρstar j i = (ρstar i - σ i) * (1 / 2 : ℝ) ^ (j+1) := by
  simp only [Lam]
  have hp : (1 / 2 : ℝ) ^ (j+1) = (1 / 2 : ℝ) ^ j * (1 / 2) := by rw [pow_succ]
  rw [hp]; ring

lemma Lam_le_Rrad {n : ℕ} {σ ρstar : Fin n → ℝ} (hσρ : ∀ i, σ i ≤ ρstar i) (j m : ℕ)
    (i : Fin n) : Lam σ ρstar j i ≤ Rrad σ ρstar j m i := by
  have h2 : 0 ≤ Lam σ ρstar (j+1) i - Lam σ ρstar j i := by
    have := Lam_le_of_le (σ := σ) (ρstar := ρstar) hσρ (Nat.le_succ j) i
    linarith
  have h3 : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
  simp only [Rrad]
  nlinarith [mul_nonneg h2 h3]

lemma Rrad_le_Lam_succ {n : ℕ} {σ ρstar : Fin n → ℝ} (hσρ : ∀ i, σ i ≤ ρstar i) (j m : ℕ)
    (i : Fin n) : Rrad σ ρstar j m i ≤ Lam σ ρstar (j+1) i := by
  have h2 : 0 ≤ Lam σ ρstar (j+1) i - Lam σ ρstar j i := by
    have := Lam_le_of_le (σ := σ) (ρstar := ρstar) hσρ (Nat.le_succ j) i
    linarith
  have h3 : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  simp only [Rrad]
  nlinarith [mul_le_mul_of_nonneg_left h3 h2]

lemma Rrad_lt_ρstar {n : ℕ} {σ ρstar : Fin n → ℝ} (hσρ : ∀ i, σ i < ρstar i)
    (j m : ℕ) (i : Fin n) : Rrad σ ρstar j m i < ρstar i := by
  refine lt_of_le_of_lt (Rrad_le_Lam_succ (fun i => (hσρ i).le) j m i) ?_
  exact Lam_lt_ρstar hσρ (j+1) i

lemma Rrad_pos {n : ℕ} {σ ρstar : Fin n → ℝ} (hσ0 : ∀ i, 0 < σ i) (hσρ : ∀ i, σ i < ρstar i)
    (j m : ℕ) (i : Fin n) : 0 < Rrad σ ρstar j m i :=
  lt_of_lt_of_le (hσ0 i) (le_trans (Lam_self_le (fun i => (hσρ i).le) j i)
    (Lam_le_Rrad (fun i => (hσρ i).le) j m i))

lemma Rrad_antitone {n : ℕ} {σ ρstar : Fin n → ℝ} (hσρ : ∀ i, σ i ≤ ρstar i) (j m : ℕ)
    (i : Fin n) : Rrad σ ρstar j (m+1) i ≤ Rrad σ ρstar j m i := by
  have h2 : 0 ≤ Lam σ ρstar (j+1) i - Lam σ ρstar j i := by
    have := Lam_le_of_le (σ := σ) (ρstar := ρstar) hσρ (Nat.le_succ j) i
    linarith
  have h3 : (1 / 2 : ℝ) ^ (m+1) ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ m)
  simp only [Rrad]
  nlinarith [mul_le_mul_of_nonneg_left h3 h2]

lemma Rrad_gap {n : ℕ} (σ ρstar : Fin n → ℝ) (j m : ℕ) (i : Fin n) :
    Rrad σ ρstar j m i - Rrad σ ρstar j (m+1) i
      = (ρstar i - σ i) * (1 / 2 : ℝ) ^ (j + m + 2) := by
  have hpm : (1 / 2 : ℝ) ^ m = 2 * (1 / 2 : ℝ) ^ (m+1) := by rw [pow_succ]; ring
  have hpow : (1 / 2 : ℝ) ^ (j + m + 2)
      = (1 / 2 : ℝ) ^ (j+1) * (1 / 2 : ℝ) ^ (m+1) := by
    rw [← pow_add]; congr 1; ring
  simp only [Rrad, Lam_succ_sub]
  rw [hpow, hpm]
  ring


/-! ## Elementary measure-theoretic and differential helpers -/

/-- A polydisc in `ℂⁿ` has finite volume. -/
lemma polydisc_volume_ne_top {n : ℕ} (ρ : Fin n → ℝ) :
    MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) ρ) ≠ ⊤ := by
  rw [volume_polydisc]
  exact (ENNReal.prod_lt_top fun j _ =>
    ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top).ne

/-- A single real number dominating the volume of `polydisc 0 ρstar`. -/
def VolB {n : ℕ} (ρstar : Fin n → ℝ) : ℝ :=
  max 1 (MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) ρstar)).toReal

lemma VolB_pos {n : ℕ} (ρstar : Fin n → ℝ) : 0 < VolB ρstar :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma VolB_nonneg {n : ℕ} (ρstar : Fin n → ℝ) : 0 ≤ VolB ρstar := (VolB_pos ρstar).le

lemma volume_polydisc_le_VolB {n : ℕ} {ρstar S : Fin n → ℝ} (hS : ∀ i, S i ≤ ρstar i) :
    MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) S) ≤ ENNReal.ofReal (VolB ρstar) := by
  calc MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) S)
      ≤ MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) ρstar) :=
        measure_mono (Work.CR.Flat.polydisc_mono hS)
    _ = ENNReal.ofReal (MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) ρstar)).toReal :=
        (ENNReal.ofReal_toReal (polydisc_volume_ne_top ρstar)).symm
    _ ≤ ENNReal.ofReal (VolB ρstar) := ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **Descent in the Lebesgue exponent**, paying the volume of the polydisc: if `p ≤ q` then the
`L^p`-seminorm on `polydisc 0 S` is bounded by the `L^q`-seminorm times `V^{1/p - 1/q}`, where `V`
dominates the volume of the polydisc. -/
lemma eLpNorm_le_volume_rpow {n : ℕ} {S : Fin n → ℝ} {u : Cn n → ℂ} {V : ℝ} (hV : 0 ≤ V)
    (hvol : MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) S) ≤ ENNReal.ofReal V)
    {p q : ENNReal} (hpq : p ≤ q) (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (hqtop : q ≠ ⊤)
    (hmeas : AEStronglyMeasurable u (MeasureTheory.volume.restrict
      (Work.CR.Flat.polydisc (0 : Cn n) S))) :
    MeasureTheory.eLpNorm u p (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc (0 : Cn n) S))
      ≤ ENNReal.ofReal (V ^ (1 / p.toReal - 1 / q.toReal)) *
          MeasureTheory.eLpNorm u q
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc (0 : Cn n) S)) := by
  set μ := MeasureTheory.volume.restrict (Work.CR.Flat.polydisc (0 : Cn n) S) with hμ
  have h1 := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) hpq hmeas
  have hμuniv : μ Set.univ = MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) S) := by
    rw [hμ, MeasureTheory.Measure.restrict_apply_univ]
  have hpt : p.toReal ≤ q.toReal := ENNReal.toReal_mono hqtop hpq
  have hp0' : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hc0 : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    have : 1 / q.toReal ≤ 1 / p.toReal := one_div_le_one_div_of_le hp0' hpt
    linarith
  have h2 : (μ Set.univ) ^ (1 / p.toReal - 1 / q.toReal)
      ≤ ENNReal.ofReal (V ^ (1 / p.toReal - 1 / q.toReal)) := by
    rw [hμuniv]
    calc (MeasureTheory.volume (Work.CR.Flat.polydisc (0 : Cn n) S))
            ^ (1 / p.toReal - 1 / q.toReal)
        ≤ (ENNReal.ofReal V) ^ (1 / p.toReal - 1 / q.toReal) :=
          ENNReal.rpow_le_rpow hvol hc0
      _ = ENNReal.ofReal (V ^ (1 / p.toReal - 1 / q.toReal)) :=
          ENNReal.ofReal_rpow_of_nonneg hV hc0
  calc MeasureTheory.eLpNorm u p μ
      ≤ MeasureTheory.eLpNorm u q μ * (μ Set.univ) ^ (1 / p.toReal - 1 / q.toReal) := h1
    _ ≤ MeasureTheory.eLpNorm u q μ * ENNReal.ofReal (V ^ (1 / p.toReal - 1 / q.toReal)) :=
        mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal (V ^ (1 / p.toReal - 1 / q.toReal)) * MeasureTheory.eLpNorm u q μ :=
        mul_comm _ _

/-- The norm of the real differential is unchanged by complexification. -/
lemma norm_fderiv_ofReal_eq {n : ℕ} (χ : Cn n → ℝ) (x : Cn n) (hχ : DifferentiableAt ℝ χ x) :
    ‖fderiv ℝ (fun z => (χ z : ℂ)) x‖ = ‖fderiv ℝ χ x‖ := by
  have hcomp : fderiv ℝ (fun z => (χ z : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ χ x) :=
    (Complex.ofRealCLM.hasFDerivAt.comp x hχ.hasFDerivAt).fderiv
  rw [hcomp]
  refine le_antisymm ?_ ?_
  · calc ‖Complex.ofRealCLM.comp (fderiv ℝ χ x)‖ ≤ ‖Complex.ofRealCLM‖ * ‖fderiv ℝ χ x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ χ x‖ := by rw [Complex.ofRealCLM_norm, one_mul]
  · have h2 : (Complex.reCLM.comp (Complex.ofRealCLM.comp (fderiv ℝ χ x))) = fderiv ℝ χ x := by
      ext v; simp
    calc ‖fderiv ℝ χ x‖ = ‖Complex.reCLM.comp (Complex.ofRealCLM.comp (fderiv ℝ χ x))‖ := by
          rw [h2]
      _ ≤ ‖Complex.reCLM‖ * ‖Complex.ofRealCLM.comp (fderiv ℝ χ x)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖Complex.ofRealCLM.comp (fderiv ℝ χ x)‖ := by rw [Complex.reCLM_norm, one_mul]

/-! ## The Moser exponent `θ = (2n)'` in the form used by the integer chain -/

lemma moserTheta_eq {n : ℕ} (hn : 0 < n) :
    Work.NN.Core.Lev.moserTheta n = (2 * (n : ℝ)) / (2 * (n : ℝ) - 1) := by
  have hp1 : (1 : NNReal) < ((2 * n : ℕ) : NNReal) := by
    rw [← NNReal.coe_lt_coe]
    have : (1 : ℕ) < 2 * n := by omega
    exact_mod_cast this
  have hc : ((((2 * n : ℕ) : NNReal)) : ℝ).HolderConjugate (Work.NN.Core.Lev.moserTheta n) := by
    have := NNReal.HolderConjugate.coe (NNReal.HolderConjugate.conjExponent hp1)
    simpa [Work.NN.Core.Lev.moserTheta] using this
  rw [Real.HolderConjugate.conjugate_eq hc]
  push_cast
  ring

/-- `(2n-1)·(θ - 1) = 1` for `θ = moserTheta n`. -/
lemma kbase_mul_moserTheta_sub_one {n : ℕ} (hn : 0 < n) :
    ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n - 1) = 1 := by
  have h1 : (1 : ℝ) ≤ 2 * (n : ℝ) := by
    have : (1 : ℕ) ≤ 2 * n := by omega
    exact_mod_cast this
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hne : (2 * (n : ℝ) - 1) ≠ 0 := by intro h; linarith
  rw [moserTheta_eq hn, Nat.cast_sub (by omega : 1 ≤ 2 * n)]
  push_cast
  field_simp
  ring

/-! ## The cutoffs for the chain family -/

/-- **Cutoffs adapted to the chain family `R j m`.** There are `K > 0`, `L ≥ 1` such that for every
`j m` there is a smooth cutoff equal to `1` on the closed polydisc of multiradius `R j (m+1)`,
supported in the polydisc of multiradius `R j m`, with `‖∇χ‖ ≤ K·L^{j+m}`. -/
lemma exists_cutoff_Rrad {n : ℕ} (hn : 0 < n) {σ ρstar : Fin n → ℝ} (hσ0 : ∀ i, 0 < σ i)
    (hσρ : ∀ i, σ i < ρstar i) :
    ∃ K L : ℝ, 0 < K ∧ 1 ≤ L ∧ ∀ (j m : ℕ), ∃ χ : Cn n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Work.CR.Flat.polydisc (0 : Cn n) (Rrad σ ρstar j m) ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z, (∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i) → χ z = 1) ∧
      (∀ z, ‖fderiv ℝ χ z‖ ≤ K * L ^ (j + m)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set σmin : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin n => σ i) with hσmindef
  have hσminpos : 0 < σmin := (Finset.lt_inf'_iff _).2 fun i _ => hσ0 i
  set ρmax : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin n => ρstar i) with hρmaxdef
  have hρmaxpos : 0 < ρmax :=
    lt_of_lt_of_le ((hσ0 ⟨0, hn⟩).trans (hσρ ⟨0, hn⟩)) (Finset.le_sup' _ (Finset.mem_univ _))
  set Dmin : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin n => ρstar i - σ i) with hDmindef
  have hDminpos : 0 < Dmin := (Finset.lt_inf'_iff _).2 fun i _ => sub_pos.mpr (hσρ i)
  have hDminle : ∀ i, Dmin ≤ ρstar i - σ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨Kc, hKcpos, pc, hpcpos, Hcut⟩ :=
    Work.NN.Core.Lev.exists_polydisc_cutoff_lipschitz (n := n) hn
    (α := (1 : ℝ) / 2) (by norm_num) (by norm_num) (Rmin := σmin) hσminpos (Rmax := ρmax) hρmaxpos
  set L : ℝ := (2 : ℝ) ^ pc with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Real.one_le_rpow (by norm_num) hpcpos.le
  refine ⟨Kc * (1 + (Dmin / 2) ^ (-pc) * L ^ 2), L, by positivity, hL1, ?_⟩
  intro j m
  set N : ℕ := j + m + 2 with hNdef
  set ε : ℝ := (Dmin / 2) * (2 : ℝ) ^ (-(N : ℝ)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hRlo : ∀ i, σmin ≤ Rrad σ ρstar j (m+1) i := by
    intro i
    refine le_trans ?_ (Lam_le_Rrad (fun i => (hσρ i).le) j (m+1) i)
    exact le_trans (Finset.inf'_le _ (Finset.mem_univ i))
      (Lam_self_le (fun i => (hσρ i).le) j i)
  have hRhi : ∀ i, Rrad σ ρstar j (m+1) i ≤ ρmax := by
    intro i
    exact le_trans (le_of_lt (Rrad_lt_ρstar hσρ j (m+1) i))
      (Finset.le_sup' _ (Finset.mem_univ i))
  obtain ⟨χ, hχcd, hχrng, hχone, hχzero, hχgrad, _⟩ := Hcut (Rrad σ ρstar j (m+1)) ε hRlo hRhi hεpos
  -- `ε` is smaller than the gap `R j m - R j (m+1)`, componentwise.
  have hgap : ∀ i, Rrad σ ρstar j (m+1) i + ε < Rrad σ ρstar j m i := by
    intro i
    have hg := Rrad_gap σ ρstar j m i
    have hle : ε < (ρstar i - σ i) * (1 / 2 : ℝ) ^ N := by
      rw [hεdef]
      have h2 : (2 : ℝ) ^ (-(N : ℝ)) = (1 / 2 : ℝ) ^ N := by
        rw [show (2 : ℝ) ^ (-(N : ℝ)) = ((2 : ℝ) ^ (N : ℝ))⁻¹ from Real.rpow_neg (by norm_num) _,
          Real.rpow_natCast, ← inv_pow]
        norm_num
      rw [h2]
      have hD : Dmin / 2 < ρstar i - σ i := by
        have := hDminle i
        linarith
      exact mul_lt_mul_of_pos_right hD (by positivity)
    have hgap2 : Rrad σ ρstar j (m+1) i
        + (ρstar i - σ i) * (1 / 2 : ℝ) ^ N = Rrad σ ρstar j m i := by
      have h2 : N = j + m + 2 := rfl
      linarith [hg]
    linarith [hgap2]
  have hsupp : tsupport χ ⊆ {z : Cn n | ∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε} := by
    have h1 : Function.support χ ⊆ {z : Cn n | ∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε} := by
      intro z hz
      rw [Function.mem_support] at hz
      by_contra hcon
      obtain ⟨i, hi⟩ := not_forall.mp hcon
      exact hz (hχzero z ⟨i, le_of_lt (lt_of_not_ge hi)⟩)
    have h2 : IsClosed {z : Cn n | ∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε} := by
      rw [show {z : Cn n | ∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε}
          = ⋂ i, {z : Cn n | ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε} from by ext z; simp]
      exact isClosed_iInter fun i => isClosed_le ((continuous_apply i).norm) continuous_const
    show closure (Function.support χ) ⊆ _
    exact closure_minimal h1 h2
  have hsupp2 : tsupport χ ⊆ Work.CR.Flat.polydisc (0 : Cn n) (Rrad σ ρstar j m) := by
    intro z hz i
    have h1 : ∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε := hsupp hz
    simpa using lt_of_le_of_lt (h1 i) (hgap i)
  have hbig : IsCompact {z : Cn n | ∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε} := by
    have heq : {z : Cn n | ∀ i, ‖z i‖ ≤ Rrad σ ρstar j (m+1) i + ε}
        = Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) (Rrad σ ρstar j (m+1) i + ε)) := by
      ext z; simp [Metric.mem_closedBall, dist_eq_norm]
    rw [heq]
    exact isCompact_univ_pi fun i => isCompact_closedBall _ _
  have hcomp : HasCompactSupport χ := hbig.of_isClosed_subset (isClosed_tsupport χ) hsupp
  have hLN : L ^ N = L ^ 2 * L ^ (j + m) := by
    rw [hNdef, show j + m + 2 = 2 + (j + m) by omega, pow_add]
  have hεpow : ε ^ (-pc) = (Dmin / 2) ^ (-pc) * (L ^ 2 * L ^ (j + m)) := by
    have hpow2 : ((2 : ℝ) ^ (-(N : ℝ))) ^ (-pc) = L ^ N := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (-(N : ℝ)) * (-pc) = pc * (N : ℝ) by ring]
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) pc (N : ℝ), Real.rpow_natCast,
        ← hLdef]
    calc ε ^ (-pc)
        = ((Dmin / 2) * (2 : ℝ) ^ (-(N : ℝ))) ^ (-pc) := by rw [hεdef]
      _ = (Dmin / 2) ^ (-pc) * ((2 : ℝ) ^ (-(N : ℝ))) ^ (-pc) :=
          Real.mul_rpow (by positivity) (Real.rpow_nonneg (by norm_num) _)
      _ = (Dmin / 2) ^ (-pc) * L ^ N := by rw [hpow2]
      _ = (Dmin / 2) ^ (-pc) * (L ^ 2 * L ^ (j + m)) := by rw [hLN]
  refine ⟨χ, (contDiff_all_iff_nat.2 hχcd) ⊤, hcomp, hsupp2, hχrng, hχone, ?_⟩
  intro z
  have hχ1 : ContDiff ℝ 1 χ := (contDiff_all_iff_nat.2 hχcd) 1
  have hz := hχgrad z
  rw [norm_fderiv_ofReal_eq χ z (hχ1.contDiffAt.differentiableAt (by norm_num))] at hz
  refine hz.trans ?_
  have hK0 : 0 ≤ Kc := hKcpos.le
  have hL2 : (1 : ℝ) ≤ L ^ (j + m) := one_le_pow₀ hL1
  have ha : 0 ≤ (Dmin / 2) ^ (-pc) * L ^ 2 := by positivity
  have hstep : (1 : ℝ) + (Dmin / 2) ^ (-pc) * (L ^ 2 * L ^ (j + m))
      ≤ (1 + (Dmin / 2) ^ (-pc) * L ^ 2) * L ^ (j + m) := by
    have h0 : (0 : ℝ) ≤ 1 + (Dmin / 2) ^ (-pc) * L ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hL2 h0
    nlinarith [h1, hL2]
  calc Kc * (1 + ε ^ (-pc))
      = Kc * (1 + (Dmin / 2) ^ (-pc) * (L ^ 2 * L ^ (j + m))) := by rw [hεpow]
    _ ≤ Kc * ((1 + (Dmin / 2) ^ (-pc) * L ^ 2) * L ^ (j + m)) :=
        mul_le_mul_of_nonneg_left hstep hKcpos.le
    _ = Kc * (1 + (Dmin / 2) ^ (-pc) * L ^ 2) * L ^ (j + m) := by ring


/-! ## The integer Moser level sequence -/

/-- The integer Moser level sequence: `k 0 = 2n-1`, `k (m+1) = ⌊k m · (2n)'⌋`. -/
def lvl (n : ℕ) : ℕ → ℕ
  | 0 => 2 * n - 1
  | (m+1) => ⌊(lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n⌋₊

@[simp] lemma lvl_zero (n : ℕ) : lvl n 0 = 2 * n - 1 := rfl

lemma lvl_succ (n : ℕ) (m : ℕ) :
    lvl n (m+1) = ⌊(lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n⌋₊ := rfl

/-- **Step A of the Moser chain for the integer-level power Caccioppoli family.**
If `u : ℂⁿ → ℂ` is `C¹` on `polydisc 0 ρstar` and satisfies the integer-level power Caccioppoli
inequality with constant `C₀` there, then for the increasing geometric family of polydiscs
`Λ j := (fun i => σ i + (ρstar i - σ i) * (1 - (1/2)^j))` one has, with constants `A, B` depending
only on `n, σ, ρstar, C₀`,
`‖u z‖ ≤ A * B^j * ‖u‖_{L^{2(2n-1)}(polydisc 0 (Λ (j+1)))}` for all `z ∈ polydisc 0 (Λ j)`. -/
theorem chainMeanValueFamily {n : ℕ} (hn : 0 < n) {σ ρstar : Fin n → ℝ} (hσ0 : ∀ j, 0 < σ j)
    (hσρ : ∀ j, σ j < ρstar j) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A B : ℝ, 0 < A ∧ 1 ≤ B ∧
      ∀ (u : Work.NN.Core.Cn n → ℂ),
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρstar) →
        (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρstar → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρstar, (φ z)^2 *
              (∑ j, (‖Work.CR.Flat.dCoord j (fun w => (u w)^k) z‖^2
                   + ‖Work.CR.Flat.dbarCoord j (fun w => (u w)^k) z‖^2))
            ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρstar,
                ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k) →
        ∀ j : ℕ, ∀ z ∈ Work.CR.Flat.polydisc 0 (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^j)),
          ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal (A * B^j) *
            MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (2 * (n:ℝ) - 1)))
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0
                (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^(j+1))))) := by
  have hσρle : ∀ i, σ i ≤ ρstar i := fun i => (hσρ i).le
  have hθ1 : 1 < Work.NN.Core.Lev.moserTheta n := Work.NN.Core.Lev.one_lt_moserTheta hn
  have hθ0 : 0 < Work.NN.Core.Lev.moserTheta n := lt_trans zero_lt_one hθ1
  have hk1 : 1 ≤ 2 * n - 1 := by omega
  have hKθ : ((2 * n - 1 : ℕ) : ℝ) * (Work.NN.Core.Lev.moserTheta n - 1) = 1 :=
    kbase_mul_moserTheta_sub_one hn
  obtain ⟨c, ρ, hcpos, hρ1, hgrowth, hkpos⟩ :=
    cmvfLevelGrowth (θ := Work.NN.Core.Lev.moserTheta n) (K := 2 * n - 1) hθ1 hk1 hKθ
      (k := lvl n) rfl (fun m => rfl)
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ1
  obtain ⟨Kc, Lc, hKcpos, hLc1, Hcut⟩ := exists_cutoff_Rrad hn hσ0 hσρ
  obtain ⟨C, hCpos, Hboost⟩ := Work.NN.Core.Lev.nnMoserBoost hn hC₀
  have hC0 : 0 ≤ C := hCpos.le
  have hKc0 : 0 ≤ Kc := hKcpos.le
  have hLc0 : 0 ≤ Lc := le_trans zero_le_one hLc1
  have hrm1 : 0 < ρ - 1 := by linarith
  have h1mrho : 0 < 1 - 1 / ρ := by
    rw [sub_pos, div_lt_one hρ0]; exact hρ1
  set sB : ℝ := 1 / (c * (1 - 1 / ρ)) with hsBdef
  set sL : ℝ := ρ / (c * (ρ - 1) ^ 2) with hsLdef
  have hsB0 : 0 ≤ sB := by
    rw [hsBdef]; exact (one_div_pos.mpr (mul_pos hcpos h1mrho)).le
  have hsL0 : 0 ≤ sL := by
    rw [hsLdef]; exact (div_pos hρ0 (mul_pos hcpos (pow_pos hrm1 2))).le
  set V : ℝ := VolB ρstar with hVdef
  have hV1 : 1 ≤ V := le_max_left _ _
  have hV0 : 0 ≤ V := le_trans zero_le_one hV1
  set B₁ : ℝ := C * (1 + Kc) + 1 with hB₁def
  have hB₁1 : 1 ≤ B₁ := by rw [hB₁def]; nlinarith [hC0, hKc0]
  have hB₁0 : 0 < B₁ := lt_of_lt_of_le zero_lt_one hB₁1
  set σδ : ℝ := 1 / (2 * c * (ρ - 1)) with hσδdef
  refine ⟨B₁ ^ sB * (max 1 Lc) ^ sL * V ^ σδ, Lc ^ sB, ?_, ?_, ?_⟩
  · have h1 : 0 < B₁ ^ sB := Real.rpow_pos_of_pos hB₁0 _
    have h2 : 0 < (max 1 Lc) ^ sL := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < V ^ σδ := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hV1) _
    positivity
  · exact Real.one_le_rpow hLc1 hsB0
  intro u hu hH j z hz
  have hlvl_nn : ∀ m, (0:ℝ) ≤ (lvl n m : ℝ) := fun m => Nat.cast_nonneg _
  have hlvl_pos : ∀ m, (0:ℝ) < (lvl n m : ℝ) := fun m => by exact_mod_cast hkpos m
  have hθc : ∀ m, 0 ≤ (lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n :=
    fun m => mul_nonneg (hlvl_nn m) hθ0.le
  -- the base norm
  set N : ENNReal := MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (2 * (n : ℝ) - 1)))
      (MeasureTheory.volume.restrict
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1)))) with hNdef
  have hNcast : (2 * (2 * (n : ℝ) - 1)) = 2 * (((2 * n - 1 : ℕ)) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]; push_cast; ring
  set bfun : ℕ → ℝ := fun m => C * (1 + Kc * Lc ^ (j + m)) + 1 with hbfundef
  have hbfun_nonneg : ∀ m, 0 ≤ bfun m := by
    intro m; rw [hbfundef]
    have : (0:ℝ) ≤ C * (1 + Kc * Lc ^ (j + m)) := by positivity
    linarith
  have hbfun1 : ∀ m, 1 ≤ bfun m := by
    intro m; rw [hbfundef]
    have : (0:ℝ) ≤ C * (1 + Kc * Lc ^ (j + m)) := by positivity
    linarith
  set δfun : ℕ → ℝ := fun m => 1 / (2 * (lvl n (m+1) : ℝ))
      - 1 / (2 * ((lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n)) with hδfundef
  set Pj : ℕ → ENNReal := fun M =>
      (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ)))) *
      (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m))) with hPjdef
  -- ## the chain
  have hchain : ∀ M, MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n M : ℝ)))
        (MeasureTheory.volume.restrict
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M)))
      ≤ (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
        * (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m))) * N := by
    intro M
    induction M with
    | zero =>
      rw [hNdef]
      simp only [Finset.range_zero, Finset.prod_empty, one_mul]
      rw [lvl_zero, ← hNcast, Rrad_zero]
    | succ M ih =>
      obtain ⟨χ, hχcd, hχcs, hχsupp, hχrng, hχone, hχgrad⟩ := Hcut j M
      have hχnn : ∀ z, 0 ≤ χ z := fun z => (hχrng z).1
      have hχle1 : ∀ z, χ z ≤ 1 := fun z => (hχrng z).2
      have hρpos : ∀ i, 0 < ρstar i := fun i => (hσ0 i).trans (hσρ i)
      have hrs : ∀ i, Rrad σ ρstar j (M+1) i < Rrad σ ρstar j M i := by
        intro i
        have h2 := Rrad_gap σ ρstar j M i
        have h3 : 0 < (ρstar i - σ i) * (1 / 2 : ℝ) ^ (j + M + 2) :=
          mul_pos (sub_pos.mpr (hσρ i)) (by positivity)
        linarith
      have hsρ : ∀ i, Rrad σ ρstar j M i < ρstar i := fun i => Rrad_lt_ρstar hσρ j M i
      have hsρ' : ∀ i, Rrad σ ρstar j (M+1) i < ρstar i := fun i => Rrad_lt_ρstar hσρ j (M+1) i
      have hL0 : 0 ≤ Kc * Lc ^ (j + M) := by positivity
      have hboost := Hboost (ρ := ρstar) hρpos hu hH (r := Rrad σ ρstar j (M+1))
        (s := Rrad σ ρstar j M) hrs hsρ hχcd hχcs hχsupp hχnn hχle1 hχone
        (L := Kc * Lc ^ (j + M)) hL0 hχgrad (lvl n M) (hkpos M)
      have hboost' : MeasureTheory.eLpNorm u
            (ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n)))
            (MeasureTheory.volume.restrict
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1))))
          ≤ ENNReal.ofReal (bfun M) ^ (1 / (2 * (lvl n M : ℝ))) *
            MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n M : ℝ)))
              (MeasureTheory.volume.restrict
                (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M))) := by
        refine hboost.trans (mul_le_mul' ?_ le_rfl)
        have hb : C * (1 + Kc * Lc ^ (j + M)) ≤ bfun M := by rw [hbfundef]; linarith
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hb) (by positivity)
      have hvolfac : MeasureTheory.volume
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))
          ≤ ENNReal.ofReal V := by
        rw [hVdef]; exact volume_polydisc_le_VolB (fun i => (hsρ' i).le)
      have hmeas : AEStronglyMeasurable u (MeasureTheory.volume.restrict
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))) :=
        ((hu.mono (Work.CR.Flat.polydisc_mono (fun i => (hsρ' i).le))).continuousOn).aestronglyMeasurable
          (Work.CR.Flat.isOpen_polydisc _ _).measurableSet
      have hpq : ENNReal.ofReal (2 * (lvl n (M+1) : ℝ))
          ≤ ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n)) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : (lvl n (M+1) : ℝ) ≤ (lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n := by
          rw [lvl_succ]; exact Nat.floor_le (hθc M)
        linarith
      have hdesc := eLpNorm_le_volume_rpow (S := Rrad σ ρstar j (M+1)) (u := u) (V := V)
        hV0 hvolfac hpq (ne_of_gt (ENNReal.ofReal_pos.mpr (by
          have h := hlvl_pos (M+1); positivity)))
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hmeas
      have hp' : (ENNReal.ofReal (2 * (lvl n (M+1) : ℝ))).toReal = 2 * (lvl n (M+1) : ℝ) :=
        ENNReal.toReal_ofReal (by positivity)
      have hq' : (ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n))).toReal
          = 2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n) :=
        ENNReal.toReal_ofReal (by positivity)
      rw [hp', hq'] at hdesc
      have hdesc' : MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n (M+1) : ℝ)))
            (MeasureTheory.volume.restrict
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1))))
          ≤ ENNReal.ofReal (V ^ δfun M) *
            MeasureTheory.eLpNorm u
              (ENNReal.ofReal (2 * ((lvl n M : ℝ) * Work.NN.Core.Lev.moserTheta n)))
              (MeasureTheory.volume.restrict
                (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j (M+1)))) := by
        rw [hδfundef]; exact hdesc
      have hgoal : (∏ m ∈ Finset.range (M+1), ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
            * (∏ m ∈ Finset.range (M+1), ENNReal.ofReal (V ^ (δfun m))) * N
          = ENNReal.ofReal (V ^ δfun M) *
              (ENNReal.ofReal (bfun M) ^ (1 / (2 * (lvl n M : ℝ)))
                * (((∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
                    * (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m)))) * N)) := by
        rw [Finset.prod_range_succ, Finset.prod_range_succ]
        ac_rfl
      rw [hgoal]
      exact hdesc'.trans (mul_le_mul' le_rfl (hboost'.trans (mul_le_mul' le_rfl ih)))
  -- ## the uniform bound on the product
  have hprodBound : ∀ M, (∏ m ∈ Finset.range M, bfun m ^ (1 / (2 * (lvl n m : ℝ))))
      ≤ B₁ ^ sB * (Lc ^ sB) ^ j * (max 1 Lc) ^ sL := by
    intro M
    have hbnd : ∀ m, bfun m ≤ (B₁ * Lc^j) * Lc^m := by
      intro m
      have hX1 : (1:ℝ) ≤ Lc^j * Lc^m := by
        have h1 : (1:ℝ) ≤ Lc^j := one_le_pow₀ hLc1
        have h2 : (1:ℝ) ≤ Lc^m := one_le_pow₀ hLc1
        nlinarith
      have hpoly : C * (1 + Kc * (Lc^j * Lc^m)) + 1
          ≤ (C * (1 + Kc) + 1) * (Lc^j * Lc^m) := by
        have hCX : C ≤ C * (Lc^j * Lc^m) := by nlinarith [hX1, hC0]
        have hfac1 : C * (1 + Kc * (Lc^j * Lc^m)) + 1 = C + C * Kc * (Lc^j * Lc^m) + 1 := by ring
        have hfac2 : (C * (1 + Kc) + 1) * (Lc^j * Lc^m)
            = C * (Lc^j * Lc^m) + C * Kc * (Lc^j * Lc^m) + (Lc^j * Lc^m) := by ring
        rw [hfac1, hfac2]
        linarith
      calc bfun m = C * (1 + Kc * Lc ^ (j + m)) + 1 := by rw [hbfundef]
        _ = C * (1 + Kc * (Lc^j * Lc^m)) + 1 := by rw [pow_add]
        _ ≤ (C * (1 + Kc) + 1) * (Lc^j * Lc^m) := hpoly
        _ = (B₁ * Lc^j) * Lc^m := by rw [hB₁def]; ring
    have hb := cmvfProdBound (p := ρ) (c := c) (B := B₁ * Lc^j) (L := Lc) hρ1 hcpos
      (by have h1 : (0:ℝ) < B₁ := hB₁0
          have h2 : (0:ℝ) < Lc := lt_of_lt_of_le zero_lt_one hLc1
          positivity) hLc1
      (m := fun m => 2 * lvl n m)
      (fun m => by have h := hgrowth m; push_cast; linarith)
      (fun m => by have h := hkpos m; omega)
      (b := bfun) (fun m => hbfun_nonneg m) hbnd M
    have hX1 : (1:ℝ) ≤ B₁ * Lc^j := by
      have h1 : (1:ℝ) ≤ Lc^j := one_le_pow₀ hLc1
      nlinarith [hB₁1, h1]
    have h1 : (max 1 (B₁ * Lc^j)) ^ sB ≤ (B₁ * Lc^j) ^ sB :=
      Real.rpow_le_rpow (by positivity) (max_le hX1 le_rfl) hsB0
    have h2 : (B₁ * Lc^j)^sB = B₁^sB * (Lc^sB)^j := by
      rw [Real.mul_rpow (le_of_lt hB₁0) (by positivity : (0:ℝ) ≤ Lc^j)]
      congr 1
      rw [show Lc ^ j = Lc ^ ((j:ℝ)) from (Real.rpow_natCast Lc j).symm,
        ← Real.rpow_mul hLc0, show ((j:ℝ) * sB) = sB * (j:ℝ) by ring,
        Real.rpow_mul hLc0, Real.rpow_natCast]
    have e1 : (max 1 (B₁ * Lc^j)) ^ (1 / (c * (1 - 1 / ρ)))
        = (max 1 (B₁ * Lc^j)) ^ sB := by rw [hsBdef]
    have e2 : (max 1 Lc) ^ (ρ / (c * (ρ - 1) ^ 2)) = (max 1 Lc) ^ sL := by rw [hsLdef]
    have heq : (∏ j ∈ Finset.range M, bfun j ^ (1 / (2 * (lvl n j : ℝ))))
        = ∏ j ∈ Finset.range M, bfun j ^ (1 / ((2 * lvl n j : ℕ) : ℝ)) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [show ((2 * lvl n j : ℕ) : ℝ) = 2 * (lvl n j : ℝ) by push_cast; ring]
    rw [← heq, e1, e2] at hb
    refine hb.trans ?_
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hPbound : ∀ M, (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
        * (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m)))
      ≤ ENNReal.ofReal ((B₁ ^ sB * (max 1 Lc) ^ sL * V ^ σδ) * (Lc ^ sB) ^ j) := by
    intro M
    have h1 : (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
        = ENNReal.ofReal (∏ m ∈ Finset.range M, bfun m ^ (1 / (2 * (lvl n m : ℝ)))) := by
      have hstep : (∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m) ^ (1 / (2 * (lvl n m : ℝ))))
          = ∏ m ∈ Finset.range M, ENNReal.ofReal (bfun m ^ (1 / (2 * (lvl n m : ℝ)))) :=
        Finset.prod_congr rfl (fun m _ => ENNReal.ofReal_rpow_of_nonneg
          (hbfun_nonneg m) (by positivity))
      rw [hstep, ← ENNReal.ofReal_prod_of_nonneg (fun m _ => Real.rpow_nonneg (hbfun_nonneg m) _)]
    have hδ0 : ∀ m, 0 ≤ δfun m := by
      intro m
      have h2 : (lvl n (m+1) : ℝ) ≤ (lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n := by
        rw [lvl_succ]; exact Nat.floor_le (hθc m)
      have ha : (0:ℝ) < 2 * (lvl n (m+1) : ℝ) := by
        have h := hlvl_pos (m+1); linarith
      have hb : 2 * (lvl n (m+1) : ℝ) ≤ 2 * ((lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n) :=
        by linarith [h2]
      have h6 := one_div_le_one_div_of_le ha hb
      rw [hδfundef]
      simp only [one_div] at h6 ⊢
      linarith
    have h2 : (∏ m ∈ Finset.range M, ENNReal.ofReal (V ^ (δfun m)))
        = ENNReal.ofReal (V ^ (∑ m ∈ Finset.range M, δfun m)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun m _ => Real.rpow_nonneg hV0 _),
        ← Real.rpow_sum_of_nonneg hV0 (fun m _ => hδ0 m)]
    have hδle : ∀ m, δfun m ≤ (1 / (2 * c * ρ)) * (ρ⁻¹)^m := by
      intro m
      have hsub : (0:ℝ) ≤ 1 / (2 * ((lvl n m : ℝ) * Work.NN.Core.Lev.moserTheta n)) :=
        (one_div_pos.mpr (mul_pos (by norm_num) (mul_pos (hlvl_pos m) hθ0))).le
      have h1 : δfun m ≤ 1 / (2 * (lvl n (m+1) : ℝ)) := by rw [hδfundef]; linarith
      have hg := hgrowth (m+1)
      have h2 : (1:ℝ) / (2 * (lvl n (m+1) : ℝ)) ≤ 1 / (2 * (c * ρ^(m+1))) := by
        exact one_div_le_one_div_of_le (by
            have h1 : (0:ℝ) < c := hcpos
            have h2 : (0:ℝ) < ρ^(m+1) := pow_pos hρ0 _
            positivity) (by linarith [hg])
      have h3 : (1:ℝ) / (2 * (c * ρ^(m+1))) = (1 / (2 * c * ρ)) * (ρ⁻¹)^m := by
        rw [pow_succ, inv_pow]
        have hcρ : c * ρ ≠ 0 := ne_of_gt (mul_pos hcpos hρ0)
        field_simp
        try ring
      linarith
    have hsum : ∑ m ∈ Finset.range M, δfun m ≤ σδ := by
      have hρinv : ‖(ρ⁻¹ : ℝ)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ0), ← one_div, div_lt_one hρ0]
        exact hρ1
      have hsumm : Summable (fun m : ℕ => (1 / (2 * c * ρ)) * (ρ⁻¹)^m) :=
        (summable_geometric_of_norm_lt_one hρinv).mul_left _
      have h4 : ∑ m ∈ Finset.range M, (1 / (2 * c * ρ)) * (ρ⁻¹)^m ≤ σδ := by
        have h5 : ∑ m ∈ Finset.range M, (1 / (2 * c * ρ)) * (ρ⁻¹)^m
            ≤ ∑' m : ℕ, (1 / (2 * c * ρ)) * (ρ⁻¹)^m :=
          Summable.sum_le_tsum _ (fun m _ => by positivity) hsumm
        have h6 : ∑' m : ℕ, (1 / (2 * c * ρ)) * (ρ⁻¹)^m = σδ := by
          rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hρinv, hσδdef]
          have hcρ : c * (ρ - 1) ≠ 0 := ne_of_gt (mul_pos hcpos hrm1)
          have hcρρ : 2 * c * ρ ≠ 0 := by positivity
          field_simp
          try ring
        linarith
      exact (Finset.sum_le_sum (fun m _ => hδle m)).trans h4
    have hVp : V ^ (∑ m ∈ Finset.range M, δfun m) ≤ V ^ σδ :=
      Real.rpow_le_rpow_of_exponent_le hV1 hsum
    have hVnn : (0:ℝ) ≤ V ^ (∑ m ∈ Finset.range M, δfun m) := Real.rpow_nonneg hV0 _
    rw [h1, h2, ← ENNReal.ofReal_mul
      (Finset.prod_nonneg (fun m _ => Real.rpow_nonneg (hbfun_nonneg m) _))]
    apply ENNReal.ofReal_le_ofReal
    calc (∏ m ∈ Finset.range M, bfun m ^ (1 / (2 * (lvl n m : ℝ))))
          * V ^ (∑ m ∈ Finset.range M, δfun m)
        ≤ (B₁ ^ sB * (Lc ^ sB) ^ j * (max 1 Lc) ^ sL) * V ^ σδ :=
          mul_le_mul (hprodBound M) hVp hVnn (by positivity)
      _ = (B₁ ^ sB * (max 1 Lc) ^ sL * V ^ σδ) * (Lc ^ sB) ^ j := by ring
  -- ## the pointwise bound
  have hz' : z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1)) :=
    Work.CR.Flat.polydisc_mono (fun i => Lam_le_of_le hσρle (Nat.le_succ j) i) hz
  have hρ'pos : ∀ i, 0 < Lam σ ρstar (j+1) i := fun i => Lam_pos hσ0 hσρ (j+1) i
  have hu' : ContinuousOn u (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1))) :=
    (hu.mono (Work.CR.Flat.polydisc_mono (fun i => (Lam_lt_ρstar hσρ (j+1) i).le))).continuousOn
  obtain ⟨r, hrpos, hballj⟩ := Metric.mem_nhds_iff.mp
    ((Work.CR.Flat.isOpen_polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar j)).mem_nhds hz)
  have hball : Metric.ball z r ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Lam σ ρstar (j+1)) :=
    hballj.trans (Work.CR.Flat.polydisc_mono (fun i => Lam_le_of_le hσρle (Nat.le_succ j) i))
  have hballR : ∀ M, Metric.ball z r ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M) :=
    fun M => hballj.trans (Work.CR.Flat.polydisc_mono (fun i => Lam_le_Rrad hσρle j M i))
  have hE1 : ∀ M : ℕ, (1:ℝ) ≤ 2 * (lvl n M : ℝ) := by
    intro M
    have h1 : (1:ℝ) ≤ (lvl n M : ℝ) := by exact_mod_cast hkpos M
    linarith
  have hEtop : Filter.Tendsto (fun M : ℕ => 2 * (lvl n M : ℝ)) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun M : ℕ => c * ρ ^ M) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hρ1).const_mul_atTop hcpos
    refine Filter.tendsto_atTop_mono (fun M => ?_) h1
    have h2 := hgrowth M
    linarith
  have hlim := Work.NN.Core.Lev.ofReal_norm_le_liminf_eLpNorm_on hn (u := u)
    (ρ := Lam σ ρstar (j+1)) hρ'pos hu' hz' hrpos hball
    (E := fun M : ℕ => 2 * (lvl n M : ℝ)) hE1 hEtop
  refine hlim.trans ?_
  have hbound : ∀ M : ℕ, MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (lvl n M : ℝ)))
        (MeasureTheory.volume.restrict (Metric.ball z r))
      ≤ ENNReal.ofReal ((B₁ ^ sB * (max 1 Lc) ^ sL * V ^ σδ) * (Lc ^ sB) ^ j) * N := by
    intro M
    have hνμ : MeasureTheory.volume.restrict (Metric.ball z r)
        ≤ MeasureTheory.volume.restrict
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (Rrad σ ρstar j M)) :=
      MeasureTheory.Measure.restrict_mono (hballR M) le_rfl
    have h1 := MeasureTheory.eLpNorm_mono_measure u hνμ
      (p := ENNReal.ofReal (2 * (lvl n M : ℝ)))
    exact h1.trans ((hchain M).trans (mul_le_mul' (hPbound M) le_rfl))
  refine le_trans (Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)) ?_
  rw [Filter.liminf_const, hNdef]
  rfl

end Work.NN.Core.Fleet
