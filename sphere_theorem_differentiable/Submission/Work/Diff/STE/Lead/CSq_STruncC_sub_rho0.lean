import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.BNorm_prelim
import Submission.Work.Diff.STE.CSq_trunc_sub_le
import Submission.Work.Diff.STE.B3.STruncR_CSq_le
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.Lead.CSq_trunc_sub_le_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/- Route: `STruncC ρ ε f z = ofReal (re (seriesFun D z))` with `D = trunc ρ ε c`, `c = fourierCoeff (per f)`
(`per f z = ∑' m, ofReal (f (z + iVec m))`).  The function `u z = ((STruncC ρ ε f z - per f z).re : ℂ)`
equals `seriesFun (E - c)` where `E k = (D k + star (D (-k)))/2` (symmetrization): use
`re_seriesFun_eq_seriesFun_symm` twice (for `D` and for `c`, the latter after `seriesFun c = per f`,
i.e. `flat.seriesFun_fourierCoeff`, from smoothness+periodicity of `per f` via
`periodization_contDiff_periodic`) and the linearity of `seriesFun`.  Hence
`fourierCoeff u = E - c` (`flat.fourierCoeff_seriesFun`, needing `ℓ¹`-summability from smoothness:
`summable_weighted_fourierCoeff_of_contDiff` + `summable_norm_of_CSq`).  Then
`CSq s (E - c) = CSq s (symm (D - c)) ≤ CSq s (D - c) ≤ 4 * ε^2 * CSq (s+1) c` by
`Work.Diff.STE.B3.CSq_symm_le` (in `Diff/STE/B3/STruncR_CSq_le`, note `symm` is linear) and
`Work.Diff.STE.Lead.CSq_trunc_sub_le_bound`. -/
theorem CSq_STruncC_sub_rho0
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (C : ℝ)
    (hρC : ∀ y : ι → ℝ, (ρ y - 1) ^ 2 ≤ C ^ 2 * ∑ i, (y i) ^ 2)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (s : ℕ) (f : (ι → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
        (((Work.Diff.STE.STruncC ρ ε f z
          - (∑' m : ι → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))).re : ℝ) : ℂ)))
      ≤ C ^ 2 * ε ^ 2 * Work.Diff.STE.CSq (s + 1)
          (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
            ∑' m : ι → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))) := by
  classical
  -- ### Vocabulary
  set g : (ι → ℝ) → ℂ :=
    fun z => ∑' m : ι → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) with hgdef
  set c : (ι → ℤ) → ℂ := Work.Diff.STE.fourierCoeff g with hcdef
  set D : (ι → ℤ) → ℂ := Work.Diff.STE.trunc ρ ε c with hDdef
  set u : (ι → ℝ) → ℂ := fun z =>
    (((Work.Diff.STE.STruncC ρ ε f z
      - (∑' m : ι → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))).re : ℝ) : ℂ) with hudef
  -- ### Smoothness and periodicity of the periodization `g`
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hsuppC : Function.support (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    exact hfsupp (by simpa [Function.mem_support] using hy)
  obtain ⟨hgcd, hgper0, -⟩ :=
    Work.Diff.STE.periodization_contDiff_periodic (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) hfC hsuppC
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by rw [hgdef]; exact hgcd
  have hgper : Work.Diff.STE.Periodic1 g := by rw [hgdef]; exact hgper0
  -- ### Summability of the Fourier coefficients `c` of `g`
  have hCw : ∀ M : ℕ, Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ M * ‖c k‖ ^ 2) := by
    intro M
    rw [hcdef]
    exact Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hgper M
  obtain ⟨s', hs'⟩ : ∃ s' : ℕ, Fintype.card ι < 2 * s' := ⟨Fintype.card ι + 1, by omega⟩
  have hCl1 : Summable (fun k : ι → ℤ => ‖c k‖) :=
    Work.Diff.STE.summable_norm_of_CSq s' hs' c (hCw s')
  -- ### The truncated family `D = trunc ρ ε c`
  have hDle : ∀ k : ι → ℤ, ‖D k‖ ≤ ‖c k‖ := by
    intro k
    have hk : ‖ρ (ε • fun i => (k i : ℝ))‖ ≤ 1 := hρb _
    have hval : D k = ((ρ (ε • fun i => (k i : ℝ)) : ℝ) : ℂ) * c k := by
      rw [hDdef]; rfl
    have hnorm : ‖(((ρ (ε • fun i => (k i : ℝ)) : ℝ)) : ℂ)‖
        = ‖ρ (ε • fun i => (k i : ℝ))‖ := by simp
    rw [hval, norm_mul, hnorm]
    calc ‖ρ (ε • fun i => (k i : ℝ))‖ * ‖c k‖ ≤ 1 * ‖c k‖ :=
          mul_le_mul_of_nonneg_right hk (norm_nonneg _)
      _ = ‖c k‖ := one_mul _
  have hDl1 : Summable (fun k : ι → ℤ => ‖D k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hDle hCl1
  have hDw : ∀ M : ℕ, Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ M * ‖D k‖ ^ 2) := by
    intro M
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hCw M)
    · exact mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) M) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hDle k) 2)
        (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) M)
  -- ### `ℓ¹`-summability of the symmetrized families
  have hDneg1 : Summable (fun k : ι → ℤ => ‖D (-k)‖) :=
    hDl1.comp_injective (Equiv.neg (ι → ℤ)).injective
  have hCneg1 : Summable (fun k : ι → ℤ => ‖c (-k)‖) :=
    hCl1.comp_injective (Equiv.neg (ι → ℤ)).injective
  have hsymmDl1 : Summable (fun k : ι → ℤ => ‖(D k + star (D (-k))) / 2‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((hDl1.add hDneg1).mul_left (1 / 2 : ℝ))
    calc ‖(D k + star (D (-k))) / 2‖ = ‖D k + star (D (-k))‖ / 2 := by
          rw [norm_div]; norm_num
      _ ≤ (‖D k‖ + ‖star (D (-k))‖) / 2 :=
          div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ = (1 / 2) * (‖D k‖ + ‖D (-k)‖) := by rw [norm_star]; ring
  have hsymmCl1 : Summable (fun k : ι → ℤ => ‖(c k + star (c (-k))) / 2‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((hCl1.add hCneg1).mul_left (1 / 2 : ℝ))
    calc ‖(c k + star (c (-k))) / 2‖ = ‖c k + star (c (-k))‖ / 2 := by
          rw [norm_div]; norm_num
      _ ≤ (‖c k‖ + ‖star (c (-k))‖) / 2 :=
          div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ = (1 / 2) * (‖c k‖ + ‖c (-k)‖) := by rw [norm_star]; ring
  -- ### The real part of `STruncC` and of `g`
  have hS : ∀ z : ι → ℝ, Work.Diff.STE.STruncC ρ ε f z
      = ((Work.Diff.STE.seriesFun D z).re : ℂ) := fun z => rfl
  have hSre : ∀ z : ι → ℝ, (Work.Diff.STE.STruncC ρ ε f z).re
      = (Work.Diff.STE.seriesFun D z).re := fun z => by rw [hS z, Complex.ofReal_re]
  have hgseries : ∀ z : ι → ℝ, g z = Work.Diff.STE.seriesFun c z := by
    intro z
    have h := Work.Diff.STE.flat.seriesFun_fourierCoeff g hg hgper z
    rw [hcdef]
    exact h.symm
  have hseriesD : ∀ z : ι → ℝ, ((Work.Diff.STE.seriesFun D z).re : ℂ)
      = Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2) z :=
    fun z => Work.Diff.STE.B3.re_seriesFun_eq_seriesFun_symm D hDl1 z
  have hseriesC : ∀ z : ι → ℝ, ((Work.Diff.STE.seriesFun c z).re : ℂ)
      = Work.Diff.STE.seriesFun (fun k => (c k + star (c (-k))) / 2) z :=
    fun z => Work.Diff.STE.B3.re_seriesFun_eq_seriesFun_symm c hCl1 z
  -- ### `u` as a difference of two Fourier series
  have hu_eq : ∀ z : ι → ℝ, u z
      = Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2) z
        - Work.Diff.STE.seriesFun (fun k => (c k + star (c (-k))) / 2) z := by
    intro z
    have hz : u z = (((Work.Diff.STE.STruncC ρ ε f z - g z).re : ℝ) : ℂ) := rfl
    rw [hz, Complex.sub_re, hSre z, hgseries z, Complex.ofReal_sub, hseriesD z, hseriesC z]
  have hu_fun : u = fun z =>
      Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2) z
        - Work.Diff.STE.seriesFun (fun k => (c k + star (c (-k))) / 2) z := funext hu_eq
  -- ### The Fourier coefficients of `u`
  have hfourier_u : Work.Diff.STE.fourierCoeff u
      = fun k : ι → ℤ => (D k + star (D (-k))) / 2 - (c k + star (c (-k))) / 2 := by
    funext k
    have hcontD : Continuous (Work.Diff.STE.seriesFun (fun k => (D k + star (D (-k))) / 2)) :=
      Work.Diff.STE.flat.continuous_seriesFun_of_summable _ hsymmDl1
    have hcontC : Continuous (Work.Diff.STE.seriesFun (fun k => (c k + star (c (-k))) / 2)) :=
      Work.Diff.STE.flat.continuous_seriesFun_of_summable _ hsymmCl1
    rw [hu_fun, Work.Diff.STE.flat.fourierCoeff_sub_of_continuous _ _ hcontD hcontC k,
      Work.Diff.STE.flat.fourierCoeff_seriesFun _ hsymmDl1 k,
      Work.Diff.STE.flat.fourierCoeff_seriesFun _ hsymmCl1 k]
  -- ### `symm` is linear on the difference `D - c`
  have hsymm_sub_eq : ∀ k : ι → ℤ,
      (D k + star (D (-k))) / 2 - (c k + star (c (-k))) / 2
        = ((D k - c k) + star (D (-k) - c (-k))) / 2 := by
    intro k
    rw [star_sub]
    ring
  have hsymm_sub_fun : (fun k : ι → ℤ => ((D k - c k) + star (D (-k) - c (-k))) / 2)
      = (fun k : ι → ℤ => (D k + star (D (-k))) / 2 - (c k + star (c (-k))) / 2) := by
    funext k
    exact (hsymm_sub_eq k).symm
  -- ### The weighted `ℓ²` summability of the truncation error
  have hsub_w : Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ s * ‖D k - c k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) ((hCw s).mul_left 4)
    · exact mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _)
    · have hle : ‖D k - c k‖ ≤ 2 * ‖c k‖ := by
        calc ‖D k - c k‖ ≤ ‖D k‖ + ‖c k‖ := norm_sub_le _ _
          _ ≤ ‖c k‖ + ‖c k‖ := add_le_add (hDle k) le_rfl
          _ = 2 * ‖c k‖ := by ring
      have hsq : ‖D k - c k‖ ^ 2 ≤ 4 * ‖c k‖ ^ 2 := by
        calc ‖D k - c k‖ ^ 2 ≤ (2 * ‖c k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
          _ = 4 * ‖c k‖ ^ 2 := by ring
      calc Work.Diff.STE.wt k ^ s * ‖D k - c k‖ ^ 2
          ≤ Work.Diff.STE.wt k ^ s * (4 * ‖c k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s)
        _ = 4 * (Work.Diff.STE.wt k ^ s * ‖c k‖ ^ 2) := by ring
  -- ### Assembly
  have hub : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u)
      ≤ C ^ 2 * ε ^ 2 * Work.Diff.STE.CSq (s + 1) c := by
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u)
        = Work.Diff.STE.CSq s (fun k : ι → ℤ =>
            (D k + star (D (-k))) / 2 - (c k + star (c (-k))) / 2) := by rw [hfourier_u]
      _ = Work.Diff.STE.CSq s (fun k : ι → ℤ =>
            ((D k - c k) + star (D (-k) - c (-k))) / 2) := by rw [hsymm_sub_fun]
      _ ≤ Work.Diff.STE.CSq s (fun k : ι → ℤ => D k - c k) :=
            Work.Diff.STE.B3.CSq_symm_le (fun k : ι → ℤ => D k - c k) s hsub_w
      _ ≤ C ^ 2 * ε ^ 2 * Work.Diff.STE.CSq (s + 1) c := by
            simpa only [hDdef] using
              CSq_trunc_sub_le_bound ρ C hρC ε hε s c (hCw (s + 1))
  exact hub

end Work.Diff.STE.Lead
