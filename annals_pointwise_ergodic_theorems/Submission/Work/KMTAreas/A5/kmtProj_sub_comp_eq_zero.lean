import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.KMTAreas.A5.tsum_conv_assoc
import Submission.Work.KMTAreas.A5.iwSymbolSet_prod_kmtEta
import Submission.Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.IonescuWainger

/-! ## The symbol of the KMT projection is square integrable -/

/-- The IW symbol `∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(· - α)` of the KMT projection is `L²`. -/
lemma memLp_kmtSymbol (ρ : ℝ) (l : ℕ) (k : ℤ) :
    MemLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) 2 circleMeasure := by
  refine MemLp.mono_exponent ?_ le_top
  exact Work.Analysis.IWMultiplier.memLp_iwSymbolSet _
    (memLp_periodize (φ := etaCut kmtEta k) (R := (2 : ℝ) ^ k) (C := 1)
      (etaCutRegular k).1.continuous.measurable
      (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) k))
      (fun x hx => (etaCutRegular k).2.2 x (le_of_lt hx))
      (fun x => by rw [(etaCutRegular k).2.1 x]; exact norm_kmtEta_le _))

/-! ## The convolution identity for the kernels -/

/-- The kernel of the composite projection is the convolution of the two kernels. -/
lemma kmtKern_conv_eq (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l l' : ℕ} {k k' : ℤ} (hl : l' ≤ l) (hk : k' < k) (hk1 : k ≤ -1)
    (hNA : NonAliasing k (iwArithFreqs ρ l)) (m : ℤ) :
    ∑' j : ℤ, kmtKern ρ l' k' j * kmtKern ρ l k (m - j) = kmtKern ρ l' k' m := by
  have hFs : Summable (fun j : ℤ => ‖fourierCoeff (iwSymbolSet (iwArithFreqs ρ l')
      (periodize (etaCut kmtEta k'))) j‖) := summable_kmtKern_norm ρ l' k'
  have h := fourierCoeff_mul_eq_tsum_conv (memLp_kmtSymbol ρ l' k') (memLp_kmtSymbol ρ l k) hFs m
  have hprod : (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut kmtEta k')) ξ
        * iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ)
      = iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut kmtEta k')) := by
    funext ξ
    exact congrFun (iwSymbolSet_prod_kmtEta ρ hρ hρ1 hl hk hk1 hNA) ξ
  rw [hprod] at h
  exact h.symm

/-! ## The main theorem -/

theorem kmtProj_sub_comp_eq_zero (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l l' : ℕ} {k k' : ℤ} (hl : l' ≤ l) (hk : k' < k) (hk1 : k ≤ -1)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing k
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l))
    {u : ℤ → ℂ} (hu : Work.KMTAreas.A5.BoundedZ u) :
    Work.KMTContract.kmtProj ρ l' k' (u - Work.KMTContract.kmtProj ρ l k u) = 0 := by
  funext n
  obtain ⟨Cu₀, hCu₀⟩ := hu
  set Cu : ℝ := max Cu₀ 0 with hCudef
  have hCu : ∀ m : ℤ, ‖u m‖ ≤ Cu := fun m => le_trans (hCu₀ m) (le_max_left _ _)
  have ha : Summable (fun j : ℤ => ‖kmtKern ρ l' k' j‖) := summable_kmtKern_norm ρ l' k'
  have hb : Summable (fun j : ℤ => ‖kmtKern ρ l k j‖) := summable_kmtKern_norm ρ l k
  have hker := kmtKern_conv_eq ρ hρ hρ1 hl hk hk1 hNA
  -- boundedness of the inner projection
  have hbounded : BoundedZ (kmtProj ρ l k u) := by
    refine ⟨(∑' i : ℤ, ‖kmtKern ρ l k i‖) * Cu, fun m => ?_⟩
    have hsum : Summable (fun j : ℤ => kmtKern ρ l k j * u (m - j)) :=
      summable_kmtKern_mul ρ l k ⟨Cu₀, hCu₀⟩ m
    rw [kmtProj_eq_conv ρ l k u m]
    refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
    have hmaj : Summable (fun j : ℤ => ‖kmtKern ρ l k j‖ * Cu) :=
      (summable_kmtKern_norm ρ l k).mul_right Cu
    have hle : ∀ j : ℤ, ‖kmtKern ρ l k j‖ * ‖u (m - j)‖ ≤ ‖kmtKern ρ l k j‖ * Cu :=
      fun j => mul_le_mul_of_nonneg_left (hCu (m - j)) (norm_nonneg _)
    rw [show (∑' j : ℤ, ‖kmtKern ρ l k j * u (m - j)‖)
        = ∑' j : ℤ, ‖kmtKern ρ l k j‖ * ‖u (m - j)‖ from tsum_congr (fun j => norm_mul _ _)]
    refine ((Summable.of_nonneg_of_le (fun j => by positivity) hle hmaj).tsum_le_tsum hle hmaj).trans_eq ?_
    rw [tsum_mul_right]
  -- unfold the outer projection
  rw [kmtProj_eq_conv ρ l' k' (u - kmtProj ρ l k u) n]
  -- split the defining series
  have hsplit : (∑' j : ℤ, kmtKern ρ l' k' j * (u - kmtProj ρ l k u) (n - j))
      = (∑' j : ℤ, kmtKern ρ l' k' j * u (n - j))
        - (∑' j : ℤ, kmtKern ρ l' k' j * (kmtProj ρ l k u) (n - j)) := by
    rw [show (∑' j : ℤ, kmtKern ρ l' k' j * (u - kmtProj ρ l k u) (n - j))
        = ∑' j : ℤ, (kmtKern ρ l' k' j * u (n - j)
            - kmtKern ρ l' k' j * (kmtProj ρ l k u) (n - j)) from
      tsum_congr (fun j => by rw [Pi.sub_apply]; ring)]
    exact Summable.tsum_sub (summable_kmtKern_mul ρ l' k' ⟨Cu₀, hCu₀⟩ n)
      (summable_kmtKern_mul ρ l' k' hbounded n)
  -- the second series is the first, by the kernel identity
  have hsecond : (∑' j : ℤ, kmtKern ρ l' k' j * (kmtProj ρ l k u) (n - j))
      = ∑' j : ℤ, kmtKern ρ l' k' j * u (n - j) := by
    refine (tsum_congr (fun j => ?_)).trans (tsum_conv_assoc (kmtKern ρ l' k') (kmtKern ρ l k) u
      (C := Cu) ha hb hCu hker n)
    rw [kmtProj_eq_conv ρ l k u (n - j)]
  rw [hsplit, hsecond, sub_self]
  rfl

end

end Work.KMTAreas.A5
