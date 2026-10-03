import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs
import Submission.Work.KMTContract.tendsto_sum_Icc_atTop
import Submission.Work.KMTContract.bound_of_memLp_count
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier

noncomputable section

/-! ## Tannery's theorem for `ℓ¹`-kernels on `ℤ`

The engine of the extension argument: an absolutely summable kernel `κ` on `ℤ` may be moved inside
a pointwise limit of uniformly bounded sequences. -/

/-- **Dominated convergence for `ℤ`-indexed sums against an `ℓ¹`-kernel.**  If `κ ∈ ℓ¹(ℤ)`, the
sequences `g n` are uniformly bounded by `B` and converge pointwise to `glim`, then
`∑'_j κ j * g n j → ∑'_j κ j * glim j`.

This is Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) with the summable majorant
`j ↦ B * ‖κ j‖`; note that no bound on `glim` has to be assumed, since `‖glim j‖ ≤ B` follows
from `hB` and `hlim`. -/
theorem tendsto_tsum_mul_of_norm_bounded
    {κ : ℤ → ℂ} (hκ : Summable fun j : ℤ => ‖κ j‖)
    {g : ℕ → ℤ → ℂ} {glim : ℤ → ℂ} {B : ℝ}
    (hB : ∀ (n : ℕ) (j : ℤ), ‖g n j‖ ≤ B)
    (hlim : ∀ j : ℤ, Filter.Tendsto (fun n : ℕ => g n j) Filter.atTop (nhds (glim j))) :
    Filter.Tendsto (fun n : ℕ => ∑' j : ℤ, κ j * g n j) Filter.atTop
      (nhds (∑' j : ℤ, κ j * glim j)) := by
  refine tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun n j => κ j * g n j) (g := fun j => κ j * glim j)
    (bound := fun j => B * ‖κ j‖) (hκ.mul_left B) (fun j => ?_) ?_
  · exact (hlim j).const_mul (κ j)
  · filter_upwards with n
    intro j
    calc ‖κ j * g n j‖ = ‖κ j‖ * ‖g n j‖ := norm_mul _ _
      _ ≤ ‖κ j‖ * B := mul_le_mul_of_nonneg_left (hB n j) (norm_nonneg _)
      _ = B * ‖κ j‖ := mul_comm _ _

/-- **Pointwise continuity of `iwConv` along uniformly bounded pointwise convergence.**  If the
kernel of the Ionescu–Wainger symbol is in `ℓ¹` (so that the defining `tsum` of `iwConv` is a
genuine sum on bounded sequences), then `iwConv A Φ` is continuous along pointwise convergence of
uniformly bounded sequences. -/
theorem tendsto_iwConv_of_bounded_tendsto
    {A : Finset Work.Analysis.IWMultiplier.Circle} {Φ : Work.Analysis.IWMultiplier.Circle → ℂ}
    (hκ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Φ) j‖)
    {g : ℕ → ℤ → ℂ} {glim : ℤ → ℂ} {B : ℝ}
    (hB : ∀ (n : ℕ) (m : ℤ), ‖g n m‖ ≤ B)
    (hlim : ∀ m : ℤ, Filter.Tendsto (fun n : ℕ => g n m) Filter.atTop (nhds (glim m)))
    (x : ℤ) :
    Filter.Tendsto (fun n : ℕ => iwConv A Φ (g n) x) Filter.atTop
      (nhds (iwConv A Φ glim x)) := by
  simp only [iwConv_apply, smul_eq_mul]
  exact tendsto_tsum_mul_of_norm_bounded (κ := fun j => iwKernel (iwSymbolSet A Φ) j)
    (B := B) hκ (fun n j => hB n (x - j)) (fun j => hlim (x - j))

/-! ## The truncation `f · 1_{[-K,K]}` -/

/-- The truncation `trunc K f = f · 1_{[-K,K]}`: a finitely supported approximation of `f`. -/
private def trunc (K : ℕ) (f : ℤ → ℂ) : ℤ → ℂ := fun x => if |x| ≤ (K : ℤ) then f x else 0

private theorem trunc_norm_le (K : ℕ) (f : ℤ → ℂ) (x : ℤ) : ‖trunc K f x‖ ≤ ‖f x‖ := by
  rw [trunc]; split <;> simp

private theorem trunc_of_abs_le {K : ℕ} {f : ℤ → ℂ} {x : ℤ} (h : |x| ≤ (K : ℤ)) :
    trunc K f x = f x :=
  if_pos h

private theorem trunc_support_finite (K : ℕ) (f : ℤ → ℂ) :
    (Function.support (trunc K f)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc (-(K : ℤ)) (K : ℤ)) ?_
  intro x hx
  by_contra hxI
  exact hx (if_neg (fun hle => hxI (by rw [Set.mem_Icc]; exact abs_le.mp hle)))

/-- The truncations of a bounded `f` converge to `f` pointwise, in the `iwConv` sense: this is the
continuity of `iwConv` along bounded pointwise convergence applied to the truncations. -/
theorem tendsto_iwConv_trunc
    {A : Finset Work.Analysis.IWMultiplier.Circle} {Φ : Work.Analysis.IWMultiplier.Circle → ℂ}
    (hκ : Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A Φ) j‖)
    {f : ℤ → ℂ} {B : ℝ} (hB : ∀ m : ℤ, ‖f m‖ ≤ B) (x : ℤ) :
    Filter.Tendsto (fun K : ℕ => iwConv A Φ (trunc K f) x) Filter.atTop
      (nhds (iwConv A Φ f x)) := by
  refine tendsto_iwConv_of_bounded_tendsto (A := A) (Φ := Φ) hκ
    (g := fun K m => trunc K f m) (glim := f) (B := B) (fun K m => ?_) (fun m => ?_) x
  · exact (trunc_norm_le K f m).trans (hB m)
  · have hev : (fun K : ℕ => trunc K f m) =ᶠ[Filter.atTop] (fun _ : ℕ => f m) :=
      Filter.eventually_atTop.mpr ⟨m.natAbs, fun K hK =>
        trunc_of_abs_le (by rw [← Int.natCast_natAbs]; exact_mod_cast hK)⟩
    exact (tendsto_const_nhds).congr' hev.symm

/-! ## The target -/

/-- **Extending an `ℓ^q` bound for `iwConv` from finitely supported inputs to bounded inputs.**
`IWLqBoundScalar A Φ q C` is only tested on finitely supported sequences.  If in addition the
kernel `j ↦ iwKernel (iwSymbolSet A Φ) j` is in `ℓ¹` (so that the defining `tsum` of `iwConv` is a
genuine sum for bounded inputs and is the limit of its partial sums), then the same bound holds for
every bounded `f : ℤ → ℂ`. -/
theorem eLpNorm_iwConv_le_of_IWLqBoundScalar_of_bounded
    {A : Finset Work.Analysis.IWMultiplier.Circle} {Φ : Work.Analysis.IWMultiplier.Circle → ℂ}
    {q : ℝ} (hq : 1 < q) {C : NNReal}
    (hκ : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖))
    (hb : Work.Analysis.IWMultiplier.IWLqBoundScalar A Φ (ENNReal.ofReal q) C)
    {f : ℤ → ℂ} (hf : ∃ B : ℝ, ∀ m : ℤ, ‖f m‖ ≤ B) :
    MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv A Φ f) (ENNReal.ofReal q)
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C : ℝ) * MeasureTheory.eLpNorm f (ENNReal.ofReal q)
          MeasureTheory.Measure.count := by
  obtain ⟨B, hB⟩ := hf
  -- Fatou's lemma for the `ℒ^q` seminorm, applied to the (finitely supported) truncations
  refine MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (hg := by pw_aesm) (u := Filter.atTop)
    (f := fun K : ℕ => fun x : ℤ => iwConv A Φ (trunc K f) x)
    (g := fun x : ℤ => iwConv A Φ f x)
    (C := ENNReal.ofReal (C : ℝ) * eLpNorm f (ENNReal.ofReal q) Measure.count) ?_ ?_ ?_
  · filter_upwards with K
    have h1 : eLpNorm (trunc K f) (ENNReal.ofReal q) Measure.count
        ≤ eLpNorm f (ENNReal.ofReal q) Measure.count :=
      eLpNorm_mono (hf := by pw_aesm) (fun x => trunc_norm_le K f x)
    exact (hb (trunc K f) (trunc_support_finite K f)).trans (mul_le_mul' le_rfl h1)
  · intro K
    exact (measurable_of_countable _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => tendsto_iwConv_trunc hκ hB x)

end

end Work.KMTAreas.A7
