/-
# Area A5: the shared vocabulary

This module fixes the vocabulary used by the proof of `Work.KMTContract.AreaA5`
(`Work.KMTAreas.area_A5`): the *minor arc input* (B) of Krause--Mirek--Tao §4 for the concrete
Ionescu--Wainger projections `kmtPj ρ`, proved from `ImprovKMT` (area A4) and the Ionescu--Wainger
multiplier theorem `IWMultiplierBoundStatement_even` (area A1) by interpolation.

The main mathematical obstruction of the interpolation is *formal*: the map
`u ↦ u - kmtProj ρ l k u` is not linear on the whole space `ℤ → ℂ` (the convolution defining
`kmtProj` is only summable for bounded `u`), while every interpolation theorem in the workspace
(`Work.Analysis.Interpolation.stein_bilinear_top`, `…bilinear_operator_interp`) takes a genuine
bilinear map.  We therefore *extend* `kmtProj ρ l k` to a linear map `piHat ρ l k` on the whole
space, agreeing with it on bounded functions (`piHat_of_bounded`): the extension is obtained by
choosing a complement of the subspace `boundedZSub` of bounded functions
(`Submodule.exists_isCompl`) and using `LinearMap.ofIsCompl`.

Since all the functions to which the interpolation is applied are bounded (they lie in some
`ℓ^p`, `1 < p`, hence are bounded by `bound_of_memLp_count`), the extension introduces no
mathematical content: the endpoints of the interpolation hold for *all* inputs, the "wild" cases
being those where the right-hand side is `⊤` or the left-hand side vanishes.

## Main definitions

* `Work.KMTAreas.A5.BoundedZ`, `…boundedZSub` — bounded functions and their submodule;
* `Work.KMTAreas.A5.piHat` — the linear extension of `kmtProj ρ l k`;
* `Work.KMTAreas.A5.AhalfBilin` — the halved average `Ã_N` as a bilinear map.
-/
import Mathlib
import Submission.Work.KMTContract.Areas
import Submission.Work.KMTContract.kmtKernel_decay
import Submission.Work.KMTContract.kernel_l1_of_decay
import Submission.Work.KMTContract.bound_of_memLp_count

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.KMTContract
open Work.Analysis.EndVar
open Work.Analysis.IonescuWainger
open Submission.PointwiseErgodicTheorems

/-! ## Bounded functions on `ℤ` -/

/-- Bounded complex-valued functions on `ℤ`; the natural domain on which the convolution
`kmtProj` is absolutely convergent. -/
def BoundedZ (u : ℤ → ℂ) : Prop := ∃ C : ℝ, ∀ x : ℤ, ‖u x‖ ≤ C

theorem boundedZ_zero : BoundedZ (0 : ℤ → ℂ) := ⟨0, by simp⟩

theorem boundedZ_add {u v : ℤ → ℂ} (hu : BoundedZ u) (hv : BoundedZ v) :
    BoundedZ (u + v) := by
  obtain ⟨C, hC⟩ := hu
  obtain ⟨D, hD⟩ := hv
  exact ⟨C + D, fun x => by
    rw [Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

theorem boundedZ_smul (c : ℂ) {u : ℤ → ℂ} (hu : BoundedZ u) : BoundedZ (c • u) := by
  obtain ⟨C, hC⟩ := hu
  exact ⟨‖c‖ * C, fun x => by
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩

theorem boundedZ_of_bound {u : ℤ → ℂ} {C : ℝ} (h : ∀ x, ‖u x‖ ≤ C) : BoundedZ u := ⟨C, h⟩

theorem boundedZ_sub {u v : ℤ → ℂ} (hu : BoundedZ u) (hv : BoundedZ v) : BoundedZ (u - v) := by
  obtain ⟨C, hC⟩ := hu
  obtain ⟨D, hD⟩ := hv
  exact ⟨C + D, fun x => by
    rw [Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hC x) (hD x))⟩

theorem boundedZ_neg {u : ℤ → ℂ} (hu : BoundedZ u) : BoundedZ (-u) := by
  obtain ⟨C, hC⟩ := hu
  exact ⟨C, fun x => by rw [Pi.neg_apply, norm_neg]; exact hC x⟩

/-- An `ℓ^p` function (`1 < p`) is bounded. -/
theorem boundedZ_of_memLp {p : ℝ≥0∞} (hp : 1 < p) {f : ℤ → ℂ}
    (hf : MemLp f p Measure.count) : BoundedZ f := by
  obtain ⟨M, hM⟩ := bound_of_memLp_count hp hf
  exact ⟨M, fun x => hM x⟩

/-- The bounded functions form a `ℂ`-subspace of `ℤ → ℂ`. -/
def boundedZSub : Submodule ℂ (ℤ → ℂ) where
  carrier := {u | BoundedZ u}
  zero_mem' := boundedZ_zero
  add_mem' := fun ha hb => boundedZ_add ha hb
  smul_mem' := fun c _ hu => boundedZ_smul c hu

/-! ## The kernel of the Ionescu--Wainger projection -/

/-- The convolution kernel of `kmtProj ρ l k`: the Fourier coefficients of the IW symbol. -/
abbrev kmtKern (ρ : ℝ) (l : ℕ) (k : ℤ) : ℤ → ℂ :=
  fun j => Work.Analysis.IWMultiplier.iwKernel
    (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j

theorem kmtProj_eq_conv (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) (n : ℤ) :
    kmtProj ρ l k f n = ∑' j : ℤ, kmtKern ρ l k j * f (n - j) :=
  kmtProj_apply ρ l k f n

/-- The kernel of `kmtProj ρ l k` is absolutely summable (it decays like `j^{-2}`). -/
theorem summable_kmtKern_norm (ρ : ℝ) (l : ℕ) (k : ℤ) :
    Summable (fun j : ℤ => ‖kmtKern ρ l k j‖) := by
  obtain ⟨C, _hC, hdec⟩ := kmtKernel_decay ρ l k
  exact kernel_l1_of_decay hdec

/-- For a bounded `u`, the convolution defining `kmtProj` is absolutely summable. -/
theorem summable_kmtKern_mul (ρ : ℝ) (l : ℕ) (k : ℤ) {u : ℤ → ℂ} (hu : BoundedZ u) (n : ℤ) :
    Summable (fun j : ℤ => kmtKern ρ l k j * u (n - j)) := by
  obtain ⟨C, hC⟩ := hu
  have hmaj : Summable (fun j : ℤ => C * ‖kmtKern ρ l k j‖) :=
    Summable.mul_left C (summable_kmtKern_norm ρ l k)
  refine Summable.of_norm_bounded hmaj (fun j => ?_)
  calc ‖kmtKern ρ l k j * u (n - j)‖ = ‖u (n - j)‖ * ‖kmtKern ρ l k j‖ := by
        rw [norm_mul, mul_comm]
    _ ≤ C * ‖kmtKern ρ l k j‖ := mul_le_mul_of_nonneg_right (hC (n - j)) (norm_nonneg _)

/-! ## Linearity of `kmtProj` on bounded functions -/

theorem kmtProj_add_bounded (ρ : ℝ) (l : ℕ) (k : ℤ) {u v : ℤ → ℂ}
    (hu : BoundedZ u) (hv : BoundedZ v) :
    kmtProj ρ l k (u + v) = kmtProj ρ l k u + kmtProj ρ l k v := by
  funext n
  rw [kmtProj_eq_conv, Pi.add_apply, kmtProj_eq_conv, kmtProj_eq_conv]
  rw [show (∑' j : ℤ, kmtKern ρ l k j * (u + v) (n - j))
      = ∑' j : ℤ, (kmtKern ρ l k j * u (n - j) + kmtKern ρ l k j * v (n - j)) from
    tsum_congr fun j => by rw [Pi.add_apply]; ring]
  rw [(summable_kmtKern_mul ρ l k hu n).tsum_add (summable_kmtKern_mul ρ l k hv n)]

theorem kmtProj_smul_bounded (ρ : ℝ) (l : ℕ) (k : ℤ) (c : ℂ) {u : ℤ → ℂ} (hu : BoundedZ u) :
    kmtProj ρ l k (c • u) = c • kmtProj ρ l k u := by
  funext n
  rw [Pi.smul_apply, kmtProj_eq_conv, kmtProj_eq_conv]
  rw [show (∑' j : ℤ, kmtKern ρ l k j * (c • u) (n - j))
      = ∑' j : ℤ, c * (kmtKern ρ l k j * u (n - j)) from
    tsum_congr fun j => by rw [Pi.smul_apply, smul_eq_mul]; ring]
  rw [tsum_mul_left, smul_eq_mul]

/-- `kmtProj ρ l k` as a linear map on the subspace of bounded functions. -/
def kmtProjLin (ρ : ℝ) (l : ℕ) (k : ℤ) : boundedZSub →ₗ[ℂ] (ℤ → ℂ) where
  toFun := fun u => kmtProj ρ l k (u : ℤ → ℂ)
  map_add' := fun u v => kmtProj_add_bounded ρ l k u.2 v.2
  map_smul' := fun c u => kmtProj_smul_bounded ρ l k c u.2

/-! ## The linear extension of `kmtProj` -/

/-- **The linear extension of `kmtProj ρ l k` to all functions.**  Since `kmtProj ρ l k` is only
linear on the subspace of bounded functions, we extend it along an arbitrary complement of that
subspace.  The extension is a genuine `LinearMap`, which is what the interpolation theorems of
`Work.Analysis.Interpolation` require; it agrees with `kmtProj ρ l k` on bounded functions
(`piHat_of_bounded`), which is the only case in which the two differ in the application. -/
def piHat (ρ : ℝ) (l : ℕ) (k : ℤ) : (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  let q : Submodule ℂ (ℤ → ℂ) := Classical.choose (Submodule.exists_isCompl boundedZSub)
  LinearMap.ofIsCompl (p := boundedZSub) (q := q)
    (Classical.choose_spec (Submodule.exists_isCompl boundedZSub)) (kmtProjLin ρ l k) 0

theorem piHat_of_bounded (ρ : ℝ) (l : ℕ) (k : ℤ) {u : ℤ → ℂ} (hu : BoundedZ u) :
    piHat ρ l k u = kmtProj ρ l k u := by
  simp only [piHat]
  exact LinearMap.ofIsCompl_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl boundedZSub))
    (φ := kmtProjLin ρ l k) (ψ := 0) (u := (⟨u, hu⟩ : boundedZSub))

/-! ## The halved average as a bilinear map -/

theorem AhalfR_smul_left' (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (c : ℂ) (f g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (c • f) g = c • AhalfR TZ N P₁ P₂ f g := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem AhalfR_smul_right' (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (c : ℂ) (f g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f (c • g) = c • AhalfR TZ N P₁ P₂ f g := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The halved average `Ã_N(-,-)` as a bilinear map.** -/
def AhalfBilin (N : ℝ≥0) (P₁ P₂ : ℤ[X]) : (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f :=
    { toFun := fun g => AhalfR TZ N P₁ P₂ f g
      map_add' := fun g₁ g₂ => AhalfR_add_right' N P₁ P₂ f g₁ g₂
      map_smul' := fun c g => AhalfR_smul_right' N P₁ P₂ c f g }
  map_add' f₁ f₂ := by
    ext g x
    simp only [LinearMap.add_apply, Pi.add_apply]
    exact congrFun (AhalfR_add_left' N P₁ P₂ f₁ f₂ g) x
  map_smul' c f := by
    ext g x
    simp only [LinearMap.smul_apply, Pi.smul_apply]
    exact congrFun (AhalfR_smul_left' N P₁ P₂ c f g) x

@[simp] theorem AhalfBilin_apply (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : ℤ → ℂ) :
    AhalfBilin N P₁ P₂ f g = AhalfR TZ N P₁ P₂ f g := rfl

end

end Work.KMTAreas.A5
