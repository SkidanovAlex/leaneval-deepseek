/-
# `Work.S15crux.prelude`

Shared vocabulary for the filtered stratum-`U` variance bound of FI §15 (the reduction
`Work.FIArea4.S15EvarG_filtered_sum_le_of_strU` takes the statement

`Σ_{e ≤ Y} Σ_{d' ∈ (X/e, Y/e]} EvarG (radN Pa) (4 d') (S15strU β u t ℓ e) ≤ C (log N)^24 (Br · En)`

as its input; this module fixes the `d'`-index set, the dyadic modulus-scale index, and the
elementary dyadic decomposition of the `d'`-sum into `Vvar`-blocks that the proof of the target
runs on.)
-/
import Mathlib
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15EvarGDefs
import Submission.Work.FIArea4.S15red.EvarG_filtered_strU_defs

namespace Work.S15crux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `d'`-index set of the stratum `e`: FI (15.2)'s `1 ≤ d' ≤ Y/e` with `X < e d'`
(`Y = S15Y Pa X j`). -/
def dset (Pa : Work.FITop.Params) (X j e : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Work.FIArea4.S15Y Pa X j / e)).filter (fun d' => X < e * d')

/-- The dyadic modulus scale of `d'`: the `k` with `2^k < 4 d' ≤ 2^(k+1)` (the modulus of the
stratum is `4 d'`). -/
def dk (d' : ℕ) : ℕ := Nat.log 2 (4 * d' - 1)

/-- The dyadic modulus scales occurring in the stratum `e`. -/
def kset (Pa : Work.FITop.Params) (X j e : ℕ) : Finset ℕ := (dset Pa X j e).image dk

/-- `2^(dk d') < 4 d' ≤ 2^(dk d' + 1)`. -/
lemma dk_spec {d' : ℕ} (hd : 1 ≤ d') :
    2 ^ dk d' < 4 * d' ∧ 4 * d' ≤ 2 ^ (dk d' + 1) := by
  have h1 : 0 < 4 * d' - 1 := by omega
  have h2 : 2 ^ dk d' ≤ 4 * d' - 1 := Nat.pow_log_le_self 2 (by omega)
  have h3 : 4 * d' - 1 < 2 ^ (dk d' + 1) := Nat.lt_pow_succ_log_self (by norm_num) (4 * d' - 1)
  omega

/-- `Evar` is nonnegative. -/
lemma Evar_nonneg (R S d : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIPlan.Evar R S d α := by
  rw [Work.FIPlan.Evar]
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

/-- `Vvar` is nonnegative. -/
lemma Vvar_nonneg (R S D : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIPlan.Vvar R S D α := by
  rw [Work.FIPlan.Vvar]
  exact Finset.sum_nonneg (fun d _ => Evar_nonneg _ _ _ _)

/-- **The dyadic decomposition of the stratum `d'`-sum.**  The moduli `4 d'` of the stratum `e`
are grouped into the dyadic blocks `(2^k, 2^(k+1)]`; each block is bounded by the corresponding
`Vvar`. -/
lemma sum_dset_Evar_le_sum_kset_Vvar (R S : ℕ) (α : ℕ → ℕ → ℂ) (Pa : Work.FITop.Params)
    (X j e : ℕ) :
    (∑ d' ∈ dset Pa X j e, Work.FIPlan.Evar R S (4 * d') α)
      ≤ ∑ k ∈ kset Pa X j e, Work.FIPlan.Vvar R S (2 ^ k) α := by
  have hmaps : ∀ d' ∈ dset Pa X j e, dk d' ∈ kset Pa X j e :=
    fun d' hd' => Finset.mem_image.mpr ⟨d', hd', rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (f := fun d' => Work.FIPlan.Evar R S (4 * d') α)]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hinj : Set.InjOn (fun i : ℕ => 4 * i)
      ↑((dset Pa X j e).filter (fun i => dk i = k)) := by
    intro a _ b _ hab
    exact Nat.mul_left_cancel (by norm_num) hab
  have hstep : (∑ i ∈ (dset Pa X j e).filter (fun i => dk i = k), Work.FIPlan.Evar R S (4 * i) α)
      = ∑ m ∈ ((dset Pa X j e).filter (fun i => dk i = k)).image (fun i => 4 * i),
          Work.FIPlan.Evar R S m α :=
    (Finset.sum_image (f := fun m => Work.FIPlan.Evar R S m α) (g := fun i => 4 * i) hinj).symm
  rw [Work.FIPlan.Vvar, hstep]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · rintro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨d', hd', rfl⟩ := hm
    rw [Finset.mem_filter] at hd'
    obtain ⟨hd'dset, hd'k⟩ := hd'
    have hd'1 : 1 ≤ d' := by
      rw [dset, Finset.mem_filter, Finset.mem_Icc] at hd'dset
      exact hd'dset.1.1
    have hsp := dk_spec hd'1
    rw [hd'k, pow_succ'] at hsp
    rw [Finset.mem_Ioc]
    exact ⟨hsp.1, by linarith [hsp.2]⟩
  · intro m _ _; exact Evar_nonneg _ _ _ _

end

end Work.S15crux
