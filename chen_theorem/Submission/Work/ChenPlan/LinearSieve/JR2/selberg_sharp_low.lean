import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.selberg_pair
import Submission.Work.ChenPlan.LinearSieve.Selberg.gsum_bound_dense
import Submission.Work.ChenPlan.LinearSieve.Framework

/-!
# `selberg_sharp_low`: the sharp Selberg bound for the low parameter range `1/4 ≤ s ≤ 2`

The sharp Selberg (Ankeny–Onishi) upper bound for the linear sieve,
`S(A,Z) ≤ X·Vf A Z·(2 e^γ / s + η) + remSum A D`, is available from
`Selberg.selberg_pair.upperValidAll_selbergU` for `s = log D / log Z ∈ [1,2]` (and hence
`UpperValid K (2e^γ/s) 1 2`).  Here the range is extended down to `s ≥ 1/4`, which is what the
Jurkat–Richert assembly needs at the low end.

Two ingredients are re-proved for the wider range:

* `Selberg.gsum_bound_dense_low`: the Ankeny–Onishi `G`-bound `s/(2e^γ) - η ≤ gSum A (√D)·Vf A Z`.
  Its proof (`Selberg.gsum_bound_dense`) consumes `s ≥ 1` only through `θ = s/2 ≥ 1/2 > delta`; for
  `s ≥ 1/4` we have `θ ≥ 1/8`, so it suffices to enlarge `D₀` so that `delta ≤ min η 1/16 < 1/8`.
* `key_sharp_low`: the elementary numerical inequality
  `1 ≤ (s/(2e^γ) - δ)·(2e^γ/s + η)`, whose proof only needs `s ≥ 1/4` (it is the reciprocal
  bookkeeping of the `G`-bound).

The proof of `gsum_bound_dense_low` below is the body of `Selberg.gsum_bound_dense` with the
threshold constant `8` replaced by `32` (so that `delta ≤ min η 1 / 16 < 1/8 ≤ θ`) and the range
hypothesis `1 ≤ s` relaxed to `1/4 ≤ s`; every other step is unchanged.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ChenPlan.LinearSieve.Selberg

open Work.ChenPlan.LinearSieve
open Work.ChenPlan.LinearSieve.Selberg.Alt

variable {A : BoundingSieve}

open MeasureTheory in

theorem gsum_bound_dense_low (K : ℝ) (hK : 0 ≤ K) :
    ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (Z : ℕ) (D : ℝ),
      2 ≤ Z → D₀ ≤ D → Work.ChenPlan.LinearSieve.IsLinearNat A Z K →
      1 / 4 ≤ Real.log D / Real.log Z → Real.log D / Real.log Z ≤ 2 →
      Real.log D / Real.log Z / (2 * Real.exp Real.eulerMascheroniConstant) - η
        ≤ Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) * Work.ChenPlan.LinearSieve.Vf A Z := by
  intro η hη
  set G : ℝ := Real.exp Real.eulerMascheroniConstant with hGdef
  have hGpos : 0 < G := by rw [hGdef]; exact Real.exp_pos _
  have hG1 : 1 ≤ G := by
    rw [hGdef]
    exact le_of_lt (Real.one_lt_exp_iff.mpr (by linarith [Real.one_half_lt_eulerMascheroniConstant]))
  set η₁ : ℝ := min η 1 with hη₁
  have hη₁pos : 0 < η₁ := lt_min hη one_pos
  have hη₁le : η₁ ≤ η := min_le_left _ _
  have hη₁1 : η₁ ≤ 1 := min_le_right _ _
  set ε : ℝ := η / (2 * G) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  refine ⟨Real.exp (32 * (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / η₁ + 1), ?_⟩
  intro A Z D hZ2 hD hlin hs1 hs2
  have hZ1 : 1 < Z := by omega
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast hZ1)
  have hD₀pos : 0 < Real.exp (32 * (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / η₁ + 1) :=
    Real.exp_pos _
  have hDpos : 0 < D := lt_of_lt_of_le hD₀pos hD
  have hsq : Real.sqrt D ≤ (Z : ℝ) := sqrt_le_of_log_div_le_two hDpos hZ1 hs2
  have hZP : ∀ p ∈ A.prodPrimes.primeFactors, p < Z := hlin.1
  have hlogDpos : 0 < Real.log D := by
    have h := (le_div_iff₀ hlogZ).mp hs1
    linarith
  -- the parameter `θ = log D / (2 log Z) ∈ [1/8,1]`
  set θ : ℝ := Real.log D / (2 * Real.log (Z : ℝ)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by positivity : (0 : ℝ) < 2 * Real.log Z)]
    linarith [(div_le_iff₀ hlogZ).mp hs2]
  have hθeighth : 1 / 8 ≤ θ := by
    rw [hθdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log Z)]
    have h := (le_div_iff₀ hlogZ).mp hs1
    linarith
  -- the light-prime error
  have hdelta_le : delta A Z K ε ≤ η₁ / 16 := by
    refine le_trans (delta_le A hK hZ2 hεpos) ?_
    have h1 : 32 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ + 1 ≤ Real.log D := by
      have h := Real.log_le_log hD₀pos hD
      rw [Real.log_exp] at h
      calc 32 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ + 1
          = 32 * (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / η₁ + 1 := by ring
        _ ≤ Real.log D := h
    have h2 : Real.log (Real.sqrt D) ≤ Real.log Z :=
      Real.log_le_log (Real.sqrt_pos.mpr hDpos) hsq
    rw [Real.log_sqrt hDpos.le] at h2
    have h3 : 16 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ ≤ Real.log Z := by
      rw [div_le_iff₀ hη₁pos]
      have h4 : 32 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ))
          ≤ Real.log D * η₁ := by
        have h5 : 32 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ ≤ Real.log D := by
          linarith
        exact (div_le_iff₀ hη₁pos).mp h5
      have h6 : Real.log D * η₁ ≤ 2 * Real.log (Z : ℝ) * η₁ :=
        mul_le_mul_of_nonneg_right (by linarith : Real.log D ≤ 2 * Real.log (Z : ℝ)) hη₁pos.le
      linarith
    have h4 : (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) ≤ (Real.log Z) * (η₁ / 16) := by
      have := (div_le_iff₀ hη₁pos).mp h3
      linarith
    rw [div_le_iff₀ hlogZ]
    linarith
  have hδlt : delta A Z K ε < θ := by
    linarith [hdelta_le, hθeighth, hη₁1]
  set θ' : ℝ := (θ - delta A Z K ε) / (1 + ε) with hθ'def
  have hθ'pos : 0 < θ' := by
    rw [hθ'def]; exact div_pos (by linarith) (by positivity)
  have hθ'1 : θ' ≤ 1 := by
    rw [hθ'def, div_le_one (by positivity : (0 : ℝ) < 1 + ε)]
    linarith [hθ1, delta_nonneg (A := A) Z K ε]
  -- the rooms
  let a : {p // p ∈ A.prodPrimes.primeFactors} → ℝ := fun p => roomA A p
  let b : {p // p ∈ A.prodPrimes.primeFactors} → ℝ := fun p => roomB A p
  have hbma : ∀ i : {p // p ∈ A.prodPrimes.primeFactors}, b i - a i = atomMass A (i : ℕ) :=
    fun i => roomB_sub_roomA A (i : ℕ)
  have ha : ∀ i, 0 ≤ a i := fun i => roomA_nonneg A (i : ℕ)
  have hab : ∀ i, a i ≤ b i := fun i => by
    have := atomMass_pos A i.2
    simp only [a, b, roomB]
    linarith
  have hdisj : ∀ i j : {p // p ∈ A.prodPrimes.primeFactors}, i ≠ j →
      Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne (fun h => hij (Subtype.ext h)) with h | h
    · exact room_disjoint A i.2 j.2 h
    · exact (room_disjoint A j.2 i.2 h).symm
  -- the up-set probabilities
  have hup : ∀ U : Finset {p // p ∈ A.prodPrimes.primeFactors},
      ENNReal.toReal (canonM (⋂ i ∈ U, Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)))
        = ∏ i ∈ U, (1 - Real.exp (-(b i - a i))) := fun U =>
    hit_all_prob canonM (fun i (x : ℕ → ℝ) => x i)
      (fun i => (coord_measurable i).aemeasurable) (fun i => coord_isStdExp i) coord_iIndep
      a b ha hab hdisj U
  -- the CDF identity
  have hcdf := Work.LinearSieve.Selberg.selectionMass_eq_measure (μ := canonM)
    (H := fun i : {p // p ∈ A.prodPrimes.primeFactors} =>
      Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i))
    (fun i => measurableSet_intervalHit _ coord_measurable (a i) (b i))
    (fun i : {p // p ∈ A.prodPrimes.primeFactors} => Real.exp (-(b i - a i))) hup
    (fun i : {p // p ∈ A.prodPrimes.primeFactors} => levelLog Z (i : ℕ)) θ
  -- the identification with `Vf * gSum`
  have hkey : Work.ChenPlan.LinearSieve.Vf A Z * Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D)
      = ENNReal.toReal (canonM {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
          levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
            (fun _ => (1 : ℝ)) ω) < θ}) := by
    rw [Vf_mul_gSum_sqrt_eq_thetaSum A hDpos rfl hZ1 hZP, hcdf]
    refine Finset.sum_bij (fun (S : Finset ℕ) (_ : S ∈ A.prodPrimes.primeFactors.powerset.filter
        (fun S => (∑ p ∈ S, levelLog Z p) < θ)) =>
        Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S))
      ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_filter] at hS ⊢
      refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
      rw [sum_level_eq (A := A) S (Finset.mem_powerset.mp hS.1)]
      exact hS.2
    · intro S hS S' hS' h
      have h1 : (Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
          (x : ℕ) ∈ S)).image (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)) = S :=
        val_image_filter (A := A) S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
      have h2 : (Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
          (x : ℕ) ∈ S')).image (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)) = S' :=
        val_image_filter (A := A) S' (Finset.mem_powerset.mp (Finset.mem_filter.mp hS').1)
      rw [← h1, h, h2]
    · intro T hT
      rw [Finset.mem_filter] at hT
      refine ⟨T.image (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_powerset.mpr (Finset.image_subset_iff.mpr (fun x _ => x.2)), ?_⟩
        rw [← sum_level_eq (A := A) _ (Finset.image_subset_iff.mpr (fun x _ => x.2))]
        · rw [filter_mem_image_val (A := A) T]
          exact hT.2
      · exact filter_mem_image_val (A := A) T
    · intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hSpow, hSθ⟩ := hS
      have hsub : S ⊆ A.prodPrimes.primeFactors := Finset.mem_powerset.mp hSpow
      show (∏ p ∈ S, A.nu p) * ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p)
        = (∏ i ∈ Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
              (x : ℕ) ∈ S), (1 - Real.exp (-(b i - a i))))
          * ∏ i ∈ (Finset.univ : Finset {p // p ∈ A.prodPrimes.primeFactors}) \
              Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S),
              Real.exp (-(b i - a i))
      have h1 : (∏ i ∈ Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
            (x : ℕ) ∈ S), (1 - Real.exp (-(b i - a i))))
          = ∏ p ∈ S, A.nu p := by
        rw [← prod_nu_eq (A := A) S hsub]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [hbma i, one_sub_exp_neg_atomMass A i.2]
      have h2 : (∏ i ∈ (Finset.univ : Finset {p // p ∈ A.prodPrimes.primeFactors}) \
            Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S),
            Real.exp (-(b i - a i)))
          = ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p) := by
        simp only [hbma]
        exact prod_exp_eq (A := A) S hsub
      rw [h1, h2]
  -- the coupling and the reference CDF
  have hle : ENNReal.toReal (canonM (Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ'))
      ≤ ENNReal.toReal (canonM {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
          levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
            (fun _ => (1 : ℝ)) ω) < θ}) := by
    set t : Set (ℕ → ℝ) := {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
        levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
          (fun _ => (1 : ℝ)) ω) < θ} with htdef
    set s : Set (ℕ → ℝ) := Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ' with hsdef
    have ht : MeasurableSet t := by
      rw [htdef]
      exact refSumLt_summand_measurable _ coord_measurable θ _ a b
    have hae_sub : ∀ᵐ ω ∂canonM, ω ∈ s → ω ∈ t := by
      filter_upwards [hae_summable] with ω hsum hlt
      have hpt := hitSum_le_refSum_add_delta A hK hZ2 hlin hεpos
        (fun i (x : ℕ → ℝ) => x i) ω hsum
      have hlt' : Alt.refSum (fun i => ω i) < θ' := hlt
      have h3 : (1 + ε) * Alt.refSum (fun i => ω i) + delta A Z K ε < θ := by
        have h2 : (1 + ε) * ((θ - delta A Z K ε) / (1 + ε)) + delta A Z K ε = θ := by
          field_simp
          ring
        rw [hθ'def] at hlt'
        linarith [mul_lt_mul_of_pos_left hlt' (by linarith : (0 : ℝ) < 1 + ε)]
      exact lt_of_le_of_lt hpt h3
    have hnull : canonM (s \ t) = 0 := by
      refine measure_mono_null ?_ (by rw [← ae_iff]; exact hae_sub)
      intro ω hω
      simp only [Set.mem_diff, Set.mem_setOf_eq] at hω ⊢
      exact fun h => hω.2 (h hω.1)
    have hmono : canonM s ≤ canonM t := by
      have hsplit := MeasureTheory.measure_inter_add_diff (μ := canonM) s ht
      calc canonM s = canonM (s ∩ t) + canonM (s \ t) := hsplit.symm
        _ = canonM (s ∩ t) + 0 := by rw [hnull]
        _ = canonM (s ∩ t) := by rw [add_zero]
        _ ≤ canonM t := measure_mono (μ := canonM) Set.inter_subset_right
    exact ENNReal.toReal_mono (measure_ne_top canonM t) hmono
  have href : ENNReal.toReal (canonM (Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ'))
      = θ' / G := by
    rw [refsum_cdf canonM (fun i (x : ℕ → ℝ) => x i)
      (fun i => (coord_measurable i).aemeasurable) (fun i => coord_isStdExp i) coord_iIndep
      hθ'pos hθ'1, hGdef]
  -- the arithmetic
  have harith : θ / G - η ≤ θ' / G := by
    have hGε : G * ε = η / 2 := by rw [hεdef]; field_simp
    have hnum : ε * θ + delta A Z K ε ≤ η * G * (1 + ε) := by
      have h1 : ε * θ ≤ ε := by nlinarith [hθ1, hεpos]
      have h2 : delta A Z K ε ≤ η / 4 := le_trans hdelta_le (by linarith)
      have h3 : η * G * (1 + ε) = η * G + η ^ 2 / 2 := by nlinarith [hGε]
      have h4 : η / 4 + ε ≤ η * G + η ^ 2 / 2 := by
        have hεb : ε ≤ η / 2 := by
          rw [hεdef, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * G)]
          nlinarith [hG1, hη]
        nlinarith [hεb, hG1, hη, sq_nonneg η]
      linarith
    rw [hθ'def]
    rw [show (θ - delta A Z K ε) / (1 + ε) / G
        = (θ - delta A Z K ε) / (G * (1 + ε)) from by field_simp]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < G * (1 + ε))]
    have hsub : (θ / G - η) * (G * (1 + ε)) = θ * (1 + ε) - η * G * (1 + ε) := by
      field_simp
    rw [hsub]
    nlinarith [hnum]
  have hθG : θ / G = Real.log D / Real.log Z / (2 * Real.exp Real.eulerMascheroniConstant) := by
    simp only [hθdef, hGdef]
    field_simp
  rw [← hθG]
  calc θ / G - η ≤ θ' / G := harith
    _ = ENNReal.toReal (canonM (Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ')) := href.symm
    _ ≤ ENNReal.toReal (canonM {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
          levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
            (fun _ => (1 : ℝ)) ω) < θ}) := hle
    _ = Work.ChenPlan.LinearSieve.Vf A Z * Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) :=
        hkey.symm
    _ = Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) * Work.ChenPlan.LinearSieve.Vf A Z := by ring

end Work.ChenPlan.LinearSieve.Selberg

namespace Work.ChenPlan.LinearSieve.JR2

/-- **The reciprocal bookkeeping of the sharp Selberg bound, for `s ≥ 1/4`.**  If the `G`-bound
gives `s/(2e^γ) - δ ≤ gSum · Vf` then multiplying by `2e^γ/s + η` must return at least `1`, so that
`X/gSum ≤ X·Vf·(2e^γ/s + η)`; this is where the (harmless) loss `min η 1 / 10^9` in the `G`-bound
is paid for.  Same as `Selberg.key_sharp`, with the hypothesis `1 ≤ s` relaxed to `1/4 ≤ s`
(the constants `1/6`, `6` become `1/24`, `24`). -/
theorem key_sharp_low (s η : ℝ) (hs1 : 1 / 4 ≤ s) (hs2 : s ≤ 2) (hη : 0 < η) :
    1 ≤ (s / (2 * Real.exp Real.eulerMascheroniConstant) - min η 1 / 10 ^ 9) *
        (2 * Real.exp Real.eulerMascheroniConstant / s + η) := by
  obtain ⟨hE1, hE3⟩ := Work.ChenPlan.LinearSieve.Selberg.exp_gamma_bounds
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hs0 : 0 < s := by linarith
  have ha : (1 : ℝ) / 24 ≤ s / (2 * E) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hs1, hE3]
  have hb : 2 * E / s ≤ 24 := by
    rw [div_le_iff₀ hs0]
    nlinarith [hs1, hE3]
  have hkey : (min η 1 / 10 ^ 9) * (24 + η) ≤ η * ((1 : ℝ) / 24) := by
    by_cases h1 : η ≤ 1
    · rw [min_eq_left h1]
      nlinarith [hη, h1, (by norm_num : (25 : ℝ) / 10 ^ 9 ≤ 1 / 24)]
    · push_neg at h1
      rw [min_eq_right h1.le]
      nlinarith [h1, (by norm_num : (25 : ℝ) / 10 ^ 9 ≤ 1 / 24)]
  have hstep : (min η 1 / 10 ^ 9) * (2 * E / s + η) ≤ η * (s / (2 * E)) := by
    have h1 : (min η 1 / 10 ^ 9) * (2 * E / s + η) ≤ (min η 1 / 10 ^ 9) * (24 + η) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : η * ((1 : ℝ) / 24) ≤ η * (s / (2 * E)) := mul_le_mul_of_nonneg_left ha hη.le
    linarith
  have hexp : (s / (2 * E) - min η 1 / 10 ^ 9) * (2 * E / s + η)
      = 1 + (η * (s / (2 * E)) - (min η 1 / 10 ^ 9) * (2 * E / s + η)) := by
    field_simp
    ring
  linarith [hstep, hexp]

/-- **The sharp Selberg bound (Ankeny–Onishi) for the low parameter range `1/4 ≤ s ≤ 2`.**
Variant of `Selberg.selberg_pair.upperValidAll_selbergU` (`UpperValidAll K selbergU 1`, only
`s ≥ 1`) with the parameter range extended down to `1/4`: for every `K ≥ 0`, `η > 0` there is `D₀`
with
`S(A,Z) ≤ X·Vf A Z·(2 e^γ / s + η) + remSum A D`,  `s = log D / log Z ∈ [1/4, 2]`.

Blueprint: `Selberg/selberg_pair.lean` (`selbergU`, `key_sharp`, `upperValidAll_selbergU`) and
`Selberg/gsum_bound_dense.lean` (`gsum_bound_dense K hK : ∃ D₀, ∀ A Z D, 2 ≤ Z → D₀ ≤ D →
IsLinearNat A Z K → 1 ≤ log D/log Z → log D/log Z ≤ 2 → s/(2e^γ) - η ≤ gSum A (√D)·Vf A Z`),
plus `SelbergBound.selberg_bound` (`S ≤ totalMass/gSum(√D) + remSum D`).

Both `gsum_bound_dense` and `key_sharp` need their range hypothesis relaxed to `s ≥ 1/4`
(the `s ≥ 1` hypothesis of `gsum_bound_dense` is consumed only to get
`delta < θ = s/2 ≥ 1/8`: enlarge `D₀` so that `delta < 1/8`; `key_sharp` must be reproved for
`s ≥ 1/4`, it hardcodes `s ≳ 0.59`).  Note: the two-level "fallback" (using the `s = 1` case for
`s < 1`) is UNSOUND — `gSum` is increasing in the level — the direct extension is required. -/
theorem selberg_sharp_low (K : ℝ) (hK : 0 ≤ K) :
    Work.ChenPlan.LinearSieve.UpperValid K
      (fun s : ℝ => 2 * Real.exp Real.eulerMascheroniConstant / s) (1/4) 2 := by
  intro η hη
  obtain ⟨D₀, hD₀⟩ := Work.ChenPlan.LinearSieve.Selberg.gsum_bound_dense_low K hK
    (min η 1 / 10 ^ 9) (by positivity)
  refine ⟨max D₀ 2, ?_⟩
  intro A Z D hZ hD hlin hX hs1 hs2
  obtain ⟨hprimes, hprod⟩ := hlin
  have hD_D0 : D₀ ≤ D := le_trans (le_max_left _ _) hD
  have hDge : (2 : ℝ) ≤ D := le_trans (le_max_right _ _) hD
  have hD1lt : (1 : ℝ) < D := by linarith
  have hDnn : (0 : ℝ) ≤ D := by linarith
  have hZ2 : (2 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hlogD0 : 0 < Real.log D := by
    have h := (le_div_iff₀ hlogZ).mp hs1
    linarith
  have hVf : Work.ChenPlan.LinearSieve.Vf A Z = Submission.ChenPlan.sieveV A :=
    Work.ChenPlan.LinearSieve.Vf_eq_sieveV A hprimes
  rw [Work.ChenPlan.LinearSieve.siftedSumLt_eq_siftedSum A hprimes, hVf]
  have hb := hD₀ A Z D hZ hD_D0 ⟨hprimes, hprod⟩ hs1 hs2
  have hsqrt1 : 1 < Real.sqrt D := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using hD1lt
  have hGpos : 0 < Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) :=
    Work.ChenPlan.LinearSieve.gSum_pos A hsqrt1
  have hsel := Work.ChenPlan.LinearSieve.selberg_bound A hsqrt1 hX
  rw [Real.sq_sqrt hDnn] at hsel
  have hnum := key_sharp_low (Real.log D / Real.log Z) η hs1 hs2 hη
  have hkey : 1 ≤ Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) *
      Work.ChenPlan.LinearSieve.Vf A Z *
      (2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) + η) := by
    have hden : 0 ≤ Real.log D / Real.log Z := div_nonneg hlogD0.le hlogZ.le
    have hnonneg : (0 : ℝ) ≤
        2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) + η := by
      have h2 : (0 : ℝ) ≤ 2 * Real.exp Real.eulerMascheroniConstant /
          (Real.log D / Real.log Z) := div_nonneg (by positivity) hden
      linarith
    have h := mul_le_mul_of_nonneg_right hb hnonneg
    linarith
  have hmain : A.totalMass / Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) ≤
      A.totalMass * Submission.ChenPlan.sieveV A *
        (2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) + η) := by
    rw [div_le_iff₀ hGpos]
    calc A.totalMass = A.totalMass * 1 := (mul_one _).symm
      _ ≤ A.totalMass * (Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) *
            Work.ChenPlan.LinearSieve.Vf A Z *
            (2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) + η)) :=
          mul_le_mul_of_nonneg_left hkey hX
      _ = A.totalMass * Submission.ChenPlan.sieveV A *
            (2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) + η) *
            Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) := by
          rw [hVf]; ring
  show BoundingSieve.siftedSum ≤ A.totalMass * Submission.ChenPlan.sieveV A *
      (2 * Real.exp Real.eulerMascheroniConstant / (Real.log D / Real.log Z) + η) +
      Submission.ChenPlan.remSum A D
  linarith [hsel, hmain]

end Work.ChenPlan.LinearSieve.JR2
