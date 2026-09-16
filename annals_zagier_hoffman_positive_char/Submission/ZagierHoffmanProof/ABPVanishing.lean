import Submission.ZagierHoffmanProof.ABPZero
import Submission.ZagierHoffmanProof.ABPFunctionalEq

/-!
# The vanishing of the auxiliary function `E` (ABP, Step 6)

* `GSuperEntire.exists_prod_quot_X_sub_C` — dividing a super-entire series by a product of
  linear factors `(t - ω_i)` with `1 ≤ v ω_i` (the `ω_i` distinct) keeps it super-entire.
* ★★★ `ABP_eq_zero_of_functional_eq` — **the vanishing of `E`**: a nonzero super-entire series
  satisfying a twisted functional equation `∑_j b_j E^{(j)} = 0` with bounded integral
  coefficients, and vanishing at `N` points `ω_i` with `1 ≤ v ω_i ≤ r' < r`, satisfies
  `|coeff| ≤ |E|_r (r'/r)^N` (Gauss/Schwarz–Jensen), while Liouville gives `1 ≤ A v (coeff)`
  — contradiction when `A |E|_r (r'/r)^N < 1`.
-/

set_option autoImplicit false
open Filter Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **Division by a product of linear factors.**  If `E` is super-entire, `1 ≤ v (ω i)` for
`i ∈ s` and the `ω i` are distinct on `s`, then `E = (∏ᵢ (t - ω i)) · G` with `G` super-entire. -/
theorem GSuperEntire.exists_prod_quot_X_sub_C {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) {E : PowerSeries K} (hE : GSuperEntire γ E)
    {ι : Type*} (s : Finset ι) {ω : ι → K}
    (hω : ∀ i ∈ s, 1 ≤ Valued.v (ω i)) (hinj : Set.InjOn ω ↑s)
    (hroot : ∀ i ∈ s, evalSeriesGen E (ω i) = 0) :
    ∃ G : PowerSeries K, E = (∏ i ∈ s, (PowerSeries.X - PowerSeries.C (ω i))) * G ∧
      GSuperEntire γ G := by
  classical
  have hlin : ∀ i : ι, GSuperEntire γ (PowerSeries.X - PowerSeries.C (ω i)) := fun i =>
    (GSuperEntire.X (γ := γ) hγ0).sub (GSuperEntire.C γ (ω i))
  induction s using Finset.induction with
  | empty => exact ⟨E, by simp, hE⟩
  | insert a t ha ih =>
    have hroot_t : ∀ i ∈ t, evalSeriesGen E (ω i) = 0 :=
      fun i hi => hroot i (Finset.mem_insert_of_mem hi)
    have hinj_t : Set.InjOn ω ↑t := hinj.mono fun x hx => Finset.mem_insert_of_mem hx
    have hω_t : ∀ i ∈ t, 1 ≤ Valued.v (ω i) := fun i hi => hω i (Finset.mem_insert_of_mem hi)
    obtain ⟨G, hEG, hGs⟩ := ih hω_t hinj_t hroot_t
    have hP : GSuperEntire γ (∏ i ∈ t, (PowerSeries.X - PowerSeries.C (ω i))) :=
      GSuperEntire.prod hγ.le t _ fun i _ => hlin i
    have hPa : evalSeriesGen (∏ i ∈ t, (PowerSeries.X - PowerSeries.C (ω i))) (ω a) ≠ 0 := by
      rw [evalSeriesGen_prod hγ harch t _ (fun i _ => hlin i) (ω a)]
      have hterm : ∀ i ∈ t, evalSeriesGen (PowerSeries.X - PowerSeries.C (ω i)) (ω a)
          = ω a - ω i := by
        intro i _
        rw [evalSeriesGen_sub (f := PowerSeries.X) (g := PowerSeries.C (ω i)) hγ harch
          (GSuperEntire.X (γ := γ) hγ0) (GSuperEntire.C γ (ω i)), evalSeriesGen_X,
          evalSeriesGen_C]
      rw [Finset.prod_congr rfl hterm]
      intro hz
      rcases Finset.prod_eq_zero_iff.mp hz with ⟨i, hi, hzi⟩
      have hai : a = i := hinj (Finset.mem_insert_self a t) (Finset.mem_insert_of_mem hi)
        (sub_eq_zero.mp hzi)
      exact ha (hai ▸ hi)
    have hGa : evalSeriesGen G (ω a) = 0 := by
      have h1 : evalSeriesGen E (ω a)
          = evalSeriesGen (∏ i ∈ t, (PowerSeries.X - PowerSeries.C (ω i))) (ω a)
            * evalSeriesGen G (ω a) := by
        rw [hEG]
        exact evalSeriesGen_mul hγ harch hP hGs (ω a)
      rw [hroot a (Finset.mem_insert_self a t)] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hPa
    have ha0 : ω a ≠ 0 := by
      intro h0
      have h := hω a (Finset.mem_insert_self a t)
      rw [h0] at h
      simp at h
    obtain ⟨G', hG', hG's⟩ := GSuperEntire.exists_quot_X_sub_C hγ harch ha0
      (hω a (Finset.mem_insert_self a t)) hGs hGa
    refine ⟨G', ?_, hG's⟩
    rw [hEG, hG', Finset.prod_insert ha]
    ring

section vanishing

variable {q : ℕ} [FrobPow K q]

/-- ★★★ **The vanishing of the auxiliary function.**  Let `E ≠ 0` be super-entire with
`∑_{j≤ℓ} b_j E^{(j)} = 0`, where the nonzero constant terms of the `b_j` are integral and
bounded by `A_b`, and with at least one `b_j(0) ≠ 0`.  If `E` vanishes at `N` distinct points
`ω_i` with `1 ≤ v (ω_i) ≤ r' < r` and `A` is a Gauss norm of `E` at radius `r`, then
`1 ≤ A_b · A · (r'/r)^N`.  Consequently `E = 0` when `A_b · A · (r'/r)^N < 1`. -/
theorem le_of_functional_eq {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ℓ : ℕ} {b : ℕ → Polynomial K} {E : PowerSeries K} (hE : GSuperEntire γ E) (hE0 : E ≠ 0)
    (hfe : ∑ j ∈ Finset.range (ℓ + 1),
      (b j : PowerSeries K) * frobTwist (R := K) (p := q) j E = 0)
    {Ab : Γ₀} (hbint : ∀ j, (b j).coeff 0 ≠ 0 → 1 ≤ Valued.v ((b j).coeff 0))
    (hbnd : ∀ j, Valued.v ((b j).coeff 0) ≤ Ab)
    (hne : ∃ j ∈ Finset.range (ℓ + 1), (b j).coeff 0 ≠ 0)
    {r r' : Γ₀} (hr1 : 1 ≤ r') (hrr : r' < r) {N : ℕ} {ω : Fin N → K}
    (hω1 : ∀ i, 1 ≤ Valued.v (ω i)) (hω2 : ∀ i, Valued.v (ω i) ≤ r')
    (hinj : Function.Injective ω) (hroot : ∀ i, evalSeriesGen E (ω i) = 0)
    {A : Γ₀} (hA : IsGaussNormAt r E A) :
    1 ≤ Ab * (A * (r' / r) ^ N) := by
  classical
  have hr1' : 1 ≤ r := le_of_lt (lt_of_le_of_lt hr1 hrr)
  have hrne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr1')
  have hex : ∃ n, PowerSeries.coeff n E ≠ 0 := by
    by_contra h
    push Not at h
    exact hE0 (PowerSeries.ext fun n => by rw [h n, map_zero])
  set m := Nat.find hex with hmdef
  have hm : PowerSeries.coeff m E ≠ 0 := Nat.find_spec hex
  have hmin : ∀ k < m, PowerSeries.coeff k E = 0 := fun k hk => by
    by_contra h
    have := Nat.find_min' hex h
    omega
  -- Liouville
  have hrel := sum_coeff_eq_zero_of_sum_frobTwist (E := E) (m := m) (ℓ := ℓ) (a := b) hmin hfe
  have hliou : 1 ≤ Ab * Valued.v (PowerSeries.coeff m E) :=
    le_mul_v_of_sum_pow_eq_zero (q := q) (c := fun j => (b j).coeff 0) hq
      (fun j hj => hbint j hj) (fun j => hbnd j) hne hm hrel
  -- Gauss / Schwarz-Jensen
  obtain ⟨G, hEG, hGs⟩ := GSuperEntire.exists_prod_quot_X_sub_C hγ0 hγ harch hE Finset.univ
    (fun i _ => hω1 i) (fun x _ y _ h => hinj h) (fun i _ => hroot i)
  obtain ⟨B, hB⟩ := exists_isGaussNormAt_of_GSuperEntire hγ harch hGs r
  have hSJ := v_coeff_le_of_gaussNorm hr1' (fun i _ => hω1 i)
    (fun i _ => le_trans (hω2 i) hrr.le) hEG hA hB m
  rw [Finset.card_univ, Fintype.card_fin] at hSJ
  have hprod : (∏ i : Fin N, Valued.v (ω i)) ≤ r' ^ N := by
    calc (∏ i : Fin N, Valued.v (ω i)) ≤ ∏ _i : Fin N, r' :=
          Finset.prod_le_prod (fun i _ => zero_le) (fun i _ => hω2 i)
      _ = r' ^ N := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hgauss : Valued.v (PowerSeries.coeff m E) ≤ A * (r' / r) ^ N := by
    calc Valued.v (PowerSeries.coeff m E)
        ≤ (∏ i : Fin N, Valued.v (ω i)) * A * (r ^ N)⁻¹ := hSJ
      _ ≤ r' ^ N * A * (r ^ N)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod zero_le) zero_le
      _ = A * ((r') ^ N * (r ^ N)⁻¹) := by rw [mul_comm (r' ^ N) A, mul_assoc]
      _ = A * (r' / r) ^ N := by rw [div_pow, div_eq_mul_inv]
  exact le_trans hliou (mul_le_mul_of_nonneg_left hgauss zero_le)

/-- **The vanishing of `E`** in the form used by the criterion. -/
theorem eq_zero_of_functional_eq {γ : Γ₀} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ℓ : ℕ} {b : ℕ → Polynomial K} {E : PowerSeries K} (hE : GSuperEntire γ E)
    (hfe : ∑ j ∈ Finset.range (ℓ + 1),
      (b j : PowerSeries K) * frobTwist (R := K) (p := q) j E = 0)
    {Ab : Γ₀} (hbint : ∀ j, (b j).coeff 0 ≠ 0 → 1 ≤ Valued.v ((b j).coeff 0))
    (hbnd : ∀ j, Valued.v ((b j).coeff 0) ≤ Ab)
    (hne : ∃ j ∈ Finset.range (ℓ + 1), (b j).coeff 0 ≠ 0)
    {r r' : Γ₀} (hr1 : 1 ≤ r') (hrr : r' < r) {N : ℕ} {ω : Fin N → K}
    (hω1 : ∀ i, 1 ≤ Valued.v (ω i)) (hω2 : ∀ i, Valued.v (ω i) ≤ r')
    (hinj : Function.Injective ω) (hroot : ∀ i, evalSeriesGen E (ω i) = 0)
    {A : Γ₀} (hA : IsGaussNormAt r E A) (hsmall : Ab * (A * (r' / r) ^ N) < 1) :
    E = 0 := by
  by_contra hE0
  have h1 := le_of_functional_eq hγ0 hγ harch hq hE hE0 hfe hbint hbnd hne hr1 hrr hω1 hω2
    hinj hroot hA
  exact absurd h1 (not_le.mpr hsmall)

end vanishing

end ZagierHoffmanPositiveChar
