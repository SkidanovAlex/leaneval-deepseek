import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.summable_int_inv_one_add_abs_pow
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.integrable_Fhat_sq

namespace Work.GM.Affine

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform Topology

open Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

/-!
# The tail part of the far weight (GM §9, region II)

The tail `Wtail K M₃ B y = M₃ Σ_{ℓ : |ℓ-y| > max(2,B)/M₃} ψ̂₁(M₃(ℓ-y))` is controlled by the
fast decay of `ψ̂₁`: since every retained lattice point satisfies `M₃|ℓ-y| > B`, the lattice sum
is `≲ B^{-(N-1)}`.  Consequently the corresponding piece of `ĝ` is small, and one obtains
`∫_{region II} ‖Σ_{m₁} |m₁|⁻¹ Bsum(ξ/m₁) Wtail(ξ/m₁)‖² ≤ C M₁M₃²/B^{2(N-1)} ∫ (Hsum)²`,
the factor `∫ (Hsum)²` coming from Plancherel for `Bsum = 𝓕 (Hsum)`.
-/

/-! ## A lattice tail estimate -/

/-- The bijection `ℕ ≃ {ℓ : ℤ // m ≤ ℓ}`, `j ↦ m + j`. -/
def intIciEquiv (m : ℤ) : ℕ ≃ {ℓ : ℤ // m ≤ ℓ} where
  toFun j := ⟨m + (j : ℤ), by omega⟩
  invFun x := (x.1 - m).toNat
  left_inv j := by
    simp only
    have h : m + (j:ℤ) - m = (j:ℤ) := by ring
    rw [h, Int.toNat_natCast]
  right_inv x := by
    obtain ⟨ℓ, hℓ⟩ := x
    apply Subtype.ext
    simp only
    have h : 0 ≤ ℓ - m := by omega
    rw [Int.toNat_of_nonneg h]
    ring

/-- Reindexing a `ℤ`-sum over a half-line as a sum over `ℕ`. -/
lemma tsum_int_Ici_eq_tsum_nat (g : ℝ → ℝ) (m : ℤ) :
    (∑' (ℓ : ℤ), if m ≤ ℓ then g ((ℓ : ℝ)) else 0) = ∑' (j : ℕ), g (((m + j : ℤ) : ℝ)) := by
  have h1 : (∑' (x : {ℓ : ℤ // m ≤ ℓ}), g ((x.1 : ℝ)))
      = ∑' (ℓ : ℤ), if m ≤ ℓ then g ((ℓ : ℝ)) else 0 := by
    refine (tsum_subtype (s := {ℓ : ℤ | m ≤ ℓ}) (f := fun ℓ : ℤ => g ((ℓ : ℝ)))).trans ?_
    apply tsum_congr
    intro ℓ
    by_cases h : m ≤ ℓ
    · simp [Set.indicator_of_mem, h]
    · simp [Set.indicator_of_notMem, h]
  rw [← h1]
  exact (Equiv.tsum_eq (intIciEquiv m) (fun x : {ℓ : ℤ // m ≤ ℓ} => g ((x.1 : ℝ)))).symm

/-- The tail integral `∫_{(0,∞)} (c + M t)^{-N} dt = c^{1-N}/((N-1) M)`, for `c > 0`, `M > 0`,
`N ≥ 2`. -/
lemma integral_Ioi_inv_add_pow {M c : ℝ} (hM : 0 < M) (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N) :
    (∫ t in Set.Ioi (0:ℝ), (1:ℝ) / (c + M*t)^N) = (1/((N:ℝ)-1)) * (1/(M * c^(N-1))) := by
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hsub : (∫ t in Set.Ioi (0:ℝ), (1:ℝ) / (c + M*t)^N)
      = M⁻¹ * ∫ x in Set.Ioi (0:ℝ), (1:ℝ)/(c + x)^N := by
    simpa [smul_eq_mul, mul_zero] using
      (integral_comp_mul_left_Ioi (g := fun x : ℝ => (1:ℝ)/(c + x)^N) (a := 0) (b := M) hM)
  have hmain : (∫ x in Set.Ioi (0:ℝ), (1:ℝ)/(c+x)^N) = (1/((N:ℝ)-1)) * (1/c^(N-1)) := by
    have hp : (1:ℝ) - (N:ℝ) = -((N:ℝ)-1) := by ring
    have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
        HasDerivAt (fun y : ℝ => - ((c+y)^((1:ℝ)-(N:ℝ)))/((N:ℝ)-1)) ((1:ℝ)/(c+x)^N) x := by
      intro x hx
      have hx0 : (0:ℝ) ≤ x := hx
      have hcx : 0 < c + x := by linarith
      have h1 : HasDerivAt (fun y : ℝ => c + y) 1 x := (hasDerivAt_id x).const_add c
      have h2 : HasDerivAt (fun y : ℝ => (c + y)^((1:ℝ)-(N:ℝ)))
          (1 * ((1:ℝ)-(N:ℝ)) * (c+x)^(((1:ℝ)-(N:ℝ))-1)) x :=
        h1.rpow_const (Or.inl (ne_of_gt hcx))
      have h3 : HasDerivAt (fun y : ℝ => - ((c+y)^((1:ℝ)-(N:ℝ)))/((N:ℝ)-1))
          (-(1 * ((1:ℝ)-(N:ℝ)) * (c+x)^(((1:ℝ)-(N:ℝ))-1)) / ((N:ℝ)-1)) x :=
        (h2.neg).div_const ((N:ℝ)-1)
      refine h3.congr_deriv ?_
      rw [show ((1:ℝ)-(N:ℝ)) - 1 = -(N:ℝ) by ring]
      rw [Real.rpow_neg (le_of_lt hcx) (N:ℝ), Real.rpow_natCast]
      rw [one_div, div_eq_mul_inv]
      have hne : ((N:ℝ) - 1) ≠ 0 := by linarith
      field_simp
      ring
    have hint : IntegrableOn (fun x : ℝ => (1:ℝ)/(c+x)^N) (Set.Ioi 0) := by
      have h := integrableOn_add_rpow_Ioi_of_lt (a := -(N:ℝ)) (c := (0:ℝ)) (m := c)
        (by linarith : -(N:ℝ) < -1) (by linarith : -c < 0)
      refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
      have hx0 : (0:ℝ) < x := hx
      have hxa : (0:ℝ) ≤ x + c := by linarith
      show (x + c) ^ (-(N:ℝ)) = 1/(c+x)^N
      rw [Real.rpow_neg hxa (N:ℝ), Real.rpow_natCast, add_comm c x, one_div]
    have htend : Tendsto (fun y : ℝ => - ((c+y)^((1:ℝ)-(N:ℝ)))/((N:ℝ)-1)) atTop (𝓝 0) := by
      have hpos : (0:ℝ) < (N:ℝ) - 1 := by linarith
      have h1 : Tendsto (fun y : ℝ => (c+y)^((1:ℝ)-(N:ℝ))) atTop (𝓝 0) := by
        rw [hp]
        exact (tendsto_rpow_neg_atTop hpos).comp (tendsto_atTop_add_const_left atTop c tendsto_id)
      have h2 := (h1.div_const ((N:ℝ)-1)).neg
      simpa [neg_div] using h2
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (0:ℝ)) (f := fun y : ℝ => - ((c+y)^((1:ℝ)-(N:ℝ)))/((N:ℝ)-1))
      (f' := fun x : ℝ => (1:ℝ)/(c+x)^N) (m := 0) hderiv hint htend
    rw [hFTC]
    have hp2 : (1:ℝ) - (N:ℝ) = -(((N-1:ℕ)):ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]; ring
    rw [add_zero, hp2, Real.rpow_neg (le_of_lt hc) (((N-1:ℕ)):ℝ), Real.rpow_natCast]
    simp only [zero_sub, neg_div, neg_neg]
    rw [one_div, div_eq_mul_inv, div_eq_mul_inv]
    have hne : ((N:ℝ) - 1) ≠ 0 := by linarith
    have hcne : c ^ (N-1) ≠ 0 := pow_ne_zero _ (ne_of_gt hc)
    field_simp
  rw [hsub, hmain]
  have hMne : M ≠ 0 := ne_of_gt hM
  have hcne : c ^ (N-1) ≠ 0 := pow_ne_zero _ (ne_of_gt hc)
  field_simp

/-- The lattice family `ℓ ↦ (1 + M |ℓ-y|)^{-N}` is summable for `M ≥ 1`, `N ≥ 2`. -/
lemma summable_lattice_inv_pow (M₃ y : ℝ) (hM₃ : 1 ≤ M₃) {N : ℕ} (hN : 2 ≤ N) :
    Summable (fun ℓ : ℤ => (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N) := by
  have hbase : Summable (fun ℓ : ℤ => (1:ℝ)/(1 + |((ℓ:ℤ):ℝ)|)^N) :=
    summable_int_inv_one_add_abs_pow N (by omega)
  refine Summable.of_norm_bounded
    (g := fun ℓ : ℤ => (1+|y|)^N * ((1:ℝ)/(1 + |((ℓ:ℤ):ℝ)|)^N)) (hbase.mul_left _) ?_
  intro ℓ
  rw [Real.norm_of_nonneg (by positivity)]
  have h2 : |((ℓ:ℤ):ℝ)| ≤ |((ℓ:ℤ):ℝ) - y| + |y| := by
    have h := abs_add_le (((ℓ:ℤ):ℝ) - y) y
    rwa [sub_add_cancel] at h
  have h1 : (1:ℝ) + |((ℓ:ℤ):ℝ)| ≤ (1+|y|) * (1 + M₃*|((ℓ:ℤ):ℝ) - y|) := by
    have hy : (0:ℝ) ≤ |y| := abs_nonneg y
    have ht : (0:ℝ) ≤ |((ℓ:ℤ):ℝ) - y| := abs_nonneg _
    have h3 : |((ℓ:ℤ):ℝ) - y| ≤ M₃ * |((ℓ:ℤ):ℝ) - y| := by nlinarith
    have h4 : (0:ℝ) ≤ |y| * (M₃ * |((ℓ:ℤ):ℝ) - y|) := by positivity
    nlinarith [h2, h3, h4]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (1:ℝ) * (1 + |((ℓ:ℤ):ℝ)|)^N ≤ ((1+|y|) * (1 + M₃*|((ℓ:ℤ):ℝ) - y|))^N := by
        rw [one_mul]; exact pow_le_pow_left₀ (by positivity) h1 N
    _ = (1+|y|)^N * (1 + M₃*|((ℓ:ℤ):ℝ) - y|)^N := mul_pow _ _ _

/-- Any truncation of the lattice family `ℓ ↦ (1 + M |ℓ-y|)^{-N}` is summable. -/
lemma summable_trunc_lattice {M₃ y : ℝ} (hM₃ : 1 ≤ M₃) {N : ℕ} (hN : 2 ≤ N)
    (c : ℤ → Prop) [DecidablePred c] :
    Summable (fun ℓ : ℤ => if c ℓ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0) := by
  refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_)
    (summable_lattice_inv_pow M₃ y hM₃ hN)
  · split_ifs with h
    · exact le_of_lt (by positivity)
    · exact le_refl 0
  · split_ifs with h
    · exact le_refl _
    · exact le_of_lt (by positivity)

/-- The right half-line lattice sum: `Σ_{ℓ > y + S/M₃} (1 + M₃|ℓ-y|)^{-N} ≤ 2/S^{N-1}`. -/
lemma half_line_le (M₃ S y : ℝ) (hM₃ : 1 ≤ M₃) (hS : 2 ≤ S) (N : ℕ) (hN : 3 ≤ N) :
    (∑' ℓ : ℤ, (if y + S/M₃ < (ℓ:ℝ) then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) ≤ 2/S^(N-1) := by
  have hM₃pos : 0 < M₃ := by linarith
  have hSpos : 0 < S := by linarith
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 1 < N)
  set m : ℤ := ⌈y + S/M₃⌉ with hm
  have hgsum : Summable (fun ℓ : ℤ => (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N) :=
    summable_lattice_inv_pow M₃ y hM₃ hN2
  have hsuml : Summable (fun ℓ : ℤ => (if y + S/M₃ < (ℓ:ℝ) then
      (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) :=
    summable_trunc_lattice hM₃ hN2 _
  have hsumm : Summable (fun ℓ : ℤ => (if m ≤ ℓ then
      (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := summable_trunc_lattice hM₃ hN2 _
  -- (1) the half-line sum is dominated by the half-line `{m ≤ ℓ}`
  have hstep1 : (∑' ℓ : ℤ, (if y + S/M₃ < (ℓ:ℝ) then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
      ≤ (∑' ℓ : ℤ, (if m ≤ ℓ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := by
    refine Summable.tsum_le_tsum (fun ℓ => ?_) hsuml hsumm
    by_cases h : y + S/M₃ < (ℓ:ℝ)
    · have hmℓ : m ≤ ℓ := by rw [hm, Int.ceil_le]; exact le_of_lt h
      rw [if_pos h, if_pos hmℓ]
    · rw [if_neg h]
      split_ifs with h2
      · exact le_of_lt (by positivity)
      · exact le_refl 0
  -- (2) reindex the half-line as a sum over `ℕ`
  have hstep2 : (∑' ℓ : ℤ, (if m ≤ ℓ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
      = ∑' j : ℕ, (1:ℝ)/(1 + M₃*|(((m + j : ℤ)):ℝ) - y|)^N :=
    tsum_int_Ici_eq_tsum_nat (fun r : ℝ => (1:ℝ)/(1 + M₃*|r - y|)^N) m
  -- (3) compare with the reference family `(1 + S + M₃ j)^{-N}`
  have hpt3 : ∀ j : ℕ, (1:ℝ)/(1 + M₃*|(((m + j : ℤ)):ℝ) - y|)^N
      ≤ (1:ℝ)/(1 + S + M₃*(j:ℝ))^N := by
    intro j
    have hmj : S/M₃ + (j:ℝ) ≤ (((m + j : ℤ)):ℝ) - y := by
      have h1 : y + S/M₃ ≤ (m:ℝ) := by rw [hm]; exact Int.le_ceil _
      push_cast
      linarith
    have hpos : 0 < (((m + j : ℤ)):ℝ) - y := by
      have h2 : (0:ℝ) < S/M₃ + (j:ℝ) := by positivity
      linarith
    rw [abs_of_pos hpos]
    have key : S + M₃*(j:ℝ) ≤ M₃ * ((((m + j : ℤ)):ℝ) - y) := by
      have h := mul_le_mul_of_nonneg_left hmj (le_of_lt hM₃pos)
      rwa [mul_add, mul_div_cancel₀ S (ne_of_gt hM₃pos)] at h
    apply one_div_le_one_div_of_le (pow_pos (by nlinarith [hM₃pos, hpos]) N)
    apply pow_le_pow_left₀ (by nlinarith [hSpos, hM₃pos, (Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))])
    linarith [key]
  have hbase : Summable (fun j : ℕ => (1:ℝ)/(1 + (j:ℝ))^N) := by
    have h := Real.summable_nat_pow_inv.mpr (by omega : 1 < N)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => ((n:ℝ)^N)⁻¹) 1).mpr h
    refine h2.congr (fun n => ?_)
    show (((n+1 : ℕ) : ℝ)^N)⁻¹ = (1:ℝ)/(1 + (n:ℝ))^N
    rw [one_div, show ((n+1 : ℕ) : ℝ) = 1 + (n:ℝ) by push_cast; ring]
  have hsum3 : Summable (fun j : ℕ => (1:ℝ)/(1 + S + M₃*(j:ℝ))^N) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hbase
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [hS, hM₃, (Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))]
  have hsum3' : Summable (fun j : ℕ => (1:ℝ)/(1 + M₃*|(((m + j : ℤ)):ℝ) - y|)^N) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hpt3 hsum3
  -- (4) integral test
  have hInt : IntegrableOn (fun t : ℝ => (1:ℝ)/(1+S+M₃*t)^N) (Set.Ioi 0) := by
    by_contra hcon
    have hzero : (∫ t in Set.Ioi (0:ℝ), (1:ℝ)/(1+S+M₃*t)^N) = 0 := integral_undef hcon
    have hval := integral_Ioi_inv_add_pow (M := M₃) (c := 1+S) hM₃pos (by linarith) hN2
    rw [hval] at hzero
    have hpos' : (0:ℝ) < (1/((N:ℝ)-1)) * (1/(M₃ * (1+S)^(N-1))) := by
      have : (0:ℝ) < (N:ℝ) - 1 := by linarith
      positivity
    linarith
  have hanti : AntitoneOn (fun t : ℝ => (1:ℝ)/(1+S+M₃*t)^N) (Set.Ici 0) := by
    intro a ha b hb hab
    have ha' : (0:ℝ) ≤ a := ha
    have ha0 : (0:ℝ) < 1 + S + M₃*a := by nlinarith [ha', hSpos, hM₃pos]
    have hble : 1 + S + M₃*a ≤ 1 + S + M₃*b := by nlinarith [hab, hM₃pos]
    apply one_div_le_one_div_of_le (pow_pos ha0 N)
    exact pow_le_pow_left₀ (le_of_lt ha0) hble N
  have hnonneg : ∀ t ∈ Set.Ioi (0:ℝ), 0 ≤ (1:ℝ)/(1+S+M₃*t)^N := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    exact le_of_lt (one_div_pos.mpr (pow_pos (by nlinarith [hSpos, hM₃pos, ht0]) N))
  have hint := AntitoneOn.tsum_le_integral hanti hInt hnonneg
  have hval2 : (∫ t in Set.Ioi (0:ℝ), (1:ℝ)/(1+S+M₃*t)^N)
      = (1/((N:ℝ)-1)) * (1/(M₃ * (1+S)^(N-1))) :=
    integral_Ioi_inv_add_pow (M := M₃) (c := 1+S) hM₃pos (by linarith) hN2
  -- (5) assemble
  have hfin : (1:ℝ)/(1+S)^N + (1/((N:ℝ)-1)) * (1/(M₃ * (1+S)^(N-1)))
      ≤ 2/S^(N-1) := by
    have h1 : (1:ℝ)/(1+S)^N ≤ 1/S^(N-1) := by
      have hSN : S^(N-1) ≤ (1+S)^N := by
        calc S^(N-1) ≤ S^N := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ S) (by omega : N-1 ≤ N)
          _ ≤ (1+S)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
      exact one_div_le_one_div_of_le (by positivity) hSN
    have h2 : (1/((N:ℝ)-1)) * (1/(M₃ * (1+S)^(N-1))) ≤ 1/S^(N-1) := by
      have heq : (1/((N:ℝ)-1)) * (1/(M₃ * (1+S)^(N-1)))
          = 1/(((N:ℝ)-1) * (M₃ * (1+S)^(N-1))) := by
        rw [one_div, one_div, one_div, ← mul_inv]
      rw [heq]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hN3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      have h2' : (1:ℝ) ≤ (N:ℝ)-1 := by linarith
      have h3' : S^(N-1) ≤ (1+S)^(N-1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      have hp : (0:ℝ) ≤ (1+S)^(N-1) := pow_nonneg (by linarith) _
      have hprod : (1:ℝ) ≤ ((N:ℝ)-1) * M₃ := by
        have := mul_le_mul h2' hM₃ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (N:ℝ)-1)
        simpa using this
      nlinarith [h3', hprod, hp]
    have hsum : (1:ℝ)/S^(N-1) + 1/S^(N-1) = 2/S^(N-1) := by
      rw [show (2:ℝ) = 1+1 by norm_num, add_div]
    linarith [h1, h2, hsum]
  calc (∑' ℓ : ℤ, (if y + S/M₃ < (ℓ:ℝ) then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
      ≤ (∑' ℓ : ℤ, (if m ≤ ℓ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := hstep1
    _ = ∑' j : ℕ, (1:ℝ)/(1 + M₃*|(((m + j : ℤ)):ℝ) - y|)^N := hstep2
    _ ≤ ∑' j : ℕ, (1:ℝ)/(1 + S + M₃*(j:ℝ))^N := Summable.tsum_le_tsum hpt3 hsum3' hsum3
    _ ≤ (1:ℝ)/(1+S+M₃*(0:ℝ))^N + ∫ t in Set.Ioi (0:ℝ), (1:ℝ)/(1+S+M₃*t)^N := hint
    _ = (1:ℝ)/(1+S)^N + (1/((N:ℝ)-1)) * (1/(M₃ * (1+S)^(N-1))) := by
        rw [hval2, mul_zero, add_zero]
    _ ≤ 2/S^(N-1) := hfin

/-- The negation equivalence of `ℤ`. -/
def intNegEquiv : ℤ ≃ ℤ where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x

/-- **Lattice tail estimate**: the `ℓ`-sum of `(1 + M₃|ℓ-y|)^{-N}` restricted to
`|ℓ-y| > S/M₃` is `≤ 4/S^{N-1}`. -/
lemma lattice_tail_sum_le (M₃ S y : ℝ) (hM₃ : 1 ≤ M₃) (hS : 2 ≤ S) (N : ℕ) (hN : 3 ≤ N) :
    (∑' ℓ : ℤ, (if S/M₃ < |(ℓ:ℝ) - y| then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) ≤ 4/S^(N-1) := by
  have hN2 : 2 ≤ N := by omega
  have hM₃pos : 0 < M₃ := by linarith
  have hSpos : 0 < S := by linarith
  have hSP : (0:ℝ) < S/M₃ := div_pos hSpos hM₃pos
  have hmirror : (∑' ℓ : ℤ, (if (ℓ:ℝ) < y - S/M₃ then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
      = (∑' ℓ : ℤ, (if -y + S/M₃ < (ℓ:ℝ) then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - (-y)|)^N else 0)) := by
    rw [← Equiv.tsum_eq intNegEquiv (fun ℓ : ℤ =>
      (if (ℓ:ℝ) < y - S/M₃ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))]
    apply tsum_congr
    intro c
    show (if ((-c : ℤ) : ℝ) < y - S/M₃ then (1:ℝ)/(1 + M₃*|((-c : ℤ) : ℝ) - y|)^N else 0)
        = (if -y + S/M₃ < (c:ℝ) then (1:ℝ)/(1 + M₃*|(c:ℝ) - (-y)|)^N else 0)
    by_cases h : -y + S/M₃ < (c:ℝ)
    · have h' : ((-c : ℤ) : ℝ) < y - S/M₃ := by push_cast; linarith
      rw [if_pos h', if_pos h]
      show (1:ℝ)/(1 + M₃*|(((-c : ℤ)):ℝ) - y|)^N = (1:ℝ)/(1 + M₃*|(c:ℝ) - (-y)|)^N
      rw [show (((-c : ℤ)):ℝ) = -(c:ℝ) by push_cast; ring,
        show -(c:ℝ) - y = -((c:ℝ) + y) by ring,
        show (c:ℝ) - (-y) = (c:ℝ) + y by ring, abs_neg]
    · have h' : ¬ ((((-c : ℤ)) : ℝ) < y - S/M₃) := by push_cast; linarith
      rw [if_neg h', if_neg h]
  have hpoint : ∀ ℓ : ℤ,
      (if S/M₃ < |(ℓ:ℝ) - y| then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)
      ≤ (if y + S/M₃ < (ℓ:ℝ) then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)
        + (if (ℓ:ℝ) < y - S/M₃ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0) := by
    intro ℓ
    by_cases h1 : y + S/M₃ < (ℓ:ℝ)
    · have hc : S/M₃ < |(ℓ:ℝ) - y| := by
        rw [abs_of_pos (by linarith : 0 < (ℓ:ℝ) - y)]; linarith
      have h2 : ¬ ((ℓ:ℝ) < y - S/M₃) := by linarith
      rw [if_pos hc, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : (ℓ:ℝ) < y - S/M₃
      · have hc : S/M₃ < |(ℓ:ℝ) - y| := by
          rw [abs_of_neg (by linarith : (ℓ:ℝ) - y < 0)]; linarith
        rw [if_pos hc, if_neg h1, if_pos h2, zero_add]
      · have habs : |(ℓ:ℝ) - y| ≤ S/M₃ := by
          rw [abs_le]; constructor <;> linarith
        rw [if_neg (not_lt.mpr habs), if_neg h1, if_neg h2, add_zero]
  have hsumR : Summable (fun ℓ : ℤ => (if y + S/M₃ < (ℓ:ℝ) then
      (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := summable_trunc_lattice hM₃ hN2 _
  have hsumL : Summable (fun ℓ : ℤ => (if (ℓ:ℝ) < y - S/M₃ then
      (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := summable_trunc_lattice hM₃ hN2 _
  have hsumF : Summable (fun ℓ : ℤ => (if S/M₃ < |(ℓ:ℝ) - y| then
      (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := summable_trunc_lattice hM₃ hN2 _
  have hsumAdd : Summable (fun ℓ : ℤ =>
      (if y + S/M₃ < (ℓ:ℝ) then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)
      + (if (ℓ:ℝ) < y - S/M₃ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) :=
    hsumR.add hsumL
  have hR : (∑' ℓ : ℤ, (if y + S/M₃ < (ℓ:ℝ) then
      (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) ≤ 2/S^(N-1) :=
    half_line_le M₃ S y hM₃ hS N hN
  have hL : (∑' ℓ : ℤ, (if (ℓ:ℝ) < y - S/M₃ then
      (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) ≤ 2/S^(N-1) := by
    rw [hmirror]
    exact half_line_le M₃ S (-y) hM₃ hS N hN
  calc (∑' ℓ : ℤ, (if S/M₃ < |(ℓ:ℝ) - y| then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
      ≤ ∑' ℓ : ℤ, ((if y + S/M₃ < (ℓ:ℝ) then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)
          + (if (ℓ:ℝ) < y - S/M₃ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) :=
        Summable.tsum_le_tsum hpoint hsumF hsumAdd
    _ = (∑' ℓ : ℤ, (if y + S/M₃ < (ℓ:ℝ) then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
        + (∑' ℓ : ℤ, (if (ℓ:ℝ) < y - S/M₃ then (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) :=
        Summable.tsum_add hsumR hsumL
    _ ≤ 2/S^(N-1) + 2/S^(N-1) := add_le_add hR hL
    _ = 4/S^(N-1) := by rw [show (4:ℝ) = 2+2 by norm_num, add_div]

/-- **Pointwise bound on the tail weight**: `‖Wtail K M₃ B y‖ ≤ C M₃/B^{N-1}` uniformly in `y`,
for `M₃ ≥ 1` and `B ≥ 2`. -/
lemma Wtail_norm_le {K : ℝ} (hK : 0 < K) (N : ℕ) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₃ B y : ℝ), 1 ≤ M₃ → 2 ≤ B →
      ‖Wtail K M₃ B y‖ ≤ C * (M₃ / B ^ (N - 1)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := psi1hat_decay K hK N
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro M₃ B y hM₃ hB
  have hM₃pos : 0 < M₃ := by linarith
  have hBpos : 0 < B := by linarith
  have hN2 : 2 ≤ N := by omega
  set S : ℝ := max 2 B with hS
  have hS2 : 2 ≤ S := le_max_left _ _
  have hSB : B ≤ S := le_max_right _ _
  have hspos : 0 < S := by linarith
  have hlat := lattice_tail_sum_le M₃ S y hM₃ hS2 N hN
  -- the two conditions agree with `S/M₃ < |ℓ - y|`
  have hcond : ∀ ℓ : ℤ, (B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y|)
      ↔ S/M₃ < |(ℓ:ℝ) - y| := by
    intro ℓ
    rw [hS]
    constructor
    · intro h
      rw [div_lt_iff₀ hM₃pos]
      have h1 : (2:ℝ) < |(ℓ:ℝ) - y| * M₃ := by rw [← div_lt_iff₀ hM₃pos]; exact h.2
      have h2 : B < |(ℓ:ℝ) - y| * M₃ := by rw [← div_lt_iff₀ hM₃pos]; exact h.1
      exact max_lt h1 h2
    · intro h
      exact ⟨lt_of_le_of_lt (div_le_div_of_nonneg_right (le_max_right (2:ℝ) B)
          (le_of_lt hM₃pos)) h,
        lt_of_le_of_lt (div_le_div_of_nonneg_right (le_max_left (2:ℝ) B)
          (le_of_lt hM₃pos)) h⟩
  have hmaj : ∀ ℓ : ℤ, ‖(if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
      psi1hat K (M₃*((ℓ:ℝ) - y)) else 0)‖
      ≤ (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
        C₀/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0) := by
    intro ℓ
    split_ifs with h
    · have h1 : |M₃*((ℓ:ℝ) - y)| = M₃*|(ℓ:ℝ) - y| := by
        rw [abs_mul, abs_of_pos hM₃pos]
      calc ‖psi1hat K (M₃*((ℓ:ℝ) - y))‖ ≤ C₀/(1 + |M₃*((ℓ:ℝ) - y)|)^N := hC₀ _
        _ = C₀/(1 + M₃*|(ℓ:ℝ) - y|)^N := by rw [h1]
    · simp
  have hsumG : Summable (fun ℓ : ℤ => (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
      C₀/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_)
      ((summable_lattice_inv_pow M₃ y hM₃ hN2).mul_left C₀)
    · split_ifs with h
      · positivity
      · exact le_refl 0
    · split_ifs with h
      · rw [mul_one_div]
      · exact mul_nonneg (le_of_lt hC₀pos) (by positivity)
  have hsumNorm : Summable (fun ℓ : ℤ => ‖(if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y|
      then psi1hat K (M₃*((ℓ:ℝ) - y)) else 0)‖) :=
    Summable.of_norm_bounded hsumG (fun ℓ => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hmaj ℓ)
  have h2 : ‖∑' ℓ : ℤ, (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
        psi1hat K (M₃*((ℓ:ℝ) - y)) else 0)‖
      ≤ ∑' ℓ : ℤ, (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
        C₀/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0) :=
    (norm_tsum_le_tsum_norm hsumNorm).trans
      (Summable.tsum_le_tsum hmaj hsumNorm hsumG)
  have h3 : (∑' ℓ : ℤ, (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
        C₀/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
      = C₀ * (∑' ℓ : ℤ, (if S/M₃ < |(ℓ:ℝ) - y| then
        (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) := by
    have : (fun ℓ : ℤ => (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
        C₀/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))
        = fun ℓ : ℤ => C₀ * (if S/M₃ < |(ℓ:ℝ) - y| then
            (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0) := by
      funext ℓ
      by_cases h : B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y|
      · rw [if_pos h, if_pos ((hcond ℓ).mp h)]; ring
      · rw [if_neg h, if_neg (fun hh => h ((hcond ℓ).mpr hh))]; ring
    rw [this, tsum_mul_left]
  have hnorm : ‖((M₃ : ℝ) : ℂ)‖ = M₃ := by
    simpa [abs_of_pos hM₃pos] using RCLike.norm_ofReal M₃
  rw [Wtail, norm_mul, hnorm]
  calc M₃ * ‖∑' ℓ : ℤ, (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
        psi1hat K (M₃*((ℓ:ℝ) - y)) else 0)‖
      ≤ M₃ * (∑' ℓ : ℤ, (if B/M₃ < |(ℓ:ℝ) - y| ∧ 2/M₃ < |(ℓ:ℝ) - y| then
          C₀/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0)) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hM₃pos)
    _ = M₃ * (C₀ * (∑' ℓ : ℤ, (if S/M₃ < |(ℓ:ℝ) - y| then
          (1:ℝ)/(1 + M₃*|(ℓ:ℝ) - y|)^N else 0))) := by rw [h3]
    _ ≤ M₃ * (C₀ * (4/S^(N-1))) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hM₃pos)
        exact mul_le_mul_of_nonneg_left hlat (le_of_lt hC₀pos)
    _ ≤ (4 * C₀) * (M₃ / B ^ (N - 1)) := by
        have hBpow : (0:ℝ) < B^(N-1) := by positivity
        have hone : (1:ℝ)/S^(N-1) ≤ 1/B^(N-1) :=
          one_div_le_one_div_of_le hBpow (pow_le_pow_left₀ (le_of_lt hBpos) hSB (N-1))
        have hM1 : M₃ * (1/S^(N-1)) ≤ M₃ * (1/B^(N-1)) :=
          mul_le_mul_of_nonneg_left hone (le_of_lt hM₃pos)
        calc M₃ * (C₀ * (4/S^(N-1))) = (4*C₀) * (M₃ * (1/S^(N-1))) := by ring
          _ ≤ (4*C₀) * (M₃ * (1/B^(N-1))) :=
              mul_le_mul_of_nonneg_left hM1 (by positivity)
          _ = (4 * C₀) * (M₃ / B ^ (N - 1)) := by ring

/-! ## Plancherel for the `m₂`-sum -/

/-- `Bsum f M₂` is the Fourier transform of the `m₂`-profile `Hsum M₂ f` (no support hypothesis
on `f`, only continuity and compact support). -/
lemma Bsum_eq_Fhat_Hsum {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    {M₂ : ℝ} (hM₂ : 0 < M₂) (x : ℝ) :
    Bsum f M₂ x = Fhat (fun u : ℝ => Hsum M₂ f u) x := by
  have hL : Bsum f M₂ x
      = ∑ m₂ ∈ R2 M₂, ((m₂:ℝ):ℂ) * ∫ v : ℝ, (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x))) := by
    rw [Bsum]
    exact Finset.sum_congr rfl (fun m₂ _ => by rw [Fhat_eq_integral'])
  have hR : Fhat (fun u : ℝ => Hsum M₂ f u) x
      = ∫ u : ℝ, ((∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) : ℝ) : ℂ) * efun (-(u * x)) := by
    rw [show (fun u : ℝ => Hsum M₂ f u)
        = fun u : ℝ => ∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) from rfl]
    rw [Fhat_eq_integral']
  rw [hL, hR]
  have hsub : ∀ m₂ ∈ R2 M₂, (∫ u : ℝ, (f (u / (m₂:ℝ)) : ℂ) * efun (-(u * x)))
      = (m₂:ℝ) * ∫ v : ℝ, (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x))) := by
    intro m₂ hm₂
    have hm₂pos : (0:ℝ) < (m₂:ℝ) := R2_pos' hm₂
    have hpt : (fun u : ℝ => (f (u / (m₂:ℝ)) : ℂ) * efun (-(u * x)))
        = fun u : ℝ => ((fun v : ℝ => (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x))))
            (u / (m₂:ℝ))) := by
      funext u
      simp only
      have e2 : -((u / (m₂:ℝ)) * ((m₂:ℝ) * x)) = -(u * x) := by field_simp; try ring
      rw [e2]
    rw [hpt]
    rw [MeasureTheory.Measure.integral_comp_div (a := (m₂:ℝ))
      (g := fun v : ℝ => (f v : ℂ) * efun (-(v * ((m₂:ℝ) * x))))]
    rw [abs_of_pos hm₂pos, Complex.real_smul]
  have hfun : (fun u : ℝ => ((∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) : ℝ) : ℂ) * efun (-(u * x)))
      = fun u : ℝ => ∑ m₂ ∈ R2 M₂, ((f (u / (m₂:ℝ)) : ℝ) : ℂ) * efun (-(u * x)) := by
    funext u
    rw [show ((∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) : ℝ) : ℂ)
        = ∑ m₂ ∈ R2 M₂, ((f (u / (m₂:ℝ)) : ℝ) : ℂ) from by push_cast; rfl]
    rw [Finset.sum_mul]
  rw [hfun]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
    exact (hsub m₂ hm₂).symm
  · intro m₂ hm₂
    have hm₂pos : (0:ℝ) < (m₂:ℝ) := R2_pos' hm₂
    have hcs₂ : HasCompactSupport (fun u : ℝ => (f (u / (m₂:ℝ)) : ℂ)) :=
      (hcs.comp_homeomorph
        (Homeomorph.mulRight₀ ((m₂:ℝ))⁻¹ (inv_ne_zero (ne_of_gt hm₂pos)))).comp_left
        (g := fun z : ℝ => (z:ℂ)) (by simp)
    have hcont : Continuous (fun u : ℝ => (f (u / (m₂:ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.comp (hf.comp (continuous_id.div_const _))
    exact (hcont.mul (contDiff_efun.comp (by fun_prop : Continuous fun u : ℝ => -(u * x))))
      |>.integrable_of_hasCompactSupport (hcs₂.mul_right (f' := fun u : ℝ => efun (-(u * x))))

/-- **Plancherel for the `m₂`-profile**: `∫ ‖Bsum f M₂ (ξ/m)‖² dξ = |m| ∫ (Hsum M₂ f)²`. -/
lemma bsum_hsum_plancherel (f : ℝ → ℝ) (M₂ : ℝ) (hM₂ : 0 < M₂)
    (hf : Continuous f) (hcs : HasCompactSupport f) {m : ℤ} (hm : m ≠ 0) :
    Integrable (fun ξ : ℝ => ‖Bsum f M₂ (ξ / (m : ℝ))‖ ^ 2) ∧
      (∫ ξ, ‖Bsum f M₂ (ξ / (m : ℝ))‖ ^ 2) = |(m : ℝ)| * ∫ u, (Hsum M₂ f u) ^ 2 := by
  have hHcont : Continuous (fun u : ℝ => Hsum M₂ f u) := by
    rw [show (fun u : ℝ => Hsum M₂ f u)
        = fun u : ℝ => ∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) from rfl]
    exact continuous_finsetSum _ (fun m₂ _ => hf.comp (continuous_id.div_const _))
  have hHfun : (fun u : ℝ => Hsum M₂ f u)
      = fun u : ℝ => ∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) := rfl
  have hHcs' : HasCompactSupport (fun u : ℝ => ∑ m₂ ∈ R2 M₂, f (u / (m₂:ℝ))) := by
    rw [hasCompactSupport_def]
    have hK : IsCompact
        (⋃ m₂ ∈ (R2 M₂ : Set ℤ), (fun v : ℝ => v * (m₂:ℝ)) '' tsupport f) :=
      (R2 M₂).finite_toSet.isCompact_biUnion
        (fun m₂ _ => hcs.image (by fun_prop : Continuous fun v : ℝ => v * (m₂:ℝ)))
    refine IsCompact.of_isClosed_subset hK isClosed_closure (closure_minimal ?_ hK.isClosed)
    intro u hu
    rw [Function.mem_support] at hu
    have hex : ∃ m₂ ∈ R2 M₂, f (u / (m₂:ℝ)) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (Finset.sum_eq_zero (fun m₂ hm₂ => hc m₂ hm₂))
    obtain ⟨m₂, hm₂, hne⟩ := hex
    have hm₂pos : (0:ℝ) < (m₂:ℝ) := R2_pos' hm₂
    refine Set.mem_iUnion.mpr ⟨m₂, Set.mem_iUnion.mpr ⟨hm₂, ?_⟩⟩
    refine ⟨u / (m₂:ℝ), subset_tsupport f (Function.mem_support.mpr hne), ?_⟩
    field_simp
  have hHcs : HasCompactSupport (fun u : ℝ => Hsum M₂ f u) := by
    rw [hHfun]; exact hHcs'
  have hcm : Continuous (fun u : ℝ => ((Hsum M₂ f u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hHcont
  have hcsc : HasCompactSupport (fun u : ℝ => ((Hsum M₂ f u : ℝ) : ℂ)) :=
    hHcs.comp_left (g := fun z : ℝ => (z:ℂ)) (by simp)
  -- the Plancherel identity for the profile
  have hmain : (∫ ξ, ‖Bsum f M₂ ξ‖ ^ 2) = ∫ u, (Hsum M₂ f u) ^ 2 := by
    have h1 : (∫ ξ, ‖Bsum f M₂ ξ‖ ^ 2)
        = ∫ ξ, ‖Fhat (fun u : ℝ => Hsum M₂ f u) ξ‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
      show ‖Bsum f M₂ ξ‖ ^ 2 = ‖Fhat (fun u : ℝ => Hsum M₂ f u) ξ‖ ^ 2
      rw [Bsum_eq_Fhat_Hsum hf hcs hM₂ ξ]
    have hF : (fun ξ : ℝ => ‖Fhat (fun u : ℝ => Hsum M₂ f u) ξ‖ ^ 2)
        = fun ξ : ℝ =>
            ‖FourierTransform.fourier (fun u : ℝ => ((Hsum M₂ f u : ℝ) : ℂ)) ξ‖ ^ 2 := rfl
    have h2 : (∫ ξ, ‖Fhat (fun u : ℝ => Hsum M₂ f u) ξ‖ ^ 2)
        = ∫ u, ‖((Hsum M₂ f u : ℝ) : ℂ)‖ ^ 2 := by
      rw [hF, ← plancherel_continuous (fun u : ℝ => ((Hsum M₂ f u : ℝ) : ℂ)) hcm hcsc]
    have h3 : (∫ u, ‖((Hsum M₂ f u : ℝ) : ℂ)‖ ^ 2) = ∫ u, (Hsum M₂ f u) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      show ‖((Hsum M₂ f u : ℝ) : ℂ)‖ ^ 2 = (Hsum M₂ f u) ^ 2
      rw [show ‖((Hsum M₂ f u : ℝ) : ℂ)‖ = |Hsum M₂ f u| from RCLike.norm_ofReal _, sq_abs]
    rw [h1, h2, h3]
  -- integrability
  have hint : Integrable (fun ξ : ℝ => ‖Bsum f M₂ ξ‖ ^ 2) := by
    have h := integrable_fourier_sq_of_continuous_hasCompactSupport hcm hcsc
    refine h.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    show ‖FourierTransform.fourier (fun u : ℝ => ((Hsum M₂ f u : ℝ) : ℂ)) ξ‖ ^ 2 = ‖Bsum f M₂ ξ‖ ^ 2
    rw [Bsum_eq_Fhat_Hsum hf hcs hM₂ ξ]
    simp only [Fhat]
  have hcm' : ((m : ℝ)) ≠ 0 := by exact_mod_cast hm
  have h2 : (∫ ξ, ‖Bsum f M₂ (ξ / (m : ℝ))‖ ^ 2)
      = |(m : ℝ)| * (∫ ξ, ‖Bsum f M₂ ξ‖ ^ 2) := by
    rw [MeasureTheory.Measure.integral_comp_div
      (g := fun ξ : ℝ => ‖Bsum f M₂ ξ‖ ^ 2) (a := ((m : ℝ))), smul_eq_mul]
  exact ⟨hint.comp_div hcm', by rw [h2, hmain]⟩

/-- The region II tail bound: the part of `ĝ` coming from the tail `|M₃(ℓ-ξ/m₁)| > B` of the
resonance weight is bounded by `M₁M₃²/B^{2(N-1)} ∫ (Hsum)²`. -/
theorem tail_part_bound {K : ℝ} (hK : 0 < K) (N : ℕ) (hN : 3 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T η B : ℝ) (M₁ M₂ M₃ : ℝ),
      1 ≤ T → 0 < η → 2 ≤ B → 0 < M₁ → 0 < M₂ → 1 ≤ M₃ →
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → (∀ u, 0 ≤ f u) →
      (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6)) \ (Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)),
        ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) ≤
        C * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hWtaille⟩ := Wtail_norm_le hK N hN
  refine ⟨48 * C₀ ^ 2 + 1, by positivity, ?_⟩
  intro T η B M₁ M₂ M₃ hT hη hB hM₁ hM₂ hM₃ f hf hcs hfnn
  have hBpos : 0 < B := by linarith
  have hM₃pos : 0 < M₃ := by linarith
  set Wb : ℝ := C₀ * (M₃ / B^(N-1)) with hWbdef
  have hWbnonneg : 0 ≤ Wb := by rw [hWbdef]; positivity
  have hWbnd : ∀ y : ℝ, ‖Wtail K M₃ B y‖ ≤ Wb := fun y => by
    rw [hWbdef]; exact hWtaille M₃ B y hM₃ hB
  set I : ℝ := ∫ s, (Hsum M₂ f s) ^ 2 with hIdef
  have hInonneg : 0 ≤ I := by
    rw [hIdef]; exact integral_nonneg (fun s => sq_nonneg _)
  set Wfun : ℝ → ℝ := fun ξ =>
    ∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))^2 * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2 with hWfundef
  have hWfun_nonneg : ∀ ξ, 0 ≤ Wfun ξ := fun ξ => by
    rw [hWfundef]; exact Finset.sum_nonneg (fun m₁ _ => by positivity)
  have hzene : ∀ m₁ ∈ R1 M₁, m₁ ≠ 0 := by
    intro m₁ hm₁ h0
    have h1 : M₁ < |((m₁:ℝ))| := (Finset.mem_filter.mp hm₁).2
    rw [h0] at h1; simp only [Int.cast_zero, abs_zero] at h1; linarith
  have habsne : ∀ m₁ ∈ R1 M₁, (|((m₁:ℝ))|) ≠ 0 := by
    intro m₁ hm₁
    have h1 : M₁ < |((m₁:ℝ))| := (Finset.mem_filter.mp hm₁).2
    exact ne_of_gt (lt_trans hM₁ h1)
  -- integrability of the individual terms
  have hInt_each : ∀ m₁ ∈ R1 M₁,
      Integrable (fun ξ : ℝ => (1/(|(m₁:ℝ)|))^2 * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2) := by
    intro m₁ hm₁
    exact ((bsum_hsum_plancherel f M₂ hM₂ hf hcs (hzene m₁ hm₁)).1).const_mul _
  have hWfun_int : Integrable Wfun := by
    rw [hWfundef]
    exact integrable_finsetSum _ (fun m₁ hm₁ => hInt_each m₁ hm₁)
  -- the value of `∫ Wfun`
  have hWfun_val : (∫ ξ, Wfun ξ) = (∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) * I := by
    rw [hWfundef, hIdef]
    rw [MeasureTheory.integral_finsetSum _ (fun m₁ hm₁ => hInt_each m₁ hm₁)]
    have hterm : ∀ m₁ ∈ R1 M₁, (∫ ξ : ℝ, (1/(|(m₁:ℝ)|))^2 * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖^2)
        = (1/(|(m₁:ℝ)|)) * ∫ s, (Hsum M₂ f s)^2 := by
      intro m₁ hm₁
      rw [MeasureTheory.integral_const_mul,
        (bsum_hsum_plancherel f M₂ hM₂ hf hcs (hzene m₁ hm₁)).2]
      have hne := habsne m₁ hm₁
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_mul]
  -- the cardinality bound
  have hempty : M₁ < 1/2 → (R1 M₁).card = 0 := by
    intro h
    have hfl : ⌊(2:ℝ)*M₁⌋ = 0 := by rw [Int.floor_eq_zero_iff]; constructor <;> linarith
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro m hm
    rw [R1, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨h1,h2⟩, h3⟩ := hm
    rw [hfl] at h1 h2
    simp only [neg_zero] at h1 h2
    have hm0 : m = 0 := by omega
    rw [hm0] at h3
    simp only [Int.cast_zero, abs_zero] at h3
    linarith
  have hcard : ((R1 M₁).card : ℝ) ≤ 6 * M₁ := by
    by_cases hhalf : M₁ < 1/2
    · rw [hempty hhalf]; simp; linarith
    · push Not at hhalf
      have h4 := card_R1_le M₁ hM₁
      linarith
  -- the pointwise bound
  have hpt : ∀ ξ : ℝ, ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2 ≤ Wb^2 * ((R1 M₁).card : ℝ) * Wfun ξ := by
    intro ξ
    have h1 : ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ B (ξ / (m₁ : ℝ))‖
        ≤ Wb * ∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|)) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖ := by
      calc ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wtail K M₃ B (ξ / (m₁ : ℝ))‖
          ≤ ∑ m₁ ∈ R1 M₁, ‖((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
              Wtail K M₃ B (ξ / (m₁ : ℝ))‖ := norm_sum_le _ _
        _ ≤ ∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|)) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖ * Wb := by
            apply Finset.sum_le_sum
            intro m₁ _
            have hz : ‖(((|(m₁:ℝ)|:ℝ):ℂ))⁻¹‖ = 1/(|(m₁:ℝ)|) := by
              rw [norm_inv,
                show ‖(((|(m₁:ℝ)|:ℝ):ℂ))‖ = |(|(m₁:ℝ)|)| from RCLike.norm_ofReal _,
                abs_of_nonneg (abs_nonneg _), one_div]
            rw [norm_mul, norm_mul, hz]
            exact mul_le_mul_of_nonneg_left (hWbnd (ξ/(m₁:ℝ))) (by positivity)
        _ = Wb * ∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|)) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m₁ _
            ring
    have hsq : (∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|)) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖)^2
        ≤ ((R1 M₁).card : ℝ) * Wfun ξ := by
      have h := sq_sum_le_card_mul_sum_sq (s := R1 M₁)
        (f := fun m₁ : ℤ => (1/(|(m₁:ℝ)|)) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖)
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hWfundef]
      apply Finset.sum_le_sum
      intro m₁ hm₁
      rw [mul_pow]
    calc ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2
        ≤ (Wb * ∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|)) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖)^2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = Wb^2 * (∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|)) * ‖Bsum f M₂ (ξ/(m₁:ℝ))‖)^2 := by ring
      _ ≤ Wb^2 * (((R1 M₁).card : ℝ) * Wfun ξ) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Wb^2 * ((R1 M₁).card : ℝ) * Wfun ξ := by ring
  -- the final arithmetic
  have hsum8 : (∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) ≤ 8 := sum_inv_abs_R1_le M₁ hM₁
  have hWb2 : Wb^2 = C₀^2 * (M₃^2 / B^(2*(N-1))) := by
    rw [hWbdef]
    have h1 : (M₃ / B^(N-1))^2 = M₃^2 / B^(2*(N-1)) := by
      rw [div_pow, ← pow_mul, mul_comm]
    rw [mul_pow, h1]
  have hmain : Wb^2 * ((R1 M₁).card : ℝ) * ((∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) * I)
      ≤ (48 * C₀ ^ 2 + 1) * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * I := by
    set Aq : ℝ := M₃^2 / B^(2*(N-1)) with hAq
    have hA0 : (0:ℝ) ≤ Aq := by rw [hAq]; positivity
    have hSig0 : (0:ℝ) ≤ (∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hReq : (48 * C₀ ^ 2 + 1) * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * I
        = (48 * C₀ ^ 2 + 1) * (M₁ * Aq) * I := by rw [hAq]; ring
    rw [hWb2, hReq]
    have hkey : C₀^2 * Aq * ((R1 M₁).card : ℝ) * ((∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) * I)
        ≤ 48*C₀^2 * (M₁ * Aq) * I := by
      have step1 : C₀^2 * Aq * ((R1 M₁).card : ℝ) ≤ C₀^2 * Aq * (6*M₁) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      have step2 : (∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) * I ≤ 8 * I :=
        mul_le_mul_of_nonneg_right hsum8 hInonneg
      calc C₀^2 * Aq * ((R1 M₁).card : ℝ) * ((∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) * I)
          ≤ C₀^2 * Aq * (6*M₁) * (8*I) := by
            refine mul_le_mul step1 step2 ?_ ?_
            · exact mul_nonneg hSig0 hInonneg
            · exact mul_nonneg (mul_nonneg (by positivity) hA0) (by positivity)
        _ = 48*C₀^2 * (M₁ * Aq) * I := by ring
    have hfin2 : 48*C₀^2 * (M₁ * Aq) * I ≤ (48 * C₀ ^ 2 + 1) * (M₁ * Aq) * I := by
      have h0 : (0:ℝ) ≤ (M₁ * Aq) * I := mul_nonneg (mul_nonneg (le_of_lt hM₁) hA0) hInonneg
      nlinarith [h0]
    linarith [hkey, hfin2]
  -- the assembly
  set Breg : Set ℝ := (Set.Icc (-(T ^ 6)) (T ^ 6)) \
    (Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) with hBregdef
  have hII : (0:ℝ) ≤ ∫ s, (Hsum M₂ f s) ^ 2 := by rw [← hIdef]; exact hInonneg
  have hfinfinal : (0:ℝ) ≤ (48 * C₀ ^ 2 + 1) * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) *
      ∫ s, (Hsum M₂ f s) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) hII
  by_cases hfin : IntegrableOn (fun ξ : ℝ => ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
      Bsum f M₂ (ξ / (m₁ : ℝ)) * Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) Breg
  · calc (∫ ξ in Breg, ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
          Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2)
        ≤ ∫ ξ in Breg, Wb^2 * ((R1 M₁).card : ℝ) * Wfun ξ := by
          refine setIntegral_mono_ae_restrict hfin (hWfun_int.integrableOn.const_mul _) ?_
          filter_upwards with ξ
          exact hpt ξ
      _ = Wb^2 * ((R1 M₁).card : ℝ) * (∫ ξ in Breg, Wfun ξ) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ Wb^2 * ((R1 M₁).card : ℝ) * (∫ ξ, Wfun ξ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine setIntegral_le_integral hWfun_int ?_
          filter_upwards with ξ
          exact hWfun_nonneg ξ
      _ = Wb^2 * ((R1 M₁).card : ℝ) * ((∑ m₁ ∈ R1 M₁, (1/(|(m₁:ℝ)|))) * I) := by
          rw [hWfun_val]
      _ ≤ (48 * C₀ ^ 2 + 1) * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * I := hmain
      _ = (48 * C₀ ^ 2 + 1) * (M₁ * M₃ ^ 2 / B ^ (2 * (N - 1))) * ∫ s, (Hsum M₂ f s) ^ 2 := by
          rw [hIdef]
  · have hzero : (∫ ξ in Breg, ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wtail K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) = 0 := integral_undef hfin
    rw [hzero]
    exact hfinfinal

end

end Work.GM.Affine
