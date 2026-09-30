import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.bpOddDefs
import Submission.Work.BW.bpOdd_bfac_lower
import Submission.Work.BW.bpOdd_den_prod_le
import Submission.Work.BW.bpOdd_dist_reindex
import Submission.Work.BW.bpOdd_dist_arith
import Submission.Work.BW.bpOdd_num25
import Submission.Work.BW.bpOdd_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

lemma two_le_abs_sub_odd {k l : ℤ} (hk : Odd k) (hl : Odd l) (hne : k ≠ l) :
    (2:ℝ) ≤ |(k:ℝ) - (l:ℝ)| := by
  obtain ⟨a, ha⟩ := hk
  obtain ⟨b, hb⟩ := hl
  have hab : a ≠ b := by rintro rfl; exact hne (by rw [ha, hb])
  have h1 : k - l = 2 * (a - b) := by omega
  have h2 : (2:ℤ) ≤ |k - l| := by
    rw [h1, abs_mul]
    have h3 : (1:ℤ) ≤ |a - b| := Int.one_le_abs (sub_ne_zero.mpr hab)
    have h4 : |(2:ℤ)| = 2 := by norm_num
    rw [h4]
    linarith
  have h5 : ((|k - l| : ℤ) : ℝ) = |(k:ℝ) - (l:ℝ)| := by
    rw [Int.cast_abs]
    push_cast
    ring
  calc (2:ℝ) = ((2:ℤ):ℝ) := by norm_num
    _ ≤ ((|k - l| : ℤ) : ℝ) := by exact_mod_cast h2
    _ = |(k:ℝ) - (l:ℝ)| := h5

lemma bpU_le_norm {η : ℝ} (hη' : η < 1/2) {l k : ℤ} (hko : Odd k) (hlo : Odd l) {z : ℂ}
    (hz : ‖z - (l:ℂ)‖ = η) : bpU η l k ≤ ‖z - (k:ℂ)‖ := by
  have hcast : ‖(k:ℂ) - (l:ℂ)‖ = |(k:ℝ) - (l:ℝ)| := by
    have h1 : (k:ℂ) - (l:ℂ) = ((k - l : ℤ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_intCast]
    congr 1
    push_cast
    ring
  have hdist : |(k:ℝ) - (l:ℝ)| - η ≤ ‖z - (k:ℂ)‖ := by
    have h1 : |(k:ℝ) - (l:ℝ)| - η ≤ ‖(k:ℂ) - z‖ := by
      have h2 := norm_sub_norm_le ((k:ℂ) - (l:ℂ)) (z - (l:ℂ))
      have h3 : ((k:ℂ) - (l:ℂ)) - (z - (l:ℂ)) = (k:ℂ) - z := by ring
      rw [h3, hcast, hz] at h2
      exact h2
    rwa [norm_sub_rev] at h1
  unfold bpU
  refine max_le ?_ hdist
  rcases eq_or_ne k l with rfl | hne
  · exact le_of_eq hz.symm
  · have h2 := two_le_abs_sub_odd hko hlo hne
    linarith

lemma bpU_eq_of_ne {η : ℝ} (hη' : η < 1/2) {l k : ℤ} (hk : Odd k) (hl : Odd l) (hne : k ≠ l) :
    bpU η l k = |(k:ℝ) - (l:ℝ)| - η := by
  unfold bpU
  rw [max_eq_right]
  linarith [two_le_abs_sub_odd hk hl hne]

lemma prod_bpU {η : ℝ} (hη : 0 < η) (hη' : η < 1/2) {X : ℕ} {l : ℤ} (hlo : Odd l)
    (hlmem : l ∈ oddIdx X) :
    ∏ k ∈ oddIdx X, bpU η l k = η * ∏ k ∈ (oddIdx X).erase l, (|(k:ℝ) - (l:ℝ)| - η) := by
  have h1 : (∏ k ∈ (oddIdx X).erase l, bpU η l k) * bpU η l l = ∏ k ∈ oddIdx X, bpU η l k :=
    Finset.prod_erase_mul (oddIdx X) (fun k => bpU η l k) hlmem
  rw [← h1]
  have h2 : bpU η l l = η := by
    unfold bpU
    rw [sub_self, abs_zero, zero_sub, max_eq_left (by linarith)]
  have h3 : ∏ k ∈ (oddIdx X).erase l, bpU η l k
      = ∏ k ∈ (oddIdx X).erase l, (|(k:ℝ) - (l:ℝ)| - η) := by
    refine Finset.prod_congr rfl (fun k hk => ?_)
    exact bpU_eq_of_ne hη' (mem_oddIdx.mp (Finset.mem_of_mem_erase hk)).1 hlo
      (fun h => by rw [h] at hk; simp at hk)
  rw [h2, h3]
  ring

lemma bpDen_lt {R η : ℝ} (hη : 0 < η) {X : ℕ} (hX : 2 ≤ X) (hXR : (X:ℝ) + η ≤ R)
    {l k : ℤ} (hl : |l| ≤ (X:ℤ)) (hk : k ∈ oddIdx X) :
    |(k:ℝ)| * (|(l:ℝ)| + η) < R^2 := by
  have hkI := mem_oddIdx_iff.mp hk
  have hkab : |(k:ℝ)| ≤ (X:ℝ) := by
    have h1 : |k| ≤ (X:ℤ) := abs_le.mpr ⟨hkI.2.1, hkI.2.2⟩
    exact_mod_cast h1
  have hlab : |(l:ℝ)| ≤ (X:ℝ) := by exact_mod_cast hl
  have h2 : |(k:ℝ)| * (|(l:ℝ)| + η) ≤ (X:ℝ) * ((X:ℝ) + η) :=
    mul_le_mul hkab (by linarith) (by positivity) (by positivity)
  have h3 : (X:ℝ) * ((X:ℝ) + η) < ((X:ℝ) + η)^2 := by
    nlinarith [hη, (Nat.cast_nonneg X : (0:ℝ) ≤ (X:ℝ))]
  have h4 : ((X:ℝ) + η)^2 ≤ R^2 := by
    have h5 : (0:ℝ) ≤ (X:ℝ) + η := by linarith
    nlinarith [mul_self_le_mul_self h5 hXR]
  linarith

theorem bprodOdd_lower {R η : ℝ} (hη : 0 < η) (hη' : η < 1/2) {X : ℕ} (hX : 2 ≤ X)
    (hXe : Even X) (hXR : (X:ℝ) + η ≤ R) {l : ℤ} (hlo : Odd l) (hl : |l| ≤ (X:ℤ))
    {z : ℂ} (hz : ‖z - (l:ℂ)‖ = η) :
    R^X * η * (∏ k ∈ (oddIdx X).erase l, (|(k:ℝ) - (l:ℝ)| - η)) / (∏ k ∈ oddIdx X, bpD R η l k)
      ≤ ‖bprodOdd R X z‖ := by
  have hR : 0 < R := by
    have h1 : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
    linarith
  have hlmem : l ∈ oddIdx X := by
    rw [mem_oddIdx_iff]
    exact ⟨hlo, (abs_le.mp hl).1, (abs_le.mp hl).2⟩
  have hfac : ∀ k ∈ oddIdx X, R * bpU η l k / bpD R η l k ≤ ‖bfac R k z‖ := by
    intro k hk
    have hko : Odd k := (mem_oddIdx.mp hk).1
    exact bpOdd_bfac_lower (le_of_lt hη) hR hz (le_trans (le_of_lt hη) (le_max_left _ _))
      (bpU_le_norm hη' hko hlo hz) (bpDen_lt hη hX hXR hl hk)
  have hfac0 : ∀ k ∈ oddIdx X, 0 ≤ R * bpU η l k / bpD R η l k := by
    intro k hk
    exact div_nonneg (mul_nonneg (le_of_lt hR) (le_trans (le_of_lt hη) (le_max_left _ _)))
      (le_of_lt (bpD_pos (le_of_lt hη) (bpDen_lt hη hX hXR hl hk)))
  have hstep : ∏ k ∈ oddIdx X, (R * bpU η l k / bpD R η l k) ≤ ∏ k ∈ oddIdx X, ‖bfac R k z‖ :=
    Finset.prod_le_prod₀ hfac0 hfac
  have hstep' : R^X * (∏ k ∈ oddIdx X, bpU η l k) / (∏ k ∈ oddIdx X, bpD R η l k)
      ≤ ∏ k ∈ oddIdx X, ‖bfac R k z‖ := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
      bpOdd_card hXe] at hstep
    exact hstep
  have hU : ∏ k ∈ oddIdx X, bpU η l k = η * ∏ k ∈ (oddIdx X).erase l, (|(k:ℝ) - (l:ℝ)| - η) :=
    prod_bpU hη hη' hlo hlmem
  calc R^X * η * (∏ k ∈ (oddIdx X).erase l, (|(k:ℝ) - (l:ℝ)| - η)) / (∏ k ∈ oddIdx X, bpD R η l k)
      = R^X * (∏ k ∈ oddIdx X, bpU η l k) / (∏ k ∈ oddIdx X, bpD R η l k) := by rw [hU]; ring
    _ ≤ ∏ k ∈ oddIdx X, ‖bfac R k z‖ := hstep'
    _ = ‖bprodOdd R X z‖ := by rw [bprodOdd_eq_prod, norm_prod]

/-- BW (25) lower half. Route (verified numerically, worst margin `e²/(2π) ≈ 1.176` at `X=2`, `R→∞`):
write `X = 2m` (`m ≥ 1`), `ω := {k odd : |k| ≤ X}`. Each factor satisfies
`‖bfac R k z‖ = R‖z−k‖/‖R²−kz‖ ≥ R(|k−l|−η)/(|R²−kl|+|k|η)` (for `k ≠ l`; for `k = l` the numerator is
`Rη`), so `‖bprodOdd R X z‖ ≥ R^X η ∏_{k∈ω,k≠l}(|k−l|−η) / ∏_{k∈ω}(|R²−kl|+|k|η)`.
Now (i) `∏_{k∈ω}(|R²−kl|+|k|η) ≤ R^{2X}/(1−η/2)`: pair `k,−k`, the pair product equals
`R⁴(1+2|k|η/R² + |k|²(η²−l²)/R⁴) ≤ R⁴(1+2|k|η/R²)`, and `∏(1+a_j) ≤ 1/(1−Σa_j)` with `Σ a_j = ηX²/(2R²) ≤ η/2`.
(ii) `∏_{k∈ω,k≠l}(|k−l|−η) ≥ 2(1−η/2)(2m−1)!!(2m−3)!!`: writing `k = 2j+1` for `j ∈ [−m, m−1]` and
`l = 2i₀+1`, the distances `|k−l| = 2|j−i₀|` form the multiset `{2t : 1≤t≤A} ∪ {2t : 1≤t≤B}` with
`A+B = 2m−1`. Since `Ψ(η) := ∏(d−η)/(1−η/2)` is decreasing in `η` (log-derivative
`1/(2−η) − Σ 1/(d−η) ≤ 0`), it suffices to check `η = 1/2`; there the value is
`∏_{t≤A}(2t−1/2)∏_{t≤B}(2t−1/2)`, minimised at the balanced split `A=m, B=m−1` (the ratio of
consecutive values is `(2A+3/2)/(2(2m−1−A)−1/2) ≥ 1` for `A ≥ m−1`), giving `(2m−1)!!(2m−3)!!`
because `2t−1/2 ≥ 2t−1`.
(iii) `2(2m−3)!!(2m−1)!! ≥ 4πX^{X−2}/e^X`: the sibling node `num25_even` states exactly this; a
self-contained route is `(2m−3)!!(2m−1)!! = ∏_{t=1}^{m−1}(4t²−1) ≥ 2^{2m−3}((m−1)!)²·(1/2)`, from
`∏(1−1/(4t²)) ≥ 1 − (1/4)Σ_t 1/t² ≥ 1/2` and `(m−1)! ≥ (e²/2)m^{m−1}e^{−m}` (induction, base
`m = 2`; `m = 1` is immediate), plus `e⁴ ≥ 16π`.
Assembly: `η(1−η/2)^X·2(2m−1)!!(2m−3)!!/R^X ≥ 4πη(1−η/2)²X^{X−2}/(e^X R^X)`.

Key facts: `0 < η`, `η < 1/2`, `X` even `≥ 2`, `(X:ℝ) + η ≤ R`, `l` odd with `|l| ≤ X`, `‖z − l‖ = η`;
`|z| ≤ |l| + η ≤ X + η ≤ R`, so no denominator `R²−kz` vanishes and `bprodOdd R X z ≠ 0`. A useful
reindexing identity: `bprodOdd R X z = ∏_{i ∈ range m} (bfac R (2i+1) z * bfac R (-(2i+1)) z)`. -/
theorem bprodOdd_norm_ge {R η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2) {X : ℕ} (hX : 2 ≤ X)
    (hXe : Even X) (hXR : (X : ℝ) + η ≤ R) {l : ℤ} (hlo : Odd l) (hl : |l| ≤ (X : ℤ))
    {z : ℂ} (hz : ‖z - (l : ℂ)‖ = η) :
    4 * Real.pi * η * (1 - η / 2) ^ 2 * (X : ℝ) ^ (X - 2) / (Real.exp (X : ℝ) * R ^ X)
      ≤ ‖bprodOdd R X z‖ := by
  obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hXe
  have hm : 1 ≤ m := by omega
  have hR : 0 < R := by
    have h1 : (2:ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast hX
    linarith
  have hloc : Odd l := hlo
  obtain ⟨i₀, hi₀⟩ := hloc
  have hlZ : |(2*i₀ + 1 : ℤ)| ≤ 2*(m:ℤ) := by rw [← hi₀]; simpa using hl
  have hA := (abs_le.mp hlZ).1
  have hB := (abs_le.mp hlZ).2
  have hpi₁ : -(m:ℤ) ≤ i₀ := by omega
  have hpi₂ : i₀ ≤ (m:ℤ) - 1 := by omega
  have hA0 : 0 ≤ (m:ℤ) - 1 - i₀ := by omega
  have hB0 : 0 ≤ (m:ℤ) + i₀ := by omega
  have hre := bpOdd_dist_reindex (η := η) hm hpi₁ hpi₂
  rw [← hi₀] at hre
  have hAB := toNat_add_toNat m i₀ hA0 hB0 hm
  have harith := bpOdd_dist_arith hη hη' hm hAB
  have hPge : 2*(1-η/2)*bpNum m ≤ ∏ k ∈ (oddIdx (2*m)).erase l, (|(k:ℝ)-(l:ℝ)|-η) := by
    rw [← hre]
    exact harith
  have hLP := bprodOdd_lower hη hη' hX hXe hXR hlo hl hz
  have hDle := bpOdd_den_prod_le hη hη' hX hXe hXR hlo hl
  have hNum := bpOdd_num25 m hm
  set P : ℝ := ∏ k ∈ (oddIdx (2*m)).erase l, (|(k:ℝ) - (l:ℝ)| - η) with hPdef
  set D : ℝ := ∏ k ∈ oddIdx (2*m), bpD R η l k with hDdef
  set K₀ : ℝ := 4 * Real.pi * (((2*m : ℕ)) : ℝ) ^ (2*m - 2) / Real.exp ((((2*m : ℕ)) : ℝ))
    with hKdef
  have hLP' : R^(2*m) * η * P / D ≤ ‖bprodOdd R (2*m) z‖ := by
    rw [hPdef, hDdef]
    exact hLP
  have hDle' : D ≤ R^(2*(2*m)) / (1-η/2) := by rw [hDdef]; exact hDle
  have hPge' : 2*(1-η/2)*bpNum m ≤ P := by rw [hPdef]; exact hPge
  have hNum' : K₀ ≤ 2*bpNum m := by rw [hKdef]; exact hNum
  have hDpos : 0 < D := by
    rw [hDdef]
    exact Finset.prod_pos (fun k hk => bpD_pos (le_of_lt hη) (bpDen_lt hη hX hXR hl hk))
  have hRpow : 0 < R^(2*m) := pow_pos hR _
  have hpow : R^(2*(2*m)) = R^(2*m) * R^(2*m) := by
    rw [show 2*(2*m) = 2*m + 2*m by omega, pow_add]
  have hN : 4 * Real.pi * η * (1-η/2)^2 * (((2*m:ℕ)):ℝ)^(2*m-2) / Real.exp ((((2*m:ℕ)):ℝ))
      = η * (1-η/2)^2 * K₀ := by
    rw [hKdef]; ring
  have hgoal : 4 * Real.pi * η * (1-η/2)^2 * (((2*m:ℕ)):ℝ)^(2*m-2)
        /(Real.exp ((((2*m:ℕ)):ℝ)) * R^(2*m))
      = (η * (1-η/2)^2 * K₀)/R^(2*m) := by
    rw [← div_div, hN]
  have key : (η * (1-η/2)^2 * K₀)/R^(2*m) ≤ R^(2*m)*η*P/D := by
    rw [le_div_iff₀ hDpos, div_mul_eq_mul_div, div_le_iff₀ hRpow]
    have hDle'' : D ≤ R^(2*m)*R^(2*m)/(1-η/2) := by rw [← hpow]; exact hDle'
    have h1 : η*(1-η/2)^2*K₀ * D ≤ η*(1-η/2)^2*K₀ * (R^(2*m)*R^(2*m)/(1-η/2)) :=
      mul_le_mul_of_nonneg_left hDle'' (by positivity)
    have hne : (1 - η/2) ≠ 0 := by linarith
    have h2 : η*(1-η/2)^2*K₀ * (R^(2*m)*R^(2*m)/(1-η/2))
        = η*(1-η/2)*K₀*(R^(2*m)*R^(2*m)) := by
      field_simp
    have hle : (1-η/2)*K₀ ≤ P := by
      have ha : (1-η/2)*K₀ ≤ (1-η/2)*(2*bpNum m) :=
        mul_le_mul_of_nonneg_left hNum' (by linarith)
      have hb : (1-η/2)*(2*bpNum m) = 2*(1-η/2)*bpNum m := by ring
      linarith [hPge']
    have h3 : η*(1-η/2)*K₀*(R^(2*m)*R^(2*m)) ≤ R^(2*m)*η*P*R^(2*m) := by
      have hB' : η*((1-η/2)*K₀)*(R^(2*m)*R^(2*m)) ≤ η*P*(R^(2*m)*R^(2*m)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (le_of_lt hη)) (by positivity)
      nlinarith [hB']
    linarith
  rw [hgoal]
  exact le_trans key hLP'


end Work.BW
