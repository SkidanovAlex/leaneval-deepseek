import Mathlib
import Submission.Work.Drive.subst_iteratedFDeriv_bound
import Submission.Work.Drive.sqrt_subst_fderiv_bound

open scoped Topology
open Set Filter

namespace Work.Drive

section

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The square-root descent -/

/-- `p ↦ S (p.1, √p.2)`, extended by `0` on the closed lower half-space. -/
noncomputable def sqrtDesc (S : X × ℝ → E) : X × ℝ → E :=
  fun p => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0

@[simp] lemma sqrtDesc_apply (S : X × ℝ → E) (p : X × ℝ) :
    sqrtDesc S p = if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0 := rfl

variable {S : X × ℝ → E}

lemma sqrtDesc_eventuallyEq_zero (y : X × ℝ) (hy : y.2 < 0) :
    sqrtDesc S =ᶠ[𝓝 y] (0 : X × ℝ → E) := by
  filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hy] with w hw
  rw [sqrtDesc_apply, if_neg (not_lt.mpr (le_of_lt hw)), Pi.zero_apply]

lemma iteratedFDeriv_sqrtDesc_eq_zero_of_neg (y : X × ℝ) (hy : y.2 < 0) (k : ℕ) :
    iteratedFDeriv ℝ k (sqrtDesc S) y = 0 := by
  have h2 := Filter.EventuallyEq.iteratedFDeriv ℝ (sqrtDesc_eventuallyEq_zero (S := S) y hy) k
  simpa using h2.eq_of_nhds

/-- On the open upper half-space the descent is smooth. -/
lemma contDiffAt_sqrtDesc_of_pos
    (hS : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S z)
    (y : X × ℝ) (hy : 0 < y.2) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sqrtDesc S) y := by
  have hpair : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : X × ℝ => (w.1, Real.sqrt w.2)) y :=
    contDiffAt_fst.prodMk (contDiffAt_snd.sqrt (ne_of_gt hy))
  have hSc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S (y.1, Real.sqrt y.2) :=
    hS _ (Real.sqrt_pos.2 hy)
  refine (hSc.comp y hpair).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hy] with w hw
  simp [sqrtDesc_apply, hw]

lemma iteratedFDeriv_succ_curryLeft (f : X × ℝ → E) (z : X × ℝ) (n : ℕ) :
    (iteratedFDeriv ℝ (n + 1) f z).curryLeft = fderiv ℝ (iteratedFDeriv ℝ n f) z := by
  apply ContinuousLinearMap.ext; intro v
  apply ContinuousMultilinearMap.ext; intro m
  rw [ContinuousMultilinearMap.curryLeft_apply, iteratedFDeriv_succ_apply_left]
  simp

/-! ### A power comparison -/

lemma sqrt_pow_le_pow {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {n k : ℕ} (h : 2 * k ≤ n) :
    (Real.sqrt u) ^ n ≤ u ^ k := by
  have hsu0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hsu1 : Real.sqrt u ≤ 1 := Real.sqrt_le_one.2 hu1
  have hsplit : (Real.sqrt u) ^ n = (Real.sqrt u) ^ (2 * k) * (Real.sqrt u) ^ (n - 2 * k) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  have h1 : (Real.sqrt u) ^ (n - 2 * k) ≤ 1 := pow_le_one₀ hsu0 hsu1
  have h2 : (Real.sqrt u) ^ (2 * k) = u ^ k := by
    rw [pow_mul (Real.sqrt u) 2 k, Real.sq_sqrt hu0]
  rw [h2]
  calc u ^ k * (Real.sqrt u) ^ (n - 2 * k) ≤ u ^ k * 1 :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hu0 k)
    _ = u ^ k := mul_one _

/-! ### The jet bound on the open half-space -/

lemma open_jet_bound {K m : ℕ} (hKm : 2 * m + 2 ≤ K) {S : X × ℝ → E}
    (hb : ∀ x₀ : X, ∃ C δ : ℝ, 0 < δ ∧ ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, 0 < t → t < δ →
      ∀ j : ℕ, j ≤ K → ‖iteratedFDeriv ℝ j S (x, t)‖ ≤ C * t ^ (K - j))
    (hS : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S z)
    {j : ℕ} (hj : j ≤ m) (z : X × ℝ) (hz : z.2 = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ y : X × ℝ, ‖y - z‖ < r → 0 < y.2 →
      ‖iteratedFDeriv ℝ j (sqrtDesc S) y‖ ≤ C * (Real.sqrt y.2) ^ (K - 2 * j) := by
  obtain ⟨b, hb0, hbsub⟩ := sqrt_subst_fderiv_bound X
  obtain ⟨c, hc0, hc⟩ := subst_iteratedFDeriv_bound (X := X) b hb0
    (fun m z hz0 hz1 => hbsub z hz0 hz1 m)
  obtain ⟨Cs, δ, hδpos, hCs⟩ := hb z.1
  refine ⟨min δ (min (δ ^ 2) 1) / 2, ?_, c j * (j + 1) * |Cs|, ?_, ?_⟩
  · have h1 : 0 < min δ (min (δ ^ 2) 1) :=
      lt_min hδpos (lt_min (by positivity) one_pos)
    linarith
  · exact mul_nonneg (mul_nonneg (hc0 j) (by positivity)) (abs_nonneg Cs)
  · intro y hy hyt
    have hyK : 2 * j ≤ K := by omega
    have hminpos : 0 ≤ min δ (min (δ ^ 2) 1) :=
      le_of_lt (lt_min hδpos (lt_min (by positivity) one_pos))
    have hrδ : min δ (min (δ ^ 2) 1) / 2 ≤ δ := by
      have hle := min_le_left δ (min (δ ^ 2) 1); linarith
    have hrδ2 : min δ (min (δ ^ 2) 1) / 2 ≤ δ ^ 2 := by
      have hle := le_trans (min_le_right δ (min (δ ^ 2) 1)) (min_le_left (δ ^ 2) 1); linarith
    have hr1 : min δ (min (δ ^ 2) 1) / 2 ≤ 1 := by
      have hle := le_trans (min_le_right δ (min (δ ^ 2) 1)) (min_le_right (δ ^ 2) 1); linarith
    have hysnd : y.2 ≤ ‖y - z‖ := by
      have h2 : (y - z).2 = y.2 := by simp [hz]
      calc y.2 ≤ ‖y.2‖ := by rw [Real.norm_eq_abs]; exact le_abs_self y.2
        _ = ‖(y - z).2‖ := by rw [h2]
        _ ≤ ‖y - z‖ := norm_snd_le _
    have hy1 : ‖y.1 - z.1‖ < δ := by
      have h1 : ‖y.1 - z.1‖ ≤ ‖y - z‖ := by
        have h2 : (y - z).1 = y.1 - z.1 := by simp
        calc ‖y.1 - z.1‖ = ‖(y - z).1‖ := by rw [h2]
          _ ≤ ‖y - z‖ := norm_fst_le _
      linarith [hy, hrδ]
    have hy2lt : y.2 < δ ^ 2 := by linarith [hysnd, hy, hrδ2]
    have hsqlt : Real.sqrt y.2 < δ := by
      calc Real.sqrt y.2 < Real.sqrt (δ ^ 2) := Real.sqrt_lt_sqrt (le_of_lt hyt) hy2lt
        _ = δ := Real.sqrt_sq (le_of_lt hδpos)
    have hy2le1 : y.2 ≤ 1 := by linarith [hysnd, hy, hr1]
    have hSOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S (Set.univ ×ˢ Set.Ioi 0) :=
      fun w hw => ContDiffWithinAt.mono (contDiffWithinAt_univ.mpr (hS w hw.2)) (Set.subset_univ _)
    have hmain := hc j E S hSOn y hyt hy2le1
    have hterm : ∀ i ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ i S (y.1, Real.sqrt y.2)‖ / (Real.sqrt y.2) ^ (2 * j - i)
          ≤ |Cs| * (Real.sqrt y.2) ^ (K - 2 * j) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hiK : i ≤ K := by omega
      have hs := hCs y.1 hy1 (Real.sqrt y.2) (Real.sqrt_pos.2 hyt) hsqlt i hiK
      have hsqrtpos : 0 < Real.sqrt y.2 := Real.sqrt_pos.2 hyt
      have hsqrtne : Real.sqrt y.2 ≠ 0 := ne_of_gt hsqrtpos
      have h2ji : 2 * j - i ≤ K - i := by omega
      calc ‖iteratedFDeriv ℝ i S (y.1, Real.sqrt y.2)‖ / (Real.sqrt y.2) ^ (2 * j - i)
          ≤ (Cs * (Real.sqrt y.2) ^ (K - i)) / (Real.sqrt y.2) ^ (2 * j - i) := by
            gcongr
          _ = Cs * ((Real.sqrt y.2) ^ (K - i) / (Real.sqrt y.2) ^ (2 * j - i)) := by ring
          _ = Cs * (Real.sqrt y.2) ^ (K - 2 * j) := by
            rw [div_eq_mul_inv, ← pow_sub₀ (Real.sqrt y.2) hsqrtne h2ji,
              show K - i - (2 * j - i) = K - 2 * j by omega]
          _ ≤ |Cs| * (Real.sqrt y.2) ^ (K - 2 * j) :=
            mul_le_mul_of_nonneg_right (le_abs_self Cs) (pow_nonneg (le_of_lt hsqrtpos) _)
    have hsum : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i S (y.1, Real.sqrt y.2)‖
            / (Real.sqrt y.2) ^ (2 * j - i)
        ≤ (j + 1 : ℝ) * (|Cs| * (Real.sqrt y.2) ^ (K - 2 * j)) := by
      calc _ ≤ ∑ i ∈ Finset.range (j + 1), |Cs| * (Real.sqrt y.2) ^ (K - 2 * j) :=
            Finset.sum_le_sum hterm
        _ = (j + 1 : ℝ) * (|Cs| * (Real.sqrt y.2) ^ (K - 2 * j)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    have heq : iteratedFDeriv ℝ j (sqrtDesc S) y
        = iteratedFDeriv ℝ j (fun y : X × ℝ => S (y.1, Real.sqrt y.2)) y := by
      have h1 : sqrtDesc S =ᶠ[𝓝 y] (fun y : X × ℝ => S (y.1, Real.sqrt y.2)) := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hyt] with w hw
        rw [sqrtDesc_apply, if_pos hw]
      exact (Filter.EventuallyEq.iteratedFDeriv ℝ h1 j).eq_of_nhds
    rw [heq]
    calc ‖iteratedFDeriv ℝ j (fun y : X × ℝ => S (y.1, Real.sqrt y.2)) y‖
          ≤ c j * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i S (y.1, Real.sqrt y.2)‖
              / (Real.sqrt y.2) ^ (2 * j - i) := hmain
      _ ≤ c j * ((j + 1 : ℝ) * (|Cs| * (Real.sqrt y.2) ^ (K - 2 * j))) :=
          mul_le_mul_of_nonneg_left hsum (hc0 j)
      _ = (c j * (j + 1) * |Cs|) * (Real.sqrt y.2) ^ (K - 2 * j) := by ring

end

/-! ### The main theorem -/

/-- **Smoothness of the truncated square-root descent.**

If `S` is smooth on the open upper half-space and its jets are bounded by
`‖D^j S (x,t)‖ ≤ C t^{K-j}` for `j ≤ K`, then `p ↦ (if 0 < p.2 then S (p.1, √p.2) else 0)`
is `C^m` whenever `2m + 2 ≤ K`. -/
theorem trunc_sqrt_contDiff {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {S : X × ℝ → E} {K m : ℕ}
    (hKm : 2 * m + 2 ≤ K)
    (hS : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S z)
    (hb : ∀ x₀ : X, ∃ C δ : ℝ, 0 < δ ∧ ∀ x : X, ‖x - x₀‖ < δ → ∀ t : ℝ, 0 < t → t < δ →
      ∀ j : ℕ, j ≤ K → ‖iteratedFDeriv ℝ j S (x, t)‖ ≤ C * t ^ (K - j)) :
    ContDiff ℝ m (fun p : X × ℝ => if 0 < p.2 then S (p.1, Real.sqrt p.2) else 0) := by
  change ContDiff ℝ m (sqrtDesc S)
  have key : ∀ k, k ≤ m →
      (∀ z : X × ℝ, z.2 = 0 → iteratedFDeriv ℝ k (sqrtDesc S) z = 0) ∧
      (∀ z : X × ℝ, z.2 = 0 →
        ContinuousAt (fun y : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) y) z) ∧
      (k < m → ∀ z : X × ℝ, z.2 = 0 →
        HasFDerivAt (fun y : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) y)
          (0 : (X × ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) E) z) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih hk
    have hE1 : ∀ z : X × ℝ, z.2 = 0 → iteratedFDeriv ℝ k (sqrtDesc S) z = 0 := by
      intro z hz
      cases k with
      | zero =>
        ext w
        rw [iteratedFDeriv_zero_apply]
        simp [sqrtDesc_apply, hz]
      | succ k' =>
        have hk'le : k' ≤ m := by omega
        have hk'm : k' < m := by omega
        have hhas : HasFDerivAt (fun y : X × ℝ => iteratedFDeriv ℝ k' (sqrtDesc S) y) 0 z :=
          (ih k' (Nat.lt_succ_self k') hk'le).2.2 hk'm z hz
        have hfz : fderiv ℝ (iteratedFDeriv ℝ k' (sqrtDesc S)) z = 0 := hhas.fderiv
        ext w
        rw [iteratedFDeriv_succ_apply_left]
        simp only [hfz, ContinuousLinearMap.zero_apply]
    have hE2 : ∀ z : X × ℝ, z.2 = 0 →
        ContinuousAt (fun y : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) y) z := by
      intro z hz
      obtain ⟨r, hr, C, hC, hbnd⟩ := open_jet_bound (X := X) (E := E) hKm hb hS hk z hz
      have hval : iteratedFDeriv ℝ k (sqrtDesc S) z = 0 := hE1 z hz
      have hysnd_of : ∀ y : X × ℝ, y.2 ≤ ‖y - z‖ := by
        intro y
        have h2 : (y - z).2 = y.2 := by simp [hz]
        calc y.2 ≤ ‖y.2‖ := by rw [Real.norm_eq_abs]; exact le_abs_self y.2
          _ = ‖(y - z).2‖ := by rw [h2]
          _ ≤ ‖y - z‖ := norm_snd_le _
      have hbndval : ∀ y : X × ℝ, ‖y - z‖ < r → ‖y - z‖ < 1 →
          ‖iteratedFDeriv ℝ k (sqrtDesc S) y‖ ≤ C * ‖y - z‖ := by
        intro y hyr hle1
        have hysnd := hysnd_of y
        rcases lt_trichotomy y.2 0 with hlt | heq | hgt
        · rw [iteratedFDeriv_sqrtDesc_eq_zero_of_neg y hlt k, norm_zero]; positivity
        · rw [hE1 y heq, norm_zero]; positivity
        · have hb1 := hbnd y hyr hgt
          have hy1le : y.2 ≤ 1 := le_of_lt (lt_of_le_of_lt hysnd hle1)
          have hpow : (Real.sqrt y.2) ^ (K - 2 * k) ≤ y.2 := by
            have h := sqrt_pow_le_pow (u := y.2) (le_of_lt hgt) hy1le (n := K - 2 * k) (k := 1) (by omega)
            simpa using h
          calc ‖iteratedFDeriv ℝ k (sqrtDesc S) y‖ ≤ C * (Real.sqrt y.2) ^ (K - 2 * k) := hb1
            _ ≤ C * y.2 := mul_le_mul_of_nonneg_left hpow hC
            _ ≤ C * ‖y - z‖ := mul_le_mul_of_nonneg_left hysnd hC
      rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨min r (min 1 (ε / (C + 1))),
        lt_min hr (lt_min one_pos (div_pos hε (by linarith))), ?_⟩
      intro y hy
      rw [dist_eq_norm] at hy
      have hyr : ‖y - z‖ < r := lt_of_lt_of_le hy (min_le_left _ _)
      have hy1 : ‖y - z‖ < 1 :=
        lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_left _ _))
      have hyε : ‖y - z‖ < ε / (C + 1) :=
        lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_right _ _))
      calc dist (iteratedFDeriv ℝ k (sqrtDesc S) y) (iteratedFDeriv ℝ k (sqrtDesc S) z)
          = ‖iteratedFDeriv ℝ k (sqrtDesc S) y‖ := by rw [dist_eq_norm, hval, sub_zero]
        _ ≤ C * ‖y - z‖ := hbndval y hyr hy1
        _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hyε) hC
        _ = (C / (C + 1)) * ε := by ring
        _ < 1 * ε := by
            refine mul_lt_mul_of_pos_right ?_ hε
            rw [div_lt_one (by linarith : (0 : ℝ) < C + 1)]
            linarith
        _ = ε := one_mul _
    have hE3 : k < m → ∀ z : X × ℝ, z.2 = 0 →
        HasFDerivAt (fun y : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) y)
          (0 : (X × ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) E) z := by
      intro hkm z hz
      obtain ⟨r, hr, C, hC, hbnd⟩ := open_jet_bound (X := X) (E := E) hKm hb hS hk z hz
      have hysnd_of : ∀ y : X × ℝ, y.2 ≤ ‖y - z‖ := by
        intro y
        have h2 : (y - z).2 = y.2 := by simp [hz]
        calc y.2 ≤ ‖y.2‖ := by rw [Real.norm_eq_abs]; exact le_abs_self y.2
          _ = ‖(y - z).2‖ := by rw [h2]
          _ ≤ ‖y - z‖ := norm_snd_le _
      have hev : ∀ᶠ y in 𝓝 z, ‖iteratedFDeriv ℝ k (sqrtDesc S) y‖ ≤ C * ‖y - z‖ ^ 2 := by
        rw [Metric.eventually_nhds_iff]
        refine ⟨min r 1, lt_min hr one_pos, fun y hy => ?_⟩
        rw [dist_eq_norm] at hy
        have hyr : ‖y - z‖ < r := lt_of_lt_of_le hy (min_le_left _ _)
        have hle1 : ‖y - z‖ < 1 := lt_of_lt_of_le hy (min_le_right _ _)
        have hysnd := hysnd_of y
        rcases lt_trichotomy y.2 0 with hlt | heq | hgt
        · rw [iteratedFDeriv_sqrtDesc_eq_zero_of_neg y hlt k, norm_zero]; positivity
        · rw [hE1 y heq, norm_zero]; positivity
        · have hb1 := hbnd y hyr hgt
          have hy1le : y.2 ≤ 1 := le_of_lt (lt_of_le_of_lt hysnd hle1)
          calc ‖iteratedFDeriv ℝ k (sqrtDesc S) y‖ ≤ C * (Real.sqrt y.2) ^ (K - 2 * k) := hb1
            _ ≤ C * ‖y - z‖ ^ 2 :=
                mul_le_mul_of_nonneg_left
                  (le_trans (sqrt_pow_le_pow (u := y.2) (le_of_lt hgt) hy1le
                      (n := K - 2 * k) (k := 2) (by omega))
                    (pow_le_pow_left₀ (le_of_lt hgt) hysnd 2)) hC
      have hO : (fun y : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) y)
          =O[𝓝 z] (fun y : X × ℝ => ‖y - z‖ ^ 2) := by
        refine Asymptotics.IsBigO.of_bound C ?_
        filter_upwards [hev] with y hyv
        rw [show ‖(fun y : X × ℝ => ‖y - z‖ ^ 2) y‖ = ‖y - z‖ ^ 2 from by
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg _)]]
        exact hyv
      have hsq : (fun y : X × ℝ => ‖y - z‖ ^ 2) =o[𝓝 z] (fun y : X × ℝ => y - z) := by
        have h1 : (fun x : X × ℝ => ‖x‖ ^ 2) =o[𝓝 0] (fun x : X × ℝ => x) :=
          Asymptotics.isLittleO_norm_pow_id (E' := X × ℝ) (n := 2) (by norm_num)
        have ht : Filter.Tendsto (fun y : X × ℝ => y - z) (𝓝 z) (𝓝 0) := by
          have h : Filter.Tendsto (fun y : X × ℝ => y - z) (𝓝 z) (𝓝 (z - z)) :=
            (continuous_id.sub continuous_const).tendsto z
          simpa using h
        refine (h1.comp_tendsto ht).congr (fun y => rfl) (fun y => rfl)
      have hlittle := hO.trans_isLittleO hsq
      rw [hasFDerivAt_iff_isLittleO]
      refine hlittle.congr (fun y => ?_) (fun y => rfl)
      simp [hE1 z hz]
    exact ⟨hE1, hE2, hE3⟩
  rw [← contDiffOn_univ]
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn (𝕜 := ℝ) (s := Set.univ) (f := sqrtDesc S)
    uniqueDiffOn_univ]
  constructor
  · intro k hk
    have hfun : (fun x : X × ℝ => iteratedFDerivWithin ℝ k (sqrtDesc S) Set.univ x)
        = fun x : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) x := by
      funext x; rw [iteratedFDerivWithin_univ]
    rw [hfun, continuousOn_univ, continuous_iff_continuousAt]
    intro y
    rcases lt_trichotomy y.2 0 with hlt | heq | hgt
    · have h1 : (fun y : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) y)
          =ᶠ[𝓝 y] (fun _ : X × ℝ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) E)) := by
        filter_upwards [Filter.EventuallyEq.iteratedFDeriv ℝ
          (sqrtDesc_eventuallyEq_zero (S := S) y hlt) k] with w hw
        rw [hw]
        simp
      exact continuousAt_const.congr h1.symm
    · exact (key k hk).2.1 y heq
    · exact ((contDiffAt_sqrtDesc_of_pos hS y hgt).iteratedFDeriv_right
        (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (le_of_eq rfl)).continuousAt
  · intro k hk
    have hfun : (fun x : X × ℝ => iteratedFDerivWithin ℝ k (sqrtDesc S) Set.univ x)
        = fun x : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) x := by
      funext x; rw [iteratedFDerivWithin_univ]
    rw [hfun]
    intro y _
    rw [differentiableWithinAt_univ]
    rcases lt_trichotomy y.2 0 with hlt | heq | hgt
    · have h1 : (fun y : X × ℝ => iteratedFDeriv ℝ k (sqrtDesc S) y)
          =ᶠ[𝓝 y] (fun _ : X × ℝ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) E)) := by
        filter_upwards [Filter.EventuallyEq.iteratedFDeriv ℝ
          (sqrtDesc_eventuallyEq_zero (S := S) y hlt) k] with w hw
        rw [hw]
        simp
      exact (differentiableAt_const (0 : ContinuousMultilinearMap ℝ (fun _ : Fin k => X × ℝ) E)).congr_of_eventuallyEq h1
    · exact ((key k (le_of_lt hk)).2.2 hk y heq).differentiableAt
    · exact ((contDiffAt_sqrtDesc_of_pos hS y hgt).iteratedFDeriv_right
        (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (le_of_eq rfl)).differentiableAt (by simp)

end Work.Drive
