import Mathlib
import Submission.Work.NN.Core.czB_holderNorm_bound
import Submission.Work.NN.Core.bmPotential_differentiableAt_holder
import Submission.Work.NN.Core.beltrami_theta_setup
import Submission.Work.NN.Core.holderNorm_le_of_tendsto

noncomputable section

open scoped NNReal ENNReal
open Set Filter

namespace Work.NN.Core

theorem beltrami_theta_fixedpoint {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (c : Fin n → Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ),
        (∀ k j, ContDiff ℝ ⊤ (c k j)) →
        (∀ k j, HasCompactSupport (c k j)) →
        (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ) →
        (∀ k, ContDiff ℝ 1 (G k)) →
        (∀ k, HasCompactSupport (G k)) →
        (∀ k, Work.CR.Flat.holderNorm 0 α (G k) Set.univ < ⊤) →
        ∃ F : Fin n → (Fin n → ℂ) → ℂ,
          (∀ j, HasCompactSupport (F j)) ∧
          (∀ j, Work.CR.Flat.holderNorm 0 α (F j) Set.univ < ⊤) ∧
          (∀ j z, F j z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * (∑ l,
              c j l z * Work.CR.Flat.dCoord l (Work.CR.Flat.Cauchy.bmPotential F) z) + G j z) := by
  classical
  set τ : Fin n → ℝ := fun j => 2 * ρ j with hτdef
  have hτpos : ∀ j, 0 < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  have hρτ : ∀ j, ρ j < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  obtain ⟨CA, hCApos, hCA⟩ := BTheta.one_step_bound (n := n) hn (α := α) hα0 hα1 hρ hτpos hρτ
  set q : ℝ := (n : ℝ) * CA with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hdenpos : (0 : ℝ) < 2 * q + 1 := by linarith
  refine ⟨1 / (2 * q + 1), by positivity, ?_⟩
  intro c G hcsm hccs hcsupp hcnorm hGsm hGcs hGnorm
  set δ : ℝ := 1 / (2 * q + 1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set lam : ℝ := q * δ with hlamdef
  have hlam0 : 0 ≤ lam := by rw [hlamdef, hδdef]; positivity
  have hlamhalf : lam ≤ 1 / 2 := by
    rw [hlamdef, hδdef, mul_one_div, div_le_iff₀ hdenpos]
    linarith
  have hlam1 : lam < 1 := by linarith
  have h1lam : (0 : ℝ) < 1 - lam := by linarith
  have hcnorm_lt : ∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ < ⊤ :=
    fun k j => lt_of_le_of_lt (hcnorm k j) ENNReal.ofReal_lt_top
  set S₀ : Fin n → (Fin n → ℂ) → ℂ := BTheta.beltramiTheta c G with hS₀def
  have hS₀fin : BTheta.famNorm α S₀ < ⊤ := by
    refine BTheta.famNorm_lt_top fun j => ?_
    obtain ⟨Cj, -, hCj⟩ := BTheta.one_step_finite (n := n) hn (α := α) hα0 hα1 hρ hτpos hρτ
      (fun l => c j l) G (fun l => hcnorm_lt j l)
      (fun l z hz => hcsupp j l z hz) hGsm hGcs hGnorm
    rw [hS₀def, BTheta.beltramiTheta_eq_of_row]
    exact lt_of_le_of_lt hCj ENNReal.ofReal_lt_top
  have hstep : ∀ H : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, Work.CR.Flat.holderNorm 0 α (H j) Set.univ < ⊤) →
      (∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → H j z = 0) →
      BTheta.famNorm α (BTheta.beltramiTheta c H) ≤ ENNReal.ofReal lam * BTheta.famNorm α H := by
    intro H hHfin hHvan
    have hcomp : ∀ j, Work.CR.Flat.holderNorm 0 α (BTheta.beltramiTheta c H j) Set.univ
        ≤ ENNReal.ofReal (CA * δ) * BTheta.famNorm α H := by
      intro j
      have h := hCA (fun l => c j l) H δ (fun l => hcnorm j l)
        (fun l z hz => hcsupp j l z hz) hHfin hHvan
      rw [BTheta.beltramiTheta_eq_of_row]
      exact h
    calc BTheta.famNorm α (BTheta.beltramiTheta c H)
        = ∑ j, Work.CR.Flat.holderNorm 0 α (BTheta.beltramiTheta c H j) Set.univ := rfl
      _ ≤ ∑ _j : Fin n, ENNReal.ofReal (CA * δ) * BTheta.famNorm α H :=
          Finset.sum_le_sum fun j _ => hcomp j
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal (CA * δ) * BTheta.famNorm α H) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) * (CA * δ)) * BTheta.famNorm α H := by
          rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from (ENNReal.ofReal_natCast n).symm,
            ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
      _ = ENNReal.ofReal lam * BTheta.famNorm α H := by
          have h : ((n : ℝ) * (CA * δ)) = lam := by rw [hlamdef, hqdef]; ring
          rw [h]
  let Y : ℕ → Fin n → (Fin n → ℂ) → ℂ := fun m => Nat.rec (0 : Fin n → (Fin n → ℂ) → ℂ)
    (fun _ Yk => BTheta.beltramiTheta c Yk + S₀) m
  have Y_zero : Y 0 = 0 := rfl
  have Y_succ : ∀ m, Y (m + 1) = BTheta.beltramiTheta c (Y m) + S₀ := fun m => rfl
  have hYvan : ∀ m, ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y m j z = 0 := by
    intro m
    induction m with
    | zero => intro j z hz; rw [Y_zero]; rfl
    | succ m ih =>
        intro j z hz
        rw [Y_succ m]
        have h1 : BTheta.beltramiTheta c (Y m) j z = 0 :=
          BTheta.beltramiTheta_vanishes hcsupp (Y m) j z hz
        have h2 : S₀ j z = 0 := by
          rw [hS₀def]
          exact BTheta.beltramiTheta_vanishes hcsupp G j z hz
        simp [h1, h2]
  have hYfin : ∀ m, BTheta.famNorm α (Y m) < ⊤ := by
    intro m
    induction m with
    | zero => rw [Y_zero]; simp
    | succ m ih =>
        rw [Y_succ m]
        have h1 : BTheta.famNorm α (BTheta.beltramiTheta c (Y m)) < ⊤ :=
          lt_of_le_of_lt (hstep (Y m) (fun j => lt_of_le_of_lt
            (BTheta.famNorm_apply_le (α := α) (Y m) j) ih) (hYvan m))
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ih)
        exact lt_of_le_of_lt (BTheta.famNorm_add_le _ _)
          (ENNReal.add_lt_top.mpr ⟨h1, hS₀fin⟩)
  set s : ℝ := (BTheta.famNorm α S₀).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hS₀eq : BTheta.famNorm α S₀ = ENNReal.ofReal s := by
    rw [hsdef]; exact (ENNReal.ofReal_toReal (ne_of_lt hS₀fin)).symm
  set T : ℕ → ℝ := fun m => ∑ i ∈ Finset.range m, lam ^ i with hTdef
  have hTnn : ∀ m, 0 ≤ T m := fun m => Finset.sum_nonneg fun i _ => pow_nonneg hlam0 i
  have hTsucc : ∀ m, T (m + 1) = 1 + lam * T m := by
    intro m
    have h2 : (∑ i ∈ Finset.range m, lam ^ (i + 1)) = lam * T m := by
      rw [hTdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ']
    calc T (m + 1) = ∑ i ∈ Finset.range (m + 1), lam ^ i := rfl
      _ = (∑ i ∈ Finset.range m, lam ^ (i + 1)) + lam ^ 0 := Finset.sum_range_succ' _ _
      _ = lam * T m + 1 := by rw [h2, pow_zero]
      _ = 1 + lam * T m := by ring
  have hTbound : ∀ m, T m ≤ 1 / (1 - lam) := by
    intro m
    induction m with
    | zero =>
        show (0 : ℝ) ≤ 1 / (1 - lam)
        exact div_nonneg zero_le_one h1lam.le
    | succ m ih =>
        rw [hTsucc m]
        have h2 : lam * T m ≤ lam * (1 / (1 - lam)) := mul_le_mul_of_nonneg_left ih hlam0
        have h3 : lam * (1 / (1 - lam)) = 1 / (1 - lam) - 1 := by
          field_simp
          ring
        linarith
  have hbd : ∀ m, BTheta.famNorm α (Y m) ≤ ENNReal.ofReal (s * T m) := by
    intro m
    induction m with
    | zero => rw [Y_zero]; simp
    | succ m ih =>
        rw [Y_succ m]
        have h1 : BTheta.famNorm α (BTheta.beltramiTheta c (Y m)) ≤
            ENNReal.ofReal lam * BTheta.famNorm α (Y m) :=
          hstep (Y m) (fun j => lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Y m) j) (hYfin m))
            (hYvan m)
        refine (BTheta.famNorm_add_le _ _).trans ?_
        have h1' : ENNReal.ofReal lam * BTheta.famNorm α (Y m)
            ≤ ENNReal.ofReal lam * ENNReal.ofReal (s * T m) := mul_le_mul_right ih _
        have hkey : ENNReal.ofReal lam * ENNReal.ofReal (s * T m) + ENNReal.ofReal s
            ≤ ENNReal.ofReal (s * T (m + 1)) := by
          rw [← ENNReal.ofReal_mul hlam0, ← ENNReal.ofReal_add (mul_nonneg hlam0 (mul_nonneg hs0 (hTnn m))) hs0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hTsucc m]
          nlinarith [hs0, hlam0, hTnn m]
        refine (add_le_add h1 le_rfl).trans ?_
        rw [hS₀eq]
        exact (add_le_add h1' le_rfl).trans hkey
  have hdiff : ∀ m, BTheta.famNorm α (Y (m + 1) - Y m) ≤ ENNReal.ofReal (lam ^ m * s) := by
    intro m
    induction m with
    | zero =>
        have h0 : Y (0 + 1) - Y 0 = S₀ := by
          rw [Y_succ 0, Y_zero, BTheta.beltramiTheta_zero]
          simp
        rw [h0, hS₀eq, pow_zero, one_mul]
    | succ m ih =>
        have hsub : Y (m + 1 + 1) - Y (m + 1)
            = BTheta.beltramiTheta c (Y (m + 1) - Y m) := by
          have h1 : Y (m + 1 + 1) - Y (m + 1)
              = (BTheta.beltramiTheta c (Y (m + 1)) + S₀)
                - (BTheta.beltramiTheta c (Y m) + S₀) := by
            rw [Y_succ (m + 1), Y_succ m]
          rw [h1]
          funext j z
          have hthis := BTheta.beltramiTheta_sub_apply hn hα0 hα1 hρ hτpos hρτ hcsupp
            (fun j => lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Y (m + 1)) j)
              (hYfin (m + 1)))
            (hYvan (m + 1))
            (fun j => lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Y m) j) (hYfin m))
            (hYvan m) j z
          have h2 : (BTheta.beltramiTheta c (Y (m + 1)) + S₀ - (BTheta.beltramiTheta c (Y m) + S₀))
              = BTheta.beltramiTheta c (Y (m + 1)) - BTheta.beltramiTheta c (Y m) := by
            funext j z
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
          rw [h2]
          exact hthis
        rw [hsub]
        refine (hstep (Y (m + 1) - Y m) ?_ ?_).trans ?_
        · intro j
          exact lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Y (m + 1) - Y m) j)
            (lt_of_le_of_lt (BTheta.famNorm_sub_le (α := α) (Y (m + 1)) (Y m))
              (ENNReal.add_lt_top.mpr ⟨hYfin (m+1), hYfin m⟩))
        · intro j z hz
          simp only [Pi.sub_apply, hYvan (m + 1) j z hz, hYvan m j z hz, sub_zero]
        · refine (mul_le_mul_right ih _).trans ?_
          rw [← ENNReal.ofReal_mul hlam0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [pow_succ]
          exact le_of_eq (by ring)
  have hcau : ∀ m m' : ℕ, m ≤ m' → BTheta.famNorm α (Y m' - Y m)
      ≤ ENNReal.ofReal (s * (lam ^ m / (1 - lam))) := by
    intro m m' hmm
    have hsub : Y m' - Y m = ∑ i ∈ Finset.range (m' - m), (Y (m + i + 1) - Y (m + i)) := by
      funext j z
      have h := BTheta.sub_eq_sum_range (fun i => Y i j z) m (m' - m)
      rw [show m + (m' - m) = m' from Nat.add_sub_cancel' hmm] at h
      simpa only [Pi.sub_apply, Finset.sum_apply] using h
    rw [hsub]
    refine (BTheta.famNorm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hdiff (m + i)).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (pow_nonneg hlam0 _) hs0)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∑ i ∈ Finset.range (m' - m), lam ^ (m + i) * s
        = s * (lam ^ m * T (m' - m)) := by
          rw [hTdef, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_add]
          ring
      _ ≤ s * (lam ^ m * (1 / (1 - lam))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hTbound _)
            (pow_nonneg hlam0 m)) hs0
      _ = s * (lam ^ m / (1 - lam)) := by ring
  have hcau' : ∀ m m' : ℕ, BTheta.famNorm α (Y m - Y m')
      ≤ ENNReal.ofReal (s * (lam ^ (min m m') / (1 - lam))) := by
    intro m m'
    rcases le_total m m' with hle | hle
    · rw [min_eq_left hle]
      have h := hcau m m' hle
      rwa [show Y m - Y m' = -(Y m' - Y m) from by
        funext a b
        simp only [Pi.sub_apply, Pi.neg_apply]
        ring,
        BTheta.famNorm_neg (α := α)]
    · rw [min_eq_right hle]
      exact hcau m' m hle
  have htendlam : Tendsto (fun m : ℕ => s * (lam ^ m / (1 - lam))) atTop (nhds 0) := by
    have h1 : Tendsto (fun m : ℕ => lam ^ m) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1
    have h2 : Tendsto (fun m : ℕ => (s / (1 - lam)) * lam ^ m) atTop (nhds ((s / (1 - lam)) * 0)) :=
      tendsto_const_nhds.mul h1
    rw [mul_zero] at h2
    refine h2.congr' (Eventually.of_forall fun m => ?_)
    ring
  have hlim : ∀ (j : Fin n) (z : Fin n → ℂ), ∃ y : ℂ, Tendsto (fun m => Y m j z) atTop (nhds y) := by
    intro j z
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 htendlam).2 ε hε)
    refine ⟨M, fun m hm m' hm' => ?_⟩
    rw [dist_eq_norm]
    have hmin : M ≤ min m m' := le_min hm hm'
    have hc : BTheta.famNorm α (Y m - Y m') ≤
        ENNReal.ofReal (s * (lam ^ (min m m') / (1 - lam))) := by
      rcases le_total m m' with hle | hle
      · have h := hcau m m' hle
        rw [min_eq_left hle]
        rwa [show Y m - Y m' = -(Y m' - Y m) from by
            funext j z
            simp only [Pi.sub_apply, Pi.neg_apply]
            ring,
          BTheta.famNorm_neg (α := α)]
      · have h := hcau m' m hle
        rw [min_eq_right hle]
        exact h
    have h1 : ENNReal.ofReal ‖Y m j z - Y m' j z‖ ≤
        ENNReal.ofReal (s * (lam ^ (min m m') / (1 - lam))) :=
      ((Work.CR.Flat.norm_apply_le_holderNorm 0 α ((Y m - Y m') j) Set.univ
        (Set.mem_univ z)).trans (BTheta.famNorm_apply_le (α := α) (Y m - Y m') j)).trans hc
    have h2 : ‖Y m j z - Y m' j z‖ ≤ s * (lam ^ (min m m') / (1 - lam)) := by
      refine (ENNReal.ofReal_le_ofReal_iff ?_).mp h1
      positivity
    have h3 : s * (lam ^ (min m m') / (1 - lam)) ≤ s * (lam ^ M / (1 - lam)) := by
      refine mul_le_mul_of_nonneg_left ?_ hs0
      refine div_le_div_of_nonneg_right ?_ h1lam.le
      exact pow_le_pow_of_le_one hlam0 (by linarith [hlamhalf] : lam ≤ 1) hmin
    have h4 : s * (lam ^ M / (1 - lam)) < ε := hM M le_rfl
    linarith
  choose Yinf hYinf using hlim
  have hYinf_fin : ∀ j, Work.CR.Flat.holderNorm 0 α (Yinf j) Set.univ < ⊤ := by
    intro j
    have hcont : ∀ m, ContDiffOn ℝ (0 : ℕ∞) ((Y m) j) Set.univ := fun m =>
      contDiffOn_zero.mpr ((continuous_of_holderNorm_zero_lt_top hα0
        (lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Y m) j)
          (hYfin m))).continuousOn)
    have hbound : ∀ m, Work.CR.Flat.holderNorm 0 α ((Y m) j) Set.univ
        ≤ ENNReal.ofReal (s * (1 / (1 - lam))) := fun m => by
      refine (BTheta.famNorm_apply_le (α := α) (Y m) j).trans ((hbd m).trans ?_)
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hTbound m) hs0)
    have hcaum : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m m' : ℕ, M ≤ m → M ≤ m' →
        Work.CR.Flat.holderNorm 0 α ((Y m - Y m') j) Set.univ ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 htendlam).2 ε hε)
      refine ⟨M, fun m m' hm hm' => ?_⟩
      have hmin : M ≤ min m m' := le_min hm hm'
      refine (BTheta.famNorm_apply_le (α := α) (Y m - Y m') j).trans
        ((hcau' m m').trans ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 : s * (lam ^ (min m m') / (1 - lam)) ≤ s * (lam ^ M / (1 - lam)) := by
        refine mul_le_mul_of_nonneg_left ?_ hs0
        refine div_le_div_of_nonneg_right ?_ h1lam.le
        exact pow_le_pow_of_le_one hlam0 (by linarith [hlamhalf] : lam ≤ 1) hmin
      linarith [hM M le_rfl]
    obtain ⟨h1, -⟩ := Work.NN.Core.holderNorm_le_of_tendsto (X := Fin n → ℂ) (k := 0) (α := α)
      (P := Set.univ) isOpen_univ (C := s * (1 / (1 - lam))) (by positivity)
      hcont hbound (fun z _ => hYinf j z) hcaum
    exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have hYinf_van : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Yinf j z = 0 := by
    intro j z hz
    have h0 : Tendsto (fun m => Y m j z) atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards with m
      exact (hYvan m j z hz).symm
    exact tendsto_nhds_unique (hYinf j z) h0
  have hYinf_diff : ∀ m j, Work.CR.Flat.holderNorm 0 α ((Y m - Yinf) j) Set.univ
      ≤ ENNReal.ofReal (s * (lam ^ m / (1 - lam))) := by
    intro m j
    have hconv : ∀ z ∈ (Set.univ : Set (Fin n → ℂ)),
        Tendsto (fun k => (Y m - Y (m + k)) j z) atTop (nhds ((Y m - Yinf) j z)) := by
      intro z _
      have h1 : Tendsto (fun k => Y (m + k) j z) atTop (nhds (Yinf j z)) := by
        have h2 : (fun k : ℕ => Y (m + k) j z) = fun k => Y (k + m) j z := by
          funext k
          rw [Nat.add_comm]
        rw [h2]
        exact (hYinf j z).comp (tendsto_add_atTop_nat m)
      have h2 : Tendsto (fun k => Y m j z - Y (m + k) j z) atTop (nhds (Y m j z - Yinf j z)) :=
        tendsto_const_nhds.sub h1
      simpa only [Pi.sub_apply] using h2
    have hcont : ∀ k : ℕ, ContDiffOn ℝ (0 : ℕ∞) ((Y m - Y (m + k)) j) Set.univ := fun k => by
      have h1 : Continuous ((Y m) j - (Y (m + k)) j) :=
        (continuous_of_holderNorm_zero_lt_top hα0 (lt_of_le_of_lt
          (BTheta.famNorm_apply_le (α := α) (Y m) j) (hYfin m))).sub
        (continuous_of_holderNorm_zero_lt_top hα0 (lt_of_le_of_lt
          (BTheta.famNorm_apply_le (α := α) (Y (m + k)) j) (hYfin (m + k))))
      have h2 : ((Y m - Y (m + k)) j) = ((Y m) j - (Y (m + k)) j) := rfl
      rw [h2]
      exact contDiffOn_zero.mpr h1.continuousOn
    have hbound : ∀ k : ℕ, Work.CR.Flat.holderNorm 0 α ((Y m - Y (m + k)) j) Set.univ
        ≤ ENNReal.ofReal (s * (lam ^ m / (1 - lam))) := fun k => by
      have h := hcau' m (m + k)
      rw [min_eq_left (Nat.le_add_right m k)] at h
      refine (BTheta.famNorm_apply_le (α := α) (Y m - Y (m + k)) j).trans h
    have hcaum : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ k k' : ℕ, M ≤ k → M ≤ k' →
        Work.CR.Flat.holderNorm 0 α ((Y m - Y (m + k)) j - (Y m - Y (m + k')) j) Set.univ
          ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 htendlam).2 ε hε)
      refine ⟨M, fun k k' hk hk' => ?_⟩
      have hmin : M ≤ min (m + k') (m + k) := le_min (by linarith) (by linarith)
      have hsub : ((Y m - Y (m + k)) j - (Y m - Y (m + k')) j)
          = (Y (m + k') - Y (m + k)) j := by
        funext a
        simp only [Pi.sub_apply]
        ring
      rw [hsub]
      refine (BTheta.famNorm_apply_le (α := α) (Y (m + k') - Y (m + k)) j).trans
        ((hcau' (m + k') (m + k)).trans ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 : s * (lam ^ (min (m + k') (m + k)) / (1 - lam))
          ≤ s * (lam ^ M / (1 - lam)) := by
        refine mul_le_mul_of_nonneg_left ?_ hs0
        refine div_le_div_of_nonneg_right ?_ h1lam.le
        exact pow_le_pow_of_le_one hlam0 (by linarith [hlamhalf] : lam ≤ 1) hmin
      linarith [hM M le_rfl]
    obtain ⟨h1, -⟩ := Work.NN.Core.holderNorm_le_of_tendsto (X := Fin n → ℂ) (k := 0) (α := α)
      (P := Set.univ) isOpen_univ (C := s * (lam ^ m / (1 - lam))) (by positivity)
      hcont hbound hconv hcaum
    exact h1
  have hfam_diff : ∀ m, BTheta.famNorm α (Y m - Yinf)
      ≤ ENNReal.ofReal ((n : ℝ) * (s * (lam ^ m / (1 - lam)))) := by
    intro m
    have hsum : BTheta.famNorm α (Y m - Yinf)
        = ∑ j, Work.CR.Flat.holderNorm 0 α ((Y m - Yinf) j) Set.univ := rfl
    rw [hsum]
    refine (Finset.sum_le_sum fun j _ => hYinf_diff m j).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
  have hfeq : ∀ j z, Yinf j z = BTheta.beltramiTheta c Yinf j z + S₀ j z := by
    intro j z
    have hconvY : Tendsto (fun m => Y (m + 1) j z) atTop (nhds (Yinf j z)) := by
      have h2 : (fun m : ℕ => Y (m + 1) j z) = fun m => Y (m + 1) j z := rfl
      rw [h2]
      exact (hYinf j z).comp (tendsto_add_atTop_nat 1)
    have hconvΦ : Tendsto (fun m => BTheta.beltramiTheta c (Y m) j z) atTop
        (nhds (BTheta.beltramiTheta c Yinf j z)) := by
      have hb : ∀ m, ‖BTheta.beltramiTheta c (Y m) j z - BTheta.beltramiTheta c Yinf j z‖
          ≤ lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam)))) := by
        intro m
        have hsub : BTheta.beltramiTheta c (Y m) j z - BTheta.beltramiTheta c Yinf j z
            = BTheta.beltramiTheta c (Y m - Yinf) j z :=
          BTheta.beltramiTheta_sub_apply hn hα0 hα1 hρ hτpos hρτ hcsupp
            (fun j => lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Y m) j) (hYfin m))
            (hYvan m)
            (fun j => lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Yinf) j)
              (lt_top_iff_ne_top.mpr (BTheta.famNorm_ne_top (fun j => hYinf_fin j))))
            hYinf_van j z
        rw [hsub]
        have h1 : ENNReal.ofReal ‖BTheta.beltramiTheta c (Y m - Yinf) j z‖
            ≤ BTheta.famNorm α (BTheta.beltramiTheta c (Y m - Yinf)) :=
          (Work.CR.Flat.norm_apply_le_holderNorm 0 α
            (BTheta.beltramiTheta c (Y m - Yinf) j) Set.univ (Set.mem_univ z)).trans
            (BTheta.famNorm_apply_le (α := α) (BTheta.beltramiTheta c (Y m - Yinf)) j)
        have h2 : BTheta.famNorm α (BTheta.beltramiTheta c (Y m - Yinf))
            ≤ ENNReal.ofReal lam * BTheta.famNorm α (Y m - Yinf) :=
          hstep (Y m - Yinf) (fun j => lt_of_le_of_lt (BTheta.famNorm_apply_le (α := α) (Y m - Yinf) j)
            (lt_of_le_of_lt (BTheta.famNorm_sub_le (α := α) (Y m) Yinf)
              (ENNReal.add_lt_top.mpr ⟨hYfin m,
                lt_top_iff_ne_top.mpr (BTheta.famNorm_ne_top (fun j => hYinf_fin j))⟩)))
            (fun j z hz => by
              simp only [Pi.sub_apply, hYvan m j z hz, hYinf_van j z hz, sub_zero])
        have h3 : BTheta.famNorm α (BTheta.beltramiTheta c (Y m - Yinf))
            ≤ ENNReal.ofReal (lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) := by
          refine h2.trans ?_
          calc ENNReal.ofReal lam * BTheta.famNorm α (Y m - Yinf)
              ≤ ENNReal.ofReal lam * ENNReal.ofReal ((n : ℝ) * (s * (lam ^ m / (1 - lam)))) :=
                mul_le_mul_right (hfam_diff m) _
            _ = ENNReal.ofReal (lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) :=
                (ENNReal.ofReal_mul hlam0).symm
        have h4 : ENNReal.ofReal ‖BTheta.beltramiTheta c (Y m - Yinf) j z‖
            ≤ ENNReal.ofReal (lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) := h1.trans h3
        refine (ENNReal.ofReal_le_ofReal_iff ?_).mp h4
        positivity
      refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
      refine squeeze_zero (fun m => norm_nonneg _) hb ?_
      have h1 : Tendsto (fun m : ℕ => s * (lam ^ m / (1 - lam))) atTop (nhds 0) := htendlam
      have h2 : Tendsto (fun m : ℕ => lam * ((n : ℝ) * (s * (lam ^ m / (1 - lam))))) atTop
          (nhds (lam * ((n : ℝ) * 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.mul h1)
      simpa using h2
    have hconv2 : Tendsto (fun m => BTheta.beltramiTheta c (Y m) j z + S₀ j z) atTop
        (nhds (BTheta.beltramiTheta c Yinf j z + S₀ j z)) := hconvΦ.add tendsto_const_nhds
    refine tendsto_nhds_unique hconvY ?_
    refine hconv2.congr' (Eventually.of_forall fun m => ?_)
    simp only [Y_succ m, Pi.add_apply]
  refine ⟨fun j => G j + Yinf j, fun j => ?_, fun j => ?_, fun j z => ?_⟩
  · exact (hGcs j).add (BTheta.hasCompactSupport_of_vanishing_off_polydisc hn hρ (hYinf_van j))
  · refine lt_of_le_of_lt (BTheta.holderNorm_zero_add_le (G j) (Yinf j) Set.univ) ?_
    exact ENNReal.add_lt_top.mpr ⟨hGnorm j, hYinf_fin j⟩
  · have hadd : BTheta.beltramiTheta c (G + Yinf) j z
        = BTheta.beltramiTheta c G j z + BTheta.beltramiTheta c Yinf j z :=
      BTheta.beltramiTheta_add_apply hn hα0 hα1 hρ hτpos hρτ hcsupp hGsm hGcs hGnorm
        hYinf_fin hYinf_van j z
    have hS₀val : S₀ j z = BTheta.beltramiTheta c G j z := rfl
    calc G j z + Yinf j z
        = G j z + (BTheta.beltramiTheta c Yinf j z + S₀ j z) := by rw [hfeq j z]
      _ = (BTheta.beltramiTheta c G j z + BTheta.beltramiTheta c Yinf j z) + G j z := by
          rw [hS₀val]; ring
      _ = BTheta.beltramiTheta c (G + Yinf) j z + G j z := by rw [← hadd]

end Work.NN.Core
