import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.badArcAux
import Submission.Work.WilE3.Taylor.CaseII.crit_no_pos_near_zero
import Submission.Work.WilE3.Taylor.CaseII.radial_no_pos_near_sphere
import Submission.Work.WilE3.Taylor.CaseII.pert_lagrange_interior
import Submission.Work.WilE3.Taylor.CaseII.pert_lagrange_boundary
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfInteriorMin
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfBoundaryMin

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII, node (T3) `badArc_fixedBall`: **Steps A and B
  of the fixed-ball argument**.

  Minimise the perturbed squared gradient `G·exp⟨v, x - y⟩` over `{Φ = Φ xₙ} ∩ {∑(xᵢ-yᵢ)² ≤ δ²}`,
  where `xₙ` are bad points tending to `y`.  Because the exponential factor is bounded by
  `e^{±δ∑|vᵢ|}` on the Euclidean ball, the minimiser `uₙ` is again bad, with the constant
  `Cs = (e^{2δ∑|vᵢ|})^q`.  Lagrange's theorem at `uₙ` (in the interior, or on the sphere with
  independent constraint gradients) then puts `uₙ` either in the interior witness set
  (`IntWit`, pivots of `pertMinor`) or in the boundary witness set (`BndWit`, pivots of
  `pertMinor3` and the sphere), unless one of the two degenerate alternatives `DegWit` holds —
  which happen only finitely often, because an analytic arc carrying either of them would have `Φ`
  constant.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-! ## The setup lemma -/

/-- **Steps A and B.**  From the failure of the gradient inequality at `y` one obtains a sequence of
minimisers `uₙ` in the Euclidean ball, each bad with the fixed constant `Cs`, and each satisfying
one of the finitely many witness conditions (`CSet`) for all but finitely many `n`. -/
theorem badArc_setup {k r : ℕ} (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) {p q : ℕ}
    (hk : 0 < k)
    (hbad : ∀ ρ : ℝ, 0 < ρ → ∃ x : Fin k → ℝ, dist x y < ρ ∧ 0 < eaEval c Φ x ∧
      (∑ l : Fin k, (eaEval c (eaD c l Φ) x) ^ 2) ^ q < (eaEval c Φ x) ^ (2 * p))
    (hyΦ : eaEval c Φ y = 0) (v : Fin k → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (x u : ℕ → Fin k → ℝ) (Cs : ℝ), 0 < Cs ∧
      (∀ n, eaEval c Φ (u n) = eaEval c Φ (x n)) ∧
      Tendsto x atTop (𝓝 y) ∧
      (∀ n, (∑ i : Fin k, (u n i - y i) ^ 2) ≤ δ ^ 2) ∧
      (∀ n, 0 < eaEval c Φ (u n) ∧
        (∑ l : Fin k, (eaEval c (eaD c l Φ) (u n)) ^ 2) ^ q
          < Cs * (eaEval c Φ (u n)) ^ (2 * p)) ∧
      (∀ᶠ n : ℕ in atTop, ∃ a : CIdx k, u n ∈ CSet c Φ v y Cs δ p q a) := by
  classical
  -- ## notation
  set G : (Fin k → ℝ) → ℝ := fun z => ∑ l : Fin k, (eaEval c (eaD c l Φ) z) ^ 2 with hGdef
  set Lf : (Fin k → ℝ) → ℝ := fun z => ∑ i : Fin k, v i * (z i - y i) with hLdef
  set Fv : (Fin k → ℝ) → ℝ := fun z => G z * Real.exp (Lf z) with hFvdef
  set Esq : (Fin k → ℝ) → ℝ := fun z => ∑ i : Fin k, (z i - y i) ^ 2 with hEdef
  set L₀ : ℝ := δ * ∑ i : Fin k, |v i| with hL₀def
  set Cs : ℝ := (Real.exp (2 * L₀)) ^ q with hCdef
  have hCs_pos : 0 < Cs := by rw [hCdef]; exact pow_pos (Real.exp_pos _) _
  have hL₀_nonneg : 0 ≤ L₀ := by
    rw [hL₀def]
    exact mul_nonneg hδ.le (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hΦcont : Continuous (fun z : Fin k → ℝ => eaEval c Φ z) :=
    continuous_iff_continuousAt.mpr fun x => (eaEval_analytic c Φ x).continuousAt
  have hGcont : Continuous G := by
    rw [hGdef]
    exact continuous_iff_continuousAt.mpr fun x => (analyticAt_sqGradEval c Φ x).continuousAt
  have hEsqcont : Continuous Esq := by
    rw [hEdef]
    exact continuous_iff_continuousAt.mpr fun x => (analyticAt_sphereSq y x).continuousAt
  have hLcont : Continuous Lf := by
    rw [hLdef]
    exact continuous_iff_continuousAt.mpr fun x => (analyticAt_linForm v y x).continuousAt
  have hFvcont : Continuous Fv := by
    rw [hFvdef]; exact hGcont.mul (hLcont.rexp)
  have hGan : ∀ x : Fin k → ℝ, AnalyticAt ℝ G x := by
    intro x; rw [hGdef]; exact analyticAt_sqGradEval c Φ x
  have hLan : ∀ x : Fin k → ℝ, AnalyticAt ℝ Lf x := by
    intro x; rw [hLdef]; exact analyticAt_linForm v y x
  have hFvan : ∀ x : Fin k → ℝ, AnalyticAt ℝ Fv x := by
    intro x; rw [hFvdef]; exact (hGan x).mul (hLan x).rexp'
  -- ## Step 1: bad points inside the Euclidean ball
  have hx_ex : ∀ n : ℕ, ∃ x : Fin k → ℝ,
      dist x y < min (1 / ((n : ℝ) + 1)) (δ / (k : ℝ)) ∧
      0 < eaEval c Φ x ∧
      (∑ l : Fin k, (eaEval c (eaD c l Φ) x) ^ 2) ^ q < (eaEval c Φ x) ^ (2 * p) :=
    fun n => hbad _ (lt_min (by positivity) (div_pos hδ (by exact_mod_cast hk)))
  choose x hxd hxpos hxbad using hx_ex
  have hxtend : Tendsto x atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg)
      (fun n => le_of_lt (lt_of_lt_of_le (hxd n) (min_le_left _ _)))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hxE : ∀ n : ℕ, ∑ i : Fin k, (x n i - y i) ^ 2 ≤ δ ^ 2 := by
    intro n
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hcoord : ∀ i : Fin k, (x n i - y i) ^ 2 ≤ (δ / (k : ℝ)) ^ 2 := by
      intro i
      have h1 : |x n i - y i| ≤ dist (x n) y := by
        have h := norm_le_pi_norm (x n - y) i
        rw [Real.norm_eq_abs] at h
        simpa [dist_eq_norm, Pi.sub_apply] using h
      have h2 : |x n i - y i| < δ / (k : ℝ) :=
        lt_of_le_of_lt h1 (lt_of_lt_of_le (hxd n) (min_le_right _ _))
      calc (x n i - y i) ^ 2 = |x n i - y i| ^ 2 := (sq_abs _).symm
        _ ≤ (δ / (k : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2.le 2
    calc ∑ i : Fin k, (x n i - y i) ^ 2 ≤ ∑ _i : Fin k, (δ / (k : ℝ)) ^ 2 :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (k : ℝ) * (δ / (k : ℝ)) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = δ ^ 2 / (k : ℝ) := by field_simp
      _ ≤ δ ^ 2 := by
          rw [div_le_iff₀ hkpos]
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          nlinarith [sq_nonneg δ, hk1]
  -- ## Step 2: the minimisers
  have hmin_ex : ∀ n : ℕ, ∃ u : Fin k → ℝ,
      (∑ i : Fin k, (u i - y i) ^ 2 ≤ δ ^ 2) ∧ eaEval c Φ u = eaEval c Φ (x n) ∧
      ∀ z : Fin k → ℝ, (∑ i : Fin k, (z i - y i) ^ 2 ≤ δ ^ 2) →
        eaEval c Φ z = eaEval c Φ (x n) → Fv u ≤ Fv z := by
    intro n
    set S : Set (Fin k → ℝ) :=
      {z : Fin k → ℝ | (∑ i : Fin k, (z i - y i) ^ 2 ≤ δ ^ 2) ∧
        eaEval c Φ z = eaEval c Φ (x n)} with hS
    have hSclosed : IsClosed S := by
      rw [hS]
      exact (isClosed_le hEsqcont continuous_const).inter (isClosed_eq hΦcont continuous_const)
    have hScpt : IsCompact S := by
      refine (isCompact_closedBall y δ).of_isClosed_subset hSclosed ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖z - y‖ ≤ Real.sqrt (∑ i : Fin k, (z i - y i) ^ 2) := by
        simpa [Pi.sub_apply] using Work.WilE3.Taylor.Grad.norm_le_sqrt_sumSq (z - y)
      have h2 : Real.sqrt (∑ i : Fin k, (z i - y i) ^ 2) ≤ δ := by
        rw [← Real.sqrt_sq hδ.le]
        exact Real.sqrt_le_sqrt hz.1
      linarith
    have hne : S.Nonempty := ⟨x n, hxE n, rfl⟩
    obtain ⟨u, huS, hu⟩ := hScpt.exists_isMinOn hne hFvcont.continuousOn
    exact ⟨u, huS.1, huS.2, fun z hz1 hz2 => (isMinOn_iff.mp hu) z ⟨hz1, hz2⟩⟩
  choose u huBall huLev huMin using hmin_ex
  -- ## Step 3: the badness transfers to the minimisers
  have hLbound : ∀ z : Fin k → ℝ, (∑ i : Fin k, (z i - y i) ^ 2 ≤ δ ^ 2) → |Lf z| ≤ L₀ := by
    intro z hz
    have hcoord : ∀ i : Fin k, |z i - y i| ≤ δ := by
      intro i
      have h1 : (z i - y i) ^ 2 ≤ δ ^ 2 :=
        le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (z j - y j)) (Finset.mem_univ i)) hz
      calc |z i - y i| = Real.sqrt ((z i - y i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt h1
        _ = δ := Real.sqrt_sq hδ.le
    have h1 : Lf z = ∑ i : Fin k, v i * (z i - y i) := by rw [hLdef]
    rw [h1]
    calc |∑ i : Fin k, v i * (z i - y i)| ≤ ∑ i : Fin k, |v i * (z i - y i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin k, |v i| * |z i - y i| := by
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i : Fin k, |v i| * δ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
      _ = L₀ := by
          rw [hL₀def, ← Finset.sum_mul]
          ring
  have hG_le : ∀ n : ℕ, G (u n) ≤ G (x n) * Real.exp (2 * L₀) := by
    intro n
    have h1 : Fv (u n) ≤ Fv (x n) := huMin n (x n) (hxE n) rfl
    have h2 : G (u n) * Real.exp (Lf (u n)) ≤ G (x n) * Real.exp (Lf (x n)) := by
      rw [hFvdef] at h1
      simpa [hFvdef] using h1
    have hxL : |Lf (x n)| ≤ L₀ := hLbound (x n) (hxE n)
    have huL : |Lf (u n)| ≤ L₀ := hLbound (u n) (huBall n)
    have h3 : Real.exp (Lf (x n) - Lf (u n)) ≤ Real.exp (2 * L₀) := by
      apply Real.exp_le_exp.mpr
      have := neg_abs_le (Lf (u n))
      linarith [abs_le.mp hxL, abs_le.mp huL]
    have h4 : G (u n) ≤ G (x n) * Real.exp (Lf (x n) - Lf (u n)) := by
      have he : (0 : ℝ) < Real.exp (Lf (u n)) := Real.exp_pos _
      rw [Real.exp_sub, ← mul_div_assoc]
      exact (le_div_iff₀ he).mpr h2
    exact le_trans h4 (mul_le_mul_of_nonneg_left h3 (by
      rw [hGdef]; exact Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hbad_u : ∀ n : ℕ, 0 < eaEval c Φ (u n) ∧
      (∑ l : Fin k, (eaEval c (eaD c l Φ) (u n)) ^ 2) ^ q < Cs * (eaEval c Φ (u n)) ^ (2 * p) := by
    intro n
    have hpos : 0 < eaEval c Φ (u n) := by rw [huLev n]; exact hxpos n
    refine ⟨hpos, ?_⟩
    have hGnn : 0 ≤ G (u n) := by rw [hGdef]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have h1 : (G (u n)) ^ q ≤ (G (x n) * Real.exp (2 * L₀)) ^ q :=
      pow_le_pow_left₀ hGnn (hG_le n) q
    have h2 : (G (x n) * Real.exp (2 * L₀)) ^ q = (G (x n)) ^ q * Cs := by
      rw [mul_pow, hCdef]
    have h3 : (G (x n)) ^ q < (eaEval c Φ (x n)) ^ (2 * p) := by
      rw [hGdef]; exact hxbad n
    have h4 : (eaEval c Φ (x n)) ^ (2 * p) = (eaEval c Φ (u n)) ^ (2 * p) := by rw [huLev n]
    have hGxnn : 0 ≤ (G (x n)) ^ q := by
      rw [hGdef]; exact pow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _
    calc (∑ l : Fin k, (eaEval c (eaD c l Φ) (u n)) ^ 2) ^ q = (G (u n)) ^ q := by rw [hGdef]
      _ ≤ (G (x n)) ^ q * Cs := by rw [← h2]; exact h1
      _ < (eaEval c Φ (u n)) ^ (2 * p) * Cs := by
          rw [← h4]
          exact mul_lt_mul_of_pos_right h3 hCs_pos
      _ = Cs * (eaEval c Φ (u n)) ^ (2 * p) := by ring
  -- ## Step 4: classification at every minimiser
  have hclass : ∀ n : ℕ, (∃ a : CIdx k, u n ∈ CSet c Φ v y Cs δ p q a) ∨
      DegWit c Φ y δ (u n) := by
    intro n
    by_cases hcrit : (∀ l : Fin k, eaEval c (eaD c l Φ) (u n) = 0)
    · exact Or.inr (Or.inl hcrit)
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin k, eaEval c (eaD c i₀ Φ) (u n) ≠ 0 := by
        by_contra hcon
        exact hcrit (fun l => by
          by_contra hl
          exact hcon ⟨l, hl⟩)
      have hgu : Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) (u n) ≠ 0 := by
        intro h
        have h1 : Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) (u n) i₀ = 0 := by
          rw [h]; rfl
        rw [Work.Taylor.Grad.grad_eaEval] at h1
        exact hi₀ h1
      rcases lt_trichotomy (∑ i : Fin k, (u n i - y i) ^ 2) (δ ^ 2) with hlt | heq | hgt
      · -- ### interior case
        have hsum_u : (∑ l : Fin k,
            (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) (u n) l) ^ 2) = G (u n) := by
          rw [hGdef]
          exact Finset.sum_congr rfl fun l _ => by rw [Work.Taylor.Grad.grad_eaEval]
        have hloc : ∀ᶠ z in nhds (u n), (fun w : Fin k → ℝ => eaEval c Φ w) z = eaEval c Φ (u n) →
            (∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) (u n) l) ^ 2)
                * Real.exp (∑ i : Fin k, v i * (u n i - y i))
              ≤ (∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) z l) ^ 2)
                * Real.exp (∑ i : Fin k, v i * (z i - y i)) := by
          have hev : ∀ᶠ z in nhds (u n), (∑ i : Fin k, (z i - y i) ^ 2) < δ ^ 2 :=
            (isOpen_lt hEsqcont continuous_const).mem_nhds hlt
          filter_upwards [hev] with z hzE hzΦ
          have hzlev : eaEval c Φ z = eaEval c Φ (x n) := by rw [hzΦ, huLev n]
          have hmain := huMin n z hzE.le hzlev
          simp only [hFvdef] at hmain
          have e2 : (∑ l : Fin k,
              (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) z l) ^ 2) = G z := by
            rw [hGdef]
            exact Finset.sum_congr rfl fun l _ => by rw [Work.Taylor.Grad.grad_eaEval]
          have e3 : Real.exp (∑ i : Fin k, v i * (z i - y i)) = Real.exp (Lf z) := by rw [hLdef]
          have e4 : Real.exp (∑ i : Fin k, v i * (u n i - y i)) = Real.exp (Lf (u n)) := by
            rw [hLdef]
          rw [hsum_u, e2, e3, e4]
          exact hmain
        obtain ⟨cc, hcc⟩ :=
          pert_lagrange_interior (fun z => eaEval_analytic c Φ z) hgu hloc
        have hcc' : ∀ i : Fin k,
            eaEval c (eaD c i (sqGrad c Φ)) (u n) + v i * eaEval c (sqGrad c Φ) (u n)
              = cc * eaEval c (eaD c i Φ) (u n) := by
          intro i
          have h := hcc i
          rw [grad_grad_sumSq, sum_grad_sq_eq, Work.Taylor.Grad.grad_eaEval] at h
          rw [mul_comm (v i)]
          exact h
        refine Or.inl ⟨Sum.inl i₀, ?_⟩
        exact ⟨(hbad_u n).1, (hbad_u n).2, hi₀,
          fun i _ => pertMinor_eq_zero_of_lagrange c Φ v i₀ (u n) cc hcc' i⟩
      · -- ### boundary case
        by_cases hind : ∃ i j : Fin k, muP c Φ y i j (u n) ≠ 0
        · obtain ⟨i₁, j₁, hij⟩ := hind
          have hijne : i₁ ≠ j₁ := by
            intro h
            exact hij (by rw [h, muP_self])
          have hindep : ∃ i j : Fin k,
              Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) (u n) i
                  * (u n j - y j)
                - Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) (u n) j
                  * (u n i - y i) ≠ 0 := by
            refine ⟨i₁, j₁, ?_⟩
            rw [Work.Taylor.Grad.grad_eaEval, Work.Taylor.Grad.grad_eaEval]
            exact hij
          have hsum_u : (∑ l : Fin k,
              (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) (u n) l) ^ 2)
              = G (u n) := by
            rw [hGdef]
            exact Finset.sum_congr rfl fun l _ => by rw [Work.Taylor.Grad.grad_eaEval]
          have hloc : ∀ᶠ z in nhds (u n), (fun w : Fin k → ℝ => eaEval c Φ w) z
                = eaEval c Φ (u n) →
              (∑ i : Fin k, (z i - y i) ^ 2) = (∑ i : Fin k, (u n i - y i) ^ 2) →
              (∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) (u n) l) ^ 2)
                  * Real.exp (∑ i : Fin k, v i * (u n i - y i))
                ≤ (∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) z l) ^ 2)
                  * Real.exp (∑ i : Fin k, v i * (z i - y i)) := by
            filter_upwards with z hzΦ hzE
            have hzlev : eaEval c Φ z = eaEval c Φ (x n) := by rw [hzΦ, huLev n]
            have hzle : (∑ i : Fin k, (z i - y i) ^ 2) ≤ δ ^ 2 := by rw [hzE, heq]
            have hmain := huMin n z hzle hzlev
            simp only [hFvdef] at hmain
            have e2 : (∑ l : Fin k,
                (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) z l) ^ 2) = G z := by
              rw [hGdef]
              exact Finset.sum_congr rfl fun l _ => by rw [Work.Taylor.Grad.grad_eaEval]
            have e3 : Real.exp (∑ i : Fin k, v i * (z i - y i)) = Real.exp (Lf z) := by rw [hLdef]
            have e4 : Real.exp (∑ i : Fin k, v i * (u n i - y i)) = Real.exp (Lf (u n)) := by
              rw [hLdef]
            rw [hsum_u, e2, e3, e4]
            exact hmain
          obtain ⟨a, b, hab⟩ :=
            pert_lagrange_boundary (fun z => eaEval_analytic c Φ z) hindep hloc
          have hab' : ∀ i : Fin k,
              eaEval c (eaD c i (sqGrad c Φ)) (u n) + v i * eaEval c (sqGrad c Φ) (u n)
                = a * eaEval c (eaD c i Φ) (u n) + b * (u n i - y i) := by
            intro i
            have h := hab i
            rw [grad_grad_sumSq, sum_grad_sq_eq, Work.Taylor.Grad.grad_eaEval] at h
            rw [mul_comm (v i)]
            exact h
          refine Or.inl ⟨Sum.inr ⟨(i₁, j₁), hijne⟩, ?_⟩
          exact ⟨(hbad_u n).1, (hbad_u n).2, heq, hijne, hij,
            fun l hl1 hl2 => pertMinor3_eq_zero_of_combo c Φ v y i₁ j₁ (u n) a b hab' l⟩
        · have hmu0 : ∀ i j : Fin k, muP c Φ y i j (u n) = 0 := by
            intro i j
            by_contra hcon
            exact hind ⟨i, j, hcon⟩
          exact Or.inr (Or.inr ⟨heq, fun i j => by
            have := hmu0 i j
            simpa only [muP] using this⟩)
      · -- impossible: `∑ (uₙ - y)² ≤ δ²`
        exact absurd (huBall n) (not_le.mpr hgt)
  -- ## Step 5: the degenerate alternatives occur only finitely often
  have hnotdeg : ∀ᶠ n : ℕ in atTop, ¬ DegWit c Φ y δ (u n) := by
    rw [← not_frequently]
    intro hfreq
    rcases frequently_or_distrib.mp hfreq with hA | hB
    · -- `∇Φ (u n) = 0` infinitely often
      obtain ⟨φ, hφmono, hφP⟩ := extraction_of_frequently_atTop hA
      have hball : ∀ n : ℕ, u (φ n) ∈ Metric.closedBall y δ := fun n => by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : ‖u (φ n) - y‖ ≤ Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) := by
          simpa [Pi.sub_apply] using Work.WilE3.Taylor.Grad.norm_le_sqrt_sumSq (u (φ n) - y)
        have h2 : Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) ≤ δ := by
          rw [← Real.sqrt_sq hδ.le]
          exact Real.sqrt_le_sqrt (huBall (φ n))
        linarith
      obtain ⟨a, -, ψ, hψmono, htend⟩ := (isCompact_closedBall y δ).tendsto_subseq hball
      set χ : ℕ → ℕ := fun n => φ (ψ n) with hχdef
      have hχmono : StrictMono χ := hφmono.comp hψmono
      have hχP : ∀ n : ℕ, ∀ l : Fin k, eaEval c (eaD c l Φ) (u (χ n)) = 0 :=
        fun n l => hφP (ψ n) l
      have hχtend : Tendsto (fun n : ℕ => u (χ n)) atTop (𝓝 a) := htend
      have hΦa : eaEval c Φ a = 0 := by
        have h1 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 (eaEval c Φ a)) :=
          (hΦcont.tendsto a).comp hχtend
        have h2 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 0) := by
          have heq' : (fun n : ℕ => eaEval c Φ (u (χ n))) = fun n => eaEval c Φ (x (χ n)) := by
            funext n; rw [huLev (χ n)]
          rw [heq']
          have h3 : Tendsto (fun n : ℕ => x (χ n)) atTop (𝓝 y) :=
            hxtend.comp hχmono.tendsto_atTop
          have h4 : Tendsto (fun n : ℕ => eaEval c Φ (x (χ n))) atTop (𝓝 (eaEval c Φ y)) :=
            (hΦcont.tendsto y).comp h3
          rw [hyΦ] at h4
          exact h4
        exact tendsto_nhds_unique h1 h2
      obtain ⟨ρ, hρpos, hρ⟩ := crit_no_pos_near_zero (fun z => eaEval_analytic c Φ z) hΦa
      have hev : ∀ᶠ n : ℕ in atTop, dist (u (χ n)) a < ρ :=
        hχtend.eventually (Metric.ball_mem_nhds a hρpos)
      obtain ⟨n, hn⟩ := hev.exists
      have hfd : fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) (u (χ n)) = 0 := by
        rw [← grad_eq_zero_iff]
        funext l
        rw [Work.Taylor.Grad.grad_eaEval]
        exact hχP n l
      have hle := hρ (u (χ n)) hn hfd
      have hpos : 0 < eaEval c Φ (u (χ n)) := by rw [huLev (χ n)]; exact hxpos (χ n)
      linarith
    · -- `∇Φ ∥ (u n - y)` on the sphere infinitely often
      obtain ⟨φ, hφmono, hφP⟩ := extraction_of_frequently_atTop hB
      have hball : ∀ n : ℕ, u (φ n) ∈ Metric.closedBall y δ := fun n => by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : ‖u (φ n) - y‖ ≤ Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) := by
          simpa [Pi.sub_apply] using Work.WilE3.Taylor.Grad.norm_le_sqrt_sumSq (u (φ n) - y)
        have h2 : Real.sqrt (∑ i : Fin k, (u (φ n) i - y i) ^ 2) ≤ δ := by
          rw [← Real.sqrt_sq hδ.le]
          exact Real.sqrt_le_sqrt (huBall (φ n))
        linarith
      obtain ⟨a, -, ψ, hψmono, htend⟩ := (isCompact_closedBall y δ).tendsto_subseq hball
      set χ : ℕ → ℕ := fun n => φ (ψ n) with hχdef
      have hχmono : StrictMono χ := hφmono.comp hψmono
      have hχP : ∀ n : ℕ, ((∑ i : Fin k, (u (χ n) i - y i) ^ 2) = δ ^ 2) ∧
          ∀ i j : Fin k, muP c Φ y i j (u (χ n)) = 0 := fun n => hφP (ψ n)
      have hχtend : Tendsto (fun n : ℕ => u (χ n)) atTop (𝓝 a) := htend
      have hΦa : eaEval c Φ a = 0 := by
        have h1 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 (eaEval c Φ a)) :=
          (hΦcont.tendsto a).comp hχtend
        have h2 : Tendsto (fun n : ℕ => eaEval c Φ (u (χ n))) atTop (𝓝 0) := by
          have heq' : (fun n : ℕ => eaEval c Φ (u (χ n))) = fun n => eaEval c Φ (x (χ n)) := by
            funext n; rw [huLev (χ n)]
          rw [heq']
          have h3 : Tendsto (fun n : ℕ => x (χ n)) atTop (𝓝 y) :=
            hxtend.comp hχmono.tendsto_atTop
          have h4 : Tendsto (fun n : ℕ => eaEval c Φ (x (χ n))) atTop (𝓝 (eaEval c Φ y)) :=
            (hΦcont.tendsto y).comp h3
          rw [hyΦ] at h4
          exact h4
        exact tendsto_nhds_unique h1 h2
      have hsphere_a : ∑ i : Fin k, (a i - y i) ^ 2 = δ ^ 2 := by
        have h1 : Tendsto (fun n : ℕ => ∑ i : Fin k, (u (χ n) i - y i) ^ 2) atTop
            (𝓝 (∑ i : Fin k, (a i - y i) ^ 2)) :=
          (hEsqcont.tendsto a).comp hχtend
        have h2 : Tendsto (fun n : ℕ => ∑ i : Fin k, (u (χ n) i - y i) ^ 2) atTop (𝓝 (δ ^ 2)) := by
          have heq' : (fun n : ℕ => ∑ i : Fin k, (u (χ n) i - y i) ^ 2) = fun _ => δ ^ 2 := by
            funext n; exact (hχP n).1
          rw [heq']; exact tendsto_const_nhds
        exact tendsto_nhds_unique h1 h2
      have hmins_a : ∀ i j : Fin k,
          fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) a (Pi.single i 1) * (a j - y j)
            - fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) a (Pi.single j 1) * (a i - y i) = 0 := by
        intro i j
        have h1 : Tendsto (fun n : ℕ => muP c Φ y i j (u (χ n))) atTop (𝓝 (muP c Φ y i j a)) :=
          (continuous_muP c Φ y i j).tendsto a |>.comp hχtend
        have h2 : Tendsto (fun n : ℕ => muP c Φ y i j (u (χ n))) atTop (𝓝 0) := by
          have heq' : (fun n : ℕ => muP c Φ y i j (u (χ n))) = fun _ => 0 := by
            funext n; exact (hχP n).2 i j
          rw [heq']; exact tendsto_const_nhds
        have h3 : muP c Φ y i j a = 0 := tendsto_nhds_unique h1 h2
        simp only [muP] at h3
        change Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) a i * (a j - y j)
          - Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) a j * (a i - y i) = 0
        rw [Work.Taylor.Grad.grad_eaEval, Work.Taylor.Grad.grad_eaEval]
        exact h3
      obtain ⟨ρ, hρpos, hρ⟩ :=
        radial_no_pos_near_sphere (fun z => eaEval_analytic c Φ z) hΦa hsphere_a
      have hev : ∀ᶠ n : ℕ in atTop, dist (u (χ n)) a < ρ :=
        hχtend.eventually (Metric.ball_mem_nhds a hρpos)
      obtain ⟨n, hn⟩ := hev.exists
      have hmin' : ∀ i j : Fin k,
          fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) (u (χ n)) (Pi.single i 1)
              * (u (χ n) j - y j)
            - fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) (u (χ n)) (Pi.single j 1)
              * (u (χ n) i - y i) = 0 := by
        intro i j
        have h := (hχP n).2 i j
        simp only [muP] at h
        change Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) (u (χ n)) i
            * (u (χ n) j - y j)
          - Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) (u (χ n)) j
            * (u (χ n) i - y i) = 0
        rw [Work.Taylor.Grad.grad_eaEval, Work.Taylor.Grad.grad_eaEval]
        exact h
      have hle := hρ (u (χ n)) hn (hχP n).1 hmin'
      have hpos : 0 < eaEval c Φ (u (χ n)) := by rw [huLev (χ n)]; exact hxpos (χ n)
      linarith
  refine ⟨x, u, Cs, hCs_pos, huLev, hxtend, huBall, hbad_u, ?_⟩
  filter_upwards [hnotdeg] with n hn
  rcases hclass n with h | h
  · exact h
  · exact absurd h hn

end Work.WilE3.Taylor.CaseII
