import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Commons.Analysis.Integration.integral_mul_sq_le
import Submission.Work.GM.Energy.EnergyCore.triple_sum_integral_le

namespace Work.GM.Energy.EnergyCore2

open Complex Finset MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable def quadSet (W : Finset ℝ) : Finset (ℝ × ℝ × ℝ × ℝ) :=
  (W ×ˢ W ×ˢ W ×ˢ W).filter (fun q : ℝ × ℝ × ℝ × ℝ => |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1)

lemma quadSet_card (W : Finset ℝ) : (quadSet W).card = Submission.GM.energy W := rfl

/-- Reindexing the quadruple set as an iterated sum, with the last variable restricted by the
`1`-separation condition `|t₁+t₂-t₃-t₄| ≤ 1`. -/
lemma sum_quadSet {M : Type*} [AddCommMonoid M] (W : Finset ℝ) (G : ℝ × ℝ × ℝ × ℝ → M) :
    (∑ q ∈ quadSet W, G q) =
      ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ∑ t4 ∈ W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1), G (t1, t2, t3, t4) := by
  classical
  simp only [quadSet, Finset.sum_filter, Finset.sum_product]

lemma mem_quadSet {W : Finset ℝ} {q : ℝ × ℝ × ℝ × ℝ} :
    q ∈ quadSet W ↔ q.1 ∈ W ∧ q.2.1 ∈ W ∧ q.2.2.1 ∈ W ∧ q.2.2.2 ∈ W
      ∧ |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1 := by
  simp only [quadSet, Finset.mem_filter, Finset.mem_product, and_assoc]

private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  rw [abs_lt]
  constructor
  · have hle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [← h] at hlt
    linarith
  · have hle : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    rw [h] at hlt
    linarith

private lemma card_le_three_of_sep {A : Finset ℝ} (hA : ∀ x ∈ A, 0 ≤ x ∧ x ≤ 2)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|) : A.card ≤ 3 := by
  classical
  have hinj : Set.InjOn (fun x : ℝ => (⌊x⌋ : ℤ)) (A : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hsep' : 1 ≤ |x - y| := hsep x hx y hy hne
    have hlt : |x - y| < 1 := abs_sub_lt_one_of_floor_eq hxy
    linarith
  have hcard : A.card = (A.image (fun x => (⌊x⌋ : ℤ))).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : A.image (fun x => (⌊x⌋ : ℤ)) ⊆ Finset.Icc (0:ℤ) 2 := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    simp only [Finset.mem_Icc]
    constructor
    · exact Int.floor_nonneg.mpr (hA x hx).1
    · have h3 : x < ((3:ℤ) : ℝ) := by
        push_cast
        linarith [(hA x hx).2]
      have := (Int.floor_lt).mpr h3
      omega
  calc A.card = (A.image (fun x => (⌊x⌋ : ℤ))).card := hcard
    _ ≤ (Finset.Icc (0:ℤ) 2).card := Finset.card_le_card hsub
    _ = 3 := by decide

/-- A `1`-separated finite set of reals meets any interval `[c-1,c+1]` of length `2` in at most
`3` points. -/
lemma card_filter_le_three {W : Finset ℝ} (hsep : Submission.GM.Separated W 1) (c : ℝ) :
    (W.filter (fun t => |c - t| ≤ 1)).card ≤ 3 := by
  classical
  set S : Finset ℝ := W.filter (fun t => |c - t| ≤ 1) with hSdef
  have hsub : S ⊆ W := by rw [hSdef]; exact Finset.filter_subset _ _
  have hsepS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (hsub hx) y (hsub hy) hxy
  have hshift_inj : ∀ x ∈ S, ∀ y ∈ S, x - (c - 1) = y - (c - 1) → x = y := by
    intro x _ y _ h; linarith
  have hcardimg : (S.image (fun t => t - (c-1))).card = S.card :=
    Finset.card_image_of_injOn hshift_inj
  have hA : ∀ x ∈ S.image (fun t => t - (c-1)), 0 ≤ x ∧ x ≤ 2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    have ht' : t ∈ W ∧ |c - t| ≤ 1 := by rw [hSdef, Finset.mem_filter] at ht; exact ht
    have h := ht'.2
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hsepS' : ∀ x ∈ S.image (fun t => t - (c-1)), ∀ y ∈ S.image (fun t => t - (c-1)),
      x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by intro h; exact hxy (by rw [h])
    have heq : (a - (c-1)) - (b - (c-1)) = a - b := by ring
    rw [heq]
    exact hsepS a ha b hb hab
  have hthis : (S.image (fun t => t - (c-1))).card ≤ 3 := card_le_three_of_sep hA hsepS'
  rw [hcardimg] at hthis
  exact hthis

/-- Cauchy–Schwarz for interval integrals: `(∫_a^b f)² ≤ (b-a) ∫_a^b f²` for `f ≥ 0`. -/
lemma sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ u in a..b, f u) ^ 2 ≤ (b - a) * ∫ u in a..b, f u ^ 2 := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hfint : Integrable f (volume.restrict (Set.Ioc a b)) := by
    have h := (hf.intervalIntegrable (μ := volume) a b).def'
    rwa [Set.uIoc_of_le hab] at h
  have h2int : Integrable (fun x => f x ^ 2) (volume.restrict (Set.Ioc a b)) := by
    have h := ((hf.pow 2).intervalIntegrable (μ := volume) a b).def'
    rwa [Set.uIoc_of_le hab] at h
  have h3int : Integrable (fun x => (1:ℝ) ^ 2) (volume.restrict (Set.Ioc a b)) :=
    integrable_const _
  have hcs := Commons.Analysis.Integration.integral_mul_sq_le_of_integrable (u := f)
      (v := fun _ => (1:ℝ)) (by simpa using hfint) h2int h3int
  have hconst : ∫ x, (1:ℝ) ∂(volume.restrict (Set.Ioc a b)) = b - a := by
    rw [MeasureTheory.integral_const]
    have hvol : (volume.restrict (Set.Ioc a b)) Set.univ = ENNReal.ofReal (b - a) := by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    simp only [Measure.real, hvol, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a),
      smul_eq_mul, mul_one]
  simp only [mul_one, one_pow, hconst] at hcs
  rwa [mul_comm] at hcs

private lemma sq_add_le_two_mul_sq_add (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

private lemma continuous_cpow_I_mul' {x : ℝ} (hx : 0 < x) :
    Continuous fun u : ℝ => (x : ℂ) ^ (Complex.I * (u : ℂ)) := by
  have h : ∀ u : ℝ, (x : ℂ) ^ (Complex.I * (u : ℂ))
      = Complex.exp (((u * Real.log x : ℝ)) * Complex.I) := by
    intro u
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
    congr 1
    push_cast
    ring
  rw [show (fun u : ℝ => (x : ℂ) ^ (Complex.I * (u : ℂ)))
      = fun u => Complex.exp (((u * Real.log x : ℝ)) * Complex.I) from funext h]
  fun_prop

lemma continuous_smoothedPoly (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) :
    Continuous fun t : ℝ => Submission.LargeValues.smoothedPoly N b t := by
  unfold Submission.LargeValues.smoothedPoly
  refine continuous_finset_sum _ fun n hn => ?_
  have hn1 : (0 : ℝ) < (n : ℝ) := by
    have h1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
    exact_mod_cast h1
  exact Continuous.mul (Continuous.mul continuous_const continuous_const)
    (continuous_cpow_I_mul' hn1)

/-- **GM Lemma 11.4** (energy controlled by the discrete third moment), taking the locality
Lemma 11.3 as a hypothesis with constant `Cloc`:
`E(W) ≤ C K² V⁻² Σ_{n₁,n₂∈[N,2N]} ‖R(n₁/n₂)‖³ + C (N/K^m)² V⁻² E(W)`.

This is a *port* of the already-proved
`Submission/Work/GM/Energy/EnergyCore/energy_le_R_cube.lean` into a fresh namespace: that file
defines `Work.GM.Energy.EnergyCore.quadSet`, which clashes with
`Submission/Work/GM/Energy/EnergyCore/FourthMomentDefs.lean` (also `quadSet`), so the two cannot
be imported together. Copy the existing proof and rename the local helpers (do NOT import the
original module). -/
theorem energy_le_R_cube (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Cloc : ℝ), 0 < Cloc →
      ∀ (N : ℕ), 1 ≤ N → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) → Submission.GM.Separated W 1 →
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      (∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖Submission.LargeValues.smoothedPoly N b t‖ ≤
          Cloc * (∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖)
            + Cloc / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖)) →
      ∀ (V K : ℝ), 1 ≤ K → 0 < V →
        (∀ t ∈ W, V ≤ ‖Submission.LargeValues.smoothedPoly N b t‖) →
        (Submission.GM.energy W : ℝ) ≤
          C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 / V ^ 2 *
              (∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
                ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
          + C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 / V ^ 2
              * (Submission.GM.energy W) := by
  obtain ⟨Cw₀, hCw₀nn, hCw₀bd⟩ := Submission.LargeValues.bumpW_deriv_bdd 0
  set Cw : ℝ := max Cw₀ 1 with hCwdef
  have hCwnn : 0 ≤ Cw := le_trans hCw₀nn (le_max_left _ _)
  have hCwbd : ∀ x, |Submission.LargeValues.bumpW x| ≤ Cw :=
    fun x => le_trans (hCw₀bd x) (le_max_left _ _)
  refine ⟨24 * Cw ^ 2 + 2, by positivity, ?_⟩
  set C : ℝ := 24 * Cw ^ 2 + 2 with hCdef
  have hCge : 24 * Cw ^ 2 ≤ C := by rw [hCdef]; linarith
  have hCge2 : 2 ≤ C := by rw [hCdef]; nlinarith [sq_nonneg Cw]
  intro Cloc hCloc N hN W hWsub hsep b hb hloc V K hK hV hbig
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hV2pos : 0 < V ^ 2 := by positivity
  have hKmpos : 0 < K ^ (m : ℝ) := Real.rpow_pos_of_pos hKpos (m : ℝ)
  set S : ℝ := ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ with hSdef
  set Y : ℝ := ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
      ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 with hYdef
  set E : ℝ := (Submission.GM.energy W : ℝ) with hEdef
  have hEcard : ((quadSet W).card : ℝ) = E := by rw [quadSet_card, ← hEdef]
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hClocK : 0 ≤ Cloc / K ^ (m : ℝ) := div_nonneg hCloc.le hKmpos.le
  -- ### Step 1
  have hstep1 : E ≤ (∑ q ∈ quadSet W,
      ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2) / V ^ 2 := by
    rw [← hEcard]
    have h1 : ((quadSet W).card : ℝ) = ∑ q ∈ quadSet W, (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones]; push_cast; rfl
    rw [h1, Finset.sum_div]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq4 : q.2.2.2 ∈ W := (mem_quadSet.mp hq).2.2.2.1
    have hbq := hbig q.2.2.2 hq4
    have hsq : V ^ 2 ≤ ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2 :=
      sq_le_sq.mpr (by rw [abs_of_pos hV, abs_of_nonneg (norm_nonneg _)]; exact hbq)
    calc (1 : ℝ) = V ^ 2 / V ^ 2 := by rw [div_self (ne_of_gt hV2pos)]
      _ ≤ ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2 / V ^ 2 :=
          div_le_div_of_nonneg_right hsq hV2pos.le
  -- ### Step 2
  have hstep2 : ∑ q ∈ quadSet W,
      ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2 ≤
      2 * Cloc ^ 2 * (∑ q ∈ quadSet W,
        (∫ u in q.2.2.2 - K..q.2.2.2 + K,
          ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2)
      + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E := by
    have hpt : ∀ q ∈ quadSet W,
        ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2 ≤
          2 * Cloc ^ 2 * (∫ u in q.2.2.2 - K..q.2.2.2 + K,
            ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2
            + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 := by
      intro q hq
      have hq4 : q.2.2.2 ∈ W := (mem_quadSet.mp hq).2.2.2.1
      have hlocq := hloc K hK q.2.2.2
      have hI0 : 0 ≤ ∫ u in q.2.2.2 - K..q.2.2.2 + K,
          ‖Submission.LargeValues.smoothedPoly N b u‖ :=
        intervalIntegral.integral_nonneg (by linarith) fun u _ => norm_nonneg _
      have hrhs0 : 0 ≤ Cloc * (∫ u in q.2.2.2 - K..q.2.2.2 + K,
            ‖Submission.LargeValues.smoothedPoly N b u‖)
          + Cloc / K ^ (m : ℝ) * S :=
        add_nonneg (mul_nonneg hCloc.le hI0) (mul_nonneg hClocK hS0)
      calc ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2
          ≤ (Cloc * (∫ u in q.2.2.2 - K..q.2.2.2 + K,
                ‖Submission.LargeValues.smoothedPoly N b u‖)
              + Cloc / K ^ (m : ℝ) * S) ^ 2 :=
            sq_le_sq.mpr (by
              rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs0]
              exact hlocq)
        _ ≤ 2 * (Cloc * (∫ u in q.2.2.2 - K..q.2.2.2 + K,
                ‖Submission.LargeValues.smoothedPoly N b u‖)) ^ 2
              + 2 * (Cloc / K ^ (m : ℝ) * S) ^ 2 := sq_add_le_two_mul_sq_add _ _
        _ = 2 * Cloc ^ 2 * (∫ u in q.2.2.2 - K..q.2.2.2 + K,
                ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2
              + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 := by ring
    calc ∑ q ∈ quadSet W, ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2
        ≤ ∑ q ∈ quadSet W, (2 * Cloc ^ 2 * (∫ u in q.2.2.2 - K..q.2.2.2 + K,
              ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2
            + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2) := Finset.sum_le_sum hpt
      _ = 2 * Cloc ^ 2 * (∑ q ∈ quadSet W,
              (∫ u in q.2.2.2 - K..q.2.2.2 + K,
                ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2)
            + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, ← hEcard]
            ring
  -- ### Step 3
  have hstep3 : ∑ q ∈ quadSet W,
        (∫ u in q.2.2.2 - K..q.2.2.2 + K,
          ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2 ≤
      2 * K * ∑ q ∈ quadSet W,
        ∫ u in q.2.2.2 - K..q.2.2.2 + K,
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have h := sq_intervalIntegral_le
      (f := fun u => ‖Submission.LargeValues.smoothedPoly N b u‖)
      ((continuous_smoothedPoly N hN b).norm) (fun x => norm_nonneg _)
      (a := q.2.2.2 - K) (b := q.2.2.2 + K) (by linarith)
    rwa [show (q.2.2.2 + K) - (q.2.2.2 - K) = 2 * K by ring] at h
  -- ### Step 4
  have hstep4 : ∑ q ∈ quadSet W,
        ∫ u in q.2.2.2 - K..q.2.2.2 + K,
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 ≤
      3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 := by
    rw [sum_quadSet]
    have hinner : ∀ t1 ∈ W, ∀ t2 ∈ W, ∀ t3 ∈ W,
        ∑ t4 ∈ W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1),
          ∫ u in t4 - K..t4 + K, ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2
        ≤ 3 * ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
            ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 := by
      intro t1 _ t2 _ t3 _
      have hcard : (W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1)).card ≤ 3 :=
        card_filter_le_three hsep (t1 + t2 - t3)
      have hone : ∀ t4 ∈ W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1),
          ∫ u in t4 - K..t4 + K, ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2
          ≤ ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
              ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 := by
        intro t4 ht4
        rw [Finset.mem_filter] at ht4
        have habs := abs_le.mp ht4.2
        have h1 : t1 + t2 - t3 - (K + 1) ≤ t4 - K := by linarith [habs.1]
        have h2 : t4 + K ≤ t1 + t2 - t3 + (K + 1) := by linarith [habs.2]
        have h3 : t4 - K ≤ t4 + K := by linarith
        refine intervalIntegral.integral_mono_interval h1 h3 h2 ?_ ?_
        · filter_upwards with x
          exact sq_nonneg _
        · exact (((continuous_smoothedPoly N hN b).norm).pow 2).intervalIntegrable
            (μ := volume) _ _
      have hI0 : 0 ≤ ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun u _ => sq_nonneg _
      calc ∑ t4 ∈ W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1),
            ∫ u in t4 - K..t4 + K, ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2
          ≤ ∑ t4 ∈ W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1),
              ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
                ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 := Finset.sum_le_sum hone
        _ = (W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1)).card •
              (∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
                ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2) := Finset.sum_const _
        _ = ((W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1)).card : ℝ) *
              (∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
                ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2) := by rw [nsmul_eq_mul]
        _ ≤ 3 * (∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
                ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hI0
    calc ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑ t4 ∈
            W.filter (fun t4 => |t1 + t2 - t3 - t4| ≤ 1),
            ∫ u in t4 - K..t4 + K, ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2
        ≤ ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            3 * ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
              ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 :=
          Finset.sum_le_sum fun t1 ht1 => Finset.sum_le_sum fun t2 ht2 =>
            Finset.sum_le_sum fun t3 ht3 => hinner t1 ht1 t2 ht2 t3 ht3
      _ = 3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
              ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t1 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t2 _ => ?_
          rw [Finset.mul_sum]
  -- ### Step 5 (GM Lemma 11.4 core; delegated to `triple_sum_integral_le`)
  have hstep5 : ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2
      ≤ 2 * (K + 1) * Cw ^ 2 * Y := by
    rw [hYdef]
    exact Work.GM.Energy.EnergyCore.triple_sum_integral_le N hN b hb Cw hCwnn hCwbd W (K + 1) (by linarith)
  -- ### Combine
  have hA : 2 * Cloc ^ 2 * (∑ q ∈ quadSet W,
        (∫ u in q.2.2.2 - K..q.2.2.2 + K,
          ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2)
      ≤ 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y := by
    have h1 : 2 * Cloc ^ 2 * (∑ q ∈ quadSet W,
          (∫ u in q.2.2.2 - K..q.2.2.2 + K,
            ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2)
        ≤ 2 * Cloc ^ 2 * (2 * K * ∑ q ∈ quadSet W,
            ∫ u in q.2.2.2 - K..q.2.2.2 + K,
              ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hstep3 (by positivity)
    have h2 : 2 * Cloc ^ 2 * (2 * K * ∑ q ∈ quadSet W,
            ∫ u in q.2.2.2 - K..q.2.2.2 + K,
              ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2)
        ≤ 2 * Cloc ^ 2 * (2 * K * (3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
              ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hstep4 (by positivity : (0:ℝ) ≤ 2 * K))
        (by positivity : (0:ℝ) ≤ 2 * Cloc ^ 2)
    have h3 : 2 * Cloc ^ 2 * (2 * K * (3 * ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
            ∫ u in t1 + t2 - t3 - (K + 1)..t1 + t2 - t3 + (K + 1),
              ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2))
        ≤ 2 * Cloc ^ 2 * (2 * K * (3 * (2 * (K + 1) * Cw ^ 2 * Y))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hstep5 (by norm_num : (0:ℝ) ≤ 3))
          (by positivity : (0:ℝ) ≤ 2 * K))
        (by positivity : (0:ℝ) ≤ 2 * Cloc ^ 2)
    calc 2 * Cloc ^ 2 * (∑ q ∈ quadSet W,
          (∫ u in q.2.2.2 - K..q.2.2.2 + K,
            ‖Submission.LargeValues.smoothedPoly N b u‖) ^ 2)
        ≤ 2 * Cloc ^ 2 * (2 * K * (3 * (2 * (K + 1) * Cw ^ 2 * Y))) :=
          le_trans (le_trans h1 h2) h3
      _ = 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y := by ring
  have hmain : ∑ q ∈ quadSet W,
      ‖Submission.LargeValues.smoothedPoly N b q.2.2.2‖ ^ 2
      ≤ 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y
        + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E :=
    le_trans hstep2 (add_le_add hA le_rfl)
  have hE1 : E ≤ (24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y
      + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E) / V ^ 2 :=
    le_trans hstep1 (div_le_div_of_nonneg_right hmain hV2pos.le)
  have hsplit : (24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y
        + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E) / V ^ 2
      = 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y / V ^ 2
        + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E / V ^ 2 := by ring
  -- second term comparison
  have hSle : S ≤ (2 * N + 1 : ℝ) := by
    rw [hSdef]
    calc ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ ≤ ∑ n ∈ Finset.Icc N (2 * N), (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => hb n
      _ = ((Finset.Icc N (2 * N)).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (2 * N + 1 : ℝ) := by
          have h2 : (Finset.Icc N (2 * N)).card ≤ 2 * N + 1 := by
            calc (Finset.Icc N (2 * N)).card ≤ (Finset.range (2 * N + 1)).card := by
                  apply Finset.card_le_card
                  intro n hn
                  rw [Finset.mem_Icc] at hn
                  rw [Finset.mem_range]
                  omega
              _ = 2 * N + 1 := Finset.card_range _
          exact_mod_cast h2
  have hkeyB : 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2
      ≤ C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 := by
    have hCl2 : Cloc ^ 2 ≤ (Cloc + 1) ^ 2 := by nlinarith [hCloc.le]
    have hS2 : S ^ 2 ≤ (2 * N + 1 : ℝ) ^ 2 := by
      rw [sq, sq]
      exact mul_self_le_mul_self hS0 hSle
    have hcore : 2 * Cloc ^ 2 * S ^ 2 ≤ C * (Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2 := by
      have hA1 : Cloc ^ 2 * S ^ 2 ≤ (Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2 :=
        mul_le_mul hCl2 hS2 (sq_nonneg S) (by positivity)
      have h2 : 2 * (Cloc ^ 2 * S ^ 2) ≤ 2 * ((Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hA1 (by norm_num)
      have h3 : 2 * ((Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2)
          ≤ C * ((Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hCge2 (by positivity)
      calc 2 * Cloc ^ 2 * S ^ 2 = 2 * (Cloc ^ 2 * S ^ 2) := by ring
        _ ≤ C * ((Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2) := le_trans h2 h3
        _ = C * (Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2 := by ring
    have hKm2 : (0 : ℝ) < (K ^ (m : ℝ)) ^ 2 := by positivity
    have e1 : 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2
        = (2 * Cloc ^ 2 * S ^ 2) / (K ^ (m : ℝ)) ^ 2 := by rw [div_pow]; ring
    have e2 : C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2
        = (C * (Cloc + 1) ^ 2 * (2 * N + 1 : ℝ) ^ 2) / (K ^ (m : ℝ)) ^ 2 := by
      rw [div_pow]; ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hcore hKm2.le
  have hBfinal : 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E / V ^ 2
      ≤ C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 / V ^ 2 * E := by
    have h1 : 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E
        ≤ C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 * E :=
      mul_le_mul_of_nonneg_right hkeyB hE0
    have h2 := div_le_div_of_nonneg_right h1 hV2pos.le
    have e : C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 * E / V ^ 2
        = C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 / V ^ 2 * E := by
      ring
    rwa [e] at h2
  -- first term comparison
  have hkeyA : 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 ≤ C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 := by
    have hCl2 : Cloc ^ 2 ≤ (Cloc + 1) ^ 2 := by nlinarith [hCloc.le]
    have hKle : K ≤ K + 1 := by linarith
    have hK1 : 0 ≤ K + 1 := by linarith
    have h1 : K * (K + 1) * Cloc ^ 2 ≤ (K + 1) * (K + 1) * (Cloc + 1) ^ 2 := by
      have ha : K * Cloc ^ 2 ≤ (K + 1) * (Cloc + 1) ^ 2 :=
        calc K * Cloc ^ 2 ≤ (K + 1) * Cloc ^ 2 :=
              mul_le_mul_of_nonneg_right hKle (sq_nonneg Cloc)
          _ ≤ (K + 1) * (Cloc + 1) ^ 2 := mul_le_mul_of_nonneg_left hCl2 hK1
      calc K * (K + 1) * Cloc ^ 2 = (K + 1) * (K * Cloc ^ 2) := by ring
        _ ≤ (K + 1) * ((K + 1) * (Cloc + 1) ^ 2) := mul_le_mul_of_nonneg_left ha hK1
        _ = (K + 1) * (K + 1) * (Cloc + 1) ^ 2 := by ring
    have h2 : 24 * Cw ^ 2 * (K * (K + 1) * Cloc ^ 2)
        ≤ 24 * Cw ^ 2 * ((K + 1) * (K + 1) * (Cloc + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 24 * Cw ^ 2 * ((K + 1) * (K + 1) * (Cloc + 1) ^ 2)
        ≤ C * ((K + 1) * (K + 1) * (Cloc + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right hCge (by positivity)
    calc 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2
        = 24 * Cw ^ 2 * (K * (K + 1) * Cloc ^ 2) := by ring
      _ ≤ C * ((K + 1) * (K + 1) * (Cloc + 1) ^ 2) := le_trans h2 h3
      _ = C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 := by ring
  have hAfinal : 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y / V ^ 2
      ≤ C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 / V ^ 2 * Y := by
    have h1 : 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y
        ≤ C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 * Y :=
      mul_le_mul_of_nonneg_right hkeyA hY0
    have h2 := div_le_div_of_nonneg_right h1 hV2pos.le
    have e : C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 * Y / V ^ 2
        = C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 / V ^ 2 * Y := by ring
    rwa [e] at h2
  calc E ≤ 24 * K * (K + 1) * Cw ^ 2 * Cloc ^ 2 * Y / V ^ 2
        + 2 * (Cloc / K ^ (m : ℝ)) ^ 2 * S ^ 2 * E / V ^ 2 := by
        rw [← hsplit]; exact hE1
    _ ≤ C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 / V ^ 2 * Y
        + C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 / V ^ 2 * E :=
        add_le_add hAfinal hBfinal


end Work.GM.Energy.EnergyCore2
