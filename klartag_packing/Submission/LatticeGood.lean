import Mathlib
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume
import Submission.Commons.Lattice.Counting.exists_qary_weighted_sum_le_ne_zero
import Submission.Commons.Lattice.Counting.exists_qary_lattice_covolume_and_image
import Submission.Commons.Lattice.MinkowskiHlawka.minkowski_hlawka
import Submission.Commons.GeometryOfNumbers.Counting.exists_prime_radius_strong

/-!
# A good starting lattice for the exploration process

See `Submission/PLAN_V9.md` §3.  The exploration process must be run against a lattice `Λ₀` of

* minimum norm `> 1` (so that `a₀ • Id` with `a₀ = (1 - 1/d)^{-2}` is `Λ₀`-free),
* covolume `≤ 4 ω_d` (so that `det A_K ≈ d^{-4}` gives an ellipsoid of *absolute* volume
  `≈ d²`), and
* `#{y ∈ Λ₀ : ‖y‖ ≤ ρ} = e^{O(√log d)}` for the shell radius `ρ ≈ 1 + O(√log d / d)`.

`ℤ^d` fails on the second point (covolume `1`); only near-optimal packings work, and the `q`-ary
ensemble supplies them.  The count comes from one application of
`exists_qary_weighted_sum_le_ne_zero`.
-/

namespace Submission.LatticeGood

set_option maxHeartbeats 4000000

open MeasureTheory Metric Matrix
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The volume of the unit ball of `ℝ^d`. -/
def omega (d : ℕ) : ℝ :=
  ENNReal.toReal (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))

lemma volume_ball_toReal {t : ℝ} (ht : 0 < t) :
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) t)).toReal
      = t ^ d * omega d :=
  Commons.Lattice.MinkowskiHlawka.volume_ball_toReal (n := d) ht

lemma omega_pos (d : ℕ) (hd : 0 < d) : 0 < omega d := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := by infer_instance
  rw [omega]
  rw [← MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball
    (MeasureTheory.volume) (0 : EuclideanSpace ℝ (Fin d)) 1]
  exact Commons.Analysis.InnerProductSpace.unitBall_volume_pos

/-! ## The Finset of short nonzero integer vectors -/

/-- The set of nonzero integer vectors `x` with `∑ xᵢ² ≤ T²`. -/
def SbSet (d : ℕ) (T : ℝ) : Set (Fin d → ℤ) :=
  {x | 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧ (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2}

lemma finite_SbSet (d : ℕ) (T : ℝ) : (SbSet d T).Finite :=
  (Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) T).subset
    (fun _ hx => hx.2)

/-- The Finset of nonzero integer vectors `x` with `∑ xᵢ² ≤ T²`. -/
def Sb (d : ℕ) (T : ℝ) : Finset (Fin d → ℤ) := (finite_SbSet d T).toFinset

lemma mem_Sb {T : ℝ} {x : Fin d → ℤ} :
    x ∈ Sb d T ↔ 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧ (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2 := by
  rw [Sb, Set.Finite.mem_toFinset (finite_SbSet d T)]
  rfl

lemma card_Sb_le {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) :
    ((Sb d T).card : ℝ) ≤ (T + Real.sqrt d / 2) ^ d * omega d := by
  haveI : Fintype ↥(SbSet d T) := (finite_SbSet d T).fintype
  have hcard1 : (Sb d T).card = Nat.card ↥(SbSet d T) := by
    rw [Sb, Set.Finite.card_toFinset]
    exact (Nat.card_eq_fintype_card).symm
  have hfin := Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) T
  have hmono : Nat.card ↥(SbSet d T)
      ≤ Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2} :=
    Nat.card_mono hfin (fun _ hx => hx.2)
  have hvol : (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2} : ℝ)
      ≤ (T + Real.sqrt d / 2) ^ d * omega d := by
    have h := Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume (d := d) hd
      (R := T) hT
    rw [volume_ball_toReal (d := d) (t := T + Real.sqrt d / 2) (by positivity)] at h
    exact h
  calc ((Sb d T).card : ℝ) = (Nat.card ↥(SbSet d T) : ℝ) := by rw [hcard1]
    _ ≤ (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2} : ℝ) := by
        exact_mod_cast hmono
    _ ≤ (T + Real.sqrt d / 2) ^ d * omega d := hvol

lemma sb_mono {T T' : ℝ} (h0 : 0 ≤ T) (h : T ≤ T') : Sb d T ⊆ Sb d T' := by
  intro x hx
  rw [mem_Sb] at hx ⊢
  exact ⟨hx.1, le_trans hx.2 (by nlinarith)⟩

lemma natCard_finset_coe {α : Type*} (s : Finset α) : Nat.card (↥(s : Set α)) = s.card := by
  rw [Nat.card_eq_fintype_card, ← Set.Finite.card_toFinset (s.finite_toSet)]
  congr 1
  exact Finset.coe_injective (Set.Finite.coe_toFinset _)

/-- The norm of the vector `k / R`, for an integer vector `k`. -/
lemma norm_toLp_div (R : ℝ) (hR : 0 < R) (k : Fin d → ℤ) :
    ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ) / R) : EuclideanSpace ℝ (Fin d))‖
      = ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ)) : EuclideanSpace ℝ (Fin d))‖ / R := by
  have h : (WithLp.toLp 2 (fun i : Fin d => (k i : ℝ) / R) : EuclideanSpace ℝ (Fin d))
      = R⁻¹ • WithLp.toLp 2 (fun i : Fin d => (k i : ℝ)) := by
    ext i
    simp [PiLp.smul_apply, div_eq_inv_mul]
  rw [h, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ R⁻¹), inv_mul_eq_div]

lemma normSq_toLp (k : Fin d → ℤ) :
    ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ)) : EuclideanSpace ℝ (Fin d))‖ ^ 2
      = ∑ i, ((k i : ℝ)) ^ 2 :=
  Commons.GeometryOfNumbers.Counting.norm_toLp_intLattice k


/-! ## The main construction -/

/-- **The good starting lattice.**  Given a prime `q`, a radius `R` with `4 ω_d R^d = q`,
`2R < q` and `(R + √d/2)^d ω_d ≤ q/3` (the last two are supplied by
`exists_prime_radius_strong`), the `q`-ary lattice `(1/R)·{x : x·a ≡ 0 mod q}` has minimum norm
`> 1`, covolume `4 ω_d`, and at most `4ρ^d` vectors in the ball of radius `ρ`. -/
theorem exists_good_lattice_of_prime_radius (d : ℕ) (hd : 2 ≤ d) {ρ : ℝ} (hρ1 : 1 ≤ ρ)
    (hρ2 : ρ ≤ 2) {q : ℕ} (hqprime : q.Prime) {R : ℝ} (hRpos : 0 < R)
    (hRq : 2 * R < (q : ℝ)) (hReq : 4 * omega d * R ^ d = (q : ℝ))
    (hRineq : (R + Real.sqrt d / 2) ^ d * omega d ≤ (q : ℝ) / 3) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      ZLattice.covolume Λ ≤ 4 * omega d ∧
      (∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) ∧
      (Nat.card {v : Λ // ‖(v : EuclideanSpace ℝ (Fin d))‖ ≤ ρ} : ℝ) ≤ 4 * ρ ^ d := by
  classical
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  have hω : 0 < omega d := omega_pos d hd0
  have hρpos : 0 < ρ := lt_of_lt_of_le one_pos hρ1
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqprime.pos
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  -- R ≥ 1
  have hRge1 : 1 ≤ R := by
    have h4 : (R + Real.sqrt d / 2) ^ d * omega d ≤ (4 * R ^ d / 3) * omega d := by
      have hq : (q : ℝ) / 3 = 4 * R ^ d * omega d / 3 := by linarith [hReq]
      rw [hq] at hRineq
      linarith [hRineq]
    have h5 : (R + Real.sqrt d / 2) ^ d ≤ 4 * R ^ d / 3 :=
      le_of_mul_le_mul_right h4 hω
    have hfac : (R + Real.sqrt d / 2) = R * (1 + Real.sqrt d / (2 * R)) := by
      field_simp <;> ring
    rw [hfac, mul_pow] at h5
    have hRp : 0 < R ^ d := pow_pos hRpos d
    have h6 : (1 + Real.sqrt d / (2 * R)) ^ d ≤ 4 / 3 := by
      have h5b : R ^ d * (1 + Real.sqrt d / (2 * R)) ^ d ≤ R ^ d * (4 / 3) := by
        rw [show (4 : ℝ) * R ^ d / 3 = R ^ d * (4 / 3) by ring] at h5
        exact h5
      exact le_of_mul_le_mul_left h5b hRp
    have hbin := one_add_mul_le_pow (a := Real.sqrt d / (2 * R))
      (by
        have h1 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg d
        have h2 : (0 : ℝ) < 2 * R := by positivity
        have h3 : (0 : ℝ) ≤ Real.sqrt d / (2 * R) := div_nonneg h1 h2.le
        linarith) d
    have h7 : 1 + (d : ℝ) * (Real.sqrt d / (2 * R)) ≤ 4 / 3 := le_trans hbin h6
    have h8 : (d : ℝ) * (Real.sqrt d / (2 * R)) ≤ 1 / 3 := by linarith
    have h10 : (d : ℝ) * Real.sqrt d / (2 * R) ≤ 1 / 3 := by
      convert h8 using 2
      ring
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R)] at h10
    have h11 : (1 : ℝ) ≤ 3 * (d : ℝ) * Real.sqrt d / 2 := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
      have hsq : (1 : ℝ) ≤ Real.sqrt d := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hd1
      nlinarith [hd1, hsq]
    nlinarith [h10, h11]
  -- the two Finsets
  set S₁ : Finset (Fin d → ℤ) := Sb d R with hS₁
  set S₂ : Finset (Fin d → ℤ) := Sb d (R * ρ) with hS₂
  have hS₁card : ((S₁.card : ℝ)) ≤ (q : ℝ) / 3 := by
    rw [hS₁]
    exact le_trans (card_Sb_le hd0 hRpos) hRineq
  have hS₂card : ((S₂.card : ℝ)) ≤ ρ ^ d * ((q : ℝ) / 3) := by
    rw [hS₂]
    refine le_trans (card_Sb_le (d := d) hd0 (T := R * ρ) (by positivity)) ?_
    have hle : R * ρ + Real.sqrt d / 2 ≤ ρ * (R + Real.sqrt d / 2) := by
      have := Real.sqrt_nonneg (d : ℝ)
      nlinarith [hRpos, hρ1]
    calc (R * ρ + Real.sqrt d / 2) ^ d * omega d
        ≤ (ρ * (R + Real.sqrt d / 2)) ^ d * omega d :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hle d) hω.le
      _ = ρ ^ d * ((R + Real.sqrt d / 2) ^ d * omega d) := by rw [mul_pow]; ring
      _ ≤ ρ ^ d * ((q : ℝ) / 3) := mul_le_mul_of_nonneg_left hRineq (by positivity)
  have hsub : S₁ ⊆ S₂ := by
    rw [hS₁, hS₂]
    exact sb_mono hRpos.le (by nlinarith [hRpos, hρ1])
  -- the weight
  set ε : ℝ := (2 / 5) * (ρ ^ d)⁻¹ with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hερ : ε * ρ ^ d = 2 / 5 := by rw [hε]; field_simp <;> ring
  have hχcond : ∀ x ∈ S₂, ∃ j, (x j : ZMod q) ≠ 0 := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    rw [hS₂] at hx
    have hxS := (mem_Sb.mp hx)
    have hRρq : R * ρ < (q : ℝ) := by nlinarith [hRq, hρ2]
    have hcoord : ∀ i, x i = 0 := by
      intro i
      have hdvd : ((q : ℤ)) ∣ x i := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (x i) q]
        exact hcon i
      have h1 : ((x i : ℝ)) ^ 2 ≤ ∑ j, ((x j : ℝ)) ^ 2 :=
        Finset.single_le_sum (f := fun j => ((x j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      have h2 : ((x i : ℝ)) ^ 2 ≤ (R * ρ) ^ 2 := le_trans h1 hxS.2
      have h3 : |((x i : ℤ) : ℝ)| < (q : ℝ) := by
        have h4 : |((x i : ℝ))| ≤ R * ρ := by
          rw [← Real.sqrt_sq_eq_abs]
          refine le_trans (Real.sqrt_le_sqrt h2) ?_
          rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ R * ρ)]
        exact lt_of_le_of_lt h4 hRρq
      have h5 : |(x i : ℤ)| < (q : ℤ) := by exact_mod_cast h3
      exact Int.eq_zero_of_abs_lt_dvd hdvd h5
    have hz : (∑ i, ((x i : ℝ)) ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hcoord i]; norm_num
    linarith [hxS.1, hz]
  obtain ⟨A, hA⟩ := Commons.Lattice.Counting.exists_qary_weighted_sum_le_ne_zero
    (q := q) (m := 1) (d := d) (S := S₂)
    (f := fun x : Fin d → ℤ => if x ∈ S₁ then (1 : ℝ) else ε)
    (fun x => by by_cases h : x ∈ S₁ <;> simp [h, hεpos.le]) hχcond
  let a : Fin d → ZMod q := fun j => A 0 j
  let χ : (Fin d → ℤ) → Prop := fun x => (∑ j, (x j : ZMod q) * a j = 0)
  have hAχ : (∑ x ∈ S₂, if χ x then (if x ∈ S₁ then (1 : ℝ) else ε) else 0)
      ≤ 2 * (q : ℝ)⁻¹ * (∑ x ∈ S₂, if x ∈ S₁ then (1 : ℝ) else ε) := by
    have h := hA
    simp only [Fin.forall_fin_one, pow_one] at h
    exact h
  -- the right-hand side
  have hRHS : (∑ x ∈ S₂, if x ∈ S₁ then (1 : ℝ) else ε)
      ≤ (S₁.card : ℝ) + ε * (S₂.card : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun x => x ∈ S₁)
      (fun x => if x ∈ S₁ then (1 : ℝ) else ε)]
    have h1 : (∑ x ∈ S₂ with x ∈ S₁, (if x ∈ S₁ then (1 : ℝ) else ε))
        = ((S₂.filter (fun x => x ∈ S₁)).card : ℝ) := by
      have h' : ∀ x ∈ S₂.filter (fun x => x ∈ S₁), (if x ∈ S₁ then (1 : ℝ) else ε) = 1 :=
        fun x hx => if_pos (Finset.mem_filter.mp hx).2
      rw [Finset.sum_congr rfl h', Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : (∑ x ∈ S₂ with ¬ x ∈ S₁, (if x ∈ S₁ then (1 : ℝ) else ε))
        = ε * ((S₂.filter (fun x => ¬ x ∈ S₁)).card : ℝ) := by
      have h' : ∀ x ∈ S₂.filter (fun x => ¬ x ∈ S₁), (if x ∈ S₁ then (1 : ℝ) else ε) = ε :=
        fun x hx => if_neg (Finset.mem_filter.mp hx).2
      rw [Finset.sum_congr rfl h', Finset.sum_const, nsmul_eq_mul]
      ring
    rw [h1, h2]
    have hc1 : ((S₂.filter (fun x => x ∈ S₁)).card : ℝ) ≤ (S₁.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)
    have hc2 : ((S₂.filter (fun x => ¬ x ∈ S₁)).card : ℝ) ≤ (S₂.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    nlinarith [hc1, hc2, hεpos]
  have hbound : 2 * (q : ℝ)⁻¹ * ((S₁.card : ℝ) + ε * (S₂.card : ℝ)) ≤ 14 / 15 := by
    have hmid : 2 * (q : ℝ)⁻¹ * ((S₁.card : ℝ) + ε * (S₂.card : ℝ))
        ≤ 2 * (q : ℝ)⁻¹ * ((q : ℝ) / 3 + ε * (ρ ^ d * ((q : ℝ) / 3))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h2 : ε * (S₂.card : ℝ) ≤ ε * (ρ ^ d * ((q : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hS₂card hεpos.le
      linarith [hS₁card, h2]
    refine le_trans hmid ?_
    have h3 : 2 * (q : ℝ)⁻¹ * ((q : ℝ) / 3 + ε * (ρ ^ d * ((q : ℝ) / 3)))
        = 2 / 3 + (2 / 3) * (ε * ρ ^ d) := by
      field_simp <;> ring
    rw [h3, hερ]; norm_num
  set F : ℝ := ∑ x ∈ S₂, if χ x then (if x ∈ S₁ then (1 : ℝ) else ε) else 0 with hF
  have hFsum : F = ∑ x ∈ S₂.filter χ, (if x ∈ S₁ then (1 : ℝ) else ε) := by
    rw [hF, Finset.sum_filter]
  have hFle : F ≤ 14 / 15 :=
    le_trans (le_trans hAχ (mul_le_mul_of_nonneg_left hRHS (by positivity))) hbound
  have hsubχ : S₁.filter χ ⊆ S₂.filter χ := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hsub hx.1, hx.2⟩
  have hnn : ∀ x, (0 : ℝ) ≤ (if x ∈ S₁ then (1 : ℝ) else ε) := by
    intro x
    by_cases hx : x ∈ S₁ <;> simp [hx, hεpos.le]
  have hsum1 : (∑ x ∈ S₁.filter χ, (if x ∈ S₁ then (1 : ℝ) else ε))
      = ((S₁.filter χ).card : ℝ) := by
    have h' : ∀ x ∈ S₁.filter χ, (if x ∈ S₁ then (1 : ℝ) else ε) = 1 :=
      fun x hx => if_pos (Finset.mem_filter.mp hx).1
    rw [Finset.sum_congr rfl h', Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the two conclusions
  have hker1 : (S₁.filter χ).card = 0 := by
    have hle : ((S₁.filter χ).card : ℝ) ≤ F := by
      rw [hFsum, ← hsum1]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubχ (fun i _ _ => hnn i)
    have hcast : ((S₁.filter χ).card : ℝ) ≤ 14 / 15 := le_trans hle hFle
    have hlt : (S₁.filter χ).card < 1 := by
      have h1 : ((S₁.filter χ).card : ℝ) < 1 := by linarith
      exact_mod_cast h1
    omega
  have hTsub : (S₂.filter χ).filter (fun x => ¬ x ∈ S₁) ⊆ S₂.filter χ :=
    Finset.filter_subset _ _
  have hsum2 : (∑ x ∈ (S₂.filter χ).filter (fun x => ¬ x ∈ S₁),
        (if x ∈ S₁ then (1 : ℝ) else ε))
      = ε * (((S₂.filter χ).filter (fun x => ¬ x ∈ S₁)).card : ℝ) := by
    have h' : ∀ x ∈ (S₂.filter χ).filter (fun x => ¬ x ∈ S₁),
        (if x ∈ S₁ then (1 : ℝ) else ε) = ε :=
      fun x hx => if_neg (Finset.mem_filter.mp hx).2
    rw [Finset.sum_congr rfl h', Finset.sum_const, nsmul_eq_mul]
    ring
  have hTle : ε * (((S₂.filter χ).filter (fun x => ¬ x ∈ S₁)).card : ℝ) ≤ F := by
    rw [hFsum, ← hsum2]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun i _ _ => hnn i)
  have hTcard : (((S₂.filter χ).filter (fun x => ¬ x ∈ S₁)).card : ℝ) ≤ (7 / 3) * ρ ^ d := by
    have hdiv : (((S₂.filter χ).filter (fun x => ¬ x ∈ S₁)).card : ℝ) ≤ (14 / 15) / ε := by
      rw [le_div_iff₀ hεpos]; linarith [hTle, hFle]
    have h56 : (14 / 15 : ℝ) / ε = (7 / 3) * ρ ^ d := by rw [hε]; field_simp <;> ring
    rw [h56] at hdiv
    have hρd : (0 : ℝ) < ρ ^ d := by positivity
    linarith
  have hker2 : ((S₂.filter χ).card : ℝ) ≤ (7 / 3) * ρ ^ d := by
    have hsplit : (S₂.filter χ).card = (S₁.filter χ).card
        + ((S₂.filter χ).filter (fun x => ¬ x ∈ S₁)).card := by
      have hc := Finset.card_filter_add_card_filter_not (s := S₂.filter χ) (p := fun x => x ∈ S₁)
      have heq : (S₂.filter χ).filter (fun x => x ∈ S₁) = S₁.filter χ := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hx2, hx3⟩, hx1⟩; exact ⟨hx1, hx3⟩
        · rintro ⟨hx1, hx3⟩; exact ⟨⟨hsub hx1, hx3⟩, hx1⟩
      rw [heq] at hc
      exact hc.symm
    rw [hsplit, hker1]
    push_cast
    linarith [hTcard]
  -- the covector is nonzero
  have ha_ne : a ≠ 0 := by
    intro hzero
    have hx0mem : (Pi.single (0 : Fin d) (1 : ℤ)) ∈ S₁ := by
      rw [hS₁, mem_Sb]
      have hsum : (∑ i, (((Pi.single (0 : Fin d) (1 : ℤ) : Fin d → ℤ) i : ℝ)) ^ 2) = 1 := by
        rw [Finset.sum_eq_single (0 : Fin d)]
        · rw [Pi.single_eq_same]; norm_num
        · intro b _ hb; rw [Pi.single_eq_of_ne hb]; norm_num
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum]
      exact ⟨by norm_num, by nlinarith [hRge1]⟩
    have hχall : ∀ x, χ x := by
      intro x
      show (∑ j, (x j : ZMod q) * a j = 0)
      simp [hzero]
    have hfilter : S₁.filter χ = S₁ := Finset.filter_true_of_mem (fun x _ => hχall x)
    rw [hfilter] at hker1
    have hempty : S₁ = ∅ := Finset.card_eq_zero.mp hker1
    rw [hempty] at hx0mem
    exact absurd hx0mem (Finset.notMem_empty _)
  obtain ⟨Λ, hdisc, hZL, hcov, himg⟩ :=
    Commons.Lattice.Counting.exists_qary_lattice_covolume_and_image (n := d) (q := q) (R := R)
      hRpos a ha_ne
  refine ⟨Λ, hdisc, hZL, ?_, ?_, ?_⟩
  · -- covolume
    have hRd : R ^ d = (q : ℝ) / (4 * omega d) := by
      rw [eq_div_iff (by positivity : (4 * omega d) ≠ 0)]
      linarith [hReq]
    rw [hcov, hRd, div_div_eq_mul_div]
    rw [mul_div_cancel_left₀ _ hqne]
  · -- minimum norm
    intro v hv
    refine le_of_lt ?_
    obtain ⟨k, hk, hkv⟩ := (himg (v : EuclideanSpace ℝ (Fin d))).mp v.2
    have hk0 : k ≠ 0 := by
      intro hkz
      rw [hkz] at hkv
      simp at hkv
      exact hv (Subtype.ext hkv)
    have hkχ : χ k := hk
    have hknotS₁ : k ∉ S₁ := by
      intro hkmem
      have hmem : k ∈ S₁.filter χ := Finset.mem_filter.mpr ⟨hkmem, hkχ⟩
      have hpos : 0 < (S₁.filter χ).card := Finset.card_pos.mpr ⟨k, hmem⟩
      omega
    rw [hS₁, mem_Sb] at hknotS₁
    push Not at hknotS₁
    have hksum : 0 < ∑ i, ((k i : ℝ)) ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hk0
      have hpos : ∃ j ∈ (Finset.univ : Finset (Fin d)), 0 < ((k j : ℝ)) ^ 2 :=
        ⟨i, Finset.mem_univ i, by
          have hki : ((k i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
          positivity⟩
      exact Finset.sum_pos' (fun j _ => sq_nonneg _) hpos
    have hkbig : R ^ 2 < ∑ i, ((k i : ℝ)) ^ 2 := by
      by_cases h : R ^ 2 < ∑ i, ((k i : ℝ)) ^ 2
      · exact h
      · exact absurd (hknotS₁ hksum) h
    have hkR : R < ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ)) : EuclideanSpace ℝ (Fin d))‖ := by
      have h1 : R ^ 2 < ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ))
          : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
        rw [normSq_toLp k]; exact hkbig
      have h2 : (0 : ℝ) ≤ R := hRpos.le
      have h3 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ))
          : EuclideanSpace ℝ (Fin d))‖ := norm_nonneg _
      nlinarith [h1, h2, h3]
    rw [hkv, norm_toLp_div R hRpos k, lt_div_iff₀ hRpos]
    linarith [hkR]
  · -- the count
    let Tins : Finset (Fin d → ℤ) := insert (0 : Fin d → ℤ) (S₂.filter χ)
    have hmem : ∀ k : Fin d → ℤ, χ k →
        ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ) / R) : EuclideanSpace ℝ (Fin d))‖ ≤ ρ →
        k ∈ Tins := by
      intro k hk hnorm
      by_cases hk0 : k = 0
      · rw [hk0]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem ?_
        rw [Finset.mem_filter]
        refine ⟨?_, hk⟩
        rw [hS₂, mem_Sb]
        have hsum : 0 < ∑ i, ((k i : ℝ)) ^ 2 := by
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hk0
          have hpos : ∃ j ∈ (Finset.univ : Finset (Fin d)), 0 < ((k j : ℝ)) ^ 2 :=
            ⟨i, Finset.mem_univ i, by
              have hki : ((k i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
              positivity⟩
          exact Finset.sum_pos' (fun j _ => sq_nonneg _) hpos
        refine ⟨hsum, ?_⟩
        have h2 : ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ)) : EuclideanSpace ℝ (Fin d))‖
            ≤ ρ * R := by
          rw [norm_toLp_div R hRpos k, div_le_iff₀ hRpos] at hnorm
          linarith [hnorm]
        calc ∑ i, ((k i : ℝ)) ^ 2
            = ‖(WithLp.toLp 2 (fun i : Fin d => (k i : ℝ)) : EuclideanSpace ℝ (Fin d))‖ ^ 2 :=
              (normSq_toLp k).symm
          _ ≤ (R * ρ) ^ 2 := by
              nlinarith [h2, norm_nonneg (WithLp.toLp 2 (fun i : Fin d => (k i : ℝ))
                : EuclideanSpace ℝ (Fin d))]
    haveI : Fintype (↥(Tins : Set (Fin d → ℤ))) := Tins.finite_toSet.fintype
    have hcard := Nat.card_le_card_of_injective
      (fun v : {v : Λ // ‖(v : EuclideanSpace ℝ (Fin d))‖ ≤ ρ} =>
        (⟨Classical.choose ((himg ((v : Λ) : EuclideanSpace ℝ (Fin d))).mp (v : Λ).2),
          hmem _ (Classical.choose_spec ((himg ((v : Λ) : EuclideanSpace ℝ (Fin d))).mp
              (v : Λ).2)).1
            (by rw [← (Classical.choose_spec ((himg ((v : Λ) : EuclideanSpace ℝ (Fin d))).mp
              (v : Λ).2)).2]; exact v.2)⟩
          : ↥(Tins : Set (Fin d → ℤ))))
      (fun v w hvw => by
        have hval : Classical.choose ((himg ((v : Λ) : EuclideanSpace ℝ (Fin d))).mp (v : Λ).2)
            = Classical.choose ((himg ((w : Λ) : EuclideanSpace ℝ (Fin d))).mp (w : Λ).2) :=
          congrArg Subtype.val hvw
        have hv' := (Classical.choose_spec
          ((himg ((v : Λ) : EuclideanSpace ℝ (Fin d))).mp (v : Λ).2)).2
        have hw' := (Classical.choose_spec
          ((himg ((w : Λ) : EuclideanSpace ℝ (Fin d))).mp (w : Λ).2)).2
        have : ((v : Λ) : EuclideanSpace ℝ (Fin d)) = ((w : Λ) : EuclideanSpace ℝ (Fin d)) := by
          rw [hv', hw', hval]
        exact Subtype.ext (Subtype.ext this))
    rw [natCard_finset_coe] at hcard
    have h1 : ((S₂.filter χ).card : ℝ) + 1 ≤ 4 * ρ ^ d := by
      have hρd : (1 : ℝ) ≤ ρ ^ d := one_le_pow₀ hρ1
      linarith [hker2, hρd]
    have h2 : ((Tins : Finset (Fin d → ℤ)).card : ℝ) ≤ 4 * ρ ^ d := by
      have hle : Tins.card ≤ (S₂.filter χ).card + 1 := Finset.card_insert_le _ _
      have : (Tins.card : ℝ) ≤ ((S₂.filter χ).card : ℝ) + 1 := by exact_mod_cast hle
      linarith [h1]
    have hcard1 : ((Nat.card {v : Λ // ‖(v : EuclideanSpace ℝ (Fin d))‖ ≤ ρ} : ℝ))
        ≤ (Tins.card : ℝ) := by exact_mod_cast hcard
    linarith [hcard1, h2]

/-- **The good starting lattice, unconditionally.** -/
theorem exists_good_lattice (d : ℕ) (hd : 2 ≤ d) {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      ZLattice.covolume Λ ≤ 4 * omega d ∧
      (∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) ∧
      (Nat.card {v : Λ // ‖(v : EuclideanSpace ℝ (Fin d))‖ ≤ ρ} : ℝ) ≤ 4 * ρ ^ d := by
  have hd0 : 0 < d := by omega
  obtain ⟨q, hq, R, hR, h2Rq, h4, h3⟩ :=
    Commons.GeometryOfNumbers.Counting.exists_prime_radius_strong hd (omega_pos d hd0)
  exact exists_good_lattice_of_prime_radius d hd hρ1 hρ2 hq hR h2Rq h4 h3

end

end Submission.LatticeGood
