import Mathlib
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.S15delta
import Submission.Work.FIArea4.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The class Cauchy–Schwarz with an arbitrary bounded class factor (standalone)

A self-contained copy of `Work.FIArea4.S15red.pairSum_classFactor_le` together with its
vocabulary `csClsF`/`csClsSum2`/`csEvG`, in its own namespace so that it does not depend on
`Submission.Work.FIArea4.S15red.relSum_bound`.

The class sums `csClsSum2` here are *Jacobi-free*: for an array `u` the pair sum over the
congruence `Δ ≡ 0 (mod m)` with an arbitrary bounded class factor `F` is bounded by the
geometric mean of the class variances `csEvG R m u`, `csEvG R m v`.  The class sums of
`Work.FIArea4.EvarG R m u` are the Jacobi-free class sums of the array `z ↦ u z * jwG m z.re`
(with the weight `jwG m (Re z) = (Re z | oddPart m)` built in), which is `EvarG_eq_csEvG` below.
-/

namespace Work.FIArea4.S15red.StrCS

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The class decomposition of the signed box -/

/-- The class of index `a` of the signed box `gBox R` modulo `m`: the points with `Re z` coprime
to `m` and `Im z ≡ a · Re z (mod m)`. -/
def csClsF (R : ℤ) (m : ℕ) (a : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox R).filter
    (fun z => Nat.Coprime z.re.natAbs m ∧
      ((z.im : ZMod m) = (a : ZMod m) * (z.re : ZMod m)))

@[simp] lemma mem_csClsF {R : ℤ} {m a : ℕ} {z : GaussianInt} :
    z ∈ csClsF R m a ↔ z ∈ Work.FIPlan.gBox R ∧ Nat.Coprime z.re.natAbs m ∧
      ((z.im : ZMod m) = (a : ZMod m) * (z.re : ZMod m)) := by
  simp [csClsF]

/-- The class sum of an array `u` on the signed box. -/
def csClsSum2 (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) (a : ℕ) : ℂ :=
  ∑ z ∈ csClsF R m a, u z

/-- The class variance of an array on the signed box. -/
def csEvG (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) : ℝ :=
  ∑ a ∈ Finset.range m, Complex.normSq (csClsSum2 R m u a)

/-- `Re z` is a unit modulo `m` when `(Re z, m) = 1`. -/
lemma csCls_isUnit (m : ℕ) (z : ℤ) (h : Nat.Coprime z.natAbs m) :
    IsUnit ((z : ℤ) : ZMod m) := by
  have h2 : IsUnit (((z.natAbs : ℤ)) : ZMod m) := by
    rw [Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime z.natAbs m).mpr h
  rcases z.natAbs_eq with hz | hz
  · rw [hz]; exact h2
  · rw [hz]; simpa using h2.neg

/-- Every point of the box whose real part is coprime to `m` lies in a class `csClsF R m a`, `a < m`. -/
lemma exists_mem_csClsF {R : ℤ} {m : ℕ} {z : GaussianInt}
    (hm : 1 ≤ m) (hz : z ∈ Work.FIPlan.gBox R) (hc : Nat.Coprime z.re.natAbs m) :
    ∃ a ∈ Finset.range m, z ∈ csClsF R m a := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨u, hu⟩ := csCls_isUnit m z.re hc
  refine ⟨((z.im : ZMod m) * (((u⁻¹ : (ZMod m)ˣ)) : ZMod m)).val,
    Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
  rw [mem_csClsF]
  refine ⟨hz, hc, ?_⟩
  have hcoe : ((z.re : ℤ) : ZMod m) = ((u : (ZMod m)ˣ) : ZMod m) := hu.symm
  rw [ZMod.natCast_zmod_val]
  rw [mul_assoc, hcoe, Units.inv_mul, mul_one]

/-- The classes cover the part of the box with `(Re z, m) = 1`. -/
lemma csClsF_cover (R : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    (Work.FIPlan.gBox R).filter (fun z => Nat.Coprime z.re.natAbs m)
      = (Finset.range m).biUnion (csClsF R m) := by
  ext z
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hz, hc⟩
    exact exists_mem_csClsF hm hz hc
  · rintro ⟨a, _, hz⟩
    exact ⟨(mem_csClsF.mp hz).1, (mem_csClsF.mp hz).2.1⟩

/-- Distinct classes are disjoint. -/
lemma csClsF_pairwiseDisjoint (R : ℤ) (m : ℕ) :
    (↑(Finset.range m) : Set ℕ).PairwiseDisjoint (csClsF R m) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  show Disjoint (csClsF R m a) (csClsF R m b)
  rw [Finset.disjoint_left]
  intro z hza hzb
  have hza' := mem_csClsF.mp hza
  have hzb' := mem_csClsF.mp hzb
  have h3 : (a : ZMod m) * (z.re : ZMod m) = (b : ZMod m) * (z.re : ZMod m) := by
    rw [← hza'.2.2, hzb'.2.2]
  have h4 : (a : ZMod m) = (b : ZMod m) := (csCls_isUnit m z.re hza'.2.1).mul_right_cancel h3
  exact hab (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff a b m).mp h4) ha hb)

/-- Two points of one class satisfy `m ∣ Δ(z₁,z₂)`. -/
lemma csClsF_delta_zero {R : ℤ} {m a : ℕ} {z1 z2 : GaussianInt}
    (h1 : z1 ∈ csClsF R m a) (h2 : z2 ∈ csClsF R m a) :
    (Work.FIPlan.Delta z1 z2 : ZMod m) = 0 := by
  have h1' := mem_csClsF.mp h1
  have h2' := mem_csClsF.mp h2
  have hD : ((Work.FIPlan.Delta z1 z2 : ℤ) : ZMod m)
      = (z1.re : ZMod m) * (z2.im : ZMod m) - (z2.re : ZMod m) * (z1.im : ZMod m) := by
    rw [Delta_eq]; push_cast; ring
  rw [hD, h2'.2.2, h1'.2.2]
  ring

/-- Conversely, a point of the box with `Re` coprime to `m` and `m ∣ Δ(z₁,z₂)` lies in the class
of `z₁`. -/
lemma mem_csClsF_of_delta_zero {R : ℤ} {m a : ℕ} {z1 z2 : GaussianInt}
    (h1 : z1 ∈ csClsF R m a) (hz2 : z2 ∈ Work.FIPlan.gBox R)
    (hc2 : Nat.Coprime z2.re.natAbs m) (hΔ : (Work.FIPlan.Delta z1 z2 : ZMod m) = 0) :
    z2 ∈ csClsF R m a := by
  have h1' := mem_csClsF.mp h1
  rw [mem_csClsF]
  refine ⟨hz2, hc2, ?_⟩
  have hD : ((Work.FIPlan.Delta z1 z2 : ℤ) : ZMod m)
      = (z1.re : ZMod m) * (z2.im : ZMod m) - (z2.re : ZMod m) * (z1.im : ZMod m) := by
    rw [Delta_eq]; push_cast; ring
  rw [hD] at hΔ
  have hm : (z1.re : ZMod m) * (z2.im : ZMod m)
      = (z1.re : ZMod m) * ((a : ZMod m) * (z2.re : ZMod m)) := by
    have hsub := sub_eq_zero.mp hΔ
    rw [hsub, h1'.2.2]
    ring
  exact (csCls_isUnit m z1.re h1'.2.1).mul_left_cancel hm

/-- A double sum of a constant times `A z₁ · conj(B z₂)` factors. -/
lemma cs_sum_const_mul_star {ι : Type*} (s t : Finset ι) (γ : ℂ) (A B : ι → ℂ) :
    (∑ z1 ∈ s, ∑ z2 ∈ t, γ * (A z1 * star (B z2)))
      = γ * (∑ z1 ∈ s, A z1) * star (∑ z2 ∈ t, B z2) := by
  trans ∑ z1 ∈ s, γ * A z1 * (∑ z2 ∈ t, star (B z2))
  · refine Finset.sum_congr rfl (fun z1 _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z2 _ => by ring)
  · rw [star_sum, ← Finset.sum_mul, ← Finset.mul_sum]

/-! ## The class Cauchy–Schwarz with an arbitrary class factor -/

/-- **The class Cauchy–Schwarz with an arbitrary bounded class factor.**  If the kernel of a pair
sum over the congruence `Δ ≡ 0 (mod m)` factors as `F(class)·(per-factor parts)`, the per-factor
parts can be absorbed into the arrays `u`, `v` and the pair sum is bounded by the geometric mean
of the class variances. -/
theorem csPairSum_le (R : ℤ) (m : ℕ) (hm : 1 ≤ m) (u v : GaussianInt → ℂ)
    (F : ZMod m → ℂ) (hF : ∀ a, ‖F a‖ ≤ 1)
    (hu : ∀ z : GaussianInt, u z ≠ 0 → Nat.Coprime z.re.natAbs m)
    (hv : ∀ z : GaussianInt, v z ≠ 0 → Nat.Coprime z.re.natAbs m) :
    ‖∑ z1 ∈ Work.FIPlan.gBox R, ∑ z2 ∈ Work.FIPlan.gBox R,
        (if (Work.FIPlan.Delta z1 z2 : ZMod m) = 0 then
          F ((z1.im : ZMod m) * ((z1.re : ZMod m))⁻¹) * (u z1 * star (v z2)) else 0)‖
      ≤ Real.sqrt (csEvG R m u) * Real.sqrt (csEvG R m v) := by
  classical
  set G : GaussianInt → GaussianInt → ℂ := fun z1 z2 =>
    (if (Work.FIPlan.Delta z1 z2 : ZMod m) = 0 then
      F ((z1.im : ZMod m) * ((z1.re : ZMod m))⁻¹) * (u z1 * star (v z2)) else 0) with hG
  have hGz1 : ∀ z1 z2, ¬ Nat.Coprime z1.re.natAbs m → G z1 z2 = 0 := by
    intro z1 z2 hnc
    have h0 : u z1 = 0 := by by_contra h; exact hnc (hu z1 h)
    simp only [hG, h0, zero_mul]
    split <;> simp
  have hGz2 : ∀ z1 z2, ¬ Nat.Coprime z2.re.natAbs m → G z1 z2 = 0 := by
    intro z1 z2 hnc
    have h0 : v z2 = 0 := by by_contra h; exact hnc (hv z2 h)
    simp only [hG, h0, star_zero, mul_zero]
    split <;> simp
  -- the class factor is constant on a class
  have hcls : ∀ a ∈ Finset.range m, ∀ z1 ∈ csClsF R m a, ∀ z2 ∈ csClsF R m a,
      G z1 z2 = F ((a : ZMod m)) * (u z1 * star (v z2)) := by
    intro a ha z1 hz1 z2 hz2
    have hz1' := mem_csClsF.mp hz1
    have hd : (Work.FIPlan.Delta z1 z2 : ZMod m) = 0 := csClsF_delta_zero hz1 hz2
    simp only [hG]
    rw [if_pos hd]
    have hu1 := csCls_isUnit m z1.re hz1'.2.1
    have hcl : (z1.im : ZMod m) * ((z1.re : ZMod m))⁻¹ = (a : ZMod m) := by
      have h2 : ((z1.im : ZMod m) * ((z1.re : ZMod m))⁻¹) * (z1.re : ZMod m)
          = (a : ZMod m) * (z1.re : ZMod m) := by
        rw [mul_assoc, ZMod.inv_mul_of_unit _ hu1, mul_one, hz1'.2.2]
      exact hu1.mul_right_cancel h2
    rw [hcl]
  -- regroup the (restricted) double sum by class
  have step1 : (∑ z1 ∈ (Work.FIPlan.gBox R).filter (fun z : GaussianInt => Nat.Coprime z.re.natAbs m),
          ∑ z2 ∈ (Work.FIPlan.gBox R).filter (fun z : GaussianInt => Nat.Coprime z.re.natAbs m),
            G z1 z2)
      = ∑ a ∈ Finset.range m, ∑ z1 ∈ csClsF R m a, ∑ z2 ∈ csClsF R m a, G z1 z2 := by
    rw [csClsF_cover R m hm]
    rw [Finset.sum_biUnion (f := fun z1 => ∑ z2 ∈ _, G z1 z2)
      (csClsF_pairwiseDisjoint R m)]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun z1 hz1 => ?_)
    rw [Finset.sum_biUnion (f := fun z2 => G z1 z2) (csClsF_pairwiseDisjoint R m)]
    refine Finset.sum_eq_single a (fun b hb hba => ?_) (fun ha' => absurd ha ha')
    refine Finset.sum_eq_zero (fun z2 hz2 => ?_)
    have hz2' := mem_csClsF.mp hz2
    simp only [hG]
    by_cases hΔ : (Work.FIPlan.Delta z1 z2 : ZMod m) = 0
    · rw [if_pos hΔ]
      exfalso
      have hmem : z2 ∈ csClsF R m a := mem_csClsF_of_delta_zero hz1 hz2'.1 hz2'.2.1 hΔ
      have hdisj := csClsF_pairwiseDisjoint R m ha hb (fun h : a = b => hba h.symm)
      exact Finset.disjoint_left.mp hdisj hmem hz2
    · rw [if_neg hΔ]
  -- reduce the original double sum to the restricted one
  have step0 : (∑ z1 ∈ Work.FIPlan.gBox R, ∑ z2 ∈ Work.FIPlan.gBox R, G z1 z2)
      = ∑ z1 ∈ (Work.FIPlan.gBox R).filter (fun z : GaussianInt => Nat.Coprime z.re.natAbs m),
          ∑ z2 ∈ (Work.FIPlan.gBox R).filter (fun z : GaussianInt => Nat.Coprime z.re.natAbs m),
            G z1 z2 := by
    refine (Finset.sum_subset
      (Finset.filter_subset (p := fun z : GaussianInt => Nat.Coprime z.re.natAbs m) _) ?_).symm.trans ?_
    · exact fun z1 hz1 hnc => Finset.sum_eq_zero (fun z2 _ =>
        hGz1 z1 z2 (fun hc => hnc (Finset.mem_filter.mpr ⟨hz1, hc⟩)))
    · refine Finset.sum_congr rfl (fun z1 hz1 => ?_)
      exact (Finset.sum_subset
        (Finset.filter_subset (p := fun z : GaussianInt => Nat.Coprime z.re.natAbs m) _)
        (fun z2 hz2 hnc => hGz2 z1 z2 (fun hc => hnc (Finset.mem_filter.mpr ⟨hz2, hc⟩)))).symm
  have hdecomp : (∑ z1 ∈ Work.FIPlan.gBox R, ∑ z2 ∈ Work.FIPlan.gBox R, G z1 z2)
      = ∑ a ∈ Finset.range m,
          F (a : ZMod m) * csClsSum2 R m u a * star (csClsSum2 R m v a) := by
    rw [step0, step1]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.sum_congr rfl (fun z1 hz1 =>
      Finset.sum_congr rfl (fun z2 hz2 => hcls a ha z1 hz1 z2 hz2))]
    simp only [csClsSum2]
    rw [cs_sum_const_mul_star]
  rw [hdecomp]
  -- Cauchy–Schwarz on the classes
  have hnorm : ∀ a : ℕ, ‖F (a : ZMod m)‖ ≤ 1 := fun a => hF _
  have hmain : ‖∑ a ∈ Finset.range m, F (a : ZMod m) * csClsSum2 R m u a * star (csClsSum2 R m v a)‖
      ≤ ∑ a ∈ Finset.range m, ‖csClsSum2 R m u a‖ * ‖csClsSum2 R m v a‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a _ => ?_))
    calc ‖F (a : ZMod m) * csClsSum2 R m u a * star (csClsSum2 R m v a)‖
        = ‖F (a : ZMod m)‖ * (‖csClsSum2 R m u a‖ * ‖csClsSum2 R m v a‖) := by
          rw [norm_mul, norm_mul, norm_star]; ring
      _ ≤ 1 * (‖csClsSum2 R m u a‖ * ‖csClsSum2 R m v a‖) :=
          mul_le_mul_of_nonneg_right (hnorm a) (by positivity)
      _ = ‖csClsSum2 R m u a‖ * ‖csClsSum2 R m v a‖ := by ring
  refine le_trans hmain ?_
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range m)
    (fun a => ‖csClsSum2 R m u a‖) (fun a => ‖csClsSum2 R m v a‖)
  simpa only [csEvG, Complex.normSq_eq_norm_sq] using this

/-- The identity with `Work.FIArea4.EvarG`: the class sums of `EvarG R m u` are the Jacobi-free
class sums of the array `z ↦ u z * jwG m z.re`. -/
lemma EvarG_eq_csEvG (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) :
    Work.FIArea4.EvarG R m u = csEvG R m (fun z => u z * Work.FIArea4.jwG m z.re) := rfl

end

end Work.FIArea4.S15red.StrCS
