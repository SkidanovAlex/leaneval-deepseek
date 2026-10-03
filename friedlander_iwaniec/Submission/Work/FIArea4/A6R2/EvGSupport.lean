/-
# `A6R2.EvGSupport` — the signed-box variance API (restored)

The source modules `Submission/Work/FIArea4/S15red/{relSum_bound,EvGDefs,EvarCls_quadrantArr,
quadPairC_eq_qPartC,clsSum2_quadSum,sum_range_mul_unit,EvG_le_Evar}.lean` and
`Submission/Work/FIArea4/EvarG_le_quadEvar.lean` are no longer present in the workspace (only
their compiled artifacts survive), so their *contents* — which are what the round-6 §15
reduction needs — are collected here verbatim, together with the shrunk-box four-quadrant
reduction `Work.S15hybrid.EvarG_le_quad_shrunk`.

Nothing here is new mathematics: it is the class decomposition of the signed box `gBox R`, the
class Cauchy–Schwarz with a bounded class factor, the four-quadrant reduction
`EvG_le_Evar` of the signed-box variance to the positive-box variance `FIPlan.Evar`, and the
identification of the `m`-dependent Jacobi factor with the one built into `Evar`
(`EvarG_le_quadEvar`).
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15delta
import Submission.Work.FIArea4.p14_uncond
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.pair_sum_le_Evar
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea4.S15expSumDefs
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.S15red.EvarG_filtered_strU_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `S15red.relSum_bound`: the variance half of FI §15 for the relaxed sum

The target is `‖relSum Pa X j β u t ℓ‖ ≤ C (log N + 1)^24 (Br Pa X * En Pa β)` uniformly, for
primitive box coefficients `β` and `1 ≤ X ≤ N^{1/9}`.

The proof follows FI §15.  The elementary layer built here is

* `clsF`/`clsSum2`/`EvG`: the classes of the *signed* box (`gBox R`) modulo `m` for points with
  `Re` coprime to `m`, the class sums of an array, and the class variance;
* `pairSum_classFactor_le`: **the class Cauchy–Schwarz with an arbitrary bounded class factor**,
  the form needed when the kernel of the pair sum is not exactly the frozen kernel of
  `pairSumG_le_EvarG` (FI §15 produces the kernel `J(Δ, ed)`, whose odd part matches the frozen
  kernel but whose `2`-adic part contributes an extra class factor);
* `EvG_le_Evar`: the reduction of the *signed*-box variance to the *positive*-box variance
  `Work.FIPlan.Evar` to which FI Proposition 14.1 applies (splitting the four sign combinations
  of `Re`/`Im`; the `Im = 0` slice is empty because `±1` is outside the polar box).
-/

namespace Work.FIArea4.S15red

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The class decomposition of the signed box -/

/-- The class of index `a` of the signed box `gBox R` modulo `m`: the points with `Re z` coprime
to `m` and `Im z ≡ a · Re z (mod m)`. -/
def clsF (R : ℤ) (m : ℕ) (a : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox R).filter
    (fun z => Nat.Coprime z.re.natAbs m ∧
      ((z.im : ZMod m) = (a : ZMod m) * (z.re : ZMod m)))

@[simp] lemma mem_clsF {R : ℤ} {m a : ℕ} {z : GaussianInt} :
    z ∈ clsF R m a ↔ z ∈ Work.FIPlan.gBox R ∧ Nat.Coprime z.re.natAbs m ∧
      ((z.im : ZMod m) = (a : ZMod m) * (z.re : ZMod m)) := by
  simp [clsF]

/-- The class sum of an array `u` on the signed box. -/
def clsSum2 (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) (a : ℕ) : ℂ :=
  ∑ z ∈ clsF R m a, u z

/-- The class variance of an array on the signed box. -/
def EvG (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) : ℝ :=
  ∑ a ∈ Finset.range m, Complex.normSq (clsSum2 R m u a)

/-- `Re z` is a unit modulo `m` when `(Re z, m) = 1`. -/
lemma cls_isUnit (m : ℕ) (z : ℤ) (h : Nat.Coprime z.natAbs m) :
    IsUnit ((z : ℤ) : ZMod m) := by
  have h2 : IsUnit (((z.natAbs : ℤ)) : ZMod m) := by
    rw [Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime z.natAbs m).mpr h
  rcases z.natAbs_eq with hz | hz
  · rw [hz]; exact h2
  · rw [hz]; simpa using h2.neg

/-- Every point of the box whose real part is coprime to `m` lies in a class `clsF R m a`, `a < m`. -/
lemma exists_mem_clsF {R : ℤ} {m : ℕ} {z : GaussianInt}
    (hm : 1 ≤ m) (hz : z ∈ Work.FIPlan.gBox R) (hc : Nat.Coprime z.re.natAbs m) :
    ∃ a ∈ Finset.range m, z ∈ clsF R m a := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨u, hu⟩ := cls_isUnit m z.re hc
  refine ⟨((z.im : ZMod m) * (((u⁻¹ : (ZMod m)ˣ)) : ZMod m)).val,
    Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
  rw [mem_clsF]
  refine ⟨hz, hc, ?_⟩
  have hcoe : ((z.re : ℤ) : ZMod m) = ((u : (ZMod m)ˣ) : ZMod m) := hu.symm
  rw [ZMod.natCast_zmod_val]
  rw [mul_assoc, hcoe, Units.inv_mul, mul_one]

/-- The classes cover the part of the box with `(Re z, m) = 1`. -/
lemma clsF_cover (R : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    (Work.FIPlan.gBox R).filter (fun z => Nat.Coprime z.re.natAbs m)
      = (Finset.range m).biUnion (clsF R m) := by
  ext z
  rw [Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hz, hc⟩
    exact exists_mem_clsF hm hz hc
  · rintro ⟨a, _, hz⟩
    exact ⟨(mem_clsF.mp hz).1, (mem_clsF.mp hz).2.1⟩

/-- Distinct classes are disjoint. -/
lemma clsF_pairwiseDisjoint (R : ℤ) (m : ℕ) :
    (↑(Finset.range m) : Set ℕ).PairwiseDisjoint (clsF R m) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_range] at ha hb
  show Disjoint (clsF R m a) (clsF R m b)
  rw [Finset.disjoint_left]
  intro z hza hzb
  have hza' := mem_clsF.mp hza
  have hzb' := mem_clsF.mp hzb
  have h3 : (a : ZMod m) * (z.re : ZMod m) = (b : ZMod m) * (z.re : ZMod m) := by
    rw [← hza'.2.2, hzb'.2.2]
  have h4 : (a : ZMod m) = (b : ZMod m) := (cls_isUnit m z.re hza'.2.1).mul_right_cancel h3
  exact hab (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff a b m).mp h4) ha hb)

/-- Two points of one class satisfy `m ∣ Δ(z₁,z₂)`. -/
lemma clsF_delta_zero {R : ℤ} {m a : ℕ} {z1 z2 : GaussianInt}
    (h1 : z1 ∈ clsF R m a) (h2 : z2 ∈ clsF R m a) :
    (Work.FIPlan.Delta z1 z2 : ZMod m) = 0 := by
  have h1' := mem_clsF.mp h1
  have h2' := mem_clsF.mp h2
  have hD : ((Work.FIPlan.Delta z1 z2 : ℤ) : ZMod m)
      = (z1.re : ZMod m) * (z2.im : ZMod m) - (z2.re : ZMod m) * (z1.im : ZMod m) := by
    rw [Delta_eq]; push_cast; ring
  rw [hD, h2'.2.2, h1'.2.2]
  ring

/-- Conversely, a point of the box with `Re` coprime to `m` and `m ∣ Δ(z₁,z₂)` lies in the class
of `z₁`. -/
lemma mem_clsF_of_delta_zero {R : ℤ} {m a : ℕ} {z1 z2 : GaussianInt}
    (h1 : z1 ∈ clsF R m a) (hz2 : z2 ∈ Work.FIPlan.gBox R)
    (hc2 : Nat.Coprime z2.re.natAbs m) (hΔ : (Work.FIPlan.Delta z1 z2 : ZMod m) = 0) :
    z2 ∈ clsF R m a := by
  have h1' := mem_clsF.mp h1
  rw [mem_clsF]
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
  exact (cls_isUnit m z1.re h1'.2.1).mul_left_cancel hm

/-- A double sum of a constant times `A z₁ · conj(B z₂)` factors. -/
lemma sum_const_mul_star {ι : Type*} (s t : Finset ι) (γ : ℂ) (A B : ι → ℂ) :
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
theorem pairSum_classFactor_le (R : ℤ) (m : ℕ) (hm : 1 ≤ m) (u v : GaussianInt → ℂ)
    (F : ZMod m → ℂ) (hF : ∀ a, ‖F a‖ ≤ 1)
    (hu : ∀ z : GaussianInt, u z ≠ 0 → Nat.Coprime z.re.natAbs m)
    (hv : ∀ z : GaussianInt, v z ≠ 0 → Nat.Coprime z.re.natAbs m) :
    ‖∑ z1 ∈ Work.FIPlan.gBox R, ∑ z2 ∈ Work.FIPlan.gBox R,
        (if (Work.FIPlan.Delta z1 z2 : ZMod m) = 0 then
          F ((z1.im : ZMod m) * ((z1.re : ZMod m))⁻¹) * (u z1 * star (v z2)) else 0)‖
      ≤ Real.sqrt (EvG R m u) * Real.sqrt (EvG R m v) := by
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
  have hcls : ∀ a ∈ Finset.range m, ∀ z1 ∈ clsF R m a, ∀ z2 ∈ clsF R m a,
      G z1 z2 = F ((a : ZMod m)) * (u z1 * star (v z2)) := by
    intro a ha z1 hz1 z2 hz2
    have hz1' := mem_clsF.mp hz1
    have hd : (Work.FIPlan.Delta z1 z2 : ZMod m) = 0 := clsF_delta_zero hz1 hz2
    simp only [hG]
    rw [if_pos hd]
    have hu1 := cls_isUnit m z1.re hz1'.2.1
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
      = ∑ a ∈ Finset.range m, ∑ z1 ∈ clsF R m a, ∑ z2 ∈ clsF R m a, G z1 z2 := by
    rw [clsF_cover R m hm]
    rw [Finset.sum_biUnion (f := fun z1 => ∑ z2 ∈ _, G z1 z2)
      (clsF_pairwiseDisjoint R m)]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun z1 hz1 => ?_)
    rw [Finset.sum_biUnion (f := fun z2 => G z1 z2) (clsF_pairwiseDisjoint R m)]
    refine Finset.sum_eq_single a (fun b hb hba => ?_) (fun ha' => absurd ha ha')
    refine Finset.sum_eq_zero (fun z2 hz2 => ?_)
    have hz2' := mem_clsF.mp hz2
    simp only [hG]
    by_cases hΔ : (Work.FIPlan.Delta z1 z2 : ZMod m) = 0
    · rw [if_pos hΔ]
      exfalso
      have hmem : z2 ∈ clsF R m a := mem_clsF_of_delta_zero hz1 hz2'.1 hz2'.2.1 hΔ
      have hdisj := clsF_pairwiseDisjoint R m ha hb (fun h : a = b => hba h.symm)
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
          F (a : ZMod m) * clsSum2 R m u a * star (clsSum2 R m v a) := by
    rw [step0, step1]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.sum_congr rfl (fun z1 hz1 =>
      Finset.sum_congr rfl (fun z2 hz2 => hcls a ha z1 hz1 z2 hz2))]
    simp only [clsSum2]
    rw [sum_const_mul_star]
  rw [hdecomp]
  -- Cauchy–Schwarz on the classes
  have hnorm : ∀ a : ℕ, ‖F (a : ZMod m)‖ ≤ 1 := fun a => hF _
  have hmain : ‖∑ a ∈ Finset.range m, F (a : ZMod m) * clsSum2 R m u a * star (clsSum2 R m v a)‖
      ≤ ∑ a ∈ Finset.range m, ‖clsSum2 R m u a‖ * ‖clsSum2 R m v a‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun a _ => ?_))
    calc ‖F (a : ZMod m) * clsSum2 R m u a * star (clsSum2 R m v a)‖
        = ‖F (a : ZMod m)‖ * (‖clsSum2 R m u a‖ * ‖clsSum2 R m v a‖) := by
          rw [norm_mul, norm_mul, norm_star]; ring
      _ ≤ 1 * (‖clsSum2 R m u a‖ * ‖clsSum2 R m v a‖) :=
          mul_le_mul_of_nonneg_right (hnorm a) (by positivity)
      _ = ‖clsSum2 R m u a‖ * ‖clsSum2 R m v a‖ := by ring
  refine le_trans hmain ?_
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range m)
    (fun a => ‖clsSum2 R m u a‖) (fun a => ‖clsSum2 R m v a‖)
  simpa only [EvG, Complex.normSq_eq_norm_sq] using this

/-! ## The quadrant arrays (for the reduction of the signed-box variance) -/

/-- The four sign-combination arrays of the signed box: the array `u` read in the quadrant
`Re = ε r`, `Im = η s` (`r, s ≥ 1`), multiplied by `(r | oddPart m)` so that the class sums of
`Work.FIPlan.Evar` (which carry that factor) reproduce the class sums of `EvG`. -/
def quadrantArr (R m : ℕ) (u : GaussianInt → ℂ) (ε η : ℤ) : ℕ → ℕ → ℂ :=
  fun r s => if r ∈ Finset.Icc 1 R ∧ s ∈ Finset.Icc 1 R ∧ Nat.Coprime r m then
      u (⟨ε * (r : ℤ), η * (s : ℤ)⟩ : GaussianInt)
        * ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart m) : ℤ) : ℂ)
    else 0


/-! ## The `e`-stratification vocabulary of FI §15

In the `(d,e)`-stratum of FI (15.1)–(15.2) the pair `(z₁,z₂)` of the box has
`(d, Re z₁) = (d, Re z₂) = e`, so `Re z_i = e·ρ_i`; writing `w_i = ρ_i + i·Im z_i`,
the kernel `(Re z̄₁z₂ | d)` factorises as the class factor `(e² + a² | d')`
(`d' = d/e`, `a ≡ Im w · Re w⁻¹ (mod 4d')`) times the per-variable factors
`(Im w_i | e)·(Re w_i | d')`, and the phases `e^{iℓ(α₂-α₁)}`, `e(u x)`, `y^{it}`
factor into a `z₁`-side and a `z₂`-side tilt.  The lemmas below set up that
vocabulary. -/

/-- The `e`-dilate `e·Re w + i·Im w` (the pair variable `z = er + is` of (15.2)). -/
def scalePt (e : ℕ) (w : GaussianInt) : GaussianInt := ⟨(e : ℤ) * w.re, w.im⟩

/-- The `z₁`-side tilt of `sepDterm`: `e^{-iℓ·arg z}·e(u·Im z/Re z)·|Re z|^{it}`. -/
def tiltA (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) : ℂ :=
  Complex.exp (-(Complex.I * (ℓ : ℂ) * ((Complex.arg z.toComplex : ℝ) : ℂ)))
    * Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * ((z.im : ℝ) / (z.re : ℝ) : ℝ)))
    * (((z.re.natAbs : ℝ) : ℂ)) ^ (Complex.I * (t : ℂ))

/-- The `z₂`-side tilt of `sepDterm`: `e^{-iℓ·arg z}·e(u·Im z/Re z)·|Re z|^{-it}`; its conjugate
carries the `z₂`-side factors `e^{iℓ·arg z}·e(-u·Im z/Re z)·|Re z|^{it}` of `sepDterm`. -/
def tiltB (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) : ℂ :=
  Complex.exp (-(Complex.I * (ℓ : ℂ) * ((Complex.arg z.toComplex : ℝ) : ℂ)))
    * Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * ((z.im : ℝ) / (z.re : ℝ) : ℝ)))
    * (((z.re.natAbs : ℝ) : ℂ)) ^ (-(Complex.I * (t : ℂ)))

/-- The pair-independent constant of the `(d,e)`-stratum: `(φ(d)/d)·(4X2^jd)^{-it}`. -/
def relConst (X j d : ℕ) (t : ℝ) : ℂ :=
  (((Nat.totient d : ℝ) / (d : ℝ) : ℝ) : ℂ)
    * (((((4 * (X : ℝ) * (2 : ℝ) ^ j * (d : ℝ))⁻¹ : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ)))

/-- The class factor `(e² + a² | d')` of the `(d,e)`-stratum. -/
def relClsFac (e d' : ℕ) (a : ZMod (4 * d')) : ℂ :=
  ((jacobiSym ((e : ℤ) ^ 2 + ((a.val : ℤ)) ^ 2) d' : ℤ) : ℂ)

/-- The `z₁`-array of the `(d,e)`-stratum, as a function of `w₁ = ρ₁ + i·Im z₁`. -/
def relArrA (e d' : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (w : GaussianInt) : ℂ :=
  β (scalePt e w) * tiltA u t ℓ (scalePt e w)
    * ((jacobiSym w.im e : ℤ) : ℂ) * ((jacobiSym w.re d' : ℤ) : ℂ)

/-- The `z₂`-array of the `(d,e)`-stratum: it stores `conj(β)·conj(tiltB)`, so that the pair sum
is `relArrA e d' β u t ℓ w₁ · relArrB e d' β u t ℓ w₂` (no outer conjugate). -/
def relArrB (e d' : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (w : GaussianInt) : ℂ :=
  star (β (scalePt e w) * tiltB u t ℓ (scalePt e w))
    * ((jacobiSym w.im e : ℤ) : ℂ) * ((jacobiSym w.re d' : ℤ) : ℂ)

/-! ## The `(d,e)`-strata of the relaxed sum -/

/-- The `(d,e)`-stratum summand read in the variables `w = ρ + i·Im z` (`z = e·ρ + i·Im z`):
the stratum conditions in the `w`-coordinates. -/
def wGuard (Pa : Work.FITop.Params) (X j d e : ℕ) (w1 w2 : GaussianInt) : Prop :=
  scalePt e w1 ∈ Work.FITop.boxN Pa ∧ scalePt e w2 ∈ Work.FITop.boxN Pa
    ∧ Nat.Coprime w1.re.natAbs (d / e) ∧ Nat.Coprime w2.re.natAbs (d / e)
    ∧ X < d ∧ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2
    ∧ 0 < Work.FIPlan.absDelta w1 w2
    ∧ Work.FIPlan.GaussCoprime (scalePt e w1) (scalePt e w2)

/-- `Finset.sum_product` with the explicit `Finset.product`; convenient because the
`×ˢ` notation and `Finset.product` are definitionally but not syntactically equal. -/
private lemma sum_product_prod {γ α β : Type*} [AddCommMonoid β] (s : Finset γ) (t : Finset α)
    (f : γ × α → β) : ∑ x ∈ s.product t, f x = ∑ x ∈ s, ∑ y ∈ t, f (x, y) := by
  change ∑ x ∈ s ×ˢ t, f x = ∑ x ∈ s, ∑ y ∈ t, f (x, y)
  rw [Finset.sum_product]

/-- **Regrouping a sum by the fibers of a map.**  If every `a ∈ s` with `C a` satisfies
`g a ∈ (Icc 1 d).filter (· ∣ d)`, then the sum over `s` of the `C`-restricted terms equals the
sum over the divisors `e ∈ [1,d]` of `d` of the `(C ∧ g = e)`-restricted terms. -/
private lemma sum_eq_sum_fibers {α M : Type*} [AddCommMonoid M] (s : Finset α) (d : ℕ)
    (C : α → Prop) [DecidablePred C] (g : α → ℕ) (f : α → M)
    (hg : ∀ a ∈ s, C a → g a ∈ (Finset.Icc 1 d).filter (fun e => e ∣ d)) :
    (∑ a ∈ s, if C a then f a else 0)
      = ∑ e ∈ (Finset.Icc 1 d).filter (fun e => e ∣ d),
          ∑ a ∈ s, if C a ∧ g a = e then f a else 0 := by
  classical
  have hterm : ∀ e, (∑ a ∈ s, if C a ∧ g a = e then f a else 0)
      = ∑ a ∈ s.filter C, if g a = e then f a else 0 := by
    intro e
    rw [← Finset.sum_filter (p := fun a => C a ∧ g a = e) (f := f)]
    rw [← Finset.sum_filter (s := s.filter C) (p := fun a => g a = e) (f := f)]
    rw [Finset.filter_filter]
  have hfib' : (∑ e ∈ (Finset.Icc 1 d).filter (fun e => e ∣ d),
        ∑ a ∈ s.filter C, if g a = e then f a else 0) = ∑ a ∈ s.filter C, f a := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s.filter C)
      (t := (Finset.Icc 1 d).filter (fun e => e ∣ d)) (g := g)
      (fun a ha => hg a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2) f]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    exact (Finset.sum_filter (s := s.filter C) (p := fun a => g a = e) (f := f)).symm
  rw [← Finset.sum_filter (s := s) (p := C) (f := f)]
  rw [Finset.sum_congr rfl (fun e _ => hterm e)]
  exact hfib'.symm

-- inlined from Submission/Work/FIArea4/S15red/EvGDefs.lean

/-!
# `S15red.EvGDefs`: vocabulary for the signed-box variance `EvG`

The target of `S15red.EvG_le_Evar` reduces the variance `EvG R m u` of the *signed* box
`Work.FIPlan.gBox R` (sum of the squared moduli of the class sums `clsF R m a`) to four copies of
the *positive* quadrant variance `Work.FIPlan.Evar`, on which FI Proposition 14.1 (Lemma 11.4)
applies.

This module contains the vocabulary of that reduction:

* `clsC R m c`: the class of the signed box indexed by a residue `c : ZMod m` (the same class as
  `clsF R m a` with `c = a`);
* `qPartC R m u ε η c`: the class sum of `u` over the quadrant `sign(Re) = ε`, `sign(Im) = η`;
* `quadPairC R m c`: the pairs `(r,s)` of the positive box `[1,R] × [1,R]` with `r` coprime to `m`
  and `s ≡ r·c (mod m)` — the shape in which the class sums of `Work.FIPlan.Evar` appear;
* `Q`: the four sign combinations.
-/





/-! ## The class of the signed box indexed by a residue -/

/-- The class of index `c : ZMod m` of the signed box `gBox R`: the points with `Re z` coprime
to `m` and `Im z ≡ c · Re z (mod m)`.  This is `clsF R m a` with `c = a`. -/
def clsC (R : ℤ) (m : ℕ) (c : ZMod m) : Finset GaussianInt :=
  (Work.FIPlan.gBox R).filter
    (fun z => Nat.Coprime z.re.natAbs m ∧ (z.im : ZMod m) = c * (z.re : ZMod m))

@[simp] lemma mem_clsC {R : ℤ} {m : ℕ} {c : ZMod m} {z : GaussianInt} :
    z ∈ clsC R m c ↔ z ∈ Work.FIPlan.gBox R ∧ Nat.Coprime z.re.natAbs m ∧
      (z.im : ZMod m) = c * (z.re : ZMod m) := by
  simp [clsC]

/-- `clsF` is `clsC` indexed by the residue of `a`. -/
lemma clsF_eq_clsC (R : ℤ) (m : ℕ) (a : ℕ) : clsF R m a = clsC R m (a : ZMod m) := rfl

/-- The class sum of `u` over the quadrant `sign(Re) = ε`, `sign(Im) = η`. -/
def qPartC (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) (ε η : ℤ) (c : ZMod m) : ℂ :=
  ∑ z ∈ (clsC R m c).filter (fun z => 0 < ε * z.re ∧ 0 < η * z.im), u z

/-! ## The pairs of the positive quadrant -/

/-- The pairs `(r,s)` of the positive box `[1,R] × [1,R]` with `r` coprime to `m` and
`s ≡ r·c (mod m)`: the pairs of the class `c` of the quadrant `Re = ε·r`, `Im = η·s`. -/
def quadPairC (R m : ℕ) (c : ZMod m) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).filter
    (fun p => Nat.Coprime p.1 m ∧ (p.2 : ZMod m) = (p.1 : ZMod m) * c)

@[simp] lemma mem_quadPairC {R m : ℕ} {c : ZMod m} {p : ℕ × ℕ} :
    p ∈ quadPairC R m c ↔ p.1 ∈ Finset.Icc 1 R ∧ p.2 ∈ Finset.Icc 1 R ∧
      Nat.Coprime p.1 m ∧ (p.2 : ZMod m) = (p.1 : ZMod m) * c := by
  simp only [quadPairC, Finset.mem_filter, Finset.mem_product]
  tauto

/-! ## The four sign combinations -/

/-- The four sign combinations `(ε,η)` of the quadrants. -/
def Q : Finset (ℤ × ℤ) := {(1, 1), (1, -1), (-1, 1), (-1, -1)}

@[simp] lemma mem_Q {p : ℤ × ℤ} :
    p ∈ Q ↔ p = (1, 1) ∨ p = (1, -1) ∨ p = (-1, 1) ∨ p = (-1, -1) := by
  simp [Q]

lemma Q_spec {p : ℤ × ℤ} (hp : p ∈ Q) : (p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1) := by
  simp only [mem_Q] at hp
  rcases hp with h | h | h | h <;> rw [h] <;> simp

lemma sum_Q_four {M : Type*} [AddCommMonoid M] (f : ℤ → ℤ → M) :
    (∑ p ∈ Q, f p.1 p.2) = f 1 1 + f 1 (-1) + f (-1) 1 + f (-1) (-1) := by
  rw [Q, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-! ## Membership in the box, elementary -/

/-- Membership in the box `gBox R`, in coordinates. -/
lemma mem_gBox_iff {R : ℤ} {w : GaussianInt} :
    w ∈ Work.FIPlan.gBox R ↔ w.re ∈ Finset.Icc (-R) R ∧ w.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(w.re, w.im), Finset.mem_product.mpr ⟨h1, h2⟩, ?_⟩
    cases w
    rfl

lemma gBox_re_mem {R : ℤ} {w : GaussianInt} (hw : w ∈ Work.FIPlan.gBox R) :
    w.re ∈ Finset.Icc (-R) R := (mem_gBox_iff.mp hw).1

lemma gBox_im_mem {R : ℤ} {w : GaussianInt} (hw : w ∈ Work.FIPlan.gBox R) :
    w.im ∈ Finset.Icc (-R) R := (mem_gBox_iff.mp hw).2

lemma mem_gBox_of {R : ℤ} {w : GaussianInt} (h1 : w.re ∈ Finset.Icc (-R) R)
    (h2 : w.im ∈ Finset.Icc (-R) R) : w ∈ Work.FIPlan.gBox R := mem_gBox_iff.mpr ⟨h1, h2⟩
-- inlined from Submission/Work/FIArea4/S15red/sum_range_mul_unit.lean


/-- Multiplication by a unit of `ZMod m` permutes the residues, so summing any
function over `b ↦ k * b` for `b ∈ {0, …, m-1}` is the same as summing over `b`. -/
theorem sum_range_mul_unit (m : ℕ) {M : Type*} [AddCommMonoid M] (k : ZMod m) (hk : IsUnit k)
    (G : ZMod m → M) :
    (∑ b ∈ Finset.range m, G (k * (b : ZMod m))) = ∑ b ∈ Finset.range m, G (b : ZMod m) := by
  rcases m with _ | n
  · simp
  · obtain ⟨u, rfl⟩ := hk
    -- Reindex `b ∈ range (n+1)` by its image under `x ↦ ↑u * x`, read back through `ZMod.val`.
    refine Finset.sum_bij
      (fun (a : ℕ) (_ : a ∈ Finset.range (n + 1)) => (↑u * (a : ZMod (n + 1))).val) ?_ ?_ ?_ ?_
    · intro a _
      exact Finset.mem_range.mpr (ZMod.val_lt _)
    · -- injectivity
      intro a₁ ha₁ a₂ ha₂ h
      have e1 : ((↑u * (a₁ : ZMod (n + 1))).val : ZMod (n + 1)) = ↑u * (a₁ : ZMod (n + 1)) :=
        ZMod.natCast_zmod_val _
      have e2 : ((↑u * (a₂ : ZMod (n + 1))).val : ZMod (n + 1)) = ↑u * (a₂ : ZMod (n + 1)) :=
        ZMod.natCast_zmod_val _
      have hmul : ↑u * (a₁ : ZMod (n + 1)) = ↑u * (a₂ : ZMod (n + 1)) := by rw [← e1, ← e2, h]
      have h2 : (a₁ : ZMod (n + 1)) = (a₂ : ZMod (n + 1)) :=
        IsUnit.mul_right_injective (Units.isUnit u) hmul
      have h1 : ((a₁ : ZMod (n + 1))).val = a₁ :=
        ZMod.val_natCast_of_lt (Finset.mem_range.mp ha₁)
      have h3 : ((a₂ : ZMod (n + 1))).val = a₂ :=
        ZMod.val_natCast_of_lt (Finset.mem_range.mp ha₂)
      rw [← h1, ← h3, h2]
    · -- surjectivity
      intro b hb
      refine ⟨((↑u⁻¹ : ZMod (n + 1)) * (b : ZMod (n + 1))).val,
        Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
      have hthis : (↑u * (((↑u⁻¹ : ZMod (n + 1)) * (b : ZMod (n + 1))).val : ZMod (n + 1))) =
          (b : ZMod (n + 1)) := by
        rw [ZMod.natCast_zmod_val]
        simp
      rw [hthis, ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)]
    · -- the two summands agree on the matched index
      intro a _
      exact congrArg G (ZMod.natCast_zmod_val (n := n + 1) (↑u * (a : ZMod (n + 1)))).symm
-- inlined from Submission/Work/FIArea4/S15red/quadPairC_eq_qPartC.lean

/-!
# `S15red.quadPairC_eq_qPartC`: reindexing the pair class onto the signed quadrant

The class sum `qPartC` of the signed quadrant `sign(Re) = ε`, `sign(Im) = η` of the class
`clsC (R:ℤ) m c'` can be computed by the *positive* pairs `quadPairC R m c`: the pairs
`(r,s)` of the box `[1,R] × [1,R]` with `s ≡ r c (mod m)`, sent to the Gaussian integer
`⟨ε r, η s⟩`.  This file proves the bijection and hence the identity, with
`c' = ε η c`.
-/





/-! ## The sign map -/

/-- The map `(r,s) ↦ ⟨ε r, η s⟩` carrying a positive pair to the signed Gaussian integer. -/
def sgnPhi (ε η : ℤ) (p : ℕ × ℕ) : GaussianInt := ⟨ε * (p.1 : ℤ), η * (p.2 : ℤ)⟩

lemma sgn_abs_eq_one (ε : ℤ) (hε : ε = 1 ∨ ε = -1) : |ε| = 1 := by
  rcases hε with h | h <;> simp [h]

lemma sgn_sq_one (ε : ℤ) (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases hε with h | h <;> simp [h]

lemma sgn_natAbs_eq_one (ε : ℤ) (hε : ε = 1 ∨ ε = -1) : ε.natAbs = 1 := by
  rcases hε with h | h <;> simp [h]

/-! ## The forward direction -/

/-- `± r` lies in the integer interval when `r` does. -/
lemma mem_Icc_of_cast {R : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ}
    (hr : r ∈ Finset.Icc 1 R) : ε * (r : ℤ) ∈ Finset.Icc (-(R:ℤ)) (R:ℤ) := by
  rw [Finset.mem_Icc]
  have hr' : (1:ℤ) ≤ (r:ℤ) ∧ (r:ℤ) ≤ (R:ℤ) := by
    rw [Finset.mem_Icc] at hr; exact_mod_cast hr
  have h0 : (0:ℤ) ≤ (r:ℤ) := by linarith
  have habs : |ε * (r:ℤ)| = (r:ℤ) := by
    rw [abs_mul, sgn_abs_eq_one ε hε, one_mul, abs_of_nonneg h0]
  have hb : |ε * (r:ℤ)| ≤ (R:ℤ) := by rw [habs]; exact hr'.2
  exact abs_le.mp hb

/-- The sign map sends `quadPairC R m c` into the signed quadrant of the class `ε η c`. -/
lemma sgnPhi_mem (R m : ℕ) (c : ZMod m) (ε η : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) {p : ℕ × ℕ}
    (hp : p ∈ quadPairC R m c) :
    sgnPhi ε η p ∈ (clsC (R:ℤ) m ((ε : ZMod m) * (η : ZMod m) * c)).filter
      (fun z => 0 < ε * z.re ∧ 0 < η * z.im) := by
  obtain ⟨hp1, hp2, hcop, hcong⟩ := mem_quadPairC.mp hp
  rw [Finset.mem_filter, mem_clsC, mem_gBox_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact mem_Icc_of_cast hε hp1
  · exact mem_Icc_of_cast hη hp2
  · have h : (sgnPhi ε η p).re.natAbs = p.1 := by
      simp only [sgnPhi]
      rw [Int.natAbs_mul, Int.natAbs_natCast, sgn_natAbs_eq_one ε hε, one_mul]
    rw [h]; exact hcop
  · simp only [sgnPhi]
    push_cast
    rcases hε with hε | hε <;>
      simp only [hε, Int.cast_one, Int.cast_neg, neg_mul] <;>
      rw [hcong] <;> ring
  · simp only [sgnPhi]
    rw [← mul_assoc, sgn_sq_one ε hε, one_mul]
    have : (1:ℤ) ≤ (p.1:ℤ) := by rw [Finset.mem_Icc] at hp1; exact_mod_cast hp1.1
    linarith
  · simp only [sgnPhi]
    rw [← mul_assoc, sgn_sq_one η hη, one_mul]
    have : (1:ℤ) ≤ (p.2:ℤ) := by rw [Finset.mem_Icc] at hp2; exact_mod_cast hp2.1
    linarith

/-! ## Injectivity -/

lemma sgnPhi_inj (ε η : ℤ) (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) :
    Function.Injective (sgnPhi ε η) := by
  intro p q hpq
  have h1 : ε * (p.1:ℤ) = ε * (q.1:ℤ) := by
    simpa [sgnPhi] using congrArg Zsqrtd.re hpq
  have h2 : η * (p.2:ℤ) = η * (q.2:ℤ) := by
    simpa [sgnPhi] using congrArg Zsqrtd.im hpq
  have hε0 : ε ≠ 0 := by rcases hε with h|h <;> simp [h]
  have hη0 : η ≠ 0 := by rcases hη with h|h <;> simp [h]
  have h1' : (p.1:ℤ) = (q.1:ℤ) := mul_left_cancel₀ hε0 h1
  have h2' : (p.2:ℤ) = (q.2:ℤ) := mul_left_cancel₀ hη0 h2
  exact Prod.ext (by exact_mod_cast h1') (by exact_mod_cast h2')

/-! ## Surjectivity -/

/-- If `0 < ε z` then `(ε z).toNat` recovers `|z|` as a natural of the box range. -/
lemma in_Icc_of_sign {R : ℕ} {z : ℤ} (hz : z ∈ Finset.Icc (-(R:ℤ)) (R:ℤ)) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hpos : 0 < ε * z) : (ε * z).toNat ∈ Finset.Icc 1 R := by
  rw [Finset.mem_Icc]
  have hz' : -(R:ℤ) ≤ z ∧ z ≤ (R:ℤ) := by rw [Finset.mem_Icc] at hz; exact hz
  have hcast : (((ε * z).toNat : ℕ) : ℤ) = ε * z := Int.toNat_of_nonneg (le_of_lt hpos)
  have habs : |ε * z| = |z| := by rw [abs_mul, sgn_abs_eq_one ε hε, one_mul]
  have hzabs : |z| ≤ (R:ℤ) := abs_le.mpr ⟨hz'.1, hz'.2⟩
  have hle : ((ε * z).toNat : ℤ) ≤ (R:ℤ) := by
    rw [hcast]
    calc ε * z ≤ |ε * z| := le_abs_self _
      _ = |z| := habs
      _ ≤ (R:ℤ) := hzabs
  constructor
  · have : (0:ℤ) < ((ε * z).toNat : ℤ) := by rw [hcast]; exact hpos
    omega
  · omega

/-- Every point of the signed quadrant of the class `ε η c` is the image of a unique pair
of `quadPairC R m c`. -/
lemma sgnPhi_surj (R m : ℕ) (c : ZMod m) (ε η : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) {z : GaussianInt}
    (hz : z ∈ (clsC (R:ℤ) m ((ε : ZMod m) * (η : ZMod m) * c)).filter
      (fun z => 0 < ε * z.re ∧ 0 < η * z.im)) :
    ∃ p, p ∈ quadPairC R m c ∧ sgnPhi ε η p = z := by
  rw [Finset.mem_filter] at hz
  obtain ⟨hzc, hzsre, hzsim⟩ := hz
  rw [mem_clsC, mem_gBox_iff] at hzc
  obtain ⟨⟨hzre, hzim⟩, hzcop, hzcong⟩ := hzc
  have hre : (((ε * z.re).toNat : ℕ) : ℤ) = ε * z.re := Int.toNat_of_nonneg (le_of_lt hzsre)
  have him : (((η * z.im).toNat : ℕ) : ℤ) = η * z.im := Int.toNat_of_nonneg (le_of_lt hzsim)
  refine ⟨((ε * z.re).toNat, (η * z.im).toNat), ?_, ?_⟩
  · rw [mem_quadPairC]
    refine ⟨in_Icc_of_sign hzre ε hε hzsre, in_Icc_of_sign hzim η hη hzsim, ?_, ?_⟩
    · have hp1n : (ε * z.re).toNat = z.re.natAbs := by
        have := congrArg Int.natAbs hre
        rw [Int.natAbs_natCast, Int.natAbs_mul, sgn_natAbs_eq_one ε hε, one_mul] at this
        exact this
      rw [hp1n]; exact hzcop
    · have e1 : (((η * z.im).toNat : ℕ) : ZMod m) = (η : ZMod m) * (z.im : ZMod m) := by
        rw [← Int.cast_natCast, him, Int.cast_mul]
      have e2 : (((ε * z.re).toNat : ℕ) : ZMod m) = (ε : ZMod m) * (z.re : ZMod m) := by
        rw [← Int.cast_natCast, hre, Int.cast_mul]
      rw [e1, e2, hzcong]
      rcases hη with hη | hη <;>
        simp only [hη, Int.cast_one, Int.cast_neg, neg_mul, one_mul] <;> ring
  · apply Zsqrtd.ext
    · simp only [sgnPhi]
      rw [hre, ← mul_assoc, sgn_sq_one ε hε, one_mul]
    · simp only [sgnPhi]
      rw [him, ← mul_assoc, sgn_sq_one η hη, one_mul]

/-! ## The reindexing -/

theorem quadPairC_eq_qPartC (R m : ℕ) (u : GaussianInt → ℂ) (ε η : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) (c : ZMod m) :
    (∑ p ∈ quadPairC R m c, u ⟨ε * (p.1 : ℤ), η * (p.2 : ℤ)⟩)
      = qPartC (R : ℤ) m u ε η ((ε : ZMod m) * (η : ZMod m) * c) := by
  rw [qPartC]
  refine Finset.sum_bij (fun p _ => sgnPhi ε η p) (fun p hp => sgnPhi_mem R m c ε η hε hη hp)
    (fun a₁ _ a₂ _ h => sgnPhi_inj ε η hε hη h) ?_ (fun p _ => rfl)
  intro z hz
  obtain ⟨p, hp, hpe⟩ := sgnPhi_surj R m c ε η hε hη hz
  exact ⟨p, hp, hpe⟩
-- inlined from Submission/Work/FIArea4/S15red/EvarCls_quadrantArr.lean





/-!
# `EvarCls_quadrantArr`

The class sums of `Work.FIPlan.Evar` are indexed by the pairs `Work.FIArea4.EvarCls R S m a` and
carry the Jacobi weight `(r | oddPart m)`.  `quadrantArr` is the signed-box array multiplied by the
same weight, so on a pair of the box with `r` coprime to `m` the *two* Jacobi weights multiply to
`1`, leaving exactly the value `u` at the corresponding point of the quadrant.  Summing over the
residue class `b (mod m)` therefore collapses the `EvarCls`-sum to the plain `quadPairC`-sum.
-/

/-- On a pair `(r,s)` of the box `[1,R]²` with `r` coprime to `m`, the product of the two Jacobi
weights `(r | oddPart m)` — the one carried by `quadrantArr` and the one carried by the `Evar`
summand — is `1`, so the weighted term is exactly `u` at the quadrant point `⟨εr, ηs⟩`. -/
lemma quadrantArr_mul_jacobiSym (R m : ℕ) (u : GaussianInt → ℂ) (ε η : ℤ) {r s : ℕ}
    (hr : r ∈ Finset.Icc 1 R) (hs : s ∈ Finset.Icc 1 R) (hc : Nat.Coprime r m) :
    quadrantArr R m u ε η r s * (jacobiSym (r : ℤ) (Work.FIPlan.oddPart m) : ℂ)
      = u ⟨ε * (r : ℤ), η * (s : ℤ)⟩ := by
  have hcop : Nat.Coprime r (Work.FIPlan.oddPart m) :=
    hc.coprime_dvd_right (Work.FIArea4.oddPart_dvd m)
  have hg : (r : ℤ).gcd ((Work.FIPlan.oddPart m : ℕ) : ℤ) = 1 := by
    rw [Nat.Coprime, ← Int.gcd_natCast_natCast] at hcop
    exact hcop
  have hJ : jacobiSym (r : ℤ) (Work.FIPlan.oddPart m) ^ 2 = 1 := jacobiSym.sq_one hg
  have hJc : ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart m) : ℤ) : ℂ) ^ 2 = 1 := by
    rw [← Int.cast_pow, hJ]; norm_num
  rw [quadrantArr, if_pos ⟨hr, hs, hc⟩]
  rw [mul_assoc, ← sq, hJc, mul_one]

theorem EvarCls_quadrantArr (R m : ℕ) (u : GaussianInt → ℂ) (ε η : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) (b : ℕ) :
    (∑ p ∈ Work.FIArea4.EvarCls (R / 2 + 1) (R / 2 + 1) m b,
        quadrantArr R m u ε η p.1 p.2 * (jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart m) : ℂ))
      = ∑ p ∈ quadPairC R m (b : ZMod m), u ⟨ε * (p.1 : ℤ), η * (p.2 : ℤ)⟩ := by
  -- The `r`- and `s`-ranges of `EvarCls (R/2+1) (R/2+1) m b` contain the box `[1,R]`.
  have hle : R ≤ 2 * (R / 2 + 1) := by omega
  -- On the box the class of `EvarCls` is exactly `quadPairC`.
  have hset : (Work.FIArea4.EvarCls (R / 2 + 1) (R / 2 + 1) m b).filter
        (fun p => p.1 ∈ Finset.Icc 1 R ∧ p.2 ∈ Finset.Icc 1 R)
      = quadPairC R m (b : ZMod m) := by
    ext p
    constructor
    · intro h
      rw [Finset.mem_filter] at h
      obtain ⟨hE, hR1, hR2⟩ := h
      rw [Work.FIArea4.mem_EvarCls, Work.FIArea4.mem_EvarR] at hE
      obtain ⟨⟨-, hcop⟩, -, hcong⟩ := hE
      rw [mem_quadPairC]
      exact ⟨hR1, hR2, hcop, hcong⟩
    · intro h
      rw [mem_quadPairC] at h
      obtain ⟨hR1, hR2, hcop, hcong⟩ := h
      rw [Finset.mem_filter, Work.FIArea4.mem_EvarCls, Work.FIArea4.mem_EvarR]
      refine ⟨⟨⟨?_, hcop⟩, ?_, hcong⟩, hR1, hR2⟩
      · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hR1).1, (Finset.mem_Icc.mp hR1).2.trans hle⟩
      · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hR2).1, (Finset.mem_Icc.mp hR2).2.trans hle⟩
  -- The summand vanishes off the box, so the sum may be restricted to it.
  have hstep1 : (∑ p ∈ Work.FIArea4.EvarCls (R / 2 + 1) (R / 2 + 1) m b,
        quadrantArr R m u ε η p.1 p.2 * (jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart m) : ℂ))
      = ∑ p ∈ (Work.FIArea4.EvarCls (R / 2 + 1) (R / 2 + 1) m b).filter
          (fun p => p.1 ∈ Finset.Icc 1 R ∧ p.2 ∈ Finset.Icc 1 R),
        quadrantArr R m u ε η p.1 p.2 * (jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart m) : ℂ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hx hxnf
    have hq : ¬ (x.1 ∈ Finset.Icc 1 R ∧ x.2 ∈ Finset.Icc 1 R) := by
      intro hq; exact hxnf (Finset.mem_filter.mpr ⟨hx, hq⟩)
    have hq' : ¬ (x.1 ∈ Finset.Icc 1 R ∧ x.2 ∈ Finset.Icc 1 R ∧ Nat.Coprime x.1 m) := by
      rintro ⟨a, b, c⟩; exact hq ⟨a, b⟩
    rw [quadrantArr, if_neg hq', zero_mul]
  rw [hstep1, hset]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [mem_quadPairC] at hp
  obtain ⟨h1, h2, hcop, hcong⟩ := hp
  exact quadrantArr_mul_jacobiSym R m u ε η h1 h2 hcop
-- inlined from Submission/Work/FIArea4/S15red/clsSum2_quadSum.lean





/-- Pointwise sign bookkeeping: for a Gaussian integer with both coordinates nonzero, exactly one
of the four sign combinations `(ε,η) ∈ Q` makes both `ε·Re z > 0` and `η·Im z > 0`, so the
signed/quadrant decomposition of the indicator of `z` sums to `w`. -/
private lemma sum_Q_quadrant (z : GaussianInt) (w : ℂ) (hre : z.re ≠ 0) (him : z.im ≠ 0) :
    (∑ p ∈ Q, (if 0 < p.1 * z.re ∧ 0 < p.2 * z.im then w else 0)) = w := by
  rw [sum_Q_four (fun a b => if 0 < a * z.re ∧ 0 < b * z.im then w else 0)]
  simp only [one_mul, neg_one_mul]
  rcases lt_or_gt_of_ne hre with h | h <;> rcases lt_or_gt_of_ne him with h' | h'
  · rw [if_neg (by omega : ¬ (0 < z.re ∧ 0 < z.im)),
        if_neg (by omega : ¬ (0 < z.re ∧ 0 < -z.im)),
        if_neg (by omega : ¬ (0 < -z.re ∧ 0 < z.im)),
        if_pos (by omega : 0 < -z.re ∧ 0 < -z.im)]
    ring
  · rw [if_neg (by omega : ¬ (0 < z.re ∧ 0 < z.im)),
        if_neg (by omega : ¬ (0 < z.re ∧ 0 < -z.im)),
        if_pos (by omega : 0 < -z.re ∧ 0 < z.im),
        if_neg (by omega : ¬ (0 < -z.re ∧ 0 < -z.im))]
    ring
  · rw [if_neg (by omega : ¬ (0 < z.re ∧ 0 < z.im)),
        if_pos (by omega : 0 < z.re ∧ 0 < -z.im),
        if_neg (by omega : ¬ (0 < -z.re ∧ 0 < z.im)),
        if_neg (by omega : ¬ (0 < -z.re ∧ 0 < -z.im))]
    ring
  · rw [if_pos (by omega : 0 < z.re ∧ 0 < z.im),
        if_neg (by omega : ¬ (0 < z.re ∧ 0 < -z.im)),
        if_neg (by omega : ¬ (0 < -z.re ∧ 0 < z.im)),
        if_neg (by omega : ¬ (0 < -z.re ∧ 0 < -z.im))]
    ring

/-- The class sum of an array on the signed box is the sum of its four quadrant class sums. -/
theorem clsSum2_quadSum (R m : ℕ) (hm : 2 ≤ m) (u : GaussianInt → ℂ)
    (hu : ∀ z : GaussianInt, u z ≠ 0 → Nat.Coprime z.re.natAbs m)
    (h0 : ∀ z : GaussianInt, z.im = 0 → u z = 0) (a : ℕ) :
    clsSum2 (R : ℤ) m u a = ∑ p ∈ Q, qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m) := by
  rw [clsSum2, clsF_eq_clsC]
  -- every point of a class of the signed box has nonzero real part (its real part is a unit mod m)
  have hre : ∀ z : GaussianInt, z ∈ clsC (R : ℤ) m (a : ZMod m) → z.re ≠ 0 := by
    intro z hz h
    have hcp : Nat.Coprime z.re.natAbs m := (mem_clsC.mp hz).2.1
    rw [show z.re = 0 from h, Int.natAbs_zero, Nat.coprime_zero_left] at hcp
    omega
  -- pointwise replacement of `u z` by its four-quadrant sum
  have key : ∀ z : GaussianInt, z ∈ clsC (R : ℤ) m (a : ZMod m) →
      u z = ∑ p ∈ Q, (if 0 < p.1 * z.re ∧ 0 < p.2 * z.im then u z else 0) := by
    intro z hz
    rcases eq_or_ne z.im 0 with him | him
    · have hsum :
          (∑ p ∈ Q, (if 0 < p.1 * z.re ∧ 0 < p.2 * z.im then u z else 0)) = 0 := by
        simp [him]
      rw [hsum, h0 z him]
    · rw [sum_Q_quadrant z (u z) (hre z hz) him]
  calc ∑ z ∈ clsC (R : ℤ) m (a : ZMod m), u z
      = ∑ z ∈ clsC (R : ℤ) m (a : ZMod m),
          ∑ p ∈ Q, (if 0 < p.1 * z.re ∧ 0 < p.2 * z.im then u z else 0) :=
        Finset.sum_congr rfl (fun z hz => key z hz)
    _ = ∑ p ∈ Q, ∑ z ∈ clsC (R : ℤ) m (a : ZMod m),
          (if 0 < p.1 * z.re ∧ 0 < p.2 * z.im then u z else 0) := Finset.sum_comm
    _ = ∑ p ∈ Q, qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [qPartC, Finset.sum_filter]
-- inlined from Submission/Work/FIArea4/S15red/EvG_le_Evar.lean






/-- The `Work.FIPlan.Evar` class sums are the sums over the pair set `EvarCls`. -/
lemma Evar_eq_sum_EvarCls (R S d : ℕ) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S d α
      = ∑ a ∈ Finset.range d,
          Complex.normSq (∑ p ∈ Work.FIArea4.EvarCls R S d a,
            α p.1 p.2 * (jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart d) : ℂ)) := by
  rw [Work.FIPlan.Evar]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  rw [Work.FIArea4.EvarCls, Work.FIArea4.EvarR]
  refine (Work.FIArea4.sum_product_filter ((Finset.Icc 1 (2 * R)).filter (fun r => Nat.Coprime r d))
    (Finset.Icc 1 (2 * S))
    (fun p : ℕ × ℕ => (p.2 : ZMod d) = (p.1 : ZMod d) * (a : ZMod d))
    (fun p : ℕ × ℕ => α p.1 p.2 * (jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart d) : ℂ))).symm

lemma Q_card : Q.card = 4 := by
  rw [Q]
  simp [Finset.card_insert_of_notMem]

/-- Cauchy–Schwarz for a sum of `s.card` terms, in `normSq` form. -/
lemma normSq_sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) ≤ ((s.card : ℕ) : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
  rw [Complex.normSq_eq_norm_sq]
  calc ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((s.card : ℕ) : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = ((s.card : ℕ) : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
        simp only [Complex.normSq_eq_norm_sq]

/-- Cauchy–Schwarz for a sum of four terms. -/
lemma normSq_sum_le_card4 {ι : Type*} (s : Finset ι) (hs : s.card = 4) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) ≤ 4 * ∑ x ∈ s, Complex.normSq (f x) := by
  have h4 : ((s.card : ℕ) : ℝ) = 4 := by rw [hs]; norm_num
  rw [← h4]
  exact normSq_sum_le_card_mul s f

/-- The product of two signs squares to one. -/
lemma sign_pair_mul {m : ℕ} {ε η : ℤ} (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) (a : ZMod m) :
    ((ε : ZMod m) * (η : ZMod m)) * (((ε : ZMod m) * (η : ZMod m)) * a) = a := by
  rcases hε with h | h <;> rcases hη with h' | h' <;> rw [h, h'] <;> ring

lemma isUnit_of_sign {m : ℕ} {ε : ℤ} (h : ε = 1 ∨ ε = -1) : IsUnit (ε : ZMod m) := by
  rcases h with h | h
  · simp only [h, Int.cast_one]; exact isUnit_one
  · simp only [h, Int.cast_neg, Int.cast_one]; exact isUnit_neg_one

theorem EvG_le_Evar (R m : ℕ) (hm : 2 ≤ m) (u : GaussianInt → ℂ)
    (hu : ∀ z : GaussianInt, u z ≠ 0 → Nat.Coprime z.re.natAbs m)
    (h0 : ∀ z : GaussianInt, z.im = 0 → u z = 0) :
    Work.FIArea4.S15red.EvG (R : ℤ) m u
      ≤ 4 * (Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (Work.FIArea4.S15red.quadrantArr R m u 1 1)
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (Work.FIArea4.S15red.quadrantArr R m u 1 (-1))
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (Work.FIArea4.S15red.quadrantArr R m u (-1) 1)
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (Work.FIArea4.S15red.quadrantArr R m u (-1) (-1))) := by
  classical
  have hstep : ∀ a : ℕ,
      Complex.normSq (clsSum2 (R : ℤ) m u a)
        ≤ 4 * ∑ p ∈ Q, Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)) := by
    intro a
    rw [clsSum2_quadSum R m hm u hu h0 a]
    exact normSq_sum_le_card4 Q Q_card _
  have hsum : (∑ a ∈ Finset.range m, Complex.normSq (clsSum2 (R : ℤ) m u a))
      ≤ 4 * ∑ p ∈ Q, ∑ a ∈ Finset.range m,
          Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)) := by
    calc ∑ a ∈ Finset.range m, Complex.normSq (clsSum2 (R : ℤ) m u a)
        ≤ ∑ a ∈ Finset.range m,
            4 * ∑ p ∈ Q, Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)) :=
          Finset.sum_le_sum (fun a _ => hstep a)
      _ = 4 * ∑ a ∈ Finset.range m, ∑ p ∈ Q,
            Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)) := by
          rw [Finset.mul_sum]
      _ = 4 * ∑ p ∈ Q, ∑ a ∈ Finset.range m,
            Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)) := by
          rw [Finset.sum_comm]
  have hquad : ∀ p ∈ Q, (∑ a ∈ Finset.range m,
        Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)))
      = Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u p.1 p.2) := by
    intro p hp
    obtain ⟨hε, hη⟩ := Q_spec hp
    have hE : Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u p.1 p.2)
        = ∑ b ∈ Finset.range m, Complex.normSq
            (∑ q ∈ quadPairC R m (b : ZMod m), u ⟨p.1 * (q.1 : ℤ), p.2 * (q.2 : ℤ)⟩) := by
      rw [Evar_eq_sum_EvarCls]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      congr 1
      exact EvarCls_quadrantArr R m u p.1 p.2 hε hη b
    have hL : (∑ a ∈ Finset.range m, Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)))
        = ∑ a ∈ Finset.range m, Complex.normSq
            (∑ q ∈ quadPairC R m (((p.1 : ZMod m) * (p.2 : ZMod m)) * (a : ZMod m)),
              u ⟨p.1 * (q.1 : ℤ), p.2 * (q.2 : ℤ)⟩) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      congr 1
      have hcc : ((p.1 : ZMod m) * (p.2 : ZMod m)) * (((p.1 : ZMod m) * (p.2 : ZMod m)) * (a : ZMod m))
          = (a : ZMod m) := sign_pair_mul hε hη (a : ZMod m)
      have hl := quadPairC_eq_qPartC R m u p.1 p.2 hε hη
        (((p.1 : ZMod m) * (p.2 : ZMod m)) * (a : ZMod m))
      rw [hcc] at hl
      exact hl.symm
    rw [hE, hL]
    exact sum_range_mul_unit m ((p.1 : ZMod m) * (p.2 : ZMod m))
      ((isUnit_of_sign hε).mul (isUnit_of_sign hη))
      (fun c : ZMod m => Complex.normSq
        (∑ q ∈ quadPairC R m c, u ⟨p.1 * (q.1 : ℤ), p.2 * (q.2 : ℤ)⟩))
  calc Work.FIArea4.S15red.EvG (R : ℤ) m u
      = ∑ a ∈ Finset.range m, Complex.normSq (clsSum2 (R : ℤ) m u a) := rfl
    _ ≤ 4 * ∑ p ∈ Q, ∑ a ∈ Finset.range m,
          Complex.normSq (qPartC (R : ℤ) m u p.1 p.2 (a : ZMod m)) := hsum
    _ = 4 * ∑ p ∈ Q, Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u p.1 p.2) := by
        congr 1
        exact Finset.sum_congr rfl (fun p hp => hquad p hp)
    _ = 4 * (Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u 1 1)
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u 1 (-1))
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u (-1) 1)
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u (-1) (-1))) := by
        rw [sum_Q_four (fun a b => Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadrantArr R m u a b))]

end

end Work.FIArea4.S15red

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Work.FIArea4.EvarG_le_quadEvar`

The signed-box variance `EvarG R m u` (the class variance of the box `gBox R` with the Jacobi
weight `(Re z | oddPart m)` built into the class sums) is bounded by four copies of the
positive-box variance `Work.FIPlan.Evar` of the *m*-independent quadrant arrays
`quadArrE R u σ` (`z = (σ₁ r, σ₂ s)`, `r, s ≥ 1`).

The proof has two steps.

* `EvarG R m u = S15red.EvG R m (u · jwG m)`: the class sums of `clsSumG` are literally the class
  sums of the signed-box variance of the weighted array `u · jwG m` (`EvarG_eq_EvG_signed`).
* `S15red.EvG_le_Evar` splits the signed-box variance into the four quadrant variances
  `Evar (quadrantArr R m (u · jwG m) σ)`.

The rest of the file identifies the four quadrants: on the pairs of the `Evar`-class sum the
weighted array `u · jwG m` evaluated at the signed point `⟨σ₁r, σ₂s⟩` is `jwG m σ₁ · u ⟨…⟩`
(up to the *idempotent* factor `(r | oddPart m)² = 1` contributed by `quadrantArr` together with
`Evar`'s own Jacobi weight), so the class sums of `quadrantArr R m (u · jwG m) σ` are exactly the
class sums of `quadArrE R u σ` multiplied by the unimodular constant `jwG m σ₁` — which does not
change `Evar`.  This is `Evar_quadrantArr_eq_quadArrE`.

The array is first zeroed off the points whose real part is not coprime to `m`
(`zeroNotCoprime`): the class sums of `EvG` and of `quadrantArr` only ever see those points, and
on them the zeroing is invisible, while the zeroing makes the coprimality hypothesis of
`EvG_le_Evar` available.
-/

/-! ## Elementary facts about the Jacobi weight `jwG` -/

/-- `jwG` is multiplicative in its (integral) argument. -/
lemma jwG_mul (m : ℕ) (a b : ℤ) : jwG m (a * b) = jwG m a * jwG m b := by
  unfold jwG
  rw [jacobiSym.mul_left]
  push_cast
  ring

/-- `jwG m σ` is unimodular on a sign `σ = ± 1`. -/
lemma normSq_jwG_sign (m : ℕ) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Complex.normSq (jwG m σ) = 1 := by
  have h1 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hsq : jwG m σ * jwG m σ = 1 := by
    rw [← jwG_mul, h1]
    simp [jwG]
  have hnorm : ‖jwG m σ‖ = 1 := by
    have h2 : ‖jwG m σ‖ * ‖jwG m σ‖ = 1 := by rw [← norm_mul, hsq, norm_one]
    nlinarith [norm_nonneg (jwG m σ)]
  rw [Complex.normSq_eq_norm_sq, hnorm]
  norm_num

/-! ## The zeroed weighted array -/

/-- The array `u · jwG m`, zeroed on the points whose real part is not coprime to `m`.  The class
sums of `EvG` and the quadrant arrays `quadrantArr` only ever evaluate the array at points with
coprime real part, so the zeroing does not change them. -/
def zeroNotCoprime (m : ℕ) (u : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun z => if Nat.Coprime z.re.natAbs m then u z * jwG m z.re else 0

lemma zeroNotCoprime_of_coprime {m : ℕ} {u : GaussianInt → ℂ} {z : GaussianInt}
    (h : Nat.Coprime z.re.natAbs m) : zeroNotCoprime m u z = u z * jwG m z.re := by
  simp only [zeroNotCoprime, if_pos h]

/-- `EvarG R m u` is the signed-box variance of the weighted array `u · jwG m`. -/
lemma EvarG_eq_EvG_signed (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) :
    EvarG R m u = Work.FIArea4.S15red.EvG R m (fun z => u z * jwG m z.re) := by
  unfold EvarG Work.FIArea4.S15red.EvG clsSumG Work.FIArea4.S15red.clsSum2
    Work.FIArea4.S15red.clsF
  rfl

/-- Zeroing off the non-coprime points does not change the signed-box variance. -/
lemma EvG_zeroNotCoprime (R : ℤ) (m : ℕ) (u : GaussianInt → ℂ) :
    Work.FIArea4.S15red.EvG R m (zeroNotCoprime m u)
      = Work.FIArea4.S15red.EvG R m (fun z => u z * jwG m z.re) := by
  unfold Work.FIArea4.S15red.EvG Work.FIArea4.S15red.clsSum2
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [Work.FIArea4.S15red.mem_clsF] at hz
  exact zeroNotCoprime_of_coprime hz.2.1

/-! ## Comparing the class sums of `quadrantArr` and of `quadArrE` -/

/-- Membership of a natural in the symmetric interval `[-R, R]` of `ℤ`. -/
lemma intCast_mem_Icc {R r : ℕ} :
    ((r : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)) ↔ r ≤ R := by
  rw [Finset.mem_Icc]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact_mod_cast h.2
  · refine ⟨?_, by exact_mod_cast h⟩
    have h0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
    have hR : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg R
    linarith

/-- Pointwise comparison of the `EvarCls`-summands of the two quadrant arrays: for a pair `(r,s)`
of the class with `r ≥ 1`, `s ≥ 1` and `r` coprime to `m`, the summand of
`Evar (quadrantArr R m (zeroNotCoprime m u) σ)` is `jwG m σ₁` times the summand of
`Evar (quadArrE R u σ)`. -/
private lemma quad_pointwise (R m : ℕ) (u : GaussianInt → ℂ) {σ₁ σ₂ : ℤ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) {a : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ Work.FIArea4.EvarCls (R / 2 + 1) (R / 2 + 1) m a) :
    Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) σ₁ σ₂ p.1 p.2
        * ((jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart m) : ℤ) : ℂ)
      = jwG m σ₁ * (quadArrE R u σ₁ σ₂ p.1 p.2
          * ((jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart m) : ℤ) : ℂ)) := by
  obtain ⟨hp1, hp2, _⟩ := Work.FIArea4.mem_EvarCls.mp hp
  obtain ⟨hp1I, hc⟩ := Work.FIArea4.mem_EvarR.mp hp1
  have hr1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1I).1
  have hs1 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
  have hz1 : ((p.1 : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)) ↔ p.1 ≤ R := intCast_mem_Icc
  have hz2 : ((p.2 : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)) ↔ p.2 ≤ R := intCast_mem_Icc
  by_cases hbox : p.1 ≤ R ∧ p.2 ≤ R
  · obtain ⟨h1, h2⟩ := hbox
    have hnat : ((⟨σ₁ * (p.1 : ℤ), σ₂ * (p.2 : ℤ)⟩ : GaussianInt).re).natAbs = p.1 := by
      show (σ₁ * (p.1 : ℤ)).natAbs = p.1
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      rcases hσ₁ with h | h <;> rw [h] <;> simp
    have hV : zeroNotCoprime m u ⟨σ₁ * (p.1 : ℤ), σ₂ * (p.2 : ℤ)⟩
        = u ⟨σ₁ * (p.1 : ℤ), σ₂ * (p.2 : ℤ)⟩ * jwG m (σ₁ * (p.1 : ℤ)) := by
      rw [zeroNotCoprime]
      refine if_pos ?_
      rw [hnat]
      exact hc
    rw [Work.FIArea4.S15red.quadrantArr_mul_jacobiSym (r := p.1) (s := p.2) R m
      (zeroNotCoprime m u) σ₁ σ₂ (Finset.mem_Icc.mpr ⟨hr1, h1⟩) (Finset.mem_Icc.mpr ⟨hs1, h2⟩) hc]
    rw [hV]
    rw [quadArrE]
    rw [if_pos ⟨hz1.mpr h1, hz2.mpr h2⟩]
    rw [jwG_mul]
    simp only [jwG]
    ring
  · have hnoR : ¬ (p.1 ∈ Finset.Icc 1 R ∧ p.2 ∈ Finset.Icc 1 R ∧ Nat.Coprime p.1 m) := by
      rintro ⟨h1, h2, -⟩
      exact hbox ⟨(Finset.mem_Icc.mp h1).2, (Finset.mem_Icc.mp h2).2⟩
    have hnoE : ¬ ((p.1 : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)
        ∧ (p.2 : ℤ) ∈ Finset.Icc (-(R : ℤ)) (R : ℤ)) := by
      rintro ⟨h1, h2⟩
      exact hbox ⟨hz1.mp h1, hz2.mp h2⟩
    have hL : Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) σ₁ σ₂ p.1 p.2 = 0 := by
      simp only [Work.FIArea4.S15red.quadrantArr, if_neg hnoR]
    have hR : quadArrE R u σ₁ σ₂ p.1 p.2 = 0 := by
      simp only [quadArrE, if_neg hnoE]
    rw [hL, hR]
    simp

/-- The `Evar` of the signed-quadrant array `quadrantArr R m (u · jwG m) σ` equals the `Evar` of
the `m`-independent quadrant array `quadArrE R u σ`: on the pairs of the class sum the two
differ by the unimodular constant `jwG m σ₁`. -/
private lemma Evar_quadrantArr_eq_quadArrE (R m : ℕ) (u : GaussianInt → ℂ) (σ₁ σ₂ : ℤ)
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) :
    Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m
        (Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) σ₁ σ₂)
      = Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u σ₁ σ₂) := by
  rw [Work.FIArea4.S15red.Evar_eq_sum_EvarCls, Work.FIArea4.S15red.Evar_eq_sum_EvarCls]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hsum : (∑ p ∈ Work.FIArea4.EvarCls (R / 2 + 1) (R / 2 + 1) m a,
        Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) σ₁ σ₂ p.1 p.2
          * ((jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart m) : ℤ) : ℂ))
      = jwG m σ₁ * ∑ p ∈ Work.FIArea4.EvarCls (R / 2 + 1) (R / 2 + 1) m a,
          quadArrE R u σ₁ σ₂ p.1 p.2
            * ((jacobiSym (p.1 : ℤ) (Work.FIPlan.oddPart m) : ℤ) : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => quad_pointwise R m u hσ₁ hp)
  rw [hsum, Complex.normSq_mul, normSq_jwG_sign m hσ₁, one_mul]

/-! ## The target -/

theorem EvarG_le_quadEvar (R : ℕ) (m : ℕ) (hm : 2 ≤ m) (u : GaussianInt → ℂ)
    (h0 : ∀ z : GaussianInt, z.im = 0 → u z * jwG m z.re = 0) :
    EvarG (R : ℤ) m u ≤
      4 * (Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u 1 1)
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u 1 (-1))
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u (-1) 1)
        + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u (-1) (-1))) := by
  classical
  have hcu : ∀ z : GaussianInt, zeroNotCoprime m u z ≠ 0 → Nat.Coprime z.re.natAbs m := by
    intro z hz
    by_contra hc
    exact hz (by simp only [zeroNotCoprime, if_neg hc])
  have hc0 : ∀ z : GaussianInt, z.im = 0 → zeroNotCoprime m u z = 0 := by
    intro z hz
    by_cases hc : Nat.Coprime z.re.natAbs m
    · simp only [zeroNotCoprime, if_pos hc]
      exact h0 z hz
    · simp only [zeroNotCoprime, if_neg hc]
  have hmain := Work.FIArea4.S15red.EvG_le_Evar R m hm (zeroNotCoprime m u) hcu hc0
  calc EvarG (R : ℤ) m u
      = Work.FIArea4.S15red.EvG (R : ℤ) m (fun z => u z * jwG m z.re) :=
        EvarG_eq_EvG_signed (R : ℤ) m u
    _ = Work.FIArea4.S15red.EvG (R : ℤ) m (zeroNotCoprime m u) :=
        (EvG_zeroNotCoprime (R : ℤ) m u).symm
    _ ≤ 4 * (Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m
            (Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) 1 1)
          + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m
            (Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) 1 (-1))
          + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m
            (Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) (-1) 1)
          + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m
            (Work.FIArea4.S15red.quadrantArr R m (zeroNotCoprime m u) (-1) (-1))) := hmain
    _ = 4 * (Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u 1 1)
          + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u 1 (-1))
          + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u (-1) 1)
          + Work.FIPlan.Evar (R / 2 + 1) (R / 2 + 1) m (quadArrE R u (-1) (-1))) := by
        rw [Evar_quadrantArr_eq_quadArrE R m u 1 1 (Or.inl rfl),
            Evar_quadrantArr_eq_quadArrE R m u 1 (-1) (Or.inl rfl),
            Evar_quadrantArr_eq_quadArrE R m u (-1) 1 (Or.inr rfl),
            Evar_quadrantArr_eq_quadArrE R m u (-1) (-1) (Or.inr rfl)]

end

end Work.FIArea4

namespace Work.S15hybrid

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary properties of the Jacobi-twisted variance `Evar` -/

lemma Evar_nonneg (R S d : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIPlan.Evar R S d α := by
  unfold Work.FIPlan.Evar
  exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

/-- **Box shrinking.**  If `α` vanishes off the box `r ≤ 2R'`, `s ≤ 2S'` and `R' ≤ R`, `S' ≤ S`,
then `Evar R S d α = Evar R' S' d α`. -/
lemma Evar_eq_of_le {R R' S S' d : ℕ} (hR : R' ≤ R) (hS : S' ≤ S) (α : ℕ → ℕ → ℂ)
    (h1 : ∀ r s, 2 * R' < r → α r s = 0) (h2 : ∀ r s, 2 * S' < s → α r s = 0) :
    Work.FIPlan.Evar R S d α = Work.FIPlan.Evar R' S' d α := by
  unfold Work.FIPlan.Evar
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have hsub : (Finset.Icc 1 (2 * R')).filter (fun r => Nat.Coprime r d)
      ⊆ (Finset.Icc 1 (2 * R)).filter (fun r => Nat.Coprime r d) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr1).1,
      le_trans (Finset.mem_Icc.mp hr1).2 (Nat.mul_le_mul_left 2 hR)⟩, hr2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    have hsub2 : (Finset.Icc 1 (2 * S')).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d))
        ⊆ (Finset.Icc 1 (2 * S)).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs1).1,
        le_trans (Finset.mem_Icc.mp hs1).2 (Nat.mul_le_mul_left 2 hS)⟩, hs2⟩
    exact (Finset.sum_subset hsub2 (fun s hs hnot => by
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hs
      have hgt : 2 * S' < s := by
        by_contra hle
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hs1).1, Nat.le_of_not_lt hle⟩, hs2⟩)
      rw [h2 r s hgt, zero_mul])).symm
  · intro r hr hnot
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    have hgt : 2 * R' < r := by
      by_contra hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hr1).1, Nat.le_of_not_lt hle⟩, hr2⟩)
    exact Finset.sum_eq_zero (fun s _ => by rw [h1 r s hgt, zero_mul])

/-- **`Evar` is dominated by `Vvar`** for any `D` with `D < m ≤ 2D`. -/
lemma Evar_le_Vvar {R S D m : ℕ} (hmD : D < m) (hm2D : m ≤ 2 * D) (α : ℕ → ℕ → ℂ) :
    Work.FIPlan.Evar R S m α ≤ Work.FIPlan.Vvar R S D α := by
  unfold Work.FIPlan.Vvar
  exact Finset.single_le_sum (fun d _ => Evar_nonneg R S d α)
    (Finset.mem_Ioc.mpr ⟨hmD, hm2D⟩)

/-! ## `quadArrE`, unfolded -/

lemma quadArrE_eq (R : ℕ) (u : GaussianInt → ℂ) (σ₁ σ₂ : ℤ) (r s : ℕ)
    (hr : r ≤ R) (hs : s ≤ R) :
    Work.FIArea4.quadArrE R u σ₁ σ₂ r s = u ⟨σ₁ * (r : ℤ), σ₂ * (s : ℤ)⟩ := by
  unfold Work.FIArea4.quadArrE
  rw [if_pos]
  refine ⟨Finset.mem_Icc.mpr ⟨?_, by exact_mod_cast hr⟩,
          Finset.mem_Icc.mpr ⟨?_, by exact_mod_cast hs⟩⟩
  · show (-(R : ℤ)) ≤ ((r : ℕ) : ℤ)
    have h1 := Int.natCast_nonneg r
    have h2 : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg R
    linarith
  · show (-(R : ℤ)) ≤ ((s : ℕ) : ℤ)
    have h1 := Int.natCast_nonneg s
    have h2 : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg R
    linarith

lemma quadArrE_eq_zero (R : ℕ) (u : GaussianInt → ℂ) (σ₁ σ₂ : ℤ) (r s : ℕ)
    (h : R < r ∨ R < s) :
    Work.FIArea4.quadArrE R u σ₁ σ₂ r s = 0 := by
  unfold Work.FIArea4.quadArrE
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [Finset.mem_Icc] at h1 h2
  rcases h with h | h
  · exact absurd (by exact_mod_cast h1.2 : r ≤ R) (by omega)
  · exact absurd (by exact_mod_cast h2.2 : s ≤ R) (by omega)

/-- `radN` read as a natural number is `KK`. -/
lemma radN_eq_KK (Pa : Work.FITop.Params) :
    Work.FITop.radN Pa = (Work.FIArea4.S15red.KK Pa : ℤ) := by
  rw [Work.FIArea4.S15red.KK, Work.FITop.radN, Int.natAbs_natCast]

/-- The four-quadrant reduction of the stratum variance, with the stratum box. -/
lemma EvarG_le_quad_shrunk (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (u t : ℝ) (ℓ : ℤ) (e : ℕ) (he : 1 ≤ e)
    (m : ℕ) (hm : 2 ≤ m) :
    Work.FIArea4.EvarG (Work.FITop.radN Pa) m (Work.FIArea4.S15strU β u t ℓ e)
      ≤ 4 * (Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                (Work.FIArea4.S15strU β u t ℓ e) 1 1)
          + Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                (Work.FIArea4.S15strU β u t ℓ e) 1 (-1))
          + Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                (Work.FIArea4.S15strU β u t ℓ e) (-1) 1)
          + Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                (Work.FIArea4.S15strU β u t ℓ e) (-1) (-1))) := by
  have h0 : ∀ z : GaussianInt, z.im = 0 →
      Work.FIArea4.S15strU β u t ℓ e z * Work.FIArea4.jwG m z.re = 0 := by
    intro z hz
    rw [Work.FIArea4.S15red.S15strU_eq_zero_of_im_eq_zero Pa φ β hβ u t ℓ e hz, zero_mul]
  have hmain := Work.FIArea4.EvarG_le_quadEvar (Work.FIArea4.S15red.KK Pa) m hm
    (Work.FIArea4.S15strU β u t ℓ e) h0
  have hcast : Work.FIArea4.EvarG ((Work.FIArea4.S15red.KK Pa : ℕ) : ℤ) m
      (Work.FIArea4.S15strU β u t ℓ e)
      = Work.FIArea4.EvarG (Work.FITop.radN Pa) m (Work.FIArea4.S15strU β u t ℓ e) := by
    rw [radN_eq_KK Pa]
  rw [hcast] at hmain
  have hRe : Work.FIArea4.S15red.ReK Pa e ≤ Work.FIArea4.S15red.KK Pa / 2 + 1 := by
    rw [Work.FIArea4.S15red.ReK]
    have h : Work.FIArea4.S15red.KK Pa / (2 * e) ≤ Work.FIArea4.S15red.KK Pa / 2 :=
      Nat.div_le_div_left (by omega : (2:ℕ) ≤ 2 * e) (by norm_num)
    omega
  have hsup : ∀ {σ₁ σ₂ : ℤ}, (σ₁ = 1 ∨ σ₁ = -1) → (σ₂ = 1 ∨ σ₂ = -1) → ∀ r s,
      Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
        (Work.FIArea4.S15strU β u t ℓ e) σ₁ σ₂ r s ≠ 0 →
        r ≤ 2 * Work.FIArea4.S15red.ReK Pa e ∧ s ≤ 2 * Work.FIArea4.S15red.SeK Pa :=
    fun h1 h2 r s => Work.FIArea4.S15red.quadArrE_strU_support Pa φ β hβ u t ℓ e he h1 h2 r s
  have hsq : ∀ (σ₁ σ₂ : ℤ) (h1 : σ₁ = 1 ∨ σ₁ = -1) (h2 : σ₂ = 1 ∨ σ₂ = -1),
      Work.FIPlan.Evar (Work.FIArea4.S15red.KK Pa / 2 + 1) (Work.FIArea4.S15red.KK Pa / 2 + 1) m
        (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
          (Work.FIArea4.S15strU β u t ℓ e) σ₁ σ₂)
      = Work.FIPlan.Evar (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa) m
        (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
          (Work.FIArea4.S15strU β u t ℓ e) σ₁ σ₂) := by
    intro σ₁ σ₂ h1 h2
    refine Evar_eq_of_le hRe (le_of_eq rfl) _ (fun r s hrs => ?_) (fun r s hss => ?_)
    · by_contra hne
      exact absurd (hsup h1 h2 r s hne).1 (by omega)
    · by_contra hne
      have h2' : s ≤ 2 * (Work.FIArea4.S15red.KK Pa / 2 + 1) := (hsup h1 h2 r s hne).2
      omega
  refine le_trans hmain (le_of_eq ?_)
  rw [hsq 1 1 (Or.inl rfl) (Or.inl rfl), hsq 1 (-1) (Or.inl rfl) (Or.inr rfl),
      hsq (-1) 1 (Or.inr rfl) (Or.inl rfl), hsq (-1) (-1) (Or.inr rfl) (Or.inr rfl)]

end

end Work.S15hybrid
