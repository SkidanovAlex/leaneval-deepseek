import Mathlib
import Submission.Work.Mostow.gapA.screwDefs

/-!
# Normal form of the Minkowski projection onto the normal space of a geodesic

For two distinct boundary points `a b ∈ Sph 3`, let `A = nullA a = (a,1)`, `B = nullB b = (b,1)`
be the two future null vectors, `s = smB a b = ⟨A,B⟩ = ⟪a,b⟫ - 1 < 0` and `m = mmB a b = -s > 0`.
Every ambient vector decomposes as `x = α A + β B + v` with `v ⊥ A, B`, and `prjN a b x = v` is the
normal component; `Nsub a b = {x | ⟨x,A⟩ = ⟨x,B⟩ = 0}` is the (positive definite) normal space.

This file proves `Work.Mostow.gapA.screwNorm`, collecting the elementary numerical and linear
algebraic facts about `prjN`, `mmB`, `smB` and `Nsub` that the `n = 3` screw-motion argument needs:

* `0 < mmB a b`, `smB a b = -mmB a b`, `smB a b ≠ 0`;
* `prjN a b x ∈ Nsub a b` and the Pythagorean identity
  `⟨prjN x, prjN x⟩ = ⟨x,x⟩ - 2 ⟨x,A⟩⟨x,B⟩ / smB`;
* `prjN a b x = 0 ↔ x ∈ span{A,B}`;
* on `Nsub a b` the projection is the identity and the Minkowski form is positive definite
  (`0 ≤ ⟨x,x⟩`, with `⟨x,x⟩ = 0 → x = 0`).

The positivity on `Nsub` is proved by writing `x = (u,t)`, `u = spatM x`: orthogonality to `A`
gives `t = ⟪u,a⟫`, so `⟨x,x⟩ = ‖u‖² - ⟪u,a⟫² = ‖u - ⟪u,a⟫ • a‖² ≥ 0`, and it vanishes only when
`u ∥ a`, which together with orthogonality to `B` and `a ≠ b` forces `u = t = 0`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## The spatial/time decomposition of the Minkowski form -/

/-- The spatial part of a vector of `ℝ^{Fin n ⊕ Fin 1}`. -/
def spatM (x : Fin n ⊕ Fin 1 → ℝ) : E n := WithLp.toLp 2 (fun i => x (Sum.inl i))

@[simp] lemma spatM_nvec (ξ : E n) : spatM (nvec ξ) = ξ := by ext i; rfl

@[simp] lemma nvec_inr (ξ : E n) : (nvec ξ) (Sum.inr 0) = 1 := rfl

/-- `mink` in terms of the spatial part and the time coordinate. -/
lemma mink_spatM (x y : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x y = inner ℝ (spatM x) (spatM y) - x (Sum.inr 0) * y (Sum.inr 0) := by
  rw [Work.Mostow.mink, Submission.Mostow.Hyper.inner_eq_sum]; rfl

lemma mink_self_norm (x : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x x = ‖spatM x‖ ^ 2 - (x (Sum.inr 0)) ^ 2 := by
  rw [mink_spatM, real_inner_self_eq_norm_sq]; ring

/-- The Bessel identity `‖u - ⟪u,a⟫ • a‖² = ‖u‖² - ⟪u,a⟫²` for a unit vector `a`. -/
lemma norm_sq_sub_inner_smul (u a : E n) (ha : ‖a‖ = 1) :
    ‖u - (inner ℝ u a) • a‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u a) ^ 2 := by
  rw [norm_sub_sq_real]
  have h2 : inner ℝ u ((inner ℝ u a) • a) = (inner ℝ u a) * (inner ℝ u a) := by
    rw [real_inner_smul_right]
  have h3 : ‖(inner ℝ u a) • a‖ ^ 2 = (inner ℝ u a) ^ 2 := by
    rw [norm_smul, ha, mul_one, Real.norm_eq_abs, sq_abs]
  rw [h2, h3]; ring

/-! ## Bilinearity of `mink` and the two-term expansion -/

lemma sn_mink_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink (x + y) z = Work.Mostow.mink x z + Work.Mostow.mink y z :=
  minkSeg_add_left x y z

lemma sn_mink_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x (y + z) = Work.Mostow.mink x y + Work.Mostow.mink x z :=
  minkSeg_add_right x y z

lemma sn_mink_smul_left (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink (r • x) y = r * Work.Mostow.mink x y := by
  have h := minkSeg_smul (n := n) r 1 x y; simpa using h

lemma sn_mink_smul_right (x : Fin n ⊕ Fin 1 → ℝ) (r : ℝ) (y : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x (r • y) = r * Work.Mostow.mink x y := by
  have h := minkSeg_smul (n := n) 1 r x y; simpa using h

lemma sn_mink_neg_left (x y : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink (-x) y = - Work.Mostow.mink x y := by
  have h := minkSeg_smul (n := n) (-1) 1 x y; simpa using h

lemma sn_mink_neg_right (x y : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x (-y) = - Work.Mostow.mink x y := by
  rw [minkSeg_comm x (-y), sn_mink_neg_left, minkSeg_comm]

lemma sn_mink_sub_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink (x - y) z = Work.Mostow.mink x z - Work.Mostow.mink y z := by
  rw [sub_eq_add_neg, sn_mink_add_left, sn_mink_neg_left]; ring

lemma sn_mink_sub_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Work.Mostow.mink x (y - z) = Work.Mostow.mink x y - Work.Mostow.mink x z := by
  rw [sub_eq_add_neg, sn_mink_add_right, sn_mink_neg_right]; ring

/-- Expansion of `mink` on a pair of two-term combinations `U - αX - βY`. -/
lemma mink_expand_screwNorm (U X Y : Fin n ⊕ Fin 1 → ℝ) (α β α' β' : ℝ) :
    Work.Mostow.mink (U - α • X - β • Y) (U - α' • X - β' • Y)
      = Work.Mostow.mink U U - α' * Work.Mostow.mink U X - β' * Work.Mostow.mink U Y
        - α * Work.Mostow.mink X U + α * α' * Work.Mostow.mink X X + α * β' * Work.Mostow.mink X Y
        - β * Work.Mostow.mink Y U + β * α' * Work.Mostow.mink Y X + β * β' * Work.Mostow.mink Y Y := by
  simp only [sn_mink_sub_left, sn_mink_sub_right, sn_mink_smul_left, sn_mink_smul_right]; ring

/-- Expansion of `mink` on a two-term combination and a vector. -/
lemma mink_expand_l_screwNorm (U X Y Z : Fin n ⊕ Fin 1 → ℝ) (α β : ℝ) :
    Work.Mostow.mink (U - α • X - β • Y) Z
      = Work.Mostow.mink U Z - α * Work.Mostow.mink X Z - β * Work.Mostow.mink Y Z := by
  simp only [sn_mink_sub_left, sn_mink_smul_left]

/-! ## Pairings of the boundary null vectors -/

lemma mink_nvec_nvec (ξ η : E n) : Work.Mostow.mink (nvec ξ) (nvec η) = inner ℝ ξ η - 1 := by
  rw [mink_spatM, spatM_nvec, spatM_nvec, nvec_inr, nvec_inr, mul_one]

lemma mink_nvec_self {ξ : E n} (hξ : ξ ∈ Sph n) : Work.Mostow.mink (nvec ξ) (nvec ξ) = 0 := by
  rw [mink_self_norm, spatM_nvec, nvec_inr, (Work.Mostow.mem_Sph_iff ξ).mp hξ]; norm_num

/-- `⟪a,b⟫ < 1` for two distinct unit vectors. -/
lemma inner_lt_one {a b : E n} (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    inner ℝ a b < 1 := by
  have ha1 : ‖a‖ = 1 := (Work.Mostow.mem_Sph_iff a).mp ha
  have hb1 : ‖b‖ = 1 := (Work.Mostow.mem_Sph_iff b).mp hb
  have hle : inner ℝ a b ≤ 1 := by
    have h := abs_real_inner_le_norm a b
    rw [ha1, hb1, mul_one] at h
    exact (abs_le.mp h).2
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hab
  have hzero : inner ℝ (a - b) (a - b) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    have h1 : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, ha1]; norm_num
    have h2 : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq, hb1]; norm_num
    have h3 : inner ℝ b a = 1 := by rw [real_inner_comm, heq]
    linarith
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-! ## Positive definiteness on the normal space -/

/-- If `x ⊥ nvec a` then its time coordinate is its `a`-coordinate. -/
lemma orth_ta {a : E n} (x : Fin n ⊕ Fin 1 → ℝ)
    (hA : Work.Mostow.mink x (nvec a) = 0) : x (Sum.inr 0) = inner ℝ (spatM x) a := by
  have h := hA
  rw [mink_spatM, spatM_nvec, nvec_inr, mul_one] at h
  linarith

/-- On the orthogonal complement of a boundary null vector the Minkowski form is nonnegative. -/
lemma mink_nonneg_of_orth {a : E n} (ha : a ∈ Sph n) (x : Fin n ⊕ Fin 1 → ℝ)
    (hA : Work.Mostow.mink x (nvec a) = 0) : 0 ≤ Work.Mostow.mink x x := by
  have ha1 : ‖a‖ = 1 := (Work.Mostow.mem_Sph_iff a).mp ha
  rw [mink_self_norm, orth_ta x hA, ← norm_sq_sub_inner_smul (spatM x) a ha1]
  exact sq_nonneg _

/-- On the orthogonal complement of two distinct boundary null vectors the Minkowski form is
positive definite. -/
lemma mink_eq_zero_of_orth {a b : E n} (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    (x : Fin n ⊕ Fin 1 → ℝ)
    (hA : Work.Mostow.mink x (nvec a) = 0) (hB : Work.Mostow.mink x (nvec b) = 0)
    (h0 : Work.Mostow.mink x x = 0) : x = 0 := by
  have ha1 : ‖a‖ = 1 := (Work.Mostow.mem_Sph_iff a).mp ha
  have hta := orth_ta x hA
  have htb := orth_ta x hB
  have hw0 : spatM x - (inner ℝ (spatM x) a) • a = 0 := by
    have h := norm_sq_sub_inner_smul (spatM x) a ha1
    have h0' : ‖spatM x‖ ^ 2 - (inner ℝ (spatM x) a) ^ 2 = 0 := by
      rw [← hta, ← mink_self_norm]; exact h0
    rw [← h] at h0'
    have : ‖spatM x - (inner ℝ (spatM x) a) • a‖ = 0 := by
      nlinarith [norm_nonneg (spatM x - (inner ℝ (spatM x) a) • a)]
    exact norm_eq_zero.mp this
  have hsp_eq : spatM x = (inner ℝ (spatM x) a) • a := sub_eq_zero.mp hw0
  have hcoin : inner ℝ (spatM x) (a - b) = 0 := by
    have h1 : inner ℝ (spatM x) a = inner ℝ (spatM x) b := by rw [← hta, htb]
    rw [inner_sub_right, h1, sub_self]
  rw [hsp_eq, real_inner_smul_left] at hcoin
  have hinnerab : inner ℝ a (a - b) = 1 - inner ℝ a b := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, ha1]; ring
  rw [hinnerab] at hcoin
  have hmmpos : 0 < 1 - inner ℝ a b := by linarith [inner_lt_one ha hb hab]
  have hinner_sp_a : inner ℝ (spatM x) a = 0 := by
    rcases mul_eq_zero.mp hcoin with h | h
    · exact h
    · exact absurd h (ne_of_gt hmmpos)
  have hsp_zero : spatM x = 0 := by rw [hsp_eq, hinner_sp_a, zero_smul]
  funext k
  rcases k with i | j
  · have hh := congrArg (fun u : E n => u i) hsp_zero
    simp only [spatM] at hh
    simpa using hh
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [hta, hinner_sp_a]; simp


theorem screwNorm {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    (0 < Work.Mostow.gapA.mmB a b) ∧ (Work.Mostow.gapA.smB a b = -Work.Mostow.gapA.mmB a b) ∧ (Work.Mostow.gapA.smB a b ≠ 0) ∧
    (∀ x : Fin 3 ⊕ Fin 1 → ℝ, Work.Mostow.gapA.prjN a b x ∈ Work.Mostow.gapA.Nsub a b) ∧
    (∀ x : Fin 3 ⊕ Fin 1 → ℝ, Work.Mostow.mink (Work.Mostow.gapA.prjN a b x) (Work.Mostow.gapA.prjN a b x)
       = Work.Mostow.mink x x - 2 * (Work.Mostow.mink x (Work.Mostow.gapA.nullA a) * Work.Mostow.mink x (Work.Mostow.gapA.nullB b)) / Work.Mostow.gapA.smB a b) ∧
    (∀ x : Fin 3 ⊕ Fin 1 → ℝ, Work.Mostow.gapA.prjN a b x = 0 ↔ x = Work.Mostow.gapA.alC a b x • Work.Mostow.gapA.nullA a + Work.Mostow.gapA.beC a b x • Work.Mostow.gapA.nullB b) ∧
    (∀ x ∈ Work.Mostow.gapA.Nsub a b, Work.Mostow.gapA.prjN a b x = x) ∧
    (∀ x ∈ Work.Mostow.gapA.Nsub a b, 0 ≤ Work.Mostow.mink x x) ∧
    (∀ x ∈ Work.Mostow.gapA.Nsub a b, Work.Mostow.mink x x = 0 → x = 0) := by
  have hAA : Work.Mostow.mink (nullA a) (nullA a) = 0 := mink_nvec_self ha
  have hBB : Work.Mostow.mink (nullB b) (nullB b) = 0 := mink_nvec_self hb
  have hAB : Work.Mostow.mink (nullA a) (nullB b) = inner ℝ a b - 1 := mink_nvec_nvec a b
  have hAB' : Work.Mostow.mink (nullA a) (nullB b) = smB a b := rfl
  have hBA' : Work.Mostow.mink (nullB b) (nullA a) = smB a b := by
    rw [Work.Mostow.minkSeg_comm]; rfl
  have hmm : 0 < mmB a b := by rw [mmB]; linarith [inner_lt_one ha hb hab]
  have hsm : smB a b = -mmB a b := by rw [smB, mmB, hAB]; ring
  have hsmne : smB a b ≠ 0 := by rw [hsm]; linarith
  refine ⟨hmm, hsm, hsmne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [mem_Nsub]
    refine ⟨?_, ?_⟩
    · rw [prjN_def, mink_expand_l_screwNorm x (nullA a) (nullB b) (nullA a) (alC a b x) (beC a b x),
        hAA, hBA', alC, beC]
      field_simp
      ring
    · rw [prjN_def, mink_expand_l_screwNorm x (nullA a) (nullB b) (nullB b) (alC a b x) (beC a b x),
        hAB', hBB, alC, beC]
      field_simp
      ring
  · intro x
    have hAx : Work.Mostow.mink (nullA a) x = Work.Mostow.mink x (nullA a) := minkSeg_comm _ _
    have hBx : Work.Mostow.mink (nullB b) x = Work.Mostow.mink x (nullB b) := minkSeg_comm _ _
    rw [prjN_def, mink_expand_screwNorm x (nullA a) (nullB b) (alC a b x) (beC a b x) (alC a b x) (beC a b x),
      hAA, hBB, hAB', hBA', hAx, hBx, alC, beC]
    field_simp
    ring
  · intro x
    constructor
    · intro h
      have hd := eq_decomp a b x
      rw [h, add_zero] at hd
      exact hd.symm
    · intro h
      have h' : x - (alC a b x • nullA a + beC a b x • nullB b) = 0 := sub_eq_zero.mpr h
      rw [prjN_def, show x - alC a b x • nullA a - beC a b x • nullB b
            = x - (alC a b x • nullA a + beC a b x • nullB b) from by abel]
      exact h'
  · intro x hx
    obtain ⟨hxA, hxB⟩ := mem_Nsub.mp hx
    rw [prjN_def, alC, beC, hxA, hxB]; simp
  · intro x hx
    obtain ⟨hxA, hxB⟩ := mem_Nsub.mp hx
    exact mink_nonneg_of_orth ha x hxA
  · intro x hx h0
    obtain ⟨hxA, hxB⟩ := mem_Nsub.mp hx
    exact mink_eq_zero_of_orth ha hb hab x hxA hxB h0

end

end Work.Mostow.gapA
